import csv, multiprocessing, os, re, subprocess, sys, threading
from collections import defaultdict
from concurrent import futures
from dataclasses import dataclass
from os import path

clear_line = '\033[K'

default_timeout = 5

@dataclass
class Config:
    dir: str
    eval_provers: list
    timeout: int
    prove_steps: bool
    stats: bool

conf = Config('', [], default_timeout, True, False)

all_provers = {
    'Natty' :
        { 'cmd': './natty -t{timeout}', 'given': r'given clauses: (\d+)' },
    'Natty_predict' :
        { 'cmd': './natty -n -t{timeout}', 'given': r'given clauses: (\d+)' },
    'E' :   # -s: silent
        { 'cmd': 'eprover-ho --auto -s --cpu-limit={timeout}',
          'stats': '--print-statistics',
          'given': r'# ...remaining for further processing +: (\d+)' },
    'Vampire' :
        { 'cmd': 'vampire -t {timeout}',
          'stats': '-stat full', 'given': r'% Activations started: (\d+)' },
    'Zipperposition' :
        { 'cmd': 'zipperposition --mode best --input tptp --timeout {timeout}',
          'given' : r'^# done (\d+) iterations'}
}
all_prover_names = list(all_provers.keys())

def read_theorems():
    files = [name.removesuffix('.thf') for name in os.listdir(conf.dir) if name.endswith('.thf')]
    files.sort(key = lambda s: [int(n) for n in s.replace('s', '').split('_')])

    theorems = {}
    for file in files:
        with open(path.join(conf.dir, file + '.thf')) as f:
            conjecture = f.readline().strip().removeprefix('% Problem: '.strip())
        id = file.replace('_', '.')
        if conf.prove_steps:
            if '_s' in file:
                include = True
            else:
                prefix = file.removesuffix('.thf') + '_s'
                include = not any(f.startswith(prefix) for f in files)  # theorem has no steps
        else:
            include = '_s' not in file
        if include:
            theorems[id] = conjecture
    return theorems

# Return a results dictionary which maps prover_name -> stat -> theorem_id -> value .
def read_results(theorems, results_file):
    results = defaultdict(lambda: defaultdict(dict))

    if path.exists(results_file):
        with open(results_file) as f:
            reader = csv.reader(f)
            for n, row in enumerate(reader):
                if n == 0:
                    header = row
                    assert header[0:2] == ['', 'conjecture']
                    continue
                
                if len(row) >= 2:
                    name, conjecture = row[0:2]
                    if name.startswith('thm '):
                        id = name.removeprefix('thm ')
                        if theorems.get(id) == conjecture:
                            for col, val in zip(header[2:], row[2:]):
                                if col[0].isupper():
                                    prover = col
                                    stat = 'time'
                                else:
                                    stat = col
                                results[prover][stat][id] = val
    return results

proving = []
lock = threading.Lock()

def show_proving():
    print(clear_line + f'proving {', '.join(proving)}...', end = '\r')

def prove(prover, file):
    with lock:
        proving.append(file)
        show_proving()

    prover_info = all_provers[prover]
    cmd = prover_info['cmd']
    cmd = cmd.replace('{timeout}', str(conf.timeout))
    if conf.stats:
        if stats := prover_info.get('stats'):
            cmd += " " + stats
        given_regex = prover_info.get('given')
    else:
        given_regex = None

    filename = path.join(conf.dir, file + '.thf')
    cmd += " " + filename

    completed = subprocess.run("time -f 'time:%U %S' " + cmd, shell = True, capture_output = True)

    text = completed.stdout.decode('utf-8') + completed.stderr.decode('utf-8')
    lines = text.splitlines()
    times = lines[-1].removeprefix('time:')
    assert times != lines[-1], 'no times found'
    elapsed = sum(map(float, times.split()))

    for line in lines:
        if m := re.search(r'SZS status (\w+)', line):
            status = m[1]
            break
        if line == 'Aborted':
            status = 'Error'
            break
    else:
        if prover.startswith('Vampire') or prover.startswith('Zipperposition'):
            status = 'Timeout'
        else:
            status = 'Error'

    success = False
    match status:
        case 'Theorem' | 'ContradictoryAxioms':  # contradictory axioms are still a proof
            time = f'{elapsed:.2f}'
            success = True
        case 'GaveUp':
            time = 'gave up'
        case 'ResourceOut' | 'Timeout':
            time = 'timeout'
        case 'Error':
            time = 'error'
        case _:
            print(f'unknown status: {text}')
            assert False

    res = {'time' : time }
    if success and given_regex != None:
        for line in lines:
            if m := re.search(given_regex, line):
                res['given'] = m[1]
                break
        else:
            if prover.startswith('Vampire'):
                res['given'] = 0

    with lock:
        print(clear_line + cmd)
        print(status)
        proving.remove(file)
        show_proving()

    return res

def prove1(prover, id):
    try:
        file = id.replace('.', '_')
        return prove(prover, file)
    except Exception as e:
        print(e)
        raise e

def run_prover(theorems, prover, results):
    ids = [id for id in theorems.keys() if id not in results[prover]['time']]

    if ids != []:
        with futures.ThreadPoolExecutor(multiprocessing.cpu_count() // 4) as ex:
            out = ex.map(lambda id: prove1(prover, id), ids)
        for id, stats in zip(ids, out):
            for stat, val in stats.items():
                results[prover][stat][id] = val
        return True
    else:
        return False

def write_results(theorems, results, results_file):
    proved : defaultdict = defaultdict(int)
    total_stat = defaultdict(lambda: defaultdict(float)) # prover -> stat -> total
    total_score = defaultdict(float)

    for prover, stats in results.items():
        for id in theorems:
            r = stats['time'].get(id)
            if r != None and r != '':
                try:
                    time = float(r)
                    proved[prover] += 1
                    total_score[prover] += time
                    for stat, d in stats.items():
                        total_stat[prover][stat] += float(d[id])
                except ValueError:
                    total_score[prover] += 2 * conf.timeout

    with open(results_file, 'w') as out:
        prover_stats = [(prover, stats) for prover in all_prover_names
                                        if (stats := results.get(prover))]
        
        writer = csv.writer(out)
        header = ['', 'conjecture']
        for prover, stats in prover_stats:
            header.append(prover)
            header += [stat for stat in stats if stat != 'time']
        writer.writerow(header)

        for id in theorems:
            row = ['thm ' + id, theorems[id]]
            for prover, stats in prover_stats:
                for stat, vals in stats.items():
                    row.append(vals.get(id, ''))
            writer.writerow(row)

        out.write('\n')
        n = len(theorems)

        proved_row = [f'proved (of {n})', '']
        avg_row = ['average', '']
        par2_row = ['PAR-2 score', '']
        stats_rows = [proved_row, avg_row, par2_row]

        for prover, stats in prover_stats:
            for stat in stats:
                avg = total_stat[prover][stat] / proved[prover]
                avg_row.append(f'{avg:.2f} sec' if stat == 'time' else f'{avg:.1f}')

                if stat == 'time':
                    percent = proved[prover] / n * 100
                    proved_row.append(f'{proved[prover]} ({percent:.0f}%)')

                    par2 = total_score[prover] / n
                    par2_row.append(f'{par2:.2f}')
                else:
                    proved_row.append('')
                    par2_row.append('')

        for row in stats_rows:
            writer.writerow(row)

        plural = '' if conf.timeout == 1 else 's'
        out.write(f'\nlimit = {conf.timeout} second{plural}\n')

def parse_args():
    i = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg == '-a':
            conf.eval_provers = list(all_provers.keys())
        elif arg == '-h':
            conf.prove_steps = False
        elif arg.startswith('-p'):
            prefix = arg[2:].lower()
            provers = [p for p in all_prover_names if p.lower().startswith(prefix)]
            conf.eval_provers = [] if provers == [] else [provers[0]]
        elif arg == '-s':
            conf.stats = True
        elif arg.startswith('-t'):
            conf.timeout = int(arg[2:])
        else:
            break
        i += 1

    if i != len(sys.argv) - 1:
        print(f'usage: {sys.argv[0]} [options...] <dir>')
        print( '    -a: evaluate all provers')
        print( '    -h: try to prove theorems without using proof steps')
        print( '    -p<prover>: evaluate only the given prover')
        print( '    -s: collect statistics')
        print(f'    -t<num>: timeout (default is {default_timeout} seconds)')
        exit(1)

    if conf.eval_provers == []:
        print('must specify prover(s) with -p or -a')
        exit(1)

    return sys.argv[i]

def main():
    conf.dir = parse_args()
    theorems = read_theorems()

    kind = 'steps' if conf.prove_steps else 'theorems'
    timeout_suffix = '' if conf.timeout == default_timeout else f'_{conf.timeout}'
    results_file = f'{conf.dir}_{kind}{timeout_suffix}.csv'
    results = read_results(theorems, results_file)

    for prover in conf.eval_provers:
        if run_prover(theorems, prover, results):
            write_results(theorems, results, results_file)

main()
