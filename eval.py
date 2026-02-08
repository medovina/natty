import csv, glob, multiprocessing, os, re, subprocess, sys, threading
from collections import defaultdict
from concurrent import futures
from dataclasses import dataclass
from os import path

clear_line = '\033[K'

default_timeout = 5

@dataclass
class Config:
    all_subdirs: bool
    dir: str
    eval_provers: list
    timeout: int
    only_summary: bool
    prove_steps: bool
    stats: bool

conf = Config(False, '', [], default_timeout, False, True, False)

all_provers = {
    'Natty' :
        { 'cmd': 'natty -t{timeout}',
          'stats_arg': '-i',
          'stats' : { 'given': r'given: (\d+)',
                      'generated': r'generated: (\d+)' } },
    'Natty (no by)' :
        { 'cmd': 'natty -b -t{timeout}',
          'short_name': 'nat_no_by',
          'stats_arg': '-i',
          'stats' : { 'given': r'given: (\d+)',
                      'generated': r'generated: (\d+)' } },
    'E' :   # -s: silent
        { 'cmd': 'eprover-ho --auto -s --cpu-limit={timeout}',
          'stats_arg': '--print-statistics',
          'stats' : { '_initial': r'# Initial clauses in saturation +: (\d+)',
                      'given': r'# ...remaining for further processing +: (\d+)',
                      'generated' : r'# Generated clauses +: (\d+)' } },
    'Vampire' :
        { 'cmd': 'vampire -t {timeout}',
          'stats_arg': '-stat full',
          'stats' : { 'given': r'% Activations started: (\d+)' } },
    'Zipperposition' :
        { 'cmd': 'zipperposition --mode best --input tptp --timeout {timeout}',
          'stats' : { 'given' : r'^# done (\d+) iterations'} }
}
all_prover_names = list(all_provers.keys())

def short_name(p):
    return all_provers[p].get('short_name') or p

def to_int(s):
    if s.isdigit():
        return int(s)
    assert len(s) == 1
    return ord(s) - ord('a')

def sort_key(s):
    s = s.split(':')[0]
    return [to_int(n) for n in s.replace('_s', '_').split('_')]

def read_theorems(thf_dir):
    files = [name.removesuffix('.thf') for name in os.listdir(thf_dir)
             if name.endswith('.thf')]
    if len(files) == 0:
        print(f'no .thf files in {thf_dir}')
        exit()

    files = [name for name in files if name[0].isdigit()]
    files.sort(key = sort_key)

    theorems = {}
    for file in files:
        with open(path.join(thf_dir, file + '.thf')) as f:
            conjecture = f.readline().strip().removeprefix('% Problem: '.strip())
        is_step = re.search(r'_s\d+$', file) is not None
        if conf.prove_steps:
            if is_step:
                include = True
            else:
                prefix = file.split(':')[0] + '_s'
                include = not any(f.startswith(prefix) for f in files)  # theorem has no steps
        else:
            include = not is_step
        if include:
            w = file.split(':')
            w[0] = w[0].replace('_', '.')
            id = ':'.join(w)
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

def prove(thf_dir, prover, file):
    with lock:
        proving.append(file)
        show_proving()

    prover_info = all_provers[prover]
    cmd = prover_info['cmd']
    cmd = cmd.replace('{timeout}', str(conf.timeout))
    if conf.stats:
        if stats_arg := prover_info.get('stats_arg'):
            cmd += " " + stats_arg
        prover_stats = prover_info.get('stats')
    else:
        prover_stats = None

    filename = path.join(thf_dir, file + '.thf')
    cmd += " " + filename

    completed = subprocess.run("time -f 'time:%U %S' " + cmd, shell = True, capture_output = True)

    text = completed.stdout.decode('utf-8', 'ignore') + completed.stderr.decode('utf-8', 'ignore')
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
    if success and prover_stats != None:
        for line in lines:
            for stat, regex in prover_stats.items():
                if m := re.search(regex, line):
                    res[stat] = int(m[1])
        if prover == 'E':
            # In E the initial clauses enter the main loop twice, one during presaturation
            # interreduction and then again during the main phase.  We don't want to count
            # them as given both times.
            res['given'] = max(0, res['given'] - res['_initial'])
            del res['_initial']
        if prover.startswith('Vampire') and 'given' not in res:
            res['given'] = 0

    with lock:
        print(clear_line + cmd)
        print(status)
        proving.remove(file)
        show_proving()

    return res

def prove1(thf_dir, prover, id):
    try:
        file = id.replace('.', '_')
        return prove(thf_dir, prover, file)
    except Exception as e:
        print(e)
        raise e

def run_prover(thf_dir, theorems, prover, results):
    ids = [id for id in theorems.keys() if id not in results[prover]['time']]

    if ids != []:
        with futures.ThreadPoolExecutor(multiprocessing.cpu_count() // 4) as ex:
            out = ex.map(lambda id: prove1(thf_dir, prover, id), ids)
        for id, stats in zip(ids, out):
            for stat, val in stats.items():
                results[prover][stat][id] = val
        return True
    else:
        return False

def is_float(s):
    try:
        float(s)
        return True
    except ValueError:
        return False

def write_results(theorems, results, results_file):
    proved : defaultdict = defaultdict(int)
    total_stat = defaultdict(lambda: defaultdict(float)) # prover -> stat -> total

    for prover, stats in results.items():
        for id in theorems:
            r = stats['time'].get(id)
            if r != None and is_float(r):
                proved[prover] += 1
                for stat, d in stats.items():
                    total_stat[prover][stat] += float(d[id])

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
        stats_rows = [proved_row, avg_row]

        for prover, stats in prover_stats:
            for stat in stats:
                avg = total_stat[prover][stat] / proved[prover]
                avg_row.append(f'{avg:.2f} sec' if stat == 'time' else f'{avg:.1f}')

                if stat == 'time':
                    percent = proved[prover] / n * 100
                    proved_row.append(f'{proved[prover]} ({percent:.0f}%)')
                else:
                    proved_row.append('')

        for row in stats_rows:
            writer.writerow(row)

        plural = '' if conf.timeout == 1 else 's'
        out.write(f'\nlimit = {conf.timeout} second{plural}\n')

def parse_args():
    i = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg == '-a':
            conf.eval_provers = all_prover_names
        elif arg == '-d':
            conf.all_subdirs = True
        elif arg.startswith('-e'):
            prefix = arg[2:].lower()
            conf.eval_provers = [p for p in all_prover_names
                       if not (short_name(p).lower().startswith(prefix))]
        elif arg == '-h':
            conf.prove_steps = False
        elif arg.startswith('-p'):
            prefix = arg[2:].lower()
            provers = [p for p in all_prover_names if short_name(p).lower().startswith(prefix)]
            conf.eval_provers = [] if provers == [] else [provers[0]]
        elif arg == '-s':
            conf.stats = True
        elif arg.startswith('-t'):
            conf.timeout = int(arg[2:])
        elif arg == '-y':
            conf.only_summary = True
        else:
            break
        i += 1

    if i != len(sys.argv) - 1:
        print(f'usage: {sys.argv[0]} [options...] <dir>')
        print( '    -a: evaluate all provers')
        print( '    -d: evaluate theorems in all subdirectories')
        print( '    -e<prover>: evaluate all provers except the given prover')
        print( '    -h: try to prove theorems without using proof steps')
        print( '    -p<prover>: evaluate only the given prover')
        print( '    -s: collect statistics')
        print(f'    -t<num>: timeout (default is {default_timeout} seconds)')
        print( '    -y: only generate summary csv')
        exit(1)

    if conf.eval_provers == [] and not conf.only_summary:
        print('must specify prover(s)')
        exit(1)

    return sys.argv[i]

def summary(top_dir):
    header = None
    proved_row, times_row = {}, {}
    total_proved, total_time = defaultdict(int), defaultdict(float)
    total = 0
    for file in sorted(glob.glob(path.join(top_dir, '*.csv'))):
        module = path.splitext(path.basename(file))[0]
        if module == 'summary':
            continue
        with open(file) as f:
            proved = {}
            reader = csv.reader(f)
            for n, row in enumerate(reader):
                if n == 0:
                    if header == None:
                        assert row[0:2] == ['', 'conjecture']
                        header = row
                    else:
                        assert header == row
                    continue
                if row != [] and (m := re.fullmatch(r'proved \(of (\d+)\)', row[0])):
                    total += int(m[1])
                    for prover, s in zip(header[2:], row[2:]):
                        n = int(s.split()[0])
                        proved[prover] = n
                        total_proved[prover] += n
                    del row[1]
                    proved_row[module] = row
                if row != [] and row[0] == 'average':
                    for prover, s in zip(header[2:], row[2:]):
                        t = float(s.split()[0])
                        total_time[prover] += t * proved[prover]
                    del row[1]
                    times_row[module] = row
    with open(path.join(top_dir, 'summary.csv'), 'w') as out:
        writer = csv.writer(out)
        header[1] = ''      # erase "conjecture"
        writer.writerow(header)
        for module in proved_row:
            row = proved_row[module]
            row.insert(0, module)
            writer.writerow(row)
            row = times_row[module]
            row.insert(0, '')
            writer.writerow(row)
        total_row = ['TOTAL', f'proved (of {total})']
        for p in header[2:]:
            percent = 100 * total_proved[p] / total
            total_row.append(f'{total_proved[p]} ({percent:.0f}%)')
        writer.writerow(total_row)
        average_row = ['', 'average']
        for p in header[2:]:
            average_time = total_time[p] / total_proved[p]
            average_row.append(f'{average_time:.2f} sec')
        writer.writerow(average_row)

def main():
    conf.dir = parse_args()

    if conf.only_summary:
        thf_dirs = []
    elif conf.all_subdirs:
        thf_dirs = [p for d in os.listdir(conf.dir) for p in [path.join(conf.dir, d)]
                    if path.isdir(p)]
    else:
        thf_dirs = [conf.dir]

    for thf_dir in sorted(thf_dirs):
        theorems = read_theorems(thf_dir)
        kind = '' if conf.prove_steps else '_theorems'
        timeout_suffix = '' if conf.timeout == default_timeout else f'_{conf.timeout}'
        results_file = f'{thf_dir}{kind}{timeout_suffix}.csv'
        results = read_results(theorems, results_file)

        for prover in conf.eval_provers:
            if run_prover(thf_dir, theorems, prover, results):
                write_results(theorems, results, results_file)

    summary(conf.dir if conf.only_summary or conf.all_subdirs else path.dirname(conf.dir))

main()
