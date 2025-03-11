import csv, os, re, subprocess, sys, time
from collections import defaultdict
from os import path

timeout = default_timeout = 5
timeout_suffix = ''
eval_all = False
eval_prover = None
all_theorems = False

i = 1
while i < len(sys.argv):
    arg = sys.argv[i]
    if arg == '-a':
        eval_all = True
    elif arg == '-h':
        all_theorems = True
    elif arg.startswith('-p'):
        eval_prover = arg[2:].lower()
    elif arg.startswith('-t'):
        timeout = int(arg[2:])
        timeout_suffix = f'_{timeout}'
    else:
        break
    i += 1

if i != len(sys.argv) - 1:
    print(f'usage: {sys.argv[0]} [options...] <dir>')
    print( '    -a: evaluate all provers')
    print( '    -h: also try to prove theorems without proof steps')
    print( '    -p<prover>: evaluate only the given prover')
    print(f'    -t<num>: timeout (default is {default_timeout} seconds)')
    sys.exit(1)
dir = sys.argv[i]

all_provers = [
    ('Natty', f'./natty -t{timeout}'),
    ('E', f'eprover-ho --auto -s --cpu-limit={timeout}'),   # -s: silent
    ('Vampire', f'vampire -t {timeout}'),
    ('Zipperposition', f'zipperposition --mode best --input tptp --timeout {timeout}'),
]

if eval_all:
    eval_provers = all_provers
elif eval_prover != None:
    eval_provers = [p for p in all_provers if p[0].lower().startswith(eval_prover)]
else:
    eval_provers = [all_provers[0]]
all_prover_names = [p[0] for p in all_provers]

files = [name.removesuffix('.thf') for name in os.listdir(dir) if name.endswith('.thf')]
files.sort(key = lambda s: [int(n) for n in s.replace('s', '').split('_')])

class Group:
    def __init__(self, name):
        self.results = {}
        self.results_file = f'{dir}_{name}{timeout_suffix}.csv'

    def read(self):
        if path.exists(self.results_file):
            with open(self.results_file) as f:
                reader = csv.DictReader(f)
                for row in reader:
                    name, conjecture = row[''], row['conjecture']
                    row_ids = [k for k, v in self.results.items()
                                 if (v[''], v['conjecture']) == (name, conjecture)]
                    if row_ids != []:
                        self.results[row_ids[0]] = row

    def write(self):
        proved : defaultdict = defaultdict(int)
        total_time = defaultdict(float)
        total_score = defaultdict(float)

        for result in self.results.values():
            for prover in all_prover_names:
                r = result.get(prover)
                if r != None and r != '':
                    try:
                        time = float(r)
                        proved[prover] += 1
                        total_time[prover] += time
                        total_score[prover] += time
                    except ValueError:
                        total_score[prover] += 2 * timeout

        provers = list(proved.keys())
        with open(self.results_file, 'w') as out:
            fieldnames = ['', 'conjecture'] + provers
            writer = csv.DictWriter(out, fieldnames = fieldnames)
            writer.writeheader()
            writer.writerows(self.results.values())
            out.write('\n')
            n = len(self.results)

            proved_row = {'' : f'proved (of {n})'}
            for p in provers:
                percent = proved[p] / n * 100
                proved_row[p] = f'{proved[p]} ({percent:.0f}%)'
            writer.writerow(proved_row)

            avg_time = { prover : f'{t / proved[prover]:.2f}'
                         for prover, t in total_time.items() }
            avg_time[''] = 'average time'
            writer.writerow(avg_time)

            score = { prover : f'{t / n:.2f}' for prover, t in total_score.items() }
            score[''] = 'PAR-2 score'
            writer.writerow(score)

            plural = '' if timeout == 1 else 's'
            out.write(f'\nlimit = {timeout} second{plural}\n')

thm_group = Group('theorems')
step_group = Group('steps')
groups = [thm_group, step_group] if all_theorems else [step_group]

results = {}
for file in files:
    with open(path.join(dir, file + '.thf')) as f:
        conjecture = f.readline().strip().removeprefix('% Problem: '.strip())
    name = file.replace('_', '.')
    data = { '' : f'thm {name}', 'conjecture' : conjecture }
    if '_s' in file:
        step_group.results[file] = data
    else:
        thm_group.results[file] = data
        prefix = file.removesuffix('.thf') + '_s'
        if not any(f.startswith(prefix) for f in files):  # theorem has no steps
            step_group.results[file] = data

for g in groups:
    g.read()

for prover, command in eval_provers:
    for group in groups:
        changed = False
        for file, result in group.results.items():
            r = result.get(prover)
            if r != None and r != '':
                continue
            changed = True

            filename = path.join(dir, file + '.thf')

            cmd = command + " " + filename
            print(cmd)

            start = time.time()
            completed = subprocess.run(cmd, shell = True, capture_output = True)
            elapsed = time.time() - start

            text = completed.stdout.decode('utf-8') + completed.stderr.decode('utf-8')
            for line in text.splitlines():
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
            print(status)
            match status:
                case 'Theorem':
                    res = f'{elapsed:.2f}'
                case 'GaveUp':
                    res = 'timeout' if prover.startswith('E ') else 'gave up'
                case 'ResourceOut' | 'Timeout':
                    res = 'timeout'
                case 'Error':
                    res = 'error'
                case _:
                    print(f'unknown status: {text}')
                    assert False
            result[prover] = res

        # output continuously
        if changed:
            group.write()
