import csv, os, re, subprocess, sys, time
from collections import defaultdict
from os import path

timeout = 5

provers = [
    ('Natty', f'./natty -t{timeout}'),
    ('E', f'eprover-ho --auto -s --cpu-limit={timeout}'),
    ('Vampire', f'vampire -t {timeout}'),
    ('Zipperposition', f'zipperposition --mode best --input tptp --timeout {timeout}'),
]

if len(sys.argv) != 2:
    print(f'usage: {sys.argv[0]} <dir>')
    sys.exit(1)

dir = sys.argv[1]
files = [name.removesuffix('.thf') for name in os.listdir(dir) if name.endswith('.thf')]
files.sort(key = lambda s: [int(n) for n in s.split('_')])

results = {}
for file in files:
    with open(path.join(dir, file + '.thf')) as f:
        conjecture = f.readline().strip().removeprefix('% Problem: '.strip())
    name = file.replace('_', '.')
    results[file] = { '' : f'thm {name}', 'conjecture' : conjecture }

results_file = dir + '_results.csv'
if path.exists(results_file):
    with open(results_file) as f:
        reader = csv.DictReader(f)
        for row in reader:
            name, conjecture = row[''], row['conjecture']
            r = [k for k, v in results.items()
                 if (v[''], v['conjecture']) == (name, conjecture)]
            if r != []:
                results[r[0]] = row

for prover, command in provers:
    for file, result in results.items():
        r = result.get(prover)
        if r != None and r != '':
            continue

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

proved : defaultdict = defaultdict(int)
total_time = defaultdict(float)
total_score = defaultdict(float)

for result in results.values():
    for prover, r in result.items():
        try:
            time = float(r)
            proved[prover] += 1
            total_time[prover] += time
            total_score[prover] += time
        except ValueError:
            total_score[prover] += 2 * timeout

with open(results_file, 'w') as out:
    fieldnames = ['', 'conjecture'] + [p[0] for p in provers]
    writer = csv.DictWriter(out, fieldnames = fieldnames, extrasaction = 'ignore')
    writer.writeheader()
    writer.writerows(results.values())
    out.write('\n')
    n = len(files)

    proved[''] = f'proved (of {n})'
    writer.writerow(proved)

    avg_time = { prover : f'{t / proved[prover]:.2f}' for prover, t in total_time.items() }
    avg_time[''] = 'average time'
    writer.writerow(avg_time)

    score = { prover : f'{t / n:.2f}' for prover, t in total_score.items() }
    score[''] = 'PAR-2 score'
    print(score)
    writer.writerow(score)

    plural = '' if timeout == 1 else 's'
    out.write(f'\nlimit = {timeout} second{plural}\n')
