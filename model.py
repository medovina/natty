import sys
import numpy as np
import pandas as pd
from sklearn.linear_model import LogisticRegression

verbose = 0

for arg in sys.argv[1:]:
    if arg == '-v':
        verbose = 1
    else:
        print(f'usage: {sys.argv[0]} [-v]')
        exit()

def geo_mean(xs, weights):
    return np.exp((np.log(xs) * weights).sum() / weights.sum())

formulas = pd.read_csv('generated.csv')

counts = formulas.loc[:, 'theorem' : 'id'].groupby('theorem').size()
thm_weights = 1000 / counts
thm_weights.name = 'sample_weight'
sample_weights = \
    pd.merge(formulas.theorem, thm_weights, left_on = 'theorem', right_index = True).sample_weight

features = formulas.drop(columns = ['theorem', 'orig', 'in_proof', 'formula'])
orig = pd.get_dummies(formulas.orig, prefix = 'is')
X = pd.concat([orig, features], axis = 1)

log_reg = LogisticRegression(
    solver = 'liblinear', penalty = 'l1', C = 0.2, verbose = verbose)
log_reg.fit(X, formulas.in_proof, sample_weights)

print(f'penalty = {log_reg.penalty}, regularization constant = {log_reg.C}, ' +
      f'solver = {log_reg.solver}')

formulas.insert(len(formulas.columns) - 2, 'prob', log_reg.predict_proba(X)[:, 1])

print()
for i in range(1, -1, -1):
    include = formulas.in_proof == i
    p = geo_mean(formulas[include].prob, sample_weights[include])
    s = 'in proof' if i == 1 else 'not in proof'
    print(f'average prob ({s}) = {p:.3f}')

print()
feature_coefs = list(zip(log_reg.feature_names_in_, log_reg.coef_[0]))
for feature, coef in feature_coefs:
    print(f'{feature}: {coef:.3f}')

intercept = log_reg.intercept_[0]
print(f'\nintercept: {intercept:.3f}')

def format_num(n):
    return f'+ {n:.2f}' if n >= 0 else f'- {-n:.2f}'

def format_feature(f):
    if f.startswith('is_'):
        return f'b(f.orig = "{f.removeprefix('is_')}")'
    else:
        return f'f.{f}'

factor = 10
cost = ([f'{- intercept / factor:.2f}'] +
        [format_num(- coef / factor) + ' * ' + format_feature(feature)
            for feature, coef in feature_coefs if feature != 'id' and coef != 0.0])
print('\ncost = ' + '\n      '.join(cost))

formulas.to_csv('generated_out.csv', float_format = '%.3f')
