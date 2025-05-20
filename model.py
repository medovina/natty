import sys, warnings

import numpy as np
import pandas as pd
from sklearn.linear_model import LogisticRegression
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler

verbose = 0

for arg in sys.argv[1:]:
    if arg == '-v':
        verbose = 1
    else:
        print(f'usage: {sys.argv[0]} [-v]')
        exit()

def geo_mean(xs, weights):
    return np.exp((np.log(xs) * weights).sum() / weights.sum())

formulas = pd.read_csv('generated.csv', true_values = ['T'], false_values = ['F'])

counts = formulas.loc[:, 'theorem' : 'id'].groupby('theorem').size()
thm_weights = 1000 / counts
thm_weights.name = 'sample_weight'
sample_weights = \
    pd.merge(formulas.theorem, thm_weights, left_on = 'theorem', right_index = True).sample_weight

features = formulas.drop(columns = ['theorem', 'orig', 'in_proof', 'formula'])
orig = pd.get_dummies(formulas.orig, prefix = 'is')
X = pd.concat([orig, features], axis = 1)

scaler = StandardScaler()
log_reg = LogisticRegression(
    solver = 'liblinear', penalty = 'l1', C = 0.02, verbose = verbose)
pipe = make_pipeline(scaler, log_reg)

with warnings.catch_warnings():
    warnings.filterwarnings('error')
    try:
        pipe.fit(X, formulas.in_proof, logisticregression__sample_weight = sample_weights)
    except Warning as w:
        print(w)
        exit()

print(f'penalty = {log_reg.penalty}, regularization constant = {log_reg.C}, ' +
      f'solver = {log_reg.solver}')

formulas.insert(len(formulas.columns) - 2, 'prob', pipe.predict_proba(X)[:, 1])

print()
for i in range(1, -1, -1):
    include = formulas.in_proof == i
    p = geo_mean(formulas[include].prob, sample_weights[include])
    s = 'in proof' if i == 1 else 'not in proof'
    print(f'average prob ({s}) = {p:.3f}')

# get unnormalized coefficients/intercept
coefficients = np.true_divide(log_reg.coef_[0],  scaler.scale_)
intercept = log_reg.intercept_[0] - np.dot(coefficients, scaler.mean_)

print()
feature_coefs = list(zip(X.columns, coefficients))
for feature, coef in feature_coefs:
    print(f'{feature}: {coef:.3f}')

print(f'\nintercept: {intercept:.3f}')

def format_num(n):
    return f'+. {n:.3f}' if n >= 0 else f'-. {-n:.3f}'

def is_boolean(f):
    return isinstance(formulas.loc[0, f], np.bool_)

def format_feature(f):
    if f.startswith('is_'):
        return f'b (f.orig = "{f.removeprefix('is_')}")'
    else:
        conv = 'b' if is_boolean(f) else 'i'
        return f'{conv} f.{f}'

factor = 10
cost = ([f'{- intercept / factor:.3f}'] +
        [format_num(- coef / factor) + ' *. ' + format_feature(feature)
            for feature, coef in feature_coefs if feature != 'id' and coef != 0.0])
print('\ncost:        ' + '\n          '.join(cost))

for c in formulas.columns:
    if is_boolean(c):
        formulas[c] = np.where(formulas[c], 'T', 'F')

formulas.to_csv('generated_out.csv', float_format = '%.3f')
