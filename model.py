import numpy as np
import pandas as pd
from sklearn.linear_model import LogisticRegression

def geo_mean(iterable):
    return np.exp(np.log(iterable).mean())

formulas = pd.read_csv('generated.csv')

counts = formulas.loc[:, 'theorem' : 'id'].groupby('theorem').size()
thm_weights = 1000 / counts
thm_weights.name = 'sample_weight'
sample_weights = \
    pd.merge(formulas.theorem, thm_weights, left_on = 'theorem', right_index = True).sample_weight

features = formulas.drop(columns = ['theorem', 'id', 'rule', 'in_proof', 'formula'])
rule = pd.get_dummies(formulas.rule, prefix = 'is')
X = pd.concat([rule, features], axis = 1)

log_reg = LogisticRegression()
log_reg.fit(X, formulas.in_proof, sample_weights)

print(f'penalty = {log_reg.penalty}, regularization constant = {log_reg.C}, ' +
      f'solver = {log_reg.solver}')

formulas.insert(len(formulas.columns) - 2, 'prob', log_reg.predict_proba(X)[:, 1])

print()
for i in range(1, -1, -1):
    p = geo_mean(formulas[formulas.in_proof == i]['prob'])
    s = 'in proof' if i == 1 else 'not in proof'
    print(f'average prob ({s}) = {p:.3f}')

print()
for feature, coef in zip(log_reg.feature_names_in_, log_reg.coef_[0]):
    print(f'{feature}: {coef:.3f}')
print()
print(f'intercept: {log_reg.intercept_[0]:.3f}')

formulas.to_csv('generated_out.csv', float_format = '%.3f')
