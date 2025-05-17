import numpy as np
import pandas as pd
from sklearn.linear_model import LogisticRegression

def geo_mean(iterable):
    return np.exp(np.log(iterable).mean())

formulas = pd.read_csv('generated.csv')
X = formulas.loc[:, 'rule' : 'in_proof'].iloc[:, 1:-1]
y = formulas.loc[:, 'in_proof']

log_reg = LogisticRegression()
log_reg.fit(X, y)
print(f'penalty = {log_reg.penalty}, regularization constant = {log_reg.C}, ' +
      f'solver = {log_reg.solver}')

formulas.insert(len(formulas.columns) - 1, 'prob', log_reg.predict_proba(X)[:, 1])

print()
for i in range(1, -1, -1):
    p = geo_mean(formulas[formulas.in_proof == i]['prob'])
    s = 'in proof' if i == 1 else 'not in proof'
    print(f'average prob ({s}) = {p:.3f}')

print()
for feature, coef in zip(log_reg.feature_names_in_, log_reg.coef_[0]):
    print(f'{feature}: {coef:.3f}')
print()
print(f'intercept: {log_reg.intercept_[0]}')

formulas.to_csv('generated_out.csv', float_format = '%.3f')
