"""Best certified NPT margin of the U(d)-covariant family for d = 3..10 (reproduces the dimension table)."""
import time, warnings, numpy as np
from scipy.optimize import minimize_scalar
from cert_sdp import *
warnings.filterwarnings("ignore")

print("Covariant family (g = h = 0): best certified margin over a, and d*alpha = -d/(d - mu)")
print(" d  vars  maxblock   best a    mu        d*alpha   NPT?   doc table")
doc = {2: -0.4, 3: -0.545046, 4: -0.679007, 5: -0.791950, 6: -0.891714, 7: -0.980181, 8: -1.060754, 9: -1.136173, 10: -1.207814}
reds = {}
for d in range(3, 11):
    t = time.time()
    red = reds[d] = Reduced(d)
    f = lambda a: -solve(red, a, 0.0, allow_g=False)[1]
    grid = np.linspace(1.05, 4.0, 13)
    vals = [f(a) for a in grid]
    k = int(np.argmin(vals))
    lo, hi = grid[max(k - 1, 0)], grid[min(k + 1, len(grid) - 1)]
    res = minimize_scalar(f, bounds=(lo, hi), method="bounded", options={"xatol": 1e-4})
    mu = -res.fun
    print(f"{d:2d}  {red.nvar:4d}  {max(len(r) for r in red.j_blocks):4d}     {res.x:.4f}  {mu:+.5f}  {-d / (d - mu):+.6f}  {'YES' if mu > 1e-7 else 'no '}   {doc.get(d)}   ({time.time() - t:.0f}s)", flush=True)
