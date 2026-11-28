"""Grid scan of the monomial-invariant family (extra diagonal terms g, h). Usage: monomial_family.py d"""
import sys, warnings, numpy as np
from cert_sdp import *
warnings.filterwarnings("ignore")
d = int(sys.argv[1])
red = Reduced(d)
A = [1.005, 1.02, 1.1, 1.3, 1.63, 2.0, 3.0]
H = [0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0]
print(f"d={d}: best margin mu over (c, g, Q); rows a, columns h   [b = e = 1]")
print("  a\\h  " + "".join(f"{h:9.2f}" for h in H))
best = (-1e9, None)
for a in A:
    row = []
    for h in H:
        try:
            s = solve(red, a, h, allow_g=True)
        except Exception:
            s = (None, None, None, None)
        v = s[1] if s[1] is not None else float("nan")
        row.append(v)
        if v == v and v > best[0]: best = (v, (a, h, s[2], s[3]))
    print(f"{a:6.2f} " + "".join(f"{v:+9.3f}" for v in row), flush=True)
print("best:", best)
