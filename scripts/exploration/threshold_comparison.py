"""Compare the certificate threshold c* with the threshold of the certificate-free reverse-block condition."""
import warnings, numpy as np
from cert_sdp import *
from reverse_block_condition import rmin
warnings.filterwarnings("ignore")
print("Is the certificate threshold the same as the threshold of the certificate-free condition?")
print("For fixed L (a = 1/x) the certificate exists iff c >= c*, with c* from the SDP.")
for d, alist in ((4, (1.5, 1.7435, 2.5)), (5, (1.4, 1.6864, 2.2)), (6, (1.6519,))):
    red = Reduced(d)
    for a in alist:
        st, mu, cstar, g = solve(red, a, 0.0, allow_g=False)
        x = 1 / a
        vals = [rmin(d, x, float(cstar) * f, restarts=(12 if d < 6 else 6), iters=200) for f in (0.97, 1.0, 1.03)]
        print(f"  d={d} a={a}: c*={float(cstar):.5f}  condition minimum at 0.97c*, c*, 1.03c*: " + ", ".join(f"{v:+.5f}" for v in vals), flush=True)
