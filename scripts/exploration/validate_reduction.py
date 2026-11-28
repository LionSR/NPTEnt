"""Cross-check the symmetry-reduced SDP against the unreduced one at d = 3 (slow: about a minute per case)."""
import time, numpy as np
from cert_sdp import *

# 0. margin formula against the state computed directly
d, a, b, h, c, e, g = 5, 1.7, 1.0, -0.3, 0.6, 1.0, -0.2
m0, mc, mg = margin_coeffs(d, a, b, h)
print("margin formula vs direct:", m0 * e + mc * c + mg * g, state_margin_direct(d, a, b, h, c, e, g))

# 1. reduced SDP against the unreduced one at d = 3
red = Reduced(3)
print("d=3: variables", red.nvar, "| J blocks", [len(r) for r in red.j_blocks], "| Gamma blocks", [len(r) for r in red.g_blocks], "| kernel rows", len(red.kernel))
for (a, h, ag) in [(1.6, 0.0, False), (1.6, 0.0, True), (1.6, -0.3, True), (2.2, -0.8, True)]:
    t = time.time(); r1 = solve(red, a, h, allow_g=ag); t1 = time.time() - t
    t = time.time(); r2 = brute(3, a, h, allow_g=ag); t2 = time.time() - t
    print(f"a={a} h={h} g free={ag}: reduced {r1[0]} mu={r1[1]:.6f} c={r1[2]:.5f} g={r1[3]:.5f} ({t1:.1f}s) | brute {r2[0]} mu={r2[1]:.6f} c={r2[2]:.5f} g={r2[3]:.5f} ({t2:.1f}s)")
