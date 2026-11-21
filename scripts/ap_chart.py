"""Draw docs/hero.png: the coefficients a_p of the curve y^2 = x^3 - 432.

Needs matplotlib (pip install matplotlib). Run from the repo root:

    python3 scripts/ap_chart.py

a_p = p + 1 - N_p, where N_p counts the solutions (x, y) mod p plus the point
at infinity. Lean proves a_p = 0 for every prime p = 2 mod 3 other than 2
(BSD/ in this repo); the chart shows that row of zeros next to the primes
p = 1 mod 3, which stay inside the Hasse bound |a_p| <= 2 sqrt(p).
Primes 2 and 3 divide the discriminant (bad reduction) and are left out.
"""

from math import sqrt
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

BOUND = 400
OUT = Path(__file__).resolve().parent.parent / "docs" / "hero.png"

# Greys only, on white: the two groups of primes differ in lightness and in
# marker shape, so the chart reads without colour.
INK = "#030303"
GRAY = "#5c5c5c"
RULE = "#bdbdbd"
QUIET = "#9a9a9a"


def primes_below(n):
    sieve = bytearray([1]) * n
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(n) if sieve[i]]


def a_p(p):
    """p + 1 - N_p by counting every pair (x, y) mod p with y^2 = x^3 - 432."""
    roots = [0] * p  # roots[r] = number of y with y^2 = r mod p
    for y in range(p):
        roots[y * y % p] += 1
    affine = sum(roots[(x * x * x - 432) % p] for x in range(p))
    return p + 1 - (affine + 1)


SANITY = {5: 0, 7: -1, 13: 5, 19: -7, 31: -4}
for q, want in SANITY.items():
    got = a_p(q)
    assert got == want, f"a_{q} = {got}, expected {want}"

primes = [p for p in primes_below(BOUND) if p >= 5]
values = {p: a_p(p) for p in primes}
two = [p for p in primes if p % 3 == 2]
one = [p for p in primes if p % 3 == 1]
assert all(values[p] == 0 for p in two), "a_p should vanish at p = 2 mod 3"
assert all(values[p] != 0 for p in one), "a nonzero a_p was expected at p = 1 mod 3"
assert all(abs(values[p]) <= 2 * sqrt(p) for p in primes), "Hasse bound broken"

print("sanity:", ", ".join(f"a_{q} = {SANITY[q]}" for q in SANITY))
print(
    f"{len(primes)} primes in [5, {BOUND}): {len(two)} with p = 2 mod 3, all a_p = 0;"
    f" {len(one)} with p = 1 mod 3, all nonzero, max |a_p| / 2 sqrt(p) ="
    f" {max(abs(values[p]) / (2 * sqrt(p)) for p in one):.3f}"
)

plt.rcParams.update(
    {
        "font.family": ["STIX Two Text", "STIXGeneral", "serif"],
        "mathtext.fontset": "stix",
        "font.size": 11,
        "axes.edgecolor": RULE,
        "axes.linewidth": 0.8,
        "xtick.color": GRAY,
        "ytick.color": GRAY,
        "xtick.major.size": 0,
        "ytick.major.size": 0,
        "xtick.major.pad": 6,
        "ytick.major.pad": 6,
    }
)

fig, ax = plt.subplots(figsize=(8.2, 3.9), dpi=200)
fig.subplots_adjust(left=0.065, right=0.68, top=0.94, bottom=0.12)

# Hasse envelope: a thin quiet curve.
xs = [5 + i * (BOUND - 5) / 400 for i in range(401)]
for sign in (1, -1):
    ax.plot(xs, [sign * 2 * sqrt(x) for x in xs], color=QUIET, lw=0.8, zorder=1)

# p = 1 mod 3: hollow grey squares.
ax.scatter(
    one,
    [values[p] for p in one],
    marker="s",
    s=26,
    facecolors="white",
    edgecolors=GRAY,
    linewidths=1.0,
    zorder=3,
)
# p = 2 mod 3: filled ink circles, every one on the axis.
ax.axhline(0, color=RULE, lw=0.8, zorder=0)
ax.scatter(two, [0] * len(two), marker="o", s=26, color=INK, linewidths=0, zorder=4)

top = 2 * sqrt(BOUND)
ax.set_xlim(0, BOUND)
ax.set_ylim(-top * 1.08, top * 1.08)
ax.set_xticks(range(0, BOUND + 1, 100))
ax.set_yticks([-40, -20, 0, 20, 40])
ax.set_yticklabels(["−40", "−20", "0", "20", "40"])
for side in ("top", "right"):
    ax.spines[side].set_visible(False)
ax.spines["left"].set_visible(False)
ax.spines["bottom"].set_visible(False)
ax.set_xlabel("prime $p$", color=GRAY, labelpad=4)
ax.text(-0.065, 1.0, "$a_p$", transform=ax.transAxes, color=GRAY, ha="left", va="bottom")

# Direct labels in the right margin, each beside the thing it names.
lab = dict(transform=ax.transData, clip_on=False, va="center")
gx = BOUND + 14
ax.scatter([gx], [0], marker="o", s=26, color=INK, clip_on=False, zorder=4)
ax.text(gx + 9, 2.9, "$p \\equiv 2$ mod 3:  $a_p = 0$", color=INK, **lab)
ax.text(gx + 9, -3.3, "proved for every such prime", color=INK, **lab)

ya = 21
ax.scatter([gx], [ya], marker="s", s=26, facecolors="white", edgecolors=GRAY,
           linewidths=1.0, clip_on=False, zorder=4)
ax.text(gx + 9, ya, "$p \\equiv 1$ mod 3", color=GRAY, **lab)

ax.text(gx - 4, top, "Hasse bound $+2\\sqrt{p}$", color=GRAY, **lab)
ax.text(gx - 4, -top, "Hasse bound $-2\\sqrt{p}$", color=GRAY, **lab)

OUT.parent.mkdir(parents=True, exist_ok=True)
fig.savefig(OUT, facecolor="white")
print(f"wrote {OUT.relative_to(Path.cwd()) if OUT.is_relative_to(Path.cwd()) else OUT}")
