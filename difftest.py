#!/usr/bin/env python3
# Independent differential test of the extracted geofence (difftest.ml).
#
# Generates a deterministic pseudo-random sweep of positions across the region,
# converts each to a rational ECEF direction, and computes the verdict with an
# independent reimplementation of the kernel decision procedure in exact Python
# Fractions.  It then feeds the same rationals to the extracted OCaml binary
# (./difftest) and checks that every extracted verdict, committed flag, and
# clearance_pos flag agrees.  Because both sides see the same exact rationals,
# any disagreement is an extraction fault.  Exits nonzero on any mismatch.

import math, random, subprocess, sys
from fractions import Fraction as F

def mk(x, y, z): return (F(x), F(y), F(z))

# The four agreed MBL points, exactly as in naqoura_line.v.
p1 = mk('3240185/4725163', '2048242/4257979', '573521/1049942')
p2 = mk('6046041/8816135', '1395546/2902183', '2728844/4994991')
p3 = mk('4892447/7125214', '4396228/9183773', '11386631/20810622')
p4 = mk('1935291/2792834', '1089867/2352157', '360157/652002')

def dot(a, b): return a[0]*b[0] + a[1]*b[1] + a[2]*b[2]
def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def merid(p): return (-p[1], p[0], F(0))

ns1, ns2, ns3 = cross(p1, p2), cross(p2, p3), cross(p3, p4)

def east_of(p, X): return dot(merid(p), X) >= 0      # Lt -> false, else true
def west_of(p, X): return dot(merid(p), X) <= 0      # Gt -> false, else true
def in_band(pw, pe, X): return east_of(pw, X) and west_of(pe, X)

def verdict(n, X):
    d = dot(n, X)
    return 'Israeli' if d > 0 else ('Lebanese' if d < 0 else 'Indeterminate')

def decide(X):
    if in_band(p2, p1, X): return verdict(ns1, X)
    if in_band(p3, p2, X): return verdict(ns2, X)
    if in_band(p4, p3, X): return verdict(ns3, X)
    return 'Indeterminate'

def to_rat_ecef(lat_deg, lon_deg):
    la, lo = math.radians(lat_deg), math.radians(lon_deg)
    comps = (math.cos(la)*math.cos(lo), math.cos(la)*math.sin(lo), math.sin(la))
    return tuple(F(round(c * 10**9), 10**9) for c in comps)

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 50000
    rng = random.Random(20221027)
    pts = []
    # A wide sweep of the region: in-band both sides plus out-of-band landward
    # of P1 and seaward of P4 (Indeterminate).
    for _ in range(n):
        pts.append(to_rat_ecef(rng.uniform(31.0, 35.5), rng.uniform(32.0, 36.5)))
    # Structured edge cases: the agreed points themselves and on-segment
    # midpoints (each lies on its segment's great circle -> Indeterminate).
    def vadd(a, b): return (a[0]+b[0], a[1]+b[1], a[2]+b[2])
    pts += [p1, p2, p3, p4, vadd(p1, p2), vadd(p2, p3), vadd(p3, p4),
            (F(0), F(0), F(-1)), (F(0), F(0), F(1))]

    lines = []
    for c in pts:
        f = []
        for q in c:
            f += [str(q.numerator), str(q.denominator)]
        lines.append(' '.join(f))
    inp = '\n'.join(lines) + '\n'

    proc = subprocess.run(['./difftest'], input=inp, capture_output=True, text=True)
    if proc.returncode != 0:
        print('difftest binary failed:', proc.stderr); sys.exit(2)
    out = proc.stdout.split('\n')

    mism = 0
    for c, o in zip(pts, out):
        exp = decide(c)
        expc = (exp != 'Indeterminate')
        got = o.split()
        if (len(got) != 3 or got[0] != exp
                or (got[1] == 'true') != expc or (got[2] == 'true') != expc):
            mism += 1
            if mism <= 8:
                print('MISMATCH at', tuple(str(q) for q in c), 'expected',
                      exp, expc, 'got', got)
    total = len(pts)
    print(f'{total - mism}/{total} positions: extracted verdicts match the '
          f'independent oracle')
    sys.exit(1 if mism else 0)

if __name__ == '__main__':
    main()
