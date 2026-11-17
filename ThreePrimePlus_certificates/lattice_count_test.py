"""Numerical test of: if S = Gamma ∩ K (K convex of area A, Gamma of covolume D) is not collinear, then |S| <= 2A/D + 2.
Random integer lattices (basis (a,b),(c,d), covolume |ad-bc| >= 1), random thin or fat parallelograms/triangles K."""
import random, math
random.seed(1)
worst = 0.0
viol = 0
trials = 0
def area_poly(P):
    s = 0.0
    for i in range(len(P)):
        x1, y1 = P[i]; x2, y2 = P[(i + 1) % len(P)]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2
def inside(P, pt):
    sgn = 0
    for i in range(len(P)):
        x1, y1 = P[i]; x2, y2 = P[(i + 1) % len(P)]
        cr = (x2 - x1) * (pt[1] - y1) - (y2 - y1) * (pt[0] - x1)
        s = (cr > 1e-12) - (cr < -1e-12)
        if s != 0:
            if sgn == 0: sgn = s
            elif s != sgn: return False
    return True
for _ in range(600):
    while True:
        a, b, c, d = [random.randint(-6, 6) for _ in range(4)]
        D = abs(a * d - b * c)
        if D >= 1: break
    # convex set: parallelogram with long side L and width w, random orientation
    L = random.choice([5, 12, 25, 40]); w = random.choice([0.05, 0.3, 1.0, 3.0]) / random.choice([1, 2, 5])
    th = random.uniform(0, math.pi)
    ux, uy = math.cos(th), math.sin(th); vx, vy = -uy, ux
    cx, cy = random.uniform(-3, 3), random.uniform(-3, 3)
    P = [(cx - L * ux - w * vx, cy - L * uy - w * vy), (cx + L * ux - w * vx, cy + L * uy - w * vy),
         (cx + L * ux + w * vx, cy + L * uy + w * vy), (cx - L * ux + w * vx, cy - L * uy + w * vy)]
    A = area_poly(P)
    pts = []
    R = int(L * 2 + 10)
    # enumerate lattice points i*(a,b)+j*(c,d) in a window
    for i in range(-2 * R, 2 * R + 1):
        for j in range(-2 * R, 2 * R + 1):
            x = i * a + j * c; y = i * b + j * d
            if abs(x) > 2 * L + 8 or abs(y) > 2 * L + 8: continue
            if inside(P, (x, y)): pts.append((x, y))
    pts = list(set(pts))
    if len(pts) < 3: continue
    p0 = pts[0]
    col = all(abs((q[0] - p0[0]) * (pts[1][1] - p0[1]) - (q[1] - p0[1]) * (pts[1][0] - p0[0])) < 1e-9 for q in pts)
    if col: continue
    trials += 1
    bound = 2 * A / D + 2
    worst = max(worst, len(pts) / bound)
    if len(pts) > bound + 1e-9: viol += 1
print("non-collinear trials:", trials, " violations:", viol, " max |S|/bound = %.3f" % worst)
