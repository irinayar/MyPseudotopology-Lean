"""Numerical checks of two lemmas used in TVGplus_v42, Theorem "Finite prime families":
(1) Lemma window-positive: w_D(t) = (1 - D^2 t^2)_+^2, kappa_Q(r) = |W_Q(r)|^2 / (Q m_Q)^2.  Check kappa(0) = 1, sum kappa <= B_D = 30D/7,
    kappa(r) <= V_2^2 / (64 I_1^2 r^4) with V_2 = 32 D / (3 sqrt 3), I_1 = 16/(15 D), the tail bound sum_{|r|>u} kappa <= A_D u^-3,
    and nonnegativity of the Fourier coefficients of K_Q (finite autocorrelations).
(2) Lemma random-transfer: f of period P, Q = alpha P, g_tau(x) = f(x - tau) w_D(x/Q).  Check E_tau |a_new(j)|^2 = sum_l kappa_Q(j - alpha l) |a(l)|^2
    (a(l) = fhat(l)/Z, Z_new = alpha m_Q Z) and the mass estimate |S_new / (alpha m_Q S) - 1| <= 4 / (alpha m_Q) for every tau."""
import cmath, math, random
random.seed(5)
D = 3
def w(t):
    t = t - round(t)
    return (1 - D * D * t * t) ** 2 if abs(t) <= 1 / D else 0.0
def dft(g, Q):
    return [sum(g[x] * cmath.exp(-2j * math.pi * r * x / Q) for x in range(Q)) for r in range(Q)]
# ---- (1)
Q = 600
wx = [w(x / Q) for x in range(Q)]
mQ = sum(wx) / Q
W = dft(wx, Q)
kap = [abs(W[r]) ** 2 / (Q * mQ) ** 2 for r in range(Q)]
V2 = 32 * D / (3 * math.sqrt(3)); I1 = 16 / (15 * D); BD = 30 * D / 7
AD = max(BD, V2 ** 2 / (24 * I1 ** 2))
print("(1) Q=%d D=%d: kappa(0)=%.6f  sum kappa=%.4f (B_D=%.3f)" % (Q, D, kap[0], sum(kap), BD))
viol = 0
for r in range(1, Q // 2 + 1):
    if kap[r] > V2 ** 2 / (64 * I1 ** 2 * r ** 4) * (1 + 1e-9): viol += 1
print("    pointwise bound kappa(r) <= V2^2/(64 I1^2 r^4): violations", viol)
bal = [(r if r <= Q // 2 else r - Q, kap[r]) for r in range(Q)]
worst = 0.0
for u in (0.5, 1, 2, 3, 5, 8, 13, 21, 34, 55):
    tail = sum(k for rr, k in bal if abs(rr) > u)
    worst = max(worst, tail * u ** 3 / AD)
print("    tail sum_{|r|>u} kappa <= A_D u^-3: max ratio %.4f (A_D=%.3f)" % (worst, AD))
auto = [sum(wx[x] * wx[(x + t) % Q] for x in range(Q)) for t in range(Q)]
print("    Fourier coefficients of K_Q (autocorrelation) min = %.3e (>= 0)" % min(auto))
# ---- (2)
P, alpha = 16, 16
Qn = P * alpha
f = [random.random() ** 3 for _ in range(P)]
S = sum(f)
fh = [sum(f[x] * cmath.exp(-2j * math.pi * l * x / P) for x in range(P)) for l in range(P)]
Z = S
a = [fh[l] / Z for l in range(P)]
wxn = [w(x / Qn) for x in range(Qn)]
mQn = sum(wxn) / Qn
Wn = dft(wxn, Qn)
kapn = [abs(Wn[r]) ** 2 / (Qn * mQn) ** 2 for r in range(Qn)]
Znew = alpha * mQn * Z
lhs = [0.0] * Qn
maxdev = 0.0
for tau in range(P):
    g = [f[(x - tau) % P] * wxn[x] for x in range(Qn)]
    gh = dft(g, Qn)
    Snew = sum(g)
    maxdev = max(maxdev, abs(Snew / (alpha * mQn * S) - 1))
    for j in range(Qn):
        lhs[j] += abs(gh[j] / Znew) ** 2 / P
rhs = [sum(kapn[(j - alpha * l) % Qn] * abs(a[l]) ** 2 for l in range(P)) for j in range(Qn)]
err = max(abs(lhs[j] - rhs[j]) for j in range(Qn))
print("(2) P=%d alpha=%d Q=%d: max_j |E_tau|a_new(j)|^2 - sum_l kappa(j-alpha l)|a(l)|^2| = %.3e (scale %.3e)" % (P, alpha, Qn, err, max(rhs)))
print("    mass estimate: max_tau |S_new/(alpha m_Q S) - 1| = %.4f  <=  4/(alpha m_Q) = %.4f" % (maxdev, 4 / (alpha * mQn)))
