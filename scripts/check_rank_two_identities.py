#!/usr/bin/env python3
"""verify_n2.py -- Exact symbolic verification for the n = 2 frame-dependent
twist theorem (the qubit-boundary theorem) of "A Classification of Sequential
Products on Simple Euclidean Jordan Algebras of Rank >= 3".

All checks are exact (SymPy symbols / rational arithmetic; no floating point).
The product under test is

    a o b := a^{1/2 + i t(a)} b a^{1/2 - i t(a)},      0^z := 0,

on M_2(C)^sa, where t(a) depends only on the unordered spectral frame of a
(t(a) := (2 tr(P R) - 1)^2 for a fixed rank-one projection R), and t(a) := 0
on scalar effects.  Each numbered check below is cited from the proof of the
qubit-boundary theorem in main.tex.

Run:  python3 verify_n2.py   (exits 0 and prints PASS lines iff all checks pass)
"""

import sys
import sympy as sp

FAILURES = []


def check(name, condition):
    if condition:
        print(f"PASS  {name}")
    else:
        print(f"FAIL  {name}")
        FAILURES.append(name)


def iszero(e):
    """True iff the sympy expression simplifies to 0 (exact).

    Complex powers are rewritten in exp/log form first so that identities
    like x^{1/2+it} conj(x^{1/2+it}) = x (x > 0, t real) resolve exactly.
    """
    return sp.simplify(sp.expand(e.rewrite(sp.exp))) == 0


def zeromat(M):
    """True iff the sympy Matrix M simplifies to the zero matrix (exact)."""
    return all(iszero(e) for e in M)


I = sp.I
half = sp.Rational(1, 2)

# Symbols. Eigenvalues positive, twist parameters real, matrix entries real.
x, y = sp.symbols('x y', positive=True)
a1, a2, b1, b2 = sp.symbols('alpha1 alpha2 beta1 beta2', positive=True)
t, s, u = sp.symbols('t s u', real=True)
lam = sp.symbols('lambda', positive=True)
b11, b22, c11, c22 = sp.symbols('b11 b22 c11 c22', real=True)
br, bi, cr, ci = sp.symbols('br bi cr ci', real=True)
w = br + I * bi          # generic off-diagonal complex entry of b
v = cr + I * ci          # generic off-diagonal complex entry of c

B = sp.Matrix([[b11, w], [sp.conjugate(w), b22]])   # generic Hermitian b
C = sp.Matrix([[c11, v], [sp.conjugate(v), c22]])   # generic Hermitian c


def Fdiag(e1, e2, tw):
    """F_a = a^{1/2 + i tw} for a = diag(e1, e2); 0^z := 0 (exact)."""
    z1 = 0 if e1 == 0 else e1 ** (half + I * tw)
    z2 = 0 if e2 == 0 else e2 ** (half + I * tw)
    return sp.Matrix([[z1, 0], [0, z2]])


def prod_diag(e1, e2, tw, M):
    """a o M for a = diag(e1, e2) carrying twist tw."""
    F = Fdiag(e1, e2, tw)
    return F * M * F.H


# ---------------------------------------------------------------------------
# 1. Block normal form (proof step (i)): in a's eigenbasis, a o b has diagonal
#    blocks x*b11, y*b22 and off-diagonal coefficient sqrt(xy) e^{i t log(x/y)}.
# ---------------------------------------------------------------------------
AB = prod_diag(x, y, t, B)
target = sp.Matrix([
    [x * b11, sp.sqrt(x * y) * sp.exp(I * t * sp.log(x / y)) * w],
    [sp.sqrt(x * y) * sp.exp(-I * t * sp.log(x / y)) * sp.conjugate(w), y * b22]])
check("1. block normal form E(x,y) = sqrt(xy) exp(i t log(x/y)) on the 1-space",
      zeromat(AB - target))

# ---------------------------------------------------------------------------
# 2. Scalar effects are twist-invisible: (lam*Id) o b = lam*b for every t;
#    hence the value of tau on scalar effects is immaterial and any refinement
#    of a degenerate resolution computes the same value (decomposition
#    independence at the coalescence point E(lam, lam) = lam*Id).
# ---------------------------------------------------------------------------
check("2a. scalar invisibility (lam*Id) o b = lam*b, any twist",
      zeromat(prod_diag(lam, lam, t, B) - lam * B))
check("2b. unitality Id o b = b, any twist",
      zeromat(prod_diag(1, 1, t, B) - B))

# ---------------------------------------------------------------------------
# 3. Rank-deficient first argument: a = diag(x, 0) gives the Lueders value
#    x * P b P independent of the twist.
# ---------------------------------------------------------------------------
P0 = sp.Matrix([[1, 0], [0, 0]])
check("3. rank-one a: a o b = x * PbP, twist-independent",
      zeromat(prod_diag(x, 0, t, B) - x * (P0 * B * P0)))

# ---------------------------------------------------------------------------
# 4. Trace identities behind the compatibility lemma.
# 4a. tr((a o b) a) = tr(a^2 b) for every twist (full rank and rank-one).
# ---------------------------------------------------------------------------
A_full = sp.Matrix([[x, 0], [0, y]])
lhs = sp.trace(prod_diag(x, y, t, B) * A_full)
rhs = sp.trace(A_full ** 2 * B)
check("4a. tr((a o b) a) = tr(a^2 b), full rank", iszero(lhs - rhs))
A_sing = sp.Matrix([[x, 0], [0, 0]])
lhs_s = sp.trace(prod_diag(x, 0, t, B) * A_sing)
rhs_s = sp.trace(A_sing ** 2 * B)
check("4a'. tr((a o b) a) = tr(a^2 b), rank one", iszero(lhs_s - rhs_s))

# ---------------------------------------------------------------------------
# 4b. In b's eigenbasis (b = diag(m1, m2), m1, m2 > 0), with a the generic
#     Hermitian matrix C above:
#     tr(b a^2) - tr((b o a) a) = (m1 + m2 - 2 sqrt(m1 m2) cos(t log(m1/m2))) |a12|^2
# ---------------------------------------------------------------------------
m1, m2 = sp.symbols('m1 m2', positive=True)
Bd = sp.Matrix([[m1, 0], [0, m2]])
lhs4b = sp.trace(Bd * C ** 2) - sp.trace(prod_diag(m1, m2, t, C) * C)
target4b = (m1 + m2 - 2 * sp.sqrt(m1 * m2) * sp.cos(t * sp.log(m1 / m2))) * (cr**2 + ci**2)
check("4b. tr(b a^2) - tr((b o a) a) = (m1+m2-2 sqrt(m1 m2) cos th)|a12|^2",
      iszero(lhs4b - target4b))

# 4b'. Singular b = diag(m1, 0): difference = m1 |a12|^2.
Bd0 = sp.Matrix([[m1, 0], [0, 0]])
lhs4b0 = sp.trace(Bd0 * C ** 2) - sp.trace(prod_diag(m1, 0, t, C) * C)
check("4b'. singular b: tr(b a^2) - tr((b o a) a) = m1 |a12|^2",
      iszero(lhs4b0 - m1 * (cr**2 + ci**2)))

# ---------------------------------------------------------------------------
# 4c. AM-GM decomposition: m1 + m2 - 2 sqrt(m1 m2) cos th
#       = (sqrt m1 - sqrt m2)^2 + 2 sqrt(m1 m2) (1 - cos th),
#     a sum of two nonnegative terms, the first zero iff m1 = m2.
# ---------------------------------------------------------------------------
th = sp.symbols('theta', real=True)
dec = (m1 + m2 - 2 * sp.sqrt(m1 * m2) * sp.cos(th)
       - (sp.sqrt(m1) - sp.sqrt(m2)) ** 2
       - 2 * sp.sqrt(m1 * m2) * (1 - sp.cos(th)))
check("4c. AM-GM decomposition identity", sp.simplify(dec) == 0)

# ---------------------------------------------------------------------------
# 5. Phase cocycle on commuting pairs: F_a F_b = zeta * F_{ab}, |zeta| = 1.
# 5a. Shared frame, equal twists (both nonscalar, ab nonscalar): zeta = 1.
# ---------------------------------------------------------------------------
FaFb = Fdiag(a1, a2, t) * Fdiag(b1, b2, t)
Fab = Fdiag(a1 * b1, a2 * b2, t)
check("5a. cocycle, shared frame, equal twists: F_a F_b = F_{ab}",
      zeromat(FaFb - Fab))

# 5b. b scalar (tau(b) = 0 by convention), a nonscalar with twist s:
#     F_a F_b = beta^{-i s} F_{beta a}, unimodular scalar.
beta = sp.symbols('beta', positive=True)
FaFb2 = Fdiag(a1, a2, s) * (sp.sqrt(beta) * sp.eye(2))
Fab2 = Fdiag(beta * a1, beta * a2, s)
zeta = beta ** (-I * s)
check("5b. cocycle, scalar b: F_a F_b = beta^{-is} F_{beta a}",
      zeromat(FaFb2 - zeta * Fab2))
check("5b'. |zeta| = 1", sp.simplify(zeta * sp.conjugate(zeta)) == 1)

# 5c. Zero eigenvalues: a = diag(a1, 0), b = diag(b1, b2) shared frame:
#     F_a F_b = F_{ab} still (both sides kill the second slot).
check("5c. cocycle with zero eigenvalue: F_a F_b = F_{ab}",
      zeromat(Fdiag(a1, 0, t) * Fdiag(b1, b2, t) - Fdiag(a1 * b1, 0, t)))

# 5d. ab scalar with a, b nonscalar sharing the frame (a1 b1 = a2 b2 = g > 0):
#     then F_a F_b is the scalar g^{1/2} e^{i t log g} Id (proof: substitute
#     b2 = a1 b1 / a2), so Ad(F_a F_b) = g * Id = Ad(F_{ab}) trivially.
g = a1 * b1
FaFb3 = Fdiag(a1, a2, t) * Fdiag(b1, a1 * b1 / a2, t)
scalar = sp.sqrt(g) * sp.exp(I * t * sp.log(g))
check("5d. ab scalar: F_a F_b = g^{1/2} e^{i t log g} Id",
      zeromat(FaFb3 - scalar * sp.eye(2)))

# ---------------------------------------------------------------------------
# 6. S5 across the compatible cases (compatible = commuting; shared frame
#    carries a single twist value because tau is a frame function).
# 6a. Both nonscalar, shared frame, full rank: a o (b o c) = (ab) o c.
# ---------------------------------------------------------------------------
lhs6 = prod_diag(a1, a2, t, prod_diag(b1, b2, t, C))
rhs6 = prod_diag(a1 * b1, a2 * b2, t, C)
check("6a. S5, shared frame, full rank", zeromat(lhs6 - rhs6))

# 6b. Rank-deficient: a = diag(a1, 0), b = diag(b1, b2) shared frame.
lhs6b = prod_diag(a1, 0, t, prod_diag(b1, b2, t, C))
rhs6b = prod_diag(a1 * b1, 0, t, C)
check("6b. S5, zero eigenvalue in a", zeromat(lhs6b - rhs6b))

# 6c. b scalar: a o (beta c) = (beta a) o c  (twists s vs s: tau(beta*a)=tau(a)).
lhs6c = prod_diag(a1, a2, s, beta * C)
rhs6c = prod_diag(beta * a1, beta * a2, s, C)
check("6c. S5, scalar b", zeromat(lhs6c - rhs6c))

# 6d. a scalar: alpha (b o c) = (alpha b) o c.
alpha = sp.symbols('alpha', positive=True)
lhs6d = alpha * prod_diag(b1, b2, t, C)
rhs6d = prod_diag(alpha * b1, alpha * b2, t, C)
check("6d. S5, scalar a", zeromat(lhs6d - rhs6d))

# 6e. ab scalar (b2 = a1*b1/a2): a o (b o c) = (ab) o c = a1 b1 c.
lhs6e = prod_diag(a1, a2, t, prod_diag(b1, a1 * b1 / a2, t, C))
check("6e. S5, ab scalar", zeromat(lhs6e - a1 * b1 * C))

# ---------------------------------------------------------------------------
# 7. Compatibility (backward direction): commuting effects are compatible.
#    Shared frame: a o b = ab = ba = b o a.
# ---------------------------------------------------------------------------
Bcomm = sp.Matrix([[b1, 0], [0, b2]])
check("7a. commuting => compatible (shared frame): a o b = b o a",
      zeromat(prod_diag(a1, a2, t, Bcomm) - prod_diag(b1, b2, t, sp.Matrix([[a1, 0], [0, a2]]))))
check("7b. scalar a compatible with every b: b o (lam Id) = lam b",
      zeromat(prod_diag(x, y, t, lam * sp.eye(2)) - lam * sp.Matrix([[x, 0], [0, y]])))

# ---------------------------------------------------------------------------
# 8. S4 instances: orthogonal supports annihilate in both orders; and a
#    noncommuting witness where the product is nonzero.
# ---------------------------------------------------------------------------
a_S4 = sp.Matrix([[sp.Rational(1, 2), 0], [0, 0]])
b_S4 = sp.Matrix([[0, 0], [0, sp.Rational(1, 3)]])
Fa_S4 = Fdiag(sp.Rational(1, 2), 0, sp.Rational(1, 4))
Fb_S4 = Fdiag(sp.Rational(1, 3), 0, sp.Rational(3, 4))  # in b's frame; reversed basis
# a o b in the standard basis:
check("8a. S4 instance: a o b = 0",
      zeromat(Fa_S4 * b_S4 * Fa_S4.H))
# b o a: compute in b's eigenbasis (swap basis): b = diag(1/3, 0) there, a = diag(0, 1/2).
a_swapped = sp.Matrix([[0, 0], [0, sp.Rational(1, 2)]])
check("8b. S4 instance: b o a = 0",
      zeromat(Fb_S4 * a_swapped * Fb_S4.H))
X_pauli = sp.Matrix([[0, 1], [1, 0]])
Fa_fr = Fdiag(1, sp.Rational(1, 4), 1)  # full-rank a = diag(1, 1/4), twist 1
check("8c. noncommuting witness: a o X != 0 (full-rank a)",
      not zeromat(Fa_fr * X_pauli * Fa_fr.H))

# ---------------------------------------------------------------------------
# 9. Frame dependence of tau for R = diag(1, 0):
#    tau = (2 tr(PR) - 1)^2 equals 1 on the standard frame and 0 on the
#    Hadamard frame; and tau is invariant under P <-> Id - P.
# ---------------------------------------------------------------------------
R = sp.Matrix([[1, 0], [0, 0]])
P_std = sp.Matrix([[1, 0], [0, 0]])
P_had = sp.Rational(1, 2) * sp.Matrix([[1, 1], [1, 1]])


def tau_of(P):
    return (2 * sp.trace(P * R) - 1) ** 2


check("9a. tau(standard frame) = 1", sp.simplify(tau_of(P_std) - 1) == 0)
check("9b. tau(Hadamard frame) = 0", sp.simplify(tau_of(P_had)) == 0)
# 9c. General symbolic rank-one projection: P parametrized by
#     P = [[p, w], [conj(w), 1-p]] with p real in [0,1] and |w|^2 = p(1-p)
#     (every rank-one projection in M_2(C) has this form).  The identity
#     tau(Id-P) = tau(P) reduces to (2(1-x)-1)^2 = (2x-1)^2 with
#     x = tr(PR); we verify it on the general parametrized P.
p_sym = sp.Symbol('p', real=True)
u_sym, v_sym = sp.symbols('u v', real=True)  # w = u + i v
w_sym = u_sym + sp.I * v_sym
P_gen = sp.Matrix([[p_sym, w_sym], [sp.conjugate(w_sym), 1 - p_sym]])
check("9c. tau invariant under P <-> Id-P (general symbolic P)",
      sp.simplify(sp.expand(tau_of(P_gen) - tau_of(sp.eye(2) - P_gen))) == 0)

# 9d. The product genuinely differs from Lueders on the tau = 1 frame:
#     a = diag(1, 1/4): off-diagonal phase e^{i log 4} != 1 (0 < log 4 < 2 pi).
a9 = prod_diag(1, sp.Rational(1, 4), 1, X_pauli)
lueders9 = sp.Matrix([[0, sp.Rational(1, 2)], [sp.Rational(1, 2), 0]])
check("9d. tau=1 frame: a o X != sqrt(a) X sqrt(a)",
      not zeromat(a9 - lueders9))
check("9d'. 0 < log 4 < 2 pi (exact)",
      bool(sp.log(4) > 0) and bool(sp.log(4) < 2 * sp.pi))
# 9e. And on the tau = 0 (Hadamard) frame the product IS Lueders:
#     a = P_had + (1/4)(Id - P_had); twist 0 => a o b = sqrt(a) b sqrt(a).
a_had = P_had + sp.Rational(1, 4) * (sp.eye(2) - P_had)
sqrt_a_had = P_had + sp.Rational(1, 2) * (sp.eye(2) - P_had)
F_had = 1 * P_had + sp.Rational(1, 4) ** half * (sp.eye(2) - P_had)  # twist 0
check("9e. tau=0 frame: a o b = sqrt(a) b sqrt(a)",
      zeromat(F_had * B * F_had.H - sqrt_a_had * B * sqrt_a_had))

# ---------------------------------------------------------------------------
# 10. Calculus constant in the continuity estimate:
#     sup_{x in (0,1]} sqrt(x) |log x| = 2/e, attained at x = e^{-2}.
# ---------------------------------------------------------------------------
xx = sp.symbols('xx', positive=True)
f10 = sp.sqrt(xx) * (-sp.log(xx))
crit = sp.solve(sp.diff(f10, xx), xx)
check("10a. unique critical point at x = e^{-2}",
      crit == [sp.exp(-2)])
check("10b. value at critical point = 2/e",
      sp.simplify(f10.subs(xx, sp.exp(-2)) - 2 / sp.E) == 0)
check("10c. boundary values: f(1) = 0 and lim_{x->0+} f = 0",
      f10.subs(xx, 1) == 0 and sp.limit(f10, xx, 0, '+') == 0)

# ---------------------------------------------------------------------------
print()
if FAILURES:
    print(f"{len(FAILURES)} CHECK(S) FAILED: {FAILURES}")
    sys.exit(1)
print("ALL CHECKS PASSED (exact symbolic arithmetic; no floating point).")
sys.exit(0)
