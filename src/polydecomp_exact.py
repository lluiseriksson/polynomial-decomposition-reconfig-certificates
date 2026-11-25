"""Exact rational polynomial, Legendre cross-polytope integral, and discrete tomography helpers over Q.

Strictly zero floating-point operations (uses int and fractions.Fraction exclusively).
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple


BivPoly = Dict[Tuple[int, int], Fraction]


def frac_to_canon_str(x: Fraction) -> str:
    if not isinstance(x, Fraction):
        raise TypeError("Expected Fraction")
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator}/{x.denominator}"


def int_gcd(a: int, b: int) -> int:
    x, y = abs(a), abs(b)
    while y:
        x, y = y, x % y
    return x


def int_fact(n: int) -> int:
    res = 1
    for i in range(2, n + 1):
        res *= i
    return res


def int_comb(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    k = min(k, n - k)
    num = 1
    den = 1
    for i in range(1, k + 1):
        num *= n - k + i
        den *= i
    return num // den


def poly_trim_z(p: Sequence[int]) -> List[int]:
    out = list(p)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_add_z(p: Sequence[int], q: Sequence[int]) -> List[int]:
    n = max(len(p), len(q))
    res = [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
    return poly_trim_z(res)


def poly_sub_z(p: Sequence[int], q: Sequence[int]) -> List[int]:
    n = max(len(p), len(q))
    res = [(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)]
    return poly_trim_z(res)


def poly_mul_z(p: Sequence[int], q: Sequence[int]) -> List[int]:
    if not p or not q:
        return [0]
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            out[i + j] += a * b
    return poly_trim_z(out)


def poly_divmod_monic_or_unit_z(dividend: Sequence[int], divisor: Sequence[int]) -> Tuple[List[int], List[int]]:
    """Exact polynomial division in Z[x] when leading coeff of divisor is +-1."""
    num = poly_trim_z(dividend)
    den = poly_trim_z(divisor)
    if den == [0] or den[-1] not in (-1, 1):
        raise ValueError("Divisor must have leading coefficient +-1")
    deg_d = len(den) - 1
    lead = den[-1]
    rem = list(num)
    if len(rem) - 1 < deg_d:
        return [0], rem
    q = [0] * (len(rem) - deg_d)
    for shift in range(len(rem) - deg_d - 1, -1, -1):
        c = rem[shift + deg_d] * lead
        q[shift] = c
        if c != 0:
            for j in range(deg_d + 1):
                rem[shift + j] -= c * den[j]
    return poly_trim_z(q), poly_trim_z(rem)


def poly_deriv_z(p: Sequence[int]) -> List[int]:
    if len(p) <= 1:
        return [0]
    return poly_trim_z([i * p[i] for i in range(1, len(p))])


def poly_eval_z(p: Sequence[int], x: int) -> int:
    acc = 0
    for c in reversed(p):
        acc = acc * x + c
    return acc


def poly_l1_z(p: Sequence[int]) -> int:
    return sum(abs(c) for c in p)


def build_m_basic_poly(sign: int, a: int, m_vec: Sequence[int], a_vec: Sequence[int]) -> List[int]:
    """Construct sign * x^a * prod_i (1 - x^{m_i * a_i}) in Z[x] (ascending powers)."""
    p = [0] * a + [sign]
    for mi, ai in zip(m_vec, a_vec):
        exp = mi * ai
        if exp == 0:
            return [0]
        fac = [1] + [0] * (exp - 1) + [-1]
        p = poly_mul_z(p, fac)
    return poly_trim_z(p)


def build_cyclotomic_poly(m: int) -> List[int]:
    """Exact cyclotomic polynomial Phi_m(x) in Z[x] via x^m - 1 = prod_{d|m} Phi_d(x)."""
    cache: Dict[int, List[int]] = {}
    for k in range(1, m + 1):
        if m % k != 0:
            continue
        p = [-1] + [0] * (k - 1) + [1]
        for d in range(1, k):
            if k % d == 0:
                p, rem = poly_divmod_monic_or_unit_z(p, cache[d])
                if rem != [0]:
                    raise RuntimeError("Cyclotomic division remainder non-zero")
        cache[k] = p
    return cache[m]


def legendre_poly_murphy(n: int) -> List[Fraction]:
    """Exact Legendre polynomial L_n(x) over Q via Murphy's formula (Sec. 1.4)."""
    def _pmul(p: List[Fraction], q: List[Fraction]) -> List[Fraction]:
        out = [Fraction(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                out[i + j] += a * b
        return out

    def _ppow(p: List[Fraction], e: int) -> List[Fraction]:
        r = [Fraction(1)]
        for _ in range(e):
            r = _pmul(r, p)
        return r

    res = [Fraction(0)] * (n + 1)
    den = 1 << n
    for i in range(n + 1):
        c = Fraction(int_comb(n, i) ** 2, den)
        term = _pmul(_ppow([Fraction(-1), Fraction(1)], i), _ppow([Fraction(1), Fraction(1)], n - i))
        for j, val in enumerate(term):
            res[j] += c * val
    return res


def compute_legendre_slice_R(k: int, l: int) -> BivPoly:
    """Exact symbolic bivariate polynomial integration of Keevash-Lim Theorem 1.6 R_l(r, s) = T1+T2+T3+T4."""
    Lkm1 = legendre_poly_murphy(k - 1)

    def _s_density(n: int) -> Dict[Tuple[int, int], Fraction]:
        if n == 0:
            return {}
        Ln = legendre_poly_murphy(n)
        fn = int_fact(n)
        out: Dict[Tuple[int, int], Fraction] = {}
        for j in range(1, n + 1):
            if Ln[j] != 0:
                out[(n - j, j - 1)] = Fraction(j, fn) * Ln[j]
        return out

    Sl = _s_density(l)
    Skl = _s_density(k - l - 1)

    def pm4(P: Dict[Tuple[int, int, int, int], Fraction], Q: Dict[Tuple[int, int, int, int], Fraction]) -> Dict[Tuple[int, int, int, int], Fraction]:
        o: Dict[Tuple[int, int, int, int], Fraction] = {}
        for k1, v1 in P.items():
            for k2, v2 in Q.items():
                kk = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2], k1[3] + k2[3])
                o[kk] = o.get(kk, Fraction(0)) + v1 * v2
        return {kk: v for kk, v in o.items() if v != 0}

    def padd4(*ds: Dict[Tuple[int, int, int, int], Fraction]) -> Dict[Tuple[int, int, int, int], Fraction]:
        o: Dict[Tuple[int, int, int, int], Fraction] = {}
        for d in ds:
            for kk, v in d.items():
                o[kk] = o.get(kk, Fraction(0)) + v
        return {kk: v for kk, v in o.items() if v != 0}

    def ppow4(P: Dict[Tuple[int, int, int, int], Fraction], e: int) -> Dict[Tuple[int, int, int, int], Fraction]:
        r: Dict[Tuple[int, int, int, int], Fraction] = {(0, 0, 0, 0): Fraction(1)}
        for _ in range(e):
            r = pm4(r, P)
        return r

    def sub_var(
        P: Dict[Tuple[int, int, int, int], Fraction],
        var_idx: int,
        sub_poly: Dict[Tuple[int, int, int, int], Fraction],
    ) -> Dict[Tuple[int, int, int, int], Fraction]:
        o: Dict[Tuple[int, int, int, int], Fraction] = {}
        for degs, v in P.items():
            d = degs[var_idx]
            rem = list(degs)
            rem[var_idx] = 0
            term = pm4({(rem[0], rem[1], rem[2], rem[3]): v}, ppow4(sub_poly, d))
            o = padd4(o, term)
        return o

    def integ(
        P: Dict[Tuple[int, int, int, int], Fraction],
        var_idx: int,
        lo_poly: Dict[Tuple[int, int, int, int], Fraction],
        hi_poly: Dict[Tuple[int, int, int, int], Fraction],
    ) -> Dict[Tuple[int, int, int, int], Fraction]:
        anti: Dict[Tuple[int, int, int, int], Fraction] = {}
        for degs, v in P.items():
            d = degs[var_idx]
            nd = list(degs)
            nd[var_idx] = d + 1
            anti[(nd[0], nd[1], nd[2], nd[3])] = v / Fraction(d + 1)
        hi = sub_var(anti, var_idx, hi_poly)
        lo = sub_var(anti, var_idx, lo_poly)
        neg_lo = {kk: -v for kk, v in lo.items()}
        return padd4(hi, neg_lo)

    y_plus_z = {(0, 0, 1, 0): Fraction(1), (0, 0, 0, 1): Fraction(1)}
    L_yz: Dict[Tuple[int, int, int, int], Fraction] = {}
    for d, c in enumerate(Lkm1):
        if c != 0:
            L_yz = padd4(L_yz, pm4({(0, 0, 0, 0): c}, ppow4(y_plus_z, d)))

    Sl_ay = {(ds, 0, da, 0): v for (ds, da), v in Sl.items()}
    Skl_bz = {(0, ds, 0, da): v for (ds, da), v in Skl.items()}
    one_m_y = {(0, 0, 0, 0): Fraction(1), (0, 0, 1, 0): Fraction(-1)}
    one_m_b = {(0, 0, 0, 0): Fraction(1), (0, 1, 0, 0): Fraction(-1)}
    one_m_a = {(0, 0, 0, 0): Fraction(1), (1, 0, 0, 0): Fraction(-1)}
    a_p = {(1, 0, 0, 0): Fraction(1)}
    b_p = {(0, 1, 0, 0): Fraction(1)}

    T1 = integ(integ(pm4(pm4(L_yz, Sl_ay), Skl_bz), 3, b_p, one_m_y), 2, a_p, one_m_b)
    Skl_b_pt = {(0, k - l - 1, 0, 0): Fraction(1, int_fact(k - l - 1))}
    T2 = pm4(Skl_b_pt, integ(pm4(sub_var(L_yz, 3, b_p), Sl_ay), 2, a_p, one_m_b))
    Sl_a_pt = {(l, 0, 0, 0): Fraction(1, int_fact(l))}
    T3 = pm4(Sl_a_pt, integ(pm4(sub_var(L_yz, 2, a_p), Skl_bz), 3, b_p, one_m_a))
    T4 = pm4(pm4(sub_var(sub_var(L_yz, 2, a_p), 3, b_p), Sl_a_pt), Skl_b_pt)

    R_ab = padd4(T1, T2, T3, T4)

    def bmul(A: BivPoly, B: BivPoly) -> BivPoly:
        out: BivPoly = {}
        for (i1, j1), v1 in A.items():
            for (i2, j2), v2 in B.items():
                kk = (i1 + i2, j1 + j2)
                out[kk] = out.get(kk, Fraction(0)) + v1 * v2
        return {kk: v for kk, v in out.items() if v != 0}

    def badd(A: BivPoly, B: BivPoly) -> BivPoly:
        out = dict(A)
        for kk, v in B.items():
            out[kk] = out.get(kk, Fraction(0)) + v
        return {kk: v for kk, v in out.items() if v != 0}

    def bpow(A: BivPoly, e: int) -> BivPoly:
        r: BivPoly = {(0, 0): Fraction(1)}
        for _ in range(e):
            r = bmul(r, A)
        return r

    r_p_s: BivPoly = {(1, 0): Fraction(1, 2), (0, 1): Fraction(1, 2)}
    r_m_s: BivPoly = {(1, 0): Fraction(1, 2), (0, 1): Fraction(-1, 2)}
    R_rs: BivPoly = {}
    for (da, db, dy, dz), v in R_ab.items():
        if dy != 0 or dz != 0:
            raise RuntimeError("Unexpected remaining integration variables")
        R_rs = badd(R_rs, bmul(bmul({(0, 0): v}, bpow(r_p_s, da)), bpow(r_m_s, db)))
    return R_rs
