"""Exact zero-floating-point four-mode certificate verifier for POLY-DECOMP-CERT-1.0.

Verifies exact algebraic, Legendre-slice, m-basic polynomial decomposition, discrete tomography,
Proposition 3.7 filling-norm, and cyclotomic-factorization certificates for:
  Peter Keevash and Jeck Lim, "Efficient reconfiguration, polynomial decompositions and
  approximate counting" (arXiv:2611.33120, Nov 24, 2026).

Strictly zero floating-point operations (uses int and fractions.Fraction exclusively).
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from fractions import Fraction
import re
from typing import Any, Dict, List, Optional, Tuple

from src.polydecomp_exact import (
    build_cyclotomic_poly,
    build_m_basic_poly,
    compute_legendre_slice_R,
    frac_to_canon_str,
    int_fact,
    int_gcd,
    legendre_poly_murphy,
    poly_add_z,
    poly_deriv_z,
    poly_divmod_monic_or_unit_z,
    poly_eval_z,
    poly_l1_z,
    poly_mul_z,
    poly_sub_z,
    poly_trim_z,
)

SCHEMA_VERSION = "POLY-DECOMP-CERT-1.0"
MAX_BIT_LEN = 2048
MAX_JSON_DEPTH = 32
MAX_ID_LEN = 128

_CANON_INT_RE = re.compile(r"\A(?:0|-?[1-9][0-9]*)\Z")
_CANON_FRAC_RE = re.compile(r"\A(-?[1-9][0-9]*)/([1-9][0-9]*)\Z")

VALID_MODES = {
    "legendre_miracle_thm16_cert",
    "m_basic_poly_decomp_cert",
    "discrete_tomography_switch_cert",
    "filling_norm_lower_bound_cert",
}


class CertError(ValueError):
    """Raised when a certificate violates schema, typing, or mathematical invariants."""


def _assert_strict_json_types(obj: Any, path: str = "root", depth: int = 0) -> None:
    if depth > MAX_JSON_DEPTH:
        raise CertError(f"{path}: JSON nesting depth exceeds {MAX_JSON_DEPTH}")
    if obj is None or type(obj) in (bool, int, str):
        return
    if type(obj) is list:
        for i, item in enumerate(obj):
            _assert_strict_json_types(item, f"{path}[{i}]", depth + 1)
        return
    if type(obj) is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise CertError(f"{path}: non-string dict key")
            _assert_strict_json_types(v, f"{path}.{k}", depth + 1)
        return
    raise CertError(f"{path}: disallowed type {type(obj).__name__} (non-exact types forbidden)")


def _require_exact_keys(d: Any, expected: set[str], label: str) -> Dict[str, Any]:
    if type(d) is not dict:
        raise CertError(f"{label}: expected dict")
    keys = set(d.keys())
    if keys != expected:
        missing = sorted(expected - keys)
        extra = sorted(keys - expected)
        raise CertError(f"{label}: key mismatch (missing={missing}, extra={extra})")
    return d


def _parse_bool(v: Any, label: str) -> bool:
    if type(v) is not bool:
        raise CertError(f"{label}: expected bool, got {type(v).__name__}")
    return v


def _parse_int(v: Any, label: str, lo: Optional[int] = None, hi: Optional[int] = None) -> int:
    if type(v) is not int:
        raise CertError(f"{label}: expected int, got {type(v).__name__}")
    if v.bit_length() > MAX_BIT_LEN:
        raise CertError(f"{label}: integer exceeds {MAX_BIT_LEN} bits")
    if lo is not None and v < lo:
        raise CertError(f"{label}: {v} < {lo}")
    if hi is not None and v > hi:
        raise CertError(f"{label}: {v} > {hi}")
    return v


def _parse_id_str(v: Any, label: str) -> str:
    if type(v) is not str or not v or len(v) > MAX_ID_LEN:
        raise CertError(f"{label}: expected non-empty string of length <= {MAX_ID_LEN}")
    if any(ord(ch) < 32 or ord(ch) == 127 for ch in v):
        raise CertError(f"{label}: ASCII control characters disallowed")
    return v


def _parse_canon_rat(v: Any, label: str) -> Fraction:
    if type(v) is not str or not v or len(v) > 256:
        raise CertError(f"{label}: expected canonical rational string")
    if _CANON_INT_RE.match(v):
        n = int(v)
        if n.bit_length() > MAX_BIT_LEN:
            raise CertError(f"{label}: rational numerator exceeds {MAX_BIT_LEN} bits")
        return Fraction(n, 1)
    m = _CANON_FRAC_RE.match(v)
    if m:
        p = int(m.group(1))
        q = int(m.group(2))
        if q <= 1:
            raise CertError(f"{label}: non-canonical denominator {q} (integers must omit /1)")
        if p.bit_length() > MAX_BIT_LEN or q.bit_length() > MAX_BIT_LEN:
            raise CertError(f"{label}: rational exceeds {MAX_BIT_LEN} bits")
        if int_gcd(p, q) != 1:
            raise CertError(f"{label}: non-reduced fraction {v!r}")
        return Fraction(p, q)
    raise CertError(f"{label}: malformed canonical rational string {v!r}")


def _parse_int_list(v: Any, label: str, min_len: int = 1, max_len: int = 256, lo: Optional[int] = None, hi: Optional[int] = None) -> List[int]:
    if type(v) is not list or not (min_len <= len(v) <= max_len):
        raise CertError(f"{label}: expected list of length {min_len}..{max_len}")
    return [_parse_int(x, f"{label}[{i}]", lo, hi) for i, x in enumerate(v)]


def _verify_mode1(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 1: Theorem 1.6 miraculous global Legendre cross-polytope slice polynomials R_l(r, s)."""
    _require_exact_keys(
        payload,
        {
            "k",
            "l",
            "claimed_L_km1",
            "claimed_R_coeffs",
            "claimed_sym_neg_ok",
            "claimed_sym_swap_ok",
            "claimed_max_deg_r",
            "claimed_max_deg_s",
            "claimed_marginal_integral",
            "claimed_symmetry_constraints",
        },
        "mode1.payload",
    )
    k = _parse_int(payload["k"], "k", 2, 5)
    l = _parse_int(payload["l"], "l", 0, k - 1)

    Lkm1 = legendre_poly_murphy(k - 1)
    raw_L = payload["claimed_L_km1"]
    if type(raw_L) is not list or len(raw_L) != k:
        raise CertError(f"claimed_L_km1: expected list of {k} canonical rationals")
    parsed_L = [_parse_canon_rat(c, f"claimed_L_km1[{i}]") for i, c in enumerate(raw_L)]
    if parsed_L != Lkm1:
        raise CertError("claimed_L_km1 does not match exact Murphy Legendre polynomial L_{k-1}")
    if sum(Lkm1, Fraction(0)) != Fraction(1):
        raise CertError("Legendre normalization L_{k-1}(1) != 1")

    R_exact = compute_legendre_slice_R(k, l)
    raw_R = payload["claimed_R_coeffs"]
    if type(raw_R) is not dict or not raw_R:
        raise CertError("claimed_R_coeffs: expected non-empty dict of monomial coefficients")
    parsed_R: Dict[Tuple[int, int], Fraction] = {}
    for key_str, val_str in raw_R.items():
        if type(key_str) is not str:
            raise CertError("claimed_R_coeffs: non-string key")
        parts = key_str.split(",")
        if len(parts) != 2 or not _CANON_INT_RE.match(parts[0]) or not _CANON_INT_RE.match(parts[1]):
            raise CertError(f"claimed_R_coeffs: invalid exponent key {key_str!r}")
        dr, ds = int(parts[0]), int(parts[1])
        if dr < 0 or ds < 0 or dr > 2 * k or ds > 2 * k:
            raise CertError(f"claimed_R_coeffs: exponent out of range ({dr}, {ds})")
        val = _parse_canon_rat(val_str, f"claimed_R_coeffs[{key_str}]")
        if val == 0:
            raise CertError(f"claimed_R_coeffs[{key_str}]: explicit zero monomial disallowed")
        parsed_R[(dr, ds)] = val

    if parsed_R != R_exact:
        raise CertError("claimed_R_coeffs does not match exact Theorem 1.6 symbolic integral R_l(r, s)")

    sym_neg = all((dr + ds) % 2 == 0 for (dr, ds) in R_exact)
    sym_swap = all(R_exact.get((ds, dr), Fraction(0)) == v for (dr, ds), v in R_exact.items())
    max_dr = max(dr for (dr, _) in R_exact)
    max_ds = max(ds for (_, ds) in R_exact)
    if not sym_neg or not sym_swap:
        raise CertError("Theorem 1.6 symmetry invariant violated")
    if max_dr > k - 1 or max_ds > k - 1:
        raise CertError(f"Theorem 1.6 degree bound violated: ({max_dr}, {max_ds}) > {k - 1}")

    # Compute exact symbolic marginal integral int_{-1}^1 R_l(r, s) ds as univariate poly in r:
    marg: Dict[int, Fraction] = {}
    for (dr, ds), v in R_exact.items():
        if ds % 2 == 0:
            marg[dr] = marg.get(dr, Fraction(0)) + v * Fraction(2, ds + 1)
    marg_nz = {dr: v for dr, v in marg.items() if v != 0}
    expected_marg = Fraction(2, int_fact(k))
    if marg_nz != {0: expected_marg}:
        raise CertError(f"Theorem 1.6 marginal integral failed cancellation: got {marg_nz}")

    if _parse_bool(payload["claimed_sym_neg_ok"], "claimed_sym_neg_ok") is not True:
        raise CertError("claimed_sym_neg_ok must be True")
    if _parse_bool(payload["claimed_sym_swap_ok"], "claimed_sym_swap_ok") is not True:
        raise CertError("claimed_sym_swap_ok must be True")
    if _parse_int(payload["claimed_max_deg_r"], "claimed_max_deg_r", 0, k - 1) != max_dr:
        raise CertError(f"claimed_max_deg_r mismatch: expected {max_dr}")
    if _parse_int(payload["claimed_max_deg_s"], "claimed_max_deg_s", 0, k - 1) != max_ds:
        raise CertError(f"claimed_max_deg_s mismatch: expected {max_ds}")
    if _parse_canon_rat(payload["claimed_marginal_integral"], "claimed_marginal_integral") != expected_marg:
        raise CertError(f"claimed_marginal_integral mismatch: expected {frac_to_canon_str(expected_marg)}")

    sym_constraints = (3 * k * (k - 1)) // 2
    if _parse_int(payload["claimed_symmetry_constraints"], "claimed_symmetry_constraints", 1) != sym_constraints:
        raise CertError(f"claimed_symmetry_constraints mismatch: expected {sym_constraints}")
    if sym_constraints <= k:
        raise CertError("Symmetry constraint count must strictly exceed k")

    return {
        "k": k,
        "l": l,
        "num_monomials": len(R_exact),
        "max_deg_r": max_dr,
        "marginal_integral": frac_to_canon_str(expected_marg),
        "symmetry_constraints": sym_constraints,
    }


def _verify_mode2(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 2: Theorem 1.2 / 1.4 exact m-basic polynomial decomposition in Z[x]."""
    _require_exact_keys(
        payload,
        {
            "k",
            "m_vec",
            "target_poly",
            "terms",
            "claimed_quotient_by_1mx_k",
            "claimed_target_l1",
            "claimed_decomp_l1_cost",
            "claimed_term_count",
        },
        "mode2.payload",
    )
    k = _parse_int(payload["k"], "k", 1, 4)
    m_vec = _parse_int_list(payload["m_vec"], "m_vec", k, k, 1, 16)
    target_poly = _parse_int_list(payload["target_poly"], "target_poly", 2, 200, -10000, 10000)
    if target_poly != poly_trim_z(target_poly):
        raise CertError("target_poly: trailing zero coefficients disallowed")

    raw_terms = payload["terms"]
    if type(raw_terms) is not list or not (1 <= len(raw_terms) <= 64):
        raise CertError("terms: expected 1..64 m-basic terms")

    accum = [0]
    decomp_l1 = 0
    for idx, t in enumerate(raw_terms):
        _require_exact_keys(t, {"sign", "shift_a", "a_vec"}, f"terms[{idx}]")
        sgn = _parse_int(t["sign"], f"terms[{idx}].sign", -1, 1)
        if sgn not in (-1, 1):
            raise CertError(f"terms[{idx}].sign must be -1 or 1")
        shift_a = _parse_int(t["shift_a"], f"terms[{idx}].shift_a", 0, 128)
        a_vec = _parse_int_list(t["a_vec"], f"terms[{idx}].a_vec", k, k, 1, 32)
        term_poly = build_m_basic_poly(sgn, shift_a, m_vec, a_vec)
        if term_poly == [0]:
            raise CertError(f"terms[{idx}]: degenerate zero m-basic polynomial")
        decomp_l1 += poly_l1_z(term_poly)
        accum = poly_add_z(accum, term_poly)

    if accum != target_poly:
        raise CertError("Sum of m-basic terms does not equal target_poly in Z[x]")

    # Exact repeated division by (1 - x) k times
    q_cur = list(target_poly)
    for step in range(k):
        q_cur, rem = poly_divmod_monic_or_unit_z(q_cur, [1, -1])
        if rem != [0]:
            raise CertError(f"target_poly is not divisible by (1 - x)^{step + 1}")

    claimed_q = _parse_int_list(payload["claimed_quotient_by_1mx_k"], "claimed_quotient_by_1mx_k", 1, 200)
    if claimed_q != poly_trim_z(claimed_q):
        raise CertError("claimed_quotient_by_1mx_k: trailing zero coefficients disallowed")
    if claimed_q != q_cur:
        raise CertError("claimed_quotient_by_1mx_k mismatch")

    target_l1 = poly_l1_z(target_poly)
    if _parse_int(payload["claimed_target_l1"], "claimed_target_l1", 1) != target_l1:
        raise CertError(f"claimed_target_l1 mismatch: expected {target_l1}")
    if _parse_int(payload["claimed_decomp_l1_cost"], "claimed_decomp_l1_cost", target_l1) != decomp_l1:
        raise CertError(f"claimed_decomp_l1_cost mismatch: expected {decomp_l1}")
    if _parse_int(payload["claimed_term_count"], "claimed_term_count", 1) != len(raw_terms):
        raise CertError(f"claimed_term_count mismatch: expected {len(raw_terms)}")

    return {
        "k": k,
        "m_vec": m_vec,
        "target_deg": len(target_poly) - 1,
        "target_l1": target_l1,
        "decomp_l1_cost": decomp_l1,
        "term_count": len(raw_terms),
    }


def _grid_xrays(grid: List[List[int]], directions: List[Tuple[int, int]]) -> List[Dict[int, int]]:
    h = len(grid)
    w = len(grid[0])
    out: List[Dict[int, int]] = []
    for dx, dy in directions:
        proj: Dict[int, int] = {}
        for y in range(h):
            for x in range(w):
                val = grid[y][x]
                if val != 0:
                    inv = dy * x - dx * y
                    proj[inv] = proj.get(inv, 0) + val
        out.append({inv: s for inv, s in proj.items() if s != 0})
    return out


def _verify_mode3(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 3: Section 1.1 & Theorem 1.1 discrete tomography zero-X-ray basic-switch reconfiguration."""
    _require_exact_keys(
        payload,
        {
            "width",
            "height",
            "directions",
            "grid_A",
            "grid_B",
            "switch_steps",
            "claimed_all_xrays_match",
            "claimed_diff_l1",
            "claimed_step_count",
            "claimed_max_abs_entry",
        },
        "mode3.payload",
    )
    w = _parse_int(payload["width"], "width", 2, 12)
    h = _parse_int(payload["height"], "height", 2, 12)

    raw_dirs = payload["directions"]
    if type(raw_dirs) is not list or not (2 <= len(raw_dirs) <= 3):
        raise CertError("directions: expected 2 or 3 primitive lattice vectors")
    directions: List[Tuple[int, int]] = []
    for i, dv in enumerate(raw_dirs):
        vec = _parse_int_list(dv, f"directions[{i}]", 2, 2, -4, 4)
        dx, dy = vec[0], vec[1]
        if dx == 0 and dy == 0:
            raise CertError(f"directions[{i}]: zero direction vector")
        if int_gcd(dx, dy) != 1:
            raise CertError(f"directions[{i}]: direction vector ({dx},{dy}) is not primitive")
        directions.append((dx, dy))
    for i in range(len(directions)):
        for j in range(i + 1, len(directions)):
            det = directions[i][0] * directions[j][1] - directions[i][1] * directions[j][0]
            if det == 0:
                raise CertError(f"directions[{i}] and directions[{j}] are collinear")

    def _parse_grid(raw: Any, label: str) -> List[List[int]]:
        if type(raw) is not list or len(raw) != h:
            raise CertError(f"{label}: expected {h} rows")
        return [_parse_int_list(row, f"{label}[{r}]", w, w, -20, 20) for r, row in enumerate(raw)]

    grid_A = _parse_grid(payload["grid_A"], "grid_A")
    grid_B = _parse_grid(payload["grid_B"], "grid_B")

    xrays_A = _grid_xrays(grid_A, directions)
    xrays_B = _grid_xrays(grid_B, directions)
    if xrays_A != xrays_B:
        raise CertError("X-ray projections of grid_A and grid_B do not match")

    diff_l1 = sum(abs(grid_A[y][x] - grid_B[y][x]) for y in range(h) for x in range(w))
    raw_steps = payload["switch_steps"]
    if type(raw_steps) is not list or not (1 <= len(raw_steps) <= 64):
        raise CertError("switch_steps: expected 1..64 basic switch steps")

    k = len(directions)
    cur = [list(row) for row in grid_A]
    max_abs = max(abs(cur[y][x]) for y in range(h) for x in range(w))

    for s_idx, step in enumerate(raw_steps):
        _require_exact_keys(step, {"sign", "origin", "scales"}, f"switch_steps[{s_idx}]")
        sgn = _parse_int(step["sign"], f"switch_steps[{s_idx}].sign", -1, 1)
        if sgn not in (-1, 1):
            raise CertError(f"switch_steps[{s_idx}].sign must be -1 or 1")
        orig = _parse_int_list(step["origin"], f"switch_steps[{s_idx}].origin", 2, 2, 0, max(w, h) - 1)
        scales = _parse_int_list(step["scales"], f"switch_steps[{s_idx}].scales", k, k, 1, max(w, h))

        delta = [[0] * w for _ in range(h)]
        for mask in range(1 << k):
            px, py = orig[0], orig[1]
            popcnt = 0
            for bit in range(k):
                if (mask >> bit) & 1:
                    popcnt += 1
                    px += scales[bit] * directions[bit][0]
                    py += scales[bit] * directions[bit][1]
            if not (0 <= px < w and 0 <= py < h):
                raise CertError(f"switch_steps[{s_idx}]: vertex ({px},{py}) outside grid {w}x{h}")
            coeff = sgn if (popcnt % 2 == 0) else -sgn
            delta[py][px] += coeff

        # Verify zero X-rays of every elementary basic switch
        sw_xrays = _grid_xrays(delta, directions)
        if any(bool(p) for p in sw_xrays):
            raise CertError(f"switch_steps[{s_idx}]: non-zero X-ray projection")

        for y in range(h):
            for x in range(w):
                cur[y][x] += delta[y][x]
                if abs(cur[y][x]) > max_abs:
                    max_abs = abs(cur[y][x])

    if cur != grid_B:
        raise CertError("Final reconfigured grid does not equal grid_B")

    if _parse_bool(payload["claimed_all_xrays_match"], "claimed_all_xrays_match") is not True:
        raise CertError("claimed_all_xrays_match must be True")
    if _parse_int(payload["claimed_diff_l1"], "claimed_diff_l1", 0) != diff_l1:
        raise CertError(f"claimed_diff_l1 mismatch: expected {diff_l1}")
    if _parse_int(payload["claimed_step_count"], "claimed_step_count", 1) != len(raw_steps):
        raise CertError(f"claimed_step_count mismatch: expected {len(raw_steps)}")
    if _parse_int(payload["claimed_max_abs_entry"], "claimed_max_abs_entry", 0) != max_abs:
        raise CertError(f"claimed_max_abs_entry mismatch: expected {max_abs}")

    return {
        "grid_shape": f"{w}x{h}",
        "num_directions": k,
        "diff_l1": diff_l1,
        "step_count": len(raw_steps),
        "max_abs_entry": max_abs,
    }


def _verify_mode4(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 4: Sec. 3.4 Prop. 3.7 filling-norm witness & Sec. 4.1 cyclotomic factorizations."""
    if type(payload) is not dict or "submode" not in payload:
        raise CertError("mode4.payload: missing submode")
    submode = _parse_id_str(payload["submode"], "submode")

    if submode == "prop37_filling_witness":
        _require_exact_keys(
            payload,
            {
                "submode",
                "a",
                "b",
                "c",
                "candidate_m",
                "base_t",
                "bound_B",
                "cramer_z",
                "claimed_f_eval1",
                "claimed_f_deriv1",
                "claimed_f_deriv2",
                "claimed_f_l1",
                "claimed_quotient_deg",
                "claimed_eq_count",
                "claimed_cramer_val",
            },
            "mode4.prop37_filling_witness",
        )
        a = _parse_int(payload["a"], "a", 2, 20)
        b = _parse_int(payload["b"], "b", 2, 20)
        c = _parse_int(payload["c"], "c", 4, 400)
        if c != a * b:
            raise CertError(f"Proposition 3.7 requires c = a*b ({a * b}), got {c}")

        # Build F_{a,b,c}(x) = (1 - x^a)(1 - x^b) - (1 - x)(1 - x^c)
        pa = [1] + [0] * (a - 1) + [-1]
        pb = [1] + [0] * (b - 1) + [-1]
        p1 = [1, -1]
        pc = [1] + [0] * (c - 1) + [-1]
        F = poly_sub_z(poly_mul_z(pa, pb), poly_mul_z(p1, pc))
        F1 = poly_deriv_z(F)
        F2 = poly_deriv_z(F1)

        ev0 = poly_eval_z(F, 1)
        ev1 = poly_eval_z(F1, 1)
        ev2 = poly_eval_z(F2, 1)
        if ev0 != 0 or ev1 != 0 or ev2 != 0:
            raise CertError(f"Expected F(1)=F'(1)=F''(1)=0, got ({ev0}, {ev1}, {ev2})")

        q_cur = list(F)
        for step in range(3):
            q_cur, rem = poly_divmod_monic_or_unit_z(q_cur, [1, -1])
            if rem != [0]:
                raise CertError(f"F is not divisible by (1 - x)^{step + 1}")

        f_l1 = poly_l1_z(F)
        q_deg = len(q_cur) - 1
        cand_m = _parse_int(payload["candidate_m"], "candidate_m", 1, 20)
        eq_count = 4 * cand_m + 3

        bound_B = _parse_int(payload["bound_B"], "bound_B", 0, 10000)
        base_t = _parse_int(payload["base_t"], "base_t", 2 * bound_B + 2, 1000000)
        cz = _parse_int_list(payload["cramer_z"], "cramer_z", 4, 4)
        z0, z1, z2, z3 = cz
        if abs(z0) > bound_B or abs(z1) > bound_B or abs(z2) > bound_B:
            raise CertError("cramer_z[0..2] exceed bound_B")
        if z3 == 0:
            raise CertError("cramer_z[3] must be non-zero for base-t non-vanishing")
        cramer_val = z0 + z1 * base_t + z2 * (base_t * base_t) + z3 * (base_t * base_t * base_t)
        if cramer_val == 0:
            raise CertError("Base-t Cramer polynomial unexpectedly vanished")

        if _parse_int(payload["claimed_f_eval1"], "claimed_f_eval1", 0, 0) != 0:
            raise CertError("claimed_f_eval1 mismatch")
        if _parse_int(payload["claimed_f_deriv1"], "claimed_f_deriv1", 0, 0) != 0:
            raise CertError("claimed_f_deriv1 mismatch")
        if _parse_int(payload["claimed_f_deriv2"], "claimed_f_deriv2", 0, 0) != 0:
            raise CertError("claimed_f_deriv2 mismatch")
        if _parse_int(payload["claimed_f_l1"], "claimed_f_l1", 1) != f_l1:
            raise CertError(f"claimed_f_l1 mismatch: expected {f_l1}")
        if _parse_int(payload["claimed_quotient_deg"], "claimed_quotient_deg", 0) != q_deg:
            raise CertError(f"claimed_quotient_deg mismatch: expected {q_deg}")
        if _parse_int(payload["claimed_eq_count"], "claimed_eq_count", 7) != eq_count:
            raise CertError(f"claimed_eq_count mismatch: expected {eq_count}")
        if _parse_int(payload["claimed_cramer_val"], "claimed_cramer_val") != cramer_val:
            raise CertError(f"claimed_cramer_val mismatch: expected {cramer_val}")

        return {
            "submode": submode,
            "triple": [a, b, c],
            "f_l1": f_l1,
            "quotient_deg": q_deg,
            "cramer_nonzero": True,
        }

    if submode == "cyclotomic_factorization":
        _require_exact_keys(
            payload,
            {
                "submode",
                "m",
                "claimed_divisors",
                "claimed_phi_polys",
                "claimed_phi_m_l1",
                "claimed_totient_deg",
            },
            "mode4.cyclotomic_factorization",
        )
        m = _parse_int(payload["m"], "m", 2, 24)
        divs = [d for d in range(1, m + 1) if m % d == 0]
        claimed_divs = _parse_int_list(payload["claimed_divisors"], "claimed_divisors", 1, 24, 1, m)
        if claimed_divs != divs:
            raise CertError(f"claimed_divisors mismatch: expected {divs}")

        raw_phis = payload["claimed_phi_polys"]
        expected_keys = {str(d) for d in divs}
        if type(raw_phis) is not dict or set(raw_phis.keys()) != expected_keys:
            raise CertError("claimed_phi_polys must map every divisor d of m")

        prod = [1]
        phi_m: List[int] = []
        for d in divs:
            exact_phi = build_cyclotomic_poly(d)
            cl_phi = _parse_int_list(raw_phis[str(d)], f"claimed_phi_polys[{d}]", 2, 32, -10, 10)
            if cl_phi != poly_trim_z(cl_phi) or cl_phi != exact_phi:
                raise CertError(f"claimed_phi_polys[{d}] does not match exact Phi_{d}(x)")
            prod = poly_mul_z(prod, exact_phi)
            if d == m:
                phi_m = exact_phi

        expected_xm_minus_1 = [-1] + [0] * (m - 1) + [1]
        if prod != expected_xm_minus_1:
            raise CertError("Product of cyclotomic polynomials did not equal x^m - 1")

        phi_m_l1 = poly_l1_z(phi_m)
        totient = len(phi_m) - 1
        if _parse_int(payload["claimed_phi_m_l1"], "claimed_phi_m_l1", 1) != phi_m_l1:
            raise CertError(f"claimed_phi_m_l1 mismatch: expected {phi_m_l1}")
        if _parse_int(payload["claimed_totient_deg"], "claimed_totient_deg", 1) != totient:
            raise CertError(f"claimed_totient_deg mismatch: expected {totient}")

        return {
            "submode": submode,
            "m": m,
            "num_divisors": len(divs),
            "phi_m_l1": phi_m_l1,
            "totient_deg": totient,
        }

    raise CertError(f"unknown mode4 submode {submode!r}")


def verify_certificate(cert: Any) -> Tuple[bool, str, Dict[str, Any]]:
    """Verify a POLY-DECOMP-CERT-1.0 certificate payload with zero floating-point arithmetic."""
    try:
        _assert_strict_json_types(cert)
        _require_exact_keys(
            cert,
            {"schema_version", "cert_id", "mode", "reference", "payload"},
            "certificate",
        )
        if cert["schema_version"] != SCHEMA_VERSION:
            raise CertError(
                f"schema_version mismatch: expected {SCHEMA_VERSION!r}, got {cert['schema_version']!r}"
            )
        cert_id = _parse_id_str(cert["cert_id"], "cert_id")
        mode = _parse_id_str(cert["mode"], "mode")
        if mode not in VALID_MODES:
            raise CertError(f"unknown mode {mode!r}")
        _parse_id_str(cert["reference"], "reference")
        payload = cert["payload"]
        if type(payload) is not dict:
            raise CertError("payload must be a dict")

        if mode == "legendre_miracle_thm16_cert":
            summary = _verify_mode1(payload)
        elif mode == "m_basic_poly_decomp_cert":
            summary = _verify_mode2(payload)
        elif mode == "discrete_tomography_switch_cert":
            summary = _verify_mode3(payload)
        else:
            summary = _verify_mode4(payload)

        summary["cert_id"] = cert_id
        summary["mode"] = mode
        return True, "OK", summary
    except CertError as exc:
        return False, str(exc), {}
