"""Generate all 16 canonical POLY-DECOMP-CERT-1.0 certificates and 4 exact datasets.

Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys
import time
from typing import Any, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.polydecomp_certifier import SCHEMA_VERSION, verify_certificate
from src.polydecomp_exact import (
    build_cyclotomic_poly,
    build_m_basic_poly,
    compute_legendre_slice_R,
    frac_to_canon_str,
    int_fact,
    legendre_poly_murphy,
    poly_add_z,
    poly_divmod_monic_or_unit_z,
    poly_l1_z,
    poly_mul_z,
    poly_sub_z,
)


def _write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def _make_mode1_cert(cert_id: str, ref: str, k: int, l: int) -> Dict[str, Any]:
    Lkm1 = legendre_poly_murphy(k - 1)
    R = compute_legendre_slice_R(k, l)
    R_dict = {f"{dr},{ds}": frac_to_canon_str(v) for (dr, ds), v in sorted(R.items())}
    max_dr = max(dr for (dr, _) in R)
    max_ds = max(ds for (_, ds) in R)
    marg = Fraction(2, int_fact(k))
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "legendre_miracle_thm16_cert",
        "reference": ref,
        "payload": {
            "k": k,
            "l": l,
            "claimed_L_km1": [frac_to_canon_str(c) for c in Lkm1],
            "claimed_R_coeffs": R_dict,
            "claimed_sym_neg_ok": True,
            "claimed_sym_swap_ok": True,
            "claimed_max_deg_r": max_dr,
            "claimed_max_deg_s": max_ds,
            "claimed_marginal_integral": frac_to_canon_str(marg),
            "claimed_symmetry_constraints": (3 * k * (k - 1)) // 2,
        },
    }


def _make_mode2_cert(
    cert_id: str,
    ref: str,
    m_vec: List[int],
    terms: List[Dict[str, Any]],
) -> Dict[str, Any]:
    k = len(m_vec)
    target = [0]
    cost = 0
    for t in terms:
        tp = build_m_basic_poly(t["sign"], t["shift_a"], m_vec, t["a_vec"])
        cost += poly_l1_z(tp)
        target = poly_add_z(target, tp)
    q = list(target)
    for _ in range(k):
        q, rem = poly_divmod_monic_or_unit_z(q, [1, -1])
        assert rem == [0]
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "m_basic_poly_decomp_cert",
        "reference": ref,
        "payload": {
            "k": k,
            "m_vec": m_vec,
            "target_poly": target,
            "terms": terms,
            "claimed_quotient_by_1mx_k": q,
            "claimed_target_l1": poly_l1_z(target),
            "claimed_decomp_l1_cost": cost,
            "claimed_term_count": len(terms),
        },
    }


def _make_mode3_cert(
    cert_id: str,
    ref: str,
    width: int,
    height: int,
    directions: List[List[int]],
    grid_A: List[List[int]],
    switch_steps: List[Dict[str, Any]],
) -> Dict[str, Any]:
    cur = [list(row) for row in grid_A]
    max_abs = max(abs(cur[y][x]) for y in range(height) for x in range(width))
    k = len(directions)
    for st in switch_steps:
        sgn = st["sign"]
        ox, oy = st["origin"]
        sc = st["scales"]
        for mask in range(1 << k):
            px, py = ox, oy
            pop = 0
            for bit in range(k):
                if (mask >> bit) & 1:
                    pop += 1
                    px += sc[bit] * directions[bit][0]
                    py += sc[bit] * directions[bit][1]
            cur[py][px] += sgn if (pop % 2 == 0) else -sgn
        for y in range(height):
            for x in range(width):
                if abs(cur[y][x]) > max_abs:
                    max_abs = abs(cur[y][x])
    grid_B = cur
    diff_l1 = sum(abs(grid_A[y][x] - grid_B[y][x]) for y in range(height) for x in range(width))
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "discrete_tomography_switch_cert",
        "reference": ref,
        "payload": {
            "width": width,
            "height": height,
            "directions": directions,
            "grid_A": grid_A,
            "grid_B": grid_B,
            "switch_steps": switch_steps,
            "claimed_all_xrays_match": True,
            "claimed_diff_l1": diff_l1,
            "claimed_step_count": len(switch_steps),
            "claimed_max_abs_entry": max_abs,
        },
    }


def _make_mode4_prop37_cert(
    cert_id: str,
    ref: str,
    a: int,
    b: int,
    cand_m: int,
    bound_B: int,
    base_t: int,
    cramer_z: List[int],
) -> Dict[str, Any]:
    c = a * b
    pa = [1] + [0] * (a - 1) + [-1]
    pb = [1] + [0] * (b - 1) + [-1]
    p1 = [1, -1]
    pc = [1] + [0] * (c - 1) + [-1]
    F = poly_sub_z(poly_mul_z(pa, pb), poly_mul_z(p1, pc))
    q = list(F)
    for _ in range(3):
        q, rem = poly_divmod_monic_or_unit_z(q, [1, -1])
        assert rem == [0]
    z0, z1, z2, z3 = cramer_z
    cval = z0 + z1 * base_t + z2 * (base_t * base_t) + z3 * (base_t * base_t * base_t)
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "filling_norm_lower_bound_cert",
        "reference": ref,
        "payload": {
            "submode": "prop37_filling_witness",
            "a": a,
            "b": b,
            "c": c,
            "candidate_m": cand_m,
            "base_t": base_t,
            "bound_B": bound_B,
            "cramer_z": cramer_z,
            "claimed_f_eval1": 0,
            "claimed_f_deriv1": 0,
            "claimed_f_deriv2": 0,
            "claimed_f_l1": poly_l1_z(F),
            "claimed_quotient_deg": len(q) - 1,
            "claimed_eq_count": 4 * cand_m + 3,
            "claimed_cramer_val": cval,
        },
    }


def _make_mode4_cyclo_cert(cert_id: str, ref: str, m: int) -> Dict[str, Any]:
    divs = [d for d in range(1, m + 1) if m % d == 0]
    phis = {str(d): build_cyclotomic_poly(d) for d in divs}
    phi_m = phis[str(m)]
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "filling_norm_lower_bound_cert",
        "reference": ref,
        "payload": {
            "submode": "cyclotomic_factorization",
            "m": m,
            "claimed_divisors": divs,
            "claimed_phi_polys": phis,
            "claimed_phi_m_l1": poly_l1_z(phi_m),
            "claimed_totient_deg": len(phi_m) - 1,
        },
    }


def build_all_certificates() -> List[Tuple[str, Dict[str, Any]]]:
    certs: List[Tuple[str, Dict[str, Any]]] = []

    # --- Mode 1: Theorem 1.6 Miraculous Legendre Cross-Polytope Slice Polynomials (4 certs) ---
    certs.append((
        "m1_thm16_legendre_k2_l0",
        _make_mode1_cert("m1_thm16_legendre_k2_l0", "Keevash-Lim arXiv:2611.33120 Thm. 1.6 (k=2, l=0)", 2, 0),
    ))
    certs.append((
        "m1_thm16_legendre_k3_l0",
        _make_mode1_cert("m1_thm16_legendre_k3_l0", "Keevash-Lim arXiv:2611.33120 Thm. 1.6 (k=3, l=0)", 3, 0),
    ))
    certs.append((
        "m1_thm16_legendre_k3_l1",
        _make_mode1_cert("m1_thm16_legendre_k3_l1", "Keevash-Lim arXiv:2611.33120 Thm. 1.6 (k=3, l=1)", 3, 1),
    ))
    certs.append((
        "m1_thm16_legendre_k4_l1",
        _make_mode1_cert("m1_thm16_legendre_k4_l1", "Keevash-Lim arXiv:2611.33120 Thm. 1.6 (k=4, l=1)", 4, 1),
    ))

    # --- Mode 2: Theorem 1.2 / 1.4 m-Basic Polynomial Decompositions in Z[x] (4 certs) ---
    certs.append((
        "m2_basic_decomp_k2_unit",
        _make_mode2_cert(
            "m2_basic_decomp_k2_unit",
            "Keevash-Lim arXiv:2611.33120 Thm. 1.2 (k=2, m=[1,1])",
            [1, 1],
            [
                {"sign": 1, "shift_a": 0, "a_vec": [2, 3]},
                {"sign": -1, "shift_a": 1, "a_vec": [1, 2]},
                {"sign": 1, "shift_a": 2, "a_vec": [2, 1]},
            ],
        ),
    ))
    certs.append((
        "m2_basic_decomp_k2_weighted_m23",
        _make_mode2_cert(
            "m2_basic_decomp_k2_weighted_m23",
            "Keevash-Lim arXiv:2611.33120 Thm. 1.2 (k=2, m=[2,3])",
            [2, 3],
            [
                {"sign": 1, "shift_a": 0, "a_vec": [1, 1]},
                {"sign": 1, "shift_a": 2, "a_vec": [2, 1]},
                {"sign": -1, "shift_a": 1, "a_vec": [1, 2]},
            ],
        ),
    ))
    certs.append((
        "m2_basic_decomp_k3_cancellation",
        _make_mode2_cert(
            "m2_basic_decomp_k3_cancellation",
            "Keevash-Lim arXiv:2611.33120 Thm. 1.2 & 1.4 (k=3, m=[1,1,1])",
            [1, 1, 1],
            [
                {"sign": 1, "shift_a": 0, "a_vec": [1, 2, 3]},
                {"sign": -1, "shift_a": 1, "a_vec": [1, 1, 2]},
                {"sign": 1, "shift_a": 0, "a_vec": [2, 1, 1]},
                {"sign": -1, "shift_a": 2, "a_vec": [1, 1, 1]},
            ],
        ),
    ))
    certs.append((
        "m2_basic_decomp_k3_weighted_m123",
        _make_mode2_cert(
            "m2_basic_decomp_k3_weighted_m123",
            "Keevash-Lim arXiv:2611.33120 Thm. 1.2 (k=3, m=[1,2,3])",
            [1, 2, 3],
            [
                {"sign": 1, "shift_a": 0, "a_vec": [1, 1, 1]},
                {"sign": -1, "shift_a": 3, "a_vec": [2, 1, 1]},
                {"sign": 1, "shift_a": 1, "a_vec": [1, 2, 1]},
            ],
        ),
    ))

    # --- Mode 3: Section 1.1 & Theorem 1.1 Discrete Tomography Basic Switches (4 certs) ---
    certs.append((
        "m3_tomography_2dir_contingency_4x4",
        _make_mode3_cert(
            "m3_tomography_2dir_contingency_4x4",
            "Keevash-Lim arXiv:2611.33120 Sec. 1 (2-dir contingency table switches)",
            4,
            4,
            [[1, 0], [0, 1]],
            [
                [1, 0, 1, 0],
                [0, 1, 0, 1],
                [1, 0, 0, 1],
                [0, 1, 1, 0],
            ],
            [
                {"sign": -1, "origin": [0, 0], "scales": [1, 1]},
                {"sign": 1, "origin": [1, 1], "scales": [2, 2]},
                {"sign": -1, "origin": [0, 2], "scales": [2, 1]},
            ],
        ),
    ))
    certs.append((
        "m3_tomography_3dir_diag_5x5",
        _make_mode3_cert(
            "m3_tomography_3dir_diag_5x5",
            "Keevash-Lim arXiv:2611.33120 Sec. 1.1 (3-dir X-rays: horiz/vert/diag)",
            5,
            5,
            [[1, 0], [0, 1], [1, 1]],
            [
                [1, 1, 0, 0, 1],
                [0, 1, 1, 0, 0],
                [1, 0, 1, 1, 0],
                [0, 0, 1, 1, 1],
                [1, 0, 0, 1, 0],
            ],
            [
                {"sign": 1, "origin": [0, 0], "scales": [1, 1, 1]},
                {"sign": -1, "origin": [1, 1], "scales": [1, 2, 1]},
            ],
        ),
    ))
    certs.append((
        "m3_tomography_3dir_antidiag_6x6",
        _make_mode3_cert(
            "m3_tomography_3dir_antidiag_6x6",
            "Keevash-Lim arXiv:2611.33120 Thm. 1.1 (3-dir multi-scale switch chain)",
            6,
            6,
            [[1, 0], [0, 1], [1, -1]],
            [
                [1, 0, 1, 1, 0, 1],
                [0, 1, 1, 0, 1, 0],
                [1, 1, 0, 1, 0, 1],
                [0, 1, 0, 1, 1, 0],
                [1, 0, 1, 0, 1, 1],
                [0, 1, 1, 0, 0, 1],
            ],
            [
                {"sign": 1, "origin": [0, 2], "scales": [1, 1, 1]},
                {"sign": -1, "origin": [1, 3], "scales": [2, 1, 1]},
                {"sign": 1, "origin": [2, 2], "scales": [1, 2, 2]},
            ],
        ),
    ))
    certs.append((
        "m3_tomography_3dir_knight_7x7",
        _make_mode3_cert(
            "m3_tomography_3dir_knight_7x7",
            "Keevash-Lim arXiv:2611.33120 Sec. 1.1 (3-dir non-unimodular slope (2,1))",
            7,
            7,
            [[1, 0], [0, 1], [2, 1]],
            [[(x + y) % 2 for x in range(7)] for y in range(7)],
            [
                {"sign": 1, "origin": [0, 0], "scales": [1, 2, 1]},
                {"sign": -1, "origin": [1, 1], "scales": [2, 1, 1]},
            ],
        ),
    ))

    # --- Mode 4: Sec. 3.4 Prop. 3.7 Filling-Norm Witness & Sec. 4.1 Cyclotomic Factorizations (4 certs) ---
    certs.append((
        "m4_prop37_filling_witness_2_3_6",
        _make_mode4_prop37_cert(
            "m4_prop37_filling_witness_2_3_6",
            "Keevash-Lim arXiv:2611.33120 Sec. 3.4 Prop. 3.7 (a=2, b=3, c=6)",
            2,
            3,
            4,
            5,
            12,
            [-5, 4, -3, 1],
        ),
    ))
    certs.append((
        "m4_prop37_filling_witness_3_5_15",
        _make_mode4_prop37_cert(
            "m4_prop37_filling_witness_3_5_15",
            "Keevash-Lim arXiv:2611.33120 Sec. 3.4 Prop. 3.7 (a=3, b=5, c=15)",
            3,
            5,
            8,
            12,
            30,
            [11, -12, 9, -2],
        ),
    ))
    certs.append((
        "m4_cyclotomic_factorization_m12",
        _make_mode4_cyclo_cert(
            "m4_cyclotomic_factorization_m12",
            "Keevash-Lim arXiv:2611.33120 Sec. 4.1 (Cyclotomic factorization m=12)",
            12,
        ),
    ))
    certs.append((
        "m4_cyclotomic_factorization_m24",
        _make_mode4_cyclo_cert(
            "m4_cyclotomic_factorization_m24",
            "Keevash-Lim arXiv:2611.33120 Sec. 4.1 (Cyclotomic factorization m=24)",
            24,
        ),
    ))

    assert len(certs) == 16
    return certs


def main() -> None:
    cert_dir = ROOT / "certificates"
    data_dir = ROOT / "data"
    cert_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)

    certs = build_all_certificates()
    replay_rows = []
    for name, cert in certs:
        _write_json(cert_dir / f"{name}.json", cert)
        t0 = time.perf_counter_ns()
        ok, msg, summary = verify_certificate(cert)
        dt_ns = time.perf_counter_ns() - t0
        if not ok:
            raise RuntimeError(f"Canonical cert {name} failed verification: {msg}")
        replay_rows.append(
            {
                "cert_id": name,
                "mode": cert["mode"],
                "ok": ok,
                "verify_ns": dt_ns,
                "summary": summary,
            }
        )
    _write_json(data_dir / "certificate_replay_summary.json", {"certificates": replay_rows})

    # Dataset 1: Theorem 1.6 exact Legendre slice polynomials across k=2..5, l=0..k-1
    exp1_rows = []
    for k in range(2, 6):
        for l in range(k):
            R = compute_legendre_slice_R(k, l)
            max_dr = max(dr for (dr, _) in R)
            max_ds = max(ds for (_, ds) in R)
            # Compute common denominator of R_l(r, s)
            den_lcm = 1
            for v in R.values():
                a, b = den_lcm, v.denominator
                x, y = a, b
                while y:
                    x, y = y, x % y
                den_lcm = (a // x) * b
            exp1_rows.append(
                {
                    "k": k,
                    "l": l,
                    "num_monomials": len(R),
                    "max_deg_r": max_dr,
                    "max_deg_s": max_ds,
                    "common_denom": den_lcm,
                    "marginal_integral": frac_to_canon_str(Fraction(2, int_fact(k))),
                    "symmetry_constraints": (3 * k * (k - 1)) // 2,
                    "poly_dof": k,
                }
            )
    _write_json(data_dir / "exp1_legendre_miracle_atlas.json", {"rows": exp1_rows})

    # Dataset 2: Proposition 3.7 filling-norm witness family F_{a,b,ab}(x) across (a,b)
    exp2_rows = []
    for a, b in [(2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (4, 5), (5, 6)]:
        c = a * b
        pa = [1] + [0] * (a - 1) + [-1]
        pb = [1] + [0] * (b - 1) + [-1]
        p1 = [1, -1]
        pc = [1] + [0] * (c - 1) + [-1]
        F = poly_sub_z(poly_mul_z(pa, pb), poly_mul_z(p1, pc))
        q = list(F)
        for _ in range(3):
            q, rem = poly_divmod_monic_or_unit_z(q, [1, -1])
            assert rem == [0]
        exp2_rows.append(
            {
                "a": a,
                "b": b,
                "c": c,
                "f_deg": len(F) - 1,
                "f_l1": poly_l1_z(F),
                "quotient_deg": len(q) - 1,
                "quotient_l1": poly_l1_z(q),
            }
        )
    _write_json(data_dir / "exp2_prop37_filling_witnesses.json", {"rows": exp2_rows})

    # Dataset 3: Cyclotomic polynomial L^1 norms and totient degrees for m=2..24
    exp3_rows = []
    for m in range(2, 25):
        phi = build_cyclotomic_poly(m)
        exp3_rows.append(
            {
                "m": m,
                "totient_deg": len(phi) - 1,
                "phi_l1": poly_l1_z(phi),
                "max_abs_coeff": max(abs(c) for c in phi),
            }
        )
    _write_json(data_dir / "exp3_cyclotomic_norms.json", {"rows": exp3_rows})

    total_ms = sum(r["verify_ns"] for r in replay_rows) / 1_000_000
    min_ms = min(r["verify_ns"] for r in replay_rows) / 1_000_000
    max_ms = max(r["verify_ns"] for r in replay_rows) / 1_000_000
    print(f"Generated & verified 16/16 canonical POLY-DECOMP-CERT-1.0 certificates ({min_ms:.3f}-{max_ms:.3f} ms, total {total_ms:.2f} ms).")


if __name__ == "__main__":
    main()
