"""Live 60-attack adversarial red-team test suite for POLY-DECOMP-CERT-1.0.

Tests 12 global schema/typing/depth/control-char/canonical-rational attacks + 12 domain attacks per mode.
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
import sys
from typing import Any, Callable, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.polydecomp_certifier import verify_certificate


def _load(name: str) -> dict[str, Any]:
    return json.loads((ROOT / "certificates" / f"{name}.json").read_text(encoding="utf-8"))


def _mutate(cert: dict[str, Any], fn: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    c = copy.deepcopy(cert)
    fn(c)
    return c


def build_attacks() -> List[Tuple[str, str, Any]]:
    m1 = _load("m1_thm16_legendre_k3_l0")
    m2 = _load("m2_basic_decomp_k3_cancellation")
    m3 = _load("m3_tomography_3dir_diag_5x5")
    m4_p37 = _load("m4_prop37_filling_witness_2_3_6")
    m4_cyc = _load("m4_cyclotomic_factorization_m12")

    attacks: List[Tuple[str, str, Any]] = []

    # --- 12 Global Schema / Type / Depth / Control-Char / Canonical-Rational Attacks ---
    attacks.append(("global", "g01_wrong_schema_version", _mutate(m1, lambda c: c.__setitem__("schema_version", "POLY-DECOMP-CERT-2.0"))))
    attacks.append(("global", "g02_unknown_mode", _mutate(m1, lambda c: c.__setitem__("mode", "bogus_mode"))))
    attacks.append(("global", "g03_extra_top_key", _mutate(m1, lambda c: c.__setitem__("extra", 1))))
    attacks.append(("global", "g04_missing_payload_key", _mutate(m1, lambda c: c["payload"].pop("k"))))
    attacks.append(("global", "g05_raw_float_injected", _mutate(m1, lambda c: c["payload"].__setitem__("k", 3.0))))
    attacks.append(("global", "g06_bool_as_int_k", _mutate(m1, lambda c: c["payload"].__setitem__("k", True))))
    attacks.append(("global", "g07_int_as_bool_sym_neg", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_sym_neg_ok", 1))))
    attacks.append(("global", "g08_nul_control_char_in_id", _mutate(m1, lambda c: c.__setitem__("cert_id", "bad\x00id"))))
    attacks.append(("global", "g09_neg_zero_canon_rat", _mutate(m1, lambda c: c["payload"]["claimed_L_km1"].__setitem__(1, "-0"))))
    attacks.append(("global", "g10_unreduced_canon_rat", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_marginal_integral", "2/6"))))
    attacks.append(("global", "g11_excess_int_bits", _mutate(m4_p37, lambda c: c["payload"].__setitem__("claimed_cramer_val", 1 << 2100))))

    def _deep_nest(c: dict[str, Any]) -> None:
        node: Any = "leaf"
        for _ in range(40):
            node = [node]
        c["payload"]["claimed_L_km1"] = node

    attacks.append(("global", "g12_excess_json_depth", _mutate(m1, _deep_nest)))

    # --- 12 Mode 1 Domain Attacks ---
    attacks.append(("mode1", "m1_01_k_out_of_range", _mutate(m1, lambda c: c["payload"].__setitem__("k", 1))))
    attacks.append(("mode1", "m1_02_l_out_of_range", _mutate(m1, lambda c: c["payload"].__setitem__("l", 3))))
    attacks.append(("mode1", "m1_03_wrong_legendre_coeff", _mutate(m1, lambda c: c["payload"]["claimed_L_km1"].__setitem__(0, "-1"))))
    attacks.append(("mode1", "m1_04_wrong_R_coeff", _mutate(m1, lambda c: c["payload"]["claimed_R_coeffs"].__setitem__("0,0", "1/4"))))
    attacks.append(("mode1", "m1_05_explicit_zero_monomial", _mutate(m1, lambda c: c["payload"]["claimed_R_coeffs"].__setitem__("1,0", "0"))))
    attacks.append(("mode1", "m1_06_malformed_monomial_key", _mutate(m1, lambda c: c["payload"]["claimed_R_coeffs"].__setitem__("bad", "1"))))
    attacks.append(("mode1", "m1_07_wrong_marginal_integral", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_marginal_integral", "1/2"))))
    attacks.append(("mode1", "m1_08_wrong_max_deg_r", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_max_deg_r", 1))))
    attacks.append(("mode1", "m1_09_wrong_max_deg_s", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_max_deg_s", 1))))
    attacks.append(("mode1", "m1_10_false_sym_swap", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_sym_swap_ok", False))))
    attacks.append(("mode1", "m1_11_wrong_sym_constraints", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_symmetry_constraints", 6))))
    attacks.append(("mode1", "m1_12_nonlist_L_no_crash", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_L_km1", "bad"))))

    # --- 12 Mode 2 Domain Attacks ---
    attacks.append(("mode2", "m2_01_wrong_m_vec_len", _mutate(m2, lambda c: c["payload"]["m_vec"].pop())))
    attacks.append(("mode2", "m2_02_zero_m_vec_entry", _mutate(m2, lambda c: c["payload"]["m_vec"].__setitem__(0, 0))))
    attacks.append(("mode2", "m2_03_trailing_zero_target", _mutate(m2, lambda c: c["payload"]["target_poly"].append(0))))
    attacks.append(("mode2", "m2_04_sum_mismatch_target", _mutate(m2, lambda c: c["payload"]["target_poly"].__setitem__(0, c["payload"]["target_poly"][0] + 1))))
    attacks.append(("mode2", "m2_05_invalid_term_sign_zero", _mutate(m2, lambda c: c["payload"]["terms"][0].__setitem__("sign", 0))))
    attacks.append(("mode2", "m2_06_zero_a_vec_entry", _mutate(m2, lambda c: c["payload"]["terms"][0]["a_vec"].__setitem__(0, 0))))
    attacks.append(("mode2", "m2_07_neg_shift_a", _mutate(m2, lambda c: c["payload"]["terms"][0].__setitem__("shift_a", -1))))
    attacks.append(("mode2", "m2_08_wrong_quotient", _mutate(m2, lambda c: c["payload"]["claimed_quotient_by_1mx_k"].__setitem__(0, 999))))
    attacks.append(("mode2", "m2_09_wrong_target_l1", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_target_l1", 999))))
    attacks.append(("mode2", "m2_10_wrong_decomp_cost", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_decomp_l1_cost", 1))))
    attacks.append(("mode2", "m2_11_wrong_term_count", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_term_count", 2))))
    attacks.append(("mode2", "m2_12_nonlist_terms_no_crash", _mutate(m2, lambda c: c["payload"].__setitem__("terms", 123))))

    # --- 12 Mode 3 Domain Attacks ---
    attacks.append(("mode3", "m3_01_non_primitive_direction", _mutate(m3, lambda c: c["payload"]["directions"].__setitem__(0, [2, 0]))))
    attacks.append(("mode3", "m3_02_collinear_directions", _mutate(m3, lambda c: c["payload"]["directions"].__setitem__(1, [-1, 0]))))
    attacks.append(("mode3", "m3_03_zero_direction", _mutate(m3, lambda c: c["payload"]["directions"].__setitem__(0, [0, 0]))))
    attacks.append(("mode3", "m3_04_xray_mismatch_A_B", _mutate(m3, lambda c: c["payload"]["grid_B"][0].__setitem__(0, c["payload"]["grid_B"][0][0] + 1))))
    attacks.append(("mode3", "m3_05_switch_out_of_bounds", _mutate(m3, lambda c: c["payload"]["switch_steps"][0].__setitem__("origin", [4, 4]))))
    attacks.append(("mode3", "m3_06_switch_invalid_sign", _mutate(m3, lambda c: c["payload"]["switch_steps"][0].__setitem__("sign", 2))))
    attacks.append(("mode3", "m3_07_switch_zero_scale", _mutate(m3, lambda c: c["payload"]["switch_steps"][0]["scales"].__setitem__(0, 0))))
    attacks.append(("mode3", "m3_08_truncated_switch_chain", _mutate(m3, lambda c: c["payload"]["switch_steps"].pop())))
    attacks.append(("mode3", "m3_09_wrong_diff_l1", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_diff_l1", 1))))
    attacks.append(("mode3", "m3_10_wrong_step_count", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_step_count", 9))))
    attacks.append(("mode3", "m3_11_wrong_max_abs", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_max_abs_entry", 99))))
    attacks.append(("mode3", "m3_12_nonlist_grid_no_crash", _mutate(m3, lambda c: c["payload"].__setitem__("grid_A", "bad"))))

    # --- 12 Mode 4 Domain Attacks ---
    attacks.append(("mode4", "m4_01_unknown_submode", _mutate(m4_p37, lambda c: c["payload"].__setitem__("submode", "bogus"))))
    attacks.append(("mode4", "m4_02_prop37_c_neq_ab", _mutate(m4_p37, lambda c: c["payload"].__setitem__("c", 7))))
    attacks.append(("mode4", "m4_03_prop37_base_t_too_small", _mutate(m4_p37, lambda c: c["payload"].__setitem__("base_t", 11))))
    attacks.append(("mode4", "m4_04_prop37_z3_zero", _mutate(m4_p37, lambda c: c["payload"]["cramer_z"].__setitem__(3, 0))))
    attacks.append(("mode4", "m4_05_prop37_z0_exceeds_B", _mutate(m4_p37, lambda c: c["payload"]["cramer_z"].__setitem__(0, 6))))
    attacks.append(("mode4", "m4_06_prop37_wrong_cramer_val", _mutate(m4_p37, lambda c: c["payload"].__setitem__("claimed_cramer_val", 42))))
    attacks.append(("mode4", "m4_07_prop37_wrong_f_l1", _mutate(m4_p37, lambda c: c["payload"].__setitem__("claimed_f_l1", 4))))
    attacks.append(("mode4", "m4_08_prop37_wrong_eq_count", _mutate(m4_p37, lambda c: c["payload"].__setitem__("claimed_eq_count", 16))))
    attacks.append(("mode4", "m4_09_cyclo_missing_divisor", _mutate(m4_cyc, lambda c: c["payload"]["claimed_divisors"].pop())))
    attacks.append(("mode4", "m4_10_cyclo_wrong_phi_coeff", _mutate(m4_cyc, lambda c: c["payload"]["claimed_phi_polys"]["12"].__setitem__(2, 1))))
    attacks.append(("mode4", "m4_11_cyclo_wrong_l1", _mutate(m4_cyc, lambda c: c["payload"].__setitem__("claimed_phi_m_l1", 5))))
    attacks.append(("mode4", "m4_12_cyclo_non_dict_phis_no_crash", _mutate(m4_cyc, lambda c: c["payload"].__setitem__("claimed_phi_polys", []))))

    assert len(attacks) == 60, f"Expected 60 attacks, got {len(attacks)}"
    return attacks


def run_red_team_suite() -> Tuple[int, int, List[str]]:
    attacks = build_attacks()
    rejected = 0
    failures: List[str] = []
    for cat, name, payload in attacks:
        ok, _, _ = verify_certificate(payload)
        if not ok:
            rejected += 1
        else:
            failures.append(f"[{cat}] {name} was UNEXPECTEDLY ACCEPTED!")
    return rejected, len(attacks), failures


def main() -> None:
    rejected, total, failures = run_red_team_suite()
    if failures:
        for f in failures:
            print("FAIL:", f)
        sys.exit(1)
    print(f"Adversarial red-team audit: {rejected}/{total} forged payloads REJECTED (100%).")


if __name__ == "__main__":
    main()
