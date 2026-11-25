"""Comprehensive pytest & 60-attack live adversarial red-team suite for Paper 37:
EUCLIDEAN-DIAM-CERT-1.0 (Giliberti & Hajiaghayi, arXiv:2611.33139).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.diameter_certifier import DiameterCertificateError, verify_diameter_certificate_exact

CERT_DIR = ROOT / "certificates"


def _load(name: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{name}.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_verify() -> None:
    paths = sorted(CERT_DIR.glob("*.json"))
    assert len(paths) == 16, f"Expected 16 certificates, found {len(paths)}"
    for p in paths:
        res = verify_diameter_certificate_exact(json.loads(p.read_text(encoding="utf-8")))
        assert res["verified"] is True


def _mut(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Dict[str, Any]:
    c = copy.deepcopy(base)
    fn(c)
    return c


def build_60_adversarial_attacks() -> List[Tuple[str, Any]]:
    m1 = _load("m1_alg4_2d_cluster_eta1_5")
    m2 = _load("m2_hull_factor_two_a1581_1000")
    m3 = _load("m3_appendix_a1_factor_two_exact")
    m4 = _load("m4_stream_2d_extreme_deletions")

    attacks: List[Tuple[str, Any]] = [
        # --- Global Schema / Type / Rational Hardening (12 attacks) ---
        ("g01_non_dict_root", [1, 2, 3]),
        ("g02_wrong_schema", _mut(m1, lambda c: c.__setitem__("schema", "EUCLIDEAN-DIAM-CERT-2.0"))),
        ("g03_empty_cert_id", _mut(m1, lambda c: c.__setitem__("cert_id", ""))),
        ("g04_unknown_mode", _mut(m1, lambda c: c.__setitem__("mode", "bogus_mode"))),
        ("g05_float_leak", _mut(m1, lambda c: c.__setitem__("eta", 0.2))),
        ("g06_none_injection", _mut(m1, lambda c: c.__setitem__("eta", None))),
        ("g07_bool_as_int_dim", _mut(m1, lambda c: c.__setitem__("dimension", True))),
        ("g08_unreduced_fraction", _mut(m1, lambda c: c.__setitem__("eta", "2/10"))),
        ("g09_den_one_fraction", _mut(m2, lambda c: c.__setitem__("coord_bound_Delta", "14/1"))),
        ("g10_neg_zero_rat", _mut(m1, lambda c: c["sample_points"][0].__setitem__(0, "-0"))),
        ("g11_oversized_rat_str", _mut(m1, lambda c: c.__setitem__("eta", "1/" + "9" * 4200))),
        ("g12_huge_int_bitlen", _mut(m1, lambda c: c.__setitem__("start_idx", 1 << 3000))),
        # --- Mode 1: Algorithm 4 Variance Certificate (12 attacks) ---
        ("m1_01_extra_key", _mut(m1, lambda c: c.__setitem__("extra", 1))),
        ("m1_02_dim_zero", _mut(m1, lambda c: c.__setitem__("dimension", 0))),
        ("m1_03_eta_above_quarter", _mut(m1, lambda c: c.__setitem__("eta", "1/3"))),
        ("m1_04_eta_zero", _mut(m1, lambda c: c.__setitem__("eta", "0"))),
        ("m1_05_start_idx_oob", _mut(m1, lambda c: c.__setitem__("start_idx", 99))),
        ("m1_06_wrong_b_idx", _mut(m1, lambda c: c.__setitem__("claimed_b_idx", 0))),
        ("m1_07_wrong_iterations", _mut(m1, lambda c: c.__setitem__("claimed_iterations", c["claimed_iterations"] + 1))),
        ("m1_08_wrong_support", _mut(m1, lambda c: c.__setitem__("claimed_support_indices", [0, 1]))),
        ("m1_09_wrong_weights", _mut(m1, lambda c: c.__setitem__("claimed_weights", ["1/2"] * len(c["claimed_weights"])))),
        ("m1_10_tampered_mean", _mut(m1, lambda c: c["claimed_mean"].__setitem__(0, "99"))),
        ("m1_11_tampered_variance", _mut(m1, lambda c: c.__setitem__("claimed_variance", "1"))),
        ("m1_12_tampered_H2", _mut(m1, lambda c: c.__setitem__("claimed_candidate_H2", "1"))),
        # --- Mode 2: Lemma 5.1 Variance Hull & Witness Radius (12 attacks) ---
        ("m2_01_hull_a_eq_1", _mut(m2, lambda c: c.__setitem__("hull_a", "1"))),
        ("m2_02_neg_weight_lambda", _mut(m2, lambda c: c["dist_lambda"].__setitem__(0, "-1/4"))),
        ("m2_03_non_unit_gamma", _mut(m2, lambda c: c["dist_gamma"].__setitem__(4, "1/2"))),
        ("m2_04_y1_outside_hull", _mut(m2, lambda c: c["hull_point_y1"].__setitem__(0, "-20"))),
        ("m2_05_y2_outside_hull", _mut(m2, lambda c: c["hull_point_y2"].__setitem__(0, "20"))),
        ("m2_06_ext_point_inside_ball", _mut(m2, lambda c: c["exterior_point_y"].__setitem__(0, "1"))),
        ("m2_07_coord_exceeds_delta", _mut(m2, lambda c: c.__setitem__("coord_bound_Delta", "1"))),
        ("m2_08_wrong_LS_sq", _mut(m2, lambda c: c.__setitem__("claimed_LS_sq", "39"))),
        ("m2_09_wrong_V_lambda", _mut(m2, lambda c: c.__setitem__("claimed_V_lambda", "11"))),
        ("m2_10_wrong_h_sq", _mut(m2, lambda c: c.__setitem__("claimed_h_sq", "15"))),
        ("m2_11_wrong_y1_y2_sq", _mut(m2, lambda c: c.__setitem__("claimed_y1_y2_sq", "100"))),
        ("m2_12_wrong_RS_q_sq", _mut(m2, lambda c: c.__setitem__("claimed_RS_q_sq", "1"))),
        # --- Mode 3: Appendix A.1 Factor-Two Two-Cap & Exponent Audit (12 attacks) ---
        ("m3_01_lam_below_sqrt2", _mut(m3, lambda c: c.__setitem__("lambda_val", "7/5"))),
        ("m3_02_scale_chain_broken", _mut(m3, lambda c: c.__setitem__("lambda_0", "2"))),
        ("m3_03_hull_exceeds_c", _mut(m3, lambda c: c.__setitem__("a", "2"))),
        ("m3_04_mixed_exceeds_hull", _mut(m3, lambda c: c.__setitem__("kappa", "3/2"))),
        ("m3_05_cap_pt_outside_unit_ball", _mut(m3, lambda c: c["cap_test_points"].append(["4/5", "4/5"]))),
        ("m3_06_cap_pt_below_t0", _mut(m3, lambda c: c["cap_test_points"].append(["1/2", "1/2"]))),
        ("m3_07_second_mask_taylor_too_weak", _mut(m3, lambda c: c.__setitem__("taylor_deg_e", 1))),
        ("m3_08_oracle_margin_failed", _mut(m3, lambda c: c.__setitem__("b0", "11/10"))),
        ("m3_09_work_exponent_nonneg", _mut(m3, lambda c: c.__setitem__("s", "1/1000"))),
        ("m3_10_target_eps_too_high", _mut(m3, lambda c: c.__setitem__("target_eps", "1/1000"))),
        ("m3_11_wrong_hull_sq", _mut(m3, lambda c: c.__setitem__("claimed_hull_sq", "3"))),
        ("m3_12_wrong_eps_lb", _mut(m3, lambda c: c.__setitem__("claimed_eps_lb", "1/10000000000"))),
        # --- Mode 4: Dynamic Stream Chain Replay & 3K Shrinkage (12 attacks) ---
        ("m4_01_B_sched_too_small", _mut(m4, lambda c: c.__setitem__("B_sched", 64))),
        ("m4_02_snapshot_m_too_small", _mut(m4, lambda c: c.__setitem__("snapshot_m", 1000))),
        ("m4_03_shrinkage_violated", _mut(m4, lambda c: c.__setitem__("child_size_Pi1", 10000))),
        ("m4_04_duplicate_insert", _mut(m4, lambda c: c["stream_ops"].insert(2, {"op": "insert", "id": "p1", "point": ["0", "0"]}))),
        ("m4_05_delete_absent_key", _mut(m4, lambda c: c["stream_ops"].insert(2, {"op": "delete", "id": "ghost"}))),
        ("m4_06_unknown_op_kind", _mut(m4, lambda c: c["stream_ops"][0].__setitem__("op", "update"))),
        ("m4_07_stale_deleted_witness", _mut(m4, lambda c: c["checkpoints"][1].__setitem__("witness_pair", ["p5", "p6"]))),
        ("m4_08_uncovered_residual_leaf", _mut(m4, lambda c: c["checkpoints"][0].__setitem__("leaf_ids", []))),
        ("m4_09_invalid_intact_ball_center", _mut(m4, lambda c: c["checkpoints"][0]["balls"][0]["center"].__setitem__(0, "99"))),
        ("m4_10_missing_final_checkpoint", _mut(m4, lambda c: c["checkpoints"].pop())),
        ("m4_11_wrong_final_diam_sq", _mut(m4, lambda c: c.__setitem__("claimed_final_diam_sq", "1"))),
        ("m4_12_poor_witness_violates_approx", _mut(m4, lambda c: (
            c["checkpoints"][0].__setitem__("witness_pair", ["p1", "p2"]),
            c["checkpoints"][0].__setitem__("claimed_witness_sq", "16"),
        ))),
        ("m4_13_invalidated_ball_routing_bypass", _mut(m4, lambda c: (
            c["checkpoints"][0].__setitem__("balls", [{
                "anchor_ids": ["p1"],
                "weights": ["1"],
                "center": ["0", "0"],
                "variance": "1000000",
                "sample_intact": False,
            }]),
            c["checkpoints"][0].__setitem__("leaf_ids", []),
        ))),
        ("m4_14_non_chain_witness_bypass", _mut(m4, lambda c: (
            c["checkpoints"][0].__setitem__("witness_pair", ["p2", "p6"]),
            c["checkpoints"][0].__setitem__("claimed_witness_sq", "173"),
        ))),
    ]
    assert len(attacks) == 62
    return attacks


def test_62_live_adversarial_attacks_rejected() -> None:
    attacks = build_60_adversarial_attacks()
    rejected = 0
    for name, payload in attacks:
        try:
            verify_diameter_certificate_exact(payload)
        except DiameterCertificateError:
            rejected += 1
        else:
            raise AssertionError(f"Adversarial attack {name!r} was NOT rejected!")
    assert rejected == 62


def test_exact_no_float_source_audit() -> None:
    for rel in ["src/diameter_exact.py", "src/diameter_certifier.py"]:
        src = (ROOT / rel).read_text(encoding="utf-8")
        assert "float(" not in src, f"float() found in {rel}"
        assert "math.sqrt" not in src, f"math.sqrt found in {rel}"
        assert "numpy" not in src, f"numpy found in {rel}"
