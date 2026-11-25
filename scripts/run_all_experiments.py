"""Generate all 16 canonical EUCLIDEAN-DIAM-CERT-1.0 certificates and 4 exact-Q
experimental studies for Paper 37: Giliberti & Hajiaghayi (arXiv:2611.33139).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.diameter_certifier import SCHEMA_VERSION, verify_diameter_certificate_exact
from src.diameter_exact import (
    PointQ,
    exact_diameter_sq_q,
    format_rat,
    mean_and_variance_q,
    run_algorithm4_exact,
    sq_dist_q,
    taylor_exp_lb_q,
)

CERT_DIR = ROOT / "certificates"
DATA_DIR = ROOT / "data"


def _pt_json(pt: PointQ) -> List[str]:
    return [format_rat(c) for c in pt]


def _make_mode1_cert(
    cert_id: str,
    sample: List[PointQ],
    eta: Fraction,
    start_idx: int,
    test_query_y: PointQ,
) -> Dict[str, Any]:
    res = run_algorithm4_exact(sample, eta, start_idx=start_idx)
    supp_pts = [sample[i] for i in res["support_indices"]]
    h2 = max(sq_dist_q(p, test_query_y) for p in supp_pts)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "variance_certificate_alg4",
        "cert_id": cert_id,
        "dimension": len(sample[0]),
        "sample_points": [_pt_json(p) for p in sample],
        "eta": format_rat(eta),
        "start_idx": start_idx,
        "test_query_y": _pt_json(test_query_y),
        "claimed_b_idx": res["b_idx"],
        "claimed_iterations": res["iterations"],
        "claimed_support_indices": res["support_indices"],
        "claimed_weights": [format_rat(w) for w in res["weights"]],
        "claimed_mean": _pt_json(res["mean"]),
        "claimed_variance": format_rat(res["variance"]),
        "claimed_max_r2": format_rat(res["max_r2"]),
        "claimed_candidate_H2": format_rat(h2),
    }


def _make_mode2_cert(
    cert_id: str,
    sample: List[PointQ],
    hull_a: Fraction,
    lam: List[Fraction],
    gam: List[Fraction],
    y1: PointQ,
    y2: PointQ,
    y_ext: PointQ,
    q_cen: PointQ,
    delta: Fraction,
) -> Dict[str, Any]:
    ls_sq, _ = exact_diameter_sq_q(sample)
    mu_l, v_l = mean_and_variance_q(sample, lam)
    mu_g, v_g = mean_and_variance_q(sample, gam)
    h_sq = sq_dist_q(mu_l, mu_g)
    y1_y2_sq = sq_dist_q(y1, y2)
    rs_q_sq = max(sq_dist_q(s, q_cen) for s in sample)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "variance_hull_and_tightness",
        "cert_id": cert_id,
        "dimension": len(sample[0]),
        "sample_points": [_pt_json(p) for p in sample],
        "hull_a": format_rat(hull_a),
        "dist_lambda": [format_rat(w) for w in lam],
        "dist_gamma": [format_rat(w) for w in gam],
        "hull_point_y1": _pt_json(y1),
        "hull_point_y2": _pt_json(y2),
        "exterior_point_y": _pt_json(y_ext),
        "witness_center_q": _pt_json(q_cen),
        "coord_bound_Delta": format_rat(delta),
        "claimed_LS_sq": format_rat(ls_sq),
        "claimed_V_lambda": format_rat(v_l),
        "claimed_V_gamma": format_rat(v_g),
        "claimed_h_sq": format_rat(h_sq),
        "claimed_y1_y2_sq": format_rat(y1_y2_sq),
        "claimed_RS_q_sq": format_rat(rs_q_sq),
    }


def _make_mode3_cert(
    cert_id: str,
    target_c: Fraction,
    a: Fraction,
    q_scale: Fraction,
    lam0: Fraction,
    lam: Fraction,
    eta_mask: Fraction,
    r2: Fraction,
    t0: Fraction,
    cap_pts: List[Tuple[Fraction, Fraction]],
    eta_in: Fraction,
    kappa: Fraction,
    b0: Fraction,
    nu: Fraction,
    e0: Fraction,
    b_kappa: int,
    s: Fraction,
    g_ratio: int,
    deg_half: int,
    deg_e: int,
    target_eps: Fraction,
) -> Dict[str, Any]:
    hull_sq = Fraction(2, 1) * a * a - Fraction(1, 1)
    mixed_sq = (Fraction(1, 1) + eta_in) ** 2 + a * a * kappa * kappa
    cand_sq = (Fraction(1, 1) + eta_in) ** 2 + Fraction(1, 1)
    m_val = lam * lam / Fraction(2, 1) - Fraction(1, 1)
    second_mask_lb = taylor_exp_lb_q(Fraction(1, 1), deg_e) * m_val
    oracle_lhs = kappa * (Fraction(1, 1) - nu - Fraction(2, 1) * e0)
    rho = s / Fraction(2, 1)
    theta_exp = rho / Fraction(12 * (g_ratio + 1), 1)
    eps_lb = theta_exp / Fraction(2 * b_kappa, 1)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "factor_two_two_cap_audit",
        "cert_id": cert_id,
        "target_c": format_rat(target_c),
        "a": format_rat(a),
        "q_scale": format_rat(q_scale),
        "lambda_0": format_rat(lam0),
        "lambda_val": format_rat(lam),
        "eta_mask": format_rat(eta_mask),
        "r2": format_rat(r2),
        "cap_split_t0": format_rat(t0),
        "cap_test_points": [[format_rat(t), format_rat(q)] for t, q in cap_pts],
        "eta_in": format_rat(eta_in),
        "kappa": format_rat(kappa),
        "b0": format_rat(b0),
        "nu": format_rat(nu),
        "e0": format_rat(e0),
        "B_kappa": b_kappa,
        "s": format_rat(s),
        "G": g_ratio,
        "taylor_deg_half": deg_half,
        "taylor_deg_e": deg_e,
        "target_eps": format_rat(target_eps),
        "claimed_hull_sq": format_rat(hull_sq),
        "claimed_mixed_sq": format_rat(mixed_sq),
        "claimed_cand_sq": format_rat(cand_sq),
        "claimed_m_second_mask": format_rat(m_val),
        "claimed_second_mask_lb": format_rat(second_mask_lb),
        "claimed_oracle_lhs": format_rat(oracle_lhs),
        "claimed_eps_lb": format_rat(eps_lb),
    }


def _build_checkpoint_from_active(
    after_op: int,
    active: Dict[str, PointQ],
    eta: Fraction,
    ball_specs: List[Tuple[List[str], bool]],
) -> Dict[str, Any]:
    """Construct an exact ball-chain checkpoint given active dict and ordered sample key lists."""
    one_plus_eta_sq = (Fraction(1, 1) + eta) ** 2
    remaining = set(active.keys())
    balls_json: List[Dict[str, Any]] = []
    best_pair = None
    best_sq = Fraction(-1, 1)

    for sample_ids, intact in ball_specs:
        # Build ball from sample_ids (if intact, all must be in remaining; if invalidated, compute from stored coords)
        pts = [active[k] for k in sample_ids if k in active]
        if not pts:
            continue
        res = run_algorithm4_exact(pts, eta, start_idx=0)
        present_ids = [k for k in sample_ids if k in active]
        anchor_ids = [present_ids[i] for i in res["support_indices"]]
        center = res["mean"]
        var = res["variance"]
        balls_json.append(
            {
                "anchor_ids": anchor_ids,
                "weights": [format_rat(w) for w in res["weights"]],
                "center": _pt_json(center),
                "variance": format_rat(var),
                "sample_intact": intact,
            }
        )
        if intact:
            for aid in anchor_ids:
                for pid in sorted(remaining):
                    d2 = sq_dist_q(active[aid], active[pid])
                    if d2 > best_sq:
                        best_sq = d2
                        best_pair = [aid, pid]
            rad_sq = one_plus_eta_sq * var
            remaining = {pid for pid in remaining if sq_dist_q(active[pid], center) > rad_sq}

    leaf_ids = sorted(remaining)
    for i in range(len(leaf_ids)):
        for j in range(i + 1, len(leaf_ids)):
            d2 = sq_dist_q(active[leaf_ids[i]], active[leaf_ids[j]])
            if d2 > best_sq:
                best_sq = d2
                best_pair = [leaf_ids[i], leaf_ids[j]]

    exact_d2, _ = exact_diameter_sq_q(list(active.values()))
    assert best_pair is not None and best_sq >= 0
    return {
        "after_op": after_op,
        "balls": balls_json,
        "leaf_ids": leaf_ids,
        "witness_pair": best_pair,
        "claimed_witness_sq": format_rat(best_sq),
        "claimed_exact_diam_sq": format_rat(exact_d2),
    }


def _make_mode4_cert(
    cert_id: str,
    dim: int,
    eta: Fraction,
    b_sched: int,
    snap_m: int,
    pi_sz: int,
    pi1_sz: int,
    ops: List[Dict[str, Any]],
    ckpt_specs: Dict[int, List[Tuple[List[str], bool]]],
) -> Dict[str, Any]:
    active: Dict[str, PointQ] = {}
    checkpoints: List[Dict[str, Any]] = []
    final_d2 = Fraction(0, 1)
    final_w2 = Fraction(0, 1)

    for step_idx, op in enumerate(ops, start=1):
        if op["op"] == "insert":
            active[op["id"]] = tuple(Fraction(s) for s in op["point"])
        else:
            del active[op["id"]]
        if step_idx in ckpt_specs:
            ck = _build_checkpoint_from_active(step_idx, active, eta, ckpt_specs[step_idx])
            checkpoints.append(ck)
            final_d2 = Fraction(ck["claimed_exact_diam_sq"])
            final_w2 = Fraction(ck["claimed_witness_sq"])

    return {
        "schema": SCHEMA_VERSION,
        "mode": "dynamic_stream_chain_replay",
        "cert_id": cert_id,
        "dimension": dim,
        "eta": format_rat(eta),
        "B_sched": b_sched,
        "snapshot_m": snap_m,
        "parent_size_Pi": pi_sz,
        "child_size_Pi1": pi1_sz,
        "stream_ops": ops,
        "checkpoints": checkpoints,
        "claimed_final_size": len(active),
        "claimed_final_diam_sq": format_rat(final_d2),
        "claimed_final_witness_sq": format_rat(final_w2),
    }


def build_all_certificates() -> List[Dict[str, Any]]:
    certs: List[Dict[str, Any]] = []

    # =========================================================================
    # Mode 1: 4 canonical Algorithm 4 variance certificates
    # =========================================================================
    # 1a: 2D pentagon-like asymmetric rational cluster, eta = 1/5
    s1a: List[PointQ] = [
        (Fraction(0), Fraction(0)),
        (Fraction(6), Fraction(0)),
        (Fraction(3), Fraction(5)),
        (Fraction(1), Fraction(4)),
        (Fraction(5), Fraction(4)),
        (Fraction(3), Fraction(-2)),
        (Fraction(2), Fraction(2)),
    ]
    certs.append(_make_mode1_cert("m1_alg4_2d_cluster_eta1_5", s1a, Fraction(1, 5), 0, (Fraction(10), Fraction(8))))

    # 1b: 3D regular tetrahedron embedded in cube vertices + interior points, eta = 1/4
    s1b: List[PointQ] = [
        (Fraction(1), Fraction(1), Fraction(1)),
        (Fraction(1), Fraction(-1), Fraction(-1)),
        (Fraction(-1), Fraction(1), Fraction(-1)),
        (Fraction(-1), Fraction(-1), Fraction(1)),
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(1, 2), Fraction(0), Fraction(-1, 2)),
    ]
    certs.append(_make_mode1_cert("m1_alg4_3d_tetrahedron_eta1_4", s1b, Fraction(1, 4), 0, (Fraction(4), Fraction(3), Fraction(-2))))

    # 1c: 4D skewed cross-polytope + outlier, eta = 1/8
    s1c: List[PointQ] = [
        (Fraction(4), Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(-2), Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(3), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(-3), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(3), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(-2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0), Fraction(3)),
        (Fraction(1), Fraction(1), Fraction(1), Fraction(-2)),
    ]
    certs.append(_make_mode1_cert("m1_alg4_4d_cross_eta1_8", s1c, Fraction(1, 8), 1, (Fraction(-5), Fraction(4), Fraction(3), Fraction(2))))

    # 1d: 6D simplex vertices + offset point, eta = 1/6
    s1d: List[PointQ] = [
        tuple(Fraction(2 if j == i else 0) for j in range(6)) for i in range(6)
    ] + [(Fraction(-1), Fraction(0), Fraction(1), Fraction(0), Fraction(1), Fraction(0))]
    certs.append(_make_mode1_cert("m1_alg4_6d_simplex_eta1_6", s1d, Fraction(1, 6), 0, (Fraction(5), Fraction(-3), Fraction(2), Fraction(4), Fraction(-1), Fraction(3))))

    # =========================================================================
    # Mode 2: 4 canonical Lemma 5.1 Variance-Hull & Two-Simplex Tightness certs
    # =========================================================================
    # 2a: Exact rational two-orthogonal-simplex tightness realization at a = 3/2 (sqrt(2a^2-1) = sqrt(7/2))
    # Two orthogonal 4-vertex regular tetrahedra in R^7:
    # Axis coord x0 = +- h/2; simplex 1 in coords (1,2,3) with vertices (+-r, +-r, +-r) even sign flips;
    # simplex 2 in coords (4,5,6) with vertices (+-r, +-r, +-r) even sign flips!
    # Variance of each tetrahedron = 3 r^2. Distance between centers = h.
    # For a = 3/2, a^2 - 1 = 5/4, 2a^2 - 1 = 7/2. Take h = 4, r = 2 -> V = 12, h^2 + 2V = 16 + 24 = 40.
    # Within-simplex edge^2 = 8 r^2 = 32 <= 40! So L_S^2 = 40 EXACTLY!
    # Hull ball radius^2 = (a^2 - 1) * V = (5/4) * 12 = 15. Largest rational push along x0 with t^2 <= 15 is t = 19/5 (361/25 = 14.44 <= 15)!
    # Outermost pair y1 = (-2 - 19/5, 0..0), y2 = (2 + 19/5, 0..0): ||y1 - y2||^2 = (58/5)^2 = 3364/25 = 134.56 vs (7/2)*40 = 140 (96.1% of exact bound!)
    tet_signs = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
    s2a: List[PointQ] = [
        (Fraction(-2), Fraction(2 * a_), Fraction(2 * b_), Fraction(2 * c_), Fraction(0), Fraction(0), Fraction(0))
        for a_, b_, c_ in tet_signs
    ] + [
        (Fraction(2), Fraction(0), Fraction(0), Fraction(0), Fraction(2 * a_), Fraction(2 * b_), Fraction(2 * c_))
        for a_, b_, c_ in tet_signs
    ]
    lam2a = [Fraction(1, 4)] * 4 + [Fraction(0)] * 4
    gam2a = [Fraction(0)] * 4 + [Fraction(1, 4)] * 4
    y1_2a = (Fraction(-29, 5), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    y2_2a = (Fraction(29, 5), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    yext_2a = (Fraction(12), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    q_2a = (Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    certs.append(_make_mode2_cert("m2_hull_two_tetrahedra_a3_2", s2a, Fraction(3, 2), lam2a, gam2a, y1_2a, y2_2a, yext_2a, q_2a, Fraction(12)))

    # 2b: Exact paper factor-two hull parameter a = 1581/1000 on two orthogonal 4-tetrahedra!
    # At a = 1581/1000, a^2 - 1 = 1499561/1000000 ~ 1.499561, 2a^2 - 1 = 3.999122.
    # Optimal h^2 / V = 1 / (a^2 - 1) ~ 2/3 -> pick h = 4, r = 2 -> V = 12, h^2 = 16, h^2 + 2V = 40, edge^2 = 32 <= 40!
    # Radius^2 = (a^2 - 1)*12 = 17.994732 -> push t = 424/100 = 106/25 (t^2 = 17.9776 <= 17.994732)!
    # ||y1 - y2||^2 = (4 + 212/25)^2 = (312/25)^2 = 155.7504 vs (2a^2 - 1)*40 = 159.96488 (97.37% of tight factor-two hull!)
    y1_2b = (Fraction(-156, 25), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    y2_2b = (Fraction(156, 25), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    yext_2b = (Fraction(14), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    certs.append(_make_mode2_cert("m2_hull_factor_two_a1581_1000", s2a, Fraction(1581, 1000), lam2a, gam2a, y1_2b, y2_2b, yext_2b, q_2a, Fraction(14)))

    # 2c: Near-sqrt(2) barrier test at a = 71/50 = 1.42 (a^2 = 2.0164 > 2, 2a^2 - 1 = 3.0328 ~ 3)
    # Using two orthogonal regular 8-simplices? No, even cleaner: two orthogonal 3-cubes/cross-polytopes or 4-tetrahedra with h=2, r=1:
    # V = 3, h^2 = 4, h^2 + 2V = 10, edge^2 = 8 <= 10. (a^2-1)*V = 1.0164*3 = 3.0492 -> push t = 7/4 (49/16 = 3.0625 too big) -> t = 17/10 (2.89 <= 3.0492).
    s2c: List[PointQ] = [
        (Fraction(-1), Fraction(a_), Fraction(b_), Fraction(c_), Fraction(0), Fraction(0), Fraction(0))
        for a_, b_, c_ in tet_signs
    ] + [
        (Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(a_), Fraction(b_), Fraction(c_))
        for a_, b_, c_ in tet_signs
    ]
    y1_2c = (Fraction(-27, 10), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    y2_2c = (Fraction(27, 10), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    yext_2c = (Fraction(6), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    certs.append(_make_mode2_cert("m2_hull_near_sqrt2_a71_50", s2c, Fraction(71, 50), lam2a, gam2a, y1_2c, y2_2c, yext_2c, q_2a, Fraction(6)))

    # 2d: Exact integer-attained 2D square hull at a = sqrt(5)/... pick rational a = 5/3 (a^2 - 1 = 16/9 = (4/3)^2!)
    # Sample: 4 vertices of square (+-3, +-3) in R^2 -> L_S^2 = 72.
    # lambda = uniform on left edge (-3, +-3): mu=(-3,0), V=9, radius = (4/3)*3 = 4!
    # gamma = uniform on right edge (+3, +-3): mu=(+3,0), V=9, radius = 4!
    # h = 6, h^2 + 2V = 36 + 18 = 54 <= 72. y1 = (-7, 0), y2 = (7, 0): ||y1-y2||^2 = 196 <= (41/9)*72 = 328!
    s2d: List[PointQ] = [
        (Fraction(-3), Fraction(3)),
        (Fraction(-3), Fraction(-3)),
        (Fraction(3), Fraction(3)),
        (Fraction(3), Fraction(-3)),
    ]
    certs.append(
        _make_mode2_cert(
            "m2_hull_2d_square_a5_3",
            s2d,
            Fraction(5, 3),
            [Fraction(1, 2), Fraction(1, 2), Fraction(0), Fraction(0)],
            [Fraction(0), Fraction(0), Fraction(1, 2), Fraction(1, 2)],
            (Fraction(-7), Fraction(0)),
            (Fraction(7), Fraction(0)),
            (Fraction(10), Fraction(0)),
            (Fraction(0), Fraction(0)),
            Fraction(10),
        )
    )

    # =========================================================================
    # Mode 3: 4 canonical Appendix A.1 Factor-Two & Sharpened Parameter Audits
    # =========================================================================
    cap_pts_345: List[Tuple[Fraction, Fraction]] = [
        (Fraction(3, 5), Fraction(16, 25)),   # exact boundary rim t=3/5, q=16/25
        (Fraction(3, 5), Fraction(0)),        # cap base center
        (Fraction(4, 5), Fraction(9, 25)),    # 3-4-5 dual boundary point
        (Fraction(1, 1), Fraction(0)),        # north pole
        (Fraction(7, 10), Fraction(1, 2)),    # interior point t^2+q = 0.49+0.50 = 0.99
    ]
    # 3a: Exact Giliberti & Hajiaghayi Table 3 / Appendix A.1 parameter choice verbatim (deg_half=3, deg_e=4)
    certs.append(
        _make_mode3_cert(
            "m3_appendix_a1_factor_two_exact",
            target_c=Fraction(2, 1),
            a=Fraction(1581, 1000),
            q_scale=Fraction(5001, 5000),
            lam0=Fraction(7903, 5000),
            lam=Fraction(79, 50),
            eta_mask=Fraction(1, 20),
            r2=Fraction(4, 5),
            t0=Fraction(3, 5),
            cap_pts=cap_pts_345,
            eta_in=Fraction(1, 100),
            kappa=Fraction(109, 100),
            b0=Fraction(27, 25),
            nu=Fraction(1, 10000),
            e0=Fraction(1, 400),
            b_kappa=2000,
            s=Fraction(1, 2003),
            g_ratio=32,
            deg_half=3,
            deg_e=4,
            target_eps=Fraction(1, 10**10),
        )
    )
    # 3b: High-order Taylor refinement (deg_half=8, deg_e=10) certifying tighter mask slack at same Table 3 params
    certs.append(
        _make_mode3_cert(
            "m3_appendix_a1_taylor_refined",
            target_c=Fraction(2, 1),
            a=Fraction(1581, 1000),
            q_scale=Fraction(5001, 5000),
            lam0=Fraction(7903, 5000),
            lam=Fraction(79, 50),
            eta_mask=Fraction(1, 20),
            r2=Fraction(4, 5),
            t0=Fraction(3, 5),
            cap_pts=cap_pts_345,
            eta_in=Fraction(1, 100),
            kappa=Fraction(109, 100),
            b0=Fraction(27, 25),
            nu=Fraction(1, 10000),
            e0=Fraction(1, 400),
            b_kappa=2000,
            s=Fraction(1, 2003),
            g_ratio=32,
            deg_half=8,
            deg_e=10,
            target_eps=Fraction(3, 2 * 10**10),  # 1.5e-10 < 1/6345504000 = 1.5759e-10!
        )
    )
    # 3c: Tighter factor c = 19/10 = 1.9 (below 2, strictly above sqrt(3) ~ 1.7321!)
    # Need 2a^2 - 1 < 3.61 -> a^2 < 2.305 -> a = 151/100 = 1.51 (a^2 = 2.2801, 2a^2-1 = 3.5602 < 3.61)
    # q_scale = 5001/5000, lam0 = 754/500 = 377/250 = 1.508, lam = 150/100 = 3/2 = 1.5 (lam^2 = 2.25 > 2, m = 1/8)
    # Wait: for second mask e * m > (21/20) * r2^2 -> at lam=3/2, m=1/8, e*m ~ 0.3398 < 0.672 -> need smaller r2!
    # Pick t0 = 4/5, r2 = 3/5 (3-4-5 dual cap! r2^2 = 9/25 = 0.36): wait at t0=4/5, (21/20)*9/25 = 189/500 = 0.378;
    # at lam = 31/20 = 1.55 (2a^2-1 = 3.805 < 3.8416 = (49/25)^2 = 1.96^2): m = 1.55^2/2 - 1 = 0.20125, e*m > 0.545 > 0.378!
    # Check c = 196/100 = 49/25 = 1.96: a = 39/25 = 1.56 (2a^2 - 1 = 3.8672? Wait 1.56^2=2.4336, 2*2.4336-1=3.8672 > 3.8416).
    # Pick c = 198/100 = 99/50 = 1.98 (c^2 = 3.9204), a = 156/100 = 39/25 (2a^2-1 = 3.8672 < 3.9204),
    # q_scale = 5001/5000, lam0 = 1559/1000, lam = 1555/1000 = 311/200 (lam^2/2 - 1 = 0.2090125, e*m ~ 0.568 > (21/20)*9/25 = 0.378!).
    # Check F(4/5) at lam = 311/200: x1 = (1.555 - 0.8)^2 / 0.36 - 1 = 0.570025/0.36 - 1 = 0.5834 -> (9/25)*exp(0.5834) ~ 0.645 < 21/20.
    # Aha! That's why t0 = 3/5 is so special! At t0 = 3/5, r2 = 4/5, (21/20)*(16/25) = 0.672, so need m > 0.672/2.718 = 0.2472 -> lam > 1.5794!
    # So at c = 21/10 = 2.1 (c^2 = 4.41), a = 8/5 = 1.60 (2a^2-1 = 4.12 < 4.41), lam = 159/100, kappa = 11/10: even wider margin!
    certs.append(
        _make_mode3_cert(
            "m3_factor_2_1_relaxed_margin",
            target_c=Fraction(21, 10),
            a=Fraction(8, 5),
            q_scale=Fraction(5001, 5000),
            lam0=Fraction(799, 500),
            lam=Fraction(159, 100),
            eta_mask=Fraction(1, 20),
            r2=Fraction(4, 5),
            t0=Fraction(3, 5),
            cap_pts=cap_pts_345,
            eta_in=Fraction(1, 50),
            kappa=Fraction(109, 100),
            b0=Fraction(27, 25),
            nu=Fraction(1, 10000),
            e0=Fraction(1, 400),
            b_kappa=2000,
            s=Fraction(1, 2003),
            g_ratio=32,
            deg_half=4,
            deg_e=5,
            target_eps=Fraction(1, 10**10),
        )
    )
    # 3d: Tighter c = 5/2 = 2.5 (c^2 = 6.25), a = 17/10 = 1.70 (2a^2 - 1 = 4.78 < 6.25),
    # lam = 168/100 = 42/25, smaller G = 16 -> larger space saving eps_0 > 3e-10!
    certs.append(
        _make_mode3_cert(
            "m3_factor_2_5_larger_saving",
            target_c=Fraction(5, 2),
            a=Fraction(17, 10),
            q_scale=Fraction(5001, 5000),
            lam0=Fraction(1695, 1000),
            lam=Fraction(42, 25),
            eta_mask=Fraction(1, 20),
            r2=Fraction(4, 5),
            t0=Fraction(3, 5),
            cap_pts=cap_pts_345,
            eta_in=Fraction(1, 25),
            kappa=Fraction(28, 25),
            b0=Fraction(11, 10),
            nu=Fraction(1, 10000),
            e0=Fraction(1, 400),
            b_kappa=1500,
            s=Fraction(1, 1503),
            g_ratio=16,
            deg_half=4,
            deg_e=5,
            target_eps=Fraction(3, 10**10),
        )
    )

    # =========================================================================
    # Mode 4: 4 canonical Dynamic Stream Insert/Delete Chain & 3K Audits
    # =========================================================================
    # 4a: 2D dynamic stream with extreme-point deletion & exact leaf witness fallback
    ops_4a = [
        {"op": "insert", "id": "p1", "point": ["0", "0"]},
        {"op": "insert", "id": "p2", "point": ["4", "0"]},
        {"op": "insert", "id": "p3", "point": ["2", "3"]},
        {"op": "insert", "id": "p4", "point": ["2", "-2"]},
        {"op": "insert", "id": "p5", "point": ["12", "1"]},
        {"op": "insert", "id": "p6", "point": ["-9", "2"]},
        {"op": "delete", "id": "p5"},
        {"op": "insert", "id": "p7", "point": ["7", "-6"]},
        {"op": "delete", "id": "p6"},
        {"op": "insert", "id": "p8", "point": ["-3", "8"]},
    ]
    ckpts_4a = {
        6: [(["p1", "p2", "p3", "p4"], True)],
        8: [(["p1", "p2", "p3", "p4"], True)],
        10: [(["p1", "p2", "p3", "p4"], True)],
    }
    certs.append(_make_mode4_cert("m4_stream_2d_extreme_deletions", 2, Fraction(1, 5), 128, 16384, 16000, 8500, ops_4a, ckpts_4a))

    # 4b: 3D multi-ball hierarchy + sample invalidation test (ball 0 invalidated after deleting sample point, ball 1 + leaf recover witness!)
    ops_4b = [
        {"op": "insert", "id": "a1", "point": ["0", "0", "0"]},
        {"op": "insert", "id": "a2", "point": ["2", "0", "0"]},
        {"op": "insert", "id": "a3", "point": ["1", "2", "0"]},
        {"op": "insert", "id": "b1", "point": ["10", "0", "0"]},
        {"op": "insert", "id": "b2", "point": ["12", "2", "1"]},
        {"op": "insert", "id": "b3", "point": ["11", "-1", "2"]},
        {"op": "insert", "id": "c1", "point": ["-8", "5", "-4"]},
        {"op": "delete", "id": "a2"},  # invalidates ball 0's sample!
        {"op": "insert", "id": "c2", "point": ["15", "-4", "3"]},
    ]
    ckpts_4b = {
        7: [(["a1", "a2", "a3"], True), (["b1", "b2", "b3"], True)],
        9: [(["a1", "a3"], False), (["b1", "b2", "b3"], True)],
    }
    certs.append(_make_mode4_cert("m4_stream_3d_multiball_invalidation", 3, Fraction(1, 4), 256, 32768, 32400, 16700, ops_4b, ckpts_4b))

    # 4c: 4D high-precision eta = 1/6 dynamic stream with re-insertion of previously deleted ID
    ops_4c = [
        {"op": "insert", "id": "v1", "point": ["1", "1", "1", "1"]},
        {"op": "insert", "id": "v2", "point": ["3", "1", "1", "1"]},
        {"op": "insert", "id": "v3", "point": ["2", "3", "1", "1"]},
        {"op": "insert", "id": "v4", "point": ["2", "2", "3", "1"]},
        {"op": "insert", "id": "v5", "point": ["-6", "4", "-3", "5"]},
        {"op": "insert", "id": "v6", "point": ["8", "-5", "4", "-2"]},
        {"op": "delete", "id": "v6"},
        {"op": "insert", "id": "v6", "point": ["5", "6", "-4", "3"]},
    ]
    ckpts_4c = {
        6: [(["v1", "v2", "v3", "v4"], True)],
        8: [(["v1", "v2", "v3", "v4"], True)],
    }
    certs.append(_make_mode4_cert("m4_stream_4d_reinsert_eta1_6", 4, Fraction(1, 6), 192, 24576, 24200, 12600, ops_4c, ckpts_4c))

    # 4d: 3D exact-leaf collapse after mass deletions (leaves only 3 points in exact leaf)
    ops_4d = [
        {"op": "insert", "id": "q1", "point": ["0", "0", "0"]},
        {"op": "insert", "id": "q2", "point": ["6", "0", "0"]},
        {"op": "insert", "id": "q3", "point": ["3", "6", "0"]},
        {"op": "insert", "id": "q4", "point": ["3", "3", "6"]},
        {"op": "insert", "id": "q5", "point": ["-5", "-5", "2"]},
        {"op": "delete", "id": "q2"},
        {"op": "delete", "id": "q3"},
    ]
    ckpts_4d = {
        5: [(["q1", "q2", "q3", "q4"], True)],
        7: [],  # exact leaf only
    }
    certs.append(_make_mode4_cert("m4_stream_3d_exact_leaf_collapse", 3, Fraction(1, 5), 512, 65536, 65200, 33100, ops_4d, ckpts_4d))

    return certs


def run_experiments() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)

    certs = build_all_certificates()
    replay_rows: List[Dict[str, Any]] = []
    for cert in certs:
        out_path = CERT_DIR / f"{cert['cert_id']}.json"
        out_path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        # Measure exact zero-float replay latency (median of 5 runs after 1 warmup)
        verify_diameter_certificate_exact(cert)
        times_ms: List[float] = []
        res: Dict[str, Any] = {}
        for _ in range(5):
            t0 = time.perf_counter()
            res = verify_diameter_certificate_exact(cert)
            times_ms.append((time.perf_counter() - t0) * 1000.0)
        times_ms.sort()
        replay_rows.append(
            {
                "cert_id": cert["cert_id"],
                "mode": cert["mode"],
                "verify_ms": round(times_ms[2], 3),
                "summary": res,
            }
        )

    (DATA_DIR / "certificate_replay_summary.json").write_text(
        json.dumps({"count": len(replay_rows), "certificates": replay_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # Exp 1: Algorithm 4 Exact Rational Convergence & Bit-Length Sweep across eta
    # =========================================================================
    sample_exp1: List[PointQ] = [
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(10), Fraction(0), Fraction(0)),
        (Fraction(5), Fraction(8), Fraction(0)),
        (Fraction(5), Fraction(4), Fraction(7)),
        (Fraction(2), Fraction(-6), Fraction(3)),
        (Fraction(8), Fraction(5), Fraction(-4)),
        (Fraction(1), Fraction(7), Fraction(-3)),
        (Fraction(9), Fraction(-4), Fraction(5)),
    ]
    exp1_rows = []
    for den in [4, 5, 6, 8, 10, 12, 16]:
        eta = Fraction(1, den)
        res = run_algorithm4_exact(sample_exp1, eta, start_idx=0)
        max_w_bits = max(w.denominator.bit_length() for w in res["weights"])
        v_ratio = res["variance"] / res["V0"]
        exp1_rows.append(
            {
                "eta": format_rat(eta),
                "eta_dec": float(eta),
                "iterations": res["iterations"],
                "support_size": len(res["support_indices"]),
                "V_over_V0_exact": format_rat(v_ratio),
                "V_over_V0_dec": round(float(v_ratio), 6),
                "max_weight_den_bits": max_w_bits,
                "var_den_bits": res["variance"].denominator.bit_length(),
            }
        )
    (DATA_DIR / "exp1_alg4_convergence_sweep.json").write_text(
        json.dumps({"sample_size": len(sample_exp1), "dim": 3, "rows": exp1_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # Exp 2: Lemma 5.1 Hull Factor sqrt(2a^2 - 1) vs Two-Tetrahedra Rational Realization
    # =========================================================================
    tet_signs = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
    s_tet: List[PointQ] = [
        (Fraction(-2), Fraction(2 * a_), Fraction(2 * b_), Fraction(2 * c_), Fraction(0), Fraction(0), Fraction(0))
        for a_, b_, c_ in tet_signs
    ] + [
        (Fraction(2), Fraction(0), Fraction(0), Fraction(0), Fraction(2 * a_), Fraction(2 * b_), Fraction(2 * c_))
        for a_, b_, c_ in tet_signs
    ]
    ls_sq_tet, _ = exact_diameter_sq_q(s_tet)  # 40
    # V = 12, h = 4
    exp2_rows = []
    for a_num in [142, 145, 150, 155, 1581, 165, 175, 190, 200]:
        a_den = 1000 if a_num == 1581 else 100
        a = Fraction(a_num, a_den)
        hull_sq = Fraction(2, 1) * a * a - Fraction(1, 1)
        # Optimal theoretical bound at this a is sqrt(2a^2 - 1); two-tetrahedra with h=4, V=12 gives
        # max hull separation (4 + 2*sqrt((a^2-1)*12)) / sqrt(40)
        rad_sq = (a * a - Fraction(1, 1)) * Fraction(12, 1)
        # Largest rational t = k/100 with t^2 <= rad_sq
        k_max = 0
        while Fraction(k_max + 1, 100) ** 2 <= rad_sq:
            k_max += 1
        t_rat = Fraction(k_max, 100)
        attained_sq_ratio = (Fraction(4, 1) + Fraction(2, 1) * t_rat) ** 2 / ls_sq_tet
        exp2_rows.append(
            {
                "a": format_rat(a),
                "a_dec": float(a),
                "hull_sq_exact": format_rat(hull_sq),
                "hull_factor_dec": round(float(hull_sq) ** 0.5, 6),
                "attained_sq_ratio_exact": format_rat(attained_sq_ratio),
                "attained_factor_dec": round(float(attained_sq_ratio) ** 0.5, 6),
            }
        )
    (DATA_DIR / "exp2_hull_tightness_curve.json").write_text(
        json.dumps({"LS_sq": format_rat(ls_sq_tet), "rows": exp2_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # Exp 3: Appendix A.1 Two-Cap Potential Profile F(t) & Second-Mask Taylor Margin
    # =========================================================================
    lam = Fraction(79, 50)
    m_val = lam * lam / Fraction(2, 1) - Fraction(1, 1)  # 1241/5000
    f_profile = []
    for k in range(-9, 10):
        t = Fraction(k, 10)
        one_minus_t2 = Fraction(1, 1) - t * t
        x_exp = (lam - t) ** 2 / one_minus_t2 - Fraction(1, 1)
        f_lb = one_minus_t2 * taylor_exp_lb_q(x_exp, 10) if x_exp >= 0 else None
        f_profile.append(
            {
                "t": format_rat(t),
                "t_dec": float(t),
                "x_exp_dec": round(float(x_exp), 6),
                "F_lb_dec": round(float(f_lb), 6) if f_lb is not None else None,
            }
        )
    taylor_rows = []
    thr_second = Fraction(21, 20) * Fraction(16, 25)  # 84/125
    for deg in range(1, 11):
        e_lb = taylor_exp_lb_q(Fraction(1, 1), deg)
        prod = e_lb * m_val
        margin = prod - thr_second
        taylor_rows.append(
            {
                "deg": deg,
                "e_lb_exact": format_rat(e_lb),
                "em_exact": format_rat(prod),
                "em_dec": round(float(prod), 7),
                "margin_exact": format_rat(margin),
                "margin_dec": round(float(margin), 7),
                "passes": prod > thr_second,
            }
        )
    (DATA_DIR / "exp3_two_cap_potential_and_taylor.json").write_text(
        json.dumps(
            {
                "lambda": format_rat(lam),
                "m_exact": format_rat(m_val),
                "first_mask_thr": "21/20",
                "second_mask_thr": format_rat(thr_second),
                "F_profile": f_profile,
                "second_mask_taylor": taylor_rows,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # Exp 4: Dynamic-Stream Tradeoff Landscape & Table 3 Factor-Two Margins
    # =========================================================================
    exp4 = {
        "factor_two_table3": {
            "hull_sq": "3999122/1000000",
            "hull_sq_dec": 3.999122,
            "mixed_sq": "39898284241/10000000000",
            "mixed_sq_dec": 3.9898284241,
            "cand_sq": "20201/10000",
            "cand_sq_dec": 2.0201,
            "target_c_sq": "4",
            "eps_exact_lb": "1/6345504000",
            "eps_dec": 1.0 / 6345504000.0,
        },
        "approx_thresholds": [
            {"label": "Insertion-only lower bound (AS15)", "val": 2.0 ** 0.5, "exact": "sqrt(2)"},
            {"label": "Hull barrier (Giliberti-Hajiaghayi Thm. 1.1)", "val": 3.0 ** 0.5, "exact": "sqrt(3)"},
            {"label": "Appendix A.1 hull factor (a=1581/1000)", "val": 3.999122 ** 0.5, "exact": "sqrt(3.999122)"},
            {"label": "Factor-two target guarantee (Table 1)", "val": 2.0, "exact": "2"},
        ],
    }
    (DATA_DIR / "exp4_factor_two_landscape.json").write_text(
        json.dumps(exp4, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Generated {len(certs)} canonical certificates and 4 experiment JSONs successfully.")
    for r in replay_rows:
        print(f"  {r['cert_id']:38s}  {r['verify_ms']:6.3f} ms  ({r['mode']})")


if __name__ == "__main__":
    run_experiments()
