"""Zero-floating-point exact-Q certificate verifier: EUCLIDEAN-DIAM-CERT-1.0.
Audits all four algorithmic and analytic pillars of
Jeff Giliberti & MohammadTaghi Hajiaghayi (arXiv:2611.33139, Nov 24, 2026)
"On Euclidean Diameter in Dynamic Streams":
  - Mode 1: variance_certificate_alg4 (Section 8.1.2 Algorithm 4 exact replay & parallel-axis audit)
  - Mode 2: variance_hull_and_tightness (Section 5.1 Lemma 5.1 hull diameter, tightness & Eq. 13 witness radius)
  - Mode 3: factor_two_two_cap_audit (Appendix A.1 Table 3, 3-4-5 two-cap masks, oracle & exponent suite)
  - Mode 4: dynamic_stream_chain_replay (Section 8.1.1 / 8.1.3 dynamic insert/delete chain & 3K shrinkage)

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import re
from fractions import Fraction
from typing import Any, Dict, List, Set, Tuple

from src.diameter_exact import (
    PointQ,
    exact_diameter_sq_q,
    format_rat,
    mean_and_variance_q,
    run_algorithm4_exact,
    sq_dist_q,
    taylor_exp_lb_q,
)

SCHEMA_VERSION = "EUCLIDEAN-DIAM-CERT-1.0"
_CANON_INT_RE = re.compile(r"^(0|-?[1-9][0-9]*)$")
_CANON_FRAC_RE = re.compile(r"^-?[1-9][0-9]*/[1-9][0-9]*$")
MAX_RAT_STR_LEN = 1200
MAX_INT_BITS = 2048


class DiameterCertificateError(ValueError):
    """Raised whenever a certificate fails any schema, type, or mathematical invariant."""


def _assert_strict_json_types(obj: Any, path: str = "$") -> None:
    t = type(obj)
    if t is bool:
        return  # allowed only where explicitly checked; rejected by _parse_int/_parse_rat
    if t is int:
        if obj.bit_length() > MAX_INT_BITS:
            raise DiameterCertificateError(f"Integer bit-length > {MAX_INT_BITS} at {path}")
        return
    if t is str:
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]")
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise DiameterCertificateError(f"Non-string dict key at {path}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    raise DiameterCertificateError(f"Forbidden JSON type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise DiameterCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    if val.bit_length() > MAX_INT_BITS:
        raise DiameterCertificateError(f"{name} exceeds max int bit length")
    return val


def _parse_bool(val: Any, name: str) -> bool:
    if type(val) is not bool:
        raise DiameterCertificateError(f"{name} must be strict bool, got {type(val).__name__}")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if type(val) is int:
        if val.bit_length() > MAX_INT_BITS:
            raise DiameterCertificateError(f"{name} integer too large")
        return Fraction(val, 1)
    if type(val) is str:
        if len(val) > MAX_RAT_STR_LEN:
            raise DiameterCertificateError(f"{name} rational string too long")
        if _CANON_INT_RE.match(val):
            iv = int(val)
            if iv.bit_length() > MAX_INT_BITS:
                raise DiameterCertificateError(f"{name} integer bit-length exceeds {MAX_INT_BITS}")
            return Fraction(iv, 1)
        if _CANON_FRAC_RE.match(val):
            num_s, den_s = val.split("/")
            num, den = int(num_s), int(den_s)
            if num.bit_length() > MAX_INT_BITS or den.bit_length() > MAX_INT_BITS:
                raise DiameterCertificateError(f"{name} rational bit-length exceeds {MAX_INT_BITS}")
            if den < 2:
                raise DiameterCertificateError(f"{name} denominator must be >= 2: {val!r}")
            q = Fraction(num, den)
            if q.numerator != num or q.denominator != den:
                raise DiameterCertificateError(f"{name} unreduced fraction: {val!r}")
            return q
        raise DiameterCertificateError(f"{name} non-canonical rational string: {val!r}")
    raise DiameterCertificateError(f"{name} invalid type {type(val).__name__}")


def _parse_point(raw: Any, dim: int, name: str) -> PointQ:
    if type(raw) is not list or len(raw) != dim:
        raise DiameterCertificateError(f"{name} must be list of length {dim}")
    return tuple(_parse_rat(raw[j], f"{name}[{j}]") for j in range(dim))


def _parse_points(raw: Any, dim: int, name: str, min_len: int = 1, max_len: int = 64) -> List[PointQ]:
    if type(raw) is not list or not (min_len <= len(raw) <= max_len):
        raise DiameterCertificateError(f"{name} must be list of length in [{min_len}, {max_len}]")
    return [_parse_point(raw[i], dim, f"{name}[{i}]") for i in range(len(raw))]


def _parse_exact_keys(cert: Dict[str, Any], required: Set[str], mode: str) -> None:
    keys = set(cert.keys())
    if keys != required:
        raise DiameterCertificateError(f"{mode} key mismatch: {sorted(keys ^ required)}")


# =============================================================================
# Mode 1: Section 8.1.2 Algorithm 4 Exact Rational Variance Certificate
# =============================================================================


def _verify_mode1_alg4(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "dimension",
        "sample_points",
        "eta",
        "start_idx",
        "test_query_y",
        "claimed_b_idx",
        "claimed_iterations",
        "claimed_support_indices",
        "claimed_weights",
        "claimed_mean",
        "claimed_variance",
        "claimed_max_r2",
        "claimed_candidate_H2",
    }
    _parse_exact_keys(cert, req, "Mode 1")
    dim = _parse_int(cert["dimension"], "dimension")
    if not (1 <= dim <= 16):
        raise DiameterCertificateError("Require 1 <= dimension <= 16")
    sample = _parse_points(cert["sample_points"], dim, "sample_points", min_len=2, max_len=64)
    eta = _parse_rat(cert["eta"], "eta")
    if not (Fraction(0, 1) < eta <= Fraction(1, 4)):
        raise DiameterCertificateError("Require 0 < eta <= 1/4")
    start_idx = _parse_int(cert["start_idx"], "start_idx")
    if not (0 <= start_idx < len(sample)):
        raise DiameterCertificateError("start_idx out of range")
    y = _parse_point(cert["test_query_y"], dim, "test_query_y")

    res = run_algorithm4_exact(sample, eta, start_idx=start_idx)

    if _parse_int(cert["claimed_b_idx"], "claimed_b_idx") != res["b_idx"]:
        raise DiameterCertificateError(f"claimed_b_idx mismatch: exact={res['b_idx']}")
    if _parse_int(cert["claimed_iterations"], "claimed_iterations") != res["iterations"]:
        raise DiameterCertificateError(f"claimed_iterations mismatch: exact={res['iterations']}")

    raw_supp = cert["claimed_support_indices"]
    if type(raw_supp) is not list:
        raise DiameterCertificateError("claimed_support_indices must be list")
    claimed_supp = [_parse_int(v, f"claimed_support_indices[{i}]") for i, v in enumerate(raw_supp)]
    if claimed_supp != res["support_indices"]:
        raise DiameterCertificateError("claimed_support_indices mismatch")

    raw_w = cert["claimed_weights"]
    if type(raw_w) is not list or len(raw_w) != len(claimed_supp):
        raise DiameterCertificateError("claimed_weights length mismatch")
    claimed_w = [_parse_rat(v, f"claimed_weights[{i}]") for i, v in enumerate(raw_w)]
    if claimed_w != res["weights"]:
        raise DiameterCertificateError("claimed_weights mismatch")

    claimed_mean = _parse_point(cert["claimed_mean"], dim, "claimed_mean")
    if claimed_mean != res["mean"]:
        raise DiameterCertificateError("claimed_mean mismatch")
    claimed_var = _parse_rat(cert["claimed_variance"], "claimed_variance")
    if claimed_var != res["variance"]:
        raise DiameterCertificateError("claimed_variance mismatch")
    claimed_max_r2 = _parse_rat(cert["claimed_max_r2"], "claimed_max_r2")
    if claimed_max_r2 != res["max_r2"]:
        raise DiameterCertificateError("claimed_max_r2 mismatch")

    # Verify full containment S subset B(c, (1 + eta)*sqrt(V))
    one_plus_eta_sq = (Fraction(1, 1) + eta) ** 2
    if claimed_max_r2 > one_plus_eta_sq * claimed_var:
        raise DiameterCertificateError("Sample containment inequality violated")

    # Verify exact parallel-axis identity and candidate anchor score H^2 >= V + ||c - y||^2
    supp_pts = [sample[i] for i in claimed_supp]
    weighted_sq_to_y = Fraction(0, 1)
    max_anchor_sq = Fraction(0, 1)
    for pt, w in zip(supp_pts, claimed_w):
        d2 = sq_dist_q(pt, y)
        weighted_sq_to_y += w * d2
        if d2 > max_anchor_sq:
            max_anchor_sq = d2
    c_to_y_sq = sq_dist_q(claimed_mean, y)
    if weighted_sq_to_y != claimed_var + c_to_y_sq:
        raise DiameterCertificateError("Parallel-axis identity violated")
    if max_anchor_sq < claimed_var + c_to_y_sq:
        raise DiameterCertificateError("Anchor max score fell below V + ||c - y||^2")
    if _parse_rat(cert["claimed_candidate_H2"], "claimed_candidate_H2") != max_anchor_sq:
        raise DiameterCertificateError(f"claimed_candidate_H2 mismatch: exact={max_anchor_sq}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "iterations": res["iterations"],
        "support_size": len(claimed_supp),
        "variance": format_rat(claimed_var),
        "max_r2": format_rat(claimed_max_r2),
        "H2": format_rat(max_anchor_sq),
    }


# =============================================================================
# Mode 2: Section 5.1 Lemma 5.1 Variance-Hull Diameter, Tightness & Witness Radius
# =============================================================================


def _verify_mode2_hull(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "dimension",
        "sample_points",
        "hull_a",
        "dist_lambda",
        "dist_gamma",
        "hull_point_y1",
        "hull_point_y2",
        "exterior_point_y",
        "witness_center_q",
        "coord_bound_Delta",
        "claimed_LS_sq",
        "claimed_V_lambda",
        "claimed_V_gamma",
        "claimed_h_sq",
        "claimed_y1_y2_sq",
        "claimed_RS_q_sq",
    }
    _parse_exact_keys(cert, req, "Mode 2")
    dim = _parse_int(cert["dimension"], "dimension")
    if not (1 <= dim <= 16):
        raise DiameterCertificateError("Require 1 <= dimension <= 16")
    sample = _parse_points(cert["sample_points"], dim, "sample_points", min_len=2, max_len=64)
    n = len(sample)
    a = _parse_rat(cert["hull_a"], "hull_a")
    if a <= Fraction(1, 1):
        raise DiameterCertificateError("Require hull_a > 1")
    a2 = a * a
    a2_minus_1 = a2 - Fraction(1, 1)

    if type(cert["dist_lambda"]) is not list or len(cert["dist_lambda"]) != n:
        raise DiameterCertificateError("dist_lambda length mismatch")
    if type(cert["dist_gamma"]) is not list or len(cert["dist_gamma"]) != n:
        raise DiameterCertificateError("dist_gamma length mismatch")
    lam = [_parse_rat(v, f"dist_lambda[{i}]") for i, v in enumerate(cert["dist_lambda"])]
    gam = [_parse_rat(v, f"dist_gamma[{i}]") for i, v in enumerate(cert["dist_gamma"])]

    try:
        mu_l, v_l = mean_and_variance_q(sample, lam)
        mu_g, v_g = mean_and_variance_q(sample, gam)
    except ValueError as exc:
        raise DiameterCertificateError(str(exc)) from exc

    ls_sq, _ = exact_diameter_sq_q(sample)
    if ls_sq <= 0:
        raise DiameterCertificateError("Degenerate sample with zero diameter")

    y1 = _parse_point(cert["hull_point_y1"], dim, "hull_point_y1")
    y2 = _parse_point(cert["hull_point_y2"], dim, "hull_point_y2")

    # Verify y1, y2 in H_a(S) via Lemma 5.1 variance representation
    if sq_dist_q(y1, mu_l) > a2_minus_1 * v_l:
        raise DiameterCertificateError("hull_point_y1 fails Lemma 5.1 variance ball condition")
    if sq_dist_q(y2, mu_g) > a2_minus_1 * v_g:
        raise DiameterCertificateError("hull_point_y2 fails Lemma 5.1 variance ball condition")

    # Verify independent-draw identity h^2 + V_lambda + V_gamma = E||s - t||^2 <= L_S^2
    h_sq = sq_dist_q(mu_l, mu_g)
    cross_exp = Fraction(0, 1)
    for i in range(n):
        if lam[i] == 0:
            continue
        for j in range(n):
            if gam[j] == 0:
                continue
            cross_exp += lam[i] * gam[j] * sq_dist_q(sample[i], sample[j])
    if cross_exp != h_sq + v_l + v_g:
        raise DiameterCertificateError("Two-draw variance identity failed")
    if h_sq + v_l + v_g > ls_sq:
        raise DiameterCertificateError("h^2 + V + W exceeded L_S^2")

    # Verify Eq. (12) hull diameter bound ||y1 - y2||^2 <= (2a^2 - 1) L_S^2
    y1_y2_sq = sq_dist_q(y1, y2)
    hull_bound_sq = (Fraction(2, 1) * a2 - Fraction(1, 1)) * ls_sq
    if y1_y2_sq > hull_bound_sq:
        raise DiameterCertificateError("Hull pair exceeded (2a^2 - 1) L_S^2")

    # Verify exterior point & Eq. (13) bounded witness ball radius: ||y - q|| > a R_S(q) and R_S(q) < D_univ/(a-1)
    y_ext = _parse_point(cert["exterior_point_y"], dim, "exterior_point_y")
    q_cen = _parse_point(cert["witness_center_q"], dim, "witness_center_q")
    delta = _parse_rat(cert["coord_bound_Delta"], "coord_bound_Delta")
    if delta <= 0:
        raise DiameterCertificateError("Require coord_bound_Delta > 0")
    for pt in list(sample) + [y_ext]:
        for c in pt:
            if abs(c) > delta:
                raise DiameterCertificateError("Sample or exterior point exceeds coordinate bound Delta")
    rs_q_sq = max(sq_dist_q(s, q_cen) for s in sample)
    ext_dist_sq = sq_dist_q(y_ext, q_cen)
    if ext_dist_sq <= a2 * rs_q_sq:
        raise DiameterCertificateError("exterior_point_y is NOT strictly outside B(q, a R_S(q))")
    d_univ_sq = Fraction(4 * dim, 1) * delta * delta
    if (a - Fraction(1, 1)) ** 2 * rs_q_sq >= d_univ_sq:
        raise DiameterCertificateError("Witness ball radius violated Eq. (13) bound D_univ / (a - 1)")

    # Check all claimed fields verbatim
    if _parse_rat(cert["claimed_LS_sq"], "claimed_LS_sq") != ls_sq:
        raise DiameterCertificateError(f"claimed_LS_sq mismatch: exact={ls_sq}")
    if _parse_rat(cert["claimed_V_lambda"], "claimed_V_lambda") != v_l:
        raise DiameterCertificateError(f"claimed_V_lambda mismatch: exact={v_l}")
    if _parse_rat(cert["claimed_V_gamma"], "claimed_V_gamma") != v_g:
        raise DiameterCertificateError(f"claimed_V_gamma mismatch: exact={v_g}")
    if _parse_rat(cert["claimed_h_sq"], "claimed_h_sq") != h_sq:
        raise DiameterCertificateError(f"claimed_h_sq mismatch: exact={h_sq}")
    if _parse_rat(cert["claimed_y1_y2_sq"], "claimed_y1_y2_sq") != y1_y2_sq:
        raise DiameterCertificateError(f"claimed_y1_y2_sq mismatch: exact={y1_y2_sq}")
    if _parse_rat(cert["claimed_RS_q_sq"], "claimed_RS_q_sq") != rs_q_sq:
        raise DiameterCertificateError(f"claimed_RS_q_sq mismatch: exact={rs_q_sq}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "LS_sq": format_rat(ls_sq),
        "y1_y2_sq": format_rat(y1_y2_sq),
        "hull_bound_sq": format_rat(hull_bound_sq),
        "RS_q_sq": format_rat(rs_q_sq),
    }


# =============================================================================
# Mode 3: Appendix A.1 Factor-Two Two-Cap Mask, Oracle & Space-Exponent Audit
# =============================================================================


def _verify_mode3_factor_two(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "target_c",
        "a",
        "q_scale",
        "lambda_0",
        "lambda_val",
        "eta_mask",
        "r2",
        "cap_split_t0",
        "cap_test_points",
        "eta_in",
        "kappa",
        "b0",
        "nu",
        "e0",
        "B_kappa",
        "s",
        "G",
        "taylor_deg_half",
        "taylor_deg_e",
        "target_eps",
        "claimed_hull_sq",
        "claimed_mixed_sq",
        "claimed_cand_sq",
        "claimed_m_second_mask",
        "claimed_second_mask_lb",
        "claimed_oracle_lhs",
        "claimed_eps_lb",
    }
    _parse_exact_keys(cert, req, "Mode 3")

    c = _parse_rat(cert["target_c"], "target_c")
    a = _parse_rat(cert["a"], "a")
    q_scale = _parse_rat(cert["q_scale"], "q_scale")
    lam0 = _parse_rat(cert["lambda_0"], "lambda_0")
    lam = _parse_rat(cert["lambda_val"], "lambda_val")
    eta_mask = _parse_rat(cert["eta_mask"], "eta_mask")
    r2 = _parse_rat(cert["r2"], "r2")
    t0 = _parse_rat(cert["cap_split_t0"], "cap_split_t0")
    eta_in = _parse_rat(cert["eta_in"], "eta_in")
    kappa = _parse_rat(cert["kappa"], "kappa")
    b0 = _parse_rat(cert["b0"], "b0")
    nu = _parse_rat(cert["nu"], "nu")
    e0 = _parse_rat(cert["e0"], "e0")
    b_kappa = _parse_int(cert["B_kappa"], "B_kappa")
    s = _parse_rat(cert["s"], "s")
    g_ratio = _parse_int(cert["G"], "G")
    deg_half = _parse_int(cert["taylor_deg_half"], "taylor_deg_half")
    deg_e = _parse_int(cert["taylor_deg_e"], "taylor_deg_e")
    target_eps = _parse_rat(cert["target_eps"], "target_eps")

    if not (1 <= deg_half <= 20 and 1 <= deg_e <= 20):
        raise DiameterCertificateError("Taylor degrees must be in [1, 20]")
    if c <= 1 or a <= 1 or q_scale <= 1 or eta_mask <= 0 or not (0 < r2 < 1) or not (0 < t0 < 1):
        raise DiameterCertificateError("Invalid geometric parameter domain")
    if eta_in <= 0 or kappa <= 1 or b0 <= 1 or nu <= 0 or e0 <= 0 or b_kappa < 1 or s <= 0 or g_ratio < 1 or target_eps <= 0:
        raise DiameterCertificateError("Invalid oracle/exponent parameter domain")

    # 1. Scale chain: a / q_scale > lambda_0 > lambda > sqrt(2)
    if not (a > q_scale * lam0 and lam0 > lam and lam * lam > Fraction(2, 1)):
        raise DiameterCertificateError("Scale chain a/q_scale > lambda_0 > lambda > sqrt(2) violated")

    # 2. Table 3 three-case squared approximation bounds
    hull_sq = Fraction(2, 1) * a * a - Fraction(1, 1)
    mixed_sq = (Fraction(1, 1) + eta_in) ** 2 + a * a * kappa * kappa
    cand_sq = (Fraction(1, 1) + eta_in) ** 2 + Fraction(1, 1)
    if not (hull_sq < c * c and mixed_sq < hull_sq and cand_sq < hull_sq):
        raise DiameterCertificateError("Table 3 three-case strict ordering violated")

    # 3. First mask at t0: g(t0) < 0, F_lb(t0) > 1 + eta_mask, and spherical cap t >= t0 -> B(t0 u, r2)
    g_t0 = t0 * lam * lam - lam * t0 * t0 + t0 * t0 * t0 - lam
    if not (g_t0 < 0):
        raise DiameterCertificateError(f"First-mask derivative numerator g(t0)={g_t0} not < 0")
    x1 = (lam - t0) ** 2 / (Fraction(1, 1) - t0 * t0) - Fraction(1, 1)
    if not (x1 > 0):
        raise DiameterCertificateError("First-mask exponent x1 must be > 0")
    f_t0_lb = (Fraction(1, 1) - t0 * t0) * taylor_exp_lb_q(x1, deg_half)
    if not (f_t0_lb > Fraction(1, 1) + eta_mask):
        raise DiameterCertificateError(f"First-mask endpoint bound {f_t0_lb} <= 1 + eta_mask")

    # Verify spherical cap containment t0^2 + r2^2 == 1 (exact cap geometry) & test points
    if (Fraction(1, 1) - t0) ** 2 > r2 * r2 or (Fraction(1, 1) - t0 * t0) > r2 * r2:
        raise DiameterCertificateError("Cap radius r2 does not contain spherical cap t >= t0")
    raw_caps = cert["cap_test_points"]
    if type(raw_caps) is not list or not (1 <= len(raw_caps) <= 32):
        raise DiameterCertificateError("cap_test_points must be non-empty list of <= 32 (t, q) pairs")
    for idx, pair in enumerate(raw_caps):
        if type(pair) is not list or len(pair) != 2:
            raise DiameterCertificateError(f"cap_test_points[{idx}] must be [t, q]")
        tj = _parse_rat(pair[0], f"cap_test_points[{idx}][0]")
        qj = _parse_rat(pair[1], f"cap_test_points[{idx}][1]")
        if qj < 0 or tj * tj + qj > Fraction(1, 1) or tj < t0:
            raise DiameterCertificateError(f"cap_test_points[{idx}] outside cap t>=t0, t^2+q<=1")
        if (tj - t0) ** 2 + qj > r2 * r2:
            raise DiameterCertificateError(f"cap_test_points[{idx}] failed cap containment B(t0 u, r2)")

    # 4. Second mask empty: m = lam^2/2 - 1, e_lb * m > (1 + eta_mask) * r2^2
    m_val = lam * lam / Fraction(2, 1) - Fraction(1, 1)
    if not (m_val > 0):
        raise DiameterCertificateError("m = lam^2/2 - 1 must be > 0")
    e_lb = taylor_exp_lb_q(Fraction(1, 1), deg_e)
    second_mask_lb = e_lb * m_val
    second_mask_thr = (Fraction(1, 1) + eta_mask) * r2 * r2
    if not (second_mask_lb > second_mask_thr):
        raise DiameterCertificateError(f"Second-mask bound {second_mask_lb} <= threshold {second_mask_thr}")

    # 5. Oracle accuracy & Chernoff rate
    oracle_lhs = kappa * (Fraction(1, 1) - nu - Fraction(2, 1) * e0)
    if not (oracle_lhs > b0 + nu):
        raise DiameterCertificateError(f"Oracle accuracy margin failed: {oracle_lhs} <= {b0 + nu}")
    x_chern = b0 * b0 - Fraction(1, 1)
    chern_lb = (x_chern * x_chern) / (Fraction(4, 1) * (Fraction(1, 1) + x_chern))
    if not (chern_lb > Fraction(1, 170)):
        raise DiameterCertificateError(f"Chernoff rate lower bound {chern_lb} <= 1/170")

    # 6. Section A.1.6 space-exponent & oracle work per update checks
    rho = s / Fraction(2, 1)
    theta_exp = rho / Fraction(12 * (g_ratio + 1), 1)
    # Using tau = -ln(1 - 1/B_kappa) > 1/B_kappa -> eps_0 = tau * theta / 2 > theta / (2 * B_kappa)
    eps_lb = theta_exp / Fraction(2 * b_kappa, 1)
    if not (eps_lb > target_eps):
        raise DiameterCertificateError(f"Recovery saving {eps_lb} <= target_eps {target_eps}")
    if not (s * Fraction(b_kappa + 1, 1) - Fraction(1, 1) < 0):
        raise DiameterCertificateError("Oracle work per update s*(B_kappa + 1) - 1 not < 0")
    if not (s * Fraction(b_kappa, 1) < Fraction(1, 1) - target_eps):
        raise DiameterCertificateError("s*B_kappa not < 1 - target_eps")
    if not (Fraction(1, 1) - s + rho < Fraction(1, 1) - target_eps):
        raise DiameterCertificateError("1 - s + rho not < 1 - target_eps")

    # Claimed value parity checks
    if _parse_rat(cert["claimed_hull_sq"], "claimed_hull_sq") != hull_sq:
        raise DiameterCertificateError(f"claimed_hull_sq mismatch: exact={hull_sq}")
    if _parse_rat(cert["claimed_mixed_sq"], "claimed_mixed_sq") != mixed_sq:
        raise DiameterCertificateError(f"claimed_mixed_sq mismatch: exact={mixed_sq}")
    if _parse_rat(cert["claimed_cand_sq"], "claimed_cand_sq") != cand_sq:
        raise DiameterCertificateError(f"claimed_cand_sq mismatch: exact={cand_sq}")
    if _parse_rat(cert["claimed_m_second_mask"], "claimed_m_second_mask") != m_val:
        raise DiameterCertificateError(f"claimed_m_second_mask mismatch: exact={m_val}")
    if _parse_rat(cert["claimed_second_mask_lb"], "claimed_second_mask_lb") != second_mask_lb:
        raise DiameterCertificateError(f"claimed_second_mask_lb mismatch: exact={second_mask_lb}")
    if _parse_rat(cert["claimed_oracle_lhs"], "claimed_oracle_lhs") != oracle_lhs:
        raise DiameterCertificateError(f"claimed_oracle_lhs mismatch: exact={oracle_lhs}")
    if _parse_rat(cert["claimed_eps_lb"], "claimed_eps_lb") != eps_lb:
        raise DiameterCertificateError(f"claimed_eps_lb mismatch: exact={eps_lb}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "hull_sq": format_rat(hull_sq),
        "mixed_sq": format_rat(mixed_sq),
        "second_mask_lb": format_rat(second_mask_lb),
        "eps_lb": format_rat(eps_lb),
    }


# =============================================================================
# Mode 4: Section 8.1.1 & 8.1.3 Dynamic Stream Insert/Delete Chain & 3K Audit
# =============================================================================


def _verify_mode4_stream_chain(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "dimension",
        "eta",
        "B_sched",
        "snapshot_m",
        "child_size_Pi1",
        "parent_size_Pi",
        "stream_ops",
        "checkpoints",
        "claimed_final_size",
        "claimed_final_diam_sq",
        "claimed_final_witness_sq",
    }
    _parse_exact_keys(cert, req, "Mode 4")
    dim = _parse_int(cert["dimension"], "dimension")
    if not (1 <= dim <= 16):
        raise DiameterCertificateError("Require 1 <= dimension <= 16")
    eta = _parse_rat(cert["eta"], "eta")
    if not (Fraction(0, 1) < eta <= Fraction(1, 4)):
        raise DiameterCertificateError("Require 0 < eta <= 1/4")
    one_plus_eta_sq = (Fraction(1, 1) + eta) ** 2
    cand_factor_sq = one_plus_eta_sq + Fraction(1, 1)

    # Verify Section 8.2 rebuild geometric shrinkage invariants
    b_sched = _parse_int(cert["B_sched"], "B_sched")
    snap_m = _parse_int(cert["snapshot_m"], "snapshot_m")
    pi_sz = _parse_int(cert["parent_size_Pi"], "parent_size_Pi")
    pi1_sz = _parse_int(cert["child_size_Pi1"], "child_size_Pi1")
    if b_sched < 128:
        raise DiameterCertificateError("Require B_sched >= 128 (Section 8.1.3)")
    if snap_m < 128 * b_sched:
        raise DiameterCertificateError("Require snapshot_m >= 128 * B_sched")
    max_del = 3 * (snap_m // b_sched)
    if pi_sz < snap_m - max_del:
        raise DiameterCertificateError("parent_size_Pi below m - 3*(m/B_sched)")
    if pi1_sz > snap_m // 2 + max_del:
        raise DiameterCertificateError("child_size_Pi1 above m/2 + 3*(m/B_sched)")
    if not (5 * pi1_sz < 3 * pi_sz):
        raise DiameterCertificateError("Geometric shrinkage |P_{i+1}| < 0.6 |P_i| violated")

    # Replay dynamic insert/delete stream
    raw_ops = cert["stream_ops"]
    if type(raw_ops) is not list or not (2 <= len(raw_ops) <= 128):
        raise DiameterCertificateError("stream_ops must have length in [2, 128]")

    raw_ckpts = cert["checkpoints"]
    if type(raw_ckpts) is not list or not (1 <= len(raw_ckpts) <= 32):
        raise DiameterCertificateError("checkpoints must have length in [1, 32]")
    ckpt_by_step: Dict[int, Dict[str, Any]] = {}
    for idx, ck in enumerate(raw_ckpts):
        if type(ck) is not dict:
            raise DiameterCertificateError(f"checkpoints[{idx}] must be dict")
        step = _parse_int(ck.get("after_op"), f"checkpoints[{idx}].after_op")
        if step in ckpt_by_step or not (1 <= step <= len(raw_ops)):
            raise DiameterCertificateError(f"Invalid or duplicate checkpoint after_op={step}")
        ckpt_by_step[step] = ck

    active: Dict[str, PointQ] = {}
    last_diam_sq = Fraction(0, 1)
    last_witness_sq = Fraction(0, 1)

    for step_idx, op in enumerate(raw_ops, start=1):
        if type(op) is not dict:
            raise DiameterCertificateError(f"stream_ops[{step_idx - 1}] must be dict")
        kind = op.get("op")
        key = op.get("id")
        if type(key) is not str or not key:
            raise DiameterCertificateError(f"stream_ops[{step_idx - 1}] invalid id")
        if kind == "insert":
            if set(op.keys()) != {"op", "id", "point"}:
                raise DiameterCertificateError(f"insert op keys mismatch at step {step_idx}")
            if key in active:
                raise DiameterCertificateError(f"Duplicate insert of active key {key!r} at step {step_idx}")
            active[key] = _parse_point(op["point"], dim, f"op[{step_idx}].point")
        elif kind == "delete":
            if set(op.keys()) != {"op", "id"}:
                raise DiameterCertificateError(f"delete op keys mismatch at step {step_idx}")
            if key not in active:
                raise DiameterCertificateError(f"Delete of absent key {key!r} at step {step_idx}")
            del active[key]
        else:
            raise DiameterCertificateError(f"Unknown stream op {kind!r} at step {step_idx}")

        if step_idx in ckpt_by_step:
            ck = ckpt_by_step[step_idx]
            ck_req = {
                "after_op",
                "balls",
                "leaf_ids",
                "witness_pair",
                "claimed_witness_sq",
                "claimed_exact_diam_sq",
            }
            _parse_exact_keys(ck, ck_req, f"checkpoint@{step_idx}")
            if len(active) < 2:
                raise DiameterCertificateError(f"Checkpoint at step {step_idx} requires >= 2 active points")

            # Route active points through chain of covering balls
            remaining: Set[str] = set(active.keys())
            raw_balls = ck["balls"]
            if type(raw_balls) is not list or len(raw_balls) > 16:
                raise DiameterCertificateError(f"Invalid balls list at step {step_idx}")
            best_valid_score_sq = Fraction(0, 1)
            valid_witness_edges: Set[Tuple[str, str]] = set()
            for b_i, ball in enumerate(raw_balls):
                if type(ball) is not dict:
                    raise DiameterCertificateError(f"ball[{b_i}] at step {step_idx} must be dict")
                b_req = {"anchor_ids", "weights", "center", "variance", "sample_intact"}
                _parse_exact_keys(ball, b_req, f"ball[{b_i}]@{step_idx}")
                sample_intact = _parse_bool(ball["sample_intact"], f"ball[{b_i}].sample_intact")
                a_ids = ball["anchor_ids"]
                w_raw = ball["weights"]
                if type(a_ids) is not list or not a_ids or type(w_raw) is not list or len(a_ids) != len(w_raw):
                    raise DiameterCertificateError(f"ball[{b_i}] anchors/weights mismatch")
                if len(set(a_ids)) != len(a_ids):
                    raise DiameterCertificateError(f"ball[{b_i}] duplicate anchor_ids")
                weights_b = [_parse_rat(w, f"ball[{b_i}].weights") for w in w_raw]
                if any(w < 0 for w in weights_b) or sum(weights_b, Fraction(0, 1)) != Fraction(1, 1):
                    raise DiameterCertificateError(f"ball[{b_i}] weights must be nonnegative and sum to 1")
                center_b = _parse_point(ball["center"], dim, f"ball[{b_i}].center")
                var_b = _parse_rat(ball["variance"], f"ball[{b_i}].variance")
                if var_b < 0:
                    raise DiameterCertificateError(f"ball[{b_i}] negative variance")

                # Only intact balls (verified cryptographically against current node input `remaining`)
                # may contribute witness scores AND route points out of `remaining`!
                # Invalidated balls (`sample_intact=False`) are disabled and CANNOT hide points from `remaining`.
                if sample_intact:
                    anchor_pts: List[PointQ] = []
                    for aid in a_ids:
                        if type(aid) is not str or aid not in remaining:
                            raise DiameterCertificateError(
                                f"Valid ball[{b_i}] at step {step_idx} references absent/routed anchor {aid!r}"
                            )
                        anchor_pts.append(active[aid])
                    c_exact, v_exact = mean_and_variance_q(anchor_pts, weights_b)
                    if c_exact != center_b or v_exact != var_b:
                        raise DiameterCertificateError(f"ball[{b_i}] center/variance mismatch at step {step_idx}")
                    # Compute node score H_i^2 = max_{a in K_i, p in P_i} ||a - p||^2 and record chain witness edges
                    for aid, a_pt in zip(a_ids, anchor_pts):
                        for pid in remaining:
                            d2 = sq_dist_q(a_pt, active[pid])
                            if d2 > best_valid_score_sq:
                                best_valid_score_sq = d2
                            valid_witness_edges.add((aid, pid))
                            valid_witness_edges.add((pid, aid))
                    # Route points inside B(c_i, (1+eta)*sqrt(V_i)) out of `remaining`
                    rad_sq = one_plus_eta_sq * var_b
                    remaining = {pid for pid in remaining if sq_dist_q(active[pid], center_b) > rad_sq}

            # Verify exact leaf covers all remaining points
            leaf_ids = ck["leaf_ids"]
            if type(leaf_ids) is not list or len(set(leaf_ids)) != len(leaf_ids):
                raise DiameterCertificateError(f"Invalid leaf_ids at step {step_idx}")
            for lid in leaf_ids:
                if type(lid) is not str or lid not in active:
                    raise DiameterCertificateError(f"leaf_id {lid!r} not in active set at step {step_idx}")
            if not remaining.issubset(set(leaf_ids)):
                raise DiameterCertificateError(f"Uncovered residual points at step {step_idx}: {sorted(remaining - set(leaf_ids))}")

            # Exact leaf diameter contribution and leaf witness edges
            leaf_pts = [active[lid] for lid in leaf_ids]
            for i in range(len(leaf_ids)):
                for j in range(i + 1, len(leaf_ids)):
                    valid_witness_edges.add((leaf_ids[i], leaf_ids[j]))
                    valid_witness_edges.add((leaf_ids[j], leaf_ids[i]))
            if len(leaf_pts) >= 2:
                leaf_d2, _ = exact_diameter_sq_q(leaf_pts)
                if leaf_d2 > best_valid_score_sq:
                    best_valid_score_sq = leaf_d2

            # Verify witness pair is active, originated from intact balls or exact leaf,
            # attains the exact chain score, and satisfies Lemma 8.1 simultaneous guarantee!
            wp = ck["witness_pair"]
            if type(wp) is not list or len(wp) != 2 or type(wp[0]) is not str or type(wp[1]) is not str:
                raise DiameterCertificateError(f"Invalid witness_pair at step {step_idx}")
            if wp[0] not in active or wp[1] not in active:
                raise DiameterCertificateError(f"Stale/deleted witness point at step {step_idx}")
            if (wp[0], wp[1]) not in valid_witness_edges:
                raise DiameterCertificateError(f"witness_pair {wp} not backed by any intact ball or exact leaf at step {step_idx}")
            w_sq = sq_dist_q(active[wp[0]], active[wp[1]])
            if _parse_rat(ck["claimed_witness_sq"], f"ckpt[{step_idx}].claimed_witness_sq") != w_sq:
                raise DiameterCertificateError(f"claimed_witness_sq mismatch at step {step_idx}")
            if w_sq != best_valid_score_sq:
                raise DiameterCertificateError(
                    f"claimed_witness_sq {w_sq} != exact chain score {best_valid_score_sq} at step {step_idx}"
                )

            exact_d2, _ = exact_diameter_sq_q(list(active.values()))
            if _parse_rat(ck["claimed_exact_diam_sq"], f"ckpt[{step_idx}].claimed_exact_diam_sq") != exact_d2:
                raise DiameterCertificateError(f"claimed_exact_diam_sq mismatch at step {step_idx}")
            if w_sq > exact_d2:
                raise DiameterCertificateError(f"Witness distance exceeded true diameter at step {step_idx}")
            if exact_d2 > cand_factor_sq * best_valid_score_sq:
                raise DiameterCertificateError(
                    f"Witness pair failed Lemma 8.1 guarantee at step {step_idx}: {exact_d2} > {cand_factor_sq} * {best_valid_score_sq}"
                )
            last_diam_sq = exact_d2
            last_witness_sq = w_sq

    if len(raw_ops) not in ckpt_by_step:
        raise DiameterCertificateError("Final stream step must be audited by a checkpoint")
    if _parse_int(cert["claimed_final_size"], "claimed_final_size") != len(active):
        raise DiameterCertificateError(f"claimed_final_size mismatch: exact={len(active)}")
    if _parse_rat(cert["claimed_final_diam_sq"], "claimed_final_diam_sq") != last_diam_sq:
        raise DiameterCertificateError(f"claimed_final_diam_sq mismatch: exact={last_diam_sq}")
    if _parse_rat(cert["claimed_final_witness_sq"], "claimed_final_witness_sq") != last_witness_sq:
        raise DiameterCertificateError(f"claimed_final_witness_sq mismatch: exact={last_witness_sq}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "ops": len(raw_ops),
        "checkpoints": len(ckpt_by_step),
        "final_size": len(active),
        "final_diam_sq": format_rat(last_diam_sq),
        "final_witness_sq": format_rat(last_witness_sq),
    }


def verify_diameter_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Top-level zero-float entry point for EUCLIDEAN-DIAM-CERT-1.0."""
    if type(cert) is not dict:
        raise DiameterCertificateError("Certificate root must be a JSON object")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise DiameterCertificateError(f"Unsupported schema: {cert.get('schema')!r}")
    cid = cert.get("cert_id")
    if type(cid) is not str or not cid:
        raise DiameterCertificateError("cert_id must be non-empty string")
    mode = cert.get("mode")
    if mode == "variance_certificate_alg4":
        return _verify_mode1_alg4(cert)
    if mode == "variance_hull_and_tightness":
        return _verify_mode2_hull(cert)
    if mode == "factor_two_two_cap_audit":
        return _verify_mode3_factor_two(cert)
    if mode == "dynamic_stream_chain_replay":
        return _verify_mode4_stream_chain(cert)
    raise DiameterCertificateError(f"Unknown verification mode: {mode!r}")
