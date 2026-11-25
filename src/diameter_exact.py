"""Pure-stdlib zero-floating-point exact-Q geometric & algorithmic primitives for
Paper 37: Giliberti & Hajiaghayi (arXiv:2611.33139, Nov 24, 2026)
"On Euclidean Diameter in Dynamic Streams".

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

PointQ = Tuple[Fraction, ...]


def sq_dist_q(p: PointQ, q: PointQ) -> Fraction:
    """Exact squared Euclidean distance between two rational vectors of equal dimension."""
    if len(p) != len(q):
        raise ValueError(f"Dimension mismatch: {len(p)} vs {len(q)}")
    total = Fraction(0, 1)
    for a, b in zip(p, q):
        d = a - b
        total += d * d
    return total


def mean_and_variance_q(
    points: Sequence[PointQ], weights: Sequence[Fraction]
) -> Tuple[PointQ, Fraction]:
    """Compute exact rational mean c = sum w_i p_i and variance V = sum w_i ||p_i - c||^2.
    Verifies weights >= 0 and sum(weights) == 1."""
    if not points or len(points) != len(weights):
        raise ValueError("Non-empty points and matching weights required")
    dim = len(points[0])
    if dim == 0:
        raise ValueError("Point dimension must be >= 1")
    w_sum = Fraction(0, 1)
    for w in weights:
        if w < 0:
            raise ValueError(f"Negative weight: {w}")
        w_sum += w
    if w_sum != Fraction(1, 1):
        raise ValueError(f"Weights must sum to 1, got {w_sum}")
    mean = [Fraction(0, 1)] * dim
    for pt, w in zip(points, weights):
        if len(pt) != dim:
            raise ValueError("Inconsistent point dimensions")
        if w != 0:
            for j in range(dim):
                mean[j] += w * pt[j]
    mean_t = tuple(mean)
    var = Fraction(0, 1)
    for pt, w in zip(points, weights):
        if w != 0:
            var += w * sq_dist_q(pt, mean_t)
    return mean_t, var


def exact_diameter_sq_q(points: Sequence[PointQ]) -> Tuple[Fraction, Tuple[int, int]]:
    """Compute exact squared diameter and lexicographically first attaining index pair."""
    n = len(points)
    if n == 0:
        raise ValueError("Empty point set")
    if n == 1:
        return Fraction(0, 1), (0, 0)
    best_d2 = Fraction(-1, 1)
    best_pair = (0, 0)
    for i in range(n):
        for j in range(i + 1, n):
            d2 = sq_dist_q(points[i], points[j])
            if d2 > best_d2:
                best_d2 = d2
                best_pair = (i, j)
    return best_d2, best_pair


def run_algorithm4_exact(
    sample: Sequence[PointQ],
    eta: Fraction,
    start_idx: int = 0,
    max_iters: int = 5000,
) -> Dict[str, object]:
    """Exact rational execution of Algorithm 4 (Section 8.1.2, arXiv:2611.33139):
    Given nonempty finite sample S in Q^d and rational 0 < eta <= 1/4, returns
    support indices K, convex weights lambda, mean c, variance V, and exact step trace
    verifying S subset B(c, (1 + eta) * sqrt(V))."""
    n = len(sample)
    if n == 0:
        raise ValueError("Sample must be nonempty")
    if not (Fraction(0, 1) < eta <= Fraction(1, 4)):
        raise ValueError(f"Require 0 < eta <= 1/4, got {eta}")
    if not (0 <= start_idx < n):
        raise ValueError("Invalid start_idx")

    a0 = sample[start_idx]
    b_idx = start_idx
    best_d0_sq = Fraction(0, 1)
    for i in range(n):
        d2 = sq_dist_q(sample[i], a0)
        if d2 > best_d0_sq:
            best_d0_sq = d2
            b_idx = i

    if best_d0_sq == 0:
        return {
            "start_idx": start_idx,
            "b_idx": start_idx,
            "D0_sq": Fraction(0, 1),
            "V0": Fraction(0, 1),
            "theta": (Fraction(1, 1) + eta) ** 2 - Fraction(1, 1),
            "gamma": ((Fraction(1, 1) + eta) ** 2 - Fraction(1, 1)) / 32,
            "support_indices": [start_idx],
            "weights": [Fraction(1, 1)],
            "mean": a0,
            "variance": Fraction(0, 1),
            "max_r2": Fraction(0, 1),
            "iterations": 0,
            "min_growth_ratio_vs_lb": None,
            "step_log": [],
        }

    one_plus_eta_sq = (Fraction(1, 1) + eta) ** 2
    theta = one_plus_eta_sq - Fraction(1, 1)
    gamma = theta / Fraction(32, 1)
    one_minus_gamma = Fraction(1, 1) - gamma
    v0 = best_d0_sq / Fraction(4, 1)

    weights = [Fraction(0, 1)] * n
    weights[start_idx] = Fraction(1, 2)
    weights[b_idx] = Fraction(1, 2)

    step_log: List[Dict[str, Fraction | int]] = []
    iters = 0
    while True:
        mean, var = mean_and_variance_q(sample, weights)
        far_idx = 0
        max_r2 = sq_dist_q(sample[0], mean)
        for i in range(1, n):
            r2 = sq_dist_q(sample[i], mean)
            if r2 > max_r2:
                max_r2 = r2
                far_idx = i
        if max_r2 <= one_plus_eta_sq * var:
            supp = [i for i, w in enumerate(weights) if w > 0]
            supp_w = [weights[i] for i in supp]
            return {
                "start_idx": start_idx,
                "b_idx": b_idx,
                "D0_sq": best_d0_sq,
                "V0": v0,
                "theta": theta,
                "gamma": gamma,
                "support_indices": supp,
                "weights": supp_w,
                "mean": mean,
                "variance": var,
                "max_r2": max_r2,
                "iterations": iters,
                "step_log": step_log,
            }
        if iters >= max_iters:
            raise RuntimeError(f"Algorithm 4 exceeded max_iters={max_iters}")
        # Update weights: lambda <- (1 - gamma) * lambda + gamma * e_a
        new_weights = [one_minus_gamma * w for w in weights]
        new_weights[far_idx] += gamma
        _, new_var = mean_and_variance_q(sample, new_weights)
        # Exact Section 8.2 algebraic identity check: V' - V == gamma*(R^2 - V) - gamma^2*R^2
        delta_v = new_var - var
        expected_delta = gamma * (max_r2 - var) - gamma * gamma * max_r2
        if delta_v != expected_delta:
            raise RuntimeError("Internal invariant failure: Algorithm 4 variance identity")
        lb_delta = (theta * theta / Fraction(64, 1)) * var
        if not (delta_v > lb_delta):
            raise RuntimeError("Internal invariant failure: variance growth lower bound")
        if new_var > Fraction(8, 1) * v0:
            raise RuntimeError("Internal invariant failure: variance exceeded 8 * V0")
        step_log.append(
            {
                "iter": iters,
                "far_idx": far_idx,
                "V_before": var,
                "R2": max_r2,
                "V_after": new_var,
                "delta_V": delta_v,
                "lb_delta": lb_delta,
            }
        )
        weights = new_weights
        iters += 1


def taylor_exp_lb_q(x: Fraction, degree: int) -> Fraction:
    """Exact rational lower bound sum_{k=0}^degree x^k / k! for exp(x) when x >= 0."""
    if x < 0 or degree < 0:
        raise ValueError("Require x >= 0 and degree >= 0")
    total = Fraction(1, 1)
    term = Fraction(1, 1)
    for k in range(1, degree + 1):
        term = term * x / Fraction(k, 1)
        total += term
    return total


def format_rat(q: Fraction) -> str:
    """Canonical reduced rational string ('n' if denominator == 1 else 'n/d')."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"
