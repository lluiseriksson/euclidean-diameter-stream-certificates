/-
  EuclideanDiameterStream.lean
  Zero-dependency Lean 4.35.0 formalization of exact algebraic, geometric,
  variance-hull, two-cap mask, and factor-two invariants for
  Giliberti & Hajiaghayi (arXiv:2611.33139, Nov 2026):
  "On Euclidean Diameter in Dynamic Streams".

  Author: Lluis Eriksson
  License: MIT
  Axiom Discipline: 0 sorry, 0 admit, 0 Classical.choice.
-/

namespace EuclideanDiameterStream

/-! ### Constructive integer helper lemmas -/

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  have h : x * x = (x.natAbs : Int) * (x.natAbs : Int) := by
    cases x with
    | ofNat n => rfl
    | negSucc n =>
      have h1 : Int.negSucc n = -((n + 1 : Nat) : Int) := rfl
      rw [h1, Int.neg_mul_neg]
      rfl
  rw [h]
  exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

private theorem sq_sub (a b : Int) : (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a]
  omega

private theorem sq_add (a b : Int) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
  omega

/-! ### Part 1: Variance-Hull Algebra & Lemma 5.1 Exact Identities -/

def wSumSqDiff (pts : List (Int × Int)) (y : Int) : Int :=
  pts.foldl (fun acc p => acc + p.1 * ((p.2 - y) * (p.2 - y))) 0

def wSumSqCentered (pts : List (Int × Int)) (W S : Int) : Int :=
  pts.foldl (fun acc p => acc + p.1 * ((W * p.2 - S) * (W * p.2 - S))) 0

def wTotal (pts : List (Int × Int)) : Int :=
  pts.foldl (fun acc p => acc + p.1) 0

def wMoment (pts : List (Int × Int)) : Int :=
  pts.foldl (fun acc p => acc + p.1 * p.2) 0

private theorem parallel_axis_point (W S y w a : Int) :
    (W * W) * (w * ((a - y) * (a - y))) =
      w * ((W * a - S) * (W * a - S))
      + 2 * ((S - W * y) * (W * (w * a) - S * w))
      + w * ((S - W * y) * (S - W * y)) := by
  have hsub : W * (a - y) = (W * a - S) + (S - W * y) := by
    rw [Int.mul_sub]; omega
  have h1 : (W * W) * (w * ((a - y) * (a - y))) = w * ((W * (a - y)) * (W * (a - y))) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [h1, hsub, sq_add]
  rw [Int.mul_add, Int.mul_add]
  have hmid : w * (2 * ((W * a - S) * (S - W * y))) =
      2 * ((S - W * y) * (W * (w * a) - S * w)) := by
    have hlin : w * (W * a - S) = W * (w * a) - S * w := by
      rw [Int.mul_sub]
      have ha : w * (W * a) = W * (w * a) := by simp [Int.mul_left_comm]
      have hb : w * S = S * w := Int.mul_comm w S
      rw [ha, hb]
    have hre : w * (2 * ((W * a - S) * (S - W * y))) =
        2 * ((S - W * y) * (w * (W * a - S))) := by
      simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hre, hlin]
  rw [hmid]

private theorem parallel_axis_aux (pts : List (Int × Int)) (W S y a1 a2 a3 a4 : Int) :
    let wT := pts.foldl (fun acc p => acc + p.1) a3
    let mT := pts.foldl (fun acc p => acc + p.1 * p.2) a4
    let dT := pts.foldl (fun acc p => acc + p.1 * ((p.2 - y) * (p.2 - y))) a1
    let cT := pts.foldl (fun acc p => acc + p.1 * ((W * p.2 - S) * (W * p.2 - S))) a2
    (W * W) * (dT - a1) =
      (cT - a2) + 2 * ((S - W * y) * (W * (mT - a4) - S * (wT - a3)))
      + (wT - a3) * ((S - W * y) * (S - W * y)) := by
  induction pts generalizing a1 a2 a3 a4 with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hstep := ih
      (a1 + p.1 * ((p.2 - y) * (p.2 - y)))
      (a2 + p.1 * ((W * p.2 - S) * (W * p.2 - S)))
      (a3 + p.1)
      (a4 + p.1 * p.2)
    have hpt := parallel_axis_point W S y p.1 p.2
    let dT := ps.foldl (fun acc q => acc + q.1 * ((q.2 - y) * (q.2 - y)))
      (a1 + p.1 * ((p.2 - y) * (p.2 - y)))
    let cT := ps.foldl (fun acc q => acc + q.1 * ((W * q.2 - S) * (W * q.2 - S)))
      (a2 + p.1 * ((W * p.2 - S) * (W * p.2 - S)))
    let wT := ps.foldl (fun acc q => acc + q.1) (a3 + p.1)
    let mT := ps.foldl (fun acc q => acc + q.1 * q.2) (a4 + p.1 * p.2)
    have hstep' :
        (W * W) * (dT - (a1 + p.1 * ((p.2 - y) * (p.2 - y)))) =
          (cT - (a2 + p.1 * ((W * p.2 - S) * (W * p.2 - S))))
          + 2 * ((S - W * y) * (W * (mT - (a4 + p.1 * p.2)) - S * (wT - (a3 + p.1))))
          + (wT - (a3 + p.1)) * ((S - W * y) * (S - W * y)) := hstep
    have hd : dT - a1 = (dT - (a1 + p.1 * ((p.2 - y) * (p.2 - y)))) + p.1 * ((p.2 - y) * (p.2 - y)) := by omega
    have hc : cT - a2 = (cT - (a2 + p.1 * ((W * p.2 - S) * (W * p.2 - S)))) + p.1 * ((W * p.2 - S) * (W * p.2 - S)) := by omega
    have hw : wT - a3 = (wT - (a3 + p.1)) + p.1 := by omega
    have hm : mT - a4 = (mT - (a4 + p.1 * p.2)) + p.1 * p.2 := by omega
    change (W * W) * (dT - a1) =
      (cT - a2) + 2 * ((S - W * y) * (W * (mT - a4) - S * (wT - a3)))
      + (wT - a3) * ((S - W * y) * (S - W * y))
    rw [hd, hc, hw, hm, Int.mul_add, Int.mul_add, Int.mul_add, Int.add_mul]
    have hlin : W * (mT - (a4 + p.1 * p.2)) + W * (p.1 * p.2) - (S * (wT - (a3 + p.1)) + S * p.1) =
        (W * (mT - (a4 + p.1 * p.2)) - S * (wT - (a3 + p.1))) + (W * (p.1 * p.2) - S * p.1) := by omega
    rw [hlin, Int.mul_add]
    omega

/-- Theorem 1 (Parallel-Axis / Variance-Distance Identity in cleared integers):
    For any finite weighted point list `pts` with total weight `W = ∑ w_i` and
    first moment `S = ∑ w_i a_i`, and any query coordinate `y`:
      `W^2 * ∑ w_i (a_i - y)^2 = ∑ w_i (W a_i - S)^2 + W (S - W y)^2`. -/
theorem parallel_axis_cleared_identity (pts : List (Int × Int)) (y : Int) :
    let W := wTotal pts
    let S := wMoment pts
    (W * W) * wSumSqDiff pts y =
      wSumSqCentered pts W S + W * ((S - W * y) * (S - W * y)) := by
  dsimp only [wTotal, wMoment, wSumSqDiff, wSumSqCentered]
  have h := parallel_axis_aux pts (pts.foldl (fun acc p => acc + p.1) 0)
    (pts.foldl (fun acc p => acc + p.1 * p.2) 0) y 0 0 0 0
  simp only [Int.sub_zero] at h
  have hzero :
      pts.foldl (fun acc p => acc + p.1) 0 * pts.foldl (fun acc p => acc + p.1 * p.2) 0
      - pts.foldl (fun acc p => acc + p.1 * p.2) 0 * pts.foldl (fun acc p => acc + p.1) 0 = 0 := by
    rw [Int.mul_comm (pts.foldl (fun acc p => acc + p.1) 0)]
    exact Int.sub_self _
  rw [hzero, Int.mul_zero, Int.mul_zero, Int.add_zero] at h
  exact h

/-- Theorem 2 (Lemma 5.1 Cauchy-Schwarz Hull Diameter Bound in cleared integers):
    If `h^2 + V + W ≤ L^2`, `u^2 ≤ V`, `w^2 ≤ W`, then
      `(h + s * (u + w))^2 ≤ (2 * s^2 + 1) * L^2`.
    Setting `s^2 = a^2 - 1` yields `2 * s^2 + 1 = 2 * a^2 - 1` (Eq. 12). -/
theorem hull_diameter_cauchy_schwarz (h s u w V W L : Int)
    (hVW : h * h + V + W ≤ L * L)
    (hu : u * u ≤ V)
    (hw : w * w ≤ W) :
    (h + s * (u + w)) * (h + s * (u + w)) ≤ (2 * (s * s) + 1) * (L * L) := by
  have h1 : 0 ≤ (s * h - u) * (s * h - u) := int_sq_nonneg _
  have h2 : 0 ≤ (s * h - w) * (s * h - w) := int_sq_nonneg _
  have h3 : 0 ≤ (s * s) * ((u - w) * (u - w)) :=
    Int.mul_nonneg (int_sq_nonneg s) (int_sq_nonneg (u - w))
  have hid :
      (2 * (s * s) + 1) * (h * h + u * u + w * w) - (h + s * (u + w)) * (h + s * (u + w)) =
        (s * h - u) * (s * h - u) + (s * h - w) * (s * h - w) + (s * s) * ((u - w) * (u - w)) := by
    have ha : (2 * (s * s) + 1) * (h * h + u * u + w * w) =
        2 * ((s * h) * (s * h)) + 2 * ((s * u) * (s * u)) + 2 * ((s * w) * (s * w))
        + h * h + u * u + w * w := by
      rw [Int.add_mul, Int.one_mul, Int.mul_add, Int.mul_add]
      have p1 : 2 * (s * s) * (h * h) = 2 * ((s * h) * (s * h)) := by
        simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      have p2 : 2 * (s * s) * (u * u) = 2 * ((s * u) * (s * u)) := by
        simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      have p3 : 2 * (s * s) * (w * w) = 2 * ((s * w) * (s * w)) := by
        simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [p1, p2, p3]
      omega
    have hb : (h + s * (u + w)) * (h + s * (u + w)) =
        h * h + 2 * ((s * h) * u) + 2 * ((s * h) * w)
        + (s * u) * (s * u) + 2 * ((s * u) * (s * w)) + (s * w) * (s * w) := by
      rw [sq_add, Int.mul_add, sq_add]
      have q1 : h * (s * u + s * w) = (s * h) * u + (s * h) * w := by
        rw [Int.mul_add]
        have r1 : h * (s * u) = (s * h) * u := by rw [← Int.mul_assoc, Int.mul_comm h s]
        have r2 : h * (s * w) = (s * h) * w := by rw [← Int.mul_assoc, Int.mul_comm h s]
        rw [r1, r2]
      rw [q1, Int.mul_add]
      omega
    have hc : (s * h - u) * (s * h - u) = (s * h) * (s * h) - 2 * ((s * h) * u) + u * u :=
      sq_sub (s * h) u
    have hd : (s * h - w) * (s * h - w) = (s * h) * (s * h) - 2 * ((s * h) * w) + w * w :=
      sq_sub (s * h) w
    have he : (s * s) * ((u - w) * (u - w)) =
        (s * u) * (s * u) - 2 * ((s * u) * (s * w)) + (s * w) * (s * w) := by
      rw [sq_sub, Int.mul_add, Int.mul_sub]
      have r1 : (s * s) * (u * u) = (s * u) * (s * u) := by
        simp [Int.mul_comm, Int.mul_left_comm]
      have r2 : (s * s) * (2 * (u * w)) = 2 * ((s * u) * (s * w)) := by
        simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      have r3 : (s * s) * (w * w) = (s * w) * (s * w) := by
        simp [Int.mul_comm, Int.mul_left_comm]
      rw [r1, r2, r3]
    rw [ha, hb, hc, hd, he]
    omega
  have hsum : h * h + u * u + w * w ≤ L * L := by omega
  have hpos : 0 ≤ 2 * (s * s) + 1 := by
    have hs := int_sq_nonneg s
    omega
  have hmono : (2 * (s * s) + 1) * (h * h + u * u + w * w) ≤ (2 * (s * s) + 1) * (L * L) :=
    Int.mul_le_mul_of_nonneg_left hsum hpos
  omega

/-- Theorem 3 (The √3 Hull Barrier at a = √2):
    For any rational `a = p / q` with `p^2 > 2 q^2` and `2 p^2 < (c^2 + 1) q^2`,
    the squared hull factor `2 a^2 - 1` lies strictly in `(3, c^2)`. -/
theorem hull_sqrt3_barrier (p q c : Int)
    (h_gt_sqrt2 : 2 * (q * q) < p * p)
    (h_lt_c : 2 * (p * p) < (c * c + 1) * (q * q)) :
    3 * (q * q) < 2 * (p * p) - q * q ∧ 2 * (p * p) - q * q < (c * c) * (q * q) := by
  constructor
  · omega
  · rw [Int.add_mul, Int.one_mul] at h_lt_c
    omega

/-- Theorem 4 (Tightness via Two Orthogonal Regular Simplices, Section 5.1):
    If `(2 A - 1) h^2 = S^2` and `V = (A - 1) h^2`, then:
      1. Cross-simplex squared distance equals `h^2 + 2 V = S^2`.
      2. Outermost hull separation `h + 2 (A - 1) h = (2 A - 1) h` has square
         `(2 A - 1) S^2`, attaining the exact Lemma 5.1 bound `√(2a^2 - 1) L_S`. -/
theorem two_simplex_tightness_exact (A h S V : Int)
    (hh : (2 * A - 1) * (h * h) = S * S)
    (hV : V = (A - 1) * (h * h)) :
    h * h + 2 * V = S * S ∧
    (h + 2 * ((A - 1) * h)) * (h + 2 * ((A - 1) * h)) = (2 * A - 1) * (S * S) := by
  constructor
  · rw [hV]
    have h1 : h * h + 2 * ((A - 1) * (h * h)) = (2 * A - 1) * (h * h) := by
      rw [Int.sub_mul, Int.sub_mul, Int.one_mul, Int.mul_sub]
      have ha : 2 * (A * (h * h)) = (2 * A) * (h * h) := by rw [Int.mul_assoc]
      rw [ha]; omega
    rw [h1, hh]
  · have hlin : h + 2 * ((A - 1) * h) = (2 * A - 1) * h := by
      rw [Int.sub_mul, Int.sub_mul, Int.one_mul, Int.mul_sub]
      have ha : 2 * (A * h) = (2 * A) * h := by rw [Int.mul_assoc]
      rw [ha]; omega
    rw [hlin]
    have hsq : ((2 * A - 1) * h) * ((2 * A - 1) * h) =
        (2 * A - 1) * ((2 * A - 1) * (h * h)) := by
      simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hsq, hh]

/-- Theorem 5 (Bounded Witness Ball Radii, Eq. 13):
    If `d * dist > a_num * R` (`d > 0`) and `dist ≤ D_univ + R`, then
    `(a_num - d) * R < d * D_univ`. -/
theorem bounded_witness_radius (a_num d dist R D_univ : Int)
    (hd : 0 < d)
    (h_ext : a_num * R < d * dist)
    (h_tri : dist ≤ D_univ + R) :
    (a_num - d) * R < d * D_univ := by
  have h1 : d * dist ≤ d * (D_univ + R) := Int.mul_le_mul_of_nonneg_left h_tri (by omega)
  have h2 : d * (D_univ + R) = d * D_univ + d * R := Int.mul_add d D_univ R
  have h3 : (a_num - d) * R = a_num * R - d * R := Int.sub_mul a_num d R
  omega

/-! ### Part 2: Section 8 Algorithm 4 Rational Variance Certificate -/

/-- Theorem 6 (Exact 1-Step Variance Update of Algorithm 4, Section 8.2):
    In cleared integer form with `γ = g / D`:
      `(D - g)(D^2 V + g^2 R^2) + g(D - g)^2 R^2 - D^3 V = D (D g (R^2 - V) - g^2 R^2)`. -/
theorem algorithm4_variance_update_identity (D g V R2 : Int) :
    ((D - g) * ((D * D) * V + (g * g) * R2) + g * ((D - g) * (D - g)) * R2) - (D * D * D) * V =
      D * (D * g * (R2 - V) - (g * g) * R2) := by
  have h1 : (D - g) * ((D * D) * V) = (D * D * D) * V - (D * D * g) * V := by
    rw [Int.sub_mul]
    have ea : D * ((D * D) * V) = (D * D * D) * V := by simp [Int.mul_assoc]
    have eb : g * ((D * D) * V) = (D * D * g) * V := by simp [Int.mul_comm, Int.mul_left_comm]
    rw [ea, eb]
  have h2 : (D - g) * ((g * g) * R2) = (D * g * g) * R2 - (g * g * g) * R2 := by
    rw [Int.sub_mul]
    have ea : D * ((g * g) * R2) = (D * g * g) * R2 := by simp [Int.mul_assoc]
    have eb : g * ((g * g) * R2) = (g * g * g) * R2 := by simp [Int.mul_assoc]
    rw [ea, eb]
  have h3 : g * ((D - g) * (D - g)) * R2 =
      (D * D * g) * R2 - 2 * ((D * g * g) * R2) + (g * g * g) * R2 := by
    rw [sq_sub, Int.mul_add, Int.mul_sub, Int.add_mul, Int.sub_mul]
    have ea : g * (D * D) * R2 = (D * D * g) * R2 := by simp [Int.mul_comm, Int.mul_left_comm]
    have eb : g * (2 * (D * g)) * R2 = 2 * ((D * g * g) * R2) := by
      simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have ec : g * (g * g) * R2 = (g * g * g) * R2 := by simp [Int.mul_assoc]
    rw [ea, eb, ec]
  have h4 : D * (D * g * (R2 - V) - (g * g) * R2) =
      (D * D * g) * R2 - (D * D * g) * V - (D * g * g) * R2 := by
    rw [Int.mul_sub, Int.mul_sub, Int.mul_sub]
    have ea : D * (D * g * R2) = (D * D * g) * R2 := by simp [Int.mul_assoc]
    have eb : D * (D * g * V) = (D * D * g) * V := by simp [Int.mul_assoc]
    have ec : D * ((g * g) * R2) = (D * g * g) * R2 := by simp [Int.mul_assoc]
    rw [ea, eb, ec]
  rw [Int.mul_add, h1, h2, h3, h4]
  omega

/-- Theorem 7 (Algorithm 4 Multiplicative Variance Growth Lower Bound, Section 8.2):
    With `θ = tn / td > 0` and `γ = θ / 32`, if `tn * V < td * (R2 - V)` and
    `R2 ≤ 16 * V`, then `16 * tn^2 * V < 32 * td * tn * (R2 - V) - tn^2 * R2`,
    which is the exact cleared form of `V' - V > (θ^2 / 64) * V`. -/
theorem algorithm4_variance_growth_lb (tn td V R2 : Int)
    (htn : 0 < tn)
    (hfail : tn * V < td * (R2 - V))
    (hcap : R2 ≤ 16 * V) :
    16 * ((tn * tn) * V) < 32 * (td * tn * (R2 - V)) - (tn * tn) * R2 := by
  have h1 : (32 * tn) * (tn * V) < (32 * tn) * (td * (R2 - V)) :=
    Int.mul_lt_mul_of_pos_left hfail (by omega)
  have h2 : (tn * tn) * R2 ≤ (tn * tn) * (16 * V) :=
    Int.mul_le_mul_of_nonneg_left hcap (int_sq_nonneg tn)
  have e1 : (32 * tn) * (tn * V) = 32 * ((tn * tn) * V) := by simp [Int.mul_assoc]
  have e2 : (32 * tn) * (td * (R2 - V)) = 32 * (td * tn * (R2 - V)) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e3 : (tn * tn) * (16 * V) = 16 * ((tn * tn) * V) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e1, e2] at h1
  rw [e3] at h2
  omega

/-- Theorem 8 (Algorithm 4 Upper Variance Cap `V ≤ 8 V_0`, Section 8.2):
    From `2 V ≤ diam^2 ≤ 4 D_0^2` and `4 V_0 = D_0^2`, we obtain `V ≤ 8 V_0`. -/
theorem algorithm4_variance_cap_8V0 (V diam2 D02 V0 : Int)
    (hV : 2 * V ≤ diam2)
    (hdiam : diam2 ≤ 4 * D02)
    (hV0 : 4 * V0 = D02) :
    V ≤ 8 * V0 := by
  omega

/-- Theorem 9 (Candidate-Score Cauchy-Schwarz Bound, Lemma 8.1):
    If `0 ≤ d * u`, `0 ≤ d * t`, `d * u ≤ p * r`, and `r^2 + t^2 ≤ H^2`, then
    `(d * u + d * t)^2 ≤ (p^2 + d^2) * H^2`. -/
theorem candidate_score_cauchy_schwarz (d p u r t H : Int)
    (hu : 0 ≤ d * u)
    (ht : 0 ≤ d * t)
    (hball : d * u ≤ p * r)
    (hH : r * r + t * t ≤ H * H) :
    (d * u + d * t) * (d * u + d * t) ≤ (p * p + d * d) * (H * H) := by
  have hlin : d * u + d * t ≤ p * r + d * t := by omega
  have hnn : 0 ≤ d * u + d * t := by omega
  have hsq1 : (d * u + d * t) * (d * u + d * t) ≤ (p * r + d * t) * (p * r + d * t) := by
    have h1 := Int.mul_le_mul_of_nonneg_left hlin hnn
    have h2 := Int.mul_le_mul_of_nonneg_right hlin (by omega : 0 ≤ p * r + d * t)
    exact Int.le_trans h1 h2
  have hcs : (p * r + d * t) * (p * r + d * t) ≤ (p * p + d * d) * (r * r + t * t) := by
    have hdiff : (p * p + d * d) * (r * r + t * t) - (p * r + d * t) * (p * r + d * t) =
        (p * t - d * r) * (p * t - d * r) := by
      rw [sq_add, sq_sub, Int.add_mul, Int.mul_add, Int.mul_add]
      have a1 : (p * p) * (r * r) = (p * r) * (p * r) := by simp [Int.mul_comm, Int.mul_left_comm]
      have a2 : (d * d) * (t * t) = (d * t) * (d * t) := by simp [Int.mul_comm, Int.mul_left_comm]
      have a3 : (p * p) * (t * t) = (p * t) * (p * t) := by simp [Int.mul_comm, Int.mul_left_comm]
      have a4 : (d * d) * (r * r) = (d * r) * (d * r) := by simp [Int.mul_comm, Int.mul_left_comm]
      have a5 : (p * r) * (d * t) = (p * t) * (d * r) := by simp [Int.mul_comm, Int.mul_left_comm]
      rw [a1, a2, a3, a4, a5]
      omega
    have hnn2 := int_sq_nonneg (p * t - d * r)
    omega
  have hpd : 0 ≤ p * p + d * d := Int.add_nonneg (int_sq_nonneg p) (int_sq_nonneg d)
  have hmono : (p * p + d * d) * (r * r + t * t) ≤ (p * p + d * d) * (H * H) :=
    Int.mul_le_mul_of_nonneg_left hH hpd
  exact Int.le_trans hsq1 (Int.le_trans hcs hmono)

/-! ### Part 3: Two-Stage Spherical Cap & Appendix A.1 Factor-Two Suite -/

/-- Theorem 10 (3-4-5 Spherical Cap Containment, Figure 1 & Section A.1.2):
    For `D ≥ 0`, `t^2 + q ≤ D^2`, and `5 t ≥ 3 D`, we have
    `(5 t - 3 D)^2 + 25 q ≤ 16 D^2`, i.e., `(t - 3/5)^2 + q ≤ (4/5)^2`. -/
theorem spherical_cap_345_containment (t q D : Int)
    (hD : 0 ≤ D)
    (hball : t * t + q ≤ D * D)
    (hcap : 3 * D ≤ 5 * t) :
    (5 * t - 3 * D) * (5 * t - 3 * D) + 25 * q ≤ 16 * (D * D) := by
  have hexp : (5 * t - 3 * D) * (5 * t - 3 * D) + 25 * q =
      25 * (t * t + q) - (6 * D) * (5 * t) + 9 * (D * D) := by
    rw [sq_sub, Int.mul_add]
    have e1 : (5 * t) * (5 * t) = 25 * (t * t) := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e2 : 2 * ((5 * t) * (3 * D)) = (6 * D) * (5 * t) := by
      simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e3 : (3 * D) * (3 * D) = 9 * (D * D) := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e1, e2, e3]
    omega
  have h1 : 25 * (t * t + q) ≤ 25 * (D * D) :=
    Int.mul_le_mul_of_nonneg_left hball (by decide)
  have h2 : (6 * D) * (3 * D) ≤ (6 * D) * (5 * t) :=
    Int.mul_le_mul_of_nonneg_left hcap (by omega)
  have h3 : (6 * D) * (3 * D) = 18 * (D * D) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [h3] at h2
  rw [hexp]
  omega

/-- Theorem 11 (Exact SOS Lower Bound on `(λ - t)^2 - q ≥ λ^2/2 - 1`, Section A.1.2):
    For all `λ, t, q, D` with `t^2 + q ≤ D^2`:
      `2((λ - t)^2 - q) - (λ^2 - 2 D^2) = (λ - 2 t)^2 + 2(D^2 - t^2 - q) ≥ 0`. -/
theorem potential_quadratic_margin_sos (lam t q D : Int)
    (hball : t * t + q ≤ D * D) :
    lam * lam - 2 * (D * D) ≤ 2 * ((lam - t) * (lam - t) - q) := by
  have hsq : 0 ≤ (lam - 2 * t) * (lam - 2 * t) := int_sq_nonneg _
  have hid :
      2 * ((lam - t) * (lam - t) - q) - (lam * lam - 2 * (D * D)) =
        (lam - 2 * t) * (lam - 2 * t) + 2 * (D * D - (t * t + q)) := by
    rw [sq_sub lam t, sq_sub lam (2 * t)]
    have e1 : lam * (2 * t) = 2 * (lam * t) := by simp [Int.mul_assoc, Int.mul_comm]
    have e2 : (2 * t) * (2 * t) = 4 * (t * t) := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e1, e2]
    omega
  omega

/-- Theorem 12 (Exact Algebraic Identity for Eq. 29 in Appendix A.1.3):
    For all `λ, t, D`:
      `(λ - t)^2 D^2 - (λ^2 - D^2)(D^2 - t^2) = (λ t - D^2)^2`. -/
theorem potential_monotone_eq29_identity (lam t D : Int) :
    ((lam - t) * (lam - t)) * (D * D) - (lam * lam - D * D) * (D * D - t * t) =
      (lam * t - D * D) * (lam * t - D * D) := by
  rw [sq_sub lam t, sq_sub (lam * t) (D * D)]
  rw [Int.add_mul, Int.sub_mul, Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have a1 : (lam * lam) * (t * t) = (lam * t) * (lam * t) := by
    simp [Int.mul_comm, Int.mul_left_comm]
  have a2 : 2 * (lam * t) * (D * D) = 2 * ((lam * t) * (D * D)) := by rw [Int.mul_assoc]
  have a3 : (t * t) * (D * D) = (D * D) * (t * t) := Int.mul_comm _ _
  rw [a1, a2, a3]
  omega

/-- Theorem 13 (Appendix A.1.2 First-Mask Right-Endpoint Exact Rational Check):
    At `λ = 79/50`, `t = 3/5`:
      `g(3/5) = -135925 / 312500 = -0.43496 < 0`,
      `(λ - t)^2 / (1 - t^2) - 1 = 801 / 1600 > 1/2`,
      `(16/25) * (1 + 1/2 + 1/8 + 1/48) = 79/75 > 21/20`. -/
theorem first_mask_endpoint_exact :
    (3 * 25 * 79 * 79 - 79 * 50 * 9 * 5 + 27 * 2500 - 79 * 50 * 125 = -135925) ∧
    (49 * 49 * 25 - 16 * 50 * 50 = 801 * 25) ∧
    (801 * 2 > 1600) ∧
    (16 * 79 * 20 > 25 * 48 * 21) := by
  decide

/-- Theorem 14 (Appendix A.1.2 Second-Mask Empty Global Lower Bound):
    At `λ = 79/50`: `m = 1241/5000`, and `(65/24) * (1241/5000) = 16133/24000 > 84/125`. -/
theorem second_mask_empty_exact :
    (79 * 79 - 2 * 50 * 50 = 1241) ∧
    (65 * 1241 = 16133 * 5) ∧
    (24 * 5000 = 24000 * 5) ∧
    (16133 * 125 > 24000 * 84) ∧
    (21 * 16 * 125 = 20 * 25 * 84) := by
  decide

/-- Theorem 15 (Appendix A.1 Table 3 Factor-Two Three-Case Strict Margins):
    At `a = 1581/1000`, `η_in = 1/100`, `κ = 109/100`:
      `a^2 > 2`, `2 a^2 - 1 = 3.999122 < 4`,
      `(1 + η_in)^2 + a^2 κ^2 = 3.9898284241 < 3.999122`,
      `(1 + η_in)^2 + 1 = 2.0201 < 3.999122`. -/
theorem factor_two_table3_three_cases :
    (1581 * 1581 > 2 * 1000 * 1000) ∧
    (2 * 1581 * 1581 - 1000000 = 3999122) ∧
    (3999122 < 4000000) ∧
    (101 * 101 * 1000000 + 1581 * 1581 * 109 * 109 = 39898284241) ∧
    (39898284241 < 3999122 * 10000) ∧
    (101 * 101 + 10000 = 20201) ∧
    (20201 * 100 < 3999122) := by
  decide

/-- Theorem 16 (Appendix A.1.3 & A.1.4 Oracle Accuracy & Coupled Tail Inequalities):
    Verifies all 5 exact rational margins in Sections A.1.3–A.1.4. -/
theorem appendix_a1_oracle_and_coupling_exact :
    (109 * 9949 = 1084441) ∧
    (1084441 > 10801 * 100) ∧
    (1664 * 1664 * 170 > 4 * 11664 * 10000) ∧
    (297 * 297 * 1950 > 17152 * 10000) ∧
    (75 * 17152 < 24 * 4 * 297 * 47) ∧
    (1024 * 8 * 1024 * 8 < 99 * 99 * 69 * 100) := by
  decide

/-! ### Part 4: Section 8.2 Rebuild Deadline & Section A.1.6 Space-Exponent Suite -/

/-- Theorem 17 (De-amortized Rebuild Deletion Budget & Geometric Shrinkage):
    For `B ≥ 128`, `m ≥ 128 * B`, `|P_i| ≥ m - 3 (m / B)`, and
    `|P_{i+1}| ≤ m / 2 + 3 (m / B)`, we have `5 |P_{i+1}| < 3 |P_i|` (`< 0.6 |P_i|`). -/
theorem rebuild_geometric_shrinkage (B m Pi Pi1 : Nat)
    (hB : 128 ≤ B)
    (hm : 128 * B ≤ m)
    (hPi : m - 3 * (m / B) ≤ Pi)
    (hPi1 : Pi1 ≤ m / 2 + 3 * (m / B)) :
    5 * Pi1 < 3 * Pi := by
  have hdiv : 128 * (m / B) ≤ m := by
    have h1 := Nat.mul_div_le m B
    have h2 : 128 * (m / B) ≤ B * (m / B) := Nat.mul_le_mul_right (m / B) hB
    exact Nat.le_trans h2 h1
  have hm_pos : 16384 ≤ m := by
    have : 128 * 128 ≤ 128 * B := Nat.mul_le_mul_left 128 hB
    omega
  omega

/-- Theorem 18 (Appendix A.1.1 & A.1.6 Scale Chain and Space-Exponent Certificate):
    Verifies:
      1. `a / q_scale > λ_0 > λ > √2` at `a=1581/1000, q_scale=5001/5000, λ_0=7903/5000, λ=79/50`.
      2. Oracle work per update: `s (B_κ + 1) - 1 = -2/2003 < 0` at `s=1/2003, B_κ=2000`.
      3. Recovery saving: `1 / (96000 * 2003 * 33) = 1 / 6345504000 > 1 / 10^10`.
      4. Remaining exponents: `2000/2003 < 1 - 10^{-10}` and `1 - 1/4006 < 1 - 10^{-10}`. -/
theorem appendix_a1_scale_chain_and_exponents :
    (1581 * 5000 * 5000 > 1000 * 5001 * 7903) ∧
    (7903 > 79 * 100) ∧
    (79 * 79 > 2 * 50 * 50) ∧
    (96000 * 2003 * 33 = 6345504000) ∧
    (6345504000 < 10000000000) ∧
    ((2001 : Int) - 2003 = -2) ∧
    (2000 * 10000000000 < 2003 * 9999999999) ∧
    (4005 * 10000000000 < 4006 * 9999999999) := by
  decide

end EuclideanDiameterStream
