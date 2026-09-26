/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.PolygonHausdorff
public import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.CyclicSum

/-!
# Cauchy perimeter of an inscribed cyclic polygon

For every direction `u`, the cyclic total variation of the linear functional `⟪·, u⟫` along the
vertices of the inscribed polygon equals twice its width:

```
∑ j, |⟪v (j+1) - v j, u⟫| = 2 * width P u.
```

Integrating this identity over the circle and using `∫₀^{2π} |⟪e, circleVec θ⟫| dθ = 4 ‖e‖`
identifies the Cauchy perimeter of the polygon with the sum of its edge lengths.
-/

@[expose] public section

open Set MeasureTheory NRR.Geometry
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace HumanVerification.CauchyCrofton

/-! ### The elementary edge integral -/

/-- Full-period integral of the absolute cosine. -/
theorem integral_abs_cos_full_period (φ : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), |Real.cos (θ - φ)|) = 4 := by
  have hpi := Real.pi_pos
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => |Real.cos x|) volume a b :=
    fun a b => (Real.continuous_cos.abs).intervalIntegrable a b
  have h1 : (∫ x in (0 : ℝ)..(Real.pi / 2), |Real.cos x|) = 1 := by
    have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2), |Real.cos x| = Real.cos x := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], hx.2⟩)
    rw [intervalIntegral.integral_congr hcongr, integral_cos]
    simp
  have h2 : (∫ x in (Real.pi / 2 : ℝ)..(3 * Real.pi / 2), |Real.cos x|) = 2 := by
    have hcongr : ∀ x ∈ Set.uIcc (Real.pi / 2 : ℝ) (3 * Real.pi / 2),
        |Real.cos x| = -Real.cos x := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le hx.1 (by linarith [hx.2]))
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_neg,
      integral_cos]
    have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
      have : (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 := by ring
      rw [this, Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two]
      ring
    rw [hsin, Real.sin_pi_div_two]
    norm_num
  have h3 : (∫ x in (3 * Real.pi / 2 : ℝ)..(2 * Real.pi), |Real.cos x|) = 1 := by
    have hcongr : ∀ x ∈ Set.uIcc (3 * Real.pi / 2 : ℝ) (2 * Real.pi),
        |Real.cos x| = Real.cos x := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      refine abs_of_nonneg ?_
      have hshift : Real.cos x = Real.cos (x - 2 * Real.pi) := by
        rw [Real.cos_sub_two_pi]
      rw [hshift]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [intervalIntegral.integral_congr hcongr, integral_cos]
    have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
      have : (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 := by ring
      rw [this, Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two]
      ring
    rw [hsin, Real.sin_two_pi]
    norm_num
  have hsplit : (∫ x in (0 : ℝ)..(2 * Real.pi), |Real.cos x|) = 4 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (a := (0:ℝ)) (b := 3 * Real.pi / 2) (c := 2 * Real.pi) (hint _ _) (hint _ _),
      ← intervalIntegral.integral_add_adjacent_intervals
        (a := (0:ℝ)) (b := Real.pi / 2) (c := 3 * Real.pi / 2) (hint _ _) (hint _ _),
      h1, h2, h3]
    norm_num
  have hper2 : Function.Periodic (fun x : ℝ => |Real.cos x|) (2 * Real.pi) := by
    intro x
    change |Real.cos (x + 2 * Real.pi)| = |Real.cos x|
    rw [Real.cos_add_two_pi]
  have hshift : (∫ θ in (0 : ℝ)..(2 * Real.pi), |Real.cos (θ - φ)|)
      = ∫ x in (0 - φ : ℝ)..(2 * Real.pi - φ), |Real.cos x| := by
    rw [intervalIntegral.integral_comp_sub_right (fun x => |Real.cos x|) φ]
  rw [hshift, show (2 * Real.pi - φ : ℝ) = (0 - φ) + 2 * Real.pi by ring,
    hper2.intervalIntegral_add_eq (0 - φ) 0]
  simpa using hsplit

/-- Integral of the absolute projection of one edge over the unit circle. -/
theorem integral_abs_inner_circleVec (e : Point2) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), |(inner ℝ e (circleVec θ) : ℝ)|) = 4 * ‖e‖ := by
  obtain ⟨φ, -, hφ⟩ := exists_angle e 0
  have hpoint : ∀ θ : ℝ, (inner ℝ e (circleVec θ) : ℝ) = ‖e‖ * Real.cos (θ - φ) := by
    intro θ
    conv_lhs => rw [hφ]
    rw [real_inner_smul_left, inner_circleVec_circleVec]
  have hcongr : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      |(inner ℝ e (circleVec θ) : ℝ)| = ‖e‖ * |Real.cos (θ - φ)| := by
    intro θ _
    rw [hpoint θ, abs_mul, abs_of_nonneg (norm_nonneg e)]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_abs_cos_full_period]
  ring

/-! ### Width of the inscribed polygon -/

variable {K : Body} {A : AngleSystem}

/-- There is a vertex maximizing any linear functional. -/
theorem exists_max_vtx (K : Body) (A : AngleSystem) (u : Point2) :
    ∃ j : ℤ, ∀ k : ℤ, (inner ℝ (vtx K A k) u : ℝ) ≤ (inner ℝ (vtx K A j) u : ℝ) := by
  classical
  have hne : (Finset.univ : Finset (Fin A.m)).Nonempty :=
    ⟨⟨0, A.m_pos⟩, Finset.mem_univ _⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin A.m))
    (fun i : Fin A.m => (inner ℝ (vtx K A (i : ℤ)) u : ℝ)) hne
  refine ⟨(i0 : ℤ), fun k => ?_⟩
  obtain ⟨i, hi⟩ := exists_fin_vtx_eq (K := K) (A := A) k
  rw [← hi]
  exact hi0 i (Finset.mem_univ i)

/-- The support function of the polygon is the maximum of the vertex values. -/
theorem supportFunction_polyBody (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {w : Point2} (hw : w ≠ 0) {C : ℝ}
    (hle : ∀ j : ℤ, (inner ℝ (vtx K A j) w : ℝ) ≤ C)
    (hex : ∃ j : ℤ, (inner ℝ (vtx K A j) w : ℝ) = C) :
    NRR.Geometry.ConvexBody.supportFunction (polyBody K A h0) w = C := by
  have hlin : IsLinearMap ℝ (fun x : Point2 => (inner ℝ x w : ℝ)) :=
    ⟨fun a b => inner_add_left _ _ _, fun c a => real_inner_smul_left _ _ _⟩
  -- the maximum is positive
  have hCpos : 0 < C := by
    obtain ⟨ε, hε, hball⟩ := exists_ball_subset_polySet (K := K) (A := A) h0
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
    set x : Point2 := (ε / (2 * ‖w‖)) • w with hx
    have hxball : x ∈ Metric.ball (0 : Point2) ε := by
      rw [Metric.mem_ball, dist_zero_right, hx, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ε / (2 * ‖w‖))]
      have hcalc : ‖w‖ * (ε / (2 * ‖w‖)) = ε / 2 := by field_simp
      rw [mul_comm, hcalc]
      linarith
    have hxP : x ∈ polySet K A := hball hxball
    have hxinner : (inner ℝ x w : ℝ) = ε * ‖w‖ / 2 := by
      rw [hx, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    have hbound : polySet K A ⊆ {y : Point2 | (inner ℝ y w : ℝ) ≤ max 0 C} := by
      refine convexHull_min ?_ (convex_halfSpace_le hlin _)
      rintro y (rfl | ⟨i, rfl⟩)
      · simp
      · exact le_trans (hle _) (le_max_right 0 C)
    have := hbound hxP
    simp only [Set.mem_ofPred_eq, hxinner] at this
    rcases le_or_gt C 0 with hC | hC
    · rw [max_eq_left hC] at this
      nlinarith
    · exact hC
  refine le_antisymm ?_ ?_
  · refine NRR.Geometry.ConvexBody.supportFunction_le _ ?_
    intro y hy
    have hbound : polySet K A ⊆ {z : Point2 | (inner ℝ z w : ℝ) ≤ C} := by
      refine convexHull_min ?_ (convex_halfSpace_le hlin _)
      rintro z (rfl | ⟨i, rfl⟩)
      · simpa using hCpos.le
      · exact hle _
    exact hbound hy
  · obtain ⟨j, hj⟩ := hex
    rw [← hj]
    exact NRR.Geometry.ConvexBody.inner_le_supportFunction _ (vtx_mem_polySet j)

/-- The width of the polygon is the range of the linear functional over its vertices. -/
theorem widthFunction_polyBody (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {u : Point2} (hu : u ≠ 0) {M N : ℝ}
    (hMle : ∀ j : ℤ, (inner ℝ (vtx K A j) u : ℝ) ≤ M) (hMex : ∃ j : ℤ, (inner ℝ (vtx K A j) u :
      ℝ) = M)
    (hNle : ∀ j : ℤ, N ≤ (inner ℝ (vtx K A j) u : ℝ)) (hNex : ∃ j : ℤ, (inner ℝ (vtx K A j) u :
      ℝ) = N) :
    NRR.Geometry.ConvexBody.widthFunction (polyBody K A h0) u = M - N := by
  rw [NRR.Geometry.ConvexBody.widthFunction_def,
    supportFunction_polyBody h0 hu hMle hMex,
    supportFunction_polyBody h0 (neg_ne_zero.2 hu) (C := -N)
      (fun j => by rw [inner_neg_right]; linarith [hNle j])
      (by obtain ⟨j, hj⟩ := hNex; exact ⟨j, by rw [inner_neg_right, hj]⟩)]
  ring

/-! ### Unimodality of the vertex values -/

/-- Two up-crossings of a positive level within one period are impossible. -/
private theorem no_two_upcrossings (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {n : Point2} {s : ℝ} (hs : 0 < s) {j k : ℤ} (hjk : j < k) (hkm : k < j + A.m)
    (hj : (inner ℝ (vtx K A j) n : ℝ) ≤ s) (hj' : s < (inner ℝ (vtx K A (j + 1)) n : ℝ))
    (hk : (inner ℝ (vtx K A k) n : ℝ) ≤ s) (hk' : s < (inner ℝ (vtx K A (k + 1)) n : ℝ)) :
    False := by
  have hjk1 : j + 1 < k := by
    rcases eq_or_lt_of_le (show j + 1 ≤ k by omega) with h | h
    · rw [← h] at hk; linarith
    · exact h
  by_cases hspread : A.θ (k + 1) - A.θ (j + 1) ≤ Real.pi
  · have hmid := inner_vtx_gt_of_between' h0 hs (j := j + 1) (i := k) (k := k + 1)
      hjk1 (by omega) hspread hj' hk'.le
    linarith
  · push Not at hspread
    have hk1m : k + 1 < j + A.m := by
      rcases eq_or_lt_of_le (show k + 1 ≤ j + A.m by omega) with h | h
      · exfalso
        have hv : vtx K A (k + 1) = vtx K A j := by rw [h]; exact vtx_periodic j
        rw [hv] at hk'
        linarith
      · exact h
    have hshort : A.θ (j + 1 + A.m) - A.θ (k + 1) ≤ Real.pi := by
      have hp := A.period (j + 1)
      linarith
    have hend : s ≤ (inner ℝ (vtx K A (j + 1 + A.m)) n : ℝ) := by
      rw [vtx_periodic (j + 1)]; linarith
    have hmid := inner_vtx_gt_of_between' h0 hs (j := k + 1) (i := j + A.m) (k := j + 1 + A.m)
      hk1m (by omega) hshort hk' hend
    rw [vtx_periodic j] at hmid
    linarith

/-- Two down-crossings of a positive level within one period are impossible. -/
private theorem no_two_downcrossings (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {n : Point2} {s : ℝ} (hs : 0 < s) {j k : ℤ} (hjk : j < k) (hkm : k < j + A.m)
    (hj : s ≤ (inner ℝ (vtx K A j) n : ℝ)) (hj' : (inner ℝ (vtx K A (j + 1)) n : ℝ) < s)
    (hk : s ≤ (inner ℝ (vtx K A k) n : ℝ)) (hk' : (inner ℝ (vtx K A (k + 1)) n : ℝ) < s) :
    False := by
  have hjk1 : j + 1 < k := by
    rcases eq_or_lt_of_le (show j + 1 ≤ k by omega) with h | h
    · rw [← h] at hk; linarith
    · exact h
  by_cases hspread : A.θ k - A.θ j ≤ Real.pi
  · have hmid := inner_vtx_ge_of_between h0 hs (j := j) (i := j + 1) (k := k)
      (by omega) hjk1 hspread hj hk
    linarith
  · push Not at hspread
    have hshort : A.θ (j + A.m) - A.θ k ≤ Real.pi := by
      have hp := A.period j
      linarith
    rcases eq_or_lt_of_le (show k + 1 ≤ j + A.m by omega) with h | h
    · have hv : vtx K A (k + 1) = vtx K A j := by rw [h]; exact vtx_periodic j
      rw [hv] at hk'
      linarith
    · have hend : s ≤ (inner ℝ (vtx K A (j + A.m)) n : ℝ) := by
        rw [vtx_periodic j]; exact hj
      have hmid := inner_vtx_ge_of_between h0 hs (j := k) (i := k + 1) (k := j + A.m)
        (by omega) h hshort hk hend
      linarith

/-- **At most one up-crossing per period.** -/
theorem upcrossing_unique (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {u : Point2} {t : ℝ} (ht : t ≠ 0) {j k : ℤ}
    (hj : (inner ℝ (vtx K A j) u : ℝ) ≤ t) (hj' : t < (inner ℝ (vtx K A (j + 1)) u : ℝ))
    (hk : (inner ℝ (vtx K A k) u : ℝ) ≤ t) (hk' : t < (inner ℝ (vtx K A (k + 1)) u : ℝ)) :
    ∃ q : ℤ, k = j + q * A.m := by
  have hmZ : (0 : ℤ) < A.m := by exact_mod_cast A.m_pos
  rcases eq_or_ne ((k - j) % A.m) 0 with hr | hr
  · exact ⟨(k - j) / A.m, by
      have := Int.emod_add_ediv_mul (k - j) (A.m : ℤ)
      omega⟩
  exfalso
  set k' : ℤ := j + (k - j) % A.m with hk'def
  have hrnn : 0 ≤ (k - j) % A.m := Int.emod_nonneg _ (by omega)
  have hrlt : (k - j) % A.m < A.m := Int.emod_lt_of_pos _ hmZ
  have hjk' : j < k' := by omega
  have hk'm : k' < j + A.m := by omega
  have hvk : vtx K A k' = vtx K A k := by
    have hsplit : k = k' + ((k - j) / A.m) * A.m := by
      have := Int.emod_add_ediv_mul (k - j) (A.m : ℤ)
      omega
    conv_rhs => rw [hsplit]
    exact (vtx_periodic_zsmul _ _).symm
  have hvk1 : vtx K A (k' + 1) = vtx K A (k + 1) := by
    have hsplit : k + 1 = (k' + 1) + ((k - j) / A.m) * A.m := by
      have := Int.emod_add_ediv_mul (k - j) (A.m : ℤ)
      omega
    conv_rhs => rw [hsplit]
    exact (vtx_periodic_zsmul _ _).symm
  rw [← hvk] at hk
  rw [← hvk1] at hk'
  rcases lt_trichotomy t 0 with htneg | htzero | htpos
  · refine no_two_downcrossings h0 (n := -u) (s := -t) (by linarith) hjk' hk'm ?_ ?_ ?_ ?_
    · rw [inner_neg_right]; linarith
    · rw [inner_neg_right]; linarith
    · rw [inner_neg_right]; linarith
    · rw [inner_neg_right]; linarith
  · exact ht htzero
  · exact no_two_upcrossings h0 (n := u) (s := t) htpos hjk' hk'm hj hj' hk hk'

/-- **Projection-variation identity.** -/
theorem sum_abs_inner_edge (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {u : Point2} (hu : u ≠ 0) :
    ∑ j ∈ Finset.range A.m,
        |(inner ℝ (vtx K A ((j : ℤ) + 1) - vtx K A (j : ℤ)) u : ℝ)|
      = 2 * NRR.Geometry.ConvexBody.widthFunction (polyBody K A h0) u := by
  obtain ⟨jM, hjM⟩ := exists_max_vtx K A u
  obtain ⟨jN, hjN⟩ := exists_max_vtx K A (-u)
  have hNle : ∀ k : ℤ, (inner ℝ (vtx K A jN) u : ℝ) ≤ (inner ℝ (vtx K A k) u : ℝ) := by
    intro k
    have h := hjN k
    rw [inner_neg_right, inner_neg_right] at h
    linarith
  rw [widthFunction_polyBody h0 hu (M := (inner ℝ (vtx K A jM) u : ℝ))
      (N := (inner ℝ (vtx K A jN) u : ℝ)) hjM ⟨jM, rfl⟩ hNle ⟨jN, rfl⟩]
  have hper : ∀ j : ℤ, (inner ℝ (vtx K A (j + A.m)) u : ℝ) = (inner ℝ (vtx K A j) u : ℝ) := by
    intro j; rw [vtx_periodic]
  have hmain := cyclic_sum_abs_sub (m := A.m) A.m_pos
    (fun j : ℤ => (inner ℝ (vtx K A j) u : ℝ)) hper
    (fun t ht j k hj hj' hk hk' => upcrossing_unique h0 ht hj hj' hk hk')
    (M := (inner ℝ (vtx K A jM) u : ℝ)) (N := (inner ℝ (vtx K A jN) u : ℝ))
    hjM ⟨jM, rfl⟩ hNle ⟨jN, rfl⟩
  rw [← hmain]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_sub_left]

/-- Each edge projection is interval integrable. -/
private theorem intervalIntegrable_abs_inner (e : Point2) :
    IntervalIntegrable (fun θ : ℝ => |(inner ℝ e (circleVec θ) : ℝ)|) volume 0 (2 * Real.pi) :=
  (((continuous_const.inner continuous_circleVec)).abs).intervalIntegrable _ _

/-! ### The Cauchy perimeter of the polygon -/

/-- **Cauchy perimeter of the inscribed polygon.** -/
theorem cPerimeter_polyBody (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    cPerimeter (polyBody K A h0) = ENNReal.ofReal (edgeLengthSum K A) := by
  rw [cPerimeter, NRR.Geometry.ConvexBody.perimeter_def, NRR.Geometry.planarPerimeter_def]
  congr 1
  have hcv : ∀ θ : ℝ, circleVec θ ≠ 0 := by
    intro θ hcon
    have := norm_circleVec θ
    rw [hcon, norm_zero] at this
    norm_num at this
  have hw : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      NRR.Geometry.ConvexBody.widthFunction (polyBody K A h0) (circleVec θ)
        = (1 / 2 : ℝ) * ∑ j ∈ Finset.range A.m,
            |(inner ℝ (vtx K A ((j : ℤ) + 1) - vtx K A (j : ℤ)) (circleVec θ) : ℝ)| := by
    intro θ _
    rw [sum_abs_inner_edge h0 (hcv θ)]
    ring
  rw [intervalIntegral.integral_congr hw, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum
      (fun i _ => intervalIntegrable_abs_inner _)]
  have hterm : ∀ j ∈ Finset.range A.m,
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          |(inner ℝ (vtx K A ((j : ℤ) + 1) - vtx K A (j : ℤ)) (circleVec θ) : ℝ)|)
        = 4 * dist (vtx K A (j : ℤ)) (vtx K A ((j : ℤ) + 1)) := by
    intro j _
    rw [integral_abs_inner_circleVec, dist_eq_norm, norm_sub_rev]
  rw [Finset.sum_congr rfl hterm, edgeLengthSum, ← Finset.mul_sum]
  ring

/-- **Cauchy–Crofton for the inscribed polygon.** -/
theorem polygon_hPerimeter_eq_cPerimeter (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    hPerimeter (polyBody K A h0) = cPerimeter (polyBody K A h0) := by
  rw [hPerimeter_polyBody h0, cPerimeter_polyBody h0]

end HumanVerification.CauchyCrofton
