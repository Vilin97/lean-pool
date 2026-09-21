/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.NearestProjection

/-!
# Monotonicity of the Hausdorff perimeter

For compact convex bodies `K ⊆ L` in the plane, `μH[1] (frontier K) ≤ μH[1] (frontier L)`.

The proof uses the nearest-point projection `nearestPoint K`, which is `1`-Lipschitz: every
boundary point of `K` is the image of a boundary point of `L` (push the boundary point of `K`
outwards along a supporting direction until it hits the boundary of `L`), so
`frontier K ⊆ nearestPoint K '' frontier L`, and Lipschitz maps do not increase the
one-dimensional Hausdorff measure.
-/

open Set MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace HumanVerification.CauchyCrofton

/-- A supporting direction at a boundary point of a convex body. -/
theorem exists_supporting_direction (K : Body) {x : Point2} (hx : x ∈ frontier (K : Set Point2)) :
    ∃ n : Point2, n ≠ 0 ∧ ∀ y ∈ (K : Set Point2), (inner ℝ y n : ℝ) ≤ (inner ℝ x n : ℝ) := by
  have hxnot : x ∉ interior (K : Set Point2) := by
    rw [K.isCompact.isClosed.frontier_eq] at hx
    exact hx.2
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (s := interior (K : Set Point2))
    (K.convex.interior) isOpen_interior hxnot
  set n : Point2 := (InnerProductSpace.toDual ℝ Point2).symm f with hn
  have hfe : (InnerProductSpace.toDual ℝ Point2) n = f := by
    rw [hn, LinearIsometryEquiv.apply_symm_apply]
  have hfn : ∀ y : Point2, f y = (inner ℝ y n : ℝ) := by
    intro y
    rw [← hfe, InnerProductSpace.toDual_apply_apply, real_inner_comm]
  obtain ⟨z, hz⟩ := K.interior_nonempty
  refine ⟨n, ?_, ?_⟩
  · intro hn0
    have hlt := hf z hz
    rw [hfn, hfn, hn0] at hlt
    simp at hlt
  · intro y hy
    by_contra hcon
    push Not at hcon
    have hfz : (inner ℝ z n : ℝ) < (inner ℝ x n : ℝ) := by
      have := hf z hz
      rwa [hfn, hfn] at this
    set fz : ℝ := (inner ℝ z n : ℝ)
    set fx : ℝ := (inner ℝ x n : ℝ)
    set fy : ℝ := (inner ℝ y n : ℝ)
    have hzy : fz < fy := lt_trans hfz hcon
    set τ : ℝ := (fx - fz) / (fy - fz) with hτ
    have hτlt : τ < 1 := by
      rw [hτ, div_lt_one (by linarith)]
      linarith
    set t : ℝ := (max τ 0 + 1) / 2 with ht
    have htτ : τ < t := by
      rw [ht]
      have h1 : τ ≤ max τ 0 := le_max_left _ _
      have h2 : max τ 0 < 1 := max_lt hτlt one_pos
      linarith
    have ht0 : 0 ≤ t := by
      rw [ht]
      have : (0:ℝ) ≤ max τ 0 := le_max_right _ _
      linarith
    have ht1 : t < 1 := by
      rw [ht]
      have : max τ 0 < 1 := max_lt hτlt one_pos
      linarith
    have hmem : (1 - t) • z + t • y ∈ interior (K : Set Point2) :=
      K.convex.combo_interior_closure_mem_interior hz (subset_closure hy)
        (by linarith) ht0 (by ring)
    have hlt := hf _ hmem
    simp only [hfn] at hlt
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at hlt
    have hgt : fx < (1 - t) * fz + t * fy := by
      rw [hτ, div_lt_iff₀ (by linarith)] at htτ
      nlinarith
    linarith

/-- A ray from a point of a compact convex body leaves it through a boundary point. -/
theorem exists_frontier_point_on_ray
    (K : Body) {a v : Point2} (ha : a ∈ (K : Set Point2)) (hv : v ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ a + t • v ∈ frontier (K : Set Point2) ∧
      ∀ s : ℝ, 0 ≤ s → a + s • v ∈ (K : Set Point2) → s ≤ t := by
  set T : Set ℝ := {t : ℝ | 0 ≤ t ∧ a + t • v ∈ (K : Set Point2)} with hT
  have hTne : T.Nonempty := ⟨0, ⟨le_refl 0, by simpa using ha⟩⟩
  have hTclosed : IsClosed T := by
    have : T = Set.Ici (0:ℝ) ∩ (fun t : ℝ => a + t • v) ⁻¹' (K : Set Point2) := by
      ext s; simp [hT, Set.mem_Ici]
    rw [this]
    exact isClosed_Ici.inter (K.isCompact.isClosed.preimage (by fun_prop))
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hTbdd : BddAbove T := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : Point2)
    refine ⟨(R + ‖a‖) / ‖v‖, fun s hs => ?_⟩
    have hmem := hR hs.2
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    have hnorm : s * ‖v‖ ≤ R + ‖a‖ := by
      have h1 : ‖s • v‖ ≤ ‖a + s • v‖ + ‖a‖ := by
        calc ‖s • v‖ = ‖(a + s • v) - a‖ := by congr 1; abel
          _ ≤ ‖a + s • v‖ + ‖a‖ := norm_sub_le _ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at h1
      linarith
    rw [le_div_iff₀ hvpos]
    exact hnorm
  set t := sSup T with htdef
  have htT : t ∈ T := hTclosed.csSup_mem hTne hTbdd
  refine ⟨t, htT.1, ?_, fun s hs0 hsK => le_csSup hTbdd ⟨hs0, hsK⟩⟩
  rw [K.isCompact.isClosed.frontier_eq]
  refine ⟨htT.2, ?_⟩
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ hint
  set s : ℝ := t + ε / (2 * ‖v‖) with hs
  have hsmem : a + s • v ∈ (K : Set Point2) := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, hs]
    have hdiff : a + (t + ε / (2 * ‖v‖)) • v - (a + t • v) = (ε / (2 * ‖v‖)) • v := by
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ε / (2 * ‖v‖))]
    have hcalc : ε / (2 * ‖v‖) * ‖v‖ = ε / 2 := by field_simp
    rw [hcalc]
    linarith
  have hspos : 0 < ε / (2 * ‖v‖) := by positivity
  have hle := le_csSup hTbdd (show s ∈ T from ⟨by rw [hs]; linarith [htT.1], hsmem⟩)
  rw [hs] at hle
  linarith

/-- Every boundary point of an inner convex body is the nearest-point image of a boundary point
of an outer convex body. -/
theorem frontier_subset_nearestPoint_image
    {K L : Body} (hKL : (K : Set Point2) ⊆ (L : Set Point2)) :
    frontier (K : Set Point2) ⊆ nearestPoint K '' frontier (L : Set Point2) := by
  intro x hx
  have hxK : x ∈ (K : Set Point2) := K.isCompact.isClosed.frontier_subset hx
  obtain ⟨n, hn, hsupp⟩ := exists_supporting_direction K hx
  obtain ⟨t, ht0, hyfront, -⟩ := exists_frontier_point_on_ray L (hKL hxK) hn
  set y : Point2 := x + t • n with hy
  refine ⟨y, hyfront, ?_⟩
  set p : Point2 := nearestPoint K y with hp
  have hpK : p ∈ (K : Set Point2) := nearestPoint_mem K y
  have h1 : (inner ℝ (y - p) (x - p) : ℝ) ≤ 0 := nearestPoint_inner_le_zero K y hxK
  have h2 : (inner ℝ (y - x) (p - x) : ℝ) ≤ 0 := by
    rw [hy]
    have hyx : x + t • n - x = t • n := by abel
    rw [hyx, real_inner_smul_left]
    have := hsupp p hpK
    have hinner : (inner ℝ n (p - x) : ℝ) = (inner ℝ p n : ℝ) - (inner ℝ x n : ℝ) := by
      rw [inner_sub_right, real_inner_comm n p, real_inner_comm n x]
    rw [hinner]
    have : (inner ℝ p n : ℝ) - (inner ℝ x n : ℝ) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos ht0 this
  have hsq : ‖x - p‖ ^ 2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq]
    have hexp : (inner ℝ (x - p) (x - p) : ℝ)
        = (inner ℝ (y - p) (x - p) : ℝ) + (inner ℝ (y - x) (p - x) : ℝ) := by
      simp only [inner_sub_left, inner_sub_right]
      ring
    rw [hexp]
    linarith
  have : ‖x - p‖ = 0 := by nlinarith [norm_nonneg (x - p)]
  have hxp : x = p := sub_eq_zero.mp (norm_eq_zero.mp this)
  exact hxp.symm

/-- **Monotonicity of the Hausdorff perimeter.** -/
theorem hPerimeter_mono {K L : Body}
    (hKL : (K : Set Point2) ⊆ (L : Set Point2)) :
    hPerimeter K ≤ hPerimeter L := by
  have himage := frontier_subset_nearestPoint_image hKL
  calc
    hPerimeter K = (μH[1] : Measure Point2) (frontier (K : Set Point2)) := rfl
    _ ≤ (μH[1] : Measure Point2)
        (nearestPoint K '' frontier (L : Set Point2)) := measure_mono himage
    _ ≤ (1 : ENNReal) ^ (1 : ℝ) *
        (μH[1] : Measure Point2) (frontier (L : Set Point2)) :=
      (lipschitz_nearestPoint K).hausdorffMeasure_image_le (by norm_num)
        (frontier (L : Set Point2))
    _ = hPerimeter L := by simp [hPerimeter]

end HumanVerification.CauchyCrofton
