/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPositiveCorrelation

/-!
# Finite central-third localization at one dyadic scale

This is the exact finite-support version of the three-shift decomposition in
KL18 (3.1).  Intervals of length `L` are chosen so that their central thirds
are the consecutive half-open tiles of length `L/3`.  Hence a compactly
supported input is exactly the sum of finitely many central-third
restrictions, with no overlap and no boundary exceptional set.

Grouping the tile index modulo three recovers the three shifted grids.  The
cross-scale nesting of each such group is left to the subsequent grid module;
the results here close the finite, fixed-scale identity used before that step.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyShiftedLocalization


noncomputable section

/-- The parent whose central third is the `n`th consecutive tile of width
`L/3`. -/
def centralThirdTileParent (L : ℝ) (hL : 0 < L) (n : ℤ) : RealInterval where
  left := ((n : ℝ) - 1) * (L / 3)
  right := ((n : ℝ) + 2) * (L / 3)
  left_lt_right := by nlinarith

theorem centralThirdTileParent_length (L : ℝ) (hL : 0 < L) (n : ℤ) :
    (centralThirdTileParent L hL n).length = L := by
  unfold centralThirdTileParent RealInterval.length
  ring

theorem centralThirdTileParent_centralThird (L : ℝ) (hL : 0 < L) (n : ℤ) :
    (centralThirdTileParent L hL n).centralThird =
      Ioc ((n : ℝ) * (L / 3)) (((n : ℝ) + 1) * (L / 3)) := by
  unfold RealInterval.centralThird centralThirdTileParent
  congr 1 <;> ring

/-- The central thirds of distinct tile parents are literally disjoint. -/
theorem centralThirdTileParents_pairwiseDisjoint (L : ℝ) (hL : 0 < L) :
    Pairwise (Disjoint on fun n : ℤ ↦ (centralThirdTileParent L hL n).centralThird) := by
  intro n m hnm
  apply Set.disjoint_left.2
  intro x hxn hxm
  change x ∈ (centralThirdTileParent L hL n).centralThird at hxn
  change x ∈ (centralThirdTileParent L hL m).centralThird at hxm
  rw [centralThirdTileParent_centralThird] at hxn hxm
  have hthird : 0 < L / 3 := by positivity
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hstep : n + 1 ≤ m := (Int.add_one_le_iff).2 hlt
    have hcast : ((n : ℝ) + 1) * (L / 3) ≤ (m : ℝ) * (L / 3) := by
      apply mul_le_mul_of_nonneg_right _ hthird.le
      exact_mod_cast hstep
    exact (not_lt_of_ge (hxn.2.trans hcast)) hxm.1
  · have hstep : m + 1 ≤ n := (Int.add_one_le_iff).2 hgt
    have hcast : ((m : ℝ) + 1) * (L / 3) ≤ (n : ℝ) * (L / 3) := by
      apply mul_le_mul_of_nonneg_right _ hthird.le
      exact_mod_cast hstep
    exact (not_lt_of_ge (hxm.2.trans hcast)) hxn.1

/-- Every real point belongs to exactly one central-third tile. -/
theorem existsUnique_mem_centralThirdTileParent (L : ℝ) (hL : 0 < L) (x : ℝ) :
    ∃! n : ℤ, x ∈ (centralThirdTileParent L hL n).centralThird := by
  let h : ℝ := L / 3
  have hh : 0 < h := by dsimp [h]; positivity
  let n : ℤ := ⌈x / h⌉ - 1
  have hlower : ((n : ℝ) * h) < x := by
    have hc := Int.ceil_lt_add_one (x / h)
    have hc' : ((⌈x / h⌉ - 1 : ℤ) : ℝ) < x / h := by
      push_cast
      linarith
    exact (lt_div_iff₀ hh).1 hc'
  have hupper : x ≤ ((n : ℝ) + 1) * h := by
    have hc := Int.le_ceil (x / h)
    have hc' : x / h ≤ ((n : ℝ) + 1) := by
      dsimp [n]
      push_cast
      simpa only [sub_add_cancel] using hc
    exact (div_le_iff₀ hh).1 hc'
  refine ⟨n, ?_, ?_⟩
  · change x ∈ (centralThirdTileParent L hL n).centralThird
    rw [centralThirdTileParent_centralThird]
    simpa only [h] using ⟨hlower, hupper⟩
  · intro m hxm
    by_contra hmn
    have hd := centralThirdTileParents_pairwiseDisjoint L hL hmn
    exact Set.disjoint_left.1 hd hxm (by
      change x ∈ (centralThirdTileParent L hL n).centralThird
      rw [centralThirdTileParent_centralThird]
      simpa only [h] using ⟨hlower, hupper⟩)

/-- A finite disjoint family of central thirds which covers the support of
`f` reconstructs `f` exactly, including all interval endpoints. -/
theorem krauseLaceyFixedScaleInput_eq_of_support_subset
    (S : Finset RealInterval) (f : ℝ → ℂ)
    (hdisj : Set.Pairwise (↑S : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.centralThird))
    (hcover : Function.support f ⊆ ⋃ I ∈ S, I.centralThird) :
    krauseLaceyFixedScaleInput S f = f := by
  classical
  funext x
  by_cases hx : f x = 0
  · simp [krauseLaceyFixedScaleInput, Set.indicator_apply, hx]
  · have hxs : x ∈ Function.support f := hx
    rcases Set.mem_iUnion.1 (hcover hxs) with ⟨I, hxI⟩
    rcases Set.mem_iUnion.1 hxI with ⟨hIS, hxI⟩
    unfold krauseLaceyFixedScaleInput
    rw [Finset.sum_eq_single I]
    · exact Set.indicator_of_mem hxI f
    · intro J hJS hJI
      have hd := hdisj hIS hJS hJI.symm
      have hxJ : x ∉ J.centralThird := fun hxJ ↦ Set.disjoint_left.1 hd hxI hxJ
      simp [hxJ]
    · intro hn
      exact (hn hIS).elim

/-- The tile-parent construction is injective, so it can be mapped into a
finite interval family without quotienting distinct cells. -/
def centralThirdTileParentEmbedding (L : ℝ) (hL : 0 < L) : ℤ ↪ RealInterval where
  toFun := centralThirdTileParent L hL
  inj' := by
    intro n m hnm
    have hleft := congrArg RealInterval.left hnm
    dsimp [centralThirdTileParent] at hleft
    have hthird : L / 3 ≠ 0 := ne_of_gt (by positivity)
    apply_fun fun z : ℝ ↦ z / (L / 3) at hleft
    simp only [mul_div_cancel_right₀ _ hthird] at hleft
    exact_mod_cast (sub_left_inj.mp hleft)

/-- Every bounded compact-support input admits an exact finite KL18
central-third decomposition at an arbitrary positive scale. -/
theorem exists_finite_centralThird_localization
    (f : L0Infinity) (L : ℝ) (hL : 0 < L) :
    ∃ S : Finset RealInterval,
      (∀ I ∈ S, I.length = L) ∧
      Set.Pairwise (↑S : Set RealInterval)
        (Disjoint on fun I : RealInterval ↦ I.centralThird) ∧
      krauseLaceyFixedScaleInput S f = f := by
  obtain ⟨R, hRpos, hR⟩ := f.hasCompactSupport_toFun.isBounded.exists_pos_norm_le
  let h : ℝ := L / 3
  have hh : 0 < h := by dsimp [h]; positivity
  let a : ℤ := ⌊-R / h⌋ - 1
  let b : ℤ := ⌈R / h⌉
  let E := centralThirdTileParentEmbedding L hL
  let S : Finset RealInterval := (Finset.Icc a b).map E
  refine ⟨S, ?_, ?_, ?_⟩
  · intro I hIS
    rcases Finset.mem_map.1 hIS with ⟨n, hn, rfl⟩
    exact centralThirdTileParent_length L hL n
  · intro I hIS J hJS hIJ
    rcases Finset.mem_map.1 hIS with ⟨n, hn, rfl⟩
    rcases Finset.mem_map.1 hJS with ⟨m, hm, rfl⟩
    apply centralThirdTileParents_pairwiseDisjoint L hL
    intro hnm
    apply hIJ
    subst m
    rfl
  · apply krauseLaceyFixedScaleInput_eq_of_support_subset S f
      (by
        intro I hIS J hJS hIJ
        rcases Finset.mem_map.1 hIS with ⟨n, hn, rfl⟩
        rcases Finset.mem_map.1 hJS with ⟨m, hm, rfl⟩
        apply centralThirdTileParents_pairwiseDisjoint L hL
        intro hnm
        apply hIJ
        subst m
        rfl)
    intro x hx
    obtain ⟨n, hxn, hnunique⟩ := existsUnique_mem_centralThirdTileParent L hL x
    have hxR : ‖x‖ ≤ R := hR x (subset_tsupport f hx)
    have hxlo : -R ≤ x := by simpa [Real.norm_eq_abs] using (abs_le.1 hxR).1
    have hxhi : x ≤ R := by simpa [Real.norm_eq_abs] using (abs_le.1 hxR).2
    have hratio_lo : -R / h ≤ x / h := (div_le_div_iff_of_pos_right hh).2 hxlo
    have hratio_hi : x / h ≤ R / h := (div_le_div_iff_of_pos_right hh).2 hxhi
    have hfloor : ⌊-R / h⌋ ≤ ⌈x / h⌉ :=
      (Int.floor_mono hratio_lo).trans (Int.floor_le_ceil (x / h))
    have hceil : ⌈x / h⌉ ≤ ⌈R / h⌉ := Int.ceil_mono hratio_hi
    have hnformula : n = ⌈x / h⌉ - 1 := by
      symm
      apply hnunique
      rw [centralThirdTileParent_centralThird]
      have hc1 := Int.ceil_lt_add_one (x / h)
      have hc2 := Int.le_ceil (x / h)
      constructor
      · change (((⌈x / h⌉ - 1 : ℤ) : ℝ) * (L / 3)) < x
        change (((⌈x / h⌉ - 1 : ℤ) : ℝ) * h) < x
        apply (lt_div_iff₀ hh).1
        push_cast
        linarith
      · change x ≤ ((((⌈x / h⌉ - 1 : ℤ) : ℝ) + 1) * (L / 3))
        change x ≤ ((((⌈x / h⌉ - 1 : ℤ) : ℝ) + 1) * h)
        apply (div_le_iff₀ hh).1
        push_cast
        simpa only [sub_add_cancel] using hc2
    have hnmem : n ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc, hnformula]
      dsimp [a, b]
      omega
    apply Set.mem_iUnion.2 ⟨centralThirdTileParent L hL n, ?_⟩
    apply Set.mem_iUnion.2 ⟨Finset.mem_map.2 ⟨n, hnmem, rfl⟩, hxn⟩

/-- Consequently the finite localized sum is the genuine positive-half
quadratic convolution at that scale. -/
theorem exists_finite_localizedSum_eq_globalConvolution
    (f : L0Infinity) (j : ℤ) :
    ∃ S : Finset RealInterval,
      (∀ I ∈ S, I.length = (2 : ℝ) ^ (j + 2)) ∧
      Set.Pairwise (↑S : Set RealInterval)
        (Disjoint on fun I : RealInterval ↦ I.centralThird) ∧
      ∀ x,
        krauseLaceyFixedScaleLocalizedSum j S f x =
          ∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) * f t := by
  have hscale : 0 < (2 : ℝ) ^ (j + 2) := by positivity
  obtain ⟨S, hlen, hdisj, hinput⟩ :=
    exists_finite_centralThird_localization f ((2 : ℝ) ^ (j + 2)) hscale
  refine ⟨S, hlen, hdisj, fun x ↦ ?_⟩
  rcases f.bounded_toFun with ⟨C, hC⟩
  have hf2 : MemLp f 2 :=
    f.hasCompactSupport_toFun.memLp_of_bound
      f.measurable_toFun.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  calc
    krauseLaceyFixedScaleLocalizedSum j S f x =
        ∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
          krauseLaceyFixedScaleInput S f t :=
      krauseLaceyFixedScaleLocalizedSum_eq_convolution j S hf2 x
    _ = _ := by rw [hinput]


end
end KrauseLaceyShiftedLocalization
end QuadraticCarleson
