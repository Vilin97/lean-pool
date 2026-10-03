/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftTreeInterface

/-!
# Finite compact-support localization into the three shifted grids

At a fixed represented scale, every consecutive central-third tile has a
unique address in one of the three translated dyadic grids. This module
turns that global partition into three finite subfamilies for a compactly
supported input and proves exact reconstruction, including endpoints.
-/

@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid

open CalderonZygmundDyadicStopping
open KrauseLaceyShiftedLocalization


noncomputable
section

/-- Classical equality for interval indices in this finite stopping construction. -/
local instance : DecidableEq RealInterval := Classical.decEq _

/-- The unique shifted-grid address chosen for a consecutive tile number. -/
noncomputable def finiteShiftGridAddress (depth : ℕ) (n : ℤ) : Fin 3 × ℤ :=
  let h := finiteShiftGridTileIndex_surjective depth n
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

theorem finiteShiftGridAddress_index (depth : ℕ) (n : ℤ) :
    finiteShiftGridTileIndex (finiteShiftGridAddress depth n).1 depth
      (finiteShiftGridAddress depth n).2 = n := by
  exact Classical.choose_spec
    (Classical.choose_spec (finiteShiftGridTileIndex_surjective depth n))

/-- The chosen address represents literally the original consecutive tile
parent, not merely an interval equal almost everywhere. -/
theorem finiteShiftGridAddress_interval
    (topScale : ℤ) (depth : ℕ) (n : ℤ) :
    finiteShiftGridInterval topScale (finiteShiftGridAddress depth n).1 depth
        (finiteShiftGridAddress depth n).2 =
      centralThirdTileParent
        (dyadicLength (shiftedGridRootLength topScale) depth)
        (dyadicLength_pos (shiftedGridRootLength_pos topScale) depth) n := by
  rw [finiteShiftGridInterval_eq_centralThirdTileParent,
    finiteShiftGridAddress_index]

/-- The finite interval family attached to a finite collection of
consecutive tile numbers. -/
noncomputable def finiteThreeShiftFamily
    (topScale : ℤ) (depth : ℕ) (E : Finset ℤ) : Finset RealInterval := by
  classical
  exact E.image fun n ↦
    finiteShiftGridInterval topScale (finiteShiftGridAddress depth n).1 depth
      (finiteShiftGridAddress depth n).2

/-- The part of a finite tile family lying in one specified shifted grid. -/
noncomputable def finiteOneShiftFamily
    (topScale : ℤ) (depth : ℕ) (E : Finset ℤ) (shift : Fin 3) :
    Finset RealInterval := by
  classical
  exact (E.filter fun n ↦ (finiteShiftGridAddress depth n).1 = shift).image fun n ↦
    finiteShiftGridInterval topScale shift depth (finiteShiftGridAddress depth n).2

theorem mem_finiteOneShiftFamily
    {topScale : ℤ} {depth : ℕ} {E : Finset ℤ} {shift : Fin 3}
    {I : RealInterval} (hI : I ∈ finiteOneShiftFamily topScale depth E shift) :
    ∃ n ∈ E, (finiteShiftGridAddress depth n).1 = shift ∧
      I = finiteShiftGridInterval topScale shift depth
        (finiteShiftGridAddress depth n).2 := by
  classical
  rcases Finset.mem_image.mp hI with ⟨n, hn, rfl⟩
  have hn' := Finset.mem_filter.mp hn
  exact ⟨n, hn'.1, hn'.2, rfl⟩

/-- The union of the three finite subfamilies is exactly the original finite
tile family. -/
theorem finiteThreeShiftFamily_eq_biUnion
    (topScale : ℤ) (depth : ℕ) (E : Finset ℤ) :
    finiteThreeShiftFamily topScale depth E =
      Finset.univ.biUnion (finiteOneShiftFamily topScale depth E) := by
  classical
  ext I
  constructor
  · intro hI
    rcases Finset.mem_image.mp hI with ⟨n, hn, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(finiteShiftGridAddress depth n).1, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨n, Finset.mem_filter.mpr ⟨hn, rfl⟩, ?_⟩
    rfl
  · intro hI
    rcases Finset.mem_biUnion.mp hI with ⟨shift, _, hshift⟩
    rcases mem_finiteOneShiftFamily hshift with ⟨n, hn, hs, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨n, hn, ?_⟩
    rw [hs]

/-- Across all three grids, the selected central thirds remain literally
pairwise disjoint. -/
theorem finiteThreeShiftFamily_pairwiseDisjoint
    (topScale : ℤ) (depth : ℕ) (E : Finset ℤ) :
    Set.Pairwise (↑(finiteThreeShiftFamily topScale depth E) : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.centralThird) := by
  classical
  intro I hI J hJ hIJ
  rcases Finset.mem_image.mp hI with ⟨n, _, rfl⟩
  rcases Finset.mem_image.mp hJ with ⟨m, _, rfl⟩
  apply finiteShiftGridCentralThird_pairwiseDisjoint topScale depth
  intro hp
  apply hIJ
  rw [hp]

/-- If the selected tile indices cover the support, the three-grid family
reconstructs the input exactly. -/
theorem finiteThreeShiftFixedScaleInput_eq_of_support_cover
    (topScale : ℤ) (depth : ℕ) (E : Finset ℤ) (f : ℝ → ℂ)
    (hcover : Function.support f ⊆ ⋃ n ∈ E,
      (centralThirdTileParent
        (dyadicLength (shiftedGridRootLength topScale) depth)
        (dyadicLength_pos (shiftedGridRootLength_pos topScale) depth) n).centralThird) :
    krauseLaceyFixedScaleInput (finiteThreeShiftFamily topScale depth E) f = f := by
  apply krauseLaceyFixedScaleInput_eq_of_support_subset
    (finiteThreeShiftFamily topScale depth E) f
    (finiteThreeShiftFamily_pairwiseDisjoint topScale depth E)
  intro x hx
  rcases Set.mem_iUnion.mp (hcover hx) with ⟨n, hxn⟩
  rcases Set.mem_iUnion.mp hxn with ⟨hn, hxn⟩
  apply Set.mem_iUnion.mpr
  refine ⟨finiteShiftGridInterval topScale (finiteShiftGridAddress depth n).1 depth
    (finiteShiftGridAddress depth n).2, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨Finset.mem_image.mpr ⟨n, hn, rfl⟩, ?_⟩
  rw [finiteShiftGridAddress_interval]
  exact hxn

/-- Every bounded compact-support input has an exact finite localization by
actual intervals from the three shifted grids at the represented scale. -/
theorem exists_finiteThreeShiftFamily_localization
    (f : L0Infinity) (topScale : ℤ) (depth : ℕ) :
    ∃ E : Finset ℤ,
      (∀ I ∈ finiteThreeShiftFamily topScale depth E,
        I.length = dyadicLength (shiftedGridRootLength topScale) depth) ∧
      Set.Pairwise (↑(finiteThreeShiftFamily topScale depth E) : Set RealInterval)
        (Disjoint on fun I : RealInterval ↦ I.centralThird) ∧
      krauseLaceyFixedScaleInput (finiteThreeShiftFamily topScale depth E) f = f := by
  obtain ⟨R, hRpos, hR⟩ := f.hasCompactSupport_toFun.isBounded.exists_pos_norm_le
  let L := dyadicLength (shiftedGridRootLength topScale) depth
  have hL : 0 < L := dyadicLength_pos (shiftedGridRootLength_pos topScale) depth
  let h : ℝ := L / 3
  have hh : 0 < h := by dsimp [h]; positivity
  let a : ℤ := ⌊-R / h⌋ - 1
  let b : ℤ := ⌈R / h⌉
  let E : Finset ℤ := Finset.Icc a b
  have hcover : Function.support (f : ℝ → ℂ) ⊆ ⋃ n ∈ E,
      (centralThirdTileParent L hL n).centralThird := by
    intro x hx
    obtain ⟨n, hxn, hnunique⟩ := existsUnique_mem_centralThirdTileParent L hL x
    have hxR : ‖x‖ ≤ R := hR x (subset_tsupport f hx)
    have hxlo : -R ≤ x := by
      simpa [Real.norm_eq_abs] using (abs_le.mp hxR).1
    have hxhi : x ≤ R := by
      simpa [Real.norm_eq_abs] using (abs_le.mp hxR).2
    have hratio_lo : -R / h ≤ x / h :=
      (div_le_div_iff_of_pos_right hh).mpr hxlo
    have hratio_hi : x / h ≤ R / h :=
      (div_le_div_iff_of_pos_right hh).mpr hxhi
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
        have hc' : ((⌈x / h⌉ - 1 : ℤ) : ℝ) < x / h := by
          push_cast
          linarith
        exact (lt_div_iff₀ hh).mp hc'
      · change x ≤ ((((⌈x / h⌉ - 1 : ℤ) : ℝ) + 1) * (L / 3))
        change x ≤ ((((⌈x / h⌉ - 1 : ℤ) : ℝ) + 1) * h)
        have hc' : x / h ≤ (((⌈x / h⌉ - 1 : ℤ) : ℝ) + 1) := by
          push_cast
          simpa only [sub_add_cancel] using hc2
        exact (div_le_iff₀ hh).mp hc'
    have hnmem : n ∈ E := by
      rw [show E = Finset.Icc a b by rfl, Finset.mem_Icc, hnformula]
      dsimp [a, b]
      omega
    apply Set.mem_iUnion.mpr
    exact ⟨n, Set.mem_iUnion.mpr ⟨hnmem, hxn⟩⟩
  refine ⟨E, ?_, finiteThreeShiftFamily_pairwiseDisjoint topScale depth E, ?_⟩
  · intro I hI
    rcases Finset.mem_image.mp hI with ⟨n, _, rfl⟩
    exact finiteShiftGridInterval_length topScale
      (finiteShiftGridAddress depth n).1 depth (finiteShiftGridAddress depth n).2
  · apply finiteThreeShiftFixedScaleInput_eq_of_support_cover topScale depth E f
    simpa only [L] using hcover

/-- Exact fixed-scale global convolution split into the three finite shifted
grid families. This is the finite-support form of KL18 display (3.1). -/
theorem exists_finite_threeShift_localizedSum_eq_globalConvolution
    (f : L0Infinity) (topScale : ℤ) (depth : ℕ) :
    ∃ G : Fin 3 → Finset RealInterval,
      (∀ shift, ∀ I ∈ G shift, ∃ q : ℤ,
        I = finiteShiftGridInterval topScale shift depth q) ∧
      Set.Pairwise (↑(Finset.univ.biUnion G) : Set RealInterval)
        (Disjoint on fun I : RealInterval ↦ I.centralThird) ∧
      ∀ x,
        krauseLaceyFixedScaleLocalizedSum (topScale - (depth : ℤ))
            (Finset.univ.biUnion G) f x =
          ∫ t, annularQuadraticKernel
            (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 (x - t) * f t := by
  obtain ⟨E, _, hdisj, hinput⟩ :=
    exists_finiteThreeShiftFamily_localization f topScale depth
  let G : Fin 3 → Finset RealInterval := finiteOneShiftFamily topScale depth E
  have hUnion : finiteThreeShiftFamily topScale depth E = Finset.univ.biUnion G :=
    finiteThreeShiftFamily_eq_biUnion topScale depth E
  have hinputUnion : krauseLaceyFixedScaleInput (Finset.univ.biUnion G) f = f := by
    rw [← hUnion]
    exact hinput
  refine ⟨G, ?_, ?_, ?_⟩
  · intro shift I hI
    rcases mem_finiteOneShiftFamily hI with ⟨n, _, _, rfl⟩
    exact ⟨(finiteShiftGridAddress depth n).2, rfl⟩
  · rw [← hUnion]
    exact hdisj
  · intro x
    rcases f.bounded_toFun with ⟨C, hC⟩
    have hf2 : MemLp f 2 :=
      f.hasCompactSupport_toFun.memLp_of_bound
        f.measurable_toFun.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    calc
      krauseLaceyFixedScaleLocalizedSum (topScale - (depth : ℤ))
          (Finset.univ.biUnion G) f x =
          ∫ t, annularQuadraticKernel
            (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 (x - t) *
              krauseLaceyFixedScaleInput (Finset.univ.biUnion G) f t :=
        krauseLaceyFixedScaleLocalizedSum_eq_convolution
          (topScale - (depth : ℤ)) (Finset.univ.biUnion G) hf2 x
      _ = _ := by rw [hinputUnion]


end


end KrauseLaceyThreeShiftGrid
end QuadraticCarleson
