/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftForest

/-!
# Exact finite multiscale action of the three shifted grids

This module records the disjointness needed to reorganize finite scale sums.
The identities are for the genuine localized pieces and retain the actual
length cutoff from the Krause--Lacey maximal partial sum.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid

open KrauseLaceyStoppingRecursion


noncomputable
section

/-- Classical equality for interval indices in this finite stopping construction. -/
local instance : DecidableEq RealInterval := Classical.decEq _

/-- Fixed-shift families from different depths cannot share an interval. -/
theorem finiteOneShiftFamily_disjoint_of_ne_depth
    (topScale : ℤ) (shift : Fin 3) {depth depth' : ℕ} (hne : depth ≠ depth')
    (E E' : Finset ℤ) :
    Disjoint (finiteOneShiftFamily topScale depth E shift)
      (finiteOneShiftFamily topScale depth' E' shift) := by
  classical
  apply Finset.disjoint_left.mpr
  intro I hI hI'
  rcases mem_finiteOneShiftFamily hI with ⟨n, _, _, hrepr⟩
  rcases mem_finiteOneShiftFamily hI' with ⟨n', _, _, hrepr'⟩
  have heq := hrepr.symm.trans hrepr'
  exact hne (finiteShiftGridInterval_global_injective topScale heq).1

/-- At one depth, families belonging to distinct members of the three-grid
decomposition cannot share an interval. -/
theorem finiteOneShiftFamily_disjoint_of_ne_shift
    (topScale : ℤ) (depth : ℕ) {shift shift' : Fin 3} (hne : shift ≠ shift')
    (E E' : Finset ℤ) :
    Disjoint (finiteOneShiftFamily topScale depth E shift)
      (finiteOneShiftFamily topScale depth E' shift') := by
  classical
  apply Finset.disjoint_left.mpr
  intro I hI hI'
  rcases mem_finiteOneShiftFamily hI with ⟨n, _, _, hrepr⟩
  rcases mem_finiteOneShiftFamily hI' with ⟨n', _, _, hrepr'⟩
  have heq := hrepr.symm.trans hrepr'
  exact hne (finiteShiftGridInterval_global_injective topScale heq).2.1

theorem finiteOneShiftFamily_pairwiseDisjoint_depths
    (topScale : ℤ) (shift : Fin 3) (E : ℕ → Finset ℤ) :
    Pairwise fun depth depth' : ℕ ↦
      Disjoint (finiteOneShiftFamily topScale depth (E depth) shift)
        (finiteOneShiftFamily topScale depth' (E depth') shift) := by
  intro depth depth' hne
  exact finiteOneShiftFamily_disjoint_of_ne_depth topScale shift hne _ _

theorem finiteOneShiftFamily_pairwiseDisjoint_shifts
    (topScale : ℤ) (depth : ℕ) (E : Finset ℤ) :
    Pairwise fun shift shift' : Fin 3 ↦
      Disjoint (finiteOneShiftFamily topScale depth E shift)
        (finiteOneShiftFamily topScale depth E shift') := by
  intro shift shift' hne
  exact finiteOneShiftFamily_disjoint_of_ne_shift topScale depth hne E E

/-- Expanding the finite multiscale family gives a sum over depths with no
multiplicity, since different depths contain different interval objects. -/
theorem sum_finiteOneShiftMultiscaleFamily
    {M : Type*} [AddCommMonoid M]
    (topScale : ℤ) (depths : Finset ℕ) (E : ℕ → Finset ℤ) (shift : Fin 3)
    (u : RealInterval → M) :
    (∑ I ∈ finiteOneShiftMultiscaleFamily topScale depths E shift, u I) =
      ∑ depth ∈ depths,
        ∑ I ∈ finiteOneShiftFamily topScale depth (E depth) shift, u I := by
  classical
  unfold finiteOneShiftMultiscaleFamily
  rw [Finset.sum_biUnion]
  intro depth _ depth' _ hne
  exact finiteOneShiftFamily_disjoint_of_ne_depth topScale shift hne _ _

/-- The genuine localized tail action over a finite one-shift multiscale
family is exactly the corresponding sum of fixed-scale localized actions. -/
theorem localizedTailAction_finiteOneShiftMultiscaleFamily
    (topScale ell : ℤ) (depths : Finset ℕ) (E : ℕ → Finset ℤ)
    (shift : Fin 3) (f : ℝ → ℂ) (x : ℝ) :
    localizedTailAction (finiteShiftGridScale topScale shift)
        (finiteOneShiftMultiscaleFamily topScale depths E shift) f ell x =
      ∑ depth ∈ depths,
        if (2 : ℝ) ^ ell ≤
            (2 : ℝ) ^ (topScale - (depth : ℤ) + 2) then
          krauseLaceyFixedScaleLocalizedSum (topScale - (depth : ℤ))
            (finiteOneShiftFamily topScale depth (E depth) shift) f x
        else 0 := by
  classical
  unfold localizedTailAction
  rw [sum_finiteOneShiftMultiscaleFamily topScale depths E shift]
  apply Finset.sum_congr rfl
  intro depth hdepth
  by_cases hcut : (2 : ℝ) ^ ell ≤
      (2 : ℝ) ^ (topScale - (depth : ℤ) + 2)
  · rw [ite_eq_left hcut]
    unfold krauseLaceyFixedScaleLocalizedSum
    apply Finset.sum_congr rfl
    intro I hI
    rcases mem_finiteOneShiftFamily hI with ⟨n, _, _, rfl⟩
    have hscale : finiteShiftGridScale topScale shift
        (finiteShiftGridInterval topScale shift depth
          (finiteShiftGridAddress depth n).2) = topScale - (depth : ℤ) := by
      simp only [finiteShiftGridScale, finiteShiftGridDepth_interval]
    rw [finiteShiftGridInterval_length_eq_scale, hscale, ite_eq_left hcut]
  · rw [ite_eq_right hcut]
    apply Finset.sum_eq_zero
    intro I hI
    rcases mem_finiteOneShiftFamily hI with ⟨n, _, _, rfl⟩
    have hscale : finiteShiftGridScale topScale shift
        (finiteShiftGridInterval topScale shift depth
          (finiteShiftGridAddress depth n).2) = topScale - (depth : ℤ) := by
      simp only [finiteShiftGridScale, finiteShiftGridDepth_interval]
    rw [finiteShiftGridInterval_length_eq_scale, hscale, ite_eq_right hcut]

/-- Summing the three fixed-scale grid pieces recovers the localized sum on
the full central-third partition, with no duplicated interval. -/
theorem sum_fixedScaleLocalizedSum_finiteOneShiftFamily
    (topScale j : ℤ) (depth : ℕ) (E : Finset ℤ)
    (f : ℝ → ℂ) (x : ℝ) :
    (∑ shift : Fin 3,
        krauseLaceyFixedScaleLocalizedSum j
          (finiteOneShiftFamily topScale depth E shift) f x) =
      krauseLaceyFixedScaleLocalizedSum j
        (finiteThreeShiftFamily topScale depth E) f x := by
  classical
  rw [finiteThreeShiftFamily_eq_biUnion]
  unfold krauseLaceyFixedScaleLocalizedSum
  apply (Finset.sum_biUnion (s := Finset.univ) (t := fun shift ↦
    finiteOneShiftFamily topScale depth E shift) ?_).symm
  intro shift _ shift' _ hne
  exact finiteOneShiftFamily_disjoint_of_ne_shift topScale depth hne E E

/-- When the central thirds cover the input, the sum of the three concrete
grid actions is exactly the genuine fixed-scale quadratic convolution. -/
theorem sum_fixedScaleLocalizedSum_eq_globalConvolution
    (f : L0Infinity) (topScale : ℤ) (depth : ℕ) (E : Finset ℤ)
    (hinput : krauseLaceyFixedScaleInput
      (finiteThreeShiftFamily topScale depth E) f = f) (x : ℝ) :
    (∑ shift : Fin 3,
        krauseLaceyFixedScaleLocalizedSum (topScale - (depth : ℤ))
          (finiteOneShiftFamily topScale depth E shift) f x) =
      ∫ t, annularQuadraticKernel
        (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 (x - t) * f t := by
  rw [sum_fixedScaleLocalizedSum_finiteOneShiftFamily]
  rcases f.bounded_toFun with ⟨C, hC⟩
  have hf2 : MemLp f 2 :=
    f.hasCompactSupport_toFun.memLp_of_bound
      f.measurable_toFun.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  calc
    krauseLaceyFixedScaleLocalizedSum (topScale - (depth : ℤ))
        (finiteThreeShiftFamily topScale depth E) f x =
        ∫ t, annularQuadraticKernel
          (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 (x - t) *
            krauseLaceyFixedScaleInput
              (finiteThreeShiftFamily topScale depth E) f t :=
      krauseLaceyFixedScaleLocalizedSum_eq_convolution
        (topScale - (depth : ℤ)) (finiteThreeShiftFamily topScale depth E) hf2 x
    _ = _ := by rw [hinput]

/-- The sum of the three finite multiscale tail actions is the exact finite
positive-half dyadic convolution tail. This is the operator-level bridge
from the three-grid forest to the positive-half smooth-truncation
approximants; the negative half is obtained separately by reflection. -/
theorem sum_localizedTailAction_eq_finite_globalTail
    (f : L0Infinity) (topScale ell : ℤ) (depths : Finset ℕ)
    (E : ℕ → Finset ℤ)
    (hinput : ∀ depth ∈ depths,
      krauseLaceyFixedScaleInput
        (finiteThreeShiftFamily topScale depth (E depth)) f = f)
    (x : ℝ) :
    (∑ shift : Fin 3,
        localizedTailAction (finiteShiftGridScale topScale shift)
          (finiteOneShiftMultiscaleFamily topScale depths E shift) f ell x) =
      ∑ depth ∈ depths,
        if (2 : ℝ) ^ ell ≤
            (2 : ℝ) ^ (topScale - (depth : ℤ) + 2) then
          ∫ t, annularQuadraticKernel
            (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 (x - t) * f t
        else 0 := by
  simp_rw [localizedTailAction_finiteOneShiftMultiscaleFamily]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro depth hdepth
  by_cases hcut : (2 : ℝ) ^ ell ≤
      (2 : ℝ) ^ (topScale - (depth : ℤ) + 2)
  · simp only [ite_eq_left hcut]
    exact sum_fixedScaleLocalizedSum_eq_globalConvolution
      f topScale depth (E depth) (hinput depth hdepth) x
  · simp only [ite_eq_right hcut, Finset.sum_const_zero]

/-- Complete finite deterministic bridge for the positive half: for any
finite set of depths there are concrete support-covering interval families,
each one-shift family lies inside its canonical parent-closed forest, and the
sum of the three local tail actions is exactly the finite positive-half
dyadic tail. -/
theorem exists_threeShiftForests_globalTail
    (f : L0Infinity) (topScale ell : ℤ) (depths : Finset ℕ)
    (maxDepth : ℕ) (hdepths : ∀ depth ∈ depths, depth ≤ maxDepth)
    (x : ℝ) :
    ∃ E : ℕ → Finset ℤ,
      (∀ shift,
        finiteOneShiftMultiscaleFamily topScale depths E shift ⊆
          completeFiniteShiftGridForest topScale shift maxDepth
            (finiteOneShiftMultiscaleAddresses depths E shift)) ∧
      (∑ shift : Fin 3,
          localizedTailAction (finiteShiftGridScale topScale shift)
            (finiteOneShiftMultiscaleFamily topScale depths E shift) f ell x) =
        ∑ depth ∈ depths,
          if (2 : ℝ) ^ ell ≤
              (2 : ℝ) ^ (topScale - (depth : ℤ) + 2) then
            ∫ t, annularQuadraticKernel
              (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 (x - t) * f t
          else 0 := by
  obtain ⟨E, hE⟩ := exists_finiteThreeShiftFamily_localization_all_depths f topScale
  refine ⟨E, ?_, ?_⟩
  · intro shift
    exact finiteOneShiftMultiscaleFamily_subset_completeForest
      topScale depths E shift maxDepth hdepths
  · exact sum_localizedTailAction_eq_finite_globalTail
      f topScale ell depths E (fun depth hdepth ↦ (hE depth).2.2) x

/-- One choice of the three localized families works simultaneously for every
physical lower cutoff and every observation point. This is the form needed
for the maximal truncation; the covering families depend only on the compact
support of `f`, not on the cutoff or the point. -/
theorem exists_threeShiftForests_globalTail_all_thresholds
    (f : L0Infinity) (topScale : ℤ) (depths : Finset ℕ)
    (maxDepth : ℕ) (hdepths : ∀ depth ∈ depths, depth ≤ maxDepth) :
    ∃ E : ℕ → Finset ℤ,
      (∀ shift,
        finiteOneShiftMultiscaleFamily topScale depths E shift ⊆
          completeFiniteShiftGridForest topScale shift maxDepth
            (finiteOneShiftMultiscaleAddresses depths E shift)) ∧
      ∀ (ell : ℤ) (x : ℝ),
        (∑ shift : Fin 3,
            localizedTailAction (finiteShiftGridScale topScale shift)
              (finiteOneShiftMultiscaleFamily topScale depths E shift) f ell x) =
          ∑ depth ∈ depths,
            if (2 : ℝ) ^ ell ≤
                (2 : ℝ) ^ (topScale - (depth : ℤ) + 2) then
              ∫ t, annularQuadraticKernel
                (positiveDyadicAmplitude (topScale - (depth : ℤ))) 1 (x - t) * f t
            else 0 := by
  obtain ⟨E, hE⟩ := exists_finiteThreeShiftFamily_localization_all_depths f topScale
  refine ⟨E, ?_, ?_⟩
  · intro shift
    exact finiteOneShiftMultiscaleFamily_subset_completeForest
      topScale depths E shift maxDepth hdepths
  · intro ell x
    exact sum_localizedTailAction_eq_finite_globalTail
      f topScale ell depths E (fun depth hdepth ↦ (hE depth).2.2) x


end

end KrauseLaceyThreeShiftGrid
end QuadraticCarleson
