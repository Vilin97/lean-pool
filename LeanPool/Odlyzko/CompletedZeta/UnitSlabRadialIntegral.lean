/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.UnitSlabRadial
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units Set
  dirichletUnitTheorem

namespace NumberField.Odlyzko

open mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- A positive unit slab coordinate factor used in the Odlyzko-bound argument. -/
noncomputable def positiveUnitSlabCoordinateFactor
    (f : ℝ → ℂ) (w : InfinitePlace K) (x : ℝ) : ℂ :=
  if w = w₀ then (Ioi 0).indicator f x
  else (Ico 0 1).indicator (fun _ ↦ 1) x

open Classical in
theorem positiveUnitSlab_indicator_eq_prod
    (f : ℝ → ℂ) (y : mixedEmbedding.realSpace K) :
    (positiveUnitFundamentalParamSet (K := K)).indicator
        (fun z ↦ f (z w₀)) y =
      ∏ w : InfinitePlace K,
        positiveUnitSlabCoordinateFactor (K := K) f w (y w) := by
  classical
  by_cases hrad : 0 < y w₀
  · by_cases hunit : ∀ w, w ≠ w₀ → y w ∈ Ico (0 : ℝ) 1
    · have hy : y ∈ positiveUnitFundamentalParamSet (K := K) := by
        exact ⟨(mem_unitFundamentalParamSet_iff y).mpr hunit, hrad⟩
      rw [Set.indicator_of_mem hy, Finset.prod_eq_single w₀]
      · simp [positiveUnitSlabCoordinateFactor, hrad]
      · intro w _ hw
        simp [positiveUnitSlabCoordinateFactor, hw,
          hunit w hw]
      · simp
    · push Not at hunit
      obtain ⟨w, hw, hyw⟩ := hunit
      have hy : y ∉ positiveUnitFundamentalParamSet (K := K) := by
        intro hy
        exact hyw ((mem_unitFundamentalParamSet_iff y).mp hy.1 w hw)
      rw [Set.indicator_of_notMem hy]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ w)
      simp [positiveUnitSlabCoordinateFactor, hw, hyw]
  · have hy : y ∉ positiveUnitFundamentalParamSet (K := K) := by
      intro hy
      exact hrad hy.2
    rw [Set.indicator_of_notMem hy]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ w₀)
    simp [positiveUnitSlabCoordinateFactor, hrad]

open Classical in
theorem setIntegral_positiveUnitFundamentalParamSet_radial
    (f : ℝ → ℂ) :
    (∫ y in positiveUnitFundamentalParamSet (K := K), f (y w₀)) =
      ∫ t in Ioi (0 : ℝ), f t := by
  rw [← integral_indicator measurableSet_positiveUnitFundamentalParamSet]
  calc
    (∫ y : mixedEmbedding.realSpace K,
        (positiveUnitFundamentalParamSet (K := K)).indicator
          (fun z ↦ f (z w₀)) y) =
        ∫ y : mixedEmbedding.realSpace K,
          ∏ w : InfinitePlace K,
            positiveUnitSlabCoordinateFactor (K := K) f w (y w) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (positiveUnitSlab_indicator_eq_prod f)
    _ = ∏ w : InfinitePlace K,
          ∫ x : ℝ, positiveUnitSlabCoordinateFactor (K := K) f w x :=
      integral_fintype_prod_volume_eq_prod _
    _ = ∫ t in Ioi (0 : ℝ), f t := by
      rw [Finset.prod_eq_single w₀]
      · simp [positiveUnitSlabCoordinateFactor,
          integral_indicator measurableSet_Ioi]
      · intro w _ hw
        simp [positiveUnitSlabCoordinateFactor, hw,
          integral_indicator measurableSet_Ico]
      · simp

open Classical in
theorem integrableOn_positiveUnitFundamentalParamSet_radial
    {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    IntegrableOn (fun y : mixedEmbedding.realSpace K ↦ f (y w₀))
      (positiveUnitFundamentalParamSet (K := K)) := by
  classical
  have hfactor (w : InfinitePlace K) :
      Integrable (positiveUnitSlabCoordinateFactor (K := K) f w) := by
    by_cases hw : w = w₀
    · subst w
      have heq :
          positiveUnitSlabCoordinateFactor (K := K) f w₀ =
            (Ioi 0).indicator f := by
        funext x
        simp [positiveUnitSlabCoordinateFactor]
      rw [heq]
      exact hf.integrable_indicator measurableSet_Ioi
    · have heq :
          positiveUnitSlabCoordinateFactor (K := K) f w =
            (Ico 0 1).indicator (fun _ ↦ 1) := by
        funext x
        simp [positiveUnitSlabCoordinateFactor, hw]
      rw [heq]
      exact
        (integrableOn_const (hs := by simp) :
          IntegrableOn (fun _ : ℝ ↦ (1 : ℂ)) (Ico 0 1)).integrable_indicator
            measurableSet_Ico
  have hprod :
      Integrable
        (fun y : mixedEmbedding.realSpace K ↦
          ∏ w : InfinitePlace K,
            positiveUnitSlabCoordinateFactor (K := K) f w (y w))
        (Measure.pi fun _ ↦ volume) :=
    Integrable.fintype_prod hfactor
  rw [← MeasureTheory.volume_pi] at hprod
  have hindicator :
      Integrable
        ((positiveUnitFundamentalParamSet (K := K)).indicator
          (fun y : mixedEmbedding.realSpace K ↦ f (y w₀))) :=
    hprod.congr (Filter.Eventually.of_forall fun y ↦
      (positiveUnitSlab_indicator_eq_prod f y).symm)
  exact (integrable_indicator_iff
    measurableSet_positiveUnitFundamentalParamSet).mp hindicator

end NumberField.Odlyzko
