/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.AnomalousDiffusion.Homogenization.Sobolev.CubeEmbedding.PeelFubini

/-! Coordinate slicing of half-open unit cells in `Vec d`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

namespace AVenhance.Infra.Torus

/-- Fubini along a selected coordinate, for any complete real normed target. This
is the vector-valued extension of CoarseGraining's `integral_peel_coord`. -/
theorem integral_peel_coord {n : ℕ} (i : Fin (n + 1)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Vec (n + 1) → E}
    (hf : Integrable f (volume : Measure (Vec (n + 1)))) :
    (∫ x, f x ∂(volume : Measure (Vec (n + 1)))) =
      ∫ z : Vec n, ∫ t : ℝ, f (i.insertNth t z)
        ∂(volume : Measure ℝ) ∂(volume : Measure (Vec n)) := by
  classical
  let μ : ∀ _ : Fin (n + 1), Measure ℝ := fun _ => volume
  have hmp := measurePreserving_piFinSuccAbove μ i
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hvol : (volume : Measure (Vec (n + 1))) = Measure.pi μ := volume_pi
  have hf' : Integrable (fun p => f (e.symm p))
      ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) := by
    have hpi : Integrable f (Measure.pi μ) := by rw [← hvol]; exact hf
    exact hmp.symm.integrable_comp_of_integrable hpi
  rw [hvol, ← hmp.symm.integral_comp' f, integral_prod_symm _ hf']
  rfl

/-- Inserting a coordinate into a vector lies in the unit cell exactly when
both the peeled coordinate and the remaining vector lie in their cells. -/
theorem mem_unitCell_insertNth_iff {n : ℕ} (i : Fin (n + 1)) (t : ℝ)
    (z : Vec n) :
    i.insertNth t z ∈ unitCell (n + 1) ↔ t ∈ Set.Ioc (0 : ℝ) 1 ∧ z ∈ unitCell n := by
  simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, i.forall_iff_succAbove,
    i.insertNth_apply_same, i.insertNth_apply_succAbove, zero_add]

/-- Restricted-cell Fubini, peeling an arbitrary coordinate of `Vec (n+1)`.
The remaining variables are integrated over their own half-open unit cell. -/
theorem integral_unitCell_peel_coord {n : ℕ} (i : Fin (n + 1))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Vec (n + 1) → E}
    (hf : IntegrableOn f (unitCell (n + 1))) :
    (∫ x in unitCell (n + 1), f x) =
      ∫ z in unitCell n, ∫ t in Set.Ioc (0 : ℝ) 1, f (i.insertNth t z) := by
  let g : Vec (n + 1) → E := (unitCell (n + 1)).indicator f
  have hg : Integrable g (volume : Measure (Vec (n + 1))) :=
    hf.integrable_indicator (measurableSet_unitCell (n + 1))
  calc
    ∫ x in unitCell (n + 1), f x = ∫ x, g x := by
      symm
      exact integral_indicator (measurableSet_unitCell (n + 1))
    _ = ∫ z : Vec n, ∫ t : ℝ, g (i.insertNth t z) :=
      integral_peel_coord i hg
    _ = ∫ z in unitCell n, ∫ t in Set.Ioc (0 : ℝ) 1, f (i.insertNth t z) := by
      have hpoint (z : Vec n) (t : ℝ) :
          g (i.insertNth t z) =
          (unitCell n).indicator
              (fun z => (Set.Ioc (0 : ℝ) 1).indicator
                (fun t => f (i.insertNth t z)) t) z := by
        classical
        simp only [g, Set.indicator_apply, mem_unitCell_insertNth_iff]
        by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1 <;>
          by_cases hz : z ∈ unitCell n <;> simp [ht, hz]
      calc
        ∫ z : Vec n, ∫ t : ℝ, g (i.insertNth t z) =
            ∫ z, ∫ t,
              (unitCell n).indicator
                (fun z => (Set.Ioc (0 : ℝ) 1).indicator
                  (fun t => f (i.insertNth t z)) t) z := by
          apply integral_congr_ae
          filter_upwards with z
          apply integral_congr_ae
          filter_upwards with t
          exact hpoint z t
        _ = ∫ z in unitCell n, ∫ t,
              (Set.Ioc (0 : ℝ) 1).indicator
                (fun t => f (i.insertNth t z)) t := by
          rw [integral_integral_indicator _ (measurableSet_unitCell n)]
        _ = ∫ z in unitCell n, ∫ t in Set.Ioc (0 : ℝ) 1,
              f (i.insertNth t z) := by
          apply setIntegral_congr_ae (measurableSet_unitCell n)
          filter_upwards with z
          intro _hz
          exact integral_indicator measurableSet_Ioc

/-- The two-dimensional instance of restricted-cell coordinate slicing. -/
theorem integral_unitCell2_peel_coord (i : Fin 2) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → E} (hf : IntegrableOn f (unitCell 2)) :
    (∫ x in unitCell 2, f x) =
      ∫ z in unitCell 1, ∫ t in Set.Ioc (0 : ℝ) 1, f (i.insertNth t z) :=
  integral_unitCell_peel_coord i hf

end AVenhance.Infra.Torus
