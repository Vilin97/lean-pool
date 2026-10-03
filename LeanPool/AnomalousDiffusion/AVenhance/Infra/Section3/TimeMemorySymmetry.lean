/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CutoffSymmetry
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.CorrTime
public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-! Translation covariance of the exponentially weighted corrector memory. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace AVenhance.Infra.Section3

open AVenhance
open Homogenization

theorem TimeMemorySymmetry.volume_restrict_Iic_add_map (t T : ℝ) :
    (volume.restrict (Set.Iic t)).map (MeasurableEquiv.addRight T) =
      volume.restrict (Set.Iic (t + T)) := by
  let e := MeasurableEquiv.addRight T
  have hpre : e ⁻¹' Set.Iic (t + T) = Set.Iic t := by
    ext s
    simp [e, MeasurableEquiv.addRight]
  have hvol : (volume : Measure ℝ).map e = volume := by
    simpa [e, MeasurableEquiv.addRight] using
      (map_add_right_eq_self (volume : Measure ℝ) T)
  calc
    (volume.restrict (Set.Iic t)).map e =
        ((volume : Measure ℝ).map e).restrict (Set.Iic (t + T)) := by
          simpa [hpre] using
            (e.restrict_map (volume : Measure ℝ) (Set.Iic (t + T))).symm
    _ = volume.restrict (Set.Iic (t + T)) := by rw [hvol]

/-- A set integral over a translated left half-line is transported by the
translation equivalence. -/
theorem TimeMemorySymmetry.integral_Iic_add_right (t T : ℝ) (f : ℝ → ℝ) :
    (∫ s in Set.Iic (t + T), f s) =
      ∫ s in Set.Iic t, f (s + T) := by
  rw [← TimeMemorySymmetry.volume_restrict_Iic_add_map t T]
  exact MeasureTheory.integral_map_equiv (MeasurableEquiv.addRight T) f

/-- The corrector memory is invariant under translating time by two large
cells and the small index by twice the number of small cells per large cell. -/
theorem corrTime_add_twoCellCount {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) :
    I.corrTime κ m
      (k + 2 * (Infra.Ingredients.tauCellCount β I.Λ m : ℤ))
      (t + 2 * tauPP β I.Λ m) = I.corrTime κ m k t := by
  let T := 2 * tauPP β I.Λ m
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  unfold Ingredients.corrTime
  change
    (∫ s in Set.Iic (t + T),
      I.zetaProd m (k + 2 *
        (Infra.Ingredients.tauCellCount β I.Λ m : ℤ)) s *
        Real.exp (ρ * (s - (t + T)))) =
    ∫ s in Set.Iic t,
      I.zetaProd m k s * Real.exp (ρ * (s - t))
  rw [TimeMemorySymmetry.integral_Iic_add_right t T]
  apply setIntegral_congr_fun (measurableSet_Iic)
  intro s hs
  change I.zetaProd m
      (k + 2 * (Infra.Ingredients.tauCellCount β I.Λ m : ℤ))
      (s + 2 * tauPP β I.Λ m) *
      Real.exp (ρ * (s + 2 * tauPP β I.Λ m -
        (t + 2 * tauPP β I.Λ m))) =
    I.zetaProd m k s * Real.exp (ρ * (s - t))
  rw [zetaProd_add_twoCellCount I hm k s]
  congr 2
  congr 1
  ring

end AVenhance.Infra.Section3
