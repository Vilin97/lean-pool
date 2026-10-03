/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.GradientDeviation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialRegularity

/-! Source estimate for the actual flow-pulled gradient in the first `d_m` term. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization

namespace AVenhance.Infra.Section4

open AVenhance

theorem DmPulledGradient.dm_gradMatrix_entry_eq_fderiv {X : Vec 2 → Vec 2}
    {x : Vec 2} (hX : DifferentiableAt ℝ X x) (i j : Fin 2) :
    gradMatrix X x i j = fderiv ℝ X x (basisVec i) j := by
  rw [gradMatrix, Matrix.of_apply]
  change fderiv ℝ (fun y => X y j) x (basisVec i) = _
  rw [fderiv_apply hX j]
  rfl

/-- Every active large cutoff lies in its time window. -/
theorem hatXiML_active_time_window {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ)
    (hactive : I.hatXiML m l t ≠ 0) :
    |t - (l : ℝ) * tauPP β I.Λ m| ≤
      tauPP β I.Λ m / 2 + tauP β I.Λ m := by
  have hτpp := I.tauPP_pos' m
  have hτp := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hle := I.hatXi_le m hm l t
  have hge : 0 ≤ I.hatXiML m l t :=
    (Ingredients.hatXiML_mem_Icc I hm l t).1
  have hmem : t ∈ Set.Icc
      ((l - 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) := by
    by_contra hnot
    apply hactive
    unfold Ingredients.hatXiML
    rw [indIcc_eq_zero_of_not_mem hnot] at hle
    exact le_antisymm hle hge
  rw [abs_le]
  constructor <;> nlinarith [hmem.1, hmem.2]

end AVenhance.Infra.Section4

end
