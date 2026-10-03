/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaSpaceTime
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Ordered-coordinate energy levels and their normalization. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section4

/-- The ordered coordinate word represented by a finite tuple. -/
def thetaCoordinateWord {n : ℕ} (i : Fin n → Fin 2) : List (Fin 2) :=
  List.ofFn i

@[simp] theorem thetaCoordinateWord_length {n : ℕ} (i : Fin n → Fin 2) :
    (thetaCoordinateWord i).length = n := by
  simp [thetaCoordinateWord]

/-- The squared spatial L² norm of one ordered derivative at time `t`. -/
noncomputable def thetaWordSpatialEnergy
    (θ : ℝ → Homogenization.Vec 2 → ℝ) (w : List (Fin 2)) (t : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube, (classicalWordDerivative w (θ t) x) ^ 2

/-- The squared space-time gradient norm of one ordered derivative. -/
noncomputable def thetaWordSpaceTimeGradientEnergy
    (θ : ℝ → Homogenization.Vec 2 → ℝ) (w : List (Fin 2)) : ℝ :=
  ∫ p in AVenhance.timeCube,
    vecNormSq (AVenhance.spaceGrad (classicalWordDerivative w (θ p.1)) p.2)

/-- The largest spatial energy over the closed unit time interval, expressed
as the supremum of the actual classical energy values. -/
noncomputable def thetaWordSpatialEnergySup
    (θ : ℝ → Homogenization.Vec 2 → ℝ) (w : List (Fin 2)) : ℝ :=
  sSup (Set.range fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} =>
    thetaWordSpatialEnergy θ w t.1)

theorem thetaWordSpatialEnergy_le_sup
    (θ : ℝ → Homogenization.Vec 2 → ℝ) (w : List (Fin 2))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hbounded : BddAbove (Set.range fun s : {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1} =>
      thetaWordSpatialEnergy θ w s.1)) :
    thetaWordSpatialEnergy θ w t ≤ thetaWordSpatialEnergySup θ w := by
  exact le_csSup hbounded ⟨⟨t, ht⟩, rfl⟩

theorem thetaWordSpatialEnergySup_le
    (θ : ℝ → Homogenization.Vec 2 → ℝ) (w : List (Fin 2)) {B : ℝ}
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, thetaWordSpatialEnergy θ w t ≤ B) :
    thetaWordSpatialEnergySup θ w ≤ B := by
  exact csSup_le ⟨thetaWordSpatialEnergy θ w 0, ⟨⟨0, by norm_num⟩, rfl⟩⟩ (by
    rintro y ⟨⟨t, ht⟩, rfl⟩
    exact hB t ht)

/-- The level `n` energy is the maximum over ordered coordinate tuples of the
uniform-time L² norm plus the diffusivity-weighted space-time gradient norm. -/
noncomputable def thetaEnergyLevel
    (θ : ℝ → Homogenization.Vec 2 → ℝ) (κ : ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' (⟨fun _ => (0 : Fin 2), Finset.mem_univ _⟩ :
    (Finset.univ : Finset (Fin n → Fin 2)).Nonempty) fun i : Fin n → Fin 2 =>
    Real.sqrt (thetaWordSpatialEnergySup θ (thetaCoordinateWord i)) +
      Real.sqrt κ * Real.sqrt
        (thetaWordSpaceTimeGradientEnergy θ (thetaCoordinateWord i))

theorem thetaEnergyLevel_le_of_coordinate
    (θ : ℝ → Homogenization.Vec 2 → ℝ) (κ : ℝ) (n : ℕ)
    (i : Fin n → Fin 2) :
    Real.sqrt (thetaWordSpatialEnergySup θ (thetaCoordinateWord i)) +
        Real.sqrt κ * Real.sqrt
          (thetaWordSpaceTimeGradientEnergy θ (thetaCoordinateWord i)) ≤
      thetaEnergyLevel θ κ n := by
  exact Finset.le_sup' (fun i : Fin n → Fin 2 =>
    Real.sqrt (thetaWordSpatialEnergySup θ (thetaCoordinateWord i)) +
      Real.sqrt κ * Real.sqrt
        (thetaWordSpaceTimeGradientEnergy θ (thetaCoordinateWord i)))
    (Finset.mem_univ i)

end AVenhance.Infra.Section4

end
