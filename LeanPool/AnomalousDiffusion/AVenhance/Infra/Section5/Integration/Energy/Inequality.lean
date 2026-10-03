/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Rate

/-! # The differential energy inequality

For `t > 0` with `‖f t‖_{HDot⁻¹} < ∞`, where `f = advDiffOp b κ v`,
`d/dt ∫ w² + κ ∫ |∇w|² ≤ ‖f t‖²_{HDot⁻¹} / κ`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus

namespace AVenhance.Infra.Section5.Integration.Energy

open AVenhance

/-- Young's inequality in the form used by the energy estimate. -/
theorem young_energy {κ N G : ℝ} (hκ : 0 < κ) :
    2 * (N * G) ≤ κ * G ^ 2 + N ^ 2 / κ := by
  have h : 0 ≤ (κ * G - N) ^ 2 / κ := by positivity
  have h2 : (κ * G - N) ^ 2 / κ = κ * G ^ 2 + N ^ 2 / κ - 2 * (N * G) := by
    field_simp
    ring
  linarith

variable {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}

namespace ForcedSetup

theorem energy_inequality (S : ForcedSetup φ κ θ₀ u v) {t : ℝ} (ht : 0 < t)
    (hfin : hMinusOneNorm (advDiffOp (streamVel φ) κ v t) ≠ ⊤) :
    (∫ x in unitCell 2, 2 * (u t x - v t x) * deriv (fun s => u s x - v s x) t) +
        κ * gradNormSq (spaceGrad fun y => u t y - v t y) ≤
      (hMinusOneNorm (advDiffOp (streamVel φ) κ v t)).toReal ^ 2 / κ := by
  rw [S.energy_rate ht]
  have hG : (∫ x in unitCell 2,
      vecDot (spaceGrad (fun y => u t y - v t y) x) (spaceGrad (fun y => u t y - v t y) x)) =
        gradNormSq (spaceGrad fun y => u t y - v t y) := by
    rw [integral_unitCell_eq_unitCube]
    rfl
  have hI : (∫ x in unitCell 2, advDiffOp (streamVel φ) κ v t x * (u t x - v t x)) =
      ∫ x in unitCube, advDiffOp (streamVel φ) κ v t x * (u t x - v t x) :=
    integral_unitCell_eq_unitCube _
  rw [hG, hI]
  have hdual := abs_integral_mul_le_hMinusOneNorm (h := advDiffOp (streamVel φ) κ v t)
    (S.wSlice ht.le) (S.wPeriodic ht.le) hfin
  set Gs := gradNormSq (spaceGrad fun y => u t y - v t y) with hGs
  have hGs0 : 0 ≤ Gs := gradNormSq_nonneg _
  have hsq : Real.sqrt Gs ^ 2 = Gs := Real.sq_sqrt hGs0
  have hyoung := young_energy (N := (hMinusOneNorm (advDiffOp (streamVel φ) κ v t)).toReal)
    (G := Real.sqrt Gs) S.hκ
  rw [hsq] at hyoung
  have habs := (abs_le.mp hdual).1
  linarith [S.hκ]

end ForcedSetup

end AVenhance.Infra.Section5.Integration.Energy

end
