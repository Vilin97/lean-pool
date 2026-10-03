/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.Chain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.UniformInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.WeakEnergyIdentity

/-! # The tail piece `w = θ − θ_M` (analytic case of `r.LeBron.2`)

Sup bound `‖w(t)‖ ≤ 2 C_t (1+A)^β ε_M^{a} ‖θ₀‖` (`a = qβ − (β-γ) > 0`) from the sup-in-time
stream-difference estimate and the classical energy bound; Hölder bound
`‖w(t) − w(s)‖ ≲ ε_M^{-(β-γ)/2} h^{1/4} ‖θ₀‖_{H¹}` from Lemma U twice; interpolation by
`holder_step` gives `‖w(t) − w(s)‖ ≤ K_w ‖θ₀‖_{H¹} h^{μ_w}` uniformly in `κ`, `M`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Abstract real algebra of the tail ratio `C ε_{M+1}^β / κ`. -/
theorem tail_ratio_le {Ct A E E' q β s κ : ℝ} (hE : 0 < E) (hE' : 0 ≤ E')
    (hE'le : E' ≤ (1 + A) * E ^ q) (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hβ : 0 ≤ β)
    (hκ : (1 / 2) * E ^ s ≤ κ) :
    Ct * E' ^ β / κ ≤ (2 * Ct * (1 + A) ^ β) * E ^ (q * β - s) := by
  have hEs : 0 < E ^ s := Real.rpow_pos_of_pos hE s
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκ
  have h1 : E' ^ β ≤ (1 + A) ^ β * E ^ (q * β) := by
    calc E' ^ β ≤ ((1 + A) * E ^ q) ^ β := Real.rpow_le_rpow hE' hE'le hβ
      _ = (1 + A) ^ β * E ^ (q * β) := by
        rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hE.le _), ← Real.rpow_mul hE.le]
  rw [div_le_iff₀ hκ0]
  have hsub : E ^ (q * β - s) * E ^ s = E ^ (q * β) := by
    rw [← Real.rpow_add hE]; congr 1; ring
  calc Ct * E' ^ β ≤ Ct * ((1 + A) ^ β * E ^ (q * β)) := mul_le_mul_of_nonneg_left h1 hCt
    _ = (2 * Ct * (1 + A) ^ β) * (E ^ (q * β - s) * ((1 / 2) * E ^ s)) := by
        rw [← hsub]; ring
    _ ≤ (2 * Ct * (1 + A) ^ β) * (E ^ (q * β - s) * κ) := by
        gcongr
    _ = _ := by ring

/-- Classical energy bound `√κ ‖∇θ_M‖ ≤ ‖θ₀‖`. -/
theorem classical_sqrt_energy_le {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (M : ℕ) {κ : ℝ} (hκ : 0 < κ) {θ₀ : Vec 2 → ℝ}
    (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) {θM : ℝ → Vec 2 → ℝ}
    (hθM : IsClassicalSol (streamVel (Φ M)) κ (fun _ _ => 0) θ₀ θM) :
    Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θM t) x)) ≤
      Real.sqrt (l2NormSq θ₀) := by
  have hadm := streamSeq_isAdmissible hΦ M
  have hcont := hadm.vel_continuous
  have hweak := Infra.Section5.RelativeError.classical_isWeakSolutionGrad hcont hθM
  have hf : MemL2On unitCube θ₀ :=
    Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On hθ₀.continuous
  have hen := Infra.Section5.divFree_energy_dissipation_bound hweak hf
    (hcont.aestronglyMeasurable) ⟨velBound β, fun t _ x => streamVel_norm_le hΦ M t x⟩
    (fun t _ => streamVel_isZ2Periodic hadm t) (isDivFree_streamVel hadm)
  rw [← Real.sqrt_mul hκ.le]
  apply Real.sqrt_le_sqrt
  have hl : 0 ≤ l2NormSq θ₀ := integral_nonneg fun x => sq_nonneg _
  linarith

end AVenhance.Infra.FullTheorem
