/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaIntegratedEnergy

/-! # Differentiated energies of a classical solution

For an ordered derivative word `w`, the energy `‖∂^w θ(s)‖²` of a classical solution is continuous
    on
`[0,T]` and has the derivative `-2κ ‖∇∂^w θ‖² - 2 C_w(s)` at every `s > 0`, where
`C_w(s) = ∫ ∂^wθ (∂^w(b·∇θ) - b·∇∂^wθ)` is the commutator pairing.  The gradient dissipation is
continuous on `[0,∞)`. -/

@[expose] public section

open Homogenization MeasureTheory Filter
open AVenhance.Infra.Section4
open scoped Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

open AVenhance

/-- `‖∂^w θ(s)‖²_{L²(cell)}`. -/
def wEnergy (w : List (Fin 2)) (θ : ℝ → Vec 2 → ℝ) (s : ℝ) : ℝ :=
  ∫ x in unitCube, (classicalWordDerivative w (θ s) x) ^ 2

/-- `‖∇∂^w θ(s)‖²_{L²(cell)}`. -/
def wDiss (w : List (Fin 2)) (θ : ℝ → Vec 2 → ℝ) (s : ℝ) : ℝ :=
  ∫ x in unitCube, vecNormSq (spaceGrad (classicalWordDerivative w (θ s)) x)

/-- The commutator pairing `∫ ∂^wθ (∂^w(b·∇θ) - b·∇∂^wθ)`. -/
def wComm (w : List (Fin 2)) (Ψ θ : ℝ → Vec 2 → ℝ) (s : ℝ) : ℝ :=
  ∫ x in unitCube, classicalWordDerivative w (θ s) x *
    (classicalWordDerivative w (classicalTransport (streamVel Ψ s) (θ s)) x -
      vecDot (streamVel Ψ s x) (spaceGrad (classicalWordDerivative w (θ s)) x))

/-- Joint time-space domain with nonnegative time, including the initial trace. -/
def WordEnergy.nonnegDomain : Set (ℝ × Vec 2) := Set.Ici (0 : ℝ) ×ˢ Set.univ

theorem wEnergy_continuousOn {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (wEnergy w θ) (Set.Icc (0 : ℝ) T) := by
  have huJoint : ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry fun t x => classicalWordDerivative w (θ t) x)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := theta_classical_word_joint_contDiffOn_nonneg hθ w
  exact theta_energy_continuousOn huJoint hT

theorem wDiss_continuousOn {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) :
    ContinuousOn (wDiss w θ) (Set.Ici (0 : ℝ)) := by
  have hgrad (j : Fin 2) : ContinuousOn
      (fun p : ℝ × Vec 2 => spaceGrad (classicalWordDerivative w (θ p.1)) p.2 j)
      WordEnergy.nonnegDomain := by
    have h := theta_classical_word_joint_contDiffOn_nonneg hθ (j :: w)
    simpa [classicalWordDerivative,
      Classical.classicalWordDerivative, WordEnergy.nonnegDomain] using h.continuousOn
  have hjoint : ContinuousOn (fun p : ℝ × Vec 2 =>
      vecNormSq (spaceGrad (classicalWordDerivative w (θ p.1)) p.2)) WordEnergy.nonnegDomain := by
    have heq : (fun p : ℝ × Vec 2 =>
        vecNormSq (spaceGrad (classicalWordDerivative w (θ p.1)) p.2)) =
        fun p => (spaceGrad (classicalWordDerivative w (θ p.1)) p.2 0) ^ 2 +
          (spaceGrad (classicalWordDerivative w (θ p.1)) p.2 1) ^ 2 := by
      funext p
      simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
    rw [heq]
    exact ((hgrad 0).pow 2).add ((hgrad 1).pow 2)
  have := theta_time_parametric_integral_continuousOn hjoint
  exact this

theorem wEnergy_hasDerivAt {Ψ θ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    (hΨ : IsAdmissibleStream Ψ)
    (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ)
    (w : List (Fin 2)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (wEnergy w θ) (-2 * κ * wDiss w θ t - 2 * wComm w Ψ θ t) t := by
  let u : ℝ → Vec 2 → ℝ := fun s x => classicalWordDerivative w (θ s) x
  have huJoint : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := theta_classical_word_joint_contDiffOn_nonneg hsol.1 w
  have hEnergyDeriv := theta_energy_hasDerivAt huJoint ht
  have hpoint := theta_classical_differentiated_transport_energy_pairing hΨ hsol ht w
  have huOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain := by
    refine huJoint.mono ?_
    intro p hp
    have hp' : 0 < p.1 := by simpa [classicalPositiveTimeDomain] using hp.1
    exact ⟨hp'.le, Set.mem_univ p.2⟩
  have htime := classicalTimePartial_eq_deriv huOpen ht
  have htimeInt :
      (∫ x in unitCube, 2 * u t x * classicalTimePartial u (t, x)) =
        2 * (∫ x in unitCube, u t x * deriv (fun s => u s x) t) := by
    rw [show (fun x : Vec 2 => 2 * u t x * classicalTimePartial u (t, x)) =
        fun x => 2 * (u t x * deriv (fun s => u s x) t) by
      funext x
      rw [htime x]
      ring]
    rw [integral_const_mul]
  have hpair' : (∫ x in unitCube, u t x * deriv (fun s => u s x) t) + κ * wDiss w θ t =
      -wComm w Ψ θ t := by
    simpa [wDiss, wComm, u] using hpoint
  have hval : (∫ x in unitCube, 2 * u t x * classicalTimePartial u (t, x)) =
      -2 * κ * wDiss w θ t - 2 * wComm w Ψ θ t := by
    rw [htimeInt]
    linarith [hpair']
  exact hEnergyDeriv.congr_deriv hval

end AVenhance.Infra.FullTheorem.Separation
