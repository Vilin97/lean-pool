/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionInputs.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.NoSelectionInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.EnergyLoss
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergySmooth

/-! # Energy balance for the difference of two classical solutions with the same drift

`w = θ - θ'` solves `∂ₜ w + b·∇w - κ Δ w = div ((κ-κ') ∇θ')`, hence
`d/dt ‖w‖² = -2κ ‖∇w‖² - 2(κ-κ') ⟨∇w, ∇θ'⟩`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSelectionInputs

open AVenhance AVenhance.Infra.Section4

theorem cont_vecDot_grad {f g : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (fun x => vecDot (spaceGrad f x) (spaceGrad g x)) := by
  have hf' := fun i => (contDiff_spaceGrad_coord hf i).continuous
  have hg' := fun i => (contDiff_spaceGrad_coord hg i).continuous
  simp only [vecDot, Fin.sum_univ_two]
  exact ((hf' 0).mul (hg' 0)).add ((hf' 1).mul (hg' 1))

theorem vecDot_smul_right (a : Vec 2) (δ : ℝ) (b : Vec 2) :
    vecDot a (δ • b) = δ * vecDot a b := by
  simp only [vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  ring

theorem spaceGrad_const_mul {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (δ : ℝ) :
    spaceGrad (fun y => δ * f y) = fun x i => δ * spaceGrad f x i := by
  funext x i
  change fderiv ℝ (fun y => δ * f y) x (basisVec i) = _
  rw [fderiv_const_mul (hf.differentiable (by simp) x)]
  simp [spaceGrad]

theorem vecDiv_smul_grad {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (δ : ℝ) (x : Vec 2) :
    vecDiv (fun y => δ • spaceGrad f y) x = δ * spaceLap f x := by
  unfold vecDiv spaceLap
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (fun y => (δ • spaceGrad f y) i) = fun y => δ * spaceGrad f y i := by
    funext y; simp
  rw [h, spaceGrad_const_mul (contDiff_spaceGrad_coord hf i)]

theorem diff_energy_hasDerivAt {Ψ θ θ' : ℝ → Vec 2 → ℝ} {κ κ' : ℝ} {θ₀ : Vec 2 → ℝ}
    (hΨ : IsAdmissibleStream Ψ)
    (hθ : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ)
    (hθ' : IsClassicalSol (streamVel Ψ) κ' (fun _ _ => 0) θ₀ θ') {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in unitCube, (θ s x - θ' s x) ^ 2)
      (-2 * κ * (∫ x in unitCube,
          vecNormSq (spaceGrad (fun y => θ t y - θ' t y) x)) -
        2 * (κ - κ') * (∫ x in unitCube,
          vecDot (spaceGrad (fun y => θ t y - θ' t y) x) (spaceGrad (θ' t) x))) t := by
  let u : ℝ → Vec 2 → ℝ := fun s x => θ s x - θ' s x
  have huJoint : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    hθ.1.sub hθ'.1
  have hopen : ∀ v : ℝ → Vec 2 → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry v) (Set.Ici (0 : ℝ) ×ˢ Set.univ) →
      ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry v) classicalPositiveTimeDomain := by
    intro v hv
    refine hv.mono ?_
    intro p hp
    have hp' : 0 < p.1 := by simpa [classicalPositiveTimeDomain] using hp.1
    exact ⟨hp'.le, Set.mem_univ p.2⟩
  have hdu := theta_energy_hasDerivAt huJoint ht
  -- derivative of u in time
  have hderiv : ∀ x, deriv (fun s => u s x) t =
      deriv (fun s => θ s x) t - deriv (fun s => θ' s x) t := by
    intro x
    have h1 := classicalTimeSection_hasDerivAt (hopen θ hθ.1) ht x
    have h2 := classicalTimeSection_hasDerivAt (hopen θ' hθ'.1) ht x
    rw [h1.deriv, h2.deriv]
    exact (h1.sub h2).deriv
  have hu : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    (classicalSmooth_slice_nonneg hθ.1 ht.le).sub (classicalSmooth_slice_nonneg hθ'.1 ht.le)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (θ t) := classicalSmooth_slice_nonneg hθ.1 ht.le
  have hsm' : ContDiff ℝ (⊤ : ℕ∞) (θ' t) := classicalSmooth_slice_nonneg hθ'.1 ht.le
  have huper : IsZ2Periodic (u t) := by
    intro n x
    have h1 := hθ.2.1 t ht.le n x
    have h2 := hθ'.2.1 t ht.le n x
    simp only [u, h1, h2]
  have hpg' : IsZ2Periodic (spaceGrad (θ' t)) :=
    (Infra.Section5.RelativeError.isPeriodicH1With_of_contDiff (hsm'.of_le (by simp))
      (hθ'.2.1 t ht.le)).2.1
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x => (κ - κ') • spaceGrad (θ' t) x) :=
    (contDiff_spaceGrad hsm').const_smul _
  have hFper : IsZ2Periodic (fun x => (κ - κ') • spaceGrad (θ' t) x) := by
    intro n x
    simp only [hpg' n x]
  have hpde : ∀ x, deriv (fun s => u s x) t - κ * spaceLap (u t) x +
      vecDot (streamVel Ψ t x) (spaceGrad (u t) x) =
      vecDiv (fun y => (κ - κ') • spaceGrad (θ' t) y) x := by
    intro x
    have e1 := hθ.2.2.2 t ht x
    have e2 := hθ'.2.2.2 t ht x
    simp only [advDiffOp] at e1 e2
    have hlap : spaceLap (u t) x = spaceLap (θ t) x - spaceLap (θ' t) x := by
      have := congrFun (Infra.Classical.smooth_spaceLap_sub hsm hsm') x
      simpa [u] using this
    have hgr : spaceGrad (u t) x = spaceGrad (θ t) x - spaceGrad (θ' t) x := by
      have := congrFun (Infra.Classical.smooth_spaceGrad_sub hsm hsm') x
      simpa [u] using this
    have hdot : vecDot (streamVel Ψ t x) (spaceGrad (u t) x) =
        vecDot (streamVel Ψ t x) (spaceGrad (θ t) x) -
          vecDot (streamVel Ψ t x) (spaceGrad (θ' t) x) := by
      rw [hgr]; simp [vecDot, mul_sub, Finset.sum_sub_distrib]
    rw [hderiv, hlap, hdot, vecDiv_smul_grad hsm']
    linarith
  have hpair := Infra.Section4.theta_forced_classical_energy_pairing (φ := Ψ) (κ := κ)
    (u := u) (F := fun s y => (κ - κ') • spaceGrad (θ' s) y) hΨ hu huper hF hFper hpde
  have hFdot : (∫ x in unitCube, vecDot (spaceGrad (u t) x) ((κ - κ') • spaceGrad (θ' t) x)) =
      (κ - κ') * ∫ x in unitCube, vecDot (spaceGrad (u t) x) (spaceGrad (θ' t) x) := by
    simp_rw [vecDot_smul_right]
    rw [integral_const_mul]
  have hopen' := hopen u huJoint
  have hval : (∫ x in unitCube, 2 * u t x * classicalTimePartial u (t, x)) =
      2 * ∫ x in unitCube, u t x * deriv (fun s => u s x) t := by
    rw [show (fun x : Vec 2 => 2 * u t x * classicalTimePartial u (t, x)) =
        fun x => 2 * (u t x * deriv (fun s => u s x) t) by
      funext x
      rw [classicalTimePartial_eq_deriv hopen' ht x]
      ring]
    rw [integral_const_mul]
  rw [hval] at hdu
  rw [hFdot] at hpair
  refine hdu.congr_deriv ?_
  linarith

end AVenhance.Infra.FullTheorem.NoSelectionInputs
