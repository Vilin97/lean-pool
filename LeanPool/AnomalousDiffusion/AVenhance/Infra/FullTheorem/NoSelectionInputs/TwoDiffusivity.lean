/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionInputs.DiffEnergy

/-! # `TwoDiffusivityContract`

Two classical solutions with the same drift and diffusivities `κ, κ'`, same data `θ₀`:
`‖θ(t) - θ'(t)‖² ≤ (κ-κ')²/(4κκ') ‖θ₀‖²`.  With `w = θ - θ'` and `δ = κ - κ'`,
`d/dt ‖w‖² = -2κ‖∇w‖² - 2δ⟨∇w,∇θ'⟩ ≤ δ²/(2κ) ‖∇θ'‖²` (Young), and
`2κ' ∫₀ᵗ ‖∇θ'‖² ≤ ‖θ₀‖²` is the energy identity of `θ'`. -/

@[expose] public section

open MeasureTheory Homogenization Set

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSelectionInputs

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.FullTheorem.Separation

/-- Integrated Young inequality: `-2κ ∫|g|² - 2δ ∫ g·h ≤ δ²/(2κ) ∫ |h|²`. -/
theorem young_integral {f h : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {κ δ : ℝ} (hκ : 0 < κ) :
    -2 * κ * (∫ x in unitCube, vecNormSq (spaceGrad f x)) -
      2 * δ * (∫ x in unitCube, vecDot (spaceGrad f x) (spaceGrad h x)) ≤
    δ ^ 2 / (2 * κ) * (∫ x in unitCube, vecNormSq (spaceGrad h x)) := by
  have cff : Continuous (fun x => vecNormSq (spaceGrad f x)) := cont_vecDot_grad hf hf
  have chh : Continuous (fun x => vecNormSq (spaceGrad h x)) := cont_vecDot_grad hh hh
  have cfh := cont_vecDot_grad hf hh
  have i1 := thetaTime_integrableOn_unitCube cff
  have i2 := thetaTime_integrableOn_unitCube cfh
  have i3 := thetaTime_integrableOn_unitCube chh
  have hnn : 0 ≤ ∫ x in unitCube, (2 * κ * vecNormSq (spaceGrad f x) +
      2 * δ * vecDot (spaceGrad f x) (spaceGrad h x) +
      δ ^ 2 / (2 * κ) * vecNormSq (spaceGrad h x)) := by
    refine integral_nonneg fun x => ?_
    have : 2 * κ * vecNormSq (spaceGrad f x) + 2 * δ * vecDot (spaceGrad f x) (spaceGrad h x) +
        δ ^ 2 / (2 * κ) * vecNormSq (spaceGrad h x) =
        2 * κ * ((spaceGrad f x 0 + δ * spaceGrad h x 0 / (2 * κ)) ^ 2 +
          (spaceGrad f x 1 + δ * spaceGrad h x 1 / (2 * κ)) ^ 2) := by
      simp only [vecNormSq, vecDot, Fin.sum_univ_two]
      field_simp
      ring
    rw [this]
    positivity
  have j1 : IntegrableOn (fun x => 2 * κ * vecNormSq (spaceGrad f x) +
      2 * δ * vecDot (spaceGrad f x) (spaceGrad h x)) unitCube :=
    (i1.const_mul _).add (i2.const_mul _)
  rw [integral_add j1 (i3.const_mul _),
    integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul] at hnn
  linarith

/-- `‖θ(t) - θ'(t)‖² ≤ (κ-κ')²/(4κκ') ‖θ₀‖²`. -/
theorem diff_energy_le {Ψ θ θ' : ℝ → Vec 2 → ℝ} {κ κ' : ℝ} {θ₀ : Vec 2 → ℝ}
    (hΨ : IsAdmissibleStream Ψ) (hκ : 0 < κ) (hκ' : 0 < κ')
    (hθ : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ)
    (hθ' : IsClassicalSol (streamVel Ψ) κ' (fun _ _ => 0) θ₀ θ') {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in unitCube, (θ t x - θ' t x) ^ 2 ≤ (κ - κ') ^ 2 / (4 * κ * κ') * l2NormSq θ₀ := by
  have h0 : ∫ x in unitCube, (θ 0 x - θ' 0 x) ^ 2 = 0 := by
    have : ∀ x, θ 0 x - θ' 0 x = 0 := fun x => by rw [hθ.2.2.1 x, hθ'.2.2.1 x]; ring
    simp [this]
  rcases ht.eq_or_lt with rfl | htpos
  · rw [h0]
    have : 0 ≤ l2NormSq θ₀ := integral_nonneg fun x => sq_nonneg _
    positivity
  set c : ℝ := (κ - κ') ^ 2 / (4 * κ * κ') with hc
  let Ew : ℝ → ℝ := fun s => ∫ x in unitCube, (θ s x - θ' s x) ^ 2
  let Φ : ℝ → ℝ := fun s => Ew s - c * (wEnergy [] θ' 0 - wEnergy [] θ' s)
  have hEwc : ContinuousOn Ew (Icc 0 t) :=
    theta_energy_continuousOn (u := fun s x => θ s x - θ' s x) (hθ.1.sub hθ'.1) ht
  have hEc : ContinuousOn (wEnergy [] θ') (Icc 0 t) := wEnergy_continuousOn hθ'.1 [] ht
  have hΦc : ContinuousOn Φ (Icc 0 t) := hEwc.sub (continuousOn_const.mul
    (continuousOn_const.sub hEc))
  have hder : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivAt Φ
      ((-2 * κ * (∫ x in unitCube,
          vecNormSq (spaceGrad (fun y => θ s y - θ' s y) x)) -
        2 * (κ - κ') * (∫ x in unitCube,
          vecDot (spaceGrad (fun y => θ s y - θ' s y) x) (spaceGrad (θ' s) x))) -
        c * (0 - (-2 * κ' * gradE θ' s))) s := by
    intro s hs
    have h1 := diff_energy_hasDerivAt hΨ hθ hθ' hs.1
    have h2 := hasDerivAt_E hΨ hθ' hs.1
    exact h1.sub ((hasDerivAt_const s (wEnergy [] θ' 0)).sub h2 |>.const_mul c)
  have hanti : AntitoneOn Φ (Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hΦc ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hder s hs).deriv]
      have hsm : ContDiff ℝ (⊤ : ℕ∞) (θ s) := classicalSmooth_slice_nonneg hθ.1 hs.1.le
      have hsm' : ContDiff ℝ (⊤ : ℕ∞) (θ' s) := classicalSmooth_slice_nonneg hθ'.1 hs.1.le
      have hy := young_integral (f := fun y => θ s y - θ' s y) (h := θ' s) (hsm.sub hsm')
        hsm' (δ := κ - κ') hκ
      have hB : gradE θ' s = ∫ x in unitCube, vecNormSq (spaceGrad (θ' s) x) := rfl
      have hcc : c * (2 * κ') = (κ - κ') ^ 2 / (2 * κ) := by
        rw [hc]; field_simp; ring
      have : c * (0 - (-2 * κ' * gradE θ' s)) = (κ - κ') ^ 2 / (2 * κ) * gradE θ' s := by
        rw [← hcc]; ring
      rw [this, hB]
      linarith
  have hΦt : Φ t ≤ Φ 0 := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  have hΦ0 : Φ 0 = 0 := by
    simp only [Φ, Ew, h0]; ring
  have hE0 : wEnergy [] θ' 0 = l2NormSq θ₀ := by
    have : ∀ x, θ' 0 x = θ₀ x := hθ'.2.2.1
    simp [wEnergy, classicalWordDerivative,
      Classical.classicalWordDerivative, l2NormSq, this]
  have hEt : 0 ≤ wEnergy [] θ' t := integral_nonneg fun x => sq_nonneg _
  have : Ew t ≤ c * (wEnergy [] θ' 0 - wEnergy [] θ' t) := by
    have := hΦt
    simp only [Φ] at this
    linarith
  have hc0 : 0 ≤ c := by positivity
  calc Ew t ≤ c * (wEnergy [] θ' 0 - wEnergy [] θ' t) := this
    _ ≤ c * l2NormSq θ₀ := by
        rw [hE0]
        exact mul_le_mul_of_nonneg_left (by linarith) hc0

theorem twoDiffusivity : TwoDiffusivityContract := by
  intro Ψ hΨ κ κ' hκ hκ' θ₀ _ _ θ θ' hθ hθ' t ht
  have hE := diff_energy_le hΨ hκ hκ' hθ hθ' ht.1
  have hl : l2NormSq (fun x => θ t x - θ' t x) =
      ∫ x in unitCube, (θ t x - θ' t x) ^ 2 := rfl
  rw [hl]
  have hl0 : 0 ≤ l2NormSq θ₀ := integral_nonneg fun x => sq_nonneg _
  have hkk : 0 < κ * κ' := mul_pos hκ hκ'
  calc Real.sqrt (∫ x in unitCube, (θ t x - θ' t x) ^ 2)
      ≤ Real.sqrt ((κ - κ') ^ 2 / (4 * κ * κ') * l2NormSq θ₀) := Real.sqrt_le_sqrt hE
    _ = |κ - κ'| / (2 * Real.sqrt (κ * κ')) * Real.sqrt (l2NormSq θ₀) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity),
          Real.sqrt_sq_eq_abs]
        have : Real.sqrt (4 * κ * κ') = 2 * Real.sqrt (κ * κ') := by
          rw [mul_assoc, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
        rw [this]

end AVenhance.Infra.FullTheorem.NoSelectionInputs
