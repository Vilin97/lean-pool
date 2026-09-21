/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPolarMetric
public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarMetricAssembly

/-! # The full derivative of the round polar parametrization -/

@[expose] public noncomputable section
open scoped Manifold

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The joint derivative of the explicit round parametrization is its radial
velocity plus its angular derivative. -/
theorem roundPolarCurve_joint_derivative {R : ℝ} (hR : R ≠ 0)
    (p q w : E) (r s : ℝ) :
    fderiv ℝ (fun z : E × ℝ => roundPolarCurve R p z.1 z.2) (q, r) (w, s) =
      s • ((-Real.sin (r / R)) • p + Real.cos (r / R) • q) +
        fderiv ℝ (fun y => roundPolarCurve R p y r) q w := by
  let Γ := fun z : E × ℝ => roundPolarCurve R p z.1 z.2
  have hd : DifferentiableAt ℝ Γ (q, r) := by
    dsimp [Γ, roundPolarCurve]
    fun_prop
  have hw : fderiv ℝ (fun y => Γ (y, r)) q w = fderiv ℝ Γ (q, r) (w, 0) := by
    have hi := hasFDerivAt_prodMk_left (𝕜 := ℝ) q r
    change fderiv ℝ (Γ ∘ fun y => (y, r)) q w = _
    rw [fderiv_comp q hd hi.differentiableAt, hi.fderiv]
    rfl
  have hr : fderiv ℝ (fun t => Γ (q, t)) r 1 = fderiv ℝ Γ (q, r) (0, 1) := by
    have hi := hasFDerivAt_prodMk_right (𝕜 := ℝ) q r
    change fderiv ℝ (Γ ∘ fun t => (q, t)) r 1 = _
    rw [fderiv_comp r hd hi.differentiableAt, hi.fderiv]
    rfl
  have hv : fderiv ℝ Γ (q, r) (0, 1) =
      (-Real.sin (r / R)) • p + Real.cos (r / R) • q := by
    rw [← hr]
    change fderiv ℝ (roundPolarCurve R p q) r 1 = _
    rw [(hasDerivAt_roundPolarCurve hR p q r).hasFDerivAt.fderiv]
    change (1 : ℝ) • ((-Real.sin (r / R)) • p + Real.cos (r / R) • q) = _
    exact one_smul ℝ _
  change fderiv ℝ Γ (q, r) (w, s) = _
  rw [polar_derivative_split, hv, ← hw]
  exact add_comm _ _

/-- The full round metric is evaluated on the actual joint derivative,
not merely on a separately specified radial-angular expression. -/
theorem roundPolarCurve_joint_metric {R : ℝ} (hR : R ≠ 0) (r : ℝ)
    (p q w v : E) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : inner ℝ p q = 0)
    (hpw : inner ℝ p w = 0) (hqw : inner ℝ q w = 0)
    (hpv : inner ℝ p v = 0) (hqv : inner ℝ q v = 0) (s t : ℝ) :
    let Γ := fun z : E × ℝ => roundPolarCurve R p z.1 z.2
    inner ℝ (fderiv ℝ Γ (q, r) (w, s)) (fderiv ℝ Γ (q, r) (v, t)) =
      s * t + R ^ 2 * Real.sin (r / R) ^ 2 * inner ℝ w v := by
  dsimp only
  rw [roundPolarCurve_joint_derivative hR, roundPolarCurve_joint_derivative hR]
  exact roundPolarCurve_full_metric R r p q w v hp hq hpq hpw hqw hpv hqv s t

/-- Curvature normalization gives exactly the coefficient of the constructed
unit-angular Obata product. -/
theorem roundPolarCurve_joint_metric_curvature {K : ℝ} (hK : 0 < K) (r : ℝ)
    (p q w v : E) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : inner ℝ p q = 0)
    (hpw : inner ℝ p w = 0) (hqw : inner ℝ q w = 0)
    (hpv : inner ℝ p v = 0) (hqv : inner ℝ q v = 0) (s t : ℝ) :
    let Γ := fun z : E × ℝ => roundPolarCurve (1 / Real.sqrt K) p z.1 z.2
    inner ℝ (fderiv ℝ Γ (q, r) (w, s)) (fderiv ℝ Γ (q, r) (v, t)) =
      (Real.sin (Real.sqrt K * r) ^ 2 / K) * inner ℝ w v + s * t := by
  have hh := roundPolarCurve_joint_metric (one_div_ne_zero (Real.sqrt_pos.mpr hK).ne')
    r p q w v hp hq hpq hpw hqw hpv hqv s t
  have hc : (1 / Real.sqrt K) ^ 2 = 1 / K := by
    rw [div_pow, one_pow, Real.sq_sqrt hK.le]
  have harg : r / (1 / Real.sqrt K) = Real.sqrt K * r := by
    simp [div_eq_mul_inv, mul_comm]
  simpa only [hc, harg, one_div_mul_eq_div,
    add_comm (s * t)] using hh

end LichnerowiczObata
