/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs
import LeanPool.Clawristotle.Section3

/-!
# Polynomial Matching (Section 5)

Temperature is spatially constant, Lorentz force expansion, and polynomial
identity matching that constrains the Maxwellian parameters (a, b, c) from the
Vlasov transport equation.
-/

open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Helper lemma proved by Aristotle
-- ============================================================================

/-- Expansion of (E + v×B)·(b + 2cv) = E·b + v·(2cE + B×b).
    Uses (v×B)·v = 0 and (v×B)·b = v·(B×b).
    Proved by Aristotle (Harmonic). -/
lemma lorentz_force_expansion (E b B v : Fin 3 → ℝ) (c : ℝ) :
    dotProduct (E + cross v B) (b + (2 * c) • v) =
    dotProduct E b + dotProduct v ((2 * c) • E + cross B b) := by
  unfold cross dotProduct
  simp [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

-- ============================================================================
-- Section 5c: Polynomial Matching (Section 5 of tex)
-- Reference: Lemmas 13-17
-- ============================================================================

/-- Lemma 14 (Temperature is spatially constant).
    Reference: lem:T_constant

    Under the conditions of Lemma 13, ∇ₓc = 0, i.e., T(x) ≡ T∞ is a
    global constant.

    Proof: The O(|v|³) terms give (v · ∇c)|v|² = 0 for all v.
    Choosing v = t eᵢ for t → ∞ shows ∂ₓᵢ c = 0 for each i.
    Since c = -1/(2T), T is constant. -/
theorem temperature_constant
    (X : Type*)
    (c : X → ℝ)
    (gradX : (X → ℝ) → X → (Fin 3 → ℝ))
    (hcubic : ∀ x v, dotProduct v (gradX c x) * normSq v = 0) :
    ∀ x, gradX c x = 0 := by
  intro x; exact cubic_coeff_zero (gradX c x) (fun v => hcubic x v)

/-- Polynomial identity from the Vlasov equation.
    When f has Maxwellian form exp(a + b·v + c|v|²), the Landau operator vanishes
    (nullspace sufficiency), so the Vlasov equation reduces to collisionless
    transport. Expanding and dividing by f > 0 gives a polynomial in v.
    Reference: Lemma 13 (lem:polynomial_identity) in H-theorem-formal.tex. -/
lemma polynomial_identity_from_vlasov
    {X : Type*} [FlatTorus3 X]
    (f : X → (Fin 3 → ℝ) → ℝ) (E B : X → (Fin 3 → ℝ))
    (Ψ : ℝ → ℝ) (ν : ℝ)
    (_hf_pos : ∀ x v, 0 < f x v)
    (_hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (_hf_int : ∀ x, Integrable (f x))
    (_hΨ : ∀ r, 0 < Ψ r)
    (_hVlasov : ∀ x v,
      dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v) :
    ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
    FlatTorus3.IsSpatiallySmooth 2 a →
    (∀ j, FlatTorus3.IsSpatiallySmooth 2 (fun y => b y j)) →
    FlatTorus3.IsSpatiallySmooth 2 c →
    (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
    ∀ x v,
      dotProduct v (FlatTorus3.gradX c x) * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => b y j) x i)) +
      dotProduct v (FlatTorus3.gradX a x) +
      dotProduct (E x) (b x) +
      dotProduct v ((2 * c x) • E x + cross (B x) (b x)) = 0 := by
  intro a b c ha hb hc hform x v
  -- Step 1: c(x) < 0 for each x (from integrability of f)
  have hc_neg : ∀ x, c x < 0 := fun x =>
    analysis_gaussian_integrability (f x) (a x) (b x) (c x) (_hf_pos x) (_hf_int x) (hform x)
  -- Step 2: Q(f(x,·)) = 0 by nullspace sufficiency (f is Maxwellian)
  have hQ_zero : ∀ x v, LandauOperator Ψ (f x) v = 0 := fun x =>
    nullspace_sufficiency Ψ (f x) (a x) (b x) (c x) (hc_neg x) (hform x)
  -- Step 3: Vlasov simplifies to collisionless transport = 0
  have hTransport : dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) = 0 := by
    have h := _hVlasov x v
    rw [hQ_zero x v, mul_zero] at h
    exact h
  -- Step 4: Compute vGrad(f x)(v) = f(x,v) · (b x + 2c(x)·v)
  have hvGrad : vGrad (f x) v = f x v • (b x + (2 * c x) • v) := by
    have h1 := vGrad_exp_quadratic (a x) (b x) (c x) v
    conv_lhs => rw [show f x = (fun w => Real.exp (a x + dotProduct (b x) w + c x * normSq w))
      from funext (hform x)]
    rw [h1]
    congr 1
    exact (hform x v).symm
  -- Step 5: Compute gradX(f(·,v)) via chain rule + linearity
  have hgradX_i : ∀ i, FlatTorus3.gradX (fun y => f y v) x i =
      f x v * (FlatTorus3.gradX a x i +
        ∑ j : Fin 3, v j * FlatTorus3.gradX (fun y => b y j) x i +
        normSq v * FlatTorus3.gradX c x i) := by
    intro i
    have hf_eq : (fun y => f y v) =
        (fun y => Real.exp (a y + dotProduct (b y) v + c y * normSq v)) :=
      funext (fun y => hform y v)
    have hbv : FlatTorus3.IsSpatiallySmooth 2 (fun y => dotProduct (b y) v) := by
      have : (fun y => dotProduct (b y) v) =
          (fun y => v 0 * b y 0 + (v 1 * b y 1 + v 2 * b y 2)) := by
        ext y
        simp [dotProduct, Fin.sum_univ_three]
        ring
      rw [this]
      exact FlatTorus3.hDiff_add 2 _ _ (FlatTorus3.hDiff_smul 2 _ _ (hb 0))
        (FlatTorus3.hDiff_add 2 _ _
          (FlatTorus3.hDiff_smul 2 _ _ (hb 1)) (FlatTorus3.hDiff_smul 2 _ _ (hb 2)))
    have hcv : FlatTorus3.IsSpatiallySmooth 2 (fun y => c y * normSq v) := by
      have : (fun y => c y * normSq v) = (fun y => normSq v * c y) := funext (fun y => mul_comm _ _)
      rw [this]; exact FlatTorus3.hDiff_smul 2 _ _ hc
    have hexp_arg_diff : FlatTorus3.IsSpatiallySmooth 2
        (fun y => a y + dotProduct (b y) v + c y * normSq v) := by
      rw [show (fun y => a y + dotProduct (b y) v + c y * normSq v) =
          (fun y => a y + (dotProduct (b y) v + c y * normSq v)) from funext (fun y => by ring)]
      exact FlatTorus3.hDiff_add 2 _ _ ha (FlatTorus3.hDiff_add 2 _ _ hbv hcv)
    rw [show FlatTorus3.gradX (fun y => f y v) x i =
        FlatTorus3.gradX (fun y => Real.exp (a y + dotProduct (b y) v + c y * normSq v)) x i
      from by rw [hf_eq]]
    rw [FlatTorus3.hGradChainExp _ (FlatTorus3.hDiff_of_le _ (by decide) hexp_arg_diff)]
    rw [show Real.exp (a x + dotProduct (b x) v + c x * normSq v) = f x v from (hform x v).symm]
    congr 1
    -- Decompose gradX(a + b·v + c|v|²) using linearity
    rw [show (fun y => a y + dotProduct (b y) v + c y * normSq v) =
        (fun y => a y + (dotProduct (b y) v + c y * normSq v)) from funext (fun y => by ring)]
    rw [FlatTorus3.hGradAdd _ _
      (FlatTorus3.hDiff_of_le _ (by decide) ha)
      (FlatTorus3.hDiff_of_le _ (by decide)
        (FlatTorus3.hDiff_add 2 _ _ hbv hcv))]
    rw [FlatTorus3.hGradAdd _ _
      (FlatTorus3.hDiff_of_le _ (by decide) hbv)
      (FlatTorus3.hDiff_of_le _ (by decide) hcv)]
    rw [show (fun y => c y * normSq v) = (fun y => normSq v * c y) from funext (fun y => by ring)]
    rw [FlatTorus3.hGradScalarMul]
    rw [show (fun y => dotProduct (b y) v) =
        (fun y => v 0 * b y 0 + (v 1 * b y 1 + v 2 * b y 2))
        from funext (fun y => by simp [dotProduct, Fin.sum_univ_three]; ring)]
    rw [FlatTorus3.hGradAdd _ _
      (FlatTorus3.hDiff_of_le _ (by decide)
        (FlatTorus3.hDiff_smul 2 _ _ (hb 0)))
      (FlatTorus3.hDiff_of_le _ (by decide)
        (FlatTorus3.hDiff_add 2 _ _
          (FlatTorus3.hDiff_smul 2 _ _ (hb 1))
          (FlatTorus3.hDiff_smul 2 _ _ (hb 2))))]
    rw [FlatTorus3.hGradAdd _ _
      (FlatTorus3.hDiff_of_le _ (by decide)
        (FlatTorus3.hDiff_smul 2 _ _ (hb 1)))
      (FlatTorus3.hDiff_of_le _ (by decide)
        (FlatTorus3.hDiff_smul 2 _ _ (hb 2)))]
    rw [FlatTorus3.hGradScalarMul (v 0) (fun y => b y 0)]
    rw [FlatTorus3.hGradScalarMul (v 1) (fun y => b y 1)]
    rw [FlatTorus3.hGradScalarMul (v 2) (fun y => b y 2)]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    ring
  -- Step 6: Substitute into transport = 0 and factor out f > 0
  have hfv_pos : 0 < f x v := _hf_pos x v
  -- Rewrite gradX as dot product with v
  have hgradX_dot : dotProduct v (FlatTorus3.gradX (fun y => f y v) x) =
      f x v * (dotProduct v (FlatTorus3.gradX a x) +
        ∑ i : Fin 3, ∑ j : Fin 3, v i * v j * FlatTorus3.gradX (fun y => b y j) x i +
        dotProduct v (FlatTorus3.gradX c x) * normSq v) := by
    -- Expand dot products, sums over Fin 3, and substitute hgradX_i
    have h0 := hgradX_i 0
    have h1 := hgradX_i 1
    have h2 := hgradX_i 2
    simp only [dotProduct, Fin.sum_univ_three, normSq] at h0 h1 h2 ⊢
    rw [h0, h1, h2]; ring
  -- Rewrite vGrad term
  have hvGrad_dot : dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      f x v * (dotProduct (E x) (b x) +
        dotProduct v ((2 * c x) • E x + cross (B x) (b x))) := by
    rw [hvGrad, dotProduct_smul, lorentz_force_expansion, smul_eq_mul]
  -- Combine: transport = f(x,v) * (polynomial) = 0
  have hPoly : f x v * (dotProduct v (FlatTorus3.gradX c x) * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => b y j) x i)) +
      dotProduct v (FlatTorus3.gradX a x) +
      dotProduct (E x) (b x) +
      dotProduct v ((2 * c x) • E x + cross (B x) (b x))) = 0 := by
    have h := hTransport
    rw [hgradX_dot, hvGrad_dot] at h
    linarith
  -- Since f(x,v) > 0, the polynomial must be 0
  exact (mul_eq_zero.mp hPoly).resolve_left (ne_of_gt hfv_pos)

end VML
