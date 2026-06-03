/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.ForMathlibFunctionsBoundedAtInfty
public import LeanPool.LeanModularForms.Modularforms.MDifferentiableFunProp
public import LeanPool.LeanModularForms.Modularforms.ForMathlibSlashActions
public import LeanPool.LeanModularForms.Modularforms.ForMathlibUpperHalfPlane
public import LeanPool.LeanModularForms.Modularforms.DimensionFormulas

/-! # JacobiTheta -/


@[expose] public section

/-!
# Jacobi theta functions

Define Jacobi theta functions Θ₂, Θ₃, Θ₄ and their fourth powers H₂, H₃, H₄.
Prove that H₂, H₃, H₄ are modualar forms of weight 2 and level Γ(2).
Also Jacobi identity: Θ₂^4 + Θ₄^4 = Θ₃^4.
-/

open scoped Real MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

/-- The `n`-th term of the Jacobi theta series `Θ₂`. -/
noncomputable def Θ₂Term (n : ℤ) (τ : ℍ) : ℂ := cexp (π * I * (n + 1 / 2 : ℂ) ^ 2 * τ)
/-- The `n`-th term of the Jacobi theta series `Θ₃`. -/
noncomputable def Θ₃Term (n : ℤ) (τ : ℍ) : ℂ := cexp (π * I * (n : ℂ) ^ 2 * τ)
/-- The `n`-th term of the Jacobi theta series `Θ₄`. -/
noncomputable def Θ₄Term (n : ℤ) (τ : ℍ) : ℂ := (-1) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ)
/-- The Jacobi theta function `Θ₂`. -/
noncomputable def Θ₂ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₂Term n τ
/-- The Jacobi theta function `Θ₃`. -/
noncomputable def Θ₃ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₃Term n τ
/-- The Jacobi theta function `Θ₄`. -/
noncomputable def Θ₄ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₄Term n τ
/-- The fourth power `Θ₂ ^ 4` of the theta function `Θ₂`. -/
noncomputable def H₂ (τ : ℍ) : ℂ := (Θ₂ τ) ^ 4
/-- The fourth power `Θ₃ ^ 4` of the theta function `Θ₃`. -/
noncomputable def H₃ (τ : ℍ) : ℂ := (Θ₃ τ) ^ 4
/-- The fourth power `Θ₄ ^ 4` of the theta function `Θ₄`. -/
noncomputable def H₄ (τ : ℍ) : ℂ := (Θ₄ τ) ^ 4

/-- Theta functions as specializations of jacobiTheta₂ -/
theorem Θ₂_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₂Term n τ = cexp (π * I * τ / 4) * jacobiTheta₂_term n (τ / 2) τ := by
  rw [Θ₂Term, jacobiTheta₂_term, ← Complex.exp_add]
  ring_nf

theorem Θ₂_as_jacobiTheta₂ (τ : ℍ) : Θ₂ τ = cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
  simp_rw [Θ₂, Θ₂_term_as_jacobiTheta₂_term, tsum_mul_left, jacobiTheta₂]

theorem Θ₃_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₃Term n τ = jacobiTheta₂_term n 0 τ := by
  simp [Θ₃Term, jacobiTheta₂_term]

theorem Θ₃_as_jacobiTheta₂ (τ : ℍ) : Θ₃ τ = jacobiTheta₂ (0 : ℂ) τ := by
  simp_rw [Θ₃, Θ₃_term_as_jacobiTheta₂_term, jacobiTheta₂]

theorem Θ₄_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₄Term n τ = jacobiTheta₂_term n (1 / 2 : ℂ) τ := by
  rw [Θ₄Term, jacobiTheta₂_term, ← exp_pi_mul_I, ← exp_int_mul, ← Complex.exp_add]
  ring_nf

theorem Θ₄_as_jacobiTheta₂ (τ : ℍ) : Θ₄ τ = jacobiTheta₂ (1 / 2 : ℂ) τ := by
  simp_rw [Θ₄, Θ₄_term_as_jacobiTheta₂_term, jacobiTheta₂]

section H_SlashInvariant

/-- Slash action of various elements on H₂, H₃, H₄ -/
lemma H₂_negI_action : (H₂ ∣[(2 : ℤ)] negI.1) = H₂ := modular_slash_negI_of_even H₂ (2: ℤ) even_two
lemma H₃_negI_action : (H₃ ∣[(2 : ℤ)] negI.1) = H₃ := modular_slash_negI_of_even H₃ (2: ℤ) even_two
lemma H₄_negI_action : (H₄ ∣[(2 : ℤ)] negI.1) = H₄ := modular_slash_negI_of_even H₄ (2: ℤ) even_two

/-- These three transformation laws follow directly from tsum definition. -/
lemma H₂_T_action : (H₂ ∣[(2 : ℤ)] T) = -H₂ := by
  ext x
  suffices hΘ₂ : Θ₂ ((1 : ℝ) +ᵥ x) = cexp (π * I / 4) * Θ₂ x by
    simp_rw [modular_slash_T_apply, Pi.neg_apply, H₂, hΘ₂, mul_pow, ← Complex.exp_nat_mul,
      mul_comm ((4 : ℕ) : ℂ), Nat.cast_ofNat, div_mul_cancel₀ (b := (4 : ℂ)) _ (by simp),
      Complex.exp_pi_mul_I, neg_one_mul]
  calc
  _ = ∑' (n : ℤ), cexp (π * I * (n + 1 / 2) ^ 2 * ((1 : ℝ) +ᵥ x)) := by
    simp_rw [Θ₂, Θ₂Term]
  _ = ∑' (n : ℤ), cexp (π * I / 4) * cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * x) := by
    apply tsum_congr fun b ↦ ?_
    rw [coe_vadd, ofReal_one]
    repeat rw [← Complex.exp_add]
    congr
    ring_nf
  _ = cexp (π * I / 4) * ∑' (n : ℤ), cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * x) := by
    rw [tsum_mul_left]
  _ = _ := by
    simp_rw [Θ₂, Θ₂Term]
    congr 1
    apply tsum_congr fun b ↦ ?_
    have : Even (b ^ 2 + b) := by
      convert Int.even_mul_succ_self b using 1
      ring_nf
    norm_cast
    rw [Complex.exp_add]
    rw [mul_comm (π * I), Complex.exp_int_mul, Complex.exp_pi_mul_I, this.neg_one_zpow, one_mul]

lemma H₃_T_action : (H₃ ∣[(2 : ℤ)] T) = H₄ := by
  ext x
  simp_rw [modular_slash_T_apply, H₃, H₄, Θ₃, Θ₄, Θ₃Term, Θ₄Term]
  congr 1
  apply tsum_congr fun b ↦ ?_
  rw [coe_vadd, ofReal_one, mul_add, Complex.exp_add, mul_one, mul_comm (π * I), ← Int.cast_pow,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]
  congr 1
  rcases Int.even_or_odd b with (hb | hb)
  · rw [hb.neg_one_zpow, Even.neg_one_zpow]
    simp [sq, hb]
  · rw [hb.neg_one_zpow, Odd.neg_one_zpow]
    simp [sq, hb]

lemma H₄_T_action : (H₄ ∣[(2 : ℤ)] T) = H₃ := by
  -- H₄|T = H₃|T^2 = Θ₂(0, z + 2) = Θ₂(0, z) = H₃
  ext x
  simp_rw [← H₃_T_action, modular_slash_T_apply, H₃, Θ₃_as_jacobiTheta₂, coe_vadd, ← add_assoc]
  norm_num
  rw [add_comm, jacobiTheta₂_add_right]

lemma H₂_T_inv_action : (H₂ ∣[(2 : ℤ)] T⁻¹) = -H₂ := by
  nth_rw 1 [← neg_eq_iff_eq_neg.mpr H₂_T_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₃_T_inv_action : (H₃ ∣[(2 : ℤ)] T⁻¹) = H₄ := by
  nth_rw 1 [← H₄_T_action, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₄_T_inv_action : (H₄ ∣[(2 : ℤ)] T⁻¹) = H₃ := by
  nth_rw 1 [← H₃_T_action, ← slash_mul, mul_inv_cancel, slash_one]

/-- Use α = T * T -/
lemma H₂_α_action : (H₂ ∣[(2 : ℤ)] α.1) = H₂ := by
  simp [α_eq_T_sq, sq, slash_mul, H₂_T_action]

lemma H₃_α_action : (H₃ ∣[(2 : ℤ)] α.1) = H₃ := by
  simp [α_eq_T_sq, sq, slash_mul, H₃_T_action, H₄_T_action]

lemma H₄_α_action : (H₄ ∣[(2 : ℤ)] α.1) = H₄ := by
  simp [α_eq_T_sq, sq, slash_mul, H₃_T_action, H₄_T_action]

/-- Use jacobiTheta₂_functional_equation -/
lemma H₂_S_action : (H₂ ∣[(2 : ℤ)] S) = -H₄ := by
  ext ⟨x, hx⟩
  have hx' : x ≠ 0 := by simp [Complex.ext_iff, hx.ne.symm]
  calc
  _ = cexp (-π * I / x) * jacobiTheta₂ (-1 / (2 * x)) (-1 / x) ^ 4 * x ^ (-2 : ℤ) := by
    rw [modular_slash_S_apply, H₂, Θ₂_as_jacobiTheta₂]
    simp only [inv_neg, mul_neg, mul_pow, ← Complex.exp_nat_mul, Nat.cast_ofNat, Int.reduceNeg,
      zpow_neg, neg_mul, mul_eq_mul_right_iff, inv_eq_zero]
    rw [mul_comm 4, div_mul_cancel₀ _ (by norm_num)]
    left
    congr 3
    · rw [← div_eq_mul_inv, neg_div]
    · rw [← one_div, neg_div, div_div, mul_comm, neg_div]
    · rw [← one_div, neg_div]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * (1 / (I / x) ^ ((1 : ℂ) / 2) * cexp (π * I / (4 * x)) * jacobiTheta₂ (1 / 2) x) ^ 4 := by
    rw [mul_right_comm, jacobiTheta₂_functional_equation]
    congr 4
    · ring_nf
    · congr 1
      rw [neg_mul, neg_div, one_div, neg_div, div_neg, neg_mul, neg_div, neg_neg]
      ring_nf
      simp [sq, ← mul_assoc, inv_mul_cancel_right₀ hx']
    · ring_nf; simp [hx']
    · ring_nf; simp [inv_inv]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * ((1 / (I / x) ^ ((1 : ℂ) / 2)) ^ 4 * cexp (π * I / (4 * x)) ^ 4
          * jacobiTheta₂ (1 / 2) x ^ 4) := by
    simp [mul_pow]
  _ = cexp (-π * I / x) * x ^ (-2 : ℤ)
        * ((1 / (I / x) ^ (2 : ℂ)) * cexp (π * I / (4 * x)) ^ 4 * jacobiTheta₂ (1 / 2) x ^ 4) := by
    congr 3
    simp only [div_pow, one_pow, ← cpow_mul_nat]
    ring_nf
  _ = cexp (-π * I / x) * (x ^ (-2 : ℤ) * (-x ^ (2 : ℤ)))
        * cexp (π * I / (4 * x)) ^ 4 * jacobiTheta₂ (1 / 2) x ^ 4 := by
    repeat rw [← mul_assoc]
    congr 4
    rw [cpow_ofNat, div_pow, one_div_div, I_sq, div_neg, div_one]
    rfl
  _ = -cexp (-π * I / x) * cexp (π * I / x) * jacobiTheta₂ (1 / 2) x ^ 4 := by
    rw [mul_neg, ← zpow_add₀ hx', neg_add_cancel, mul_neg, zpow_zero, mul_one]
    congr 2
    rw [← Complex.exp_nat_mul]
    ring_nf
  _ = -jacobiTheta₂ (1 / 2) x ^ 4 := by
    rw [neg_mul, ← Complex.exp_add, neg_mul (π : ℂ), neg_div, neg_add_cancel, Complex.exp_zero,
      neg_one_mul]
  _ = -H₄ ⟨x, hx⟩ := by
    simp [H₄, Θ₄_as_jacobiTheta₂]

lemma H₃_S_action : (H₃ ∣[(2 : ℤ)] S) = -H₃ := by
  ext x
  have hx' : (x : ℂ) ≠ 0 := by obtain ⟨x, hx⟩ := x; change x ≠ 0; simp [Complex.ext_iff, hx.ne.symm]
  have := jacobiTheta₂_functional_equation 0
  simp only [neg_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at this
  simp only [modular_slash_S_apply, H₃, inv_neg, Θ₃_as_jacobiTheta₂, Int.reduceNeg, zpow_neg,
    Pi.neg_apply]
  rw [this, mul_pow, neg_div, div_neg, neg_neg, one_div (x : ℂ)⁻¹, inv_inv,
    mul_right_comm, ← neg_one_mul (_ ^ 4)]
  congr
  rw [div_pow, ← cpow_mul_nat, mul_neg, neg_neg]
  ring_nf!
  rw [← mul_inv, cpow_ofNat, sq, ← mul_assoc, zpow_two]
  ring_nf!
  rw [inv_pow, inv_I, even_two.neg_pow, I_sq, mul_neg_one, inv_inv, neg_mul, inv_mul_cancel₀]
  exact pow_ne_zero _ hx'

lemma H₄_S_action : (H₄ ∣[(2 : ℤ)] S) = - H₂ := by
  rw [← neg_eq_iff_eq_neg.mpr H₂_S_action, neg_slash, ← slash_mul, modular_S_sq,
    ModularForm.slash_neg' _ _ (by decide), slash_one]

lemma H₂_S_action' (z : ℍ) : H₂ (S • z) = - z ^ 2 * H₄ z := by
    have h := congrFun H₂_S_action z
    simp only [SL_slash_apply, denom_S, zpow_neg, zpow_two, Pi.neg_apply] at h
    field_simp [ne_zero] at h ⊢
    exact h

lemma H₄_S_action' (z : ℍ) : H₄ (S • z) = - z ^ 2 * H₂ z := by
    have h := congrFun H₄_S_action z
    simp only [SL_slash_apply, denom_S, zpow_neg, zpow_two, Pi.neg_apply] at h
    field_simp [ne_zero z] at h ⊢
    exact h

lemma H₂_S_inv_action : (H₂ ∣[(2 : ℤ)] S⁻¹) = -H₄ := by
  rw [← neg_eq_iff_eq_neg.mpr H₄_S_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₃_S_inv_action : (H₃ ∣[(2 : ℤ)] S⁻¹) = -H₃ := by
  nth_rw 1 [← neg_eq_iff_eq_neg.mpr H₃_S_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

lemma H₄_S_inv_action : (H₄ ∣[(2 : ℤ)] S⁻¹) = -H₂ := by
  rw [← neg_eq_iff_eq_neg.mpr H₂_S_action, neg_slash, ← slash_mul, mul_inv_cancel, slash_one]

/-- Use β = -S * α^(-1) * S -/
lemma H₂_β_action : (H₂ ∣[(2 : ℤ)] β.1) = H₂ := calc
  _ = (((H₂ ∣[(2 : ℤ)] negI.1) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α.1⁻¹) ∣[(2 : ℤ)] S := by
    simp [β_eq_negI_mul_S_mul_α_inv_mul_S, slash_mul]
  _ = _ := by
    rw [H₂_negI_action, H₂_S_action, neg_slash, neg_slash, α_eq_T_sq]
    simp [sq, slash_mul, H₄_T_inv_action, H₃_T_inv_action, H₄_S_action]

lemma H₃_β_action : (H₃ ∣[(2 : ℤ)] β.1) = H₃ := calc
  _ = (((H₃ ∣[(2 : ℤ)] negI.1) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α.1⁻¹) ∣[(2 : ℤ)] S := by
    simp [β_eq_negI_mul_S_mul_α_inv_mul_S, slash_mul]
  _ = _ := by
    rw [H₃_negI_action, H₃_S_action, neg_slash, neg_slash, α_eq_T_sq]
    simp [sq, slash_mul, H₄_T_inv_action, H₃_T_inv_action, H₃_S_action]

lemma H₄_β_action : (H₄ ∣[(2 : ℤ)] β.1) = H₄ := calc
  _ = (((H₄ ∣[(2 : ℤ)] negI.1) ∣[(2 : ℤ)] S) ∣[(2 : ℤ)] α.1⁻¹) ∣[(2 : ℤ)] S := by
    simp [β_eq_negI_mul_S_mul_α_inv_mul_S, slash_mul]
  _ = _ := by
    rw [H₄_negI_action, H₄_S_action, neg_slash, neg_slash, α_eq_T_sq]
    simp [sq, slash_mul, H₂_T_inv_action, H₂_S_action]

/-- H₂, H₃, H₄ are modular forms of weight 2 and level Γ(2) -/
noncomputable def H₂SIF : SlashInvariantForm (Γ 2) 2 where
  toFun := H₂
  slash_action_eq' := slashaction_generators_Γ2 H₂ (2 : ℤ) H₂_α_action H₂_β_action H₂_negI_action

/-- `H₃` as a slash-invariant form of weight 2 and level `Γ(2)`. -/
noncomputable def H₃SIF : SlashInvariantForm (Γ 2) 2 where
  toFun := H₃
  slash_action_eq' := slashaction_generators_Γ2 H₃ (2 : ℤ) H₃_α_action H₃_β_action H₃_negI_action

/-- `H₄` as a slash-invariant form of weight 2 and level `Γ(2)`. -/
noncomputable def H₄SIF : SlashInvariantForm (Γ 2) 2 where
  toFun := H₄
  slash_action_eq' := slashaction_generators_Γ2 H₄ (2 : ℤ) H₄_α_action H₄_β_action H₄_negI_action

@[simp] lemma H₂_SIF_coe : (H₂SIF : ℍ → ℂ) = H₂ := rfl

@[simp] lemma H₃_SIF_coe : (H₃SIF : ℍ → ℂ) = H₃ := rfl

@[simp] lemma H₄_SIF_coe : (H₄SIF : ℍ → ℂ) = H₄ := rfl

end H_SlashInvariant



section H_MDifferentiable

lemma H₂_SIF_MDifferentiable : MDiff H₂SIF := by
  intro τ
  suffices h_diff : DifferentiableAt ℂ (↑ₕH₂) (τ : ℂ) by
    have : (H₂ ∘ ↑ofComplex) ∘ UpperHalfPlane.coe = H₂SIF := by
      ext x
      simp [H₂SIF, ofComplex_apply]
    rw [← this]
    exact h_diff.mdifferentiableAt.comp τ τ.mdifferentiable_coe
  have hU : {z : ℂ | 0 < z.im} ∈ 𝓝 (τ : ℂ) := isOpen_upperHalfPlaneSet.mem_nhds τ.2
  let F : ℂ → ℂ := fun t => (cexp (((π : ℂ) * I / 4) * t) * jacobiTheta₂ (t / 2) t) ^ 4
  have hF : DifferentiableAt ℂ F (τ : ℂ) := by
    have h_exp : DifferentiableAt ℂ (fun t : ℂ => cexp ((π * I / 4) * t)) (τ : ℂ) := by
      have : DifferentiableAt ℂ (fun t : ℂ => (π * I / 4) * t) (τ : ℂ) :=
        (differentiableAt_id.const_mul ((π : ℂ) * I / 4))
      exact this.cexp
    have h_theta : DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) (τ : ℂ) := by
      let f : ℂ → ℂ × ℂ := fun t : ℂ => (t / 2, t)
      let g : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
      have hg : DifferentiableAt ℂ g (f (τ : ℂ)) := by
        simpa [f] using (hasFDerivAt_jacobiTheta₂ ((τ : ℂ) / 2) τ.2).differentiableAt
      have hf : DifferentiableAt ℂ f (τ : ℂ) :=
        (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
      simpa [f, g] using (DifferentiableAt.fun_comp' (τ : ℂ) hg hf)
    have h_prod : DifferentiableAt ℂ (fun t : ℂ => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t)
        (τ : ℂ) := h_exp.mul h_theta
    have h := h_prod.pow 4
    simp only [F]
    exact h
  have h_ev : F =ᶠ[𝓝 (τ : ℂ)] (↑ₕH₂) := by
    refine Filter.eventually_of_mem hU ?_
    intro z hz
    have h_arg : cexp (((π : ℂ) * I / 4) * z) = cexp (π * I * z / 4) := by
      have : ((π : ℂ) * I / 4) * z = (π * I * z) / 4 := by
        simp [div_eq_mul_inv, mul_comm, mul_assoc]
      simp [this]
    simp [F, H₂, Θ₂_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz, h_arg]
  exact (DifferentiableAt.congr_of_eventuallyEq hF h_ev.symm)

lemma H₃_SIF_MDifferentiable : MDiff H₃SIF := by
  rw [mdifferentiable_iff]
  simp only [H₃SIF, SlashInvariantForm.coe_mk]
  have hθ : DifferentiableOn ℂ (fun z => jacobiTheta₂ (0 : ℂ) z) {z | 0 < z.im} := by
    intro x hx
    exact (differentiableAt_jacobiTheta₂_snd 0 (by simpa using hx)).differentiableWithinAt
  have hθ4 : DifferentiableOn ℂ (fun z => (jacobiTheta₂ (0 : ℂ) z) ^ 4) {z | 0 < z.im} := by
    apply DifferentiableOn.pow
    intro x hx
    exact hθ x hx
  apply hθ4.congr
  intro _ hz
  simp [Function.comp, H₃, Θ₃_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz]

lemma H₄_SIF_MDifferentiable : MDiff H₄SIF := by
  intro τ
  have hθ : DifferentiableAt ℂ (fun z : ℂ => jacobiTheta₂ (1 / 2 : ℂ) z) (τ : ℂ) :=
    differentiableAt_jacobiTheta₂_snd (1 / 2 : ℂ) τ.2
  have hθpow : DifferentiableAt ℂ (fun z : ℂ => (jacobiTheta₂ (1 / 2 : ℂ) z) ^ 4) (τ : ℂ) :=
    (DifferentiableAt.pow hθ 4)
  have hMD_comp :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        ((fun z : ℂ => (jacobiTheta₂ (1 / 2 : ℂ) z) ^ 4) ∘ UpperHalfPlane.coe) τ :=
    hθpow.mdifferentiableAt.comp τ τ.mdifferentiable_coe
  have hMD_comp_within :
      MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ)
        ((fun z : ℂ => (jacobiTheta₂ (1 / 2 : ℂ) z) ^ 4) ∘ UpperHalfPlane.coe) Set.univ τ := by
    simpa [mdifferentiableWithinAt_univ] using hMD_comp
  have hfun_eq :
      ((fun z : ℂ => (jacobiTheta₂ (1 / 2 : ℂ) z) ^ 4) ∘ UpperHalfPlane.coe)
        = (H₄SIF : ℍ → ℂ) := by
    ext x
    simp [H₄SIF, H₄, Θ₄_as_jacobiTheta₂, Function.comp]
  have hMD_within :
      MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ) (⇑H₄SIF) Set.univ τ :=
    MDifferentiableWithinAt.congr hMD_comp_within (by
      intro x hx
      have := congrArg (fun f : ℍ → ℂ => f x) hfun_eq.symm
      simpa [Function.comp] using this) (by
      have := congrArg (fun f : ℍ → ℂ => f τ) hfun_eq.symm
      simpa [Function.comp] using this)
  simpa [mdifferentiableWithinAt_univ] using hMD_within

@[fun_prop]
lemma H₂_MDifferentiable : MDiff H₂ := by
  simpa [H₂SIF, SlashInvariantForm.coe_mk] using H₂_SIF_MDifferentiable

@[fun_prop]
lemma H₃_MDifferentiable : MDiff H₃ := by
  simpa [H₃SIF, SlashInvariantForm.coe_mk] using H₃_SIF_MDifferentiable

@[fun_prop]
lemma H₄_MDifferentiable : MDiff H₄ := by
  simpa [H₄SIF, SlashInvariantForm.coe_mk] using H₄_SIF_MDifferentiable

/-- Differentiability of `t ↦ jacobiTheta₂(t/2, t)` at points in the upper half-plane. -/
lemma differentiableAt_jacobiTheta₂_half (τ : ℍ) :
    DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) ↑τ := by
  let f : ℂ → ℂ × ℂ := fun t => (t / 2, t)
  have hf : DifferentiableAt ℂ f ↑τ :=
    (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
  have hg : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (f ↑τ) := by
    simpa [f] using (hasFDerivAt_jacobiTheta₂ ((τ : ℂ) / 2) τ.2).differentiableAt
  have h := DifferentiableAt.comp (x := (τ : ℂ)) hg hf
  simp only [f, Function.comp_def] at h
  exact h

lemma Θ₂_MDifferentiable : MDiff Θ₂ := by
  intro τ
  have hΘ₂_diff : DifferentiableAt ℂ
      (fun t : ℂ => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t) (τ : ℂ) :=
    ((differentiableAt_id.const_mul ((π : ℂ) * I / 4)).cexp).mul
      (differentiableAt_jacobiTheta₂_half τ)
  have hMD := hΘ₂_diff.mdifferentiableAt.comp τ τ.mdifferentiable_coe
  have : (fun t : ℂ => cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t) ∘
      UpperHalfPlane.coe = Θ₂ := by
    ext x; simp only [Function.comp_apply, Θ₂_as_jacobiTheta₂]; ring_nf
  rwa [this] at hMD

end H_MDifferentiable



section H_isBoundedAtImInfty

variable (γ : SL(2, ℤ))

-- TODO: Isolate this somewhere
lemma jacobiTheta₂_term_half_apply (n : ℤ) (z : ℂ) :
    jacobiTheta₂_term n (z / 2) z = cexp (π * I * (n ^ 2 + n) * z) := by
  rw [jacobiTheta₂_term]
  ring_nf

lemma jacobiTheta₂_rel_aux (n : ℤ) (t : ℝ) :
    rexp (-π * (n + 1 / 2) ^ 2 * t)
      = rexp (-π * t / 4) * jacobiTheta₂_term n (I * t / 2) (I * t) := by
  rw [jacobiTheta₂_term_half_apply, ofReal_exp, ofReal_exp, ← Complex.exp_add, ofReal_mul]
  congr
  ring_nf
  simp
  ring_nf!

-- lemma Complex.norm_exp (z : ℂ) : ‖cexp z‖ = rexp z.re := by
-- simp [abs_exp]

lemma Complex.norm_exp_mul_I (z : ℂ) : ‖cexp (z * I)‖ = rexp (-z.im) := by
  simp [norm_exp]

theorem isBoundedAtImInfty_H₂ : IsBoundedAtImInfty H₂ := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, H₂, Θ₂]
  use (∑' n : ℤ, rexp (-π * ((n : ℝ) + 1 / 2) ^ 2)) ^ 4, 1
  intro z hz
  rw [norm_pow]
  gcongr
  calc
    _ = ‖∑' (n : ℤ), cexp (π * I * (n + 1 / 2) ^ 2 * z)‖ := rfl
    _ ≤ ∑' (n : ℤ), ‖cexp (π * I * (n + 1 / 2) ^ 2 * z)‖ := norm_tsum_le_tsum_norm ?_
    _ = ∑' (n : ℤ), ‖cexp (π * I * ((n + 1 / 2) ^ 2 * z : ℂ))‖ := by simp only [← mul_assoc]
    _ = ∑' (n : ℤ), ‖rexp (-π * (((n + 1 / 2) ^ 2 : ℝ) * z : ℂ).im)‖ := by
      apply tsum_congr fun b ↦ ?_
      have (z : ℂ) : ‖cexp z‖ = ‖cexp z.re‖ := by
        nth_rw 1 [← Complex.re_add_im z, Complex.exp_add, norm_mul, norm_exp_ofReal_mul_I, mul_one]
      rw [this, mul_comm (π : ℂ), mul_assoc, I_mul_re, ← ofReal_exp,
        norm_real, Real.norm_eq_abs, im_ofReal_mul, neg_mul]
      simp
    _ = ∑' (n : ℤ), ‖rexp (-π * ((n + 1 / 2) ^ 2 : ℝ) * z.im)‖ := by
      simp_rw [im_ofReal_mul, UpperHalfPlane.im, ← mul_assoc]
    _ ≤ _ := Summable.tsum_le_tsum (fun b ↦ ?_) ?_ ?_
  · -- TODO: simplify and refactor this proof with subproof 3 & 4
    have (n : ℤ) : cexp (π * I * (n + 1 / 2) ^ 2 * z)
        = cexp (π * I * z / 4) * jacobiTheta₂_term n (z / 2) z := by
      rw [jacobiTheta₂_term_half_apply, ← Complex.exp_add]
      ring_nf
    simp_rw [this, ← smul_eq_mul (a := cexp _)]
    apply Summable.norm
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff, coe_im]
    linarith
  · rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_monotone
    repeat rw [neg_mul]
    apply neg_le_neg
    have : (b : ℝ) + 1 / 2 ≠ 0 := by
      intro hb
      rw [add_eq_zero_iff_eq_neg] at hb
      have : (2 * b : ℝ) = -1 := by simp [hb]
      norm_cast at this
      exact Int.not_odd_iff_even.mpr (even_two_mul b) (by rw [this]; simp)
    convert (mul_le_mul_iff_right₀ (mul_pos pi_pos (sq_pos_of_ne_zero this))).mpr hz using 1
    rw [mul_one]
  · apply Summable.norm
    apply summable_ofReal.mp
    simp_rw [jacobiTheta₂_rel_aux, ofReal_exp, ← smul_eq_mul (a := cexp _)]
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff, I_mul_im, ofReal_re]
    linarith
  · apply summable_ofReal.mp
    have (n : ℤ) := jacobiTheta₂_rel_aux n 1
    simp_rw [mul_one] at this
    simp_rw [this, ← smul_eq_mul]
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff]
    simp

-- We isolate this lemma out as it's also used in the proof for Θ₄
lemma isBoundedAtImInfty_H₃_aux (z : ℍ) (hz : 1 ≤ z.im) :
    ∑' (n : ℤ), ‖Θ₃Term n z‖ ≤ ∑' (n : ℤ), rexp (-π * n ^ 2) := by
  have h_rw (z : ℍ) (n : ℤ) : -(π * n ^ 2 * z : ℂ).im = -π * n ^ 2 * z.im := by
    rw [mul_assoc, im_ofReal_mul, ← Int.cast_pow, ← ofReal_intCast, im_ofReal_mul]
    simp [← mul_assoc]
  have h_sum (z : ℍ) : Summable fun n : ℤ ↦ rexp (-π * n ^ 2 * z.im) := by
    have := (summable_jacobiTheta₂_term_iff 0 z).mpr z.2
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add, mul_right_comm _ I, norm_exp_mul_I, h_rw]
      at this
    simpa using summable_ofReal.mp this
  calc
    _ = ∑' (n : ℤ), ‖cexp (π * (n : ℂ) ^ 2 * z * I)‖ := by simp_rw [Θ₃Term, mul_right_comm _ I]
    _ = ∑' (n : ℤ), rexp (-π * (n : ℂ) ^ 2 * z).im := by simp_rw [Complex.norm_exp_mul_I]; simp
    _ = ∑' (n : ℤ), rexp (-π * (n : ℝ) ^ 2 * z.im) := by
      congr with n
      rw [← ofReal_neg, ← coe_im, ← im_ofReal_mul]
      simp
    _ ≤ _ := Summable.tsum_le_tsum (fun b ↦ ?_) ?_ ?_
  · apply exp_monotone
    simp only [neg_mul, neg_le_neg_iff]
    exact le_mul_of_one_le_right (by positivity) hz
  · exact h_sum z
  · simpa using h_sum UpperHalfPlane.I

theorem isBoundedAtImInfty_H₃ : IsBoundedAtImInfty H₃ := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, H₃, Θ₃]
  use (∑' n : ℤ, rexp (-π * n ^ 2)) ^ 4, 1
  intro z hz
  rw [norm_pow]
  gcongr
  -- rw [← ]
  apply (norm_tsum_le_tsum_norm ?_).trans (isBoundedAtImInfty_H₃_aux z hz)
  simp_rw [Θ₃_term_as_jacobiTheta₂_term]
  apply Summable.norm
  rw [summable_jacobiTheta₂_term_iff]
  exact z.2

theorem isBoundedAtImInfty_H₄ : IsBoundedAtImInfty H₄ := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, H₄, Θ₄]
  use (∑' n : ℤ, rexp (-π * n ^ 2)) ^ 4, 1
  intro z hz
  rw [norm_pow]
  gcongr
  calc
    _ ≤ ∑' (n : ℤ), ‖Θ₄Term n z‖ := norm_tsum_le_tsum_norm ?_
    _ = ∑' (n : ℤ), ‖Θ₃Term n z‖ := by congr with n; simp [Θ₄Term, Θ₃Term]
    _ ≤ _ := isBoundedAtImInfty_H₃_aux z hz
  simp_rw [Θ₄_term_as_jacobiTheta₂_term]
  apply Summable.norm
  rw [summable_jacobiTheta₂_term_iff]
  exact z.2

theorem isBoundedAtImInfty_H_slash : IsBoundedAtImInfty (H₂ ∣[(2 : ℤ)] γ)
      ∧ IsBoundedAtImInfty (H₃ ∣[(2 : ℤ)] γ) ∧ IsBoundedAtImInfty (H₄ ∣[(2 : ℤ)] γ) := by
  apply Subgroup.closure_induction_left (s := {S, T, ↑negI})
      (p := fun γ _ ↦ IsBoundedAtImInfty (H₂ ∣[(2 : ℤ)] γ) ∧ IsBoundedAtImInfty (H₃ ∣[(2 : ℤ)] γ)
        ∧ IsBoundedAtImInfty (H₄ ∣[(2 : ℤ)] γ))
  · simp [isBoundedAtImInfty_H₂, isBoundedAtImInfty_H₃, isBoundedAtImInfty_H₄]
  · intro x hx y _ h
    simp_rw [slash_mul]
    rcases hx with (rfl | rfl | rfl | _)
    · simp_rw [H₂_S_action, H₃_S_action, H₄_S_action, neg_slash, isBoundedAtImInfty_neg_iff]
      use h.right.right, h.right.left, h.left
    · simp_rw [H₂_T_action, H₃_T_action, H₄_T_action, neg_slash, isBoundedAtImInfty_neg_iff]
      use h.left, h.right.right, h.right.left
    · rw [SL_slash, H₂_negI_action, H₃_negI_action, H₄_negI_action]
      exact h
  · intro x hx y _ h
    simp_rw [slash_mul]
    rcases hx with (rfl | rfl | rfl | _)
    · simp_rw [H₂_S_inv_action, H₃_S_inv_action, H₄_S_inv_action, neg_slash,
        isBoundedAtImInfty_neg_iff]
      use h.right.right, h.right.left, h.left
    · simp_rw [H₂_T_inv_action, H₃_T_inv_action, H₄_T_inv_action, neg_slash,
        isBoundedAtImInfty_neg_iff]
      use h.left, h.right.right, h.right.left
    · rw [← Subgroup.coe_inv, modular_negI_inv, SL_slash,
        modular_slash_negI_of_even _ 2 (by decide)]
      rw [H₃_negI_action, H₄_negI_action]
      exact h
  · intro s hs
    simp_rw [Set.mem_setOf_eq, Set.mem_range] at hs
    obtain ⟨s, rfl⟩ := hs
    rw [Set.mem_iInter, SetLike.mem_coe]
    intro hs
    have hs2 : {S, T} ⊆ (s : Set (SL(2, ℤ))) := by
      apply subset_trans _ hs
      simp only [Set.singleton_subset_iff, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        Set.insert_subset_insert]
    simp only [top_le_iff.mp <| SL2Z_generate.symm ▸ (Subgroup.closure_le s).mpr hs2,
      Subgroup.mem_top]

theorem isBoundedAtImInfty_H₂_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (H₂ ∣[(2 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  exact hA.symm ▸ (isBoundedAtImInfty_H_slash A').left

theorem isBoundedAtImInfty_H₃_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (H₃ ∣[(2 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  exact hA.symm ▸ (isBoundedAtImInfty_H_slash A').right.left

theorem isBoundedAtImInfty_H₄_slash :
    ∀ A ∈ 𝒮ℒ, IsBoundedAtImInfty (H₄ ∣[(2 : ℤ)] (A : GL (Fin 2) ℝ)) := by
  intro A ⟨A', hA⟩
  exact hA.symm ▸ (isBoundedAtImInfty_H_slash A').right.right

end H_isBoundedAtImInfty

/-- `H₂` as a modular form of weight 2 and level `Γ(2)`. -/
noncomputable def H₂MF : ModularForm (Γ 2) 2 := {
  H₂SIF with
  holo' := H₂_SIF_MDifferentiable
  bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₂_slash
}

/-- `H₃` as a modular form of weight 2 and level `Γ(2)`. -/
noncomputable def H₃MF : ModularForm (Γ 2) 2 := {
  H₃SIF with
  holo' := H₃_SIF_MDifferentiable
  bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₃_slash
}

/-- `H₄` as a modular form of weight 2 and level `Γ(2)`. -/
noncomputable def H₄MF : ModularForm (Γ 2) 2 := {
  H₄SIF with
  holo' := H₄_SIF_MDifferentiable
  bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₄_slash
}

@[simp] lemma H₂_MF_coe : (H₂MF : ℍ → ℂ) = H₂ := rfl

@[simp] lemma H₃_MF_coe : (H₃MF : ℍ → ℂ) = H₃ := rfl

@[simp] lemma H₄_MF_coe : (H₄MF : ℍ → ℂ) = H₄ := rfl

/-!
## Jacobi identity

The Jacobi identity states H₂ + H₄ = H₃ (equivalently Θ₂⁴ + Θ₄⁴ = Θ₃⁴).
This is blueprint Lemma 6.41, proved via dimension vanishing for weight 4 cusp forms.

The proof strategy:
1. Define g := H₂ + H₄ - H₃ and f := g²
2. Show f is SL₂(ℤ)-invariant (weight 4, level 1) via S/T invariance
3. Show f vanishes at i∞ (is a cusp form)
4. Apply cusp form vanishing: dim S₄(Γ₁) = 0
5. From g² = 0 conclude g = 0

The S/T slash action lemmas are proved here. The full proof requiring
asymptotics (atImInfty) is in AtImInfty.lean to avoid circular imports.
-/

section JacobiIdentity

/-- The difference g := H₂ + H₄ - H₃ -/
noncomputable def jacobiG : ℍ → ℂ := H₂ + H₄ - H₃

/-- The squared difference f := g² -/
noncomputable def jacobiF : ℍ → ℂ := jacobiG ^ 2

/-- S-action on g: g|[2]S = -g -/
lemma jacobi_g_S_action : (jacobiG ∣[(2 : ℤ)] S) = -jacobiG := by
  change ((H₂ + H₄ - H₃) ∣[(2 : ℤ)] S) = -(H₂ + H₄ - H₃)
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_S_action, H₃_S_action, H₄_S_action]
  ext z
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/-- T-action on g: g|[2]T = -g -/
lemma jacobi_g_T_action : (jacobiG ∣[(2 : ℤ)] T) = -jacobiG := by
  change ((H₂ + H₄ - H₃) ∣[(2 : ℤ)] T) = -(H₂ + H₄ - H₃)
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_T_action, H₃_T_action, H₄_T_action]
  ext z
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/-- Rewrite jacobiF as a pointwise product -/
lemma jacobi_f_eq_mul : jacobiF = jacobiG * jacobiG := by
  ext
  simp [jacobiF, sq]

/-- S-invariance of f: f|[4]S = f, because g|[2]S = -g. -/
lemma jacobi_f_S_action : (jacobiF ∣[(4 : ℤ)] S) = jacobiF := by
  -- simp only needed: lemmas must be applied in order (not a terminal simp)
  simp only [jacobi_f_eq_mul, show (4 : ℤ) = 2 + 2 by norm_num,
    mul_slash_SL2 2 2 S _ _, jacobi_g_S_action, neg_mul_neg]

/-- T-invariance of f: f|[4]T = f, because g|[2]T = -g. -/
lemma jacobi_f_T_action : (jacobiF ∣[(4 : ℤ)] T) = jacobiF := by
  -- simp only needed: lemmas must be applied in order (not a terminal simp)
  simp only [jacobi_f_eq_mul, show (4 : ℤ) = 2 + 2 by norm_num,
    mul_slash_SL2 2 2 T _ _, jacobi_g_T_action, neg_mul_neg]

/-- Full SL₂(ℤ) invariance of f with weight 4 -/
lemma jacobi_f_SL2Z_invariant : ∀ γ : SL(2, ℤ), jacobiF ∣[(4 : ℤ)] γ = jacobiF :=
  slashaction_generators_SL2Z jacobiF 4 jacobi_f_S_action jacobi_f_T_action

/-- jacobiF as a SlashInvariantForm of weight 4 and level Γ(1) -/
noncomputable def jacobiFSIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 4 where
  toFun := jacobiF
  slash_action_eq' := slashaction_generators_GL2R jacobiF 4 jacobi_f_S_action jacobi_f_T_action

/-- jacobiG is holomorphic (MDifferentiable) since H₂, H₃, H₄ are -/
lemma jacobi_g_MDifferentiable : MDiff jacobiG := by unfold jacobiG; fun_prop

/-- jacobiF is holomorphic (MDifferentiable) since jacobiG is -/
lemma jacobi_f_MDifferentiable : MDiff jacobiF := by
  unfold jacobiF
  have _ := jacobi_g_MDifferentiable
  fun_prop

/-- jacobiFSIF is holomorphic -/
lemma jacobi_f_SIF_MDifferentiable : MDiff jacobiFSIF := jacobi_f_MDifferentiable

end JacobiIdentity

/-!
## Limits at infinity

We prove the limit of Θᵢ(z) and Hᵢ(z) as z tends to i∞. This is used to prove the Jacobi identity.
-/

theorem jacobiTheta₂_half_mul_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ (x / 2) x) atImInfty (𝓝 2) := by
  simp_rw [jacobiTheta₂, jacobiTheta₂_term]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun z (n : ℤ) ↦ cexp (2 * π * I * n * (z / 2) + π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := Set.indicator {-1, 0} 1)
    (bound := fun n : ℤ ↦ rexp (π / 4) * rexp (-π * ((n : ℝ) + 1 / 2) ^ 2)) ?_ ?_ ?_
  · simp [← tsum_subtype]
  · -- TODO: merge this with proof of isBoundedAtImInfty_H₂
    apply summable_ofReal.mp
    have (n : ℤ) := jacobiTheta₂_rel_aux n 1
    simp_rw [mul_one] at this
    simp_rw [ofReal_mul, this, ← smul_eq_mul]
    apply Summable.const_smul
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff]
    simp
  · intro n
    have : n = -1 ∨ n = 0 ∨ n ∉ ({-1, 0} : Set ℤ) := by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rcases this with (rfl | rfl | hn) <;> ring_nf
    · simp
    · simp
    · simp only [hn, not_false_eq_true, Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have h₁ (n : ℤ) (z : ℂ) : (π * I * n * z + π * I * n ^ 2 * z) = π * (n + n ^ 2) * z * I := by
        ring_nf
      have h_base' : rexp (-π) ^ ((n : ℝ) + n ^ 2) < 1 := by
        apply Real.rpow_lt_one
        · positivity
        · apply Real.exp_lt_one_iff.mpr (by simp only [Left.neg_neg_iff]; positivity)
        convert_to 0 < ((n * (n + 1) : ℤ) : ℝ)
        · push_cast
          ring_nf
        · apply Int.cast_pos.mpr
          by_cases hn' : 0 < n
          · apply mul_pos hn' (by omega)
          · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
            exact mul_pos_of_neg_of_neg (by omega) (by omega)
      simp_rw [h₁, norm_exp_mul_I, mul_assoc, im_ofReal_mul, ← Int.cast_pow, ← Int.cast_add,
        ← ofReal_intCast, im_ofReal_mul, ← mul_assoc, Int.cast_add, Int.cast_pow, ← neg_mul,
        Real.exp_mul, coe_im]
      refine (tendsto_rpow_atTop_of_base_lt_one _ ?_ h_base').comp tendsto_im_atImInfty
      exact neg_one_lt_zero.trans (by positivity)
  · rw [eventually_atImInfty]
    use 1
    intro z hz k
    simp_rw [← Real.exp_add]
    ring_nf
    trans ‖cexp (((π * k + π * k ^ 2 : ℝ) * z) * I)‖
    · apply le_of_eq
      simpa [add_mul] using by ring_nf
    · rw [norm_exp_mul_I, im_ofReal_mul]
      have (n : ℤ) : 0 ≤ (n : ℝ) ^ 2 + n := by
        nth_rw 2 [← mul_one n]
        rw [sq, Int.cast_mul, Int.cast_one, ← mul_add]
        rcases lt_trichotomy (-1) n with (hn | rfl | hn)
        · apply mul_nonneg <;> norm_cast; omega
        · norm_num
        · apply mul_nonneg_of_nonpos_of_nonpos <;> norm_cast <;> omega
      simpa using le_mul_of_one_le_right
        (by rw [← mul_add, add_comm]; exact mul_nonneg Real.pi_nonneg (this k)) hz

theorem jacobiTheta₂_zero_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ 0 x) atImInfty (𝓝 1) := by
  simp_rw [jacobiTheta₂, jacobiTheta₂_term, mul_zero, zero_add]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦ cexp (π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := fun k ↦ if k = 0 then 1 else 0)
    (bound := fun n : ℤ ↦ rexp (-π * n ^ 2)) ?_ ?_ ?_
  · simp
  · apply summable_ofReal.mp
    have := (summable_jacobiTheta₂_term_iff 0 I).mpr (by simp)
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add, mul_right_comm _ I, mul_assoc, ← sq, I_sq,
      mul_neg_one, norm_exp, re_ofReal_mul, neg_re, mul_neg, ← neg_mul, ← ofReal_intCast,
      ← ofReal_pow, ofReal_re] at this
    exact this
  · intro k
    split_ifs with hk
    · subst hk
      simp
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [mul_right_comm _ I, norm_exp_mul_I, mul_assoc, im_ofReal_mul, ← ofReal_intCast,
        ← ofReal_pow, im_ofReal_mul, ← mul_assoc]
      simpa using tendsto_im_atImInfty.const_mul_atTop (by positivity)
  · rw [eventually_atImInfty]
    use 1, fun z hz k ↦ ?_
    simp_rw [mul_right_comm _ I, norm_exp_mul_I]
    simpa [← ofReal_intCast, ← ofReal_pow] using le_mul_of_one_le_right (by positivity) hz

theorem jacobiTheta₂_half_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ (1 / 2 : ℂ) x) atImInfty (𝓝 1) := by
  have hnorm (z : ℍ) (k : ℤ) :
      ‖cexp (2 * π * I * k * (1 / 2 : ℂ) + π * I * k ^ 2 * z)‖ = rexp (-π * k ^ 2 * z.im) := by
    simpa [jacobiTheta₂_term, coe_im] using
      (norm_jacobiTheta₂_term k (1 / 2 : ℂ) (z : ℂ))
  simp_rw [jacobiTheta₂, jacobiTheta₂_term]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦ cexp (2 * π * I * n * (1 / 2 : ℂ) + π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := fun k ↦ if k = 0 then 1 else 0)
    (bound := fun n : ℤ ↦ rexp (-π * n ^ 2)) ?_ ?_ ?_
  · simp
  · apply summable_ofReal.mp
    have := (summable_jacobiTheta₂_term_iff 0 I).mpr (by simp)
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add, mul_right_comm _ I, mul_assoc, ← sq, I_sq,
      mul_neg_one, norm_exp, re_ofReal_mul, neg_re, mul_neg, ← neg_mul, ← ofReal_intCast,
      ← ofReal_pow, ofReal_re] at this
    exact this
  · intro k
    split_ifs with hk
    · subst hk
      simp
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [hnorm]
      have hk2_pos : 0 < (k : ℝ) ^ 2 := by
        exact sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hk)
      exact (Real.tendsto_exp_atBot).comp
        (tendsto_im_atImInfty.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos, hk2_pos]))
  · rw [eventually_atImInfty]
    use 1, fun z hz k ↦ ?_
    rw [hnorm]
    have hcoef_nonpos : (-π * (k : ℝ) ^ 2) ≤ 0 := by
      nlinarith [Real.pi_pos, sq_nonneg (k : ℝ)]
    have hmul : (-π * (k : ℝ) ^ 2) * z.im ≤ (-π * (k : ℝ) ^ 2) * 1 := by
      exact mul_le_mul_of_nonpos_left hz hcoef_nonpos
    simpa using Real.exp_le_exp.mpr hmul

theorem Θ₂_tendsto_atImInfty : Tendsto Θ₂ atImInfty (𝓝 0) := by
  rw [funext Θ₂_as_jacobiTheta₂, ← zero_mul (2 : ℂ)]
  refine Tendsto.mul ?_ jacobiTheta₂_half_mul_apply_tendsto_atImInfty
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  -- simp_rw directly below fails
  have (z : ℍ) : ‖cexp (π * I * z / 4)‖ = rexp (-π * z.im / 4) := by
    rw [mul_right_comm, mul_div_right_comm, norm_exp_mul_I]
    simp [neg_div]
  simp_rw [this]
  exact (Real.tendsto_exp_atBot).comp <|
    -- TODO: tendsto_div_const_atBot_of_pos and its friends should be aliased under Tendsto.
    (tendsto_div_const_atBot_of_pos zero_lt_four).mpr
      (tendsto_im_atImInfty.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))

theorem Θ₃_tendsto_atImInfty : Tendsto Θ₃ atImInfty (𝓝 1) := by
  simpa [funext Θ₃_as_jacobiTheta₂] using jacobiTheta₂_zero_apply_tendsto_atImInfty

theorem Θ₄_tendsto_atImInfty : Tendsto Θ₄ atImInfty (𝓝 1) := by
  simpa [funext Θ₄_as_jacobiTheta₂] using jacobiTheta₂_half_apply_tendsto_atImInfty

theorem H₂_tendsto_atImInfty : Tendsto H₂ atImInfty (𝓝 0) := by
  convert Θ₂_tendsto_atImInfty.pow 4
  norm_num

theorem H₃_tendsto_atImInfty : Tendsto H₃ atImInfty (𝓝 1) := by
  convert Θ₃_tendsto_atImInfty.pow 4
  norm_num

theorem H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 1) := by
  convert Θ₄_tendsto_atImInfty.pow 4
  norm_num

/-!
## Jacobi identity proof

We prove that g := H₂ + H₄ - H₃ → 0 at i∞, hence f := g² → 0.
Combined with the dimension vanishing for weight 4 cusp forms, this proves the Jacobi identity.
-/

/-- The function g := H₂ + H₄ - H₃ tends to 0 at i∞.
    Since H₂ → 0, H₃ → 1, H₄ → 1, we have g → 0 + 1 - 1 = 0. -/
theorem jacobi_g_tendsto_atImInfty : Tendsto jacobiG atImInfty (𝓝 0) := by
  convert (H₂_tendsto_atImInfty.add H₄_tendsto_atImInfty).sub H₃_tendsto_atImInfty using 1
  norm_num

/-- The function f := g² tends to 0 at i∞. -/
theorem jacobi_f_tendsto_atImInfty : Tendsto jacobiF atImInfty (𝓝 0) := by
  convert jacobi_g_tendsto_atImInfty.pow 2 using 1
  norm_num

private noncomputable def jacobi_f_CF : CuspForm (Γ 1) 4 :=
  cuspFormOfSIFTendstoZero jacobiFSIF jacobi_f_SIF_MDifferentiable
    jacobi_f_tendsto_atImInfty

/-- jacobiF = 0 by dimension argument: weight-4 cusp forms vanish. -/
theorem jacobi_f_eq_zero : jacobiF = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 4 (by norm_num)) jacobi_f_CF)

/-- jacobiG = 0 as a function (from g² = 0) -/
theorem jacobi_g_eq_zero : jacobiG = 0 := by
  ext z
  simpa [jacobiF] using congr_fun jacobi_f_eq_zero z

/-- Jacobi identity: H₂ + H₄ = H₃ (Blueprint Lemma 6.41) -/
theorem jacobi_identity : H₂ + H₄ = H₃ := by
  ext z; simpa [jacobiG, sub_eq_zero] using congr_fun jacobi_g_eq_zero z

private noncomputable def theta_prod : ℍ → ℂ := H₂ * H₃ * H₄

private lemma theta_prod_S_action : (theta_prod ∣[(6 : ℤ)] S) = -theta_prod := by
  simp only [theta_prod, show (6 : ℤ) = (2 + 2) + 2 from by norm_num,
    mul_slash_SL2 (2 + 2) 2 S _ _, mul_slash_SL2 2 2 S _ _,
    H₂_S_action, H₃_S_action, H₄_S_action]
  ext z; simp [Pi.mul_apply, Pi.neg_apply]; ring

private lemma theta_prod_T_action : (theta_prod ∣[(6 : ℤ)] T) = -theta_prod := by
  simp only [theta_prod, show (6 : ℤ) = (2 + 2) + 2 from by norm_num,
    mul_slash_SL2 (2 + 2) 2 T _ _, mul_slash_SL2 2 2 T _ _,
    H₂_T_action, H₃_T_action, H₄_T_action]
  ext z; simp [Pi.mul_apply, Pi.neg_apply]; ring

private noncomputable def theta_prod_sq : ℍ → ℂ := fun z => (H₂ z * H₃ z * H₄ z) ^ 2

private lemma theta_prod_sq_eq_mul : theta_prod_sq = theta_prod * theta_prod := by
  ext z; simp [theta_prod_sq, theta_prod, sq, Pi.mul_apply]

private lemma theta_prod_sq_S_action : (theta_prod_sq ∣[(12 : ℤ)] S) = theta_prod_sq := by
  rw [theta_prod_sq_eq_mul, show (12 : ℤ) = 6 + 6 from by norm_num,
    mul_slash_SL2 6 6 S _ _, theta_prod_S_action, neg_mul_neg]

private lemma theta_prod_sq_T_action : (theta_prod_sq ∣[(12 : ℤ)] T) = theta_prod_sq := by
  rw [theta_prod_sq_eq_mul, show (12 : ℤ) = 6 + 6 from by norm_num,
    mul_slash_SL2 6 6 T _ _, theta_prod_T_action, neg_mul_neg]

private lemma theta_prod_sq_SL2Z_invariant :
    ∀ γ : SL(2, ℤ), theta_prod_sq ∣[(12 : ℤ)] γ = theta_prod_sq :=
  slashaction_generators_SL2Z theta_prod_sq 12
    theta_prod_sq_S_action theta_prod_sq_T_action

private lemma theta_prod_sq_MDifferentiable : MDiff theta_prod_sq := by
  change MDiff (fun z => (H₂ z * H₃ z * H₄ z) ^ 2)
  exact ((H₂_SIF_MDifferentiable.mul H₃_SIF_MDifferentiable).mul H₄_SIF_MDifferentiable).pow 2

private lemma theta_prod_sq_tendsto_atImInfty : Tendsto theta_prod_sq atImInfty (𝓝 0) := by
  change Tendsto (fun z => (H₂ z * H₃ z * H₄ z) ^ 2) atImInfty (𝓝 0)
  have : (0 : ℂ) = (0 * 1 * 1) ^ 2 := by norm_num
  rw [this]
  exact ((H₂_tendsto_atImInfty.mul H₃_tendsto_atImInfty).mul H₄_tendsto_atImInfty).pow 2

private noncomputable def theta_prod_sq_SIF :
    SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := theta_prod_sq
  slash_action_eq' := slashaction_generators_GL2R theta_prod_sq 12
    theta_prod_sq_S_action theta_prod_sq_T_action

private noncomputable def theta_prod_sq_CF : CuspForm (CongruenceSubgroup.Gamma 1) 12 :=
  cuspFormOfSIFTendstoZero theta_prod_sq_SIF theta_prod_sq_MDifferentiable
    theta_prod_sq_tendsto_atImInfty

private lemma theta_prod_sq_CF_apply (z : ℍ) :
    theta_prod_sq_CF z = theta_prod_sq z := rfl

/-- Transport a level-one modular-form rank fact from `𝒮ℒ` to the (definitionally distinct)
group `↑Γ(1)`; `subst` on a generalized group avoids the `IsArithmetic`/`HasDetOne` motive issue. -/
private lemma rank_modularForm_gammaOne {k : ℤ} {r : Cardinal}
    (h : Module.rank ℂ (ModularForm 𝒮ℒ k) = r) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = r := by
  have key : ∀ (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] [G.HasDetOne],
      G = (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) →
      Module.rank ℂ (ModularForm G k) = r →
      Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = r := by
    intro G _ _ hh hrank; subst hh; exact hrank
  exact key 𝒮ℒ CongruenceSubgroup.Gamma_one_coe_eq_SL.symm h

private lemma finrank_cuspform_12 :
    Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) 12) = 1 := by
  apply Module.finrank_eq_of_rank_eq
  rw [LinearEquiv.rank_eq (CuspFormsIsoModforms 12),
    show (12 - 12 : ℤ) = 0 from by norm_num]
  exact rank_modularForm_gammaOne ModularForm.levelOne_weight_zero_rank_one

private lemma theta_prod_sq_proportional :
    ∃ c : ℂ, c • Delta = theta_prod_sq_CF :=
  (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).mp finrank_cuspform_12 theta_prod_sq_CF

private lemma Θ₂_div_exp_tendsto :
    Tendsto (fun z : ℍ ↦ Θ₂ z / cexp (π * I * ↑z / 4)) atImInfty (nhds 2) := by
  simp_rw [Θ₂_as_jacobiTheta₂, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  exact jacobiTheta₂_half_mul_apply_tendsto_atImInfty

private lemma H₂_div_exp_tendsto :
    Tendsto (fun z : ℍ ↦ H₂ z / cexp (↑π * I * ↑z)) atImInfty (nhds 16) := by
  have h_eq : ∀ z : ℍ, H₂ z / cexp (↑π * I * ↑z) = (jacobiTheta₂ (↑z / 2) ↑z) ^ 4 := by
    intro z
    rw [H₂, Θ₂_as_jacobiTheta₂, mul_pow]
    have he : cexp (↑π * I * ↑z / 4) ^ 4 = cexp (↑π * I * ↑z) := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    rw [he, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  simp_rw [h_eq]
  have h16 : (2 : ℂ) ^ 4 = (16 : ℂ) := by norm_num
  rw [← h16]
  exact jacobiTheta₂_half_mul_apply_tendsto_atImInfty.pow 4

lemma Delta_eq_H₂_H₃_H₄ (τ : ℍ) :
    Delta τ = ((H₂ τ) * (H₃ τ) * (H₄ τ))^2 / (256 : ℂ) := by
  obtain ⟨c, hc⟩ := theta_prod_sq_proportional
  have hc_pw : ∀ z : ℍ, c * Delta z = theta_prod_sq z := by
    intro z
    have h := DFunLike.congr_fun hc z
    rw [show (c • Delta : CuspForm _ _) z = c * Delta z from rfl] at h
    rwa [theta_prod_sq_CF_apply] at h
  have hc_eq : c = 256 := by
    have hD_asymp : Tendsto (fun z : ℍ ↦ Delta z / cexp (2 * ↑π * I * ↑z))
        atImInfty (nhds 1) := by
      have h_eq : ∀ z : ℍ, Delta z / cexp (2 * ↑π * I * ↑z) =
          ∏' (n : ℕ), (1 - cexp (2 * ↑π * I * (↑n + 1) * ↑z)) ^ 24 := by
        intro z; rw [Delta_apply, Δ]
        rw [mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
      simp_rw [h_eq]; exact Delta_boundedfactor
    have hP_asymp : Tendsto (fun z : ℍ ↦ theta_prod_sq z / cexp (2 * ↑π * I * ↑z))
        atImInfty (nhds 256) := by
      have h_rewrite : ∀ z : ℍ, theta_prod_sq z / cexp (2 * ↑π * I * ↑z) =
          (H₂ z / cexp (↑π * I * ↑z)) ^ 2 * (H₃ z) ^ 2 * (H₄ z) ^ 2 := by
        intro z
        have hq : cexp (2 * ↑π * I * ↑z) = cexp (↑π * I * ↑z) ^ 2 := by
          rw [← Complex.exp_nat_mul]; ring_nf
        simp only [theta_prod_sq]
        rw [hq]; field_simp
      simp_rw [h_rewrite]
      have : (256 : ℂ) = 16 ^ 2 * 1 ^ 2 * 1 ^ 2 := by norm_num
      rw [this]
      exact ((H₂_div_exp_tendsto.pow 2).mul (H₃_tendsto_atImInfty.pow 2)).mul
        (H₄_tendsto_atImInfty.pow 2)
    have h_eq_fns : ∀ z : ℍ, c * (Delta z / cexp (2 * ↑π * I * ↑z)) =
        theta_prod_sq z / cexp (2 * ↑π * I * ↑z) := by
      intro z; rw [← mul_div_assoc, hc_pw]
    have hc_lim : Tendsto (fun z : ℍ ↦ c * (Delta z / cexp (2 * ↑π * I * ↑z)))
        atImInfty (nhds c) := by
      have := hD_asymp.const_mul c; rwa [mul_one] at this
    exact tendsto_nhds_unique (hc_lim.congr h_eq_fns) hP_asymp
  have h := hc_pw τ
  rw [hc_eq] at h
  simp only [theta_prod_sq] at h
  rw [eq_div_iff (show (256 : ℂ) ≠ 0 by norm_num), mul_comm]
  exact h

/-!
## Imaginary Axis Properties

Properties of theta functions when restricted to the positive imaginary axis z = I*t.
-/

section ImagAxisProperties

/-- Each term Θ₂Term n (I*t) has zero imaginary part for t > 0. -/
lemma Θ₂_term_imag_axis_real (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₂Term n ⟨I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₂Term
  change (cexp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (I * t))).im = 0
  have hexpr : Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (I * ↑t) =
      (-(Real.pi * ((n : ℝ) + 1/2) ^ 2 * t) : ℝ) := by
    have hI : I ^ 2 = -1 := I_sq
    push_cast
    ring_nf
    simp only [hI]
    ring
  rw [hexpr]
  exact exp_ofReal_im _

/-- `im` distributes over tsum when each term has zero imaginary part. -/
lemma Complex.im_tsum_eq_zero_of_im_eq_zero (f : ℤ → ℂ)
    (hf : Summable f) (him : ∀ n, (f n).im = 0) :
    (∑' n : ℤ, f n).im = 0 := by
  rw [Complex.im_tsum hf]
  simp [him]

/-- Θ₂(I*t) has zero imaginary part for t > 0. -/
lemma Θ₂_imag_axis_real (t : ℝ) (ht : 0 < t) :
    (Θ₂ ⟨I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₂
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  have hsum : Summable fun n : ℤ => Θ₂Term n z := by
    simp_rw [Θ₂_term_as_jacobiTheta₂_term]
    apply Summable.mul_left
    rw [summable_jacobiTheta₂_term_iff]
    exact z.im_pos
  apply Complex.im_tsum_eq_zero_of_im_eq_zero _ hsum
  intro n
  exact Θ₂_term_imag_axis_real n t ht

/-- `(-1 : ℂ)^n` has zero imaginary part for any integer n. -/
lemma neg_one_zpow_im_eq_zero (n : ℤ) : ((-1 : ℂ) ^ n).im = 0 := by
  rcases Int.even_or_odd n with hn | hn <;> (rw [hn.neg_one_zpow]; simp)

/-- Each term Θ₄Term n (I*t) has zero imaginary part for t > 0. -/
lemma Θ₄_term_imag_axis_real (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₄Term n ⟨I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₄Term
  change ((-1 : ℂ) ^ n * cexp (Real.pi * I * (n : ℂ) ^ 2 * (I * t))).im = 0
  -- Simplify the exponent: π * I * n² * (I*t) = -π * n² * t
  have hexpr : Real.pi * I * (n : ℂ) ^ 2 * (I * t) =
      (-(Real.pi * (n : ℝ) ^ 2 * t) : ℝ) := by
    have hI : I ^ 2 = -1 := I_sq
    push_cast
    ring_nf
    simp only [hI]
    ring
  rw [hexpr]
  -- Now we have (-1)^n * exp(real), both are real
  have hexp_real : (cexp (-(Real.pi * (n : ℝ) ^ 2 * t) : ℝ)).im = 0 := exp_ofReal_im _
  have hneg_one_real : ((-1 : ℂ) ^ n).im = 0 := neg_one_zpow_im_eq_zero n
  simp only [Complex.mul_im, hneg_one_real, hexp_real, mul_zero, zero_mul, add_zero]

/-- Θ₄(I*t) has zero imaginary part for t > 0. -/
lemma Θ₄_imag_axis_real (t : ℝ) (ht : 0 < t) :
    (Θ₄ ⟨I * t, by simp [ht]⟩).im = 0 := by
  unfold Θ₄
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  have hsum : Summable fun n : ℤ => Θ₄Term n z := by
    simp_rw [Θ₄_term_as_jacobiTheta₂_term]
    rw [summable_jacobiTheta₂_term_iff]
    exact z.im_pos
  apply Complex.im_tsum_eq_zero_of_im_eq_zero _ hsum
  intro n
  exact Θ₄_term_imag_axis_real n t ht

/--
`H₂(it)` is real for all `t > 0`.
Blueprint: Follows from the q-expansion having real coefficients.
Proof strategy: H₂ = Θ₂^4 where Θ₂(it) = ∑ₙ exp(-π(n+1/2)²t) is a sum of real
exponentials.
-/
@[fun_prop]
theorem H₂_imag_axis_real : ResToImagAxis.Real H₂ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₂]
  -- H₂ = Θ₂^4, and Θ₂(I*t) has zero imaginary part,
  -- so H₂(I*t) = Θ₂(I*t)^4 has zero imaginary part
  have hΘ₂_im := Θ₂_imag_axis_real t ht
  exact Complex.im_pow_eq_zero_of_im_eq_zero hΘ₂_im 4

/-- Each term Θ₂Term n (I*t) has positive real part equal to exp(-π(n+1/2)²t) for t > 0. -/
lemma Θ₂_term_imag_axis_re (n : ℤ) (t : ℝ) (ht : 0 < t) :
    (Θ₂Term n ⟨I * t, by simp [ht]⟩).re =
      Real.exp (-Real.pi * ((n : ℝ) + 1/2) ^ 2 * t) := by
  unfold Θ₂Term
  change (cexp (Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (I * t))).re = _
  have hexpr : Real.pi * I * ((n : ℂ) + 1 / 2) ^ 2 * (I * ↑t) =
      (-(Real.pi * ((n : ℝ) + 1/2) ^ 2 * t) : ℝ) := by
    have hI : I ^ 2 = -1 := I_sq
    push_cast
    ring_nf
    simp only [hI]
    ring
  rw [hexpr]
  rw [Complex.exp_ofReal_re]
  ring_nf

/-- Each term Θ₂Term n (I*t) has positive real part for t > 0. -/
lemma Θ₂_term_imag_axis_re_pos (n : ℤ) (t : ℝ) (ht : 0 < t) :
    0 < (Θ₂Term n ⟨I * t, by simp [ht]⟩).re := by
  rw [Θ₂_term_imag_axis_re n t ht]
  exact Real.exp_pos _

/-- Θ₂(I*t) has positive real part for t > 0.
Proof: Each term Θ₂Term n (I*t) = exp(-π(n+1/2)²t) is a positive real.
The sum of positive reals is positive. -/
lemma Θ₂_imag_axis_re_pos (t : ℝ) (ht : 0 < t) :
    0 < (Θ₂ ⟨I * t, by simp [ht]⟩).re := by
  -- Θ₂(it) = ∑ₙ exp(-π(n+1/2)²t) where each term is positive real
  -- The sum of positive terms (at least one nonzero) is positive
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  -- Summability of the complex series
  have hsum : Summable fun n : ℤ => Θ₂Term n z := by
    simp_rw [Θ₂_term_as_jacobiTheta₂_term]
    apply Summable.mul_left
    rw [summable_jacobiTheta₂_term_iff]
    exact z.im_pos
  -- Convert complex tsum to real part of tsum
  unfold Θ₂
  rw [Complex.re_tsum hsum]
  -- Summability of the real series
  have hsum_re : Summable fun n : ℤ => (Θ₂Term n z).re := by
    obtain ⟨x, hx⟩ := hsum
    exact ⟨x.re, Complex.hasSum_re hx⟩
  -- Each term is positive
  have hpos : ∀ n : ℤ, 0 < (Θ₂Term n z).re := fun n => Θ₂_term_imag_axis_re_pos n t ht
  -- Use that sum of positive terms is positive
  exact Summable.tsum_pos hsum_re (fun n => le_of_lt (hpos n)) 0 (hpos 0)

/--
`H₂(it) > 0` for all `t > 0`.
Blueprint: Lemma 6.43 - H₂ is positive on the imaginary axis.
Proof strategy: Each term exp(-π(n+1/2)²t) > 0, so Θ₂(it) > 0, hence H₂ = Θ₂^4 > 0.
-/
@[fun_prop]
theorem H₂_imag_axis_pos : ResToImagAxis.Pos H₂ := by
  constructor
  · exact H₂_imag_axis_real
  · intro t ht
    simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₂]
    -- H₂ = Θ₂^4 where Θ₂(it) is real and positive
    -- For z with z.im = 0 and z.re > 0, (z^4).re = (z.re)^4 > 0
    have hΘ₂_im := Θ₂_imag_axis_real t ht
    have hΘ₂_re_pos := Θ₂_imag_axis_re_pos t ht
    -- z^4 for z real equals z.re^4
    have hpow : (Θ₂ ⟨I * t, by simp [ht]⟩ ^ 4).re =
        (Θ₂ ⟨I * t, by simp [ht]⟩).re ^ 4 := by
      set z := Θ₂ ⟨I * t, by simp [ht]⟩ with hz_def
      have hz_real : z.im = 0 := hΘ₂_im
      -- When im = 0, z = z.re (as complex), so z^4 = (z.re)^4
      have hz_eq : z = (z.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hz_real]
      rw [hz_eq]
      norm_cast
    rw [hpow]
    exact pow_pos hΘ₂_re_pos 4

/--
`H₄(it)` is real for all `t > 0`.
Blueprint: Corollary 6.43 - follows from Θ₄ being real on the imaginary axis.
-/
@[fun_prop]
theorem H₄_imag_axis_real : ResToImagAxis.Real H₄ := by
  intro t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte, H₄]
  have hΘ₄_im := Θ₄_imag_axis_real t ht
  exact Complex.im_pow_eq_zero_of_im_eq_zero hΘ₄_im 4

/--
`H₄(it) > 0` for all `t > 0`.
Blueprint: Corollary 6.43 - H₄ is positive on the imaginary axis.

Proof strategy: Use the modular S-transformation relating H₄ and H₂.
From H₄_S_action: (H₄ ∣[2] S) = -H₂
From ResToImagAxis.SlashActionS: relates values at t and 1/t.
This gives H₂(i/t) = t² * H₄(it), so H₄(it) > 0 follows from H₂(i/t) > 0.
-/
@[fun_prop]
theorem H₄_imag_axis_pos : ResToImagAxis.Pos H₄ := by
  constructor
  · exact H₄_imag_axis_real
  · intro t ht
    -- Strategy: Use H₄_S_action and ResToImagAxis.SlashActionS to relate
    -- H₄ positivity to H₂ positivity via the modular S-transformation
    have h1t_pos : 0 < 1 / t := one_div_pos.mpr ht
    -- Apply SlashActionS at 1/t
    have hSlash := ResToImagAxis.SlashActionS H₄ 2 h1t_pos
    -- Use H₄_S_action: (H₄ ∣[2] S) = -H₂
    rw [H₄_S_action] at hSlash
    -- Now hSlash : (-H₂).resToImagAxis (1/t) = I^(-2) * (1/t)^(-2) * H₄.resToImagAxis t
    -- Simplify: I^(-2) = -1
    have hI_neg2 : (I : ℂ) ^ (-2 : ℤ) = -1 := by
      change (I ^ 2)⁻¹ = -1
      rw [I_sq]
      norm_num
    -- Simplify: (1/t)^(-2) = t^2
    have h1t_neg2 : ((1 / t : ℝ) : ℂ) ^ (-2 : ℤ) = (t : ℂ) ^ 2 := by
      have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
      simp only [one_div, ofReal_inv, zpow_neg]
      -- Goal: ((↑t)⁻¹ ^ 2)⁻¹ = ↑t ^ 2
      field_simp
    -- Simplify 1/(1/t) = t
    have h1_div_1t : 1 / (1 / t) = t := by field_simp
    -- The negation of resToImagAxis
    have hNeg : (-H₂).resToImagAxis (1 / t) = -(H₂.resToImagAxis (1 / t)) := by
      simp only [Function.resToImagAxis_apply, ResToImagAxis, h1t_pos, ↓reduceDIte, Pi.neg_apply]
    -- Substitute into hSlash
    rw [hNeg, hI_neg2, h1t_neg2, h1_div_1t] at hSlash
    -- hSlash : -(H₂.resToImagAxis (1/t)) = -1 * t^2 * H₄.resToImagAxis t
    -- Simplify: H₂.resToImagAxis (1/t) = t^2 * H₄.resToImagAxis t
    have hEq : H₂.resToImagAxis (1 / t) = (t : ℂ) ^ 2 * H₄.resToImagAxis t := by
      have h : -H₂.resToImagAxis (1 / t) = -(↑t ^ 2 * H₄.resToImagAxis t) := by
        simp only [neg_mul, one_mul] at hSlash ⊢
        exact hSlash
      exact neg_inj.mp h
    -- H₂.resToImagAxis (1/t).re > 0 from H₂_imag_axis_pos
    have hH₂_pos := H₂_imag_axis_pos.2 (1 / t) h1t_pos
    -- H₄.resToImagAxis t is real (im = 0)
    have hH₄_real := H₄_imag_axis_real t ht
    -- From hEq, extract real parts
    have hRe : (H₂.resToImagAxis (1 / t)).re = ((t : ℂ) ^ 2 * H₄.resToImagAxis t).re := by
      rw [hEq]
    -- Since t^2 is real positive and H₄.resToImagAxis t is real:
    -- (t^2 * H₄.resToImagAxis t).re = t^2 * (H₄.resToImagAxis t).re
    have hProd_re : ((t : ℂ) ^ 2 * H₄.resToImagAxis t).re =
        (t : ℝ) ^ 2 * (H₄.resToImagAxis t).re := by
      simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte] at hH₄_real ⊢
      simp only [sq, Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      ring_nf
      simp only [hH₄_real, mul_zero, sub_zero]
    -- Combine: t^2 * (H₄.resToImagAxis t).re > 0 and t^2 > 0 imply (H₄.resToImagAxis t).re > 0
    rw [hRe, hProd_re] at hH₂_pos
    have ht2_pos : 0 < (t : ℝ) ^ 2 := sq_pos_of_pos ht
    rw [mul_comm] at hH₂_pos
    exact pos_of_mul_pos_left hH₂_pos (le_of_lt ht2_pos)

end ImagAxisProperties
