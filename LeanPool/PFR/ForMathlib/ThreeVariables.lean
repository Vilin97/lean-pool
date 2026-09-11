/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.Independence.Basic
public import LeanPool.ZhangYeungInequality.PFR.ForMathlib.Pair

/-!
# Consequences of three-way independence
-/

open scoped ZhangYeungPFR

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.iIndepFun

variable {Ω : Type*} [MeasureSpace Ω]
  {G : Type*} [hG : MeasurableSpace G]

variable {Z₁ Z₂ Z₃ : Ω → G} (h_indep : iIndepFun ![Z₁, Z₂, Z₃])

include h_indep





public
lemma reindex_three_bac :
    iIndepFun ![Z₂, Z₁, Z₃] := by
  let σ : Fin 3 ≃ Fin 3 :=
  { toFun := ![1, 0, 2]
    invFun := ![1, 0, 2]
    left_inv i := by fin_cases i <;> rfl
    right_inv i := by fin_cases i <;> rfl }
  refine .of_precomp σ.symm.surjective ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl







private abbrev κ : Fin 2 → Type
  | 0 => Fin 1
  | 1 => Fin 2

private def κ_equiv : (Σ i, κ i) ≃ Fin 3 where
  toFun := fun x ↦ match x with
    | Sigma.mk 0 _ => 0
    | Sigma.mk 1 ⟨0, _⟩ => 1
    | Sigma.mk 1 ⟨1, _⟩ => 2
  invFun := ![Sigma.mk 0 ⟨0, zero_lt_one⟩,
    Sigma.mk 1 ⟨0, zero_lt_two⟩, Sigma.mk 1 ⟨1, one_lt_two⟩]
  left_inv := by rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl
  right_inv i := by fin_cases i <;> rfl

private instance fintype_kappa : ∀ (i : Fin 2), Fintype (κ i)
  | 0 | 1 => inferInstanceAs (Fintype (Fin _))

variable (G) in
private abbrev self_or_prod : Fin 2 → Type _
  | 0 => G
  | 1 => G × G

public
lemma pair_last_of_three
    (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) (hZ₃ : Measurable Z₃) :
    IndepFun Z₁ (⟨Z₂, Z₃⟩) := by
  have T := iIndepFun.pi' (m := fun _ _ ↦ hG) ?_ (h_indep.precomp κ_equiv.injective); swap
  · rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> assumption
  -- apply to this pair of independent variables the function mapping the latter pair (as
  -- a function on `Fin 2`) to the same pair, but in the product space sense.
  -- It retains independence, proving the conclusion.
  let phi_third : ∀ (i : Fin 2), (κ i → G) → (self_or_prod G i)
    | 0 => (fun f ↦ f ⟨0, zero_lt_one⟩)
    | 1 => (fun f ↦ (f ⟨0, zero_lt_two⟩, f ⟨1, one_lt_two⟩))
  let M i : MeasurableSpace (self_or_prod G i) := by match i with | 0 | 1 => infer_instance
  have := T.comp phi_third
  refine (this ?_).indepFun (i := 0) (j := 1) zero_ne_one
  intro i
  match i with
  | 0 | 1 => fun_prop

end ProbabilityTheory.iIndepFun
