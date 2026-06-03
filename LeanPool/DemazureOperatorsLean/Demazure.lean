/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Complex.Polynomial.Basic
import Init.System.IO

import Mathlib.Data.Complex.Basic

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.RingTheory.MvPolynomial.Basic

import Mathlib.Data.Finsupp.Defs

/-!
# LeanPool.DemazureOperatorsLean.Demazure
-/

noncomputable section
open MvPolynomial

namespace Demazure

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

/- In this file we define the Demazure operator directly as a function
  in the ring of multivariate polynomials -/

/- Prerequisites  -/

/-- The polynomial obtained by swapping the variables indexed by `i` and `j`. -/
def SwapVariablesFun (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) : (MvPolynomial (Fin n) ℂ) :=
  (renameEquiv ℂ (Equiv.swap i j)) p

@[simp]
lemma swap_variables_map_zero (i j : Fin n) : SwapVariablesFun i j 0 = 0 := by
  rw[SwapVariablesFun]
  have : (0 : MvPolynomial (Fin n) ℂ) = C 0 := by
    refine C_0.symm
  rw[this]
  exact rename_C (Equiv.swap i j) 0

@[simp]
lemma swap_variables_map_one {i j : Fin n} : SwapVariablesFun i j 1 = 1 := by
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_add {i j : Fin n} : ∀p q :
    MvPolynomial (Fin n) ℂ,
    SwapVariablesFun i j (p + q) = SwapVariablesFun i j p + SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_sub {i j : Fin n} : ∀p q :
    MvPolynomial (Fin n) ℂ,
    SwapVariablesFun i j (p - q) = SwapVariablesFun i j p - SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_mul {i j : Fin n} : ∀p q :
    MvPolynomial (Fin n) ℂ,
    SwapVariablesFun i j (p * q) = SwapVariablesFun i j p * SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

lemma swap_variables_mul' (i j : Fin n) : ∀p q :
    MvPolynomial (Fin n) ℂ,
    SwapVariablesFun i j (p * q) = SwapVariablesFun i j p * SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

lemma swap_variables_mul'' {i j : Fin n} {p q : MvPolynomial (Fin n) ℂ} :
 SwapVariablesFun i j (p * q) = SwapVariablesFun i j p * SwapVariablesFun i j q := by
  simp[SwapVariablesFun]

lemma swap_variables_add'' {i j : Fin n} {p q : MvPolynomial (Fin n) ℂ} :
 SwapVariablesFun i j (p + q) = SwapVariablesFun i j p + SwapVariablesFun i j q := by
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_commutes {i j : Fin n} : ∀r : ℂ, SwapVariablesFun i j (C r) = C r := by
  intro r
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_order_two {i j : Fin n} {p : MvPolynomial (Fin n) ℂ} :
  SwapVariablesFun i j (SwapVariablesFun i j p) = p := by
  rw [SwapVariablesFun, SwapVariablesFun, renameEquiv_apply, renameEquiv_apply, rename_rename]
  convert rename_id_apply (R := ℂ) p
  funext k
  simp

/-- The algebra equivalence swapping the variables indexed by `i` and `j`. -/
def SwapVariables (i : Fin n) (j : Fin n) :
    AlgEquiv ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) :=
  renameEquiv ℂ (Equiv.swap i j)

@[simp]
lemma swap_variables_apply (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) :
    SwapVariables i j p = SwapVariablesFun i j p := rfl

/-- The polynomial equation of the unit circle in two variables. -/
def circleEquation : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 + X 1 ^ 2 - C 1

example : circleEquation = SwapVariables 0 1 circleEquation := by
  simp [circleEquation, SwapVariables]
  ring

/- some more properties of swap_variables and others -/

lemma swap_variables_ne_zero (i j : Fin (n + 1)) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ, p ≠ 0 → SwapVariables i j p ≠ 0 := by
  intro p hp h
  apply hp
  rw[← map_zero (SwapVariables i j)] at h
  apply AlgEquiv.injective (SwapVariables i j)
  exact h

@[simp]
lemma swap_variables_first {i j : Fin (n + 1)} : SwapVariablesFun i j (X i) = X j := by
  simp [SwapVariablesFun]

lemma swap_variables_symmetrical {i j : Fin (n + 1)} {p : MvPolynomial (Fin (n + 1)) ℂ} :
  SwapVariablesFun i j p = SwapVariablesFun j i p := by
  simp [SwapVariablesFun, Equiv.swap_comm]

@[simp]
lemma swap_variables_second {i j : Fin (n + 1)} : SwapVariablesFun i j (X j) = X i := by
  simp [SwapVariablesFun]

@[simp]
lemma swap_variables_none {i j k : Fin (n + 1)} (h1 : k ≠ i) (h2 : k ≠ j) :
SwapVariablesFun i j (X k) = X k := by
  simp [SwapVariablesFun, h1, h2, Equiv.swap_apply_of_ne_of_ne]

lemma swap_variables_none' {i j k : Fin (n + 1)} {h1 : k ≠ i} {h2 : k ≠ j} :
SwapVariablesFun i j (X k) = X k := by
  simp [SwapVariablesFun, h1, h2, Equiv.swap_apply_of_ne_of_ne]

/- Some really specific and technical lemmas-/
lemma fin_succ_ne_fin_castSucc (i : Fin n) : Fin.succ i ≠ Fin.castSucc i := by
  apply Fin.val_ne_iff.mp
  dsimp
  norm_num

lemma wario_number_one {n : ℕ} {a : ℕ} {h : a < n} {a' : ℕ} {h' : a' < n} :
({ val := a, isLt := h } : Fin n) ≠ { val := a', isLt := h' } ↔ a ≠ a' := by
  rw[ne_eq]
  rw[ne_eq]
  apply not_iff_not.mpr
  exact Fin.mk_eq_mk


lemma i_ne_i_plus_1 {i : ℕ} {h : i < n + 1} {h' : i + 1 < n + 1} :
 ({ val := i, isLt := h } : Fin (n + 1)) ≠ { val := i + 1, isLt := h' } := by
  rw[wario_number_one]
  linarith

lemma demazure_denominator_not_null (i : Fin n) :
    (X (Fin.castSucc i) : MvPolynomial (Fin (n + 1)) ℂ) - X (Fin.succ i) ≠ 0 := by
  apply MvPolynomial.ne_zero_iff.mpr
  use Finsupp.single (Fin.succ i) 1
  rw[MvPolynomial.coeff_sub]
  rw[MvPolynomial.coeff_X]
  rw[MvPolynomial.coeff_X']
  have h : Finsupp.single (Fin.castSucc i) 1 ≠ Finsupp.single (Fin.succ i) 1 := by
    apply Finsupp.ne_iff.mpr
    use Fin.succ i
    simp[fin_succ_ne_fin_castSucc]
  rw [if_neg h]
  simp

/- Now we can use these to define the demazure numerator. We distinguish the variable x_i
 to perform division by (x_i - x_(i+1)) later (only univariable division is supported) -/

/-- The numerator used to define the Demazure operator in one distinguished variable. -/
def DemazureNumerator (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) :
    Polynomial (MvPolynomial (Fin n) ℂ) :=
  let i' : Fin (n + 1) := Fin.castSucc i
  let i'_plus_1 : Fin (n + 1) := Fin.succ i
  let numerator := p - SwapVariables i' i'_plus_1 p
  let numerator_X_i_at_start : MvPolynomial (Fin (n + 1)) ℂ := SwapVariables i' 0 numerator
  (finSuccEquiv ℂ n) numerator_X_i_at_start

lemma demazure_numerator_add (i : Fin n) : ∀ p q : MvPolynomial (Fin (n + 1)) ℂ,
  DemazureNumerator i (p + q) = DemazureNumerator i p + DemazureNumerator i q := by
  intro p q
  simp [DemazureNumerator, SwapVariables, map_add, sub_eq_add_neg]
  abel

lemma demazure_numerator_C_mul (i : Fin n) : ∀ (p : MvPolynomial (Fin (n + 1)) ℂ) (r : ℂ),
 DemazureNumerator i (C r * p) = Polynomial.C (C r) * DemazureNumerator i p := by
  intro p r
  simp only [DemazureNumerator, SwapVariables, map_mul, renameEquiv_apply, algHom_C,
    algebraMap_eq, sub_eq_add_neg, map_add, map_neg, rename_rename]
  rw [show (MvPolynomial.finSuccEquiv ℂ n) (C r : MvPolynomial (Fin (n + 1)) ℂ) =
    Polynomial.C (C r) by simp [MvPolynomial.finSuccEquiv_apply]]
  ring

-- Now we also define the denominator taking the variable x_i as the variable to divide by
/-- The monic denominator `X - X_i` used in the Demazure division step. -/
def DemazureDenominator (i : Fin n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let X_i : MvPolynomial (Fin n) ℂ := MvPolynomial.X i
  let denominator_X : Polynomial (MvPolynomial (Fin n) ℂ) := (Polynomial.X - Polynomial.C X_i)
  denominator_X

lemma demazure_denominator_ne_zero : ∀ i : Fin n, DemazureDenominator i ≠ 0 := by
  intro i
  simpa [DemazureDenominator] using Polynomial.X_sub_C_ne_zero (X i)

lemma demazure_denominator_monic : ∀ i : Fin n, Polynomial.Monic (DemazureDenominator i) := by
  intro i
  simpa [DemazureDenominator] using Polynomial.monic_X_sub_C (X i)

/- the division is exact so the demazure operator is well defined
(division by polynomials returns just the quotient) -/
lemma demazure_division_exact : ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
  (DemazureNumerator i p).modByMonic (DemazureDenominator i) = 0 := by
    intro i p
    simp only [DemazureNumerator, SwapVariables, renameEquiv_apply, map_sub,
      rename_rename, finSuccEquiv_apply, coe_eval₂Hom, DemazureDenominator,
      Polynomial.modByMonic_X_sub_C_eq_C_eval, Polynomial.eval_sub, polynomial_eval_eval₂]
    apply sub_eq_zero.mpr
    apply congr_arg Polynomial.C
    repeat
      rw[MvPolynomial.eval₂_rename]
    apply MvPolynomial.eval₂_congr
    intro j c _ _
    simp[Equiv.swap_apply_def]
    by_cases h1 : j = Fin.castSucc i
    · simp[h1, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]
    by_cases h2 : j = Fin.succ i
    · simp[h2, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]
    by_cases h3 : j = 0
    · subst h3
      simp[h1, h2]
    simp[h1, h2, h3]


/-- The Demazure operator as a function on multivariate polynomials. -/
def DemazureFun (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) : MvPolynomial (Fin (n + 1)) ℂ  :=
  let numerator := DemazureNumerator i p
  let denominator := DemazureDenominator i
  let division := numerator.divByMonic denominator
  let division_mv : MvPolynomial (Fin (n + 1)) ℂ := (AlgEquiv.symm (finSuccEquiv ℂ n)) division
  let i' : Fin (n + 1) := Fin.castSucc i
  SwapVariables i' 0 division_mv

/- Some auxiliary lemmas for the multivariate polynomial ring -/
lemma poly_mul_cancel {p q r : Polynomial (MvPolynomial (Fin n) ℂ)} (hr : r ≠ 0) :
    p = q ↔ (r * p) = (r * q) := by
  constructor
  · intro h
    exact congrArg (HMul.hMul r) h
  · intro h
    exact mul_left_cancel₀ hr h

lemma poly_cancel_left {p q r : MvPolynomial (Fin n) ℂ} (hr : r ≠ 0) :
    (r * p) = (r * q) → p = q := by
  intro h
  exact mul_left_cancel₀ hr h

lemma poly_div_cancel {p q r : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hr : Polynomial.Monic r) (hp : p %ₘ r = 0) (hq : q %ₘ r = 0) :
    p = q ↔ (p /ₘ r) = (q /ₘ r) := by
  constructor
  · intro h
    exact congrArg (fun x => x /ₘ r) h
  · intro h
    have div_p : p %ₘ r + r * (p /ₘ r) = p := Polynomial.modByMonic_add_div p r
    have div_q : q %ₘ r + r * (q /ₘ r) = q := Polynomial.modByMonic_add_div q r
    rw[hp, zero_add] at div_p
    rw[hq, zero_add] at div_q
    rw[← div_p, ← div_q]
    apply (poly_mul_cancel (Polynomial.Monic.ne_zero hr)).mp h

lemma poly_exact_div_mul_cancel {p q : Polynomial (MvPolynomial (Fin n) ℂ)}
 (_q_monic : Polynomial.Monic q) (exact_div : p %ₘ q = 0) : q * (p /ₘ q) = p := by
  nth_rewrite 2 [← sub_zero p]
  apply eq_sub_of_add_eq
  rw[add_comm]
  rw[← exact_div]
  exact Polynomial.modByMonic_add_div p q

-- since the division is exact, the quotient perfectly divides the numerator
lemma demazure_division_exact' : ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
    DemazureDenominator i * ((DemazureNumerator i p) /ₘ (DemazureDenominator i)) =
      DemazureNumerator i p := by
  intro i p
  apply poly_exact_div_mul_cancel (demazure_denominator_monic i) (demazure_division_exact i p)

/- Now we prove that the Demazure operator is a linear map directly with the definition.
  This requires a lot of work to disentangle it -/

lemma demazure_map_add (i : Fin n) : ∀p q : MvPolynomial (Fin (n + 1)) ℂ,
  DemazureFun i (p + q) = DemazureFun i p + DemazureFun i q := by
  intro p q
  simp only [DemazureFun, SwapVariables, renameEquiv_apply]
  rw[← map_add]
  apply congr_arg
  rw[← map_add (AlgEquiv.symm (MvPolynomial.finSuccEquiv ℂ n))
    (DemazureNumerator i p /ₘ DemazureDenominator i)
    (DemazureNumerator i q /ₘ DemazureDenominator i)]
  apply congr_arg
  apply (poly_mul_cancel (demazure_denominator_ne_zero i)).mpr
  simp only [mul_add]
  simp only [demazure_division_exact']
  exact demazure_numerator_add i p q

lemma demazure_map_smul (i : Fin n) : ∀ (r : ℂ) (p : MvPolynomial (Fin (n + 1)) ℂ),
  DemazureFun i (r • p) = r • DemazureFun i p := by
  intro r p
  simp only [DemazureFun, SwapVariables, smul_eq_C_mul, renameEquiv_apply]
  nth_rewrite 2 [← rename_C (Equiv.swap (Fin.castSucc i) 0) r]
  rw[← map_mul]
  apply congr_arg
  nth_rewrite 2 [← MvPolynomial.finSuccEquiv_comp_C_eq_C]
  simp only [RingHom.comp, Nat.succ_eq_add_one, RingHom.coe_coe, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw[← map_mul (AlgEquiv.symm (MvPolynomial.finSuccEquiv ℂ n))]
  apply congr_arg
  apply (poly_mul_cancel (demazure_denominator_ne_zero i)).mpr
  rw[← mul_assoc]
  rw [mul_comm (DemazureDenominator i) (Polynomial.C (C r))]
  simp only [demazure_division_exact']
  rw[mul_assoc]
  rw[demazure_division_exact' i p]
  exact demazure_numerator_C_mul i p r

/-- The Demazure operator as a complex-linear map. -/
def DemazureLinear (i : Fin n) :
    LinearMap (RingHom.id ℂ) (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (n + 1)) ℂ) where
  toFun := DemazureFun i
  map_add' := demazure_map_add i
  map_smul' := demazure_map_smul i

lemma one_of_div_by_monic_self : ∀ (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (_h : Polynomial.Monic p), p /ₘ p = 1 := by
  intro p hp
  have hmod : p %ₘ p = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hp).mpr (dvd_refl p)
  have h := Polynomial.modByMonic_add_div p p
  rw [hmod, zero_add] at h
  apply (mul_left_cancel₀ hp.ne_zero)
  simpa using h


-- Example showing that the demazure operator doesn't respect the multiplication
lemma demazure_not_multiplicative : ∀ (i : Fin n), ∃(p q : MvPolynomial (Fin (n+1)) ℂ),
  DemazureLinear i (p * q) ≠ DemazureLinear i p * DemazureLinear i q := by
  intro i
  use (X (Fin.castSucc i))
  use C 1
  simp only [DemazureLinear, mul_one, LinearMap.coe_mk, AddHom.coe_mk, DemazureFun,
    SwapVariables, DemazureNumerator, renameEquiv_apply, rename_X, Equiv.swap_apply_left,
    map_sub, Equiv.swap_apply_def, fin_succ_ne_fin_castSucc, ↓reduceIte, Fin.succ_ne_zero,
    DemazureDenominator, map_one, sub_self, map_zero,
    Polynomial.zero_divByMonic, mul_zero, ne_eq]
  rw [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  rw[one_of_div_by_monic_self]
  · simp
  · exact Polynomial.monic_X_sub_C (X i)

/- Doing anything with the definition, even simple things, requires a lot of work given
the complexity of the definition. That's why in DemazureAux.lean we introduce an alternative
definition that will be the one we actually use for computations -/

end Demazure

end
