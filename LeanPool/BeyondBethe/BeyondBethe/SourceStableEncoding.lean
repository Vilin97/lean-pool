/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.SourceStableInduction
import LeanPool.BeyondBethe.BeyondBethe.CapacityOrder
import Mathlib.Tactic

/-! # Source Stable Encoding -/

open scoped BigOperators
open scoped ComplexConjugate

namespace BeyondBethe

/-!
# Encoding multiaffine polynomials by Boolean coefficient tables
-/

noncomputable def boolExponent {n : ℕ} (S : Fin n → Bool) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ bif S i then 1 else 0)

@[simp]
theorem boolExponent_apply {n : ℕ} (S : Fin n → Bool) (i : Fin n) :
    boolExponent S i = bif S i then 1 else 0 := by
  simp [boolExponent]

theorem boolExponent_injective {n : ℕ} :
    Function.Injective (@boolExponent n) := by
  intro S T h
  funext i
  have hi := DFunLike.congr_fun h i
  simp only [boolExponent_apply] at hi
  cases hS : S i <;> cases hT : T i <;> simp [hS, hT] at hi ⊢

noncomputable def exponentBool {n : ℕ} (d : Fin n →₀ ℕ) : Fin n → Bool :=
  fun i ↦ decide (d i = 1)

theorem boolExponent_exponentBool {n : ℕ} (d : Fin n →₀ ℕ)
    (hd : ∀ i, d i ≤ 1) : boolExponent (exponentBool d) = d := by
  ext i
  simp only [boolExponent_apply, exponentBool]
  by_cases h : d i = 1
  · simp [h]
  · have hz : d i = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hd i) with hz | ho
      · exact hz
      · exact (h ho).elim
    simp [h, hz]

theorem coeff_eq_zero_of_not_squarefree
    {n : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultiaffine p) {d : Fin n →₀ ℕ}
    (hd : ¬ ∀ i, d i ≤ 1) : p.coeff d = 0 := by
  by_contra hcoeff
  push Not at hd
  obtain ⟨i, hi⟩ := hd
  have hmem : d ∈ p.support := MvPolynomial.mem_support_iff.mpr hcoeff
  have hdegree := MvPolynomial.monomial_le_degreeOf i hmem
  have := hp i
  omega

theorem multiaffine_eq_boolExpansion
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : IsMultiaffine p) :
    p = ∑ S : Fin n → Bool,
      MvPolynomial.monomial (boolExponent S) (p.coeff (boolExponent S)) := by
  classical
  ext d
  by_cases hd : ∀ i, d i ≤ 1
  · let S := exponentBool d
    have hSd : boolExponent S = d := boolExponent_exponentBool d hd
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single S]
    · simp [hSd]
    · intro T hT hTS
      simp only [MvPolynomial.coeff_monomial]
      rw [ite_eq_right]
      intro h
      apply hTS
      exact boolExponent_injective (h.trans hSd.symm)
    · intro hS
      exact (hS (Finset.mem_univ S)).elim
  · rw [coeff_eq_zero_of_not_squarefree hp hd, MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro S hS
    simp only [MvPolynomial.coeff_monomial]
    rw [ite_eq_right]
    intro h
    apply hd
    intro i
    rw [← h, boolExponent_apply]
    cases S i <;> simp

noncomputable def boolMonomial {n : ℕ}
    (x : Fin n → ℝ) (S : Fin n → Bool) : ℝ :=
  ∏ i, (x i) ^ (bif S i then (1 : ℕ) else 0)

theorem multiaffine_eval_eq_boolSum
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : IsMultiaffine p)
    (x : Fin n → ℝ) :
    p.eval x = ∑ S : Fin n → Bool,
      p.coeff (boolExponent S) * boolMonomial x S := by
  calc
    p.eval x =
        (∑ S : Fin n → Bool,
          MvPolynomial.monomial (boolExponent S) (p.coeff (boolExponent S))).eval x := by
            rw [← multiaffine_eq_boolExpansion p hp]
    _ = ∑ S : Fin n → Bool,
        p.coeff (boolExponent S) * boolMonomial x S := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S hS
      simp only [MvPolynomial.eval_monomial]
      congr 1
      rw [Finsupp.prod_fintype]
      · simp [boolMonomial, boolExponent_apply]
      · intro i
        simp

theorem sum_bool_fin_succ {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : (Fin (n + 1) → Bool) → R) :
    (∑ S : Fin (n + 1) → Bool, f S) =
      ∑ b : Bool, ∑ T : Fin n → Bool, f (prependBool b T) := by
  let e : Bool × (Fin n → Bool) ≃ (Fin (n + 1) → Bool) :=
    Fin.consEquiv (fun _ ↦ Bool)
  calc
    (∑ S : Fin (n + 1) → Bool, f S) =
        ∑ p : Bool × (Fin n → Bool), f (e p) := by
          symm
          exact e.sum_comp f
    _ = ∑ b : Bool, ∑ T : Fin n → Bool, f (prependBool b T) := by
      rw [Fintype.sum_prod_type]
      rfl

theorem boolMonomial_prepend {n : ℕ} (x : Fin (n + 1) → ℝ)
    (b : Bool) (S : Fin n → Bool) :
    boolMonomial x (prependBool b S) =
      (bif b then x 0 else 1) * boolMonomial (fun i ↦ x i.succ) S := by
  rw [boolMonomial, Fin.prod_univ_succ, boolMonomial]
  simp only [prependBool, Fin.cases_zero, Fin.cases_succ]
  cases b <;> simp

theorem sum_sum_mul_factors {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [CommRing R]
    (c : ι → κ → R) (u : ι → R) (v : κ → R) (A B : R) :
    (∑ i, ∑ j, c i j * (A * u i) * (B * v j)) =
      A * B * (∑ i, ∑ j, c i j * u i * v j) := by
  calc
    (∑ i, ∑ j, c i j * (A * u i) * (B * v j)) =
        ∑ i, ∑ j, (A * B) * (c i j * u i * v j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ i, (A * B) * (∑ j, c i j * u i * v j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = A * B * (∑ i, ∑ j, c i j * u i * v j) := by
      rw [Finset.mul_sum]

theorem pairTableEval_eq_boolDoubleSum :
    ∀ {n : ℕ} (c : PairTable n) (y z : Fin n → ℝ),
      pairTableEval n c y z =
        ∑ S : Fin n → Bool, ∑ T : Fin n → Bool,
          c S T * boolMonomial y S * boolMonomial z T := by
  intro n
  induction n with
  | zero =>
      intro c y z
      have hy (S : Fin 0 → Bool) : boolMonomial y S = 1 := by
        rw [boolMonomial]
        apply Finset.prod_eq_one
        intro i hi
        exact Fin.elim0 i
      have hz (T : Fin 0 → Bool) : boolMonomial z T = 1 := by
        rw [boolMonomial]
        apply Finset.prod_eq_one
        intro i hi
        exact Fin.elim0 i
      simp only [pairTableEval, Fintype.sum_unique, hy, hz, mul_one]
      apply congrArg₂ c <;> apply Subsingleton.elim
  | succ n ih =>
      intro c y z
      rw [sum_bool_fin_succ]
      simp_rw [sum_bool_fin_succ]
      simp only [Fintype.sum_bool, boolMonomial_prepend,
        Finset.sum_add_distrib]
      rw [sum_sum_mul_factors, sum_sum_mul_factors,
        sum_sum_mul_factors, sum_sum_mul_factors]
      simp only [Bool.false_eq, Bool.true_eq, Bool.cond_false, Bool.cond_true,
        one_mul, mul_one]
      change pairTableEval (n + 1) c y z =
        y 0 * z 0 *
              (∑ S, ∑ T, pairTableSection c true true S T *
                boolMonomial (fun i ↦ y i.succ) S * boolMonomial (fun i ↦ z i.succ) T) +
          z 0 *
              (∑ S, ∑ T, pairTableSection c false true S T *
                boolMonomial (fun i ↦ y i.succ) S * boolMonomial (fun i ↦ z i.succ) T) +
        (y 0 *
              (∑ S, ∑ T, pairTableSection c true false S T *
                boolMonomial (fun i ↦ y i.succ) S * boolMonomial (fun i ↦ z i.succ) T) +
          (∑ S, ∑ T, pairTableSection c false false S T *
            boolMonomial (fun i ↦ y i.succ) S * boolMonomial (fun i ↦ z i.succ) T))
      rw [← ih (pairTableSection c true true) (fun i ↦ y i.succ) (fun i ↦ z i.succ),
        ← ih (pairTableSection c false true) (fun i ↦ y i.succ) (fun i ↦ z i.succ),
        ← ih (pairTableSection c true false) (fun i ↦ y i.succ) (fun i ↦ z i.succ),
        ← ih (pairTableSection c false false) (fun i ↦ y i.succ) (fun i ↦ z i.succ)]
      simp only [pairTableEval]
      ring

noncomputable def coefficientPairTable {n : ℕ}
    (p q : MvPolynomial (Fin n) ℝ) : PairTable n :=
  fun S T ↦ p.coeff (boolExponent S) * q.coeff (boolExponent T)

theorem coefficientPairTable_eval
    {n : ℕ} (p q : MvPolynomial (Fin n) ℝ)
    (hp : IsMultiaffine p) (hq : IsMultiaffine q)
    (y z : Fin n → ℝ) :
    pairTableEval n (coefficientPairTable p q) y z = p.eval y * q.eval z := by
  rw [pairTableEval_eq_boolDoubleSum,
    multiaffine_eval_eq_boolSum p hp,
    multiaffine_eval_eq_boolSum q hq]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp [coefficientPairTable]
  ring

noncomputable def complexBoolMonomial {n : ℕ}
    (x : Fin n → ℂ) (S : Fin n → Bool) : ℂ :=
  ∏ i, (x i) ^ (bif S i then (1 : ℕ) else 0)

theorem multiaffine_eval₂_eq_boolSum
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : IsMultiaffine p)
    (x : Fin n → ℂ) :
    p.eval₂ (algebraMap ℝ ℂ) x = ∑ S : Fin n → Bool,
      ((p.coeff (boolExponent S) : ℝ) : ℂ) * complexBoolMonomial x S := by
  calc
    p.eval₂ (algebraMap ℝ ℂ) x =
        ((∑ S : Fin n → Bool,
          MvPolynomial.monomial (boolExponent S) (p.coeff (boolExponent S) : ℝ)) :
            MvPolynomial (Fin n) ℝ).eval₂
            (algebraMap ℝ ℂ) x := by
              rw [← multiaffine_eq_boolExpansion p hp]
    _ = ∑ S : Fin n → Bool,
        ((p.coeff (boolExponent S) : ℝ) : ℂ) * complexBoolMonomial x S := by
      rw [MvPolynomial.eval₂_sum]
      apply Finset.sum_congr rfl
      intro S hS
      simp only [MvPolynomial.eval₂_monomial, map_natCast]
      congr 1
      rw [Finsupp.prod_fintype]
      · simp [complexBoolMonomial, boolExponent_apply]
      · intro i
        simp

noncomputable def pairTableComplexEval :
    ∀ n : ℕ, PairTable n → (Fin n → ℂ) → (Fin n → ℂ) → ℂ
  | 0, c, _, _ => (c (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i) : ℂ)
  | n + 1, c, y, z =>
      let yt : Fin n → ℂ := fun i ↦ y i.succ
      let zt : Fin n → ℂ := fun i ↦ z i.succ
      let a := pairTableComplexEval n (pairTableSection c true true) yt zt
      let b := pairTableComplexEval n (pairTableSection c true false) yt zt
      let cc := pairTableComplexEval n (pairTableSection c false true) yt zt
      let d := pairTableComplexEval n (pairTableSection c false false) yt zt
      a * y 0 * z 0 + b * y 0 + cc * z 0 + d

theorem complexBoolMonomial_prepend {n : ℕ} (x : Fin (n + 1) → ℂ)
    (b : Bool) (S : Fin n → Bool) :
    complexBoolMonomial x (prependBool b S) =
      (bif b then x 0 else 1) * complexBoolMonomial (fun i ↦ x i.succ) S := by
  rw [complexBoolMonomial, Fin.prod_univ_succ, complexBoolMonomial]
  simp only [prependBool, Fin.cases_zero, Fin.cases_succ]
  cases b <;> simp

theorem pairTableComplexEval_eq_boolDoubleSum :
    ∀ {n : ℕ} (c : PairTable n) (y z : Fin n → ℂ),
      pairTableComplexEval n c y z =
        ∑ S : Fin n → Bool, ∑ T : Fin n → Bool,
          (c S T : ℂ) * complexBoolMonomial y S * complexBoolMonomial z T := by
  intro n
  induction n with
  | zero =>
      intro c y z
      have hy (S : Fin 0 → Bool) : complexBoolMonomial y S = 1 := by
        rw [complexBoolMonomial]
        apply Finset.prod_eq_one
        intro i hi
        exact Fin.elim0 i
      have hz (T : Fin 0 → Bool) : complexBoolMonomial z T = 1 := by
        rw [complexBoolMonomial]
        apply Finset.prod_eq_one
        intro i hi
        exact Fin.elim0 i
      simp only [pairTableComplexEval, Fintype.sum_unique, hy, hz, mul_one]
      norm_cast
  | succ n ih =>
      intro c y z
      rw [sum_bool_fin_succ]
      simp_rw [sum_bool_fin_succ]
      simp only [Fintype.sum_bool, complexBoolMonomial_prepend,
        Finset.sum_add_distrib]
      rw [sum_sum_mul_factors, sum_sum_mul_factors,
        sum_sum_mul_factors, sum_sum_mul_factors]
      simp only [Bool.cond_false, Bool.cond_true, one_mul, mul_one]
      change pairTableComplexEval (n + 1) c y z =
        y 0 * z 0 *
              (∑ S, ∑ T, (pairTableSection c true true S T : ℂ) *
                complexBoolMonomial (fun i ↦ y i.succ) S * complexBoolMonomial (fun i ↦ z i.succ) T) +
          z 0 *
              (∑ S, ∑ T, (pairTableSection c false true S T : ℂ) *
                complexBoolMonomial (fun i ↦ y i.succ) S * complexBoolMonomial (fun i ↦ z i.succ) T) +
        (y 0 *
              (∑ S, ∑ T, (pairTableSection c true false S T : ℂ) *
                complexBoolMonomial (fun i ↦ y i.succ) S * complexBoolMonomial (fun i ↦ z i.succ) T) +
          (∑ S, ∑ T, (pairTableSection c false false S T : ℂ) *
            complexBoolMonomial (fun i ↦ y i.succ) S * complexBoolMonomial (fun i ↦ z i.succ) T))
      rw [← ih (pairTableSection c true true) (fun i ↦ y i.succ) (fun i ↦ z i.succ),
        ← ih (pairTableSection c false true) (fun i ↦ y i.succ) (fun i ↦ z i.succ),
        ← ih (pairTableSection c true false) (fun i ↦ y i.succ) (fun i ↦ z i.succ),
        ← ih (pairTableSection c false false) (fun i ↦ y i.succ) (fun i ↦ z i.succ)]
      simp only [pairTableComplexEval]
      ring

theorem coefficientPairTable_complexEval
    {n : ℕ} (p q : MvPolynomial (Fin n) ℝ)
    (hp : IsMultiaffine p) (hq : IsMultiaffine q)
    (y z : Fin n → ℂ) :
    pairTableComplexEval n (coefficientPairTable p q) y z =
      p.eval₂ (algebraMap ℝ ℂ) y * q.eval₂ (algebraMap ℝ ℂ) z := by
  rw [pairTableComplexEval_eq_boolDoubleSum,
    multiaffine_eval₂_eq_boolSum p hp,
    multiaffine_eval₂_eq_boolSum q hq]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp [coefficientPairTable]
  push_cast
  ring

def pairVariablesLeft :
    ∀ n : ℕ, (PairVariables n → ℂ) → Fin n → ℂ
  | 0, _, i => Fin.elim0 i
  | n + 1, w, i => Fin.cases (w none) (pairVariablesLeft n ((w ∘ some) ∘ some)) i

def pairVariablesRight :
    ∀ n : ℕ, (PairVariables n → ℂ) → Fin n → ℂ
  | 0, _, i => Fin.elim0 i
  | n + 1, w, i => Fin.cases (w (some none)) (pairVariablesRight n ((w ∘ some) ∘ some)) i

theorem pairTableStablePolynomial_eval_coordinates :
    ∀ {n : ℕ} (c : PairTable n) (w : PairVariables n → ℂ),
      (pairTableStablePolynomial n c).eval w =
        pairTableComplexEval n c (pairVariablesLeft n w)
          (fun i ↦ -pairVariablesRight n w i) := by
  intro n
  induction n with
  | zero => intro c w; simp [pairTableStablePolynomial, pairTableComplexEval]
  | succ n ih =>
      intro c w
      change Option (Option (PairVariables n)) → ℂ at w
      simp only [pairTableStablePolynomial]
      change
        (linearExtension
          (linearExtension (pairTableStablePolynomial n (pairTableSection c false false))
            (-pairTableStablePolynomial n (pairTableSection c false true)))
          (linearExtension (pairTableStablePolynomial n (pairTableSection c true false))
            (-pairTableStablePolynomial n (pairTableSection c true true)))).eval w =
          pairTableComplexEval (n + 1) c
            (Fin.cases (w none) (pairVariablesLeft n ((w ∘ some) ∘ some)))
            (fun i ↦ -Fin.cases (w (some none))
              (pairVariablesRight n ((w ∘ some) ∘ some)) i)
      rw [linearExtension_eval, linearExtension_eval, linearExtension_eval]
      simp only [MvPolynomial.eval_neg]
      rw [ih, ih, ih, ih]
      simp only [pairTableComplexEval, pairVariablesLeft, pairVariablesRight,
        Fin.cases_zero, Fin.cases_succ, Function.comp_apply]
      ring

theorem coefficientPairTable_nonnegative
    {n : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    (hp : HasNonnegativeCoefficients p) (hq : HasNonnegativeCoefficients q) :
    PairTableNonnegative (coefficientPairTable p q) := by
  intro S T
  exact mul_nonneg (hp _) (hq _)

theorem eval₂_conj_of_real
    {σ : Type*} (p : MvPolynomial σ ℝ) (z : σ → ℂ) :
    p.eval₂ (algebraMap ℝ ℂ) (fun i ↦ conj (z i)) =
      conj (p.eval₂ (algebraMap ℝ ℂ) z) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, map_mul]

theorem IsRealStable.lowerHalfPlane
    {σ : Type*} {p : MvPolynomial σ ℝ} (hp : IsRealStable p)
    (z : σ → ℂ) (hz : ∀ i, (z i).im < 0) :
    p.eval₂ (algebraMap ℝ ℂ) z ≠ 0 := by
  have hupper : ∀ i, 0 < (conj (z i)).im := by
    intro i
    simpa using neg_pos.mpr (hz i)
  have hne := hp (fun i ↦ conj (z i)) hupper
  rw [eval₂_conj_of_real] at hne
  intro hzero
  apply hne
  rw [hzero]
  simp

theorem pairVariablesLeft_upper :
    ∀ {n : ℕ} (w : PairVariables n → ℂ),
      (∀ i, 0 < (w i).im) → ∀ j, 0 < (pairVariablesLeft n w j).im := by
  intro n
  induction n with
  | zero => intro w hw j; exact Fin.elim0 j
  | succ n ih =>
      intro w hw j
      change Option (Option (PairVariables n)) → ℂ at w
      refine Fin.cases (hw none) (fun i ↦ ?_) j
      exact ih ((w ∘ some) ∘ some) (fun k ↦ hw (some (some k))) i

theorem pairVariablesRight_upper :
    ∀ {n : ℕ} (w : PairVariables n → ℂ),
      (∀ i, 0 < (w i).im) → ∀ j, 0 < (pairVariablesRight n w j).im := by
  intro n
  induction n with
  | zero => intro w hw j; exact Fin.elim0 j
  | succ n ih =>
      intro w hw j
      change Option (Option (PairVariables n)) → ℂ at w
      refine Fin.cases (hw (some none)) (fun i ↦ ?_) j
      exact ih ((w ∘ some) ∘ some) (fun k ↦ hw (some (some k))) i

theorem coefficientPairTable_stable
    {n : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    (hpMulti : IsMultiaffine p) (hqMulti : IsMultiaffine q)
    (hpStable : IsRealStable p) (hqStable : IsRealStable q) :
    IsUpperHalfPlaneStable
      (pairTableStablePolynomial n (coefficientPairTable p q)) := by
  intro w hw
  rw [pairTableStablePolynomial_eval_coordinates,
    coefficientPairTable_complexEval p q hpMulti hqMulti]
  apply mul_ne_zero
  · apply hpStable
    exact pairVariablesLeft_upper w hw
  · apply hqStable.lowerHalfPlane
    intro i
    simp only [Complex.neg_im]
    exact neg_lt_zero.mpr (pairVariablesRight_upper w hw i)

theorem pairTableDiagonalSum_eq_boolSum :
    ∀ {n : ℕ} (c : PairTable n),
      pairTableDiagonalSum n c = ∑ S : Fin n → Bool, c S S := by
  intro n
  induction n with
  | zero =>
      intro c
      simp only [pairTableDiagonalSum, Fintype.sum_unique]
      apply congrArg₂ c <;> apply Subsingleton.elim
  | succ n ih =>
      intro c
      rw [sum_bool_fin_succ]
      simp only [Fintype.sum_bool]
      change pairTableDiagonalSum (n + 1) c =
        (∑ S, pairTableSection c true true S S) +
          ∑ S, pairTableSection c false false S S
      rw [← ih (pairTableSection c true true),
        ← ih (pairTableSection c false false)]
      simp only [pairTableDiagonalSum]
      ring

theorem exponentBool_boolExponent {n : ℕ} (S : Fin n → Bool) :
    exponentBool (boolExponent S) = S := by
  apply boolExponent_injective
  rw [boolExponent_exponentBool]
  intro i
  rw [boolExponent_apply]
  cases S i <;> simp
theorem coefficientInnerProduct_eq_boolSum
    {n : ℕ} (p q : MvPolynomial (Fin n) ℝ)
    (hp : IsMultiaffine p) :
    coefficientInnerProduct p q =
      ∑ S : Fin n → Bool,
        p.coeff (boolExponent S) * q.coeff (boolExponent S) := by
  classical
  let target := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun S ↦ boolExponent S ∈ p.support ∧ boolExponent S ∈ q.support)
  have hsquarefree {d : Fin n →₀ ℕ}
      (hd : d ∈ p.support.filter (· ∈ q.support)) : ∀ i, d i ≤ 1 := by
    intro i
    have hdp : d ∈ p.support := (Finset.mem_filter.mp hd).1
    exact (MvPolynomial.monomial_le_degreeOf i hdp).trans (hp i)
  have hreindex :
      (∑ d ∈ p.support.filter (· ∈ q.support), p.coeff d * q.coeff d) =
        ∑ S ∈ target, p.coeff (boolExponent S) * q.coeff (boolExponent S) := by
    apply Finset.sum_nbij' exponentBool boolExponent
    · intro d hd
      have heq := boolExponent_exponentBool d (hsquarefree hd)
      have hdpair := Finset.mem_filter.mp hd
      change exponentBool d ∈ target
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [heq] using hdpair⟩
    · intro S hS
      have hpair := (Finset.mem_filter.mp hS).2
      exact Finset.mem_filter.mpr hpair
    · intro d hd
      exact boolExponent_exponentBool d (hsquarefree hd)
    · intro S hS
      exact exponentBool_boolExponent S
    · intro d hd
      rw [boolExponent_exponentBool d (hsquarefree hd)]
  have htarget :
      (∑ S ∈ target, p.coeff (boolExponent S) * q.coeff (boolExponent S)) =
        ∑ S, p.coeff (boolExponent S) * q.coeff (boolExponent S) := by
    dsimp only [target]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hpS : boolExponent S ∈ p.support
    · by_cases hqS : boolExponent S ∈ q.support
      · simp [hpS, hqS]
      · have hqzero : q.coeff (boolExponent S) = 0 :=
          MvPolynomial.notMem_support_iff.mp hqS
        simp [hpS, hqS, hqzero]
    · have hpzero : p.coeff (boolExponent S) = 0 :=
          MvPolynomial.notMem_support_iff.mp hpS
      simp [hpS, hpzero]
  unfold coefficientInnerProduct
  convert hreindex.trans htarget using 1
  apply Finset.sum_congr
  · ext d
    simp
  · intro d hd
    rfl

theorem coefficientPairTable_diagonalSum
    {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) (hp : IsMultiaffine p) :
    pairTableDiagonalSum n (coefficientPairTable p q) =
      coefficientInnerProduct p q := by
  rw [pairTableDiagonalSum_eq_boolSum,
    coefficientInnerProduct_eq_boolSum p q hp]
  rfl

theorem pairTableBoundary_eq_stableBoundaryFactor :
    ∀ {n : ℕ} (α : Fin n → ℝ),
      pairTableBoundary n α = stableBoundaryFactor α := by
  intro n
  induction n with
  | zero =>
      intro α
      simp [pairTableBoundary, stableBoundaryFactor]
  | succ n ih =>
      intro α
      simp only [pairTableBoundary]
      have hdef : stableBoundaryFactor α =
          ∏ i, α i ^ α i * (1 - α i) ^ (1 - α i) := rfl
      rw [hdef, Fin.prod_univ_succ, ih]
      have htaildef : stableBoundaryFactor (fun i : Fin n ↦ α i.succ) =
          ∏ i : Fin n, α i.succ ^ α i.succ *
            (1 - α i.succ) ^ (1 - α i.succ) := rfl
      rw [htaildef]
      rfl

theorem pairTableMonomial_eq_realMonomial :
    ∀ {n : ℕ} (x α : Fin n → ℝ),
      pairTableMonomial n x α = realMonomial x α := by
  intro n
  induction n with
  | zero =>
      intro x α
      simp [pairTableMonomial, realMonomial]
  | succ n ih =>
      intro x α
      simp only [pairTableMonomial]
      have hdef : realMonomial x α = ∏ i, x i ^ α i := rfl
      rw [hdef, Fin.prod_univ_succ, ih]
      have htaildef : realMonomial (fun i : Fin n ↦ x i.succ)
          (fun i : Fin n ↦ α i.succ) = ∏ i : Fin n, x i.succ ^ α i.succ := rfl
      rw [htaildef]

/-- The stable-coefficient inequality on the canonical finite coordinate type.
The source theorem assumes homogeneity and a prescribed total degree, but the
coefficient-table proof only needs nonnegative coefficients, multiaffinity,
stability, and `α ∈ [0,1]^n`; we record the stronger statement exposed by the
formal proof. -/
theorem stableCoefficient_fin
    {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) (α : Fin n → ℝ)
    (hpNonneg : HasNonnegativeCoefficients p)
    (hqNonneg : HasNonnegativeCoefficients q)
    (hpMulti : IsMultiaffine p) (hqMulti : IsMultiaffine q)
    (hpStable : IsRealStable p) (hqStable : IsRealStable q)
    (hα : ∀ i, 0 ≤ α i ∧ α i ≤ 1) :
    stableBoundaryFactor α *
        polynomialCapacity α p * polynomialCapacity α q ≤
      coefficientInnerProduct p q := by
  have hboundary : 0 ≤ stableBoundaryFactor α := by
    rw [← pairTableBoundary_eq_stableBoundaryFactor α]
    exact pairTableBoundary_nonnegative hα
  have hcapP : 0 ≤ polynomialCapacity α p :=
    polynomialCapacity_nonneg hpNonneg α
  have hcapQ : 0 ≤ polynomialCapacity α q :=
    polynomialCapacity_nonneg hqNonneg α
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨y, z, hy, hz, hwitness⟩ :=
    pairTable_stableCoefficient_witness
      (coefficientPairTable p q) α
      (coefficientPairTable_nonnegative hpNonneg hqNonneg)
      (Or.inr (coefficientPairTable_stable hpMulti hqMulti hpStable hqStable))
      hα ε hε
  have hmy : 0 < realMonomial y α := realMonomial_pos hy α
  have hmz : 0 < realMonomial z α := realMonomial_pos hz α
  let rp := p.eval y / realMonomial y α
  let rq := q.eval z / realMonomial z α
  have hrp : 0 ≤ rp := by
    dsimp [rp]
    exact div_nonneg
      (eval_nonneg_of_nonnegativeCoefficients hpNonneg (fun i ↦ (hy i).le))
      hmy.le
  have hrq : 0 ≤ rq := by
    dsimp [rq]
    exact div_nonneg
      (eval_nonneg_of_nonnegativeCoefficients hqNonneg (fun i ↦ (hz i).le))
      hmz.le
  have hcaps :
      polynomialCapacity α p * polynomialCapacity α q ≤ rp * rq := by
    exact mul_le_mul
      (polynomialCapacity_le_ratio hpNonneg α y hy)
      (polynomialCapacity_le_ratio hqNonneg α z hz)
      hcapQ hrp
  have hscaled := mul_le_mul_of_nonneg_left hcaps hboundary
  calc
    stableBoundaryFactor α * polynomialCapacity α p *
          polynomialCapacity α q =
        stableBoundaryFactor α *
          (polynomialCapacity α p * polynomialCapacity α q) := by ring
    _ ≤ stableBoundaryFactor α * (rp * rq) := hscaled
    _ = stableBoundaryFactor α *
        ((p.eval y * q.eval z) /
          (realMonomial y α * realMonomial z α)) := by
      dsimp [rp, rq]
      field_simp [hmy.ne', hmz.ne']
    _ = pairTableBoundary n α *
        (pairTableEval n (coefficientPairTable p q) y z /
          (pairTableMonomial n y α * pairTableMonomial n z α)) := by
      rw [pairTableBoundary_eq_stableBoundaryFactor,
        coefficientPairTable_eval p q hpMulti hqMulti,
        pairTableMonomial_eq_realMonomial,
        pairTableMonomial_eq_realMonomial]
    _ ≤ pairTableDiagonalSum n (coefficientPairTable p q) + ε := hwitness
    _ = coefficientInnerProduct p q + ε := by
      rw [coefficientPairTable_diagonalSum p q hpMulti]

end BeyondBethe
