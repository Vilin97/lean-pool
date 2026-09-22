/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.OmnificFiniteDegree
public import Mathlib.Data.Prod.Lex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Sum.Order
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Exponential

import all LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Omnific integers at every finite power of omega

For each natural number `n`, let `FiniteLex n` be the lexicographic order on natural tuples of
length `n`. Its order type is `ω ^ n`. Define negative real numbers recursively by

`E 0 * = -1`,

`E (n + 1) (m, p) = -(1 / 3) ^ m + (1 / 3) ^ (m + 1) E n p`.

The intervals occupied by successive values of `m` are disjoint, so `E n` is a strict order
embedding. Negating these values and adjoining a final zero gives a strictly decreasing sequence
of Conway exponents of order type `ω ^ n + 1`.

The normal form `finitePowerOz n` has coefficient one at every exponent in this sequence. It is a
nonordinary reduced omnific integer, its Conway length is exactly `ω ^ n + 1`, and it has finite
degree. Consequently, every member of the family is primal.

This construction does not assert irreducibility. At degree two, coefficients contain information
not determined by support geometry alone, as illustrated by the PS06 example. Within this family,
doubling every coefficient preserves the support but destroys reducedness.

## References

* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, <https://doi.org/10.1016/j.aim.2024.109513>, cited
  as [LM24].
* J. Pommersheim, S. Shahriari, *Unique factorization in generalized power series rings*,
Proc. Amer. Math. Soc. 134 (2006), 1277–1287, cited as [PS06].
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.FinitePowerFamily

open Ordinal

/-- Natural tuples of length `n`, ordered lexicographically from the first coordinate. -/
abbrev FiniteLex : ℕ → Type
  | .zero => Unit
  | .succ n => Lex (ℕ × FiniteLex n)

noncomputable instance finiteLexLinearOrder : (n : ℕ) → LinearOrder (FiniteLex n)
  | .zero => inferInstanceAs (LinearOrder Unit)
  | .succ n => by
      letI : LinearOrder (FiniteLex n) := finiteLexLinearOrder n
      exact Prod.Lex.instLinearOrder ℕ (FiniteLex n)

instance finiteLexWellFoundedLT : (n : ℕ) → WellFoundedLT (FiniteLex n)
  | .zero => by
      change WellFoundedLT Unit
      exact Finite.wellFounded_of_trans_of_irrefl (· < ·)
  | .succ n => by
      let : WellFoundedLT (FiniteLex n) := finiteLexWellFoundedLT n
      exact inferInstanceAs (WellFoundedLT (Lex (ℕ × FiniteLex n)))

/-- The lexicographic natural tuples of length `n` have order type `ω ^ n`. -/
theorem typeLT_finiteLex (n : ℕ) :
    Ordinal.type ((· < ·) : FiniteLex n → FiniteLex n → Prop) =
      (Ordinal.omega0 : Ordinal.{0}) ^ (n : Ordinal.{0}) := by
  induction n with
  | zero => simp [FiniteLex]
  | succ n ih =>
      change Ordinal.type
        (Prod.Lex ((· < ·) : ℕ → ℕ → Prop)
          ((· < ·) : FiniteLex n → FiniteLex n → Prop)) = _
      rw [Ordinal.type_prod_lex, Ordinal.type_nat_lt]
      rw [ih]
      rw [← Ordinal.opow_add_one]
      congr 2

/-- The contraction factor separating consecutive lexicographic blocks. -/
def scale : ℝ := 1 / 3

@[simp]
theorem scale_eq_one_div_three : scale = (1 / 3 : ℝ) := by
  rfl

private theorem scale_pos : 0 < scale := by norm_num [scale]

private theorem scale_le_one : scale ≤ 1 := by norm_num [scale]

/-- A bounded negative real realization of the lexicographic tuple order. -/
def finitePowerExponent : (n : ℕ) → FiniteLex n → ℝ
  | .zero, _ => -1
  | .succ n, p =>
      -scale ^ (ofLex p).1 +
        scale ^ ((ofLex p).1 + 1) * finitePowerExponent n (ofLex p).2

@[simp]
theorem finitePowerExponent_zero (p : FiniteLex 0) :
    finitePowerExponent 0 p = -1 := by
  rfl

@[simp]
theorem finitePowerExponent_succ (n : ℕ) (p : FiniteLex (n + 1)) :
    finitePowerExponent (n + 1) p =
      -scale ^ (ofLex p).1 +
        scale ^ ((ofLex p).1 + 1) * finitePowerExponent n (ofLex p).2 := by
  rfl

theorem finitePowerExponent_neg : ∀ (n : ℕ) (p : FiniteLex n),
    finitePowerExponent n p < 0
  | 0, _ => by simp [finitePowerExponent]
  | n + 1, p => by
      have htail := finitePowerExponent_neg n (ofLex p).2
      have hpow : 0 < scale ^ ((ofLex p).1 + 1) := pow_pos scale_pos _
      have hmul :
          scale ^ ((ofLex p).1 + 1) * finitePowerExponent n (ofLex p).2 < 0 :=
        mul_neg_of_pos_of_neg hpow htail
      have hfirst : 0 < scale ^ (ofLex p).1 := pow_pos scale_pos _
      simp only [finitePowerExponent]
      linarith

/-- Every finite-tuple exponent lies weakly above `-3 / 2`. -/
theorem finitePowerExponent_lowerBound :
    ∀ (n : ℕ) (p : FiniteLex n),
      -(3 / 2 : ℝ) ≤ finitePowerExponent n p
  | 0, _ => by norm_num [finitePowerExponent]
  | n + 1, p => by
      have htail := finitePowerExponent_lowerBound n (ofLex p).2
      have hpowNonneg : 0 ≤ scale ^ ((ofLex p).1 + 1) := (pow_pos scale_pos _).le
      have htailMul :
          scale ^ ((ofLex p).1 + 1) * (-(3 / 2 : ℝ)) ≤
            scale ^ ((ofLex p).1 + 1) * finitePowerExponent n (ofLex p).2 :=
        mul_le_mul_of_nonneg_left htail hpowNonneg
      have hfirst : scale ^ (ofLex p).1 ≤ 1 := by
        simpa using pow_le_pow_of_le_one scale_pos.le scale_le_one
          (Nat.zero_le (ofLex p).1)
      have hsecond : scale ^ ((ofLex p).1 + 1) ≤ scale := by
        simpa using pow_le_pow_of_le_one scale_pos.le scale_le_one
          (Nat.succ_le_succ (Nat.zero_le (ofLex p).1))
      simp only [finitePowerExponent]
      norm_num [scale] at htailMul hfirst hsecond ⊢
      linarith

private theorem finitePowerExponent_succ_lt_blockLimit
    (n : ℕ) (p : FiniteLex (n + 1)) :
    finitePowerExponent (n + 1) p < -scale ^ (ofLex p).1 := by
  have htail := finitePowerExponent_neg n (ofLex p).2
  have hpow : 0 < scale ^ ((ofLex p).1 + 1) := pow_pos scale_pos _
  simp only [finitePowerExponent]
  nlinarith

private theorem finitePowerExponent_succ_blockLowerBound
    (n : ℕ) (p : FiniteLex (n + 1)) :
    -(3 / 2 : ℝ) * scale ^ (ofLex p).1 ≤ finitePowerExponent (n + 1) p := by
  have htail := finitePowerExponent_lowerBound n (ofLex p).2
  have hpowNonneg : 0 ≤ scale ^ ((ofLex p).1 + 1) := (pow_pos scale_pos _).le
  have htailMul :
      scale ^ ((ofLex p).1 + 1) * (-(3 / 2 : ℝ)) ≤
        scale ^ ((ofLex p).1 + 1) * finitePowerExponent n (ofLex p).2 :=
    mul_le_mul_of_nonneg_left htail hpowNonneg
  simp only [finitePowerExponent]
  rw [pow_succ] at htailMul ⊢
  norm_num [scale] at htailMul ⊢
  linarith

/-- The real realization preserves the lexicographic order. -/
theorem finitePowerExponent_strictMono (n : ℕ) : StrictMono (finitePowerExponent n) := by
  induction n with
  | zero =>
      intro p q hpq
      exact (lt_irrefl p hpq).elim
  | succ n ih =>
      intro p q hpq
      induction p using Lex.rec with | h p =>
      induction q using Lex.rec with | h q =>
      rcases p with ⟨m, p⟩
      rcases q with ⟨m', q⟩
      rw [Prod.Lex.lt_iff'] at hpq
      rcases hpq with ⟨hfirstLe, htailOfEq⟩
      change m ≤ m' at hfirstLe
      change m = m' → p < q at htailOfEq
      rcases hfirstLe.eq_or_lt with hfirst | hfirst
      · have htail := htailOfEq hfirst
        change -scale ^ m + scale ^ (m + 1) * finitePowerExponent n p <
          -scale ^ m' + scale ^ (m' + 1) * finitePowerExponent n q
        subst m'
        simpa only [add_comm] using
          (add_lt_add_left
            (mul_lt_mul_of_pos_left (ih htail) (pow_pos scale_pos (m + 1)))
            (-scale ^ m))
      · have hpUpper := finitePowerExponent_succ_lt_blockLimit n (toLex (m, p))
        have hqLower := finitePowerExponent_succ_blockLowerBound n (toLex (m', q))
        have hpow : scale ^ m' ≤ scale ^ (m + 1) :=
          pow_le_pow_of_le_one scale_pos.le scale_le_one (Nat.succ_le_iff.mpr hfirst)
        rw [pow_succ] at hpow
        norm_num [scale] at hpow
        have hpPowPos : 0 < (1 / 3 : ℝ) ^ m := by positivity
        have hsep : -scale ^ m < -(3 / 2 : ℝ) * scale ^ m' := by
          norm_num [scale]
          nlinarith [hpPowPos]
        calc
          finitePowerExponent (n + 1) (toLex (m, p)) < -scale ^ m := hpUpper
          _ < -(3 / 2 : ℝ) * scale ^ m' := hsep
          _ ≤ finitePowerExponent (n + 1) (toLex (m', q)) := hqLower

/-- The order embedding of the finite lexicographic tuples into the negative reals. -/
def finitePowerExponentEmbedding (n : ℕ) : FiniteLex n ↪o ℝ :=
  OrderEmbedding.ofStrictMono _ (finitePowerExponent_strictMono n)

/-- The all-zero tuple in the `n`-coordinate lexicographic index. -/
def finitePowerZeroIndex : (n : ℕ) → FiniteLex n
  | .zero => ()
  | .succ n => toLex (0, finitePowerZeroIndex n)

/-- The positive real Conway exponent attached to a finite tuple. -/
def finitePowerConwayExponent (n : ℕ) (p : FiniteLex n) : ℝ :=
  -finitePowerExponent n p

@[simp]
theorem finitePowerConwayExponent_apply (n : ℕ) (p : FiniteLex n) :
    finitePowerConwayExponent n p = -finitePowerExponent n p := by
  rfl

theorem finitePowerConwayExponent_pos (n : ℕ) (p : FiniteLex n) :
    0 < finitePowerConwayExponent n p := by
  exact neg_pos.mpr (finitePowerExponent_neg n p)

theorem finitePowerConwayExponent_strictAnti (n : ℕ) :
    StrictAnti (finitePowerConwayExponent n) := by
  intro p q hpq
  exact neg_lt_neg ((finitePowerExponent_strictMono n) hpq)

/-- The tuple exponents followed by the constant exponent. -/
abbrev ConwayIndex (n : ℕ) := WithTop (FiniteLex n)

theorem typeLT_conwayIndex (n : ℕ) :
    Ordinal.type ((· < ·) : ConwayIndex n → ConwayIndex n → Prop) =
      (Ordinal.omega0 : Ordinal.{0}) ^ (n : Ordinal.{0}) + 1 := by
  let : WellFoundedLT (FiniteLex n ⊕ₗ PUnit) :=
    (WithTop.orderIsoSumLexPUnit (α := FiniteLex n)).symm.toOrderEmbedding.wellFoundedLT
  calc
    Ordinal.type ((· < ·) : ConwayIndex n → ConwayIndex n → Prop) =
        Ordinal.type ((· < ·) : (FiniteLex n ⊕ₗ PUnit) →
          (FiniteLex n ⊕ₗ PUnit) → Prop) :=
      (WithTop.orderIsoSumLexPUnit (α := FiniteLex n)).toRelIsoLT.ordinalType_congr
    _ = (Ordinal.omega0 : Ordinal.{0}) ^ (n : Ordinal.{0}) + 1 := by
      change Ordinal.type
        (Sum.Lex ((· < ·) : FiniteLex n → FiniteLex n → Prop)
          ((· < ·) : PUnit → PUnit → Prop)) = _
      rw [Ordinal.type_sum_lex, typeLT_finiteLex]
      simp

/-- The exponent sequence of the `n`-th Conway normal form. -/
def finitePowerConwayExponentAtIndex (n : ℕ) : ConwayIndex n → Surreal.{0}
  | ⊤ => 0
  | (p : FiniteLex n) => (finitePowerConwayExponent n p : ℝ)

@[simp]
theorem finitePowerConwayExponentAtIndex_top (n : ℕ) :
    finitePowerConwayExponentAtIndex n ⊤ = 0 := by
  rfl

@[simp]
theorem finitePowerConwayExponentAtIndex_coe (n : ℕ) (p : FiniteLex n) :
    finitePowerConwayExponentAtIndex n (p : ConwayIndex n) =
      (finitePowerConwayExponent n p : ℝ) := by
  rfl

theorem finitePowerConwayExponentAtIndex_strictAnti (n : ℕ) :
    StrictAnti (finitePowerConwayExponentAtIndex n) := by
  intro p q hpq
  induction p using WithTop.recTopCoe with
  | top => exact (not_lt_of_ge le_top hpq).elim
  | coe p =>
      induction q using WithTop.recTopCoe with
      | top =>
          change (0 : Surreal) < (finitePowerConwayExponent n p : ℝ)
          exact_mod_cast finitePowerConwayExponent_pos n p
      | coe q =>
          change ((finitePowerConwayExponent n q : ℝ) : Surreal) <
            (finitePowerConwayExponent n p : ℝ)
          exact_mod_cast finitePowerConwayExponent_strictAnti n
            (WithTop.coe_lt_coe.mp hpq)

/-- The coefficient function of the `n`-th Conway normal form. -/
def finitePowerCoefficient (n : ℕ) (i : Surreal.{0}) : ℝ :=
  by
    classical
    exact if i ∈ Set.range (finitePowerConwayExponentAtIndex n) then 1 else 0

private theorem support_finitePowerCoefficient (n : ℕ) :
    Function.support (finitePowerCoefficient n) =
      Set.range (finitePowerConwayExponentAtIndex n) := by
  classical
  ext i
  simp [Function.support, finitePowerCoefficient]

/-- The coefficient support is a small set. -/
theorem small_support_finitePowerCoefficient (n : ℕ) :
    Small.{0} (Function.support (finitePowerCoefficient n)) := by
  rw [support_finitePowerCoefficient]
  infer_instance

/-- The coefficient support is reverse well-ordered. -/
theorem wellFoundedOn_support_finitePowerCoefficient (n : ℕ) :
    (Function.support (finitePowerCoefficient n)).WellFoundedOn (· > ·) := by
  rw [support_finitePowerCoefficient, Set.wellFoundedOn_range]
  convert wellFounded_lt (α := ConwayIndex n) using 1
  ext p q
  exact (finitePowerConwayExponentAtIndex_strictAnti n).lt_iff_gt

/-- The coefficient-one Conway normal form of support type `ω ^ n + 1`. -/
def finitePowerNormalForm (n : ℕ) : SurrealHahnSeries.{0} :=
  SurrealHahnSeries.mk (finitePowerCoefficient n)
    (small_support_finitePowerCoefficient n)
    (wellFoundedOn_support_finitePowerCoefficient n)

@[simp]
theorem finitePowerNormalForm_coeff (n : ℕ) (i : Surreal) :
    (finitePowerNormalForm n).coeff i = finitePowerCoefficient n i := by
  rw [finitePowerNormalForm, SurrealHahnSeries.coeff_mk, finitePowerCoefficient]

@[simp]
theorem finitePowerNormalForm_support (n : ℕ) :
    (finitePowerNormalForm n).support =
      Set.range (finitePowerConwayExponentAtIndex n) := by
  rw [finitePowerNormalForm, SurrealHahnSeries.support_mk,
    support_finitePowerCoefficient]

/-- The `n`-th Conway normal form has length exactly `ω ^ n + 1`. -/
theorem finitePowerNormalForm_length (n : ℕ) :
    (finitePowerNormalForm n).length =
      (Ordinal.omega0 : Ordinal.{0}) ^ (n : Ordinal.{0}) + 1 := by
  let f : ConwayIndex n → Surrealᵒᵈ :=
    fun p ↦ OrderDual.toDual (finitePowerConwayExponentAtIndex n p)
  have hf : StrictMono f := by
    intro p q hpq
    exact finitePowerConwayExponentAtIndex_strictAnti n hpq
  let eRange : ConwayIndex n ≃o Set.range f := hf.orderIso f
  let eSupport : (finitePowerNormalForm n).support ≃ Set.range f := {
    toFun x := ⟨OrderDual.toDual x.1, by
      have hx : x.1 ∈ Set.range (finitePowerConwayExponentAtIndex n) := by
        rw [← finitePowerNormalForm_support]
        exact x.2
      obtain ⟨p, hp⟩ := hx
      exact ⟨p, congrArg OrderDual.toDual hp⟩⟩
    invFun x := ⟨OrderDual.ofDual x.1, by
      rw [finitePowerNormalForm_support]
      obtain ⟨p, hp⟩ := x.2
      exact ⟨p, congrArg OrderDual.ofDual hp⟩⟩
    left_inv x := Subtype.ext rfl
    right_inv x := Subtype.ext rfl }
  let eSupportRel :
      (· > · : (finitePowerNormalForm n).support →
        (finitePowerNormalForm n).support → Prop) ≃r
      (· < · : Set.range f → Set.range f → Prop) := {
    toEquiv := eSupport
    map_rel_iff' := by intro x y; rfl }
  let e :
      (· > · : (finitePowerNormalForm n).support →
        (finitePowerNormalForm n).support → Prop) ≃r
      (· < · : ConwayIndex n → ConwayIndex n → Prop) :=
    eSupportRel.trans eRange.symm.toRelIsoLT
  have htype :
      Ordinal.type (α := (finitePowerNormalForm n).support) (· > ·) =
        Ordinal.lift.{1, 0}
          (Ordinal.type ((· < ·) : ConwayIndex n → ConwayIndex n → Prop)) := by
    simpa only [Ordinal.lift_id'] using e.ordinal_lift_type_eq
  have hsupport := SurrealHahnSeries.type_support (finitePowerNormalForm n)
  rw [htype, typeLT_conwayIndex] at hsupport
  exact Ordinal.lift_inj.mp hsupport.symm

theorem finitePowerNormalForm_coeff_exponent (n : ℕ) (p : FiniteLex n) :
    (finitePowerNormalForm n).coeff (finitePowerConwayExponent n p : ℝ) = 1 := by
  classical
  rw [finitePowerNormalForm_coeff, finitePowerCoefficient, ite_eq_left]
  exact ⟨(↑p : ConwayIndex n), rfl⟩

theorem finitePowerNormalForm_coeff_zero (n : ℕ) :
    (finitePowerNormalForm n).coeff 0 = 1 := by
  classical
  rw [finitePowerNormalForm_coeff, finitePowerCoefficient, ite_eq_left]
  exact ⟨⊤, rfl⟩

private theorem finitePowerNormalForm_support_nonnegative (n : ℕ) :
    (finitePowerNormalForm n).support ⊆ Set.Ici 0 := by
  rw [finitePowerNormalForm_support]
  rintro i ⟨p, rfl⟩
  induction p using WithTop.recTopCoe with
  | top => exact Set.mem_Ici.mpr (le_refl (0 : Surreal))
  | coe p =>
      rw [Set.mem_Ici]
      change (0 : Surreal) ≤ (finitePowerConwayExponent n p : ℝ)
      exact_mod_cast (finitePowerConwayExponent_pos n p).le

/-- The `n`-th coefficient-one normal form as an omnific integer. -/
def finitePowerOz (n : ℕ) : Oz.OmnificInteger.{0} :=
  ⟨finitePowerNormalForm n, by
    rw [Oz.mem_omnificIntegers]
    exact ⟨finitePowerNormalForm_support_nonnegative n,
      ⟨1, by simpa using (finitePowerNormalForm_coeff_zero n).symm⟩⟩⟩

@[simp]
theorem finitePowerOz_val (n : ℕ) :
    (finitePowerOz n).1 = finitePowerNormalForm n := by
  rfl

theorem finitePowerOz_support (n : ℕ) :
    (finitePowerOz n).1.support =
      Set.range (finitePowerConwayExponentAtIndex n) := by
  rw [finitePowerOz_val, finitePowerNormalForm_support]

/-- The `n`-th member of the family has Conway length exactly `ω ^ n + 1`. -/
theorem finitePowerOz_length (n : ℕ) :
    (finitePowerOz n).1.length =
      (Ordinal.omega0 : Ordinal.{0}) ^ (n : Ordinal.{0}) + 1 := by
  rw [finitePowerOz_val, finitePowerNormalForm_length]

/-- Distinct natural numbers give distinct omnific integers in the family. -/
theorem finitePowerOz_injective : Function.Injective finitePowerOz := by
  intro m n hmn
  have hlength := congrArg (fun x : Oz.OmnificInteger ↦ x.1.length) hmn
  rw [finitePowerOz_length, finitePowerOz_length] at hlength
  change Order.succ (Ordinal.omega0 ^ (m : Ordinal)) =
    Order.succ (Ordinal.omega0 ^ (n : Ordinal)) at hlength
  have hpower := Order.succ_injective hlength
  have hexponent :=
    (Ordinal.opow_right_inj Ordinal.one_lt_omega0).mp hpower
  exact_mod_cast hexponent

/-- Subtracting one removes the constant exponent from the `n`-th normal form. -/
theorem zero_not_mem_finitePowerOz_sub_one_support (n : ℕ) :
    0 ∉ ((finitePowerOz n).1 - 1).support := by
  rw [SurrealHahnSeries.mem_support_iff,
    SurrealHahnSeries.coeff_sub_apply, finitePowerOz_val,
    finitePowerNormalForm_coeff_zero,
    Oz.one_eq_single_zero,
    SurrealHahnSeries.coeff_single_self]
  norm_num

/-- No member of the family is an ordinary integer. -/
theorem finitePowerOz_not_isOrdinaryInteger (n : ℕ) :
    ¬ Oz.IsOrdinaryInteger (finitePowerOz n) := by
  rw [Oz.IsOrdinaryInteger]
  rintro ⟨z, hz⟩
  let p := finitePowerZeroIndex n
  let e : Surreal := (finitePowerConwayExponent n p : ℝ)
  have he0 : e ≠ 0 := by
    change ((finitePowerConwayExponent n p : ℝ) : Surreal) ≠ 0
    exact_mod_cast (finitePowerConwayExponent_pos n p).ne'
  have hcoeff := congrArg (fun q : SurrealHahnSeries ↦ q.coeff e) hz
  have hleft : (finitePowerOz n).1.coeff e = 1 := by
    rw [finitePowerOz_val]
    exact finitePowerNormalForm_coeff_exponent n p
  have hright : (z : SurrealHahnSeries).coeff e = 0 := by
    rw [Oz.intCast_eq_single_zero]
    exact SurrealHahnSeries.coeff_single_of_ne he0.symm _
  rw [hleft, hright] at hcoeff
  norm_num at hcoeff

/-- Every member of the family is reduced. -/
theorem finitePowerOz_isReduced (n : ℕ) :
    Oz.IsReduced (finitePowerOz n) := by
  rw [Oz.IsReduced]
  constructor
  · intro hzero
    apply finitePowerOz_not_isOrdinaryInteger n
    refine ⟨0, ?_⟩
    rw [hzero]
    rw [Oz.intCast_eq_single_zero]
    norm_num
  · refine ⟨0, ?_⟩
    intro i hi
    have hiSupport := hi.1
    rw [finitePowerOz_val, finitePowerNormalForm_support] at hiSupport
    obtain ⟨p, hp⟩ := hiSupport
    induction p using WithTop.recTopCoe with
    | top =>
        simp only [finitePowerConwayExponentAtIndex] at hp
        have hi0 : i = 0 := hp.symm
        subst i
        exact (zero_not_mem_finitePowerOz_sub_one_support n hi.2).elim
    | coe p =>
        change ArchimedeanClass.mk i = 0
        rw [← hp]
        exact Surreal.mk_realCast (finitePowerConwayExponent_pos n p).ne'

universe w

private theorem omega_opow_nat_add_one_lt_omega_opow_omega (n : ℕ) :
    (Ordinal.omega0 : Ordinal.{w}) ^ (n : Ordinal.{w}) + 1 <
      (Ordinal.omega0 : Ordinal.{w}) ^ (Ordinal.omega0 : Ordinal.{w}) := by
  cases n with
  | zero =>
      rw [Nat.cast_zero, Ordinal.opow_zero]
      calc
        (1 : Ordinal.{w}) + 1 = 2 := by norm_num
        _ < Ordinal.omega0 := Ordinal.natCast_lt_omega0 2
        _ = Ordinal.omega0 ^ (1 : Ordinal.{w}) := by rw [Ordinal.opow_one]
        _ < Ordinal.omega0 ^ Ordinal.omega0 :=
          (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
            Ordinal.one_lt_omega0
  | succ n =>
      have hw : (1 : Ordinal.{w}) <
          Ordinal.omega0 ^ ((n + 1 : ℕ) : Ordinal.{w}) :=
        (Ordinal.one_lt_opow).2 ⟨Ordinal.one_lt_omega0, by simp⟩
      simpa only [mul_one] using
        (Ordinal.opow_mul_add_lt_opow
          (b := (Ordinal.omega0 : Ordinal.{w}))
          (u := ((n + 1 : ℕ) : Ordinal.{w}))
          (v := 1) (w := 1) (x := Ordinal.omega0)
          Ordinal.one_lt_omega0 hw (Ordinal.natCast_lt_omega0 (n + 1)))

private theorem lift_omega0_opow_natCast (n : ℕ) :
    Ordinal.lift.{1, 0} ((Ordinal.omega0 : Ordinal.{0}) ^ (n : Ordinal)) =
      (Ordinal.omega0 : Ordinal.{1}) ^ (n : Ordinal) := by
  rw [Ordinal.opow_natCast, Ordinal.opow_natCast]
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, Ordinal.lift_mul, ih]

/-- Every member of the family has Conway length below `ω ^ ω`. -/
theorem finitePowerOz_hasFiniteDegree (n : ℕ) :
    Oz.HasFiniteDegree (finitePowerOz n) := by
  rw [Oz.HasFiniteDegree, finitePowerOz_val,
    finitePowerNormalForm_length, Ordinal.lift_add, Ordinal.lift_one,
    lift_omega0_opow_natCast]
  exact omega_opow_nat_add_one_lt_omega_opow_omega n

/-- Every coefficient-one omnific integer `finitePowerOz n` is primal. -/
def PrimalFamily : Prop :=
  ∀ n : ℕ, IsPrimal (finitePowerOz n)

/-
## Formal proof

Proof module: `Support.FinitePowerFamilyProof`.

* `PrimalFamily` → `PrimalFamily.proof`
-/

/-- Twice the `n`-th normal form. -/
def finitePowerFoil (n : ℕ) : Oz.OmnificInteger :=
  2 * finitePowerOz n

@[simp]
theorem finitePowerFoil_val (n : ℕ) :
    (finitePowerFoil n).1 = 2 * finitePowerNormalForm n := by
  rfl

/-- Doubling all nonzero coefficients leaves the exponent support unchanged. -/
theorem finitePowerFoil_support (n : ℕ) :
    (finitePowerFoil n).1.support = (finitePowerOz n).1.support := by
  rw [finitePowerFoil_val, finitePowerOz_val, two_mul]
  ext i
  simp only [SurrealHahnSeries.mem_support_iff,
    SurrealHahnSeries.coeff_add_apply]
  constructor
  · intro h hzero
    apply h
    rw [hzero, zero_add]
  · intro h hsum
    apply h
    linarith

/-- The doubled normal form is not reduced: its constant exponent survives subtraction by one. -/
theorem finitePowerFoil_not_isReduced (n : ℕ) :
    ¬ Oz.IsReduced (finitePowerFoil n) := by
  rw [Oz.IsReduced]
  rintro ⟨_, c, hc⟩
  let p := finitePowerZeroIndex n
  let e : Surreal := (finitePowerConwayExponent n p : ℝ)
  have he0 : e ≠ 0 := by
    change ((finitePowerConwayExponent n p : ℝ) : Surreal) ≠ 0
    exact_mod_cast (finitePowerConwayExponent_pos n p).ne'
  have hzeroFoil : 0 ∈ (finitePowerFoil n).1.support := by
    rw [finitePowerFoil_support, finitePowerOz_support]
    exact ⟨⊤, rfl⟩
  have hzeroSub : 0 ∈ ((finitePowerFoil n).1 - 1).support := by
    rw [SurrealHahnSeries.mem_support_iff,
      SurrealHahnSeries.coeff_sub_apply, finitePowerFoil_val, two_mul,
      SurrealHahnSeries.coeff_add_apply, finitePowerNormalForm_coeff_zero,
      Oz.one_eq_single_zero,
      SurrealHahnSeries.coeff_single_self]
    norm_num
  have heFoil : e ∈ (finitePowerFoil n).1.support := by
    rw [finitePowerFoil_support, finitePowerOz_support]
    exact ⟨(↑p : ConwayIndex n), rfl⟩
  have hone : (1 : SurrealHahnSeries).coeff e = 0 := by
    rw [Oz.one_eq_single_zero]
    exact SurrealHahnSeries.coeff_single_of_ne he0.symm _
  have heSub : e ∈ ((finitePowerFoil n).1 - 1).support := by
    rw [SurrealHahnSeries.mem_support_iff,
      SurrealHahnSeries.coeff_sub_apply, finitePowerFoil_val, two_mul,
      SurrealHahnSeries.coeff_add_apply,
      finitePowerNormalForm_coeff_exponent, hone]
    norm_num
  have hclassZero := hc ⟨hzeroFoil, hzeroSub⟩
  have hclassE := hc ⟨heFoil, heSub⟩
  change ArchimedeanClass.mk (0 : Surreal) = c at hclassZero
  change ArchimedeanClass.mk e = c at hclassE
  have hmkE : ArchimedeanClass.mk e = 0 := by
    change ArchimedeanClass.mk ((finitePowerConwayExponent n p : ℝ) : Surreal) = 0
    exact Surreal.mk_realCast (finitePowerConwayExponent_pos n p).ne'
  have hmkZero : ArchimedeanClass.mk (0 : Surreal) ≠ 0 := by simp
  apply hmkZero
  calc
    ArchimedeanClass.mk (0 : Surreal) = c := hclassZero
    _ = ArchimedeanClass.mk e := hclassE.symm
    _ = 0 := hmkE

end ConwayRefinement.Standalone.Oz.FinitePowerFamily
