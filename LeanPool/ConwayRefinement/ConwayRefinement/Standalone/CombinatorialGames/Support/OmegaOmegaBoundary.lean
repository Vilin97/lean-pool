/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.FinitePowerFamily
public import Mathlib.Data.Sigma.Order

import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# An omnific integer at the `ω ^ ω` boundary

Let `BoundaryIndex` be the lexicographic sum over `n : ℕ` of the natural tuples `FiniteLex n`.
Its order type is

`∑ n < ω, ω ^ n = ω ^ ω`.

The `n`-th tuple block is placed in the negative real interval

`[-(1 / 3) ^ n, -(1 / 3) ^ (n + 1))`.

These intervals occur consecutively and approach zero. Negating gives a strictly decreasing
sequence of positive Conway exponents. The coefficient-one normal form on this sequence is a
purely infinite omnific integer: its coefficient at exponent zero is zero.

The resulting omnific integer is nonordinary and reduced, and its Conway length is exactly
`ω ^ ω`. Thus it lies at, rather than below, the strict length bound in the finite-degree
primality theorem. No primality or nonprimality assertion is made about this boundary element.

## References

* J. H. Conway, *On Numbers and Games*, 2nd ed., A K Peters, 2001.
* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, cited as [LM24].
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.OmegaOmegaBoundary

open Ordinal
open ConwayRefinement.Standalone.Oz.FinitePowerFamily

/-- The lexicographic sum of the finite-tuple orders of types `ω ^ n`. -/
abbrev BoundaryIndex := Σₗ n : ℕ, FiniteLex n

instance : WellFoundedLT BoundaryIndex where
  wf := by
    change WellFounded
      (Sigma.Lex (· < ·) fun n => (· < · : FiniteLex n → FiniteLex n → Prop))
    let e := Equiv.psigmaEquivSigma (fun n : ℕ => FiniteLex n)
    let f :
        (Sigma.Lex (· < ·) fun n => (· < · : FiniteLex n → FiniteLex n → Prop)) ↪r
          (PSigma.Lex (· < ·) fun n => (· < · : FiniteLex n → FiniteLex n → Prop)) := {
      toFun := e.symm
      inj' := e.symm.injective
      map_rel_iff' := by
        rintro ⟨i, a⟩ ⟨j, b⟩
        simp only [PSigma.lex_iff, Sigma.lex_iff]
        rfl }
    exact f.wellFounded
      (WellFounded.psigma_lex wellFounded_lt fun n => (finiteLexWellFoundedLT n).wf)

private theorem fiber_type_le_boundary (n : ℕ) :
    (Ordinal.omega0 : Ordinal) ^ (n : Ordinal) ≤
      Ordinal.type ((· < ·) : BoundaryIndex → BoundaryIndex → Prop) := by
  rw [← typeLT_finiteLex]
  apply Ordinal.type_le_iff'.mpr
  refine ⟨{
    toFun := fun p => ⟨n, p⟩
    inj' := by intro p q h; cases h; rfl
    map_rel_iff' := by
      intro p q
      change Sigma.Lex (· < ·) (fun n => (· < ·)) ⟨n, p⟩ ⟨n, q⟩ ↔ p < q
      exact ⟨fun h => by cases h with
        | left _ _ hn => exact (lt_irrefl n hn).elim
        | right _ _ hpq => exact hpq,
        fun hpq => Sigma.Lex.right p q hpq⟩ }⟩

private theorem omegaPowOmega_le_boundaryType :
    (Ordinal.omega0 : Ordinal) ^ Ordinal.omega0 ≤
      Ordinal.type ((· < ·) : BoundaryIndex → BoundaryIndex → Prop) := by
  rw [Ordinal.opow_limit Ordinal.omega0_ne_zero Ordinal.isSuccLimit_omega0]
  apply Ordinal.iSup_le
  intro i
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp i.2
  rw [hn]
  exact fiber_type_le_boundary n

private def boundaryRank (x : BoundaryIndex) : Ordinal :=
  let p := ofLex x
  Ordinal.omega0 ^ ((p.1 + 1 : ℕ) : Ordinal) +
    Ordinal.typein ((· < ·) : FiniteLex p.1 → FiniteLex p.1 → Prop) p.2

@[simp]
private theorem boundaryRank_mk (n : ℕ) (p : FiniteLex n) :
    boundaryRank (toLex ⟨n, p⟩) =
      Ordinal.omega0 ^ ((n + 1 : ℕ) : Ordinal) +
        Ordinal.typein ((· < ·) : FiniteLex n → FiniteLex n → Prop) p := by
  rfl

private theorem typein_finiteLex_lt_opow (n : ℕ) (p : FiniteLex n) :
    Ordinal.typein ((· < ·) : FiniteLex n → FiniteLex n → Prop) p <
      Ordinal.omega0 ^ (n : Ordinal) := by
  rw [← typeLT_finiteLex]
  exact Ordinal.typein_lt_type _ p

private theorem boundaryRank_lt_stage (n : ℕ) (p : FiniteLex n) :
    boundaryRank (toLex ⟨n, p⟩) <
      Ordinal.omega0 ^ ((n + 2 : ℕ) : Ordinal) := by
  rw [boundaryRank_mk]
  simpa only [mul_one] using
    (Ordinal.opow_mul_add_lt_opow
      (b := Ordinal.omega0)
      (u := ((n + 1 : ℕ) : Ordinal))
      (v := 1)
      (w := Ordinal.typein ((· < ·) : FiniteLex n → FiniteLex n → Prop) p)
      (x := ((n + 2 : ℕ) : Ordinal))
      Ordinal.one_lt_omega0
      ((typein_finiteLex_lt_opow n p).trans
        ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (by
          exact_mod_cast Nat.lt_succ_self n)))
      (by exact_mod_cast (show n + 1 < n + 2 by omega)))

private theorem boundaryRank_lt_omegaPowOmega (x : BoundaryIndex) :
    boundaryRank x < Ordinal.omega0 ^ Ordinal.omega0 := by
  induction x using Lex.rec with
  | h x =>
      obtain ⟨n, p⟩ := x
      exact (boundaryRank_lt_stage n p).trans
        ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
          (Ordinal.natCast_lt_omega0 (n + 2)))

private theorem boundaryRank_strictMono : StrictMono boundaryRank := by
  intro x y hxy
  induction x using Lex.rec with
  | h x =>
      induction y using Lex.rec with
      | h y =>
          obtain ⟨n, p⟩ := x
          obtain ⟨m, q⟩ := y
          change Sigma.Lex (· < ·) (fun n => (· < ·)) ⟨n, p⟩ ⟨m, q⟩ at hxy
          cases hxy with
          | left _ _ hnm =>
              apply (boundaryRank_lt_stage n p).trans_le
              calc
                Ordinal.omega0 ^ ((n + 2 : ℕ) : Ordinal) ≤
                    Ordinal.omega0 ^ ((m + 1 : ℕ) : Ordinal) :=
                  Ordinal.opow_le_opow_right Ordinal.omega0_pos (by
                    exact_mod_cast (show n + 2 ≤ m + 1 by omega))
                _ ≤ boundaryRank (toLex ⟨m, q⟩) := by
                  rw [boundaryRank_mk]
                  exact le_add_right (le_refl _)
          | right _ _ hpq =>
              rw [boundaryRank_mk, boundaryRank_mk]
              exact add_lt_add_right
                ((Ordinal.typein_lt_typein
                  ((· < ·) : FiniteLex n → FiniteLex n → Prop)).mpr hpq) _

private def boundaryRankToType (x : BoundaryIndex) :
    (Ordinal.omega0 ^ Ordinal.omega0).ToType :=
  Ordinal.enum
    ((· < ·) :
      (Ordinal.omega0 ^ Ordinal.omega0).ToType →
        (Ordinal.omega0 ^ Ordinal.omega0).ToType → Prop)
    ⟨boundaryRank x, by
      rw [Ordinal.type_toType]
      exact boundaryRank_lt_omegaPowOmega x⟩

private theorem boundaryRankToType_strictMono : StrictMono boundaryRankToType := by
  intro x y hxy
  unfold boundaryRankToType
  apply (Ordinal.enum_lt_enum
    (r := ((· < ·) :
      (Ordinal.omega0 ^ Ordinal.omega0).ToType →
        (Ordinal.omega0 ^ Ordinal.omega0).ToType → Prop))).mpr
  exact boundaryRank_strictMono hxy

private theorem boundaryType_le_omegaPowOmega :
    Ordinal.type ((· < ·) : BoundaryIndex → BoundaryIndex → Prop) ≤
      Ordinal.omega0 ^ Ordinal.omega0 := by
  rw [← Ordinal.type_toType (Ordinal.omega0 ^ Ordinal.omega0)]
  apply Ordinal.type_le_iff'.mpr
  exact ⟨(OrderEmbedding.ofStrictMono boundaryRankToType
    boundaryRankToType_strictMono).ltEmbedding⟩

/-- The lexicographic sum of the finite-tuple orders has order type `ω ^ ω`. -/
theorem typeLT_boundaryIndex :
    Ordinal.type ((· < ·) : BoundaryIndex → BoundaryIndex → Prop) =
      Ordinal.omega0 ^ Ordinal.omega0 := by
  exact le_antisymm boundaryType_le_omegaPowOmega omegaPowOmega_le_boundaryType

private theorem boundary_scale_pos : 0 < scale := by
  norm_num [scale]

private theorem boundary_scale_le_one : scale ≤ 1 := by
  norm_num [scale]

/-- The increasing negative real sequence used before reversing the Conway exponents. -/
def boundarySignedExponent (x : BoundaryIndex) : ℝ :=
  match ofLex x with
  | ⟨n, p⟩ =>
      -scale ^ (n + 1) +
        (4 / 9 : ℝ) * scale ^ n * finitePowerExponent n p

@[simp]
theorem boundarySignedExponent_mk (n : ℕ) (p : FiniteLex n) :
    boundarySignedExponent (toLex ⟨n, p⟩) =
      -scale ^ (n + 1) +
        (4 / 9 : ℝ) * scale ^ n * finitePowerExponent n p := by
  rfl

private theorem boundarySignedExponent_lt_blockLimit (n : ℕ) (p : FiniteLex n) :
    boundarySignedExponent (toLex ⟨n, p⟩) < -scale ^ (n + 1) := by
  have hp := finitePowerExponent_neg n p
  have hs : 0 < (4 / 9 : ℝ) * scale ^ n :=
    mul_pos (by norm_num) (pow_pos boundary_scale_pos n)
  rw [boundarySignedExponent_mk]
  nlinarith

private theorem boundarySignedExponent_blockLowerBound (n : ℕ) (p : FiniteLex n) :
    -scale ^ n ≤ boundarySignedExponent (toLex ⟨n, p⟩) := by
  have hp := finitePowerExponent_lowerBound n p
  have hs : 0 ≤ (4 / 9 : ℝ) * scale ^ n :=
    (mul_pos (by norm_num) (pow_pos boundary_scale_pos n)).le
  have hmul := mul_le_mul_of_nonneg_left hp hs
  rw [boundarySignedExponent_mk, pow_succ]
  norm_num [scale] at hmul ⊢
  nlinarith

/-- The `n`-th block lies in the interval
`[-scale ^ n, -scale ^ (n + 1))`. -/
theorem boundarySignedExponent_mem_block (n : ℕ) (p : FiniteLex n) :
    boundarySignedExponent (toLex ⟨n, p⟩) ∈
      Set.Ico (-scale ^ n) (-scale ^ (n + 1)) := by
  exact ⟨boundarySignedExponent_blockLowerBound n p,
    boundarySignedExponent_lt_blockLimit n p⟩

/-- Every signed exponent is negative. -/
theorem boundarySignedExponent_neg (x : BoundaryIndex) :
    boundarySignedExponent x < 0 := by
  induction x using Lex.rec with
  | h x =>
      obtain ⟨n, p⟩ := x
      exact (boundarySignedExponent_lt_blockLimit n p).trans
        (neg_lt_zero.mpr (pow_pos boundary_scale_pos _))

/-- The signed exponent sequence preserves the boundary-index order. -/
theorem boundarySignedExponent_strictMono : StrictMono boundarySignedExponent := by
  intro x y hxy
  induction x using Lex.rec with
  | h x =>
      induction y using Lex.rec with
      | h y =>
          obtain ⟨n, p⟩ := x
          obtain ⟨m, q⟩ := y
          change Sigma.Lex (· < ·) (fun n => (· < ·)) ⟨n, p⟩ ⟨m, q⟩ at hxy
          cases hxy with
          | left _ _ hnm =>
              apply (boundarySignedExponent_lt_blockLimit n p).trans_le
              calc
                -scale ^ (n + 1) ≤ -scale ^ m := by
                  exact neg_le_neg
                    (pow_le_pow_of_le_one boundary_scale_pos.le
                      boundary_scale_le_one (by omega))
                _ ≤ boundarySignedExponent (toLex ⟨m, q⟩) :=
                  boundarySignedExponent_blockLowerBound m q
          | right _ _ hpq =>
              rw [boundarySignedExponent_mk, boundarySignedExponent_mk]
              have hs : 0 < (4 / 9 : ℝ) * scale ^ n :=
                mul_pos (by norm_num) (pow_pos boundary_scale_pos n)
              exact add_lt_add_right
                (mul_lt_mul_of_pos_left (finitePowerExponent_strictMono n hpq) hs) _

/-- The positive real Conway exponent obtained by reversing the signed exponent sequence. -/
def boundaryConwayExponent (x : BoundaryIndex) : ℝ :=
  -boundarySignedExponent x

@[simp]
theorem boundaryConwayExponent_apply (x : BoundaryIndex) :
    boundaryConwayExponent x = -boundarySignedExponent x := by
  rfl

/-- Every boundary Conway exponent is positive. -/
theorem boundaryConwayExponent_pos (x : BoundaryIndex) :
    0 < boundaryConwayExponent x := by
  exact neg_pos.mpr (boundarySignedExponent_neg x)

/-- The boundary Conway exponents strictly decrease along the index order. -/
theorem boundaryConwayExponent_strictAnti : StrictAnti boundaryConwayExponent := by
  intro x y hxy
  exact neg_lt_neg (boundarySignedExponent_strictMono hxy)

/-- The positive Conway exponents in the `n`-th block lie in
`(scale ^ (n + 1), scale ^ n]`. -/
theorem boundaryConwayExponent_mem_block (n : ℕ) (p : FiniteLex n) :
    boundaryConwayExponent (toLex ⟨n, p⟩) ∈
      Set.Ioc (scale ^ (n + 1)) (scale ^ n) := by
  rw [Set.mem_Ioc, boundaryConwayExponent_apply]
  exact ⟨by
    simpa using neg_lt_neg (boundarySignedExponent_lt_blockLimit n p),
    by simpa using neg_le_neg (boundarySignedExponent_blockLowerBound n p)⟩

/-- The surreal Conway exponent associated to an index. -/
def boundaryExponentAtIndex (x : BoundaryIndex) : Surreal.{0} :=
  (boundaryConwayExponent x : ℝ)

/-- Every surreal boundary exponent is positive. -/
theorem boundaryExponentAtIndex_pos (x : BoundaryIndex) :
    0 < boundaryExponentAtIndex x := by
  simpa only [boundaryExponentAtIndex, Real.toSurreal_pos_iff] using
    boundaryConwayExponent_pos x

/-- The surreal boundary exponents strictly decrease along the index order. -/
theorem boundaryExponentAtIndex_strictAnti : StrictAnti boundaryExponentAtIndex := by
  intro x y hxy
  simpa only [boundaryExponentAtIndex, Real.toSurreal_lt_iff] using
    boundaryConwayExponent_strictAnti hxy

/-- The coefficient function equal to one exactly on the boundary exponents. -/
def boundaryCoefficient (i : Surreal.{0}) : ℝ :=
  by
    classical
    exact if i ∈ Set.range boundaryExponentAtIndex then 1 else 0

private theorem support_boundaryCoefficient :
    Function.support boundaryCoefficient = Set.range boundaryExponentAtIndex := by
  classical
  ext i
  simp [Function.support, boundaryCoefficient]

/-- The boundary coefficient support is a small set. -/
theorem small_support_boundaryCoefficient :
    Small.{0} (Function.support boundaryCoefficient) := by
  rw [support_boundaryCoefficient]
  infer_instance

/-- The boundary coefficient support is reverse well-ordered. -/
theorem wellFoundedOn_support_boundaryCoefficient :
    (Function.support boundaryCoefficient).WellFoundedOn (· > ·) := by
  rw [support_boundaryCoefficient, Set.wellFoundedOn_range]
  convert wellFounded_lt (α := BoundaryIndex) using 1
  ext x y
  exact boundaryExponentAtIndex_strictAnti.lt_iff_gt

/-- The coefficient-one Conway normal form whose support has order type `ω ^ ω`. -/
def boundaryNormalForm : SurrealHahnSeries.{0} :=
  SurrealHahnSeries.mk boundaryCoefficient
    small_support_boundaryCoefficient
    wellFoundedOn_support_boundaryCoefficient

@[simp]
theorem boundaryNormalForm_coeff (i : Surreal.{0}) :
    boundaryNormalForm.coeff i = boundaryCoefficient i := by
  rw [boundaryNormalForm, SurrealHahnSeries.coeff_mk, boundaryCoefficient]

@[simp]
theorem boundaryNormalForm_support :
    boundaryNormalForm.support = Set.range boundaryExponentAtIndex := by
  rw [boundaryNormalForm, SurrealHahnSeries.support_mk, support_boundaryCoefficient]

/-- The boundary normal form has Conway length exactly `ω ^ ω`. -/
theorem boundaryNormalForm_length :
    boundaryNormalForm.length = Ordinal.omega0 ^ Ordinal.omega0 := by
  let f : BoundaryIndex → Surrealᵒᵈ :=
    fun x ↦ OrderDual.toDual (boundaryExponentAtIndex x)
  have hf : StrictMono f := by
    intro x y hxy
    exact boundaryExponentAtIndex_strictAnti hxy
  let eRange : BoundaryIndex ≃o Set.range f := hf.orderIso f
  let eSupport : boundaryNormalForm.support ≃ Set.range f := {
    toFun x := ⟨OrderDual.toDual x.1, by
      have hx : x.1 ∈ Set.range boundaryExponentAtIndex := by
        rw [← boundaryNormalForm_support]
        exact x.2
      obtain ⟨p, hp⟩ := hx
      exact ⟨p, congrArg OrderDual.toDual hp⟩⟩
    invFun x := ⟨OrderDual.ofDual x.1, by
      rw [boundaryNormalForm_support]
      obtain ⟨p, hp⟩ := x.2
      exact ⟨p, congrArg OrderDual.ofDual hp⟩⟩
    left_inv x := Subtype.ext rfl
    right_inv x := Subtype.ext rfl }
  let eSupportRel :
      (· > · : boundaryNormalForm.support → boundaryNormalForm.support → Prop) ≃r
      (· < · : Set.range f → Set.range f → Prop) := {
    toEquiv := eSupport
    map_rel_iff' := by intro x y; rfl }
  let e :
      (· > · : boundaryNormalForm.support → boundaryNormalForm.support → Prop) ≃r
      (· < · : BoundaryIndex → BoundaryIndex → Prop) :=
    eSupportRel.trans eRange.symm.toRelIsoLT
  have htype :
      Ordinal.type (α := boundaryNormalForm.support) (· > ·) =
        Ordinal.lift.{1, 0}
          (Ordinal.type ((· < ·) : BoundaryIndex → BoundaryIndex → Prop)) := by
    simpa only [Ordinal.lift_id'] using e.ordinal_lift_type_eq
  have hsupport := SurrealHahnSeries.type_support boundaryNormalForm
  rw [htype, typeLT_boundaryIndex] at hsupport
  exact Ordinal.lift_inj.mp hsupport.symm

theorem boundaryNormalForm_coeff_exponent (x : BoundaryIndex) :
    boundaryNormalForm.coeff (boundaryExponentAtIndex x) = 1 := by
  classical
  rw [boundaryNormalForm_coeff, boundaryCoefficient, if_pos]
  exact ⟨x, rfl⟩

theorem boundaryNormalForm_coeff_zero : boundaryNormalForm.coeff 0 = 0 := by
  classical
  rw [boundaryNormalForm_coeff, boundaryCoefficient, if_neg]
  rintro ⟨x, hx⟩
  have hxpos := boundaryExponentAtIndex_pos x
  rw [hx] at hxpos
  exact (lt_irrefl 0 hxpos).elim

private theorem boundaryNormalForm_support_nonnegative :
    boundaryNormalForm.support ⊆ Set.Ici 0 := by
  rw [boundaryNormalForm_support]
  rintro i ⟨x, rfl⟩
  exact (boundaryExponentAtIndex_pos x).le

/-- The purely infinite coefficient-one normal form as an omnific integer. -/
def boundaryOz : Oz.OmnificInteger.{0} :=
  ⟨boundaryNormalForm, by
    rw [Oz.mem_omnificIntegers]
    exact ⟨boundaryNormalForm_support_nonnegative,
      ⟨0, by simpa using boundaryNormalForm_coeff_zero.symm⟩⟩⟩

@[simp]
theorem boundaryOz_val : boundaryOz.1 = boundaryNormalForm := by
  rfl

theorem boundaryOz_support :
    boundaryOz.1.support = Set.range boundaryExponentAtIndex := by
  rw [boundaryOz_val, boundaryNormalForm_support]

theorem boundaryOz_coeff_exponent (x : BoundaryIndex) :
    boundaryOz.1.coeff (boundaryExponentAtIndex x) = 1 := by
  rw [boundaryOz_val, boundaryNormalForm_coeff_exponent]

theorem boundaryOz_coeff_zero : boundaryOz.1.coeff 0 = 0 := by
  rw [boundaryOz_val, boundaryNormalForm_coeff_zero]

/-- The boundary omnific integer has Conway length exactly `ω ^ ω`. -/
theorem boundaryOz_length :
    boundaryOz.1.length = Ordinal.omega0 ^ Ordinal.omega0 := by
  rw [boundaryOz_val, boundaryNormalForm_length]

/-- The boundary omnific integer is not an integer constant. -/
theorem boundaryOz_not_isOrdinaryInteger :
    ¬ Oz.IsOrdinaryInteger boundaryOz := by
  rw [Oz.IsOrdinaryInteger]
  rintro ⟨z, hz⟩
  let x : BoundaryIndex := toLex ⟨0, ()⟩
  let e : Surreal := boundaryExponentAtIndex x
  have he0 : e ≠ 0 := (boundaryExponentAtIndex_pos x).ne'
  have hcoeff := congrArg (fun q : SurrealHahnSeries ↦ q.coeff e) hz
  have hleft : boundaryOz.1.coeff e = 1 := by
    rw [boundaryOz_val]
    exact boundaryNormalForm_coeff_exponent x
  have hright : (z : SurrealHahnSeries).coeff e = 0 := by
    rw [Oz.intCast_eq_single_zero]
    exact SurrealHahnSeries.coeff_single_of_ne he0.symm _
  rw [hleft, hright] at hcoeff
  norm_num at hcoeff

private theorem boundaryOz_ne_zero : boundaryOz ≠ 0 := by
  intro hzero
  apply boundaryOz_not_isOrdinaryInteger
  refine ⟨0, ?_⟩
  rw [hzero, Oz.intCast_eq_single_zero]
  norm_num

/-- The boundary omnific integer is reduced. -/
theorem boundaryOz_isReduced : Oz.IsReduced boundaryOz := by
  rw [Oz.IsReduced]
  refine ⟨boundaryOz_ne_zero, 0, ?_⟩
  intro i hi
  change ArchimedeanClass.mk i = 0
  have hiSupport := hi.1
  rw [boundaryOz_support] at hiSupport
  obtain ⟨x, hx⟩ := hiSupport
  rw [← hx, boundaryExponentAtIndex]
  exact Surreal.mk_realCast (boundaryConwayExponent_pos x).ne'

private theorem lift_omega0_opow_natCast_boundary (n : ℕ) :
    Ordinal.lift.{1, 0} ((Ordinal.omega0 : Ordinal.{0}) ^ (n : Ordinal)) =
      (Ordinal.omega0 : Ordinal.{1}) ^ (n : Ordinal) := by
  rw [Ordinal.opow_natCast, Ordinal.opow_natCast]
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, Ordinal.lift_mul, ih]

private theorem omegaPowOmega_le_lift_boundaryOz_length :
    (Ordinal.omega0 : Ordinal.{1}) ^ (Ordinal.omega0 : Ordinal.{1}) ≤
      Ordinal.lift.{1, 0} boundaryOz.1.length := by
  rw [Ordinal.opow_limit Ordinal.omega0_ne_zero Ordinal.isSuccLimit_omega0]
  apply Ordinal.iSup_le
  intro i
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp i.2
  rw [hn, ← lift_omega0_opow_natCast_boundary]
  rw [Ordinal.lift_le, boundaryOz_length]
  exact Ordinal.opow_le_opow_right Ordinal.omega0_pos
    (Ordinal.natCast_lt_omega0 n).le

/-- The boundary omnific integer does not satisfy the strict finite-degree inequality. -/
theorem boundaryOz_not_hasFiniteDegree : ¬ Oz.HasFiniteDegree boundaryOz := by
  rw [Oz.HasFiniteDegree]
  exact not_lt_of_ge omegaPowOmega_le_lift_boundaryOz_length

end ConwayRefinement.Standalone.Oz.OmegaOmegaBoundary
