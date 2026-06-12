/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Term.Basic

/-! # Basic -/


noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

/-- Imported declaration from the Incompleteness formalization. -/
def qqRel (k r v : V) : V := ⟪0, k, r, v⟫ + 1

/-- Imported declaration from the Incompleteness formalization. -/
def qqNRel (k r v : V) : V := ⟪1, k, r, v⟫ + 1

/-- Imported declaration from the Incompleteness formalization. -/
def qqVerum : V := ⟪2, 0⟫ + 1

/-- Imported declaration from the Incompleteness formalization. -/
def qqFalsum : V := ⟪3, 0⟫ + 1

/-- Imported declaration from the Incompleteness formalization. -/
def qqAnd (p q : V) : V := ⟪4, p, q⟫ + 1

/-- Imported declaration from the Incompleteness formalization. -/
def qqOr (p q : V) : V := ⟪5, p, q⟫ + 1

/-- Imported declaration from the Incompleteness formalization. -/
def qqAll (p : V) : V := ⟪6, p⟫ + 1

/-- Imported declaration from the Incompleteness formalization. -/
def qqEx (p : V) : V := ⟪7, p⟫ + 1

/-- Imported declaration from the Incompleteness formalization. -/
scoped prefix:max "^rel " => qqRel

/-- Imported declaration from the Incompleteness formalization. -/
scoped prefix:max "^nrel " => qqNRel

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "^⊤" => qqVerum

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "^⊥" => qqFalsum

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation p:69 " ^⋏ " q:70 => qqAnd p q

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation p:68 " ^⋎ " q:69 => qqOr p q

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "^∀ " p:64 => qqAll p

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "^∃ " p:64 => qqEx p

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.qqRelDef : Sg0.Semisentence 4 :=
  .mkSigma “p k r v. ∃ p' < p, !pair₄Def p' 0 k r v ∧ p = p' + 1” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.qqNRelDef : Sg0.Semisentence 4 :=
  .mkSigma “p k r v. ∃ p' < p, !pair₄Def p' 1 k r v ∧ p = p' + 1” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.qqVerumDef : Sg0.Semisentence 1 :=
  .mkSigma “p. ∃ p' < p, !pairDef p' 2 0 ∧ p = p' + 1” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.qqFalsumDef : Sg0.Semisentence 1 :=
  .mkSigma “p. ∃ p' < p, !pairDef p' 3 0 ∧ p = p' + 1” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.qqAndDef : Sg0.Semisentence 3 :=
  .mkSigma “r p q. ∃ r' < r, !pair₃Def r' 4 p q ∧ r = r' + 1” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.qqOrDef : Sg0.Semisentence 3 :=
  .mkSigma “r p q. ∃ r' < r, !pair₃Def r' 5 p q ∧ r = r' + 1” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.qqAllDef : Sg0.Semisentence 2 :=
  .mkSigma “r p. ∃ r' < r, !pairDef r' 6 p ∧ r = r' + 1” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.qqExDef : Sg0.Semisentence 2 :=
  .mkSigma “r p. ∃ r' < r, !pairDef r' 7 p ∧ r = r' + 1” (by simp)

lemma qqRel_defined : Sg0-Function₃ (qqRel : V → V → V → V) via qqRelDef := by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.succ_two_eq_three,
    Nat.reduceAdd, qqRelDef, Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_bexLT, Semiterm.val_bvar, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecCons_zero, Semiterm.val_const,
    Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero, Matrix.cons_app_two,
    Matrix.cons_app_three, Matrix.cons_val_fin_one, Matrix.cons_app_four,
    Matrix.constant_eq_singleton, eval_pair₄Def, Matrix.cons_val_one,
    Semiformula.eval_operator₂, Semiterm.val_operator₂, ORingStruc.one_eq_one,
    Structure.Add.add, Structure.Eq.eq, LogicalConnective.Prop.and_eq, ↓existsAndEq, true_and]
  constructor
  · intro h
    rw [h]
    exact ⟨by simp [qqRel], by simp [qqRel]⟩
  · rintro ⟨_, h⟩
    exact h

lemma qqNRel_defined : Sg0-Function₃ (qqNRel : V → V → V → V) via qqNRelDef := by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.succ_two_eq_three,
    Nat.reduceAdd, qqNRelDef, Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_bexLT, Semiterm.val_bvar, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecCons_zero, Semiterm.val_const,
    Structure.numeral_eq_numeral, ORingStruc.one_eq_one, Matrix.cons_app_two,
    Matrix.cons_app_three, Matrix.cons_val_fin_one, Matrix.cons_app_four,
    Matrix.constant_eq_singleton, eval_pair₄Def, Matrix.cons_val_one,
    Semiformula.eval_operator₂, Semiterm.val_operator₂, Structure.Add.add, Structure.Eq.eq,
    LogicalConnective.Prop.and_eq, ↓existsAndEq, true_and]
  constructor
  · intro h
    rw [h]
    exact ⟨by simp [qqNRel], by simp [qqNRel]⟩
  · rintro ⟨_, h⟩
    exact h

lemma qqVerum_defined : Sg0-Function₀ (qqVerum : V) via qqVerumDef := by
  intro v
  simp only [Fin.isValue, Nat.reduceAdd, qqVerumDef, Nat.succ_eq_add_one,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.vecCons_zero, Semiterm.val_const, Structure.numeral_eq_numeral, numeral_two_eq_two,
    Matrix.cons_val_fin_one, ORingStruc.zero_eq_zero, Matrix.constant_eq_singleton,
    pair_defined_iff, Matrix.cons_val_one, Matrix.cons_app_two, Semiformula.eval_operator₂,
    Semiterm.val_operator₂, ORingStruc.one_eq_one, Structure.Add.add, Structure.Eq.eq,
    LogicalConnective.Prop.and_eq, ↓existsAndEq, true_and]
  constructor
  · intro h
    rw [h]
    exact ⟨by simp [qqVerum], by simp [qqVerum]⟩
  · rintro ⟨_, h⟩
    exact h

lemma qqFalsum_defined : Sg0-Function₀ (qqFalsum : V) via qqFalsumDef := by
  intro v
  simp only [Fin.isValue, Nat.reduceAdd, qqFalsumDef, Nat.succ_eq_add_one,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.vecCons_zero, Semiterm.val_const, Structure.numeral_eq_numeral, numeral_three_eq_three,
    Matrix.cons_val_fin_one, ORingStruc.zero_eq_zero, Matrix.constant_eq_singleton,
    pair_defined_iff, Matrix.cons_val_one, Matrix.cons_app_two, Semiformula.eval_operator₂,
    Semiterm.val_operator₂, ORingStruc.one_eq_one, Structure.Add.add, Structure.Eq.eq,
    LogicalConnective.Prop.and_eq, ↓existsAndEq, true_and]
  constructor
  · intro h
    rw [h]
    exact ⟨by simp [qqFalsum], by simp [qqFalsum]⟩
  · rintro ⟨_, h⟩
    exact h

lemma qqAnd_defined : Sg0-Function₂ (qqAnd : V → V → V) via qqAndDef := by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.reduceAdd,
    qqAndDef, Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_bexLT, Semiterm.val_bvar, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecCons_zero, Semiterm.val_const,
    Structure.numeral_eq_numeral, numeral_four_eq_four, Matrix.cons_app_two,
    Matrix.cons_val_fin_one, Matrix.cons_app_three, Matrix.constant_eq_singleton,
    eval_pair₃Def, Matrix.cons_val_one, Semiformula.eval_operator₂, Semiterm.val_operator₂,
    ORingStruc.one_eq_one, Structure.Add.add, Structure.Eq.eq, LogicalConnective.Prop.and_eq,
    ↓existsAndEq, true_and]
  constructor
  · intro h
    rw [h]
    exact ⟨by simp [qqAnd], by simp [qqAnd]⟩
  · rintro ⟨_, h⟩
    exact h

lemma qqOr_defined : Sg0-Function₂ (qqOr : V → V → V) via qqOrDef := by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.reduceAdd,
    qqOrDef, Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_bexLT, Semiterm.val_bvar, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecCons_zero, Semiterm.val_const,
    Structure.numeral_eq_numeral, numeral_eq_natCast, Nat.cast_ofNat, Matrix.cons_app_two,
    Matrix.cons_val_fin_one, Matrix.cons_app_three, Matrix.constant_eq_singleton,
    eval_pair₃Def, Matrix.cons_val_one, Semiformula.eval_operator₂, Semiterm.val_operator₂,
    Nat.cast_one, Structure.Add.add, Structure.Eq.eq, LogicalConnective.Prop.and_eq,
    ↓existsAndEq, true_and]
  constructor
  · intro h
    rw [h]
    exact ⟨by simp [qqOr], by simp [qqOr]⟩
  · rintro ⟨_, h⟩
    exact h

lemma qqForall_defined : Sg0-Function₁ (qqAll : V → V) via qqAllDef := by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, qqAllDef,
    Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT,
    Semiterm.val_bvar, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.vecCons_zero, Semiterm.val_const, Structure.numeral_eq_numeral,
    numeral_eq_natCast, Nat.cast_ofNat, Matrix.cons_val_fin_one, Matrix.cons_app_two,
    Matrix.constant_eq_singleton, pair_defined_iff, Matrix.cons_val_one,
    Semiformula.eval_operator₂, Semiterm.val_operator₂, Nat.cast_one, Structure.Add.add,
    Structure.Eq.eq, LogicalConnective.Prop.and_eq, ↓existsAndEq, true_and]
  constructor
  · intro h
    rw [h]
    exact ⟨by simp [qqAll], by simp [qqAll]⟩
  · rintro ⟨_, h⟩
    exact h

lemma qqExists_defined : Sg0-Function₁ (qqEx : V → V) via qqExDef := by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, qqExDef,
    Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT,
    Semiterm.val_bvar, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.vecCons_zero, Semiterm.val_const, Structure.numeral_eq_numeral,
    numeral_eq_natCast, Nat.cast_ofNat, Matrix.cons_val_fin_one, Matrix.cons_app_two,
    Matrix.constant_eq_singleton, pair_defined_iff, Matrix.cons_val_one,
    Semiformula.eval_operator₂, Semiterm.val_operator₂, Nat.cast_one, Structure.Add.add,
    Structure.Eq.eq, LogicalConnective.Prop.and_eq, ↓existsAndEq, true_and]
  constructor
  · intro h
    rw [h]
    exact ⟨by simp [qqEx], by simp [qqEx]⟩
  · rintro ⟨_, h⟩
    exact h

@[simp] lemma eval_qqRelDef (v) :
    Semiformula.Evalbm V v qqRelDef.val ↔ v 0 = ^rel (v 1) (v 2) (v 3) := qqRel_defined.df.iff v

@[simp] lemma eval_qqNRelDef (v) :
    Semiformula.Evalbm V v qqNRelDef.val ↔ v 0 = ^nrel (v 1) (v 2) (v 3) := qqNRel_defined.df.iff v

@[simp] lemma eval_qqVerumDef (v) :
    Semiformula.Evalbm V v qqVerumDef.val ↔ v 0 = ^⊤ := qqVerum_defined.df.iff v

@[simp] lemma eval_qqFalsumDef (v) :
    Semiformula.Evalbm V v qqFalsumDef.val ↔ v 0 = ^⊥ := qqFalsum_defined.df.iff v

@[simp] lemma eval_qqAndDef (v) :
    Semiformula.Evalbm V v qqAndDef.val ↔ v 0 = (v 1) ^⋏ (v 2) := qqAnd_defined.df.iff v

@[simp] lemma eval_qqOrDef (v) :
    Semiformula.Evalbm V v qqOrDef.val ↔ v 0 = (v 1) ^⋎ (v 2) := qqOr_defined.df.iff v

@[simp] lemma eval_qqAllDef (v) :
    Semiformula.Evalbm V v qqAllDef.val ↔ v 0 = ^∀ (v 1) := qqForall_defined.df.iff v

@[simp] lemma eval_qqExDef (v) :
    Semiformula.Evalbm V v qqExDef.val ↔ v 0 = ^∃ (v 1) := qqExists_defined.df.iff v

instance (ℌ : HierarchySymbol) :
    ℌ-Function₃ (qqRel : V → V → V → V) :=
  .of_zero qqRel_defined.to_definable

instance (ℌ : HierarchySymbol) :
    ℌ-Function₃ (qqNRel : V → V → V → V) :=
  .of_zero qqNRel_defined.to_definable

-- instance (ℌ : HierarchySymbol) : ℌ-Function₀ (qqVerum : V) :=
--   .of_zero qqVerum_defined.to_definable

-- instance (ℌ : HierarchySymbol) : ℌ-Function₁ (qqFalsum : V →
--     V) := .of_zero qqFalsum_defined.to_definable

instance (ℌ : HierarchySymbol) :
    ℌ-Function₂ (qqAnd : V → V → V) :=
  .of_zero qqAnd_defined.to_definable

instance (ℌ : HierarchySymbol) :
    ℌ-Function₂ (qqOr : V → V → V) :=
  .of_zero qqOr_defined.to_definable

instance (ℌ : HierarchySymbol) :
    ℌ-Function₁ (qqAll : V → V) :=
  .of_zero qqForall_defined.to_definable

instance (ℌ : HierarchySymbol) :
    ℌ-Function₁ (qqEx : V → V) :=
  .of_zero qqExists_defined.to_definable

end «lp_section_1»

@[simp] lemma qqRel_inj (k₁ r₁ v₁ k₂ r₂ v₂ : V) :
    ^rel k₁ r₁ v₁ = ^rel k₂ r₂ v₂ ↔ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqRel]
@[simp] lemma qqNRel_inj (k₁ r₁ v₁ k₂ r₂ v₂ : V) :
    ^nrel k₁ r₁ v₁ = ^nrel k₂ r₂ v₂ ↔ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqNRel]
@[simp] lemma qqAnd_inj (p₁ q₁ p₂ q₂ : V) :
    p₁ ^⋏ q₁ = p₂ ^⋏ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by
  simp [qqAnd]
@[simp] lemma qqOr_inj (p₁ q₁ p₂ q₂ : V) : p₁ ^⋎ q₁ = p₂ ^⋎ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by simp [qqOr]
@[simp] lemma qqAll_inj (p₁ p₂ : V) : ^∀ p₁ = ^∀ p₂ ↔ p₁ = p₂ := by simp [qqAll]
@[simp] lemma qqEx_inj (p₁ p₂ : V) : ^∃ p₁ = ^∃ p₂ ↔ p₁ = p₂ := by simp [qqEx]

@[simp] lemma arity_lt_rel (k r v : V) : k < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left k ⟪r, v⟫) <| le_pair_right _ _
@[simp] lemma r_lt_rel (k r v : V) : r < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
      le_pair_right _ _
@[simp] lemma v_lt_rel (k r v : V) : v < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <|
      le_pair_right _ _

@[simp] lemma arity_lt_nrel (k r v : V) :
    k < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma r_lt_nrel (k r v : V) : r < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
      le_pair_right _ _
@[simp] lemma v_lt_nrel (k r v : V) : v < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <|
      le_pair_right _ _

lemma nth_lt_qqRel_of_lt {i k r v : V} (hi : i < len v) : v.[i] < ^rel k r v :=
  lt_trans (nth_lt_self hi) (v_lt_rel _ _ _)

lemma nth_lt_qqNRel_of_lt {i k r v : V} (hi : i < len v) : v.[i] < ^nrel k r v :=
  lt_trans (nth_lt_self hi) (v_lt_nrel _ _ _)

@[simp] lemma lt_and_left (p q : V) :
    p < p ^⋏ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma lt_and_right (p q : V) :
    q < p ^⋏ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma lt_or_left (p q : V) :
    p < p ^⋎ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma lt_or_right (p q : V) :
    q < p ^⋎ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma lt_forall (p : V) : p < ^∀ p := le_iff_lt_succ.mp <| le_pair_right _ _

@[simp] lemma lt_exists (p : V) : p < ^∃ p := le_iff_lt_succ.mp <| le_pair_right _ _

namespace FormalizedFormula

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
def Phi (C : Set V) (p : V) : Prop :=
  (∃ k R v, L.Rel k R ∧ L.IsUTermVec k v ∧ p = ^rel k R v) ∨
  (∃ k R v, L.Rel k R ∧ L.IsUTermVec k v ∧ p = ^nrel k R v) ∨
  (p = ^⊤) ∨
  (p = ^⊥) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∀ p₁) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∃ p₁)

private lemma phi_iff (C p : V) :
    Phi L {x | x ∈ C} p ↔
    (∃ k < p, ∃ r < p, ∃ v < p, L.Rel k r ∧ L.IsUTermVec k v ∧ p = ^rel k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, L.Rel k r ∧ L.IsUTermVec k v ∧ p = ^nrel k r v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ p = ^∀ p₁) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ p = ^∃ p₁) where
  mp := by
    rintro (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | H)
    · left; refine ⟨k, ?_, r, ?_, v, ?_, hkr, hv, rfl⟩ <;> simp
    · right; left; refine ⟨k, ?_, r, ?_, v, ?_, hkr, hv, rfl⟩ <;> simp
    right; right
    rcases H with (rfl | rfl | H)
    · left; rfl
    · right; left; rfl
    right; right
    rcases H with (⟨q, r, hp, hq, rfl⟩ | ⟨q, r, hp, hq, rfl⟩ | H)
    · left; refine ⟨q, ?_, r, ?_, hp, hq, rfl⟩ <;> simp
    · right; left; refine ⟨q, ?_, r, ?_, hp, hq, rfl⟩ <;> simp
    right; right
    rcases H with (⟨q, h, rfl⟩ | ⟨q, h, rfl⟩)
    · left; refine ⟨q, ?_, h, rfl⟩; simp
    · right; refine ⟨q, ?_, h, rfl⟩; simp
  mpr := by
    unfold Phi
    rintro (⟨k, _, r, _, v, _, hkr, hv, rfl⟩ | ⟨k, _, r, _, v, _, hkr, hv, rfl⟩ | H)
    · left; exact ⟨k, r, v, hkr, hv, rfl⟩
    · right; left; exact ⟨k, r, v, hkr, hv, rfl⟩
    right; right
    rcases H with (rfl | rfl | H)
    · left; rfl
    · right; left; rfl
    right; right
    rcases H with (⟨q, _, r, _, hq, hr, rfl⟩ | ⟨q, _, r, _, hq, hr, rfl⟩ | H)
    · left; exact ⟨q, r, hq, hr, rfl⟩
    · right; left; exact ⟨q, r, hq, hr, rfl⟩
    right; right
    rcases H with (⟨q, _, hq, rfl⟩ | ⟨q, _, hq, rfl⟩)
    · left; exact ⟨q, hq, rfl⟩
    · right; exact ⟨q, hq, rfl⟩

/-- Imported declaration from the Incompleteness formalization. -/
def formulaAux : Sg0.Semisentence 2 := .mkSigma
  “p C.
    !qqVerumDef p ∨
    !qqFalsumDef p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqAllDef p p₁) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqExDef p p₁)”
  (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def blueprint (pL : LDef) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma
    “p C.
      (∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.isUTermVecDef.sigma k v ∧ !qqRelDef p k r v) ∨
      (∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.isUTermVecDef.sigma k v ∧ !qqNRelDef p k r v) ∨
      !formulaAux p C” (by simp))
  (.mkPi
    “p C.
      (∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.isUTermVecDef.pi k v ∧ !qqRelDef p k r v) ∨
      (∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.isUTermVecDef.pi k v ∧ !qqNRelDef p k r v) ∨
      !formulaAux p C” (by simp))⟩

/-- Imported declaration from the Incompleteness formalization. -/
def construction : Fixpoint.Construction V (blueprint pL) where
  Φ := fun _ ↦ Phi L
  defined := ⟨
    by  intro v
        -- simp [blueprint, HierarchySymbol.Semiformula.val_sigma, L.isUTermVec_defined.proper.iff']
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, blueprint, Fin.isValue,
          HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.sigma_mkDelta,
          HierarchySymbol.Semiformula.val_mkSigma, LogicalConnective.HomClass.map_or,
          Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
          Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
          LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
          Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
          Matrix.cons_val_three, Fin.succ_one_eq_two, eval_qqRelDef, LogicalConnective.Prop.and_eq,
          eval_qqNRelDef, LogicalConnective.Prop.or_eq, HierarchySymbol.Semiformula.pi_mkDelta,
          HierarchySymbol.Semiformula.val_mkPi, L.isUTermVec_defined.proper.iff']
        ,
    by  intro v
        -- simpa [blueprint, Language.Defined.eval_rel_iff (L := L), L.isUTermVec_defined.df.iff,
        --  HierarchySymbol.Semiformula.val_sigma, formulaAux] using phi_iff L _ _
        simpa only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, blueprint,
          HierarchySymbol.Semiformula.val_sigma, formulaAux,
          HierarchySymbol.Semiformula.val_mkSigma, LogicalConnective.HomClass.map_or,
          HierarchySymbol.Semiformula.val_mkDelta, Semiformula.eval_bexLT, Semiterm.val_bvar,
          Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_two, Matrix.vecTail,
          Function.comp_apply, Fin.succ_zero_eq_one, LogicalConnective.HomClass.map_and,
          Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_zero,
          Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
          Language.Defined.eval_rel_iff (L := L), L.isUTermVec_defined.df.iff,
          Matrix.cons_val_three, Fin.succ_one_eq_two, eval_qqRelDef, LogicalConnective.Prop.and_eq,
          eval_qqNRelDef, eval_qqVerumDef, eval_qqFalsumDef, Semiformula.eval_operator₂,
          Structure.Mem.mem, eval_qqAndDef, eval_qqOrDef, eval_qqAllDef, eval_qqExDef,
          LogicalConnective.Prop.or_eq] using phi_iff L _ _⟩

  monotone := by
    unfold Phi
    rintro C C' hC _ x (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨q, r, hqC, hrC, rfl⟩ | ⟨q, r, hqC, hrC, rfl⟩ | H)
    · left; exact ⟨q, r, hC hqC, hC hrC, rfl⟩
    · right; left; exact ⟨q, r, hC hqC, hC hrC, rfl⟩
    right; right
    rcases H with (⟨q, hqC, rfl⟩ | ⟨q, hqC, rfl⟩)
    · left; exact ⟨q, hC hqC, rfl⟩
    · right; exact ⟨q, hC hqC, rfl⟩

instance : (construction L).StrongFinite V where
  strong_finite := by
    unfold construction Phi
    rintro C _ x (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨q, r, hqC, hrC, rfl⟩ | ⟨q, r, hqC, hrC, rfl⟩ | H)
    · left; exact ⟨q, r, by simp [hqC], by simp [hrC], rfl⟩
    · right; left; exact ⟨q, r, by simp [hqC], by simp [hrC], rfl⟩
    right; right
    rcases H with (⟨q, hqC, rfl⟩ | ⟨q, hqC, rfl⟩)
    · left; exact ⟨q, by simp [hqC], rfl⟩
    · right; exact ⟨q, by simp [hqC], rfl⟩

end FormalizedFormula

section «lp_section_2»

open FormalizedFormula

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.IsUFormula : V → Prop := (construction L).Fixpoint ![]

section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.LDef.isUFormulaDef (pL : LDef) : Dlt1.Semisentence 1 :=
  (blueprint pL).fixpointDefΔ₁

lemma _root_.LO.Arith.Language.isUFormula_defined :
    Dlt1-Predicate L.IsUFormula via pL.isUFormulaDef :=
  (construction L).fixpoint_definedΔ₁

instance _root_.LO.Arith.Language.isUFormulaDef_definable :
    Dlt1-Predicate L.IsUFormula :=
  L.isUFormula_defined.to_definable

instance _root_.LO.Arith.Language.isUFormulaDef_definable' :
    Γ-[m + 1]-Predicate L.IsUFormula :=
  L.isUFormulaDef_definable.of_deltaOne

end «lp_section_3»

variable {L}

lemma _root_.LO.Arith.Language.IsUFormula.case_iff {p : V} :
    L.IsUFormula p ↔
    (∃ k R v, L.Rel k R ∧ L.IsUTermVec k v ∧ p = ^rel k R v) ∨
    (∃ k R v, L.Rel k R ∧ L.IsUTermVec k v ∧ p = ^nrel k R v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ p₂, L.IsUFormula p₁ ∧ L.IsUFormula p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, L.IsUFormula p₁ ∧ L.IsUFormula p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁, L.IsUFormula p₁ ∧ p = ^∀ p₁) ∨
    (∃ p₁, L.IsUFormula p₁ ∧ p = ^∃ p₁) :=
  (construction L).case

alias ⟨Language.IsUFormula.case, Language.IsUFormula.mk⟩ := Language.IsUFormula.case_iff

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.rel {k r v : V} :
    L.IsUFormula (^rel k r v) ↔ L.Rel k r ∧ L.IsUTermVec k v :=
  ⟨by intro h
      rcases h.case with (⟨k, r, v, hkr, hv, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp_all only [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx,
            add_left_inj, pair_ext_iff, true_and, zero_ne_one, false_and,
            OfNat.zero_ne_ofNat],
   by rintro ⟨hkr, hv⟩
      exact Language.IsUFormula.mk (Or.inl ⟨k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.nrel {k r v : V} :
    L.IsUFormula (^nrel k r v) ↔ L.Rel k r ∧ L.IsUTermVec k v :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨k, r, v, hkr, hv, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp_all only [qqNRel, qqRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx,
            add_left_inj, pair_ext_iff, one_ne_zero, OfNat.one_ne_ofNat, false_and, true_and],
   by rintro ⟨hkr, hv⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inl ⟨k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.verum : L.IsUFormula ^⊤ :=
  Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inl rfl)

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.falsum : L.IsUFormula ^⊥ :=
  Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.and {p q : V} :
    L.IsUFormula (p ^⋏ q) ↔ L.IsUFormula p ∧ L.IsUFormula q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, hp, hq, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp_all only [qqAnd, qqRel, qqNRel, qqVerum, qqFalsum, qqOr, qqAll, qqEx,
            add_left_inj, pair_ext_iff, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
            OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, false_and, true_and, and_self],
   by rintro ⟨hp, hq⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p, q, hp,
        hq, rfl⟩)⟩

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.or {p q : V} :
    L.IsUFormula (p ^⋎ q) ↔ L.IsUFormula p ∧ L.IsUFormula q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, hp, hq, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp_all only [qqOr, qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqAll, qqEx,
            add_left_inj, pair_ext_iff, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
            OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, false_and, true_and, and_self],
   by rintro ⟨hp, hq⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p,
        q, hp, hq, rfl⟩)⟩

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.all {p : V} :
    L.IsUFormula (^∀ p) ↔ L.IsUFormula p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, hp, h⟩ | ⟨_, _, h⟩) <;>
          simp_all only [qqAll, qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqEx,
            add_left_inj, pair_ext_iff, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
            OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, false_and, true_and],
   by rintro hp
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inl ⟨p, hp, rfl⟩)⟩

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.ex {p : V} :
    L.IsUFormula (^∃ p) ↔ L.IsUFormula p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, hp, h⟩) <;>
          simp_all only [qqEx, qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll,
            add_left_inj, pair_ext_iff, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
            OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, false_and, true_and],
   by rintro hp
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr ⟨p, hp, rfl⟩)⟩

lemma _root_.LO.Arith.Language.IsUFormula.pos {p : V} (h : L.IsUFormula p) : 0 < p := by
  rcases h.case with (⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;>
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]

--lemma Language.IsSemiformula.pos {n p : V} (h : L.Semiformula n p) : 0 < p := h.1.pos

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.not_zero : ¬L.IsUFormula (0 :
    V) := by
  intro h; simpa using h.pos

-- @[simp] lemma Language.IsSemiformula.not_zero (m : V) : ¬L.Semiformula m (0 : V) := by
--   intro h; simpa using h.pos

/-
@[simp] lemma Language.IsSemiformula.rel {k r v : V} :
    L.IsUFormula (^rel k r v) ↔ L.Rel k r ∧ L.IsUTermVec k v := by simp
@[simp] lemma Language.IsSemiformula.nrel {n k r v : V} :
    L.Semiformula n (^nrel n k r v) ↔ L.Rel k r ∧ L.SemitermVec k n v := by
      simp [Language.IsSemiformula]
@[simp] lemma Language.IsSemiformula.verum (n : V) :
    L.Semiformula n ^⊤[n] := by
  simp [Language.IsSemiformula]
@[simp] lemma Language.IsSemiformula.falsum (n : V) :
    L.Semiformula n ^⊥[n] := by
  simp [Language.IsSemiformula]
@[simp] lemma Language.IsSemiformula.and {n p q : V} :
    L.Semiformula n (p ^⋏ q) ↔ L.Semiformula n p ∧ L.Semiformula n q := by
      simp [Language.IsSemiformula]
@[simp] lemma Language.IsSemiformula.or {n p q : V} :
    L.Semiformula n (p ^⋎ q) ↔ L.Semiformula n p ∧ L.Semiformula n q := by
      simp [Language.IsSemiformula]
@[simp] lemma Language.IsSemiformula.all {n p : V} :
    L.Semiformula n (^∀ p) ↔ L.Semiformula (n + 1) p := by
  simp [Language.IsSemiformula]
@[simp] lemma Language.IsSemiformula.ex {n p : V} :
    L.Semiformula n (^∃ p) ↔ L.Semiformula (n + 1) p := by
  simp [Language.IsSemiformula]
-/

lemma _root_.LO.Arith.Language.IsUFormula.induction1 (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hrel : ∀ k r v, L.Rel k r → L.IsUTermVec k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.Rel k r → L.IsUTermVec k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, L.IsUFormula p → L.IsUFormula q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, L.IsUFormula p → L.IsUFormula q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, L.IsUFormula p → P p → P (^∀ p))
    (hex : ∀ p, L.IsUFormula p → P p → P (^∃ p)) :
    ∀ p, L.IsUFormula p → P p :=
  (construction L).induction (v := ![]) hP (by
    rintro C hC x (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ |
      ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact hrel k r v hkr hv
    · exact hnrel k r v hkr hv
    · exact hverum
    · exact hfalsum
    · exact hand p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hor p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hall p (hC p hp).1 (hC p hp).2
    · exact hex p (hC p hp).1 (hC p hp).2)

lemma _root_.LO.Arith.Language.IsUFormula.induction_sigma1 {P : V → Prop} (hP : Sg1-Predicate P)
    (hrel : ∀ k r v, L.Rel k r → L.IsUTermVec k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.Rel k r → L.IsUTermVec k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, L.IsUFormula p → L.IsUFormula q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, L.IsUFormula p → L.IsUFormula q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, L.IsUFormula p → P p → P (^∀ p))
    (hex : ∀ p, L.IsUFormula p → P p → P (^∃ p)) :
    ∀ p, L.IsUFormula p → P p :=
  Language.IsUFormula.induction1 Sg hP hrel hnrel hverum hfalsum hand hor hall hex

lemma _root_.LO.Arith.Language.IsUFormula.induction_pi1 {P : V → Prop} (hP : Pg1-Predicate P)
    (hrel : ∀ k r v, L.Rel k r → L.IsUTermVec k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.Rel k r → L.IsUTermVec k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, L.IsUFormula p → L.IsUFormula q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, L.IsUFormula p → L.IsUFormula q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, L.IsUFormula p → P p → P (^∀ p))
    (hex : ∀ p, L.IsUFormula p → P p → P (^∃ p)) :
    ∀ p, L.IsUFormula p → P p :=
  Language.IsUFormula.induction1 Pg hP hrel hnrel hverum hfalsum hand hor hall hex

/-
lemma Language.IsSemiformula.induction (Γ) {P : V → V → Prop} (hP : Γ-[1]-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, L.Semiformula n p → P n p := by
  suffices ∀ p, L.IsUFormula p → ∀ n ≤ p, fstIdx p = n → P n p
  by rintro n p ⟨h, rfl⟩; exact this p h (fstIdx p) (by simp) rfl
  apply Language.IsUFormula.induction (P := fun p ↦ ∀ n ≤ p, fstIdx p = n → P n p) Γ
  · apply HierarchySymbol.Boldface.ball_le (by definability)
    apply HierarchySymbol.Boldface.imp (by definability)
    simp; exact hP
  · rintro n k r v hr hv _ _ rfl; simpa using hrel n k r v hr hv
  · rintro n k r v hr hv _ _ rfl; simpa using hnrel n k r v hr hv
  · rintro n _ _ rfl; simpa using hverum n
  · rintro n _ _ rfl; simpa using hfalsum n
  · rintro n p q hp hq ihp ihq _ _ rfl
    simpa using hand n p q hp hq
      (by simpa [hp.2] using ihp (fstIdx p) (by simp) rfl) (by simpa [hq.2] using ihq (fstIdx q) (by
      simp) rfl)
  · rintro n p q hp hq ihp ihq _ _ rfl
    simpa using hor n p q hp hq
      (by simpa [hp.2] using ihp (fstIdx p) (by simp) rfl) (by simpa [hq.2] using ihq (fstIdx q) (by
      simp) rfl)
  · rintro n p hp ih _ _ rfl
    simpa using hall n p hp (by simpa [hp.2] using ih (fstIdx p) (by simp) rfl)
  · rintro n p hp ih _ _ rfl
    simpa using hex n p hp (by simpa [hp.2] using ih (fstIdx p) (by simp) rfl)

lemma Language.IsSemiformula.induction_sigma₁ {P : V → V → Prop} (hP : Sg1-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, L.Semiformula n p → P n p :=
  Language.IsSemiformula.induction Sg hP hrel hnrel hverum hfalsum hand hor hall hex

lemma Language.IsSemiformula.induction_pi1 {P : V → V → Prop} (hP : Pg1-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, L.Semiformula n p → P n p :=
  Language.IsSemiformula.induction Pg hP hrel hnrel hverum hfalsum hand hor hall hex
-/

end «lp_section_2»

namespace Language
namespace UformulaRec1

/-- Imported declaration from the Incompleteness formalization. -/
structure Blueprint (pL : LDef) where
  /-- Imported declaration from the Incompleteness formalization. -/
  rel : Sg1.Semisentence 5
  /-- Imported declaration from the Incompleteness formalization. -/
  nrel       : Sg1.Semisentence 5
  /-- Imported declaration from the Incompleteness formalization. -/
  verum      : Sg1.Semisentence 2
  /-- Imported declaration from the Incompleteness formalization. -/
  falsum     : Sg1.Semisentence 2
  /-- Imported declaration from the Incompleteness formalization. -/
  and        : Sg1.Semisentence 6
  /-- Imported declaration from the Incompleteness formalization. -/
  or         : Sg1.Semisentence 6
  /-- Imported declaration from the Incompleteness formalization. -/
  all        : Sg1.Semisentence 4
  /-- Imported declaration from the Incompleteness formalization. -/
  ex         : Sg1.Semisentence 4
  /-- Imported declaration from the Incompleteness formalization. -/
  allChanges : Sg1.Semisentence 2
  /-- Imported declaration from the Incompleteness formalization. -/
  exChanges  : Sg1.Semisentence 2

namespace Blueprint

variable {pL : LDef} (β : Blueprint pL)

/-- Imported declaration from the Incompleteness formalization. -/
def blueprint (β : Blueprint pL) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !pL.isUFormulaDef.sigma p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p k R v ∧ !β.rel y param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p k R v ∧ !β.nrel y param k R v) ∨
    (!qqVerumDef p ∧ !β.verum y param) ∨
    (!qqFalsumDef p ∧ !β.falsum y param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqAndDef p p₁ p₂ ∧
        !β.and y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqOrDef p p₁ p₂ ∧ !β.or y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      (∃ param', !β.allChanges param' param ∧ :⟪param', p₁, y₁⟫:∈ C) ∧ !qqAllDef p p₁ ∧
        !β.all y param p₁ y₁) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      (∃ param', !β.exChanges param' param ∧ :⟪param', p₁, y₁⟫:∈ C) ∧ !qqExDef p p₁ ∧
        !β.ex y param p₁ y₁))
  ” (by simp))
  (.mkPi “pr C.
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !pL.isUFormulaDef.pi p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p k R v ∧ !β.rel.graphDelta.pi.val y param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p k R v ∧ !β.nrel.graphDelta.pi.val y param k R v) ∨
    (!qqVerumDef p ∧ !β.verum.graphDelta.pi.val y param) ∨
    (!qqFalsumDef p ∧ !β.falsum.graphDelta.pi.val y param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqAndDef p p₁ p₂ ∧
        !β.and.graphDelta.pi.val y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqOrDef p p₁ p₂ ∧
        !β.or.graphDelta.pi.val y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      (∀ param', !β.allChanges param' param →
        :⟪param', p₁, y₁⟫:∈ C) ∧ !qqAllDef p p₁ ∧ !β.all.graphDelta.pi.val y param p₁ y₁) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      (∀ param', !β.exChanges param' param →
        :⟪param', p₁, y₁⟫:∈ C) ∧ !qqExDef p p₁ ∧ !β.ex.graphDelta.pi.val y param p₁ y₁))
  ” (by simp))⟩

/-- Imported declaration from the Incompleteness formalization. -/
def graph : Sg1.Semisentence 3 := .mkSigma
  “param p y. ∃ pr, !pair₃Def pr param p y ∧ !β.blueprint.fixpointDef pr” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def result : Sg1.Semisentence 3 := .mkSigma
  “y param p. (!pL.isUFormulaDef.pi p → !β.graph param p y) ∧ (¬!pL.isUFormulaDef.sigma p → y =
    0)” (by simp)

end Blueprint

variable (V)

/-- Imported declaration from the Incompleteness formalization. -/
structure Construction (L : Arith.Language V) (φ : Blueprint pL) where
  /-- Imported declaration from the Incompleteness formalization. -/
  rel (param k R v : V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  nrel       (param k R v : V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  verum      (param : V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  falsum     (param : V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  and        (param p₁ p₂ y₁ y₂ : V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  or         (param p₁ p₂ y₁ y₂ : V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  all        (param p₁ y₁ : V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  ex         (param p₁ y₁ : V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  allChanges (param : V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  exChanges  (param : V) : V
  rel_defined    : Sg1-Function₄ rel via φ.rel
  nrel_defined   : Sg1-Function₄ nrel via φ.nrel
  verum_defined  : Sg1-Function₁ verum via φ.verum
  falsum_defined : Sg1-Function₁ falsum via φ.falsum
  and_defined    : Sg1-Function₅ and via φ.and
  or_defined     : Sg1-Function₅ or via φ.or
  all_defined    : Sg1-Function₃ all via φ.all
  ex_defined     : Sg1-Function₃ ex via φ.ex
  allChanges_defined : Sg1-Function₁ allChanges via φ.allChanges
  exChanges_defined  : Sg1-Function₁ exChanges via φ.exChanges

variable {V}

namespace Construction

variable {β : Blueprint pL} (c : Construction V L β)

/-- Imported declaration from the Incompleteness formalization. -/
def Phi (C : Set V) (pr : V) : Prop :=
  ∃ param p y, pr = ⟪param, p, y⟫ ∧
  L.IsUFormula p ∧ (
  (∃ k r v, p = ^rel k r v ∧ y = c.rel param k r v) ∨
  (∃ k r v, p = ^nrel k r v ∧ y = c.nrel param k r v) ∨
  (p = ^⊤ ∧ y = c.verum param) ∨
  (p = ^⊥ ∧ y = c.falsum param) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏ p₂ ∧ y =
    c.and param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎ p₂ ∧ y =
    c.or  param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ y₁, ⟪c.allChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∀ p₁ ∧ y = c.all param p₁ y₁) ∨
  (∃ p₁ y₁, ⟪c.exChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∃ p₁ ∧ y = c.ex  param p₁ y₁) )

private lemma phi_iff (C pr : V) :
    c.Phi {x | x ∈ C} pr ↔
    ∃ param ≤ pr, ∃ p ≤ pr, ∃ y ≤ pr, pr = ⟪param, p, y⟫ ∧ L.IsUFormula p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, p = ^rel k R v ∧ y = c.rel param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, p = ^nrel k R v ∧ y = c.nrel param k R v) ∨
    (p = ^⊤ ∧ y = c.verum param) ∨
    (p = ^⊥ ∧ y = c.falsum param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏ p₂ ∧ y = c.and param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎ p₂ ∧ y = c.or param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      ⟪c.allChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∀ p₁ ∧ y = c.all param p₁ y₁) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      ⟪c.exChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∃ p₁ ∧ y = c.ex param p₁ y₁)) := by
  constructor
  · rintro ⟨param, p, y, rfl, hp, H⟩
    refine ⟨param, by simp,
      p, le_trans (le_pair_left p y) (le_pair_right _ _),
      y, le_trans (le_pair_right p y) (le_pair_right _ _), rfl, hp, ?_⟩
    rcases H with (⟨k, r, v, rfl, rfl⟩ | ⟨k, r, v, rfl, rfl⟩ | H)
    · left; exact ⟨k, by simp, r, by simp, v, by simp, rfl, rfl⟩
    · right; left; exact ⟨k, by simp, r, by simp, v, by simp, rfl, rfl⟩
    right; right
    rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | H)
    · left; exact ⟨rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), y₂,
          lt_of_le_of_lt (by simp) (lt_of_mem_rng h₂),
        h₁, h₂, rfl, rfl⟩
    · right; left; exact ⟨p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), y₂,
          lt_of_le_of_lt (by simp) (lt_of_mem_rng h₂),
        h₁, h₂, rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, y₁, h₁, rfl, rfl⟩ | ⟨p₁, y₁, h₁, rfl, rfl⟩)
    · left; exact ⟨p₁, by simp, y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), h₁, rfl, rfl⟩
    · right; exact ⟨p₁, by simp, y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), h₁, rfl, rfl⟩
  · rintro ⟨param, _, p, _, y, _, rfl, hp, H⟩
    refine ⟨param, p, y, rfl, hp, ?_⟩
    rcases H with (⟨k, _, r, _, v, _, rfl, rfl⟩ | ⟨k, _, r, _, v, _, rfl, rfl⟩ | H)
    · left; exact ⟨k, r, v, rfl, rfl⟩
    · right; left; exact ⟨k, r, v, rfl, rfl⟩
    right; right
    rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | H)
    · left; exact ⟨rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩
    · right; left; exact ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, _, y₁, _, h₁, rfl, rfl⟩ | ⟨p₁, _, y₁, _, h₁, rfl, rfl⟩)
    · left; exact ⟨p₁, y₁, h₁, rfl, rfl⟩
    · right; exact ⟨p₁, y₁, h₁, rfl, rfl⟩

/-- Imported declaration from the Incompleteness formalization. -/
def construction : Fixpoint.Construction V (β.blueprint) where
  Φ := fun _ ↦ c.Phi
  defined :=
  ⟨by intro v
      /-
      simp? [HierarchySymbol.Semiformula.val_sigma, Blueprint.blueprint,
        L.isUFormula_defined.df.iff, L.isUFormula_defined.proper.iff',
        c.rel_defined.iff, c.rel_defined.graph_delta.proper.iff',
        c.nrel_defined.iff, c.nrel_defined.graph_delta.proper.iff',
        c.verum_defined.iff, c.verum_defined.graph_delta.proper.iff',
        c.falsum_defined.iff, c.falsum_defined.graph_delta.proper.iff',
        c.and_defined.iff, c.and_defined.graph_delta.proper.iff',
        c.or_defined.iff, c.or_defined.graph_delta.proper.iff',
        c.all_defined.iff, c.all_defined.graph_delta.proper.iff',
        c.ex_defined.iff, c.ex_defined.graph_delta.proper.iff',
        c.allChanges_defined.iff, c.allChanges_defined.graph_delta.proper.iff',
        c.exChanges_defined.iff, c.exChanges_defined.graph_delta.proper.iff']
      -/
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Blueprint.blueprint, Fin.isValue,
        HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.sigma_mkDelta,
        HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_two, Matrix.vecTail,
        Function.comp_apply, Fin.succ_zero_eq_one, LogicalConnective.HomClass.map_and,
        Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_three, Fin.succ_one_eq_two,
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton, eval_pair₃Def,
        L.isUFormula_defined.df.iff, LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT,
        Matrix.cons_val_four, Matrix.cons_val_succ, eval_qqRelDef, Matrix.cons_app_five,
        c.rel_defined.iff, LogicalConnective.Prop.and_eq, eval_qqNRelDef, c.nrel_defined.iff,
        eval_qqVerumDef, c.verum_defined.iff, eval_qqFalsumDef, c.falsum_defined.iff,
        Matrix.cons_app_six, Matrix.cons_app_seven, Semiformula.eval_operator₄,
        Matrix.cons_app_eight, eval_memRel₃, eval_qqAndDef, c.and_defined.iff, eval_qqOrDef,
        c.or_defined.iff, Semiformula.eval_ex, c.allChanges_defined.iff, exists_eq_left,
        eval_qqAllDef, c.all_defined.iff, c.exChanges_defined.iff, eval_qqExDef, c.ex_defined.iff,
        LogicalConnective.Prop.or_eq, HierarchySymbol.Semiformula.pi_mkDelta,
        HierarchySymbol.Semiformula.val_mkPi, L.isUFormula_defined.proper.iff',
        c.rel_defined.graph_delta.proper.iff', HierarchySymbol.Semiformula.graphDelta_val,
        c.nrel_defined.graph_delta.proper.iff', c.verum_defined.graph_delta.proper.iff',
        c.falsum_defined.graph_delta.proper.iff', c.and_defined.graph_delta.proper.iff',
        c.or_defined.graph_delta.proper.iff', Semiformula.eval_all,
        LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, forall_eq,
        c.all_defined.graph_delta.proper.iff', c.ex_defined.graph_delta.proper.iff'],
    by  intro v
        /-
        simpa? [HierarchySymbol.Semiformula.val_sigma, Blueprint.blueprint,
          L.isUFormula_defined.df.iff,
          c.rel_defined.iff,
          c.nrel_defined.iff,
          c.verum_defined.iff,
          c.falsum_defined.iff,
          c.and_defined.iff,
          c.or_defined.iff,
          c.all_defined.iff,
          c.ex_defined.iff,
          c.allChanges_defined.iff,
          c.exChanges_defined.iff] using c.phi_iff _ _
        -/
        simpa only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Blueprint.blueprint,
          HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.val_mkDelta,
          HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
          Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_two, Matrix.vecTail,
          Function.comp_apply, Fin.succ_zero_eq_one, LogicalConnective.HomClass.map_and,
          Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_three, Fin.succ_one_eq_two,
          Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
          eval_pair₃Def, L.isUFormula_defined.df.iff, LogicalConnective.HomClass.map_or,
          Semiformula.eval_bexLT, Matrix.cons_val_four, Matrix.cons_val_succ, eval_qqRelDef,
          Matrix.cons_app_five, c.rel_defined.iff, LogicalConnective.Prop.and_eq, eval_qqNRelDef,
          c.nrel_defined.iff, eval_qqVerumDef, c.verum_defined.iff, eval_qqFalsumDef,
          c.falsum_defined.iff, Matrix.cons_app_six, Matrix.cons_app_seven,
          Semiformula.eval_operator₄, Matrix.cons_app_eight, eval_memRel₃, eval_qqAndDef,
          c.and_defined.iff, eval_qqOrDef, c.or_defined.iff, Semiformula.eval_ex,
          c.allChanges_defined.iff, exists_eq_left, eval_qqAllDef, c.all_defined.iff,
          c.exChanges_defined.iff, eval_qqExDef, c.ex_defined.iff,
          LogicalConnective.Prop.or_eq] using c.phi_iff _ _⟩
  monotone := by
    unfold Phi
    rintro C C' hC _ _ ⟨param, p, y, rfl, hp, H⟩
    refine ⟨param, p, y, rfl, hp, ?_⟩
    rcases H with (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩
    · right; left; exact ⟨p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, r₁, h₁, rfl, rfl⟩ | ⟨p₁, r₁, h₁, rfl, rfl⟩)
    · left; exact ⟨p₁, r₁, hC h₁, rfl, rfl⟩
    · right; exact ⟨p₁, r₁, hC h₁, rfl, rfl⟩

instance : c.construction.Finite where
  finite {C _ pr h} := by
    rcases h with ⟨param, p, y, rfl, hp, (h | h | h | h |
      ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, y₁, h₁,
        rfl, rfl⟩ | ⟨p₁, y₁, h₁, rfl, rfl⟩)⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inl h⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inr <| Or.inl h⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inr <| Or.inr <| Or.inl h⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inr <| Or.inr <| Or.inr <| Or.inl h⟩
    · exact ⟨Max.max ⟪param, p₁, y₁⟫ ⟪param, p₂, y₂⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; left
        exact ⟨p₁, p₂, y₁, y₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl,
          rfl⟩⟩
    · exact ⟨Max.max ⟪param, p₁, y₁⟫ ⟪param, p₂, y₂⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; right; left
        exact ⟨p₁, p₂, y₁, y₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl,
          rfl⟩⟩
    · exact ⟨⟪c.allChanges param, p₁, y₁⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; right; right; left
        exact ⟨p₁, y₁, by simp [h₁], rfl, rfl⟩⟩
    · exact ⟨⟪c.exChanges param, p₁, y₁⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; right; right; right
        exact ⟨p₁, y₁, by simp [h₁], rfl, rfl⟩⟩

/-- Imported declaration from the Incompleteness formalization. -/
def Graph (param : V) (x y : V) : Prop := c.construction.Fixpoint ![] ⟪param, x, y⟫

variable {param : V}

variable {c}

lemma _root_.LO.Arith.Language.UformulaRec1.Construction.Graph.case_iff {p y : V} :
    c.Graph param p y ↔
    L.IsUFormula p ∧ (
    (∃ k R v, p = ^rel k R v ∧ y = c.rel param k R v) ∨
    (∃ k R v, p = ^nrel k R v ∧ y = c.nrel param k R v) ∨
    (p = ^⊤ ∧ y = c.verum param) ∨
    (p = ^⊥ ∧ y = c.falsum param) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph param p₁ y₁ ∧ c.Graph param p₂ y₂ ∧ p = p₁ ^⋏ p₂ ∧ y =
      c.and param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph param p₁ y₁ ∧ c.Graph param p₂ y₂ ∧ p = p₁ ^⋎ p₂ ∧ y =
      c.or param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ y₁, c.Graph (c.allChanges param) p₁ y₁ ∧ p = ^∀ p₁ ∧ y = c.all param p₁ y₁) ∨
    (∃ p₁ y₁, c.Graph (c.exChanges param) p₁ y₁ ∧ p = ^∃ p₁ ∧ y = c.ex param p₁ y₁) ) :=
  Iff.trans c.construction.case (by
    constructor
    · rintro ⟨param, p, y, e, H⟩;
      simp only [pair_ext_iff] at e; rcases e with ⟨rfl, rfl, rfl⟩
      refine H
    · intro H; exact ⟨_, _, _, rfl, H⟩)

variable (c β)

lemma graph_defined : Sg1-Relation₃ c.Graph via β.graph := by
  intro v; simp [Blueprint.graph, c.construction.fixpoint_defined.iff, Matrix.empty_eq]; rfl

lemma eval_graphDef (v) :
    Semiformula.Evalbm V v β.graph.val ↔ c.Graph (v 0) (v 1) (v 2) := (graph_defined β c).df.iff v

instance graph_definable : Sg-[0 + 1]-Relation₃ c.Graph := (c.graph_defined).to_definable

variable {β}

lemma graph_dom_uformula {p r} :
    c.Graph param p r → L.IsUFormula p := fun h ↦ Graph.case_iff.mp h |>.1

lemma graph_rel_iff {k r v y} (hkr : L.Rel k r) (hv : L.IsUTermVec k v) :
    c.Graph param (^rel k r v) y ↔ y = c.rel param k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨k, r, v, H, rfl⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp only [qqRel_inj] at H; rcases H with ⟨rfl, rfl, rfl⟩; rfl
    · simp [qqRel, qqNRel] at H
    · simp [qqRel, qqVerum] at H
    · simp [qqRel, qqFalsum] at H
    · simp [qqRel, qqAnd] at H
    · simp [qqRel, qqOr] at H
    · simp [qqRel, qqAll] at H
    · simp [qqRel, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_nrel_iff {k r v y} (hkr : L.Rel k r) (hv : L.IsUTermVec k v) :
    c.Graph param (^nrel k r v) y ↔ y = c.nrel param k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqNRel, qqRel] at H
    · simp only [qqNRel_inj] at H; rcases H with ⟨rfl, rfl, rfl⟩; rfl
    · simp [qqNRel, qqVerum] at H
    · simp [qqNRel, qqFalsum] at H
    · simp [qqNRel, qqAnd] at H
    · simp [qqNRel, qqOr] at H
    · simp [qqNRel, qqAll] at H
    · simp [qqNRel, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inr <| Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_verum_iff {y} :
    c.Graph param ^⊤ y ↔ y = c.verum param := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, rfl⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqVerum, qqRel] at H
    · simp [qqVerum, qqNRel] at H
    · simp only at H; rcases H; rfl
    · simp [qqVerum, qqFalsum] at H
    · simp [qqVerum, qqAnd] at H
    · simp [qqVerum, qqOr] at H
    · simp [qqVerum, qqAll] at H
    · simp [qqVerum, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_falsum_iff {y} :
    c.Graph param ^⊥ y ↔ y = c.falsum param := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, rfl⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqFalsum, qqRel] at H
    · simp [qqFalsum, qqNRel] at H
    · simp [qqFalsum, qqVerum] at H
    · simp only at H; rcases H; rfl
    · simp [qqFalsum, qqAnd] at H
    · simp [qqFalsum, qqOr] at H
    · simp [qqFalsum, qqAll] at H
    · simp [qqFalsum, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl,
    rfl⟩⟩

lemma graph_rel {k r v} (hkr : L.Rel k r) (hv : L.IsUTermVec k v) :
    c.Graph param (^rel k r v) (c.rel param k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_nrel {k r v} (hkr : L.Rel k r) (hv : L.IsUTermVec k v) :
    c.Graph param (^nrel k r v) (c.nrel param k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inr <| Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_verum :
    c.Graph param ^⊤ (c.verum param) :=
      (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_falsum :
    c.Graph param ^⊥ (c.falsum param) :=
      (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_and {p₁ p₂ r₁ r₂ : V} (hp₁ : L.IsUFormula p₁) (hp₂ : L.IsUFormula p₂)
    (h₁ : c.Graph param p₁ r₁) (h₂ : c.Graph param p₂ r₂) :
    c.Graph param (p₁ ^⋏ p₂) (c.and param p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁,
    p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_and_inv {p₁ p₂ r : V} :
    c.Graph param (p₁ ^⋏ p₂) r → ∃ r₁ r₂, c.Graph param p₁ r₁ ∧ c.Graph param p₂ r₂ ∧ r =
        c.and param p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqAnd, qqRel] at H
  · simp [qqAnd, qqNRel] at H
  · simp [qqAnd, qqVerum] at H
  · simp [qqAnd, qqFalsum] at H
  · simp only [qqAnd_inj] at H; rcases H with ⟨rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqAnd, qqOr] at H
  · simp [qqAnd, qqAll] at H
  · simp [qqAnd, qqEx] at H

lemma graph_or {p₁ p₂ r₁ r₂ : V} (hp₁ : L.IsUFormula p₁) (hp₂ : L.IsUFormula p₂)
    (h₁ : c.Graph param p₁ r₁) (h₂ : c.Graph param p₂ r₂) :
    c.Graph param (p₁ ^⋎ p₂) (c.or param p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂],
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_or_inv {p₁ p₂ r : V} :
    c.Graph param (p₁ ^⋎ p₂) r → ∃ r₁ r₂, c.Graph param p₁ r₁ ∧ c.Graph param p₂ r₂ ∧ r =
        c.or param p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqOr, qqRel] at H
  · simp [qqOr, qqNRel] at H
  · simp [qqOr, qqVerum] at H
  · simp [qqOr, qqFalsum] at H
  · simp [qqOr, qqAnd] at H
  · simp only [qqOr_inj] at H; rcases H with ⟨rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqOr, qqAll] at H
  · simp [qqOr, qqEx] at H

lemma graph_all {p₁ r₁ : V} (hp₁ : L.IsUFormula p₁) (h₁ : c.Graph (c.allChanges param) p₁ r₁) :
    c.Graph param (^∀ p₁) (c.all param p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁],
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_all_inv {p₁ r : V} :
    c.Graph param (^∀ p₁) r → ∃ r₁, c.Graph (c.allChanges param) p₁ r₁ ∧ r = c.all param p₁ r₁ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqAll, qqRel] at H
  · simp [qqAll, qqNRel] at H
  · simp [qqAll, qqVerum] at H
  · simp [qqAll, qqFalsum] at H
  · simp [qqAll, qqAnd] at H
  · simp [qqAll, qqOr] at H
  · simp only [qqAll_inj] at H; rcases H with rfl
    exact ⟨_, by assumption, rfl⟩
  · simp [qqAll, qqEx] at H

lemma graph_ex {p₁ r₁ : V} (hp₁ : L.IsUFormula p₁) (h₁ : c.Graph (c.exChanges param) p₁ r₁) :
    c.Graph param (^∃ p₁) (c.ex param p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁],
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_ex_inv {p₁ r : V} :
    c.Graph param (^∃ p₁) r → ∃ r₁, c.Graph (c.exChanges param) p₁ r₁ ∧ r = c.ex param p₁ r₁ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩)⟩
  · simp [qqEx, qqRel] at H
  · simp [qqEx, qqNRel] at H
  · simp [qqEx, qqVerum] at H
  · simp [qqEx, qqFalsum] at H
  · simp [qqEx, qqAnd] at H
  · simp [qqEx, qqOr] at H
  · simp [qqEx, qqAll] at H
  · simp only [qqEx_inj] at H; rcases H with rfl
    exact ⟨_, by assumption, rfl⟩

variable (param)

lemma graph_exists {p : V} : L.IsUFormula p → ∃ y, c.Graph param p y := by
  haveI : Sg1-Function₁ c.allChanges := c.allChanges_defined.to_definable
  haveI : Sg1-Function₁ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V :=
    fun _ param ↦ Max.max param (Max.max (c.allChanges param) (c.exChanges param))
  have hf : Sg1-Function₂ f := by
    change Sg1-Function₂ (fun _ param ↦
      Max.max param (Max.max (c.allChanges param) (c.exChanges param)))
    definability
  apply order_ball_induction_sigma1 hf ?_ ?_ p param
  · definability
  intro p param ih hp
  rcases hp.case with
    (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ |
    rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ |
    ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  · exact ⟨c.rel param k r v, c.graph_rel hkr hv⟩
  · exact ⟨c.nrel param k r v, c.graph_nrel hkr hv⟩
  · exact ⟨c.verum param, c.graph_verum⟩
  · exact ⟨c.falsum param, c.graph_falsum⟩
  · rcases ih p₁ (by simp) param (by simp [f]) hp₁ with ⟨y₁, h₁⟩
    rcases ih p₂ (by simp) param (by simp [f]) hp₂ with ⟨y₂, h₂⟩
    exact ⟨c.and param p₁ p₂ y₁ y₂, c.graph_and hp₁ hp₂ h₁ h₂⟩
  · rcases ih p₁ (by simp) param (by simp [f]) hp₁ with ⟨y₁, h₁⟩
    rcases ih p₂ (by simp) param (by simp [f]) hp₂ with ⟨y₂, h₂⟩
    exact ⟨c.or param p₁ p₂ y₁ y₂, c.graph_or hp₁ hp₂ h₁ h₂⟩
  · rcases ih p₁ (by simp) (c.allChanges param) (by simp [f]) hp₁ with ⟨y₁, h₁⟩
    exact ⟨c.all param p₁ y₁, c.graph_all hp₁ h₁⟩
  · rcases ih p₁ (by simp) (c.exChanges param) (by simp [f]) hp₁ with ⟨y₁, h₁⟩
    exact ⟨c.ex param p₁ y₁, c.graph_ex hp₁ h₁⟩

lemma graph_unique {p : V} :
    L.IsUFormula p → ∀ {param r r'}, c.Graph param p r → c.Graph param p r' → r = r' := by
  apply Language.IsUFormula.induction_pi1 (P :=
    fun p ↦ ∀ {param r r'}, c.Graph param p r → c.Graph param p r' → r = r')
    (by definability)
  case hrel =>
    intro k R v hkR hv
    simp [c.graph_rel_iff hkR hv]
  case hnrel =>
    intro k R v hkR hv
    simp [c.graph_nrel_iff hkR hv]
  case hverum =>
    simp [c.graph_verum_iff]
  case hfalsum =>
    simp [c.graph_falsum_iff]
  case hand =>
    intro p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr'
    rcases c.graph_and_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_and_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hor =>
    intro p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr'
    rcases c.graph_or_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_or_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hall =>
    intro p _ ih param r r' hr hr'
    rcases c.graph_all_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_all_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl
  case hex =>
    intro p _ ih param r r' hr hr'
    rcases c.graph_ex_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_ex_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl

lemma exists_unique {p : V} (hp : L.IsUFormula p) : ∃! r, c.Graph param p r := by
  rcases c.graph_exists param hp with ⟨r, hr⟩
  exact ExistsUnique.intro r hr (fun r' hr' ↦ c.graph_unique hp hr' hr)

lemma exists_unique_all (p : V) :
    ∃! r, (L.IsUFormula p → c.Graph param p r) ∧ (¬L.IsUFormula p → r = 0) := by
  by_cases hp : L.IsUFormula p <;> simp [hp, exists_unique]

/-- Imported declaration from the Incompleteness formalization. -/
def result (p : V) : V := Classical.choose! (c.exists_unique_all param p)

lemma result_prop {p : V} (hp : L.IsUFormula p) : c.Graph param p (c.result param p) :=
  Classical.choose!_spec (c.exists_unique_all param p) |>.1 hp

lemma result_prop_not {p : V} (hp : ¬L.IsUFormula p) : c.result param p = 0 :=
  Classical.choose!_spec (c.exists_unique_all param p) |>.2 hp

variable {param}

lemma result_eq_of_graph {p r} (h : c.Graph param p r) : c.result param p = r := Eq.symm <|
  Classical.choose_uniq (c.exists_unique_all param p) (by simp [c.graph_dom_uformula h, h])

@[simp] lemma result_rel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    c.result param (^rel k R v) = c.rel param k R v :=
  c.result_eq_of_graph (c.graph_rel hR hv)

@[simp] lemma result_nrel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    c.result param (^nrel k R v) = c.nrel param k R v :=
  c.result_eq_of_graph (c.graph_nrel hR hv)

@[simp] lemma result_verum : c.result param ^⊤ = c.verum param := c.result_eq_of_graph c.graph_verum

@[simp] lemma result_falsum :
    c.result param ^⊥ = c.falsum param :=
  c.result_eq_of_graph c.graph_falsum

@[simp] lemma result_and {p q}
    (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    c.result param (p ^⋏ q) = c.and param p q (c.result param p) (c.result param q) :=
  c.result_eq_of_graph (c.graph_and hp hq (c.result_prop param hp) (c.result_prop param hq))

@[simp] lemma result_or {p q}
    (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    c.result param (p ^⋎ q) = c.or param p q (c.result param p) (c.result param q) :=
  c.result_eq_of_graph (c.graph_or hp hq (c.result_prop param hp) (c.result_prop param hq))

@[simp] lemma result_all {p} (hp : L.IsUFormula p) :
    c.result param (^∀ p) = c.all param p (c.result (c.allChanges param) p) :=
  c.result_eq_of_graph (c.graph_all hp (c.result_prop (c.allChanges param) hp))

@[simp] lemma result_ex {p} (hp : L.IsUFormula p) :
    c.result param (^∃ p) = c.ex param p (c.result (c.exChanges param) p) :=
  c.result_eq_of_graph (c.graph_ex hp (c.result_prop _ hp))

section «lp_section_4»

lemma result_defined : Sg1-Function₂ c.result via β.result := by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.reduceAdd,
    Blueprint.result, Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_sigma,
    HierarchySymbol.Semiformula.val_mkSigma, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Matrix.cons_val_fin_one,
    Semiterm.val_bvar, Matrix.constant_eq_singleton, L.isUFormula_defined.proper.iff',
    L.isUFormula_defined.df.iff, Matrix.vecCons_zero, Matrix.comp_vecCons', c.eval_graphDef,
    Matrix.cons_val_one, Matrix.cons_app_two, LogicalConnective.Prop.arrow_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
    Semiformula.eval_operator₂, Semiterm.val_const, Structure.numeral_eq_numeral,
    ORingStruc.zero_eq_zero, Structure.Eq.eq, LogicalConnective.Prop.and_eq]
  exact Classical.choose!_eq_iff (c.exists_unique_all (v 1) (v 2))

instance result_definable : Sg-[0 + 1]-Function₂ c.result := c.result_defined.to_definable

end «lp_section_4»

lemma uformula_result_induction {P : V → V → V → Prop} (hP : Sg1-Relation₃ P)
    (hRel : ∀ param k R v, L.Rel k R → L.IsUTermVec k v → P param (^rel k R v) (c.rel param k R v))
    (hNRel : ∀ param k R v, L.Rel k R → L.IsUTermVec k v →
      P param (^nrel k R v) (c.nrel param k R v))
    (hverum : ∀ param, P param ^⊤ (c.verum param))
    (hfalsum : ∀ param, P param ^⊥ (c.falsum param))
    (hand : ∀ param p q, L.IsUFormula p → L.IsUFormula q →
      P param p (c.result param p) → P param q (c.result param q) →
        P param (p ^⋏ q) (c.and param p q (c.result param p) (c.result param q)))
    (hor : ∀ param p q, L.IsUFormula p → L.IsUFormula q →
      P param p (c.result param p) → P param q (c.result param q) →
        P param (p ^⋎ q) (c.or param p q (c.result param p) (c.result param q)))
    (hall : ∀ param p, L.IsUFormula p →
      P (c.allChanges param) p (c.result (c.allChanges param) p) →
      P param (^∀ p) (c.all param p (c.result (c.allChanges param) p)))
    (hex : ∀ param p, L.IsUFormula p →
      P (c.exChanges param) p (c.result (c.exChanges param) p) →
      P param (^∃ p) (c.ex param p (c.result (c.exChanges param) p))) :
    ∀ {param p : V}, L.IsUFormula p → P param p (c.result param p) := by
  haveI : Sg1-Function₂ c.result := c.result_definable
  haveI : Sg1-Function₁ c.allChanges := c.allChanges_defined.to_definable
  haveI : Sg1-Function₁ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V :=
    fun _ param ↦ Max.max param (Max.max (c.allChanges param) (c.exChanges param))
  have hf : Sg1-Function₂ f := by
    change Sg1-Function₂ (fun _ param ↦
      Max.max param (Max.max (c.allChanges param) (c.exChanges param)))
    definability
  intro param p
  apply order_ball_induction_sigma1 hf ?_ ?_ p param
  · apply HierarchySymbol.Boldface.imp
      (HierarchySymbol.Boldface.comp₁ (HierarchySymbol.BoldfaceFunction.var _))
      (HierarchySymbol.Boldface.comp₃
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.comp₂ (HierarchySymbol.BoldfaceFunction.var _)
          (HierarchySymbol.BoldfaceFunction.var _)))
  intro p param ih hp
  rcases hp.case with
    (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, hp₁, hp₂,
      rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  · simpa [hkr, hv] using hRel param k r v hkr hv
  · simpa [hkr, hv] using hNRel param k r v hkr hv
  · simpa using hverum param
  · simpa using hfalsum param
  · simpa [c.result_and hp₁ hp₂] using
      hand param p₁ p₂ hp₁ hp₂ (ih p₁ (by simp) param (by simp [f]) hp₁) (ih p₂ (by simp) param (by
        simp [f]) hp₂)
  · simpa [c.result_or hp₁ hp₂] using
      hor param p₁ p₂ hp₁ hp₂ (ih p₁ (by simp) param (by simp [f]) hp₁) (ih p₂ (by simp) param (by
        simp [f]) hp₂)
  · simpa [c.result_all hp₁] using
      hall param p₁ hp₁ (ih p₁ (by simp) (c.allChanges param) (by simp [f]) hp₁)
  · simpa [c.result_ex hp₁] using
      hex param p₁ hp₁ (ih p₁ (by simp) (c.exChanges param) (by simp [f]) hp₁)

/-
lemma semiformula_result_induction {P : V → V → V → V → Prop} (hP : Sg1-Relation₄ P)
    (hRel : ∀ param k R v, L.Rel k R → L.SemitermVec k n v →
      P param (^rel n k R v) (c.rel param k R v))
    (hNRel : ∀ param k R v, L.Rel k R → L.SemitermVec k n v →
      P param (^nrel n k R v) (c.nrel param k R v))
    (hverum : ∀ param, P param (^⊤[n]) (c.verum param))
    (hfalsum : ∀ param, P param (^⊥[n]) (c.falsum param))
    (hand : ∀ param p q, L.Semiformula n p → L.Semiformula n q →
      P param p (c.result param p) → P param q (c.result param q) →
        P param (p ^⋏ q) (c.and param p q (c.result param p) (c.result param q)))
    (hor : ∀ param p q, L.Semiformula n p → L.Semiformula n q →
      P param p (c.result param p) → P param q (c.result param q) →
        P param (p ^⋎ q) (c.or param p q (c.result param p) (c.result param q)))
    (hall : ∀ param p, L.Semiformula (n + 1) p →
      P (c.allChanges param) (n + 1) p (c.result (c.allChanges param) p) →
      P param (^∀ p) (c.all param p (c.result (c.allChanges param) p)))
    (hex : ∀ param p, L.Semiformula (n + 1) p →
      P (c.exChanges param) (n + 1) p (c.result (c.exChanges param) p) →
      P param (^∃ p) (c.ex param p (c.result (c.exChanges param) p))) :
    ∀ {param p : V}, L.Semiformula n p → P param p (c.result param p) := by
  suffices ∀ {param p : V}, L.IsUFormula p → ∀ n ≤ p, n = fstIdx p → P param p (c.result param p)
  by intro param p hp; exact @this param p hp.1 n (by simp [hp.2]) hp.2
  intro param p hp
  apply c.uformula_result_induction (P := fun param p y ↦ ∀ n ≤ p, n = fstIdx p → P param p y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · apply HierarchySymbol.Boldface.ball_le (HierarchySymbol.BoldfaceFunction.var _)
    simp_all only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two,
      Fin.succ_zero_eq_one]
    apply LO.FirstOrder.Arith.HierarchySymbol.Boldface.imp
    · simp_all only [SigmaPiDelta.alt_sigma, Fin.isValue]
      apply LO.FirstOrder.Arith.HierarchySymbol.Boldface.comp₂
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue]
        apply LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction.comp₁
        simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
    · apply LO.FirstOrder.Arith.HierarchySymbol.Boldface.comp₄
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue]
        apply LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction.comp₁
        simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
  · rintro param k R v hkR hv _ _ rfl; simpa using hRel param k R v hkR hv
  · rintro param k R v hkR hv _ _ rfl; simpa using hNRel param k R v hkR hv
  · rintro param _ _ rfl; simpa using hverum param
  · rintro param _ _ rfl; simpa using hfalsum param
  · rintro param p q hp hq ihp ihq _ _ rfl
    have ihp : P param p (c.result param p) := ihp n (by simp [hp.2]) hp.2
    have ihq : P param q (c.result param q) := ihq n (by simp [hq.2]) hq.2
    simpa using hand param p q hp hq ihp ihq
  · rintro param p q hp hq ihp ihq _ _ rfl
    have ihp : P param p (c.result param p) := ihp n (by simp [hp.2]) hp.2
    have ihq : P param q (c.result param q) := ihq n (by simp [hq.2]) hq.2
    simpa using hor param p q hp hq ihp ihq
  · rintro param p hp ihp _ _ rfl
    have ihp : P (c.allChanges param) (n + 1) p (c.result (c.allChanges param) p) :=
      ihp (n + 1) (by simp [hp.2]) hp.2
    simpa using hall param p hp ihp
  · rintro param p hp ihp _ _ rfl
    have ihp : P (c.exChanges param) (n + 1) p (c.result (c.exChanges param) p) :=
      ihp (n + 1) (by simp [hp.2]) hp.2
    simpa using hex param p hp ihp
-/

end Construction

end UformulaRec1
end Language

section «lp_section_5»

namespace BV

/-- Imported declaration from the Incompleteness formalization. -/
def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel := .mkSigma “y param k R v. ∃ M, !pL.termBVVecDef M k v ∧ !listMaxDef y M” (by simp)
  nrel := .mkSigma “y param k R v. ∃ M, !pL.termBVVecDef M k v ∧ !listMaxDef y M” (by simp)
  verum := .mkSigma “y param. y = 0” (by simp)
  falsum := .mkSigma “y param. y = 0” (by simp)
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !Arith.max y y₁ y₂” (by simp)
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !Arith.max y y₁ y₂” (by simp)
  all := .mkSigma “y param p₁ y₁. !subDef y y₁ 1” (by simp)
  ex := .mkSigma “y param p₁ y₁. !subDef y y₁ 1” (by simp)
  allChanges := .mkSigma “param' param. param' = 0” (by simp)
  exChanges := .mkSigma “param' param. param' = 0” (by simp)

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
def construction : Language.UformulaRec1.Construction V L (blueprint pL) where
  rel {_} := fun k _ v ↦ listMax (L.termBVVec k v)
  nrel {_} := fun k _ v ↦ listMax (L.termBVVec k v)
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  or {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  all {_} := fun _ y₁ ↦ y₁ - 1
  ex {_} := fun _ y₁ ↦ y₁ - 1
  allChanges := fun _ ↦ 0
  exChanges := fun _ ↦ 0
  rel_defined := by intro v; simp [blueprint, L.termBVVec_defined.df.iff]
  nrel_defined := by intro v; simp [blueprint, L.termBVVec_defined.df.iff]
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]
  or_defined := by intro v; simp [blueprint]
  all_defined := by intro v; simp [blueprint]
  ex_defined := by intro v; simp [blueprint]
  allChanges_defined := by intro v; simp [blueprint]
  exChanges_defined := by intro v; simp [blueprint]

end BV

open BV

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.bv (p : V) : V := (construction L).result 0 p

variable {L}

section «lp_section_6»

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.LDef.bvDef (pL : LDef) :
    Sg1.Semisentence 2 :=
  (blueprint pL).result.rew (Rew.substs ![#0, ‘0’, #1])

variable (L)

lemma _root_.LO.Arith.Language.bv_defined : Sg1-Function₁ L.bv via pL.bvDef := fun v ↦ by
  unfold Language.bv
  simpa [LDef.bvDef, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
    (construction L).result_defined ![v 0, 0, v 1]

instance _root_.LO.Arith.Language.bv_definable : Sg1-Function₁ L.bv := L.bv_defined.to_definable

instance _root_.LO.Arith.Language.bv_definable' (Γ) :
    Γ-[m + 1]-Function₁ L.bv :=
  L.bv_definable.of_sigmaOne

end «lp_section_6»

@[simp] lemma bv_rel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.bv (^rel k R v) = listMax (L.termBVVec k v) := by simp [Language.bv, hR, hv, construction]

@[simp] lemma bv_nrel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.bv (^nrel k R v) = listMax (L.termBVVec k v) := by simp [Language.bv, hR, hv, construction]

@[simp] lemma bv_verum : L.bv ^⊤ = 0 := by simp [Language.bv, construction]

@[simp] lemma bv_falsum : L.bv ^⊥ = 0 := by simp [Language.bv, construction]

@[simp] lemma bv_and {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.bv (p ^⋏ q) = Max.max (L.bv p) (L.bv q) := by simp [Language.bv, hp, hq, construction]

@[simp] lemma bv_or {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.bv (p ^⋎ q) = Max.max (L.bv p) (L.bv q) := by simp [Language.bv, hp, hq, construction]

@[simp] lemma bv_all {p} (hp : L.IsUFormula p) :
    L.bv (^∀ p) = L.bv p - 1 := by
  simp [Language.bv, hp, construction]

@[simp] lemma bv_ex {p} (hp : L.IsUFormula p) :
    L.bv (^∃ p) = L.bv p - 1 := by
  simp [Language.bv, hp, construction]

lemma bv_eq_of_not_isUFormula {p} (h : ¬L.IsUFormula p) :
    L.bv p = 0 :=
  (construction L).result_prop_not _ h

end «lp_section_5»

section «lp_section_7»

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Arith.Language.IsSemiformula (n p : V) : Prop where
  isUFormula : L.IsUFormula p
  bv : L.bv p ≤ n

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Language.IsFormula (p : V) : Prop := L.IsSemiformula 0 p

variable {L}

lemma _root_.LO.Arith.Language.isSemiformula_iff {n p : V} :
    L.IsSemiformula n p ↔ L.IsUFormula p ∧ L.bv p ≤ n :=
  ⟨fun h ↦ ⟨h.isUFormula, h.bv⟩, by rintro ⟨hp, h⟩; exact ⟨hp, h⟩⟩

section «lp_section_8»

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.LDef.isSemiformulaDef (pL : LDef) : Dlt1.Semisentence 2 := .mkDelta
  (.mkSigma “n p. !pL.isUFormulaDef.sigma p ∧ ∃ b, !pL.bvDef b p ∧ b ≤ n” (by simp))
  (.mkPi “n p. !pL.isUFormulaDef.pi p ∧ ∀ b, !pL.bvDef b p → b ≤ n” (by simp))

lemma _root_.LO.Arith.Language.isSemiformula_defined :
    Dlt1-Relation L.IsSemiformula via pL.isSemiformulaDef := by
  constructor
  · intro v; simp [FirstOrder.Arith.LDef.isSemiformulaDef, HierarchySymbol.Semiformula.val_sigma,
      L.bv_defined.df.iff, L.isUFormula_defined.proper.iff']
  · intro v; simp [FirstOrder.Arith.LDef.isSemiformulaDef, HierarchySymbol.Semiformula.val_sigma,
      L.bv_defined.df.iff, L.isUFormula_defined.df.iff, Language.isSemiformula_iff]

instance _root_.LO.Arith.Language.isSemiformula_definable :
    Dlt1-Relation L.IsSemiformula :=
  L.isSemiformula_defined.to_definable

instance _root_.LO.Arith.Language.isSemiformulaDef_definable' :
    Γ-[m + 1]-Relation L.IsSemiformula :=
  L.isSemiformula_definable.of_deltaOne

end «lp_section_8»

@[simp] lemma _root_.LO.Arith.Language.IsUFormula.isSemiformula {p : V} (h : L.IsUFormula p) :
    L.IsSemiformula (L.bv p) p where
  isUFormula := h
  bv := by rfl

@[simp] lemma _root_.LO.Arith.Language.IsSemiformula.rel {n k r v : V} :
    L.IsSemiformula n (^rel k r v) ↔ L.Rel k r ∧ L.IsSemitermVec k n v := by
  constructor
  · intro h
    have hrv : L.Rel k r ∧ L.IsUTermVec k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun i hi ↦ by
      have : listMax (L.termBVVec k v) ≤ n := by simpa [hrv] using h.bv
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_rel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [Language.nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma _root_.LO.Arith.Language.IsSemiformula.nrel {n k r v : V} :
    L.IsSemiformula n (^nrel k r v) ↔ L.Rel k r ∧ L.IsSemitermVec k n v := by
  constructor
  · intro h
    have hrv : L.Rel k r ∧ L.IsUTermVec k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun i hi ↦ by
      have : listMax (L.termBVVec k v) ≤ n := by simpa [hrv] using h.bv
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_nrel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [Language.nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma _root_.LO.Arith.Language.IsSemiformula.verum {n} :
    L.IsSemiformula n ^⊤ :=
  ⟨by simp, by simp⟩

@[simp] lemma _root_.LO.Arith.Language.IsSemiformula.falsum {n} :
    L.IsSemiformula n ^⊥ :=
  ⟨by simp, by simp⟩

@[simp] lemma _root_.LO.Arith.Language.IsSemiformula.and {n p q : V} :
    L.IsSemiformula n (p ^⋏ q) ↔ L.IsSemiformula n p ∧ L.IsSemiformula n q := by
  constructor
  · intro h
    have hpq : L.IsUFormula p ∧ L.IsUFormula q := by simpa using h.isUFormula
    have hbv : L.bv p ≤ n ∧ L.bv q ≤ n := by simpa [hpq] using h.bv
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv,
      hq.bv]⟩

@[simp] lemma _root_.LO.Arith.Language.IsSemiformula.or {n p q : V} :
    L.IsSemiformula n (p ^⋎ q) ↔ L.IsSemiformula n p ∧ L.IsSemiformula n q := by
  constructor
  · intro h
    have hpq : L.IsUFormula p ∧ L.IsUFormula q := by simpa using h.isUFormula
    have hbv : L.bv p ≤ n ∧ L.bv q ≤ n := by simpa [hpq] using h.bv
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv,
      hq.bv]⟩

@[simp] lemma _root_.LO.Arith.Language.IsSemiformula.all {n p : V} :
    L.IsSemiformula n (^∀ p) ↔ L.IsSemiformula (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show L.IsUFormula p by simpa using h.isUFormula] using h.bv⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv]⟩

@[simp] lemma _root_.LO.Arith.Language.IsSemiformula.ex {n p : V} :
    L.IsSemiformula n (^∃ p) ↔ L.IsSemiformula (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show L.IsUFormula p by simpa using h.isUFormula] using h.bv⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv]⟩

lemma _root_.LO.Arith.Language.IsSemiformula.case_iff {n p : V} :
    L.IsSemiformula n p ↔
    (∃ k R v, L.Rel k R ∧ L.IsSemitermVec k n v ∧ p = ^rel k R v) ∨
    (∃ k R v, L.Rel k R ∧ L.IsSemitermVec k n v ∧ p = ^nrel k R v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ p₂, L.IsSemiformula n p₁ ∧ L.IsSemiformula n p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, L.IsSemiformula n p₁ ∧ L.IsSemiformula n p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁, L.IsSemiformula (n + 1) p₁ ∧ p = ^∀ p₁) ∨
    (∃ p₁, L.IsSemiformula (n + 1) p₁ ∧ p = ^∃ p₁) := by
  constructor
  · intro h
    rcases h.isUFormula.case with
      (⟨k, r, v, _, _, rfl⟩ | ⟨k, r, v, _, _, rfl⟩ | rfl | rfl | ⟨p₁, p₂, _, _, rfl⟩ | ⟨p₁, p₂,
        _, _, rfl⟩ | ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩)
    · have : L.Rel k r ∧ L.IsSemitermVec k n v := by simpa using h
      exact Or.inl ⟨k, r, v, by simp [this]⟩
    · have : L.Rel k r ∧ L.IsSemitermVec k n v := by simpa using h
      exact Or.inr <| Or.inl ⟨k, r, v, by simp [this]⟩
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · have : L.IsSemiformula n p₁ ∧ L.IsSemiformula n p₂ := by simpa using h
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, by simp [this]⟩
    · have : L.IsSemiformula n p₁ ∧ L.IsSemiformula n p₂ := by simpa using h
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, by simp [this]⟩
    · have : L.IsSemiformula (n + 1) p₁ := by simpa using h
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, by simp [this]⟩
    · have : L.IsSemiformula (n + 1) p₁ := by simpa using h
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨p₁, by simp [this]⟩
  · rintro (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂,
    rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩) <;> simp [*]

lemma _root_.LO.Arith.Language.IsSemiformula.case {P : V → V → Prop} {n p} (hp :
    L.IsSemiformula n p)
    (hrel : ∀ n k r v, L.Rel k r → L.IsSemitermVec k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.IsSemitermVec k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.IsSemiformula (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.IsSemiformula (n + 1) p → P n (^∃ p)) : P n p := by
  rcases Language.IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁,
      p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ _ hR hv
  · exact hnrel _ _ _ _ hR hv
  · exact hverum n
  · exact hfalsum n
  · exact hand _ _ _ h₁ h₂
  · exact hor _ _ _ h₁ h₂
  · exact hall _ _ h₁
  · exact hex _ _ h₁

lemma _root_.LO.Arith.Language.IsSemiformula.induction_sigma1 {P : V → V → Prop} (hP :
    Sg1-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.IsSemitermVec k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.IsSemitermVec k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.IsSemiformula (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.IsSemiformula (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    L.IsSemiformula n p → P n p := by
  have : Sg1-Function₂ (fun _ (n : V) ↦ n + 1) := by definability
  apply order_ball_induction_sigma1 this ?_ ?_ p n
  · apply HierarchySymbol.Boldface.imp
    · apply HierarchySymbol.Boldface.comp₂
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
    · apply HierarchySymbol.Boldface.comp₂
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
  intro p n ih hp
  rcases Language.IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁,
      p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · apply hrel _ _ _ _ hR hv
  · apply hnrel _ _ _ _ hR hv
  · apply hverum
  · apply hfalsum
  · apply hand _ _ _ h₁ h₂ (ih p₁ (by simp) n (by simp) h₁) (ih p₂ (by simp) n (by simp) h₂)
  · apply hor _ _ _ h₁ h₂ (ih p₁ (by simp) n (by simp) h₁) (ih p₂ (by simp) n (by simp) h₂)
  · apply hall _ _ h₁ (ih p₁ (by simp) (n + 1) (by simp) h₁)
  · apply hex _ _ h₁ (ih p₁ (by simp) (n + 1) (by simp) h₁)

lemma _root_.LO.Arith.Language.IsSemiformula.induction_pi1 {P : V → V → Prop} (hP : Pg1-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.IsSemitermVec k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.IsSemitermVec k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.IsSemiformula (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.IsSemiformula (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    L.IsSemiformula n p → P n p := by
  suffices L.IsUFormula p → ∀ n, L.IsSemiformula n p → P n p by intro h; exact this h.isUFormula n h
  apply Language.IsUFormula.induction_pi1 (P := fun p ↦ ∀ n, L.IsSemiformula n p → P n p)
  · definability
  · intro k R v hR _ n h
    have : L.Rel k R ∧ L.IsSemitermVec k n v := by simpa using h
    exact hrel _ _ _ _ hR this.2
  · intro k R v hR _ n h
    have : L.Rel k R ∧ L.IsSemitermVec k n v := by simpa using h
    exact hnrel _ _ _ _ hR this.2
  · intro n _; apply hverum
  · intro n _; apply hfalsum
  · intro p q _ _ ihp ihq n h
    have : L.IsSemiformula n p ∧ L.IsSemiformula n q := by simpa using h
    apply hand _ _ _ this.1 this.2 (ihp n this.1) (ihq n this.2)
  · intro p q _ _ ihp ihq n h
    have : L.IsSemiformula n p ∧ L.IsSemiformula n q := by simpa using h
    apply hor _ _ _ this.1 this.2 (ihp n this.1) (ihq n this.2)
  · intro p _ ihp n h
    have : L.IsSemiformula (n + 1) p := by simpa using h
    apply hall _ _ this (ihp _ this)
  · intro p _ ihp n h
    have : L.IsSemiformula (n + 1) p := by simpa using h
    apply hex _ _ this (ihp _ this)

lemma _root_.LO.Arith.Language.IsSemiformula.induction1 (Γ) {P : V → V → Prop} (hP :
    Γ-[1]-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.IsSemitermVec k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.IsSemitermVec k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.IsSemiformula n p → L.IsSemiformula n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.IsSemiformula (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.IsSemiformula (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    L.IsSemiformula n p → P n p :=
  match Γ with
  | Sg => Language.IsSemiformula.induction_sigma1 hP hrel hnrel hverum hfalsum hand hor hall hex
  | Pg => Language.IsSemiformula.induction_pi1 hP hrel hnrel hverum hfalsum hand hor hall hex
  | Dlt =>
    Language.IsSemiformula.induction_sigma1 hP.of_delta hrel hnrel hverum hfalsum hand hor hall hex


lemma _root_.LO.Arith.Language.IsSemiformula.pos {n p : V} (h : L.IsSemiformula n p) :
    0 < p :=
  h.isUFormula.pos

@[simp] lemma _root_.LO.Arith.Language.IsSemiformula.not_zero (m : V) : ¬L.IsSemiformula m (0 :
    V) := by
  intro h; simpa using h.pos

end «lp_section_7»

namespace Language
namespace UformulaRec1
namespace Construction

variable {β : Blueprint pL} {c : Construction V L β} {param : V}

lemma semiformula_result_induction {P : V → V → V → V → Prop} (hP : Sg1-Relation₄ P)
    (hRel : ∀ n param k R v, L.Rel k R → L.IsSemitermVec k n v →
      P param n (^rel k R v) (c.rel param k R v))
    (hNRel : ∀ n param k R v, L.Rel k R → L.IsSemitermVec k n v →
      P param n (^nrel k R v) (c.nrel param k R v))
    (hverum : ∀ n param, P param n ^⊤ (c.verum param))
    (hfalsum : ∀ n param, P param n ^⊥ (c.falsum param))
    (hand : ∀ n param p q, L.IsSemiformula n p → L.IsSemiformula n q →
      P param n p (c.result param p) → P param n q (c.result param q) →
        P param n (p ^⋏ q) (c.and param p q (c.result param p) (c.result param q)))
    (hor : ∀ n param p q, L.IsSemiformula n p → L.IsSemiformula n q →
      P param n p (c.result param p) → P param n q (c.result param q) →
        P param n (p ^⋎ q) (c.or param p q (c.result param p) (c.result param q)))
    (hall : ∀ n param p, L.IsSemiformula (n + 1) p →
      P (c.allChanges param) (n + 1) p (c.result (c.allChanges param) p) →
      P param n (^∀ p) (c.all param p (c.result (c.allChanges param) p)))
    (hex : ∀ n param p, L.IsSemiformula (n + 1) p →
      P (c.exChanges param) (n + 1) p (c.result (c.exChanges param) p) →
      P param n (^∃ p) (c.ex param p (c.result (c.exChanges param) p))) :
    ∀ {param n p : V}, L.IsSemiformula n p → P param n p (c.result param p) := by
  haveI : Sg1-Function₂ c.result := c.result_definable
  haveI : Sg1-Function₁ c.allChanges := c.allChanges_defined.to_definable
  haveI : Sg1-Function₁ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V → V :=
    fun _ param _ ↦ Max.max param (Max.max (c.allChanges param) (c.exChanges param))
  have hf : Sg1-Function₃ f := by
    change Sg1-Function₃ (fun _ param _ ↦ Max.max param
      (Max.max (c.allChanges param) (c.exChanges param)))
    definability
  let g : V → V → V → V := fun _ _ n ↦ n + 1
  have hg : Sg1-Function₃ g := by
    change Sg1-Function₃ (fun _ _ n ↦ n + 1)
    definability
  intro param n p
  apply order_ball_induction₂_sigma1 hf hg ?_ ?_ p param n
  · apply HierarchySymbol.Boldface.imp
    · apply HierarchySymbol.Boldface.comp₂
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
    · apply HierarchySymbol.Boldface.comp₄
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
      apply HierarchySymbol.BoldfaceFunction.comp₂ (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
  intro p param n ih hp
  rcases Language.IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁,
      p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · simpa [hR, hv.isUTerm] using hRel n param k R v hR hv
  · simpa [hR, hv.isUTerm] using hNRel n param k R v hR hv
  · simpa using hverum n param
  · simpa using hfalsum n param
  · simpa [h₁.isUFormula, h₂.isUFormula] using
      hand n param p₁ p₂ h₁ h₂
        (ih p₁ (by simp) param (by simp [f]) n (by simp [g]) h₁)
        (ih p₂ (by simp) param (by simp [f]) n (by simp [g]) h₂)
  · simpa [h₁.isUFormula, h₂.isUFormula] using
      hor n param p₁ p₂ h₁ h₂
        (ih p₁ (by simp) param (by simp [f]) n (by simp [g]) h₁)
        (ih p₂ (by simp) param (by simp [f]) n (by simp [g]) h₂)
  · simpa [h₁.isUFormula] using
      hall n param p₁ h₁
        (ih p₁ (by simp) (c.allChanges param) (by simp [f]) (n + 1) (by simp [g]) h₁)
  · simpa [h₁.isUFormula] using
      hex n param p₁ h₁
        (ih p₁ (by simp) (c.exChanges param) (by simp [f]) (n + 1) (by simp [g]) h₁)

end Construction
end UformulaRec1
end Language

end Arith
end LO

end «lp_nc_section_1»
