/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Semantics.Semantics
import LeanPool.Incompleteness.Foundation.Vorspiel.NotationClass

/-! # Operator -/


namespace LO

namespace FirstOrder

variable {L : Language}

namespace Semiterm

/-- Imported declaration from the Incompleteness formalization. -/
structure Operator (L : Language) (n : ℕ) where
  /-- Imported declaration from the Incompleteness formalization. -/
  term : Semiterm L Empty n

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Const (L : Language.{u}) := Operator L 0

/-- Imported declaration from the Incompleteness formalization. -/
def fn {k} (f : L.Func k) : Operator L k := ⟨Semiterm.func f (#·)⟩

namespace Operator

/-- Imported declaration from the Incompleteness formalization. -/
def equiv : Operator L n ≃ Semiterm L Empty n where
  toFun := Operator.term
  invFun := Operator.mk
  left_inv := by intro _; simp
  right_inv := by intro _; simp

/-- Imported declaration from the Incompleteness formalization. -/
def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L ξ n) : Semiterm L ξ n :=
  Rew.substs v (Rew.emb o.term)

/-- Imported declaration from the Incompleteness formalization. -/
@[coe] abbrev const (c : Const L) : Semiterm L ξ n := c.operator ![]

instance : Coe (Const L) (Semiterm L ξ n) := ⟨Operator.const⟩

/-- Imported declaration from the Incompleteness formalization. -/
def comp (o : Operator L k) (w : Fin k → Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

@[simp] lemma operator_comp (o : Operator L k) (w : Fin k → Operator L l) (v :
    Fin l → Semiterm L ξ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    simp only [operator, comp, Rew.emb_eq_id, Rew.id_app, ←Rew.comp_app]
    congr 1
    ext <;> simp only [Rew.comp_app, Rew.substs_bvar, Rew.emb_bvar, Rew.substs_fvar]; contradiction

/-- Imported declaration from the Incompleteness formalization. -/
def bvar (x : Fin n) : Operator L n := ⟨#x⟩

lemma operator_bvar (x : Fin k) (v : Fin k → Semiterm L ξ n) : (bvar x).operator v = v x := by
  simp [operator, bvar]

lemma bv_operator {k} (o : Operator L k) (v : Fin k → Semiterm L ξ (n + 1)) :
    (o.operator v).bv = .biUnion o.term.bv fun i ↦ (v i).bv  := by
  simp only [operator]
  generalize o.term = s
  induction s
  · simp only [Rew.emb_bvar, Rew.substs_bvar, bv_bvar, Finset.singleton_biUnion]
  · contradiction
  · simp only [Rew.func, bv_func, Finset.biUnion_biUnion, *]

lemma positive_operator_iff {k} {o : Operator L k} {v : Fin k → Semiterm L ξ (n + 1)} :
    (o.operator v).Positive ↔ ∀ i ∈ o.term.bv, (v i).Positive := by
  simp only [Positive, bv_operator, Finset.mem_biUnion, forall_exists_index, and_imp]
  exact ⟨fun h i hi x hx ↦ h x i hi hx, fun h x i hi hx ↦ h i hi x hx⟩

@[simp] lemma positive_const (c : Const L) : (c :
    Semiterm L ξ (n + 1)).Positive := by
  simp [const, positive_operator_iff]

-- f.operator ![ ... f.operator ![f.operator ![z, t 0], t 1], ... ,t (n-1)]
/-- Imported declaration from the Incompleteness formalization. -/
def foldr (f : Operator L 2) (z : Operator L k) : List (Operator L k) → Operator L k
  | []      => z
  | o :: os => f.comp ![foldr f z os, o]

@[simp] lemma foldr_nil (f : Operator L 2) (z : Operator L k) : f.foldr z [] = z := rfl

@[simp] lemma operator_foldr_cons (f : Operator L 2) (z : Operator L k) (o : Operator L k) (os :
    List (Operator L k))
  (v : Fin k → Semiterm L ξ n) :
    (f.foldr z (o :: os)).operator v = f.operator ![(f.foldr z os).operator v, o.operator v] := by
  simp [foldr, operator_comp, Matrix.fun_eq_vec₂]

/-- Imported declaration from the Incompleteness formalization. -/
def iterr (f : Operator L 2) (z : Const L) : (n : ℕ) → Operator L n
  | 0     => z
  | _ + 1 => f.foldr (bvar 0) (List.ofFn fun x => bvar x.succ)

@[simp] lemma iterr_zero (f : Operator L 2) (z : Const L) : f.iterr z 0 = z := rfl

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
protected class Zero (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  zero : Semiterm.Const L

/-- Imported declaration from the Incompleteness formalization. -/
protected class One (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  one : Semiterm.Const L

/-- Imported declaration from the Incompleteness formalization. -/
protected class Add (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  add : Semiterm.Operator L 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class Mul (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  mul : Semiterm.Operator L 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class Exp (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  exp : Semiterm.Operator L 1

/-- Imported declaration from the Incompleteness formalization. -/
protected class Sub (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  sub : Semiterm.Operator L 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class Div (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  div : Semiterm.Operator L 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class Star (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  star : Semiterm.Const L

/-- Imported declaration from the Incompleteness formalization. -/
class GoedelNumber (L : Language) (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  goedelNumber : α → Semiterm.Const L

/-- Imported declaration from the Incompleteness formalization. -/
notation "op(0)" => Zero.zero

/-- Imported declaration from the Incompleteness formalization. -/
notation "op(1)" => One.one

/-- Imported declaration from the Incompleteness formalization. -/
notation "op(+)" => Add.add

/-- Imported declaration from the Incompleteness formalization. -/
notation "op(*)" => Mul.mul

instance [L.Zero] : Operator.Zero L := ⟨⟨Semiterm.func Language.Zero.zero ![]⟩⟩

instance [L.One] : Operator.One L := ⟨⟨Semiterm.func Language.One.one ![]⟩⟩

instance [L.Add] : Operator.Add L := ⟨⟨Semiterm.func Language.Add.add Semiterm.bvar⟩⟩

instance [L.Mul] : Operator.Mul L := ⟨⟨Semiterm.func Language.Mul.mul Semiterm.bvar⟩⟩

instance [L.Exp] : Operator.Exp L := ⟨⟨Semiterm.func Language.Exp.exp Semiterm.bvar⟩⟩

instance [L.Star] : Operator.Star L := ⟨⟨Semiterm.func Language.Star.star ![]⟩⟩

lemma _root_.LO.FirstOrder.Semiterm.Operator.Zero.term_eq [L.Zero] :
    (@Zero.zero L _).term = Semiterm.func Language.Zero.zero ![] :=
  rfl

lemma _root_.LO.FirstOrder.Semiterm.Operator.One.term_eq [L.One] :
    (@One.one L _).term = Semiterm.func Language.One.one ![] :=
  rfl

lemma _root_.LO.FirstOrder.Semiterm.Operator.Add.term_eq [L.Add] :
    (@Add.add L _).term = Semiterm.func Language.Add.add Semiterm.bvar :=
  rfl

lemma _root_.LO.FirstOrder.Semiterm.Operator.Mul.term_eq [L.Mul] :
    (@Mul.mul L _).term = Semiterm.func Language.Mul.mul Semiterm.bvar :=
  rfl

lemma _root_.LO.FirstOrder.Semiterm.Operator.Exp.term_eq [L.Exp] :
    (@Exp.exp L _).term = Semiterm.func Language.Exp.exp Semiterm.bvar :=
  rfl

lemma _root_.LO.FirstOrder.Semiterm.Operator.Star.term_eq [L.Star] :
    (@Star.star L _).term = Semiterm.func Language.Star.star ![] :=
  rfl

open Language Semiterm

/-- Imported declaration from the Incompleteness formalization. -/
def numeral (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L] : ℕ → Const L
  | 0     => Zero.zero
  | n + 1 => Add.add.foldr One.one (List.replicate n One.one)

variable [hz : Operator.Zero L] [ho : Operator.One L] [ha : Operator.Add L]

lemma numeral_zero : numeral L 0 = Zero.zero := by rfl

lemma numeral_one : numeral L 1 = One.one := by rfl

lemma numeral_succ (hz : z ≠ 0) :
    numeral L (z + 1) = Operator.Add.add.comp ![numeral L z, One.one] := by
  cases z with
  | zero => exact False.elim (hz rfl)
  | succ z => rfl

lemma numeral_add_two : numeral L (z + 2) = Operator.Add.add.comp ![numeral L (z + 1), One.one] :=
  numeral_succ (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev encode (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L]
    {α : Type*} [Encodable α] (a : α) : Semiterm.Const L :=
  Semiterm.Operator.numeral L (Encodable.encode a)

end «lp_section_1»

@[simp] lemma _root_.LO.FirstOrder.Semiterm.Operator.Add.positive_iff [L.Add] (t u :
    Semiterm L ξ (n + 1)) :
    (Operator.Add.add.operator ![t, u]).Positive ↔ t.Positive ∧ u.Positive := by
  simp [positive_operator_iff, Add.term_eq, bv_func]

@[simp] lemma _root_.LO.FirstOrder.Semiterm.Operator.Mul.positive_iff [L.Mul] (t u :
    Semiterm L ξ (n + 1)) :
    (Operator.Mul.mul.operator ![t, u]).Positive ↔ t.Positive ∧ u.Positive := by
  simp [positive_operator_iff, Mul.term_eq, bv_func]

@[simp] lemma _root_.LO.FirstOrder.Semiterm.Operator.Exp.positive_iff [L.Exp] (t :
    Semiterm L ξ (n + 1)) :
    (Operator.Exp.exp.operator ![t]).Positive ↔ t.Positive := by
  simp [positive_operator_iff, Exp.term_eq, bv_func]

section «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
def npow (L : Language) [Operator.One L] [Operator.Mul L] (n : ℕ) : Operator L 1 :=
  Operator.Mul.mul.foldr (One.one.comp ![]) (List.replicate n (bvar 0))

variable [Operator.One L] [Operator.Mul L]


lemma npow_zero : npow L 0 = One.one.comp ![] := rfl

lemma npow_succ : npow L (n + 1) = Operator.Mul.mul.comp ![npow L n, bvar 0] := rfl

end «lp_section_2»

@[simp] lemma npow_positive_iff [Operator.One L] [L.Mul] (t : Semiterm L ξ (n + 1)) (k : ℕ) :
    ((Operator.npow L k).operator ![t]).Positive ↔ k = 0 ∨ t.Positive := by
  cases k
  · simp only [npow_zero, operator_comp, positive_operator_iff, Matrix.cons_val_fin_one,
      Fin.forall_fin_one, IsEmpty.forall_iff, true_or]
  · simp only [npow_succ, operator_comp, positive_operator_iff, Matrix.cons_val_fin_one,
      Fin.forall_fin_one, Fin.forall_fin_two, Matrix.vecCons_zero, Matrix.cons_val_one,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or]
    simp only [Mul.term_eq, bv_func, bv_bvar, Finset.biUnion_singleton_eq_self, Finset.mem_univ,
      forall_const]
    constructor
    · intro h
      exact h.2 (by simp [bvar])
    · intro h
      exact ⟨fun _ => h, fun _ => h⟩

namespace GoedelNumber

variable {α} [GoedelNumber L α]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev goedelNumber' (a : α) : Semiterm L ξ n := const (goedelNumber a)

instance : GoedelQuote α (Semiterm L ξ n) := ⟨goedelNumber'⟩

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def ofEncodable [Operator.Zero L] [Operator.One L] [Operator.Add L] {α : Type*} [Encodable α] :
    GoedelNumber L α :=
  ⟨Operator.encode L⟩

end GoedelNumber

end Operator

section «lp_section_3»

variable {L : Language}

@[simp] lemma complexity_zero [L.Zero] : ((Operator.Zero.zero : Const L) :
    Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.Zero.term_eq, complexity_func]

@[simp] lemma complexity_one [L.One] : ((Operator.One.one : Const L) :
    Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.One.term_eq, complexity_func]

@[simp] lemma complexity_add [L.Add] (t u : Semiterm L ξ n) :
    (Operator.Add.add.operator ![t, u]).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.operator, Operator.Add.term_eq, complexity_func, Rew.func]
  simp [show (Finset.univ : Finset (Fin 2)) =
    {0, 1} from by ext i; cases i using Fin.cases <;> simp [Fin.eq_zero]]

@[simp] lemma complexity_mul [L.Mul] (t u : Semiterm L ξ n) :
    (Operator.Mul.mul.operator ![t, u]).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.operator, Operator.Mul.term_eq, complexity_func, Rew.func]
  simp [show (Finset.univ : Finset (Fin 2)) =
    {0, 1} from by ext i; cases i using Fin.cases <;> simp [Fin.eq_zero]]

end «lp_section_3»

section «lp_section_4»

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Semiterm.Operator.val
    {M : Type w} [s : Structure L M] (o : Operator L k) (v :
    Fin k → M) :
    M :=
  Semiterm.val s v Empty.elim o.term

variable {M : Type w} {s : Structure L M}

lemma val_operator {k} (o : Operator L k) (v) :
    val s e ε (o.operator v) = o.val (fun x => (v x).val s e ε) := by
  rw [Operator.operator, val_substs, val_emb, Operator.val]
  congr
  funext x
  exact Empty.elim x

@[simp 1100] lemma val_const (o : Const L) :
    val s e ε o.const = o.val ![] := by
  simp [Operator.const, val_operator, Matrix.empty_eq]

@[simp] lemma val_operator₀ (o : Const L) :
    val s e ε (o.operator v) = o.val ![] := by
  simp [Matrix.empty_eq]

@[simp] lemma val_operator₁ (o : Operator L 1) :
    val s e ε (o.operator ![t]) = o.val ![t.val s e ε] := by
  rw [val_operator]
  congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact Fin.elim0 i

@[simp] lemma val_operator₂ (o : Operator L 2) (t u) :
    val s e ε (o.operator ![t, u]) = o.val ![t.val s e ε, u.val s e ε] :=
  by
    rw [val_operator]
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Fin.elim0 i

lemma _root_.LO.FirstOrder.Semiterm.Operator.val_comp (o₁ : Operator L k) (o₂ :
    Fin k → Operator L m) (v :
    Fin m → M) :
  (o₁.comp o₂).val v = o₁.val (fun i => (o₂ i).val v) := by
  simpa [Operator.comp, Operator.val] using
    (Semiterm.val_operator (s := s) (e := v) (ε := Empty.elim) (o := o₁)
      (v := fun i => (o₂ i).term))

@[simp] lemma _root_.LO.FirstOrder.Semiterm.Operator.val_bvar {n} (x : Fin n) (v : Fin n → M) :
    (Operator.bvar (L := L) x).val v = v x := by simp [Operator.bvar, Operator.val]

end «lp_section_4»

end Semiterm

namespace Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
structure Operator (L : Language.{u}) (n : ℕ) where
  /-- Imported declaration from the Incompleteness formalization. -/
  sentence : Semisentence L n

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Const (L : Language.{u}) := Operator L 0

namespace Operator

/-- Imported declaration from the Incompleteness formalization. -/
def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L ξ n) :
    Semiformula L ξ n :=
  Rewriting.embedding o.sentence <~ v

/-- Imported declaration from the Incompleteness formalization. -/
@[coe] def const (c : Const L) : Semiformula L ξ n := c.operator ![]

instance : Coe (Const L) (Semiformula L ξ n) := ⟨Operator.const⟩

/-- Imported declaration from the Incompleteness formalization. -/
def comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

lemma operator_comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l) (v :
    Fin l → Semiterm L ξ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    unfold operator Rewriting.embedding Rewriting.substitute comp
    simp only [operator, ← TransitiveRewriting.comp_app, Rew.emb_eq_id, Rew.comp_id];
    congr 2
    ext <;> simp only [Rew.comp_app, Rew.substs_bvar, Rew.emb_bvar, Rew.substs_fvar]
    · congr
    · contradiction

/-- Imported declaration from the Incompleteness formalization. -/
def and {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋏ o₂.sentence⟩

/-- Imported declaration from the Incompleteness formalization. -/
def or {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋎ o₂.sentence⟩

@[simp] lemma operator_and (o₁ o₂ : Operator L k) (v : Fin k → Semiterm L ξ n) :
  (o₁.and o₂).operator v = o₁.operator v ⋏ o₂.operator v := by simp [operator, and]

@[simp] lemma operator_or (o₁ o₂ : Operator L k) (v : Fin k → Semiterm L ξ n) :
  (o₁.or o₂).operator v = o₁.operator v ⋎ o₂.operator v := by simp [operator, or]

/-- Imported declaration from the Incompleteness formalization. -/
protected class Eq (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  eq : Semiformula.Operator L 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class LT (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  lt : Semiformula.Operator L 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class LE (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  le : Semiformula.Operator L 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class Mem (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  mem : Semiformula.Operator L 2

/-- Imported declaration from the Incompleteness formalization. -/
notation "op(=)" => Operator.Eq.eq

/-- Imported declaration from the Incompleteness formalization. -/
notation "op(<)" => Operator.LT.lt

/-- Imported declaration from the Incompleteness formalization. -/
notation "op(≤)" => Operator.LE.le

/-- Imported declaration from the Incompleteness formalization. -/
notation "op(∈)" => Operator.Mem.mem

instance [Language.Eq L] : Operator.Eq L := ⟨⟨Semiformula.rel Language.Eq.eq Semiterm.bvar⟩⟩

instance [Language.LT L] : Operator.LT L := ⟨⟨Semiformula.rel Language.LT.lt Semiterm.bvar⟩⟩

instance [Operator.Eq L] [Operator.LT L] : Operator.LE L := ⟨Eq.eq.or LT.lt⟩

lemma _root_.LO.FirstOrder.Semiformula.Operator.Eq.sentence_eq [L.Eq] :
    (@Eq.eq L _).sentence = Semiformula.rel Language.Eq.eq Semiterm.bvar :=
  rfl

lemma _root_.LO.FirstOrder.Semiformula.Operator.LT.sentence_eq [L.LT] :
    (@LT.lt L _).sentence = Semiformula.rel Language.LT.lt Semiterm.bvar :=
  rfl

lemma _root_.LO.FirstOrder.Semiformula.Operator.LE.sentence_eq [L.Eq] [L.LT] :
    (@LE.le L _).sentence = Eq.eq.sentence ⋎ LT.lt.sentence :=
  rfl

lemma _root_.LO.FirstOrder.Semiformula.Operator.LE.def_of_Eq_of_LT [Operator.Eq L] [Operator.LT L] :
    (@Operator.LE.le L _) = Eq.eq.or LT.lt := rfl

@[simp] lemma _root_.LO.FirstOrder.Semiformula.Operator.Eq.equal_inj [L.Eq] {t₁ t₂ u₁ u₂ :
    Semiterm L ξ₂ n₂} :
    Eq.eq.operator ![t₁, u₁] = Eq.eq.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, Eq.sentence_eq, Matrix.fun_eq_vec₂]

@[simp] lemma _root_.LO.FirstOrder.Semiformula.Operator.LT.lt_inj [L.LT] {t₁ t₂ u₁ u₂ :
    Semiterm L ξ₂ n₂} :
    LT.lt.operator ![t₁, u₁] = LT.lt.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, LT.sentence_eq, Matrix.fun_eq_vec₂]

@[simp] lemma _root_.LO.FirstOrder.Semiformula.Operator.LE.le_inj [L.Eq] [L.LT] {t₁ t₂ u₁ u₂ :
    Semiterm L ξ₂ n₂} :
    LE.le.operator ![t₁, u₁] = LE.le.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, LE.sentence_eq, Eq.sentence_eq, LT.sentence_eq, Matrix.fun_eq_vec₂]

lemma lt_def [L.LT] (t u : Semiterm L ξ n) :
    LT.lt.operator ![t, u] = Semiformula.rel Language.LT.lt ![t, u] := by
      simp [operator, LT.sentence_eq, rew_rel]

lemma eq_def [L.Eq] (t u : Semiterm L ξ n) :
    Eq.eq.operator ![t, u] = Semiformula.rel Language.Eq.eq ![t, u] := by
      simp [operator, Eq.sentence_eq, rew_rel]

lemma le_def [L.Eq] [L.LT] (t u : Semiterm L ξ n) :
    LE.le.operator ![t, u] = Semiformula.rel Language.Eq.eq ![t,
        u] ⋎ Semiformula.rel Language.LT.lt ![t, u] := by
  simp [operator, Eq.sentence_eq, LT.sentence_eq, LE.sentence_eq, rew_rel]

variable {L : Language}

@[simp] lemma _root_.LO.FirstOrder.Semiformula.Operator.Eq.open [L.Eq] (t u : Semiterm L ξ n) :
    (Eq.eq.operator ![t, u]).Open := by
  simp [Operator.operator, Operator.Eq.sentence_eq, Semiformula.open_rel]

@[simp] lemma _root_.LO.FirstOrder.Semiformula.Operator.LT.open [L.LT] (t u : Semiterm L ξ n) :
    (LT.lt.operator ![t, u]).Open := by
  simp [Operator.operator, Operator.LT.sentence_eq, Semiformula.open_rel]

@[simp] lemma _root_.LO.FirstOrder.Semiformula.Operator.LE.open [L.Eq] [L.LT] (t u :
    Semiterm L ξ n) :
    (LE.le.operator ![t, u]).Open := by
  simp [Operator.operator, Operator.LE.sentence_eq, Operator.Eq.sentence_eq,
    Operator.LT.sentence_eq, Semiformula.open_rel, Semiformula.open_or]

end Operator

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Semiformula.Operator.val
    {M : Type w} [s : Structure L M] {k} (o : Operator L k) (v :
    Fin k → M) :
    Prop :=
  Semiformula.Eval s v Empty.elim o.sentence

section «lp_section_5»

variable {M : Type w} {s : Structure L M}

@[simp] lemma val_operator_and {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.and o₂).val v ↔ o₁.val v ∧ o₂.val v := by simp [Operator.and, Operator.val]

@[simp] lemma val_operator_or {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.or o₂).val v ↔ o₁.val v ∨ o₂.val v := by simp [Operator.or, Operator.val]

lemma eval_operator {k} {o : Operator L k} {v : Fin k → Semiterm L ξ n} :
    Eval s e ε (o.operator v) ↔ o.val (fun i => (v i).val s e ε) := by
  simp [Operator.operator, eval_substs, Operator.val]

@[simp] lemma eval_operator₀ {o : Const L} {v} :
    Eval s e ε (o.operator v) ↔ o.val (M := M) ![] := by
  simp [eval_operator, Matrix.empty_eq]

@[simp] lemma eval_operator₁ {o : Operator L 1} {t : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t]) ↔ o.val ![t.val s e ε] := by
  simp [eval_operator, Matrix.constant_eq_singleton]

@[simp] lemma eval_operator₂ {o : Operator L 2} {t₁ t₂ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε] := by
  rw [eval_operator]
  apply of_eq
  congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

end «lp_section_5»

/-- Imported declaration from the Incompleteness formalization. -/
def ballLT [Operator.LT L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) :
    Semiformula L ξ n :=
  ∀[Operator.LT.lt.operator ![#0, Rew.bShift t]] φ

/-- Imported declaration from the Incompleteness formalization. -/
def bexLT [Operator.LT L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) :
    Semiformula L ξ n :=
  ∃[Operator.LT.lt.operator ![#0, Rew.bShift t]] φ

/-- Imported declaration from the Incompleteness formalization. -/
def ballLE [Operator.LE L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) :
    Semiformula L ξ n :=
  ∀[Operator.LE.le.operator ![#0, Rew.bShift t]] φ

/-- Imported declaration from the Incompleteness formalization. -/
def bexLE [Operator.LE L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) :
    Semiformula L ξ n :=
  ∃[Operator.LE.le.operator ![#0, Rew.bShift t]] φ

/-- Imported declaration from the Incompleteness formalization. -/
def ballMem [Operator.Mem L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) :
    Semiformula L ξ n :=
  ∀[Operator.Mem.mem.operator ![#0, Rew.bShift t]] φ

/-- Imported declaration from the Incompleteness formalization. -/
def bexMem [Operator.Mem L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) :
    Semiformula L ξ n :=
  ∃[Operator.Mem.mem.operator ![#0, Rew.bShift t]] φ

end Semiformula

namespace Rew

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

protected lemma operator (o : Semiterm.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator (fun i => ω (v i)) := by
  simp only [Semiterm.Operator.operator, ←comp_app]
  congr 1
  ext <;> simp only [comp_app, emb_bvar, substs_bvar]; try contradiction

protected lemma operator' (o : Semiterm.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator (ω ∘ v) := ω.operator o v

@[simp] lemma finitary0 (o : Semiterm.Operator L 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator ![] := by simp [ω.operator', Matrix.empty_eq]

@[simp] lemma finitary1 (o : Semiterm.Operator L 1) (t : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t]) = o.operator ![ω t] := by simp [ω.operator']

@[simp] lemma finitary2 (o : Semiterm.Operator L 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp [ω.operator']

@[simp 1100] lemma finitary3 (o : Semiterm.Operator L 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp [ω.operator']

@[simp 1100] protected lemma const (c : Semiterm.Const L) : ω c = c :=
  by simp [Semiterm.Operator.const]

lemma hom_operator (o : Semiformula.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ o.operator v = o.operator fun i ↦ ω (v i) := by
  unfold Semiformula.Operator.operator Rewriting.substitute Rewriting.embedding
  simp only [← TransitiveRewriting.comp_app]; congr 2
  ext <;> simp only [Rew.comp_app, Rew.substs_bvar, Rew.emb_bvar]; contradiction

lemma hom_operator' (o : Semiformula.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ o.operator v = o.operator (ω ∘ v) := ω.hom_operator o v

@[simp] lemma hom_finitary0 (o : Semiformula.Operator L 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator v) = o.operator ![] := by simp [ω.hom_operator', Matrix.empty_eq]

@[simp] lemma hom_finitary1 (o : Semiformula.Operator L 1) (t : Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator ![t]) = o.operator ![ω t] := by simp [ω.hom_operator']

@[simp] lemma hom_finitary2 (o : Semiformula.Operator L 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp [ω.hom_operator']

@[simp] lemma hom_finitary3 (o : Semiformula.Operator L 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp [ω.hom_operator']

@[simp] lemma hom_const : ω ▹ (Semiformula.Operator.const c :
    Semiformula L ξ₁ n₁) = Semiformula.Operator.const c := by
  simp [Semiformula.Operator.const, ω.hom_operator']

open Semiformula

lemma eq_equal_iff [L.Eq] {φ : Semiformula L ξ₁ n₁} {t u : Semiterm L ξ₂ n₂} :
    ω ▹ φ = Operator.Eq.eq.operator ![t, u] ↔
        ∃ t' u', ω t' = t ∧ ω u' = u ∧ φ = Operator.Eq.eq.operator ![t', u'] := by
  cases φ using Semiformula.rec' <;> simp only [LogicalConnective.HomClass.map_top,
    LogicalConnective.HomClass.map_bot, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_or, Rewriting.app_all, Rewriting.app_ex, Operator.operator,
    Operator.Eq.sentence_eq, rew_rel, rew_nrel, emb_bvar, substs_bvar, reduceCtorEq,
    and_false, exists_false, rel.injEq, exists_and_left]
  case hrel k' r' v =>
    by_cases hk : k' = 2 <;> simp [hk]; rcases hk with rfl; simp
    by_cases hr : r' = Language.Eq.eq <;> simp [hr, funext_iff]

lemma eq_lt_iff [L.LT] {φ : Semiformula L ξ₁ n₁} {t u : Semiterm L ξ₂ n₂} :
    ω ▹ φ = Operator.LT.lt.operator ![t, u] ↔
    ∃ t' u', ω t' = t ∧ ω u' = u ∧ φ = Operator.LT.lt.operator ![t', u'] := by
  cases φ using Semiformula.rec' <;> simp only [LogicalConnective.HomClass.map_top,
    LogicalConnective.HomClass.map_bot, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_or, Rewriting.app_all, Rewriting.app_ex, Operator.operator,
    Operator.LT.sentence_eq, rew_rel, rew_nrel, emb_bvar, substs_bvar, reduceCtorEq,
    and_false, exists_false, rel.injEq, exists_and_left]
  case hrel k' r' v =>
    by_cases hk : k' = 2 <;> simp [hk]; rcases hk with rfl; simp
    by_cases hr : r' = Language.LT.lt <;> simp [hr, funext_iff]

end Rew

namespace Structure

open Semiterm Semiformula

variable (L) (M : Type*) [Structure L M]

/-- Imported declaration from the Incompleteness formalization. -/
protected class Zero [Operator.Zero L] [Zero M] : Prop where
  zero : (@Operator.Zero.zero L _).val ![] = (0 : M)

/-- Imported declaration from the Incompleteness formalization. -/
protected class One [Operator.One L] [One M] : Prop where
  one : (@Operator.One.one L _).val ![] = (1 : M)

/-- Imported declaration from the Incompleteness formalization. -/
protected class Add [Operator.Add L] [Add M] : Prop where
  add : ∀ a b : M, (@Operator.Add.add L _).val ![a, b] = a + b

/-- Imported declaration from the Incompleteness formalization. -/
protected class Mul [Operator.Mul L] [Mul M] : Prop where
  mul : ∀ a b : M, (@Operator.Mul.mul L _).val ![a, b] = a * b

/-- Imported declaration from the Incompleteness formalization. -/
protected class Exp [Operator.Exp L] [Exp M] : Prop where
  exp : ∀ a : M, (@Operator.Exp.exp L _).val ![a] = exp a

/-- Imported declaration from the Incompleteness formalization. -/
protected class Eq [Operator.Eq L] : Prop where
  eq : ∀ a b : M, (@Operator.Eq.eq L _).val ![a, b] ↔ a = b

/-- Imported declaration from the Incompleteness formalization. -/
protected class LT [Operator.LT L] [LT M] : Prop where
  lt : ∀ a b : M, (@Operator.LT.lt L _).val ![a, b] ↔ a < b

/-- Imported declaration from the Incompleteness formalization. -/
protected class LE [Operator.LE L] [LE M] : Prop where
  le : ∀ a b : M, (@Operator.LE.le L _).val ![a, b] ↔ a ≤ b

/-- Imported declaration from the Incompleteness formalization. -/
class Mem [Operator.Mem L] [Membership M M] : Prop where
  mem : ∀ a b : M, (@Operator.Mem.mem L _).val ![a, b] ↔ a ∈ b

attribute [simp] Zero.zero One.one Add.add Mul.mul Exp.exp Eq.eq LT.lt LE.le Mem.mem

instance [L.Eq] [L.LT] [Structure.Eq L M] [PartialOrder M] [Structure.LT L M] :
  Structure.LE L M := ⟨by
    intro a b
    rw [Operator.LE.def_of_Eq_of_LT]
    simp only [Semiformula.val_operator_or, Structure.Eq.eq, Structure.LT.lt]
    exact le_iff_eq_or_lt.symm⟩

variable {L}

@[simp] lemma zero_eq_of_lang [L.Zero] [Zero M] [Structure.Zero L M] :
    Structure.func (L := L) Language.Zero.zero ![] = (0 : M) := by
  simpa[Semiterm.Operator.val, Semiterm.Operator.Zero.zero, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.Zero.zero (L := L) (M := M)

@[simp] lemma one_eq_of_lang [L.One] [One M] [Structure.One L M] :
    Structure.func (L := L) Language.One.one ![] = (1 : M) := by
  simpa[Semiterm.Operator.val, Semiterm.Operator.One.one, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.One.one (L := L) (M := M)

@[simp] lemma add_eq_of_lang [L.Add] [Add M] [Structure.Add L M] {v : Fin 2 → M} :
    Structure.func (L := L) Language.Add.add v = v 0 + v 1 := by
  simpa[Semiterm.Operator.val, Semiterm.Operator.Add.term_eq, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.Add.add (L := L) (v 0) (v 1)

@[simp] lemma mul_eq_of_lang [L.Mul] [Mul M] [Structure.Mul L M] {v : Fin 2 → M} :
    Structure.func (L := L) Language.Mul.mul v = v 0 * v 1 := by
  simpa[Semiterm.Operator.val, Semiterm.Operator.Mul.term_eq, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.Mul.mul (L := L) (v 0) (v 1)

@[simp] lemma exp_eq_of_lang [L.Exp] [Exp M] [Structure.Exp L M] {v : Fin 1 → M} :
    Structure.func (L := L) Language.Exp.exp v = exp (v 0) := by
  simpa[Semiterm.Operator.val, Semiterm.Operator.Exp.term_eq, val_func,
    ←Matrix.constant_eq_singleton'] using Structure.Exp.exp (L := L) (v 0)

lemma le_iff_of_eq_of_lt
    [Operator.Eq L] [Operator.LT L] [LT M] [Structure.Eq L M] [Structure.LT L M] {a b :
    M} :
    (@Operator.LE.le L _).val ![a, b] ↔ a = b ∨ a < b := by
  simp [Operator.LE.def_of_Eq_of_LT]

@[simp] lemma eq_lang [L.Eq] [Structure.Eq L M] {v : Fin 2 → M} :
    Structure.rel (L := L) Language.Eq.eq v ↔ v 0 = v 1 := by
  simpa[Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, eval_rel,
    ←Matrix.fun_eq_vec₂] using Structure.Eq.eq (L := L) (v 0) (v 1)

@[simp] lemma lt_lang [L.LT] [LT M] [Structure.LT L M] {v : Fin 2 → M} :
    Structure.rel (L := L) Language.LT.lt v ↔ v 0 < v 1 := by
  simpa[Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, eval_rel,
    ←Matrix.fun_eq_vec₂] using Structure.LT.lt (L := L) (v 0) (v 1)

lemma operator_val_ofEquiv_iff (φ : M ≃ N) {k : ℕ} {o : Semiformula.Operator L k} {v : Fin k → N} :
    letI : Structure L N := ofEquiv φ
    o.val v ↔ o.val (φ.symm ∘ v) := by
      simp [Semiformula.Operator.val, eval_ofEquiv_iff, Empty.eq_elim]

end Structure

namespace Semiformula

variable {M : Type*} {s : Structure L M}

variable {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)}

@[simp] lemma eval_ballLT [Operator.LT L] [LT M] [Structure.LT L M] {e ε} :
    Eval s e ε (φ.ballLT t) ↔ ∀ x < t.val s e ε, Eval s (x :> e) ε φ := by simp [ballLT]

@[simp] lemma eval_bexLT [Operator.LT L] [LT M] [Structure.LT L M] {e ε} :
    Eval s e ε (φ.bexLT t) ↔ ∃ x < t.val s e ε, Eval s (x :> e) ε φ := by simp [bexLT]

@[simp] lemma eval_ballLE [Operator.LE L] [LE M] [Structure.LE L M] {e ε} :
    Eval s e ε (φ.ballLE t) ↔ ∀ x ≤ t.val s e ε, Eval s (x :> e) ε φ := by simp [ballLE]

@[simp] lemma eval_bexLE [Operator.LE L] [LE M] [Structure.LE L M] {e ε} :
    Eval s e ε (φ.bexLE t) ↔ ∃ x ≤ t.val s e ε, Eval s (x :> e) ε φ := by simp [bexLE]

@[simp] lemma eval_ballMem [Operator.Mem L] [Membership M M] [Structure.Mem L M] {e ε} :
    Eval s e ε (φ.ballMem t) ↔ ∀ x ∈ t.val s e ε, Eval s (x :> e) ε φ := by simp [ballMem]

@[simp] lemma eval_bexMem [Operator.Mem L] [Membership M M] [Structure.Mem L M] {e ε} :
    Eval s e ε (φ.bexMem t) ↔ ∃ x ∈ t.val s e ε, Eval s (x :> e) ε φ := by simp [bexMem]

end Semiformula

namespace Semiterm

variable [L.Zero] [L.One] [L.Add]

/-- Imported declaration from the Incompleteness formalization. -/
@[coe] abbrev numeral (k : ℕ) : Semiterm L ξ n := Operator.numeral L k

instance : Coe ℕ (Semiterm L ξ n) := ⟨numeral⟩

end Semiterm

end FirstOrder

end LO
