/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.Entailment

/-!
# Language of first-order logic

This file defines the language of first-order logic.

- `LO.FirstOrder.Language.empty` is the empty language.
- `LO.FirstOrder.Language.constant C` is a language with only constants of the element `C`.
- `LO.FirstOrder.Language.oRing`, `ℒₒᵣ` is the language of ordered ring.
-/

namespace LO

namespace FirstOrder

/-- Imported declaration from the Incompleteness formalization. -/
structure Language where
  /-- Imported declaration from the Incompleteness formalization. -/
  Func : Nat → Type u
  /-- Imported declaration from the Incompleteness formalization. -/
  Rel  : Nat → Type u

namespace Language

/-- Imported declaration from the Incompleteness formalization. -/
class IsRelational (L : Language) where
  func_empty : ∀ k, IsEmpty (L.Func (k + 1))

/-- Imported declaration from the Incompleteness formalization. -/
class IsConstant (L : Language) extends IsRelational L where
  rel_empty : ∀ k, IsEmpty (L.Rel k)

/-- Imported declaration from the Incompleteness formalization. -/
class ConstantInhabited (L : Language) extends Inhabited (L.Func 0)

instance {L : Language} [L.ConstantInhabited] : Inhabited (L.Func 0) := inferInstance

/-- Imported declaration from the Incompleteness formalization. -/
protected def empty : Language where
  Func := fun _ => PEmpty
  Rel  := fun _ => PEmpty

instance : Inhabited Language := ⟨Language.empty⟩

/-- Imported declaration from the Incompleteness formalization. -/
inductive GraphFunc : ℕ → Type
  | start : GraphFunc 0
  | terminal : GraphFunc 0

/-- Imported declaration from the Incompleteness formalization. -/
inductive GraphRel : ℕ → Type
  | equal : GraphRel 2
  | le : GraphRel 2

/-- Imported declaration from the Incompleteness formalization. -/
def graph : Language where
  Func := GraphFunc
  Rel := GraphRel

/-- Imported declaration from the Incompleteness formalization. -/
inductive BinaryRel : ℕ → Type
  | isone : BinaryRel 1
  | equal : BinaryRel 2
  | le : BinaryRel 2

/-- Imported declaration from the Incompleteness formalization. -/
def binary : Language where
  Func := fun _ => Empty
  Rel := BinaryRel

/-- Imported declaration from the Incompleteness formalization. -/
inductive EqRel : ℕ → Type
  | equal : EqRel 2

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def equal : Language where
  Func := fun _ => Empty
  Rel := EqRel

instance (k) : ToString (equal.Func k) := ⟨fun _ => ""⟩

instance (k) : ToString (equal.Rel k) := ⟨fun _ => "\\mathrm{Eq}"⟩

instance (k) : DecidableEq (equal.Func k) := fun a b => by rcases a

instance (k) : DecidableEq (equal.Rel k) := fun a b => by rcases a; rcases b; exact isTrue (by simp)

instance (k) : Encodable (equal.Func k) := IsEmpty.toEncodable

instance (k) : Encodable (equal.Rel k) where
  encode := fun _ => 0
  decode := fun _ =>
    match k with
    | 2 => some EqRel.equal
    | _ => none
  encodek := fun x => by rcases x; simp

namespace ORing

/-- Imported declaration from the Incompleteness formalization. -/
inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | add : Func 2
  | mul : Func 2

/-- Imported declaration from the Incompleteness formalization. -/
inductive Rel : ℕ → Type
  | eq : Rel 2
  | lt : Rel 2

end ORing

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def oRing : Language where
  Func := ORing.Func
  Rel := ORing.Rel

/-- Imported declaration from the Incompleteness formalization. -/
notation "ℒₒᵣ" => oRing

namespace ORing

instance (k) : ToString (oRing.Func k) :=
⟨ fun s =>
  match s with
  | Func.zero => "0"
  | Func.one  => "1"
  | Func.add  => "(+)"
  | Func.mul  => "(\\cdot)"⟩

instance (k) : ToString (oRing.Rel k) :=
⟨ fun s =>
  match s with
  | Rel.eq => "\\mathrm{Eq}"
  | Rel.lt    => "\\mathrm{LT}"⟩

instance (k) : DecidableEq (oRing.Func k) := fun a b =>
  by
    rcases a <;> rcases b <;> simp only [reduceCtorEq] <;>
      try {exact instDecidableTrue} <;>
      try {exact instDecidableFalse}

instance (k) : DecidableEq (oRing.Rel k) := fun a b =>
  by
    rcases a <;> rcases b <;> simp only [reduceCtorEq] <;>
      try {exact instDecidableTrue} <;>
      try {exact instDecidableFalse}

instance (k) : Encodable (oRing.Func k) where
  encode := fun x =>
    match x with
    | Func.zero => 0
    | Func.one  => 1
    | Func.add  => 0
    | Func.mul  => 1
  decode := fun e =>
    match k, e with
    | 0, 0 => some Func.zero
    | 0, 1 => some Func.one
    | 2, 0 => some Func.add
    | 2, 1 => some Func.mul
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance Func1IsEmpty : IsEmpty (oRing.Func 1) := ⟨by rintro ⟨⟩⟩

/-- Imported declaration from the Incompleteness formalization. -/
theorem FuncGe3IsEmpty : ∀ k ≥ 3, IsEmpty (oRing.Func k)
  | 0       => by simp
  | 1       => by simp [show ¬3 ≤ 1 from of_decide_eq_false rfl]
  | 2       => by simp [show ¬3 ≤ 2 from of_decide_eq_false rfl]
  | (n + 3) => fun _ => ⟨by rintro ⟨⟩⟩

instance (k) : Encodable (oRing.Rel k) where
  encode := fun x =>
    match x with
    | Rel.eq => 0
    | Rel.lt => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | 2, 1 => some Rel.lt
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

/-- Imported declaration from the Incompleteness formalization. -/
def funcEquivFinFour : (k : ℕ) × oRing.Func k ≃ Fin 4 where
  toFun f :=
    match f with
    | ⟨0, Func.zero⟩ => 0
    | ⟨0,  Func.one⟩ => 1
    | ⟨2,  Func.add⟩ => 2
    | ⟨2,  Func.mul⟩ => 3
  invFun x :=
    match x with
    | 0 => ⟨0, Func.zero⟩
    | 1 => ⟨0,  Func.one⟩
    | 2 => ⟨2,  Func.add⟩
    | 3 => ⟨2,  Func.mul⟩
  left_inv f :=
    match f with
    | ⟨0, Func.zero⟩ => rfl
    | ⟨0,  Func.one⟩ => rfl
    | ⟨2,  Func.add⟩ => rfl
    | ⟨2,  Func.mul⟩ => rfl
  right_inv x :=
    match x with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl

/-- Imported declaration from the Incompleteness formalization. -/
def relEquivFinTwo : (k : ℕ) × oRing.Rel k ≃ Fin 2 where
  toFun f :=
    match f with
    | ⟨2, Rel.eq⟩ => 0
    | ⟨2, Rel.lt⟩ => 1
  invFun x :=
    match x with
    | 0 => ⟨2, Rel.eq⟩
    | 1 => ⟨2, Rel.lt⟩
  left_inv f :=
    match f with
    | ⟨2, Rel.eq⟩ => rfl
    | ⟨2, Rel.lt⟩ => rfl
  right_inv x :=
    match x with
    | 0 => rfl
    | 1 => rfl

end ORing

namespace Constant

variable (C : Type*)

/-- Imported declaration from the Incompleteness formalization. -/
inductive Func : ℕ → Type _
  | const (c : C) : Func 0

end Constant

section «lp_section_1»

variable (C : Type*)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Language.constLang : Language := ⟨Constant.Func C, fun _ => PEmpty⟩

--instance : Coe (Type*) Language := ⟨constLang⟩

instance : Coe C ((constLang C).Func 0) := ⟨Constant.Func.const⟩

instance : IsConstant (constLang C) where
  func_empty := fun k => ⟨by rintro ⟨⟩⟩
  rel_empty  := fun k => ⟨by rintro ⟨⟩⟩

/-- Imported declaration from the Incompleteness formalization. -/
abbrev unit : Language := constLang PUnit

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
def ofFunc (F : ℕ → Type v) : Language := ⟨F, fun _ => PEmpty⟩

/-- Imported declaration from the Incompleteness formalization. -/
def add (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) : Language :=
  ⟨fun k => L₁.Func k ⊕ L₂.Func k, fun k => L₁.Rel k ⊕ L₂.Rel k⟩

instance : _root_.Add Language := ⟨add⟩

/-- Imported declaration from the Incompleteness formalization. -/
def sigma (L : ι → Language) : Language := ⟨fun k => Σ i, (L i).Func k, fun k => Σ i, (L i).Rel k⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected class Eq (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  eq : L.Rel 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class LT (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  lt : L.Rel 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class Zero (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  zero : L.Func 0

/-- Imported declaration from the Incompleteness formalization. -/
protected class One (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  one : L.Func 0

/-- Imported declaration from the Incompleteness formalization. -/
protected class Add (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  add : L.Func 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class Mul (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  mul : L.Func 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class Pow (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  pow : L.Func 2

/-- Imported declaration from the Incompleteness formalization. -/
protected class Exp (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  exp : L.Func 1

/-- Imported declaration from the Incompleteness formalization. -/
class Pairing (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  pair : L.Func 2

/-- Imported declaration from the Incompleteness formalization. -/
class Star (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  star : L.Func 0

attribute [match_pattern] Zero.zero One.one Add.add Mul.mul Exp.exp Eq.eq LT.lt Star.star

/-- Imported declaration from the Incompleteness formalization. -/
class ORing (L : Language) extends L.Eq, L.LT, L.Zero, L.One, L.Add, L.Mul

instance : ORing oRing where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

instance : ConstantInhabited ℒₒᵣ where
  default := Language.Zero.zero

instance : Star unit where
  star := ()

instance (L : Language) (S : Language) [Star S] : Star (L.add S) where
  star := Sum.inr Star.star

instance (L : Language) (S : Language) [L.Zero] : (L.add S).Zero where
  zero := Sum.inl Zero.zero

instance (L : Language) (S : Language) [L.One] : (L.add S).One where
  one := Sum.inl One.one

instance (L : Language) (S : Language) [L.Add] : (L.add S).Add where
  add := Sum.inl Add.add

instance (L : Language) (S : Language) [L.Mul] : (L.add S).Mul where
  mul := Sum.inl Mul.mul

instance (L : Language) (S : Language) [L.Eq] : (L.add S).Eq where
  eq := Sum.inl Eq.eq

instance (L : Language) (S : Language) [L.LT] : (L.add S).LT where
  lt := Sum.inl LT.lt

/-- Imported declaration from the Incompleteness formalization. -/
@[ext] structure Hom (L₁ L₂ : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  func : {k : ℕ} → L₁.Func k → L₂.Func k
  /-- Imported declaration from the Incompleteness formalization. -/
  rel : {k : ℕ} → L₁.Rel k → L₂.Rel k

/-- Imported declaration from the Incompleteness formalization. -/
scoped[LO.FirstOrder] infix:25 " →ᵥ " => LO.FirstOrder.Language.Hom

namespace Hom
variable (L L₁ L₂ L₃ : Language) (Φ : Hom L₁ L₂)

/-- Imported declaration from the Incompleteness formalization. -/
protected def id : L →ᵥ L where
  func := id
  rel := id

variable {L L₁ L₂ L₃}

/-- Imported declaration from the Incompleteness formalization. -/
def comp (Ψ : L₂ →ᵥ L₃) (Φ : L₁ →ᵥ L₂) : L₁ →ᵥ L₃ where
  func := Ψ.func ∘ Φ.func
  rel  := Ψ.rel ∘ Φ.rel

/-- Imported declaration from the Incompleteness formalization. -/
def add₁ (L₁ : Language) (L₂ : Language) : L₁ →ᵥ L₁.add L₂ := ⟨Sum.inl, Sum.inl⟩

/-- Imported declaration from the Incompleteness formalization. -/
def add₂ (L₁ : Language) (L₂ : Language) : L₂ →ᵥ L₁.add L₂ := ⟨Sum.inr, Sum.inr⟩

/-- Imported declaration from the Incompleteness formalization. -/
lemma func_add₁ (L₁ : Language) (L₂ : Language) (f : L₁.Func k) :
    (add₁ L₁ L₂).func f = Sum.inl f := rfl

lemma rel_add₁ (L₁ : Language) (L₂ : Language) (r : L₁.Rel k) :
    (add₁ L₁ L₂).rel r = Sum.inl r := rfl

lemma func_add₂ (L₁ : Language) (L₂ : Language) (f : L₂.Func k) :
    (add₂ L₁ L₂).func f = Sum.inr f := rfl

lemma rel_add₂ (L₁ : Language) (L₂ : Language) (r : L₂.Rel k) :
    (add₂ L₁ L₂).rel r = Sum.inr r := rfl

@[simp] lemma add₂_star (L₁ : Language) (L₂ : Language) [Star L₂] :
    (add₂ L₁ L₂).func Star.star = Star.star := rfl

@[simp] lemma add₁_zero (L₁ : Language) (L₂ : Language) [L₁.Zero] :
    (add₁ L₁ L₂).func Zero.zero = Zero.zero := rfl

@[simp] lemma add₁_one (L₁ : Language) (L₂ : Language) [L₁.One] :
    (add₁ L₁ L₂).func One.one = One.one := rfl

@[simp] lemma add₁_add (L₁ : Language) (L₂ : Language) [L₁.Add] :
    (add₁ L₁ L₂).func Add.add = Add.add := rfl

@[simp] lemma add₁_mul (L₁ : Language) (L₂ : Language) [L₁.Mul] :
    (add₁ L₁ L₂).func Mul.mul = Mul.mul := rfl

@[simp] lemma add₁_eq (L₁ : Language) (L₂ : Language) [L₁.Eq] :
    (add₁ L₁ L₂).rel Eq.eq = Eq.eq := rfl

@[simp] lemma add₁_lt (L₁ : Language) (L₂ : Language) [L₁.LT] :
    (add₁ L₁ L₂).rel LT.lt = LT.lt := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def sigma (L : ι → Language) (i : ι) : L i →ᵥ Language.sigma L := ⟨fun f => ⟨i, f⟩, fun r => ⟨i, r⟩⟩

lemma func_sigma (L : ι → Language) (i : ι) (f : (L i).Func k) : (sigma L i).func f = ⟨i, f⟩ := rfl

lemma rel_sigma (L : ι → Language) (i : ι) (r : (L i).Rel k) : (sigma L i).rel r = ⟨i, r⟩ := rfl

end Hom

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Language.ORing.embedding (L : Language) [ORing L] : ℒₒᵣ →ᵥ L where
  func := fun {n} f ↦
    match n, f with
    | 0, Zero.zero => Zero.zero
    | 0, One.one   => One.one
    | 2, Add.add   => Add.add
    | 2, Mul.mul   => Mul.mul
  rel := fun {n} r ↦
    match n, r with
    | 2, Eq.eq => Eq.eq
    | 2, LT.lt => LT.lt
end Language

/-- Imported declaration from the Incompleteness formalization. -/
protected class _root_.LO.FirstOrder.Language.DecidableEq (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  func : (k : ℕ) → DecidableEq (L.Func k)
  /-- Imported declaration from the Incompleteness formalization. -/
  rel : (k : ℕ) → DecidableEq (L.Rel k)

instance (L : Language) [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] :
    L.DecidableEq :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance (L : Language) [L.DecidableEq] (k : ℕ) :
    DecidableEq (L.Func k) :=
  Language.DecidableEq.func k

instance (L : Language) [L.DecidableEq] (k : ℕ) :
    DecidableEq (L.Rel k) :=
  Language.DecidableEq.rel k

instance (L : Language) [L.DecidableEq] (k : ℕ) :
    DecidableEq (L.Rel k) :=
  Language.DecidableEq.rel k

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.FirstOrder.Language.Finite (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  func : Fintype ((k : ℕ) × L.Func k)
  /-- Imported declaration from the Incompleteness formalization. -/
  rel : Fintype ((k : ℕ) × L.Rel k)

instance : Language.Finite ℒₒᵣ where
  func := Fintype.ofEquiv (Fin 4) Language.ORing.funcEquivFinFour.symm
  rel := Fintype.ofEquiv (Fin 2) Language.ORing.relEquivFinTwo.symm

end FirstOrder

end LO
