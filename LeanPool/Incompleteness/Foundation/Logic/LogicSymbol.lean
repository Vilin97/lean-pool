/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Vorspiel.Vorspiel

/-!
# Logic Symbols

This file defines structure that has logical connectives $\top, \bot, \land, \lor, \to, \lnot$
and their homomorphisms.

## Main Definitions
* `LO.LogicalConnective` is defined so that `LO.LogicalConnective F` is a type that has logical
* connectives $\top, \bot, \land, \lor, \to, \lnot$.
* `LO.LogicalConnective.Hom` is defined so that `f : F →ˡᶜ G` is a homomorphism from `F` to `G`,
* i.e.,
a function that preserves logical connectives.

-/

namespace LO

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class Tilde (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  tilde : α → α

/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class Arrow (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  arrow : α → α → α

/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class Wedge (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  wedge : α → α → α

/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class Vee (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  vee : α → α → α

/-- Imported declaration from the Incompleteness formalization. -/
class LogicalConnective (α : Type*)
  extends Top α, Bot α, Tilde α, Arrow α, Wedge α, Vee α

/-- Imported declaration from the Incompleteness formalization. -/
prefix:75 "∼" => Tilde.tilde

/-- Imported declaration from the Incompleteness formalization. -/
infixr:60 " ==> " => Arrow.arrow

/-- Imported declaration from the Incompleteness formalization. -/
infixr:69 " ⋏ " => Wedge.wedge

/-- Imported declaration from the Incompleteness formalization. -/
infixr:68 " ⋎ " => Vee.vee

attribute [match_pattern]
  Tilde.tilde
  Arrow.arrow
  Wedge.wedge
  Vee.vee

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
class DeMorgan (F : Type*) [LogicalConnective F] where
  verum : ∼(⊤ : F) = ⊥
  falsum          : ∼(⊥ : F) = ⊤
  imply (φ ψ : F) : (φ ==> ψ) = ∼φ ⋎ ψ
  and (φ ψ : F)   : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ
  or (φ ψ : F)    : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ
  neg (φ : F)     : ∼∼φ = φ

attribute [simp] DeMorgan.verum DeMorgan.falsum DeMorgan.and DeMorgan.or DeMorgan.neg

/-- Introducing `∼φ` as an abbreviation of `φ ==> ⊥`. -/
class NegAbbrev (F : Type*) [Tilde F] [Arrow F] [Bot F] where
  neg {φ : F} : ∼φ = φ ==> ⊥

namespace LogicalConnective

section «lp_section_2»
variable {α : Type*} [LogicalConnective α]

/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern] def iff (a b : α) := (a ==> b) ⋏ (b ==> a)

/-- Imported declaration from the Incompleteness formalization. -/
infix:61 " <=> " => LogicalConnective.iff

end «lp_section_2»

@[reducible]
instance PropLogicSymbols : LogicalConnective Prop where
  top := True
  bot := False
  tilde := Not
  arrow := fun P Q => (P → Q)
  wedge := And
  vee := Or

@[simp] lemma _root_.LO.LogicalConnective.Prop.top_eq : ⊤ = True := rfl

@[simp] lemma _root_.LO.LogicalConnective.Prop.bot_eq : ⊥ = False := rfl

@[simp] lemma _root_.LO.LogicalConnective.Prop.neg_eq (φ : Prop) : ∼φ = ¬φ := rfl

/-- Imported declaration from the Incompleteness formalization. -/
@[simp] lemma _root_.LO.LogicalConnective.Prop.arrow_eq (φ ψ : Prop) : (φ ==> ψ) = (φ → ψ) := rfl

@[simp] lemma _root_.LO.LogicalConnective.Prop.and_eq (φ ψ : Prop) : (φ ⋏ ψ) = (φ ∧ ψ) := rfl

@[simp] lemma _root_.LO.LogicalConnective.Prop.or_eq (φ ψ : Prop) : (φ ⋎ ψ) = (φ ∨ ψ) := rfl

@[simp] lemma _root_.LO.LogicalConnective.Prop.iff_eq (φ ψ : Prop) :
    (φ <=> ψ) = (φ ↔ ψ) := by
  simp[LogicalConnective.iff, iff_iff_implies_and_implies]

instance : DeMorgan Prop where
  verum := by simp
  falsum := by simp
  imply := fun _ _ => by simp[imp_iff_not_or]
  and := fun _ _ => by simp[-not_and, not_and_or]
  or := fun _ _ => by simp[not_or]
  neg := fun _ => by simp

/-- Imported declaration from the Incompleteness formalization. -/
class HomClass (F : Type*) (α β :
    outParam Type*) [LogicalConnective α] [LogicalConnective β] [FunLike F α β] where
  map_top : ∀ (f : F), f ⊤ = ⊤
  map_bot : ∀ (f : F), f ⊥ = ⊥
  map_neg : ∀ (f : F) (φ : α), f (∼ φ) = ∼f φ
  map_imply : ∀ (f : F) (φ ψ : α), f (φ ==> ψ) = f φ ==> f ψ
  map_and : ∀ (f : F) (φ ψ : α), f (φ ⋏ ψ) = f φ ⋏ f ψ
  map_or  : ∀ (f : F) (φ ψ : α), f (φ ⋎ ψ) = f φ ⋎ f ψ

attribute [simp] HomClass.map_top HomClass.map_bot HomClass.map_neg HomClass.map_imply
  HomClass.map_and HomClass.map_or

namespace HomClass

variable (F : Type*) (α β : outParam Type*) [LogicalConnective α] [LogicalConnective β]
variable [FunLike F α β]
variable [HomClass F α β]
variable (f : F) (a b : α)

instance : CoeFun F (fun _ => α → β) := ⟨DFunLike.coe⟩

@[simp] lemma map_iff : f (a <=> b) = f a <=> f b := by simp[LogicalConnective.iff]

end HomClass

variable (α β γ : Type*) [LogicalConnective α] [LogicalConnective β] [LogicalConnective γ]

/-- Imported declaration from the Incompleteness formalization. -/
structure Hom where
  /-- Imported declaration from the Incompleteness formalization. -/
  toTr : α → β
  map_top' : toTr ⊤ = ⊤
  map_bot' : toTr ⊥ = ⊥
  map_neg' : ∀ φ, toTr (∼φ) = ∼toTr φ
  map_imply' : ∀ φ ψ, toTr (φ ==> ψ) = toTr φ ==> toTr ψ
  map_and' : ∀ φ ψ, toTr (φ ⋏ ψ) = toTr φ ⋏ toTr ψ
  map_or'  : ∀ φ ψ, toTr (φ ⋎ ψ) = toTr φ ⋎ toTr ψ

/-- Imported declaration from the Incompleteness formalization. -/
infix:25 " →ˡᶜ " => Hom

namespace Hom
variable {α β γ}

instance : FunLike (α →ˡᶜ β) α β where
  coe := toTr
  coe_injective := by
    rintro ⟨_⟩ ⟨_⟩ h
    simpa only [mk.injEq] using h

@[ext] lemma ext (f g : α →ˡᶜ β) (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

instance : HomClass (α →ˡᶜ β) α β where
  map_top := map_top'
  map_bot := map_bot'
  map_neg := map_neg'
  map_imply := map_imply'
  map_and := map_and'
  map_or := map_or'

variable (f : α →ˡᶜ β) (a b : α)

/-- Imported declaration from the Incompleteness formalization. -/
protected def id : α →ˡᶜ α where
  toTr := id
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp

@[simp] lemma app_id (a : α) : LogicalConnective.Hom.id a = a := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def comp (g : β →ˡᶜ γ) (f : α →ˡᶜ β) : α →ˡᶜ γ where
  toTr := g ∘ f
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp

@[simp] lemma app_comp (g : β →ˡᶜ γ) (f : α →ˡᶜ β) (a : α) :
     g.comp f a = g (f a) := rfl

end Hom

/-- Imported declaration from the Incompleteness formalization. -/
class AndOrClosed {F} [LogicalConnective F] (C : F → Prop) where
  verum : C ⊤
  falsum : C ⊥
  and {f g : F} : C f → C g → C (f ⋏ g)
  or  {f g : F} : C f → C g → C (f ⋎ g)

/-- Imported declaration from the Incompleteness formalization. -/
class Closed {F} [LogicalConnective F] (C : F → Prop) extends AndOrClosed C where
  not {f : F} : C f → C (∼f)
  imply {f g : F} : C f → C g → C (f ==> g)

end LogicalConnective

section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Tilde.Subclosed [Tilde F] (C : F → Prop) where
  tilde_closed : C (∼φ) → C φ

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Arrow.Subclosed [Arrow F] (C : F → Prop) where
  arrow_closed : C (φ ==> ψ) → C φ ∧ C ψ

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Wedge.Subclosed [Wedge F] (C : F → Prop) where
  wedge_closed : C (φ ⋏ ψ) → C φ ∧ C ψ

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Vee.Subclosed [Vee F] (C : F → Prop) where
  vee_closed : C (φ ⋎ ψ) → C φ ∧ C ψ

attribute [aesop safe 5 forward]
  Tilde.Subclosed.tilde_closed
  Arrow.Subclosed.arrow_closed
  Wedge.Subclosed.wedge_closed
  Vee.Subclosed.vee_closed

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.LogicalConnective.Subclosed [LogicalConnective F] (C : F → Prop) extends
  toTildeSubclosed : Tilde.Subclosed C,
  toArrowSubclosed : Arrow.Subclosed C,
  toWedgeSubclosed : Wedge.Subclosed C,
  toVeeSubclosed : Vee.Subclosed C

end «lp_section_3»

section «lp_section_4»

variable {α β : Type*} [LogicalConnective α] [LogicalConnective β]

/-- Imported declaration from the Incompleteness formalization. -/
def conjLt (φ : ℕ → α) : ℕ → α
  | 0     => ⊤
  | k + 1 => φ k ⋏ conjLt φ k

@[simp] lemma conjLt_zero (φ : ℕ → α) : conjLt φ 0 = ⊤ := rfl

@[simp] lemma conjLt_succ (φ : ℕ → α) (k) : conjLt φ (k + 1) = φ k ⋏ conjLt φ k := rfl

@[simp] lemma hom_conj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (φ :
    ℕ → α) :
    f (conjLt φ k) ↔ ∀ i < k, f (φ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [conjLt_succ, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
      ih]
    constructor
    · rintro ⟨hk, h⟩
      intro i hi
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with (rfl | hi)
      · exact hk
      · exact h i hi
    · rintro h
      exact ⟨h k (by simp), fun i hi ↦ h i (Nat.lt_add_right 1 hi)⟩

/-- Imported declaration from the Incompleteness formalization. -/
def disjLt (φ : ℕ → α) : ℕ → α
  | 0     => ⊥
  | k + 1 => φ k ⋎ disjLt φ k

@[simp] lemma disjLt_zero (φ : ℕ → α) : disjLt φ 0 = ⊥ := rfl

@[simp] lemma disjLt_succ (φ : ℕ → α) (k) : disjLt φ (k + 1) = φ k ⋎ disjLt φ k := rfl

@[simp] lemma hom_disj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (φ :
    ℕ → α) :
    f (disjLt φ k) ↔ ∃ i < k, f (φ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [disjLt_succ, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨k, by simp, h⟩
      · exact ⟨i, Nat.lt_add_right 1 hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with (rfl | hi)
      · left; exact h
      · right; exact ⟨i, hi, h⟩

end «lp_section_4»

end LO

open LO

namespace Matrix

section «lp_section_5»

variable {α : Type*}
variable [LogicalConnective α] [LogicalConnective β]

/-- Imported declaration from the Incompleteness formalization. -/
def conjVec : {n : ℕ} → (Fin n → α) → α
  | 0,     _ => ⊤
  | _ + 1, v => v 0 ⋏ conjVec (vecTail v)

@[simp] lemma conj_nil (v : Fin 0 → α) : conjVec v = ⊤ := rfl

@[simp] lemma conj_cons {a : α} {v : Fin n → α} : conjVec (a :> v) = a ⋏ conjVec v := rfl

@[simp] lemma conj_hom_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
  (f : F) (v : Fin n → α) : f (conjVec v) = ∀ i, f (v i) := by
  induction n with
  | zero => simp [conjVec]
  | succ n ih =>
    simp only [conjVec, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
      eq_iff_iff]
    rw [ih]
    constructor
    · intro ⟨hz, hs⟩ i; cases i using Fin.cases; { exact hz }; { exact hs _ }
    · intro h; exact ⟨h 0, fun i => h _⟩

lemma hom_conj [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) :
    f (conjVec v) = conjVec (f ∘ v) := by
  induction n with
  | zero => simp only [conjVec, LogicalConnective.HomClass.map_top]
  | succ n ih => simp [ih, conjVec, Matrix.vecTail_comp]

lemma hom_conj₂ [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) :
    f (conjVec v) = conjVec fun i => f (v i) :=
  hom_conj f v

/-- Imported declaration from the Incompleteness formalization. -/
def disj : {n : ℕ} → (Fin n → α) → α
  | 0,     _ => ⊥
  | _ + 1, v => v 0 ⋎ disj (vecTail v)

@[simp] lemma disj_nil (v : Fin 0 → α) : disj v = ⊥ := rfl

@[simp] lemma disj_cons {a : α} {v : Fin n → α} : disj (a :> v) = a ⋎ disj v := rfl

@[simp] lemma disj_hom_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
  (f : F) (v : Fin n → α) : f (disj v) = ∃ i, f (v i) := by
  induction n with
  | zero => simp [disj]
  | succ n ih =>
    simp only [disj, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
      eq_iff_iff]
    rw [ih]
    constructor
    · rintro (H | ⟨i, H⟩); { exact ⟨0, H⟩ }; { exact ⟨i.succ, H⟩ }
    · rintro ⟨i, h⟩
      cases i using Fin.cases; { left; exact h }; { right; exact ⟨_, h⟩ }

lemma hom_disj [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) :
    f (disj v) = disj (f ∘ v) := by
  induction n with
  | zero => simp only [disj, LogicalConnective.HomClass.map_bot]
  | succ n ih => simp [ih, disj, Matrix.vecTail_comp]

lemma hom_disj' [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) :
    f (disj v) = disj fun i => f (v i) :=
  hom_disj f v

end «lp_section_5»

end Matrix

namespace List

section «lp_section_6»

variable {α : Type*} [LogicalConnective α]

/-- Imported declaration from the Incompleteness formalization. -/
def conj : List α → α
  | []      => ⊤
  | a :: as => a ⋏ as.conj

@[simp] lemma conj_nil : conj (α := α) [] = ⊤ := rfl

@[simp] lemma conj_cons {a : α} {as : List α} : conj (a :: as) = a ⋏ as.conj := rfl

lemma map_conj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l : List α) :
    f l.conj ↔ ∀ a ∈ l, f a := by
  induction l <;> simp[*]

lemma map_conj_append [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l₁ l₂ :
    List α) :
    f (l₁ ++ l₂).conj ↔ f (l₁.conj ⋏ l₂.conj) := by
  induction l₁ <;> induction l₂ <;> aesop;

/-- Imported declaration from the Incompleteness formalization. -/
def disj : List α → α
  | []      => ⊥
  | a :: as => a ⋎ as.disj

@[simp] lemma disj_nil : disj (α := α) [] = ⊥ := rfl

@[simp] lemma disj_cons {a : α} {as : List α} : disj (a :: as) = a ⋎ as.disj := rfl

lemma map_disj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l : List α) :
    f l.disj ↔ ∃ a ∈ l, f a := by
  induction l <;> simp[*]

lemma map_disj_append [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l₁ l₂ :
    List α) :
    f (l₁ ++ l₂).disj ↔ f (l₁.disj ⋎ l₂.disj) := by
  induction l₁ <;> induction l₂ <;> aesop;

end «lp_section_6»

section «lp_section_7»

variable {F : Type u} [LogicalConnective F]
variable {φ ψ : F}

/-- Remark: `[φ].conj₂ = φ ≠ φ ⋏ ⊤ = [φ].conj` -/
def conj₂ : List F → F
| [] => ⊤
| [φ] => φ
| φ :: ψ :: rs => φ ⋏ (ψ :: rs).conj₂

/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "⋀" => List.conj₂

@[simp] lemma conj₂_nil : ⋀[] = (⊤ : F) := rfl

@[simp] lemma conj₂_singleton : ⋀[φ] = φ := rfl

@[simp] lemma conj₂_doubleton : ⋀[φ, ψ] = φ ⋏ ψ := rfl

@[simp] lemma conj₂_cons_nonempty {a : F} {as : List F} (h : as ≠ [] := by assumption) :
    ⋀(a :: as) = a ⋏ ⋀as := by
  cases as with
  | nil => contradiction;
  | cons ψ rs => simp [List.conj₂]

/-- Remark: `[φ].disj = φ ≠ φ ⋎ ⊥ = [φ].disj` -/
def disj₂ : List F → F
| [] => ⊥
| [φ] => φ
| φ :: ψ :: rs => φ ⋎ (ψ :: rs).disj₂

/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "⋁" => disj₂

@[simp] lemma disj₂_nil : ⋁[] = (⊥ : F) := rfl

@[simp] lemma disj₂_singleton : ⋁[φ] = φ := rfl

@[simp] lemma disj₂_doubleton : ⋁[φ, ψ] = φ ⋎ ψ := rfl

@[simp] lemma disj₂_cons_nonempty {a : F} {as : List F} (h : as ≠ [] := by assumption) :
    ⋁(a :: as) = a ⋎ ⋁as := by
  cases as with
  | nil => contradiction;
  | cons ψ rs => simp [disj₂]

end «lp_section_7»

end List

namespace Finset

section «lp_section_8»

variable [LogicalConnective α]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def conj (s : Finset α) : α := s.toList.conj

lemma map_conj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (s : Finset α) :
    f s.conj ↔ ∀ a ∈ s, f a := by
  simpa [conj] using List.map_conj f s.toList

lemma map_conj_union [DecidableEq α] [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
    (f : F) (s₁ s₂ : Finset α) : f (s₁ ∪ s₂).conj ↔ f (s₁.conj ⋏ s₂.conj) := by
  simp only [Finset.mem_union, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    map_conj]
  aesop

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def disj (s : Finset α) : α := s.toList.disj

lemma map_disj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (s : Finset α) :
    f s.disj ↔ ∃ a ∈ s, f a := by
  simpa [disj] using List.map_disj f s.toList

lemma map_disj_union [DecidableEq α] [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
    (f : F) (s₁ s₂ : Finset α) : f (s₁ ∪ s₂).disj ↔ f (s₁.disj ⋎ s₂.disj) := by
  simp only [Finset.mem_union, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    map_disj]
  aesop

end «lp_section_8»

end Finset
