/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.LogicSymbol

/-! # Quantifier -/



namespace LO

/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class SigmaSymbol (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  sigma : α

/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class PiSymbol (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  pi : α

/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class DeltaSymbol (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  delta : α

/-- Imported declaration from the Incompleteness formalization. -/
notation "Sg" => SigmaSymbol.sigma

/-- Imported declaration from the Incompleteness formalization. -/
notation "Pg" => PiSymbol.pi

/-- Imported declaration from the Incompleteness formalization. -/
notation "Dlt" => DeltaSymbol.delta

attribute [match_pattern] SigmaSymbol.sigma PiSymbol.pi DeltaSymbol.delta

/-- Imported declaration from the Incompleteness formalization. -/
inductive Polarity where
  | sigma
  | pi

namespace Polarity

instance : SigmaSymbol Polarity := ⟨sigma⟩

instance : PiSymbol Polarity := ⟨pi⟩

/-- Imported declaration from the Incompleteness formalization. -/
def alt : Polarity → Polarity
  | Sg => Pg
  | Pg => Sg

lemma eq_sigma : sigma = Sg := rfl

lemma eq_pi : pi = Pg := rfl

@[simp] lemma alt_sigma : alt Sg = Pg := rfl

@[simp] lemma alt_pi : alt Pg = Sg := rfl

@[simp] lemma alt_alt (Γ : Polarity) : Γ.alt.alt = Γ := by
  rcases Γ <;> rfl

end Polarity

/-- Imported declaration from the Incompleteness formalization. -/
inductive SigmaPiDelta where | sigma | pi | delta

namespace SigmaPiDelta

instance : SigmaSymbol SigmaPiDelta := ⟨sigma⟩

instance : PiSymbol SigmaPiDelta := ⟨pi⟩

instance : DeltaSymbol SigmaPiDelta := ⟨delta⟩

/-- Imported declaration from the Incompleteness formalization. -/
def alt : SigmaPiDelta → SigmaPiDelta
  | Sg => Pg
  | Pg => Sg
  | Dlt => Dlt

lemma eq_sigma : sigma = Sg := rfl

lemma eq_pi : pi = Pg := rfl

lemma eq_delta : delta = Dlt := rfl

@[simp] lemma alt_sigma : alt Sg = Pg := rfl

@[simp] lemma alt_pi : alt Pg = Sg := rfl

@[simp] lemma alt_delta : alt Dlt = Dlt := rfl

@[simp] lemma alt_alt (Γ : SigmaPiDelta) : Γ.alt.alt = Γ := by
  rcases Γ <;> rfl

end SigmaPiDelta

/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class UnivQuantifier (α : ℕ → Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  univ : ∀ {n}, α (n + 1) → α n

/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class ExQuantifier (α : ℕ → Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ex : ∀ {n}, α (n + 1) → α n

/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∀' " => UnivQuantifier.univ

/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∃' " => ExQuantifier.ex

attribute [match_pattern]
  UnivQuantifier.univ
  ExQuantifier.ex

/-- Imported declaration from the Incompleteness formalization. -/
class Quantifier (α : ℕ → Type*) extends UnivQuantifier α, ExQuantifier α

/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → Type*) extends Quantifier α where
  /-- Imported declaration from the Incompleteness formalization. -/
  connectives : (n : ℕ) → LogicalConnective (α n)

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalConnective (α n) := LCWQ.connectives n

instance (α : ℕ → Type*) [Quantifier α] [(n : ℕ) → LogicalConnective (α n)] : LCWQ α where
  connectives := inferInstance

section «lp_section_1»

variable {α : ℕ → Type*} [UnivQuantifier α] [ExQuantifier α]

/-- Imported declaration from the Incompleteness formalization. -/
def quant : Polarity → α (n + 1) → α n
  | Sg, φ => ∃' φ
  | Pg, φ => ∀' φ

@[simp] lemma quant_sigma (φ : α (n + 1)) : quant Sg φ = ∃' φ := rfl

@[simp] lemma quant_pi (φ : α (n + 1)) : quant Pg φ = ∀' φ := rfl

end «lp_section_1»

section «lp_section_2»

variable {α : ℕ → Type*} [UnivQuantifier α]

/-- Imported declaration from the Incompleteness formalization. -/
def univClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => univClosure (∀' a)

/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∀* " => univClosure

@[simp] lemma univClosure_zero (a : α 0) : ∀* a = a := rfl

lemma univClosure_succ {n} (a : α (n + 1)) : ∀* a = ∀* ∀' a := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def univItr : (k : ℕ) → α (n + k) → α n
  | 0,     a => a
  | k + 1, a => univItr k (∀' a)

/-- Imported declaration from the Incompleteness formalization. -/
notation "∀^[" k "] " φ:64 => univItr k φ

@[simp] lemma univItr_zero (a : α n) : ∀^[0] a = a := rfl

@[simp] lemma univItr_one (a : α (n + 1)) : ∀^[1] a = ∀' a := rfl

lemma univItr_succ {k} (a : α (n + (k + 1))) : ∀^[k + 1] a = ∀^[k] (∀' a) := rfl

end «lp_section_2»

section «lp_section_3»

variable {α : ℕ → Type*} [ExQuantifier α]

/-- Imported declaration from the Incompleteness formalization. -/
def exClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => exClosure (∃' a)

/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∃* " => exClosure

@[simp] lemma exClosure_zero (a : α 0) : ∃* a = a := rfl

lemma exClosure_succ {n} (a : α (n + 1)) : ∃* a = ∃* ∃' a := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def exItr : (k : ℕ) → α (n + k) → α n
  | 0,     a => a
  | k + 1, a => exItr k (∃' a)

/-- Imported declaration from the Incompleteness formalization. -/
notation "∃^[" k "] " φ:64 => exItr k φ

@[simp] lemma exItr_zero (a : α n) : ∃^[0] a = a := rfl

@[simp] lemma exItr_one (a : α (n + 1)) : ∃^[1] a = ∃' a := rfl

lemma exItr_succ {k} (a : α (n + (k + 1))) : ∃^[k + 1] a = ∃^[k] (∃' a) := rfl

end «lp_section_3»

section «lp_section_4»

variable {α : ℕ → Type*}

/-- Imported declaration from the Incompleteness formalization. -/
def ball [UnivQuantifier α] [Arrow (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) :
    α n :=
  ∀' (φ ==> ψ)

/-- Imported declaration from the Incompleteness formalization. -/
def bex [ExQuantifier α] [Wedge (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∃' (φ ⋏ ψ)

/-- Imported declaration from the Incompleteness formalization. -/
notation:64 "∀[" φ "] " ψ => ball φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
notation:64 "∃[" φ "] " ψ => bex φ ψ

end «lp_section_4»

end LO
