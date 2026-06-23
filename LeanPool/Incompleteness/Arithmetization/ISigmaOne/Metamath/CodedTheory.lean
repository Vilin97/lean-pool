/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Coding
import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Proof.Typed
import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.PeanoMinus

/-! # CodedTheory -/


namespace LO
namespace FirstOrder
namespace Theory

@[simp] lemma mem_add_iff {T U : Theory L} {φ} : φ ∈ T + U ↔ φ ∈ T ∨ φ ∈ U := by simp [add_def]

end Theory
end FirstOrder
end LO

namespace LO
namespace FirstOrder
namespace Semiformula

variable {L : Language}

variable {M : Type*} [Structure L M]

/-- Imported declaration from the Incompleteness formalization. -/
def curve (σ : Semisentence L 1) : Set M := {x | M ⊧/![x] σ}

variable {σ π : Semisentence L 1}

lemma curve_mem_left {x : M} (hx : x ∈ σ.curve) :
    x ∈ (σ ⋎ π).curve := by
  rw [curve]
  exact Or.inl hx

lemma curve_mem_right {x : M} (hx : x ∈ π.curve) :
    x ∈ (σ ⋎ π).curve := by
  rw [curve]
  exact Or.inr hx

end Semiformula
end FirstOrder
end LO

namespace LO
namespace FirstOrder
namespace Theory

open LO.Arith

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) →
  Encodable (L.Rel k)] [DefinableLanguage L]

/-- Imported declaration from the Incompleteness formalization. -/
class Delta1Definable (T : Theory L) extends Arith.LDef.TDef L.lDef where
  mem_iff {φ} : ℕ ⊧/![⌜φ⌝] ch.val ↔ φ ∈ T
  isDelta1 : ch.ProvablyProperOn 𝐈Sg1

/-- Imported declaration from the Incompleteness formalization. -/
def tDef (T : Theory L) [d : T.Delta1Definable] : L.lDef.TDef := d.toTDef

@[simp] lemma _root_.LO.FirstOrder.Theory.Delta1Definable.mem_iff' (T : Theory L) [d :
    T.Delta1Definable] :
    ℕ ⊧/![⌜φ⌝] T.tDef.ch.val ↔ φ ∈ T := d.mem_iff

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {T : Theory L} [T.Delta1Definable]

variable (T V)

/-- Imported declaration from the Incompleteness formalization. -/
def codeIn : (L.codeIn V).Theory where
  set := T.tDef.ch.val.curve

@[simp] lemma properOn : T.tDef.ch.ProperOn V :=
  (LO.FirstOrder.Theory.Delta1Definable.isDelta1 (T := T)).properOn V

variable {T V}

@[simp] lemma mem_codeIn_iff {σ} : ⌜σ⌝ ∈ T.codeIn V ↔ σ ∈ T :=
  have : V ⊧/![⌜σ⌝] T.tDef.ch.val ↔ ℕ ⊧/![⌜σ⌝] T.tDef.ch.val := by
    simpa [coe_quote, Matrix.constant_eq_singleton] using
      FirstOrder.Arith.models_iff_of_Delta1 (V :=
      V) (σ := T.tDef.ch) (by simp) (by simp) (e := ![⌜σ⌝])
  Iff.trans this Theory.Delta1Definable.mem_iff

instance tDef_defined : (T.codeIn V).Defined T.tDef where
  defined := ⟨by
    intro v
    rw [show v = ![v 0] from Matrix.constant_eq_singleton']
    have :=
      (consequence_iff (T := 𝐈Sg1)).mp (sound! <|
          FirstOrder.Theory.Delta1Definable.isDelta1 (T := T)) V inferInstance
    simp [models_iff] at this ⊢
    simp [Theory.tDef, this, Matrix.constant_eq_singleton],
  by intro v; simp [FirstOrder.Semiformula.curve, Theory.codeIn, ←Matrix.constant_eq_singleton']⟩

variable (T V)

/-- Imported declaration from the Incompleteness formalization. -/
def tCodeIn (T : Theory L) [T.Delta1Definable] : (L.codeIn V).TTheory where
  thy := T.codeIn V
  pthy := T.tDef

variable {T V}

variable {U : Theory L}

namespace Delta1Definable

open Arith.HierarchySymbol.Semiformula LO.FirstOrder.Theory

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def add (dT : T.Delta1Definable) (dU : U.Delta1Definable) : (T + U).Delta1Definable where
  ch := T.tDef.ch ⋎ U.tDef.ch
  mem_iff {φ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ ProperOn.or (by simp) (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def ofEq (dT : T.Delta1Definable) (h : T = U) : U.Delta1Definable where
  ch := dT.ch
  mem_iff := by rcases h; exact dT.mem_iff
  isDelta1 := by rcases h; exact dT.isDelta1

omit [V ⊧ₘ* 𝐈Sg1] [T.Delta1Definable] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma add_subset_left (dT : T.Delta1Definable) (dU : U.Delta1Definable) :
    haveI := dT.add dU
    T.codeIn V ⊆ (T + U).codeIn V := by
  intro p hp
  apply FirstOrder.Semiformula.curve_mem_left
  simp only [val_sigma] at hp ⊢; exact hp

omit [V ⊧ₘ* 𝐈Sg1] [T.Delta1Definable] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma add_subset_right (dT : T.Delta1Definable) (dU : U.Delta1Definable) :
    haveI := dT.add dU
    U.codeIn V ⊆ (T + U).codeIn V := by
  intro p hp
  apply FirstOrder.Semiformula.curve_mem_right
  simp only [val_sigma] at hp ⊢; exact hp

instance empty : Theory.Delta1Definable (∅ : Theory L) where
  ch := ⊥
  mem_iff {ψ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

/-! memo: This noncomputable is *not* essetial. -/
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
noncomputable
def singleton (φ : SyntacticFormula L) : Theory.Delta1Definable {φ} where
  ch := .ofZero (.mkSigma “x. x = ↑⌜φ⌝” (by simp)) _
  mem_iff {ψ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

@[simp] lemma singleton_toTDef_ch_val (φ : FirstOrder.SyntacticFormula L) :
    letI := Delta1Definable.singleton φ
    (FirstOrder.Theory.Delta1Definable.toTDef {φ}).ch.val = “x. x = ↑⌜φ⌝” := rfl

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
noncomputable
def ofList (l : List (SyntacticFormula L)) : Delta1Definable {φ | φ ∈ l} :=
  match l with
  |     [] => empty.ofEq (by ext; simp)
  | φ :: l => ((singleton φ).add (ofList l)).ofEq (by ext; simp)

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
noncomputable
def ofFinite (T : Theory L) (h : Set.Finite T) : T.Delta1Definable :=
  (ofList h.toFinset.toList).ofEq (by ext; simp)

end Delta1Definable

end Theory
end FirstOrder
end LO
