/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.Vorspiel.Lemmata
import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.StrictHierarchy

/-!

# Arithmetical Formula Sorted by Arithmetical Hierarchy

This file defines the $\Sigma_n / \Pi_n / \Delta_n$ formulas of arithmetic of first-order logic.

- `Sg-[m].Semiformula ξ n` is a `Semiformula ℒₒᵣ ξ n` which is `Sg-[m]`.
- `Pg-[m].Semiformula ξ n` is a `Semiformula ℒₒᵣ ξ n` which is `Pg-[m]`.
- `Dlt-[m].Semiformula ξ n` is a pair of `Sg-[m].Semiformula ξ n` and `Pg-[m].Semiformula ξ n`.
- `ProperOn` : `φ.ProperOn M` iff `φ`'s two element `φ.sigma` and `φ.pi` are equivalent on model
  `M`.

-/

namespace LO
namespace FirstOrder
namespace Arith

/-- Imported declaration from the Incompleteness formalization. -/
structure HierarchySymbol where
  /-- Imported declaration from the Incompleteness formalization. -/
  Γ : SigmaPiDelta
  /-- Imported declaration from the Incompleteness formalization. -/
  rank : ℕ

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation:max Γ:max "-[" n "]" => HierarchySymbol.mk Γ n

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.sigmaZero : HierarchySymbol := Sg-[0]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.piZero : HierarchySymbol := Pg-[0]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.deltaZero : HierarchySymbol := Dlt-[0]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.sigmaOne : HierarchySymbol := Sg-[1]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.piOne : HierarchySymbol := Pg-[1]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.HierarchySymbol.deltaOne : HierarchySymbol := Dlt-[1]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Sg0 : HierarchySymbol := HierarchySymbol.sigmaZero

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Pg0 : HierarchySymbol := HierarchySymbol.piZero

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Dlt0 : HierarchySymbol := HierarchySymbol.deltaZero

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Sg1 : HierarchySymbol := HierarchySymbol.sigmaOne

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Pg1 : HierarchySymbol := HierarchySymbol.piOne

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Dlt1 : HierarchySymbol := HierarchySymbol.deltaOne

namespace HierarchySymbol

variable (ξ : Type*) (n : ℕ)

/-- Imported declaration from the Incompleteness formalization. -/
protected inductive Semiformula : HierarchySymbol → Type _ where
  | mkSigma {m} : (φ : Semiformula ℒₒᵣ ξ n) → Hierarchy Sg m φ → Sg-[m].Semiformula
  | mkPi {m}    : (φ : Semiformula ℒₒᵣ ξ n) → Hierarchy Pg m φ → Pg-[m].Semiformula
  | mkDelta {m} : Sg-[m].Semiformula → Pg-[m].Semiformula → Dlt-[m].Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Semisentence (Γ : HierarchySymbol) (n : ℕ) := Γ.Semiformula Empty n

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Sentence (Γ : HierarchySymbol) := Γ.Semiformula Empty 0

variable {Γ : HierarchySymbol}

variable {ξ n}

namespace Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
def val {Γ : HierarchySymbol} : Γ.Semiformula ξ n → Semiformula ℒₒᵣ ξ n
  | mkSigma φ _ => φ
  | mkPi    φ _ => φ
  | mkDelta φ _ => φ.val

@[simp] lemma val_mkSigma (φ : Semiformula ℒₒᵣ ξ n) (hp : Hierarchy Sg m φ) :
    (mkSigma φ hp).val = φ :=
  rfl

@[simp] lemma val_mkPi (φ : Semiformula ℒₒᵣ ξ n) (hp : Hierarchy Pg m φ) :
    (mkPi φ hp).val = φ :=
  rfl

@[simp] lemma val_mkDelta (φ : Sg-[m].Semiformula ξ n) (ψ : Pg-[m].Semiformula ξ n) :
    (mkDelta φ ψ).val = φ.val :=
  rfl

instance : Coe (Sg0.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩
instance : Coe (Pg0.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩
instance : Coe (Dlt0.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩

instance : Coe (Sg1.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩
instance : Coe (Pg1.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩
instance : Coe (Dlt1.Semisentence n) (Semisentence ℒₒᵣ n) := ⟨Semiformula.val⟩

lemma sigma_prop : (φ : Sg-[m].Semiformula ξ n) → Hierarchy Sg m φ.val
  | mkSigma _ h => h

lemma pi_prop : (φ : Pg-[m].Semiformula ξ n) → Hierarchy Pg m φ.val
  | mkPi _ h => h

@[simp] lemma polarity_prop : {Γ : Polarity} → (φ : Γ-[m].Semiformula ξ n) → Hierarchy Γ m φ.val
  | Sg, φ => φ.sigma_prop
  | Pg, φ => φ.pi_prop

/-- Imported declaration from the Incompleteness formalization. -/
def sigma : Dlt-[m].Semiformula ξ n → Sg-[m].Semiformula ξ n
  | mkDelta φ _ => φ

@[simp] lemma sigma_mkDelta (φ : Sg-[m].Semiformula ξ n) (ψ : Pg-[m].Semiformula ξ n) :
    (mkDelta φ ψ).sigma = φ :=
  rfl

/-- Imported declaration from the Incompleteness formalization. -/
def pi : Dlt-[m].Semiformula ξ n → Pg-[m].Semiformula ξ n
  | mkDelta _ φ => φ

@[simp] lemma pi_mkDelta (φ : Sg-[m].Semiformula ξ n) (ψ : Pg-[m].Semiformula ξ n) :
    (mkDelta φ ψ).pi = ψ :=
  rfl

lemma val_sigma (φ : Dlt-[m].Semiformula ξ n) : φ.sigma.val = φ.val := by rcases φ; simp

/-- Imported declaration from the Incompleteness formalization. -/
def mkPolarity (φ : Semiformula ℒₒᵣ ξ n) : (Γ : Polarity) → Hierarchy Γ m φ → Γ-[m].Semiformula ξ n
  | Sg, h => mkSigma φ h
  | Pg, h => mkPi φ h

@[simp] lemma val_mkPolarity (φ : Semiformula ℒₒᵣ ξ n) {Γ} (h : Hierarchy Γ m φ) :
    (mkPolarity φ Γ h).val = φ := by
  cases Γ <;> rfl

@[simp] lemma hierarchy_sigma (φ : Sg-[m].Semiformula ξ n) : Hierarchy Sg m φ.val := φ.sigma_prop

@[simp] lemma hierarchy_pi (φ : Pg-[m].Semiformula ξ n) : Hierarchy Pg m φ.val := φ.pi_prop

@[simp] lemma hierarchy_zero {Γ Γ' m} (φ : Γ-[0].Semiformula ξ n) : Hierarchy Γ' m φ.val := by
  cases Γ
  · exact Hierarchy.of_zero φ.sigma_prop
  · exact Hierarchy.of_zero φ.pi_prop
  · cases φ
    simp only [val_mkDelta]; exact Hierarchy.of_zero (sigma_prop _)

variable {M : Type*} [ORingStruc M]

variable (M)

/-- Imported declaration from the Incompleteness formalization. -/
def ProperOn (φ : Dlt-[m].Semisentence n) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalbm M e φ.sigma.val ↔ Semiformula.Evalbm M e φ.pi.val

/-- Imported declaration from the Incompleteness formalization. -/
def ProperWithParamOn (φ : Dlt-[m].Semiformula M n) : Prop :=
  ∀ (e : Fin n → M), Semiformula.Evalm M e id φ.sigma.val ↔ Semiformula.Evalm M e id φ.pi.val

/-- Imported declaration from the Incompleteness formalization. -/
def ProvablyProperOn (φ : Dlt-[m].Semisentence n) (T : Theory ℒₒᵣ) : Prop :=
  T ⊢!. ∀* “!φ.sigma.val ⋯ ↔ !φ.pi.val ⋯”

variable {M}

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.iff {φ :
    Dlt-[m].Semisentence n}
    (h : φ.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e φ.sigma.val ↔ Semiformula.Evalbm M e φ.pi.val := h e

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.iff {φ :
    Dlt-[m].Semiformula M n}
    (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id φ.sigma.val ↔ Semiformula.Evalm (L := ℒₒᵣ) M e id φ.pi.val := h e

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.iff' {φ :
    Dlt-[m].Semisentence n}
    (h : φ.ProperOn M) (e : Fin n → M) :
    Semiformula.Evalbm M e φ.pi.val ↔ Semiformula.Evalbm M e φ.val := by simp [←h.iff, val_sigma]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.iff' {φ :
    Dlt-[m].Semiformula M n}
    (h : φ.ProperWithParamOn M) (e : Fin n → M) :
    Semiformula.Evalm M e id φ.pi.val ↔ Semiformula.Evalm (L := ℒₒᵣ) M e id φ.val := by
      simp [←h.iff, val_sigma]

section «lp_section_1»

variable (T : Theory ℒₒᵣ)

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn
    [𝐄𝐐 wkn T] {φ :
    Dlt-[m].Semisentence n}
    (h : ∀ (M : Type w) [ORingStruc M] [M ⊧ₘ* T], φ.ProperOn M) : φ.ProvablyProperOn T := by
  apply complete (T := T) <| FirstOrder.Arith.oRing_consequence_of.{w} T _ ?_
  intro M _ _
  simpa [models_iff] using (h M).iff

variable {T}

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProvablyProperOn.properOn
    {φ : Dlt-[m].Semisentence n} (h : φ.ProvablyProperOn T)
    (M : Type w) [ORingStruc M] [M ⊧ₘ* T] : φ.ProperOn M := by
  intro v
  have := by simpa [models_iff] using consequence_iff.mp (sound! (T := T) h) M inferInstance
  exact this v

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
def rew (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) : {Γ :
    HierarchySymbol} → Γ.Semiformula ξ₁ n₁ → Γ.Semiformula ξ₂ n₂
  | Sg-[_], mkSigma φ hp => mkSigma (ω ▹ φ) (by simpa using hp)
  | Pg-[_], mkPi φ hp    => mkPi (ω ▹ φ) (by simpa using hp)
  | Dlt-[_], mkDelta φ ψ  => mkDelta (φ.rew ω) (ψ.rew ω)

@[simp] lemma val_rew (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) {Γ : HierarchySymbol} (φ : Γ.Semiformula ξ₁ n₁) :
    (φ.rew ω).val = ω ▹ φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases φ with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew]

@[simp] lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.rew
    {φ : Dlt-[m].Semisentence n₁} (h : φ.ProperOn M) (ω :
    Rew ℒₒᵣ Empty n₁ Empty n₂) :
    (φ.rew ω).ProperOn M := by
  rcases φ
  simp only [Semiformula.ProperOn, Semiformula.rew, Semiformula.sigma_mkDelta,
    Semiformula.val_rew, Semiformula.eval_rew, Empty.eq_elim, Semiformula.pi_mkDelta]
  intro e; exact h.iff _

@[simp] lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.rew'
    {φ : Dlt-[m].Semisentence n₁} (h : φ.ProperOn M) (ω :
    Rew ℒₒᵣ Empty n₁ M n₂) :
    (φ.rew ω).ProperWithParamOn M := by
  rcases φ; intro e; simp [Semiformula.rew, Semiformula.eval_rew, Empty.eq_elim]
  simpa using h.iff _

@[simp] lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.rew {φ :
    Dlt-[m].Semiformula M n₁}
    (h : φ.ProperWithParamOn M) (f : Fin n₁ →
        Semiterm ℒₒᵣ M n₂) : (φ.rew (Rew.substs f)).ProperWithParamOn M := by
  rcases φ; intro e;
  simp only [Semiformula.rew, Semiformula.sigma_mkDelta, Semiformula.val_rew,
    Semiformula.eval_rew, Semiformula.pi_mkDelta]
  exact h.iff _

/-- Imported declaration from the Incompleteness formalization. -/
def emb : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | Sg-[_], mkSigma φ hp => mkSigma (Semiformula.lMap Language.oringEmb φ) (Hierarchy.oringEmb hp)
  | Pg-[_], mkPi φ hp    => mkPi (Semiformula.lMap Language.oringEmb φ) (Hierarchy.oringEmb hp)
  | Dlt-[_], mkDelta φ ψ  => mkDelta φ.emb ψ.emb

@[simp] lemma val_emb {Γ : HierarchySymbol} (φ : Γ.Semiformula ξ n) :
    φ.emb.val = Semiformula.lMap Language.oringEmb φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases φ with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [val, emb]

@[simp] lemma pi_emb (φ : Dlt-[m].Semiformula ξ n) : φ.emb.pi = φ.pi.emb := by cases φ; rfl

@[simp] lemma sigma_emb (φ : Dlt-[m].Semiformula ξ n) : φ.emb.sigma = φ.sigma.emb := by cases φ; rfl

@[simp] lemma emb_proper (φ : Dlt-[m].Semisentence n) : φ.emb.ProperOn M ↔ φ.ProperOn M := by
  rcases φ; simp [ProperOn, emb]

@[simp] lemma emb_properWithParam (φ : Dlt-[m].Semiformula M n) :
    φ.emb.ProperWithParamOn M ↔ φ.ProperWithParamOn M := by
  rcases φ; simp [ProperWithParamOn, emb]

/-- Imported declaration from the Incompleteness formalization. -/
def extd {Γ : HierarchySymbol} : Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | mkSigma φ hp => mkSigma (Semiformula.lMap Language.oringEmb φ) (Hierarchy.oringEmb hp)
  | mkPi φ hp    => mkPi (Semiformula.lMap Language.oringEmb φ) (Hierarchy.oringEmb hp)
  | mkDelta φ ψ  => mkDelta φ.extd ψ.extd

@[simp]
lemma eval_extd_iff {e ε} {φ : Γ.Semiformula ξ n} :
    Semiformula.Evalm M e ε φ.extd.val ↔ Semiformula.Evalm M e ε φ.val := by
  induction φ <;> simp [extd, *]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.extd
    {φ : Dlt-[m].Semisentence n} (h :
    φ.ProperOn M) :
    φ.extd.ProperOn M := by
  intro e; rcases φ; simpa [Semiformula.extd] using h.iff e

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.extd
    {φ : Dlt-[m].Semisentence n} (h :
    φ.ProperOn M) :
    φ.extd.ProperOn M := by
  intro e; rcases φ; simpa [Semiformula.extd] using h.iff e

lemma sigma_extd_val (φ : Sg-[m].Semiformula ξ n) :
    φ.extd.val = Semiformula.lMap Language.oringEmb φ.val := by
  rcases φ; simp [extd]

lemma pi_extd_val (φ : Pg-[m].Semiformula ξ n) :
    φ.extd.val = Semiformula.lMap Language.oringEmb φ.val := by
  rcases φ; simp [extd]

lemma sigmaZero {Γ} (φ : Γ-[0].Semiformula ξ k) : Hierarchy Sg 0 φ.val :=
  match Γ with
  | Sg => φ.sigma_prop
  | Pg => φ.pi_prop.of_zero
  | Dlt => by simp []

/-- Imported declaration from the Incompleteness formalization. -/
def ofZero {Γ'} (φ : Γ'-[0].Semiformula ξ k) : (Γ : HierarchySymbol) → Γ.Semiformula ξ k
  | Sg-[_] => mkSigma φ.val φ.sigmaZero.of_zero
  | Pg-[_] => mkPi φ.val φ.sigmaZero.of_zero
  | Dlt-[_] => mkDelta (mkSigma φ.val φ.sigmaZero.of_zero) (mkPi φ.val φ.sigmaZero.of_zero)

/-- Imported declaration from the Incompleteness formalization. -/
def ofDeltaOne (φ : Dlt1.Semiformula ξ k) : (Γ : SigmaPiDelta) → (m : ℕ) → Γ-[m+1].Semiformula ξ k
  | Sg, m => mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))
  | Pg, m => mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp))
  | Dlt, m =>
    mkDelta (mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))) (mkPi φ.pi.val
      (φ.pi.pi_prop.mono (by simp)))

@[simp] lemma ofZero_val {Γ'} (φ : Γ'-[0].Semiformula ξ n) (Γ) : (ofZero φ Γ).val = φ.val := by
  match Γ with
  | Sg-[_] => simp [ofZero]
  | Pg-[_] => simp [ofZero]
  | Dlt-[_] => simp [ofZero]

@[simp] lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.of_zero (φ :
    Γ'-[0].Semisentence k) (m) :
    (ofZero φ Dlt-[m]).ProperOn M := by
  simp [ProperOn, ofZero]

@[simp] lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.of_zero (φ :
    Γ'-[0].Semiformula M k) (m) :
    (ofZero φ Dlt-[m]).ProperWithParamOn M := by
  simp [ProperWithParamOn, ofZero]

/-- Imported declaration from the Incompleteness formalization. -/
def verum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | Sg-[m] => mkSigma ⊤ (by simp)
  | Pg-[m] => mkPi ⊤ (by simp)
  | Dlt-[m] => mkDelta (mkSigma ⊤ (by simp)) (mkPi ⊤ (by simp))

/-- Imported declaration from the Incompleteness formalization. -/
def falsum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | Sg-[m] => mkSigma ⊥ (by simp)
  | Pg-[m] => mkPi ⊥ (by simp)
  | Dlt-[m] => mkDelta (mkSigma ⊥ (by simp)) (mkPi ⊥ (by simp))

/-- Imported declaration from the Incompleteness formalization. -/
def and : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | Sg-[m], φ, ψ => mkSigma (φ.val ⋏ ψ.val) (by simp)
  | Pg-[m], φ, ψ => mkPi (φ.val ⋏ ψ.val) (by simp)
  | Dlt-[m], φ, ψ =>
    mkDelta (mkSigma (φ.sigma.val ⋏ ψ.sigma.val) (by simp)) (mkPi (φ.pi.val ⋏ ψ.pi.val) (by simp))

/-- Imported declaration from the Incompleteness formalization. -/
def or : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | Sg-[m], φ, ψ => mkSigma (φ.val ⋎ ψ.val) (by simp)
  | Pg-[m], φ, ψ => mkPi (φ.val ⋎ ψ.val) (by simp)
  | Dlt-[m], φ, ψ =>
    mkDelta (mkSigma (φ.sigma.val ⋎ ψ.sigma.val) (by simp)) (mkPi (φ.pi.val ⋎ ψ.pi.val) (by simp))

/-- Imported declaration from the Incompleteness formalization. -/
def negSigma (φ : Sg-[m].Semiformula ξ n) : Pg-[m].Semiformula ξ n := mkPi (∼φ.val) (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def negPi (φ : Pg-[m].Semiformula ξ n) : Sg-[m].Semiformula ξ n := mkSigma (∼φ.val) (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def negDelta (φ : Dlt-[m].Semiformula ξ n) :
    Dlt-[m].Semiformula ξ n :=
  mkDelta (φ.pi.negPi) (φ.sigma.negSigma)

/-- Imported declaration from the Incompleteness formalization. -/
def ball (t : Semiterm ℒₒᵣ ξ n) : {Γ :
    HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | Sg-[m], φ => mkSigma (∀[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | Pg-[m], φ => mkPi (∀[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | Dlt-[m], φ =>
    mkDelta (mkSigma (∀[“#0 < !!(Rew.bShift t)”] φ.sigma.val) (by simp)) (mkPi (∀[“#0 <
      !!(Rew.bShift t)”] φ.pi.val) (by simp))

/-- Imported declaration from the Incompleteness formalization. -/
def bex (t : Semiterm ℒₒᵣ ξ n) : {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | Sg-[m], φ => mkSigma (∃[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | Pg-[m], φ => mkPi (∃[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | Dlt-[m], φ =>
    mkDelta (mkSigma (∃[“#0 < !!(Rew.bShift t)”] φ.sigma.val) (by simp)) (mkPi (∃[“#0 <
      !!(Rew.bShift t)”] φ.pi.val) (by simp))

/-- Imported declaration from the Incompleteness formalization. -/
def all (φ : Pg-[m + 1].Semiformula ξ (n + 1)) :
    Pg-[m + 1].Semiformula ξ n :=
  mkPi (∀' φ.val) φ.pi_prop.all

/-- Imported declaration from the Incompleteness formalization. -/
def ex (φ : Sg-[m + 1].Semiformula ξ (n + 1)) :
    Sg-[m + 1].Semiformula ξ n :=
  mkSigma (∃' φ.val) φ.sigma_prop.ex

instance : Top (Γ.Semiformula ξ n) := ⟨verum⟩

instance : Bot (Γ.Semiformula ξ n) := ⟨falsum⟩

instance : Wedge (Γ.Semiformula ξ n) := ⟨and⟩

instance : Vee (Γ.Semiformula ξ n) := ⟨or⟩

instance : Tilde (Dlt-[m].Semiformula ξ n) := ⟨negDelta⟩

instance : LogicalConnective (Dlt-[m].Semiformula ξ n) where
  arrow φ ψ := ∼φ ⋎ ψ

instance : ExQuantifier (Sg-[m + 1].Semiformula ξ) := ⟨ex⟩

instance : UnivQuantifier (Pg-[m + 1].Semiformula ξ) := ⟨all⟩

/-- Imported declaration from the Incompleteness formalization. -/
def substSigma (φ : Sg-[m + 1].Semiformula ξ 1) (F : Sg-[m + 1].Semiformula ξ (n + 1)) :
    Sg-[m + 1].Semiformula ξ n := (F ⋏ φ.rew (Rew.substs ![#0])).ex

@[simp] lemma val_verum : (⊤ : Γ.Semiformula ξ n).val = ⊤ := by
  rcases Γ with ⟨Γ, m⟩
  rcases Γ <;> rfl

@[simp] lemma sigma_verum {m} : (⊤ : Dlt-[m].Semiformula ξ n).sigma = ⊤ := by simp [Top.top, verum]

@[simp] lemma pi_verum {m} : (⊤ : Dlt-[m].Semiformula ξ n).pi = ⊤ := by simp [Top.top, verum]

@[simp] lemma val_falsum : (⊥ : Γ.Semiformula ξ n).val = ⊥ := by
  rcases Γ with ⟨Γ, m⟩
  rcases Γ <;> rfl

@[simp] lemma sigma_falsum {m} : (⊥ :
    Dlt-[m].Semiformula ξ n).sigma = ⊥ := by
  simp [Bot.bot, falsum]

@[simp] lemma pi_falsum {m} : (⊥ : Dlt-[m].Semiformula ξ n).pi = ⊥ := by simp [Bot.bot, falsum]

@[simp] lemma val_and (φ ψ : Γ.Semiformula ξ n) : (φ ⋏ ψ).val = φ.val ⋏ ψ.val := by
  suffices (φ.and ψ).val = φ.val ⋏ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [and, val, val_sigma]

@[simp] lemma sigma_and (φ ψ : Dlt-[m].Semiformula ξ n) :
    (φ ⋏ ψ).sigma = φ.sigma ⋏ ψ.sigma := by
  simp [Wedge.wedge, and]

@[simp] lemma pi_and (φ ψ : Dlt-[m].Semiformula ξ n) :
    (φ ⋏ ψ).pi = φ.pi ⋏ ψ.pi := by
  simp [Wedge.wedge, and]

@[simp] lemma val_or (φ ψ : Γ.Semiformula ξ n) : (φ ⋎ ψ).val = φ.val ⋎ ψ.val := by
  suffices (φ.or ψ).val = φ.val ⋎ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [or, val, val_sigma]

@[simp] lemma sigma_or (φ ψ : Dlt-[m].Semiformula ξ n) :
    (φ ⋎ ψ).sigma = φ.sigma ⋎ ψ.sigma := by
  simp [Vee.vee, or]

@[simp] lemma pi_or (φ ψ : Dlt-[m].Semiformula ξ n) :
    (φ ⋎ ψ).pi = φ.pi ⋎ ψ.pi := by
  simp [Vee.vee, or]

@[simp] lemma val_negSigma {m} (φ : Sg-[m].Semiformula ξ n) :
    φ.negSigma.val = ∼φ.val := by
  simp [negSigma]

@[simp] lemma val_negPi {m} (φ : Pg-[m].Semiformula ξ n) :
    φ.negPi.val = ∼φ.val := by
  simp [negPi]

lemma val_negDelta {m} (φ : Dlt-[m].Semiformula ξ n) :
    (∼φ).val = ∼φ.pi.val := by
  simp [Tilde.tilde, negDelta]

@[simp] lemma sigma_negDelta {m} (φ : Dlt-[m].Semiformula ξ n) :
    (∼φ).sigma = φ.pi.negPi := by
  simp [Tilde.tilde, negDelta]

@[simp] lemma sigma_negPi {m} (φ : Dlt-[m].Semiformula ξ n) :
    (∼φ).pi = φ.sigma.negSigma := by
  simp [Tilde.tilde, negDelta]

@[simp] lemma val_ball (t : Semiterm ℒₒᵣ ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (ball t φ).val = ∀[“#0 < !!(Rew.bShift t)”] φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [ball, val, val_sigma]

@[simp] lemma val_bex (t : Semiterm ℒₒᵣ ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (bex t φ).val = ∃[“#0 < !!(Rew.bShift t)”] φ.val := by
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [bex, val, val_sigma]

@[simp] lemma val_exSigma {m} (φ : Sg-[m + 1].Semiformula ξ (n + 1)) : (ex φ).val = ∃' φ.val := rfl

@[simp] lemma val_allPi {m} (φ : Pg-[m + 1].Semiformula ξ (n + 1)) : (all φ).val = ∀' φ.val := rfl

@[simp] lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.verum : (⊤ :
    Dlt-[m].Semisentence k).ProperOn M := by
  intro e; simp

@[simp] lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.falsum : (⊥ :
    Dlt-[m].Semisentence k).ProperOn M := by
  intro e; simp

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.and
    {φ ψ : Dlt-[m].Semisentence k} (hp : φ.ProperOn M) (hq :
    ψ.ProperOn M) :
    (φ ⋏ ψ).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.or
    {φ ψ : Dlt-[m].Semisentence k} (hp : φ.ProperOn M) (hq :
    ψ.ProperOn M) :
    (φ ⋎ ψ).ProperOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.neg
    {φ : Dlt-[m].Semisentence k} (hp :
    φ.ProperOn M) :
    (∼φ).ProperOn M := by
  intro e; simp [hp.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.eval_neg {φ :
    Dlt-[m].Semisentence k} (hp :
    φ.ProperOn M) (e) :
    Semiformula.Evalbm M e (∼φ).val ↔ ¬Semiformula.Evalbm M e φ.val := by
  simp [←val_sigma, hp.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.ball
    {t} {φ : Dlt-[m + 1].Semisentence (k + 1)} (hp :
    φ.ProperOn M) :
    (ball t φ).ProperOn M := by
  intro e; simp [Semiformula.ball, hp.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperOn.bex
    {t} {φ : Dlt-[m + 1].Semisentence (k + 1)} (hp :
    φ.ProperOn M) :
    (bex t φ).ProperOn M := by
  intro e; simp [Semiformula.bex, hp.iff]

@[simp] lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.verum : (⊤ :
    Dlt-[m].Semiformula M k).ProperWithParamOn M := by
  intro e; simp

@[simp] lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.falsum : (⊥ :
    Dlt-[m].Semiformula M k).ProperWithParamOn M := by
  intro e; simp

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.and {φ ψ :
    Dlt-[m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) : (φ ⋏ ψ).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.or {φ ψ :
    Dlt-[m].Semiformula M k}
    (hp : φ.ProperWithParamOn M) (hq : ψ.ProperWithParamOn M) : (φ ⋎ ψ).ProperWithParamOn M := by
  intro e; simp [hp.iff, hq.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.neg
    {φ : Dlt-[m].Semiformula M k} (hp :
    φ.ProperWithParamOn M) :
    (∼φ).ProperWithParamOn M := by
  intro e; simp [hp.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.eval_neg {φ :
    Dlt-[m].Semiformula M k} (hp :
    φ.ProperWithParamOn M) (e) :
    Semiformula.Evalm M e id (∼φ).val ↔ ¬Semiformula.Evalm M e id φ.val := by
  simp [←val_sigma, hp.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.ball {t} {φ :
    Dlt-[m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (ball t φ).ProperWithParamOn M := by
  intro e; simp [Semiformula.ball, hp.iff]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.Semiformula.ProperWithParamOn.bex {t} {φ :
    Dlt-[m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (bex t φ).ProperWithParamOn M := by
  intro e; simp [Semiformula.bex, hp.iff]

/-- Imported declaration from the Incompleteness formalization. -/
def graphDelta (φ : Sg-[m].Semiformula ξ (k + 1)) : Dlt-[m].Semiformula ξ (k + 1) :=
  match m with
  | 0     => φ.ofZero _
  | m + 1 => mkDelta φ (mkPi “x. ∀ y, !φ.val y ⋯ → y = x” (by simp))

@[simp] lemma graphDelta_val (φ : Sg-[m].Semiformula ξ (k + 1)) :
    φ.graphDelta.val = φ.val := by
  cases m <;> simp [graphDelta]

end Semiformula

end HierarchySymbol

end Arith
end FirstOrder
end LO
