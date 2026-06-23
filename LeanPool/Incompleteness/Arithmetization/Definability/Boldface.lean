/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.Definability.Hierarchy
import LeanPool.Incompleteness.Arithmetization.Vorspiel.Graph

/-! # Boldface -/


namespace LO
namespace FirstOrder
namespace Arith

end Arith

/-- Imported declaration from the Incompleteness formalization. -/
def Defined {k} (R : (Fin k → V) → Prop) [Structure L V] (φ : Semisentence L k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalbm V v φ

/-- Imported declaration from the Incompleteness formalization. -/
def DefinedWithParam {k} (R : (Fin k → V) → Prop) [Structure L V] (φ : Semiformula L V k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalm V v id φ

lemma _root_.LO.FirstOrder.Defined.iff [Structure L V] {k} {R : (Fin k → V) → Prop} {φ :
    Semisentence L k} (h :
    Defined R φ) (v) :
    Semiformula.Evalbm V v φ ↔ R v := (h v).symm

lemma _root_.LO.FirstOrder.DefinedWithParam.iff [Structure L V] {k} {R : (Fin k → V) → Prop} {φ :
    Semiformula L V k} (h :
    DefinedWithParam R φ) (v) :
    Semiformula.Evalm V v id φ ↔ R v := (h v).symm

namespace Arith
namespace HierarchySymbol

variable (ξ : Type*) (n : ℕ)

open LO.Arith

variable {V : Type*} [ORingStruc V]

/-- Imported declaration from the Incompleteness formalization. -/
def Defined (R : (Fin k → V) → Prop) : {ℌ : HierarchySymbol} → ℌ.Semisentence k → Prop
  | Sg-[_], φ => FirstOrder.Defined R φ.val
  | Pg-[_], φ => FirstOrder.Defined R φ.val
  | Dlt-[_], φ => φ.ProperOn V ∧ FirstOrder.Defined R φ.val

/-- Imported declaration from the Incompleteness formalization. -/
def DefinedWithParam (R : (Fin k → V) → Prop) : {ℌ : HierarchySymbol} → ℌ.Semiformula V k → Prop
  | Sg-[_], φ => FirstOrder.DefinedWithParam R φ.val
  | Pg-[_], φ => FirstOrder.DefinedWithParam R φ.val
  | Dlt-[_], φ => φ.ProperWithParamOn V ∧ FirstOrder.DefinedWithParam R φ.val

variable {ℌ : HierarchySymbol} {Γ : SigmaPiDelta}

section «lp_section_1»

variable (ℌ)

/-- Imported declaration from the Incompleteness formalization. -/
class Lightface {k} (P : (Fin k → V) → Prop) : Prop where
  definable : ∃ φ : ℌ.Semisentence k, Defined P φ

/-- Imported declaration from the Incompleteness formalization. -/
class Boldface {k} (P : (Fin k → V) → Prop) : Prop where
  definable : ∃ φ : ℌ.Semiformula V k, DefinedWithParam P φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedPred (P : V → Prop) (φ : ℌ.Semisentence 1) : Prop := Defined (fun v ↦ P (v 0)) φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedRel (R : V → V → Prop) (φ : ℌ.Semisentence 2) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1)) φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedRel₃ (R : V → V → V → Prop) (φ : ℌ.Semisentence 3) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2)) φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedRel₄ (R : V → V → V → V → Prop) (φ : ℌ.Semisentence 4) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2) (v 3)) φ

variable {ℌ}

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction {k} (f : (Fin k → V) → V) (φ : ℌ.Semisentence (k + 1)) : Prop :=
  Defined (fun v => v 0 = f (v ·.succ)) φ

variable (ℌ)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₀ (c : V) (φ : ℌ.Semisentence 1) : Prop := DefinedFunction (fun _ => c) φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₁ (f : V → V) (φ : ℌ.Semisentence 2) : Prop :=
  DefinedFunction (fun v => f (v 0)) φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₂ (f : V → V → V) (φ : ℌ.Semisentence 3) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1)) φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₃ (f : V → V → V → V) (φ : ℌ.Semisentence 4) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2)) φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₄ (f : V → V → V → V → V) (φ : ℌ.Semisentence 5) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3)) φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedFunction₅ (f : V → V → V → V → V → V) (φ : ℌ.Semisentence 6) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3) (v 4)) φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfacePred (P : V → Prop) : Prop := ℌ.Boldface (k := 1) (fun v ↦ P (v 0))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel (P : V → V → Prop) : Prop := ℌ.Boldface (k := 2) (fun v ↦ P (v 0) (v 1))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel₃ (P : V → V → V → Prop) : Prop :=
  ℌ.Boldface (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel₄ (P : V → V → V → V → Prop) : Prop :=
  ℌ.Boldface (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel₅ (P : V → V → V → V → V → Prop) : Prop :=
  ℌ.Boldface (k := 5) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceRel₆ (P : V → V → V → V → V → V → Prop) : Prop :=
  ℌ.Boldface (k := 6) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction (f : (Fin k → V) → V) : Prop :=
  ℌ.Boldface (k := k + 1) (fun v ↦ v 0 = f (v ·.succ))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₀ (c : V) : Prop := ℌ.BoldfaceFunction (k := 0) (fun _ ↦ c)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₁ (f : V → V) : Prop := ℌ.BoldfaceFunction (k := 1) (fun v ↦ f (v 0))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₂ (f : V → V → V) : Prop :=
  ℌ.BoldfaceFunction (k := 2) (fun v ↦ f (v 0) (v 1))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₃ (f : V → V → V → V) : Prop :=
  ℌ.BoldfaceFunction (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₄ (f : V → V → V → V → V) : Prop :=
  ℌ.BoldfaceFunction (k := 4) (fun v ↦ f (v 0) (v 1) (v 2) (v 3))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceFunction₅ (f : V → V → V → V → V → V) : Prop :=
  ℌ.BoldfaceFunction (k := 5) (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4))

variable {ℌ}

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Predicate " P " via " φ => DefinedPred Γ P φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation " P " via " φ => DefinedRel Γ P φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₃ " P " via " φ => DefinedRel₃ Γ P φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₄ " P " via " φ => DefinedRel₄ Γ P φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₀ " c " via " φ => DefinedFunction₀ Γ c φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₁ " f " via " φ => DefinedFunction₁ Γ f φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₂ " f " via " φ => DefinedFunction₂ Γ f φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₃ " f " via " φ => DefinedFunction₃ Γ f φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₄ " f " via " φ => DefinedFunction₄ Γ f φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₅ " f " via " φ => DefinedFunction₅ Γ f φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Predicate " P => BoldfacePred Γ P

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation " P => BoldfaceRel Γ P

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₃ " P => BoldfaceRel₃ Γ P

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₄ " P => BoldfaceRel₄ Γ P

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Relation₅ " P => BoldfaceRel₅ Γ P

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₁ " f => BoldfaceFunction₁ Γ f

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₂ " f => BoldfaceFunction₂ Γ f

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₃ " f => BoldfaceFunction₃ Γ f

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ "-Function₄ " f => BoldfaceFunction₄ Γ f


end «lp_section_1»

section «lp_section_2»

variable {k} {P Q : (Fin k → V) → Prop}

namespace Defined

lemma df {R : (Fin k → V) → Prop} {φ : ℌ.Semisentence k} (h : Defined R φ) :
    FirstOrder.Defined R φ.val :=
  match ℌ with
  | Sg-[_] => h
  | Pg-[_] => h
  | Dlt-[_] => h.2

lemma proper {R : (Fin k → V) → Prop} {m} {φ : Dlt-[m].Semisentence k} (h : Defined R φ) :
    φ.ProperOn V :=
  h.1

lemma of_zero {R : (Fin k → V) → Prop} {φ : Sg0.Semisentence k} (h : Defined R φ) :
    Defined R (φ.ofZero ℌ) :=
  match ℌ with
  | Sg-[m] => by intro _; simp [h.iff]
  | Pg-[m] => by intro _; simp [h.iff]
  | Dlt-[m] => ⟨by simp, by intro _; simp [h.iff]⟩

lemma emb {R : (Fin k → V) → Prop} {φ : ℌ.Semisentence k} (h : Defined R φ) : Defined R φ.emb :=
  match ℌ with
  | Sg-[m] => by intro _; simp [h.iff]
  | Pg-[m] => by intro _; simp [h.iff]
  | Dlt-[m] => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩

lemma of_iff {P Q : (Fin k → V) → Prop} (h : ∀ x, P x ↔ Q x) {φ : ℌ.Semisentence k} (H :
    Defined Q φ) :
    Defined P φ := by rwa [show P = Q from by funext v; simp [h]]

lemma to_definable (φ : ℌ.Semisentence k) (hP : Defined P φ) : ℌ.Boldface P := ⟨φ.rew Rew.emb, by
  match ℌ with
  | Sg-[_] => intro; simp [hP.iff]
  | Pg-[_] => intro; simp [hP.iff]
  | Dlt-[_] => exact ⟨
    fun v ↦ by rcases φ; simpa [HierarchySymbol.Semiformula.rew] using hP.proper.rew Rew.emb v,
    by intro; simp [hP.df.iff]⟩⟩

lemma to_definable₀ {φ : Sg0.Semisentence k} (hP : Defined P φ) :
    ℌ.Boldface P := Defined.to_definable (φ.ofZero ℌ) hP.of_zero

lemma to_definable_oRing (φ : ℌ.Semisentence k) (hP : Defined P φ) :
    ℌ.Boldface P := Defined.to_definable φ.emb hP.emb

lemma to_definable_oRing₀ (φ : Sg0.Semisentence k) (hP : Defined P φ) :
    ℌ.Boldface P := Defined.to_definable₀ hP.emb

end Defined

namespace DefinedFunction

lemma of_eq {f g : (Fin k → V) → V} (h : ∀ x, f x = g x)
    {φ : ℌ.Semisentence (k + 1)} (H : DefinedFunction f φ) : DefinedFunction g φ :=
  Defined.of_iff (by intro; simp [h]) H

lemma graph_delta {f : (Fin k → V) → V} {φ : Sg-[m].Semisentence (k + 1)}
    (h : DefinedFunction f φ) : DefinedFunction f φ.graphDelta :=
  ⟨by rcases m with _ | m <;> simp only [HierarchySymbol.Semiformula.graphDelta,
      Semiformula.ProperOn.of_zero]
      intro e
      simp only [Semiformula.sigma_mkDelta, h.df.iff, Semiformula.pi_mkDelta,
        Semiformula.val_mkPi, Semiformula.eval_all, Nat.succ_eq_add_one,
        LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Matrix.comp_vecCons',
        Semiterm.val_bvar, Matrix.vecCons_zero, Matrix.vecCons_succ,
        Semiformula.eval_operator₂, Matrix.cons_val_one, Structure.Eq.eq,
        LogicalConnective.Prop.arrow_eq, forall_eq]
      rw [eq_comm],
   by intro v; simp [h.df.iff]⟩

end DefinedFunction

namespace DefinedWithParam

lemma df {R : (Fin k → V) → Prop} {φ : ℌ.Semiformula V k} (h : DefinedWithParam R φ) :
    FirstOrder.DefinedWithParam R φ.val :=
  match ℌ with
  | Sg-[_] => h
  | Pg-[_] => h
  | Dlt-[_] => h.2

lemma proper {R : (Fin k → V) → Prop} {m} {φ : Dlt-[m].Semiformula V k} (h : DefinedWithParam R φ) :
    φ.ProperWithParamOn V :=
  h.1

lemma of_zero {R : (Fin k → V) → Prop} {Γ'} {φ : Γ'-[0].Semiformula V k}
    (h : DefinedWithParam R φ) {Γ} : DefinedWithParam R (φ.ofZero Γ) :=
  match Γ with
  | Sg-[m] => by intro _; simp [h.df.iff]
  | Pg-[m] => by intro _; simp [h.df.iff]
  | Dlt-[m] => ⟨by simp , by intro _; simp [h.df.iff]⟩

lemma of_deltaOne {R : (Fin k → V) → Prop} {Γ m} {φ : Dlt1.Semiformula V k}
    (h : DefinedWithParam R φ) : DefinedWithParam R (φ.ofDeltaOne Γ m) :=
  match Γ with
  | Sg =>
    by
      intro _
      simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, HierarchySymbol.Semiformula.val_sigma]
  | Pg => by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, h.proper.iff']
  | Dlt =>
    ⟨by
      intro _
      simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff,
        HierarchySymbol.Semiformula.val_sigma, h.proper.iff'],
    by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff,
      HierarchySymbol.Semiformula.val_sigma]⟩

lemma emb {R : (Fin k → V) → Prop} {φ : ℌ.Semiformula V k} (h : DefinedWithParam R φ) :
    DefinedWithParam R φ.emb :=
  match ℌ with
  | Sg-[m] => by intro _; simp [h.iff]
  | Pg-[m] => by intro _; simp [h.iff]
  | Dlt-[m] => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩

lemma of_iff {P Q : (Fin k → V) → Prop} (h : ∀ x, P x ↔ Q x)
    {φ : ℌ.Semiformula V k} (H : DefinedWithParam Q φ) : DefinedWithParam P φ := by
  rwa [show P = Q from by funext v; simp [h]]

lemma to_definable {φ : ℌ.Semiformula V k} (h : DefinedWithParam P φ) : ℌ.Boldface P := ⟨φ, h⟩

lemma to_definable₀ {φ : Γ'-[0].Semiformula V k}
    (h : DefinedWithParam P φ) : ℌ.Boldface P := ⟨φ.ofZero ℌ, h.of_zero⟩

lemma to_definable_deltaOne {φ : Dlt1.Semiformula V k} {Γ m}
    (h : DefinedWithParam P φ) : Γ-[m + 1].Boldface P := ⟨φ.ofDeltaOne Γ m, h.of_deltaOne⟩

lemma retraction {φ : ℌ.Semiformula V k} (hp : DefinedWithParam P φ) (f : Fin k → Fin l) :
    DefinedWithParam (fun v ↦ P fun i ↦ v (f i)) (φ.rew <| Rew.substs fun x ↦ #(f x)) :=
  match ℌ with
  | Sg-[_] => by intro; simp [hp.df.iff]
  | Pg-[_] => by intro; simp [hp.df.iff]
  | Dlt-[_] => ⟨hp.proper.rew _, by intro; simp [hp.df.iff]⟩

@[simp] lemma verum : DefinedWithParam (fun _ ↦ True) (⊤ : ℌ.Semiformula V k) :=
  match ℌ with
  | Sg-[m] => by intro v; simp
  | Pg-[m] => by intro v; simp
  | Dlt-[m] => ⟨by simp, by intro v; simp⟩

@[simp] lemma falsum : DefinedWithParam (fun _ ↦ False) (⊥ : ℌ.Semiformula V k) :=
  match ℌ with
  | Sg-[m] => by intro v; simp
  | Pg-[m] => by intro v; simp
  | Dlt-[m] => ⟨by simp, by intro v; simp⟩

lemma and {φ ψ : ℌ.Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x ∧ Q x) (φ ⋏ ψ) :=
  match ℌ with
  | Sg-[m] => by intro v; simp [hp.iff, hq.iff]
  | Pg-[m] => by intro v; simp [hp.iff, hq.iff]
  | Dlt-[m] => ⟨hp.proper.and hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩

lemma or {φ ψ : ℌ.Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x ∨ Q x) (φ ⋎ ψ) :=
  match ℌ with
  | Sg-[m] => by intro v; simp [hp.iff, hq.iff]
  | Pg-[m] => by intro v; simp [hp.iff, hq.iff]
  | Dlt-[m] => ⟨hp.proper.or hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩

lemma negSigma {φ : Sg-[m].Semiformula V k} (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun x ↦ ¬P x) φ.negSigma := by intro v; simp [hp.iff]

lemma negPi {φ : Pg-[m].Semiformula V k} (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun x ↦ ¬P x) φ.negPi := by intro v; simp [hp.iff]

lemma not {φ : Dlt-[m].Semiformula V k} (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun x ↦ ¬P x) (∼φ) :=
      ⟨hp.proper.neg, by intro v; simp [hp.proper.eval_neg, hp.df.iff]⟩

lemma imp {φ ψ : Dlt-[m].Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x → Q x) (φ ==> ψ) :=
      (hp.not.or hq).of_iff (by intro x; simp [imp_iff_not_or])

lemma iff {φ ψ : Dlt-[m].Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x ↔ Q x) (φ <=> ψ) :=
      ((hp.imp hq).and (hq.imp hp)).of_iff <| by intro v; simp [iff_iff_implies_and_implies]

lemma ball {P : (Fin (k + 1) → V) → Prop} {φ : ℌ.Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) (t : Semiterm ℒₒᵣ V k) :
    DefinedWithParam (fun v ↦ ∀ x < t.valm V v id,
      P (x :> v)) (HierarchySymbol.Semiformula.ball t φ) :=
  match ℌ with
  | Sg-[m] => by intro v; simp [hp.df.iff]
  | Pg-[m] => by intro v; simp [hp.df.iff]
  | Dlt-[m] => ⟨hp.proper.ball, by intro v; simp [hp.df.iff]⟩

lemma bex {P : (Fin (k + 1) → V) → Prop} {φ : ℌ.Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) (t : Semiterm ℒₒᵣ V k) :
    DefinedWithParam (fun v ↦ ∃ x < t.valm V v id,
      P (x :> v)) (HierarchySymbol.Semiformula.bex t φ) :=
  match ℌ with
  | Sg-[m] => by intro v; simp [hp.df.iff]
  | Pg-[m] => by intro v; simp [hp.df.iff]
  | Dlt-[m] => ⟨hp.proper.bex, by intro v; simp [hp.df.iff]⟩

lemma ex {P : (Fin (k + 1) → V) → Prop} {φ : Sg-[m + 1].Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun v ↦ ∃ x, P (x :> v)) φ.ex := by intro _; simp [hp.df.iff]

lemma all {P : (Fin (k + 1) → V) → Prop} {φ : Pg-[m + 1].Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun v ↦ ∀ x, P (x :> v)) φ.all := by intro _; simp [hp.df.iff]

end DefinedWithParam

namespace BoldfaceRel

@[simp] instance eq : ℌ.BoldfaceRel (Eq : V → V → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1” (by simp)) (by intro _; simp)

@[simp] instance lt : ℌ.BoldfaceRel (LT.lt : V → V → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 < #1” (by simp)) (by intro _; simp)

@[simp] instance le [V ⊧ₘ* 𝐏𝐀⁻] : ℌ.BoldfaceRel (LE.le : V → V → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 ≤ #1” (by simp)) (by intro _; simp)

end BoldfaceRel

namespace BoldfaceFunction₂

instance add : ℌ.BoldfaceFunction₂ ((· + ·) : V → V → V) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 + #2” (by simp)) (by intro _; simp)

instance mul : ℌ.BoldfaceFunction₂ ((· * ·) : V → V → V) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 * #2” (by simp)) (by intro _; simp)

instance hAdd : ℌ.BoldfaceFunction₂ (HAdd.hAdd : V → V → V) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 + #2” (by simp)) (by intro _; simp)

instance hMul : ℌ.BoldfaceFunction₂ (HMul.hMul : V → V → V) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 * #2” (by simp)) (by intro _; simp)

end BoldfaceFunction₂

namespace Boldface

lemma mkPolarity {P : (Fin k → V) → Prop} {Γ : Polarity}
    (φ : Semiformula ℒₒᵣ V k) (hp : Hierarchy Γ m φ) (hP : ∀ v, P v ↔
      Semiformula.Evalm V v id φ) : Γ-[m].Boldface P :=
  match Γ with
  | Sg => ⟨.mkSigma φ hp, by intro v; simp [hP]⟩
  | Pg => ⟨.mkPi φ hp, by intro v; simp [hP]⟩

lemma of_iff (H : ℌ.Boldface Q) (h : ∀ x, P x ↔ Q x) : ℌ.Boldface P := by
  rwa [show P = Q from by funext v; simp [h]]

lemma of_oRing (h : ℌ.Boldface P) : ℌ.Boldface P := by rcases h with ⟨φ, hP⟩; exact ⟨φ.emb, hP.emb⟩

lemma of_delta (h : Dlt-[m].Boldface P) : Γ-[m].Boldface P := by
  rcases h with ⟨φ, h⟩
  match Γ with
  | Sg => exact ⟨φ.sigma, by intro v; simp [HierarchySymbol.Semiformula.val_sigma, h.df.iff]⟩
  | Pg =>
    exact ⟨φ.pi, by intro v; simp [←h.proper v, HierarchySymbol.Semiformula.val_sigma, h.df.iff]⟩
  | Dlt => exact ⟨φ, h⟩

instance [Dlt-[m].Boldface P] (Γ) : Γ-[m].Boldface P := of_delta inferInstance

lemma of_sigma_of_pi (hσ : Sg-[m].Boldface P) (hπ : Pg-[m].Boldface P) : Γ-[m].Boldface P :=
  match Γ with
  | Sg => hσ
  | Pg => hπ
  | Dlt => by
    rcases hσ with ⟨φ, hp⟩; rcases hπ with ⟨ψ, hq⟩
    exact ⟨.mkDelta φ ψ, by intro v; simp [hp.df.iff, hq.df.iff], by intro v; simp [hp.df.iff]⟩

lemma of_zero (h : Γ'-[0].Boldface P) : ℌ.Boldface P := by
  rcases h with ⟨⟨φ, hp⟩⟩; exact hp.to_definable₀

lemma of_deltaOne (h : Dlt1.Boldface P) {Γ m} : Γ-[m + 1].Boldface P := by
  rcases h with ⟨⟨φ, hp⟩⟩; exact hp.to_definable_deltaOne

instance [Sg0.Boldface P] (ℌ : HierarchySymbol) : ℌ.Boldface P :=
  Boldface.of_zero (Γ' := Sg) (ℌ := ℌ) inferInstance

lemma retraction (h : ℌ.Boldface P) {n} (f : Fin k → Fin n) :
    ℌ.Boldface fun v ↦ P (fun i ↦ v (f i)) := by
  rcases h with ⟨φ, h⟩
  exact ⟨φ.rew (Rew.substs (fun i ↦ #(f i))),
  match ℌ with
  | Sg-[_] => by intro; simp [h.df.iff]
  | Pg-[_] => by intro; simp [h.df.iff]
  | Dlt-[_] => ⟨h.proper.rew _, by intro; simp [h.df.iff]⟩⟩

lemma retractiont (h : ℌ.Boldface P) (f : Fin k → Semiterm ℒₒᵣ V n) :
    ℌ.Boldface fun v ↦ P (fun i ↦ Semiterm.valm V v id (f i)) := by
  rcases h with ⟨φ, h⟩
  exact ⟨φ.rew (Rew.substs f),
  match ℌ with
  | Sg-[_] => by intro; simp [h.df.iff]
  | Pg-[_] => by intro; simp [h.df.iff]
  | Dlt-[_] => ⟨h.proper.rew _, by intro; simp [h.df.iff]⟩⟩

@[simp] lemma const {P : Prop} : ℌ.Boldface (fun _ : Fin k → V ↦ P) := of_zero (by
  by_cases hP : P
  · exact ⟨.mkSigma ⊤ (by simp), by intro; simp[hP]⟩
  · exact ⟨.mkSigma ⊥ (by simp), by intro; simp[hP]⟩)

lemma and (h₁ : ℌ.Boldface P) (h₂ : ℌ.Boldface Q) :
    ℌ.Boldface (fun v ↦ P v ∧ Q v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨p₁ ⋏ p₂, h₁.and h₂⟩

lemma conj {k l} {P : Fin l → (Fin k → V) → Prop}
    (h : ∀ i, ℌ.Boldface fun w : Fin k → V ↦ P i w) :
    ℌ.Boldface fun v : Fin k → V ↦ ∀ i, P i v := by
  induction l
  case zero => simp
  case succ l ih =>
    suffices ℌ.Boldface fun v : Fin k → V ↦ P 0 v ∧ ∀ i : Fin l, P i.succ v by
      apply of_iff this; intro x
      constructor
      · intro h
        exact ⟨h 0, fun i ↦ h i.succ⟩
      · rintro ⟨h0, hs⟩
        intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ i => exact hs i
    apply and (h 0); apply ih
    intro i; exact h i.succ

lemma or (h₁ : ℌ.Boldface P) (h₂ : ℌ.Boldface Q) :
    ℌ.Boldface (fun v ↦ P v ∨ Q v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨p₁ ⋎ p₂, h₁.or h₂⟩

lemma not (h : Γ.alt-[m].Boldface P) :
    Γ-[m].Boldface (fun v ↦ ¬P v) := by
  match Γ with
  | Sg => rcases h with ⟨φ, h⟩; exact ⟨φ.negPi, h.negPi⟩
  | Pg => rcases h with ⟨φ, h⟩; exact ⟨φ.negSigma, h.negSigma⟩
  | Dlt => rcases h with ⟨φ, h⟩; exact ⟨φ.negDelta, h.not⟩

lemma imp (h₁ : Γ.alt-[m].Boldface P) (h₂ : Γ-[m].Boldface Q) :
    Γ-[m].Boldface (fun v ↦ P v → Q v) := by
  match Γ with
  | Sg =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negPi.or p₂, (h₁.negPi.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | Pg =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negSigma.or p₂, (h₁.negSigma.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | Dlt =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩; exact ⟨p₁ ==> p₂, h₁.imp h₂⟩

lemma iff (h₁ : Dlt-[m].Boldface P) (h₂ : Dlt-[m].Boldface Q) {Γ} :
    Γ-[m].Boldface (fun v ↦ P v ↔ Q v) :=
  .of_delta (by rcases h₁ with ⟨φ, hp⟩; rcases h₂ with ⟨ψ, hq⟩; exact ⟨φ <=> ψ, hp.iff hq⟩)

lemma all {P : (Fin k → V) → V → Prop} (h : Pg-[s + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Pg-[s + 1].Boldface (fun v ↦ ∀ x, P v x) := by
  rcases h with ⟨φ, hp⟩
  exact ⟨.mkPi (∀' φ.val) (by simp), by intro v; simp [hp.df.iff]⟩

lemma ex {P : (Fin k → V) → V → Prop} (h : Sg-[s + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Sg-[s + 1].Boldface (fun v ↦ ∃ x, P v x) := by
  rcases h with ⟨φ, hp⟩
  exact ⟨.mkSigma (∃' φ.val) (by simp), by intro v; simp [hp.df.iff]⟩

lemma equal' (i j : Fin k) : ℌ.Boldface fun v : Fin k → V ↦ v i = v j := by
  simpa using retraction BoldfaceRel.eq ![i, j]

lemma of_sigma {f : (Fin k → V) → V} (h : Sg-[m].BoldfaceFunction f) {Γ} :
    Γ-[m].BoldfaceFunction f := by
  cases m with
  | zero => exact of_zero h
  | succ m =>
    apply of_sigma_of_pi
    · exact h
    · have : Pg-[m + 1].Boldface fun v ↦ ∀ y, y = f (v ·.succ) → v 0 = y := all <| imp
        (by simpa using retraction h (0 :> (·.succ.succ)))
        (by simpa using equal' 1 0)
      exact of_iff this (fun v ↦ by simp)

lemma exVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : Sg-[m + 1].Boldface fun w : Fin (k + l) →
      V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    Sg-[m + 1].Boldface fun v : Fin k → V ↦ ∃ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices Sg-[m + 1].Boldface fun v : Fin k → V ↦ ∃ y, ∃ ys : Fin l → V, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · rintro ⟨ys, h⟩; exact ⟨ys 0, (ys ·.succ), by simpa using h⟩
      · rintro ⟨y, ys, h⟩; exact ⟨_, h⟩
    apply ex; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) :=
      Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp only [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases i using Fin.cases with
        | zero =>
          simp only [Matrix.vecCons_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        | succ i =>
          simp only [Matrix.vecCons_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma allVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : Pg-[m + 1].Boldface fun w : Fin (k + l) →
      V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    Pg-[m + 1].Boldface fun v : Fin k → V ↦ ∀ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices Pg-[m + 1].Boldface fun v : Fin k → V ↦ ∀ y, ∀ ys : Fin l → V, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · intro h y ys; apply h
      · intro h ys; simpa using h (ys 0) (ys ·.succ)
    apply all; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) :=
      Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp only [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases i using Fin.cases with
        | zero =>
          simp only [Matrix.vecCons_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        | succ i =>
          simp only [Matrix.vecCons_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

private lemma substitution_sigma {f : Fin k → (Fin l → V) → V} (hP : Sg-[m + 1].Boldface P) (hf :
    ∀ i, Sg-[m + 1].BoldfaceFunction (f i)) :
    Sg-[m + 1].Boldface fun z ↦ P (fun i ↦ f i z) := by
  have : Sg-[m + 1].Boldface fun z ↦ ∃ ys : Fin k → V, (∀ i, ys i = f i z) ∧ P ys := by
    apply exVec; apply and
    · apply conj; intro i
      simpa using retraction (of_sigma (hf i)) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact of_iff this <| by
    intro v
    constructor
    · intro hP
      exact ⟨(f · v), by simp, hP⟩
    · rintro ⟨ys, hys, hP⟩
      have : ys = fun i ↦ f i v := funext hys
      rcases this; exact hP

private lemma substitution_pi {f : Fin k → (Fin l → V) → V} (hP : Pg-[m + 1].Boldface P) (hf :
    ∀ i, Sg-[m + 1].BoldfaceFunction (f i)) :
    Pg-[m + 1].Boldface fun z ↦ P (fun i ↦ f i z) := by
  have : Pg-[m + 1].Boldface fun z ↦ ∀ ys : Fin k → V, (∀ i, ys i = f i z) → P ys := by
    apply allVec; apply imp
    · apply conj; intro i
      simpa using retraction (of_sigma (hf i)) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact of_iff this <| by
    intro v
    constructor
    · intro h ys e
      have : ys = (f · v) := funext e
      rcases this; exact h
    · intro h; apply h _ (by simp)

lemma substitution {f : Fin k → (Fin l → V) → V}
    (hP : Γ-[m + 1].Boldface P) (hf : ∀ i, Sg-[m + 1].BoldfaceFunction (f i)) :
    Γ-[m + 1].Boldface fun z ↦ P (fun i ↦ f i z) :=
  match Γ with
  | Sg => substitution_sigma hP hf
  | Pg => substitution_pi hP hf
  | Dlt => of_sigma_of_pi (substitution_sigma (of_delta hP) hf) (substitution_pi (of_delta hP) hf)

end Boldface

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfacePred.comp {P : V → Prop} {k} {f :
    (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfacePred P) (hf : Sg-[m + 1].BoldfaceFunction f) :
    Γ-[m + 1].Boldface (fun v ↦ P (f v)) :=
  Boldface.substitution (f := ![f]) hP (by simpa using hf)

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceRel.comp {P : V → V → Prop} {k} {f g :
    (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfaceRel P)
    (hf : Sg-[m + 1].BoldfaceFunction f) (hg : Sg-[m + 1].BoldfaceFunction g) :
    Γ-[m + 1].Boldface fun v ↦ P (f v) (g v) :=
  Boldface.substitution (f := ![f, g]) hP (by simp [forall_fin_iff_zero_and_forall_succ, hf, hg])

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceRel₃.comp {k} {P :
    V → V → V → Prop} {f₁ f₂ f₃ :
    (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfaceRel₃ P)
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂)
    (hf₃ : Sg-[m + 1].BoldfaceFunction f₃) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  Boldface.substitution (f :=
    ![f₁, f₂, f₃]) hP (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceRel₄.comp {k} {P :
    V → V → V → V → Prop} {f₁ f₂ f₃ f₄ :
    (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfaceRel₄ P)
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂)
    (hf₃ : Sg-[m + 1].BoldfaceFunction f₃) (hf₄ : Sg-[m + 1].BoldfaceFunction f₄) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  Boldface.substitution (f :=
    ![f₁, f₂, f₃, f₄]) hP (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄])

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceRel₅.comp {k} {P :
    V → V → V → V → V → Prop} {f₁ f₂ f₃ f₄ f₅ :
    (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfaceRel₅ P)
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂)
    (hf₃ : Sg-[m + 1].BoldfaceFunction f₃) (hf₄ : Sg-[m + 1].BoldfaceFunction f₄)
    (hf₅ : Sg-[m + 1].BoldfaceFunction f₅) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  Boldface.substitution (f :=
    ![f₁, f₂, f₃, f₄, f₅]) hP (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄,
      hf₅])

namespace Boldface

lemma comp₁ {k} {P : V → Prop} {f : (Fin k → V) → V}
    [Γ-[m + 1].BoldfacePred P]
    (hf : Sg-[m + 1].BoldfaceFunction f) : Γ-[m + 1].Boldface fun v ↦ P (f v) :=
  BoldfacePred.comp inferInstance hf

lemma comp₂ {k} {P : V → V → Prop} {f g : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel P]
    (hf : Sg-[m + 1].BoldfaceFunction f) (hg : Sg-[m + 1].BoldfaceFunction g) :
    Γ-[m + 1].Boldface (fun v ↦ P (f v) (g v)) :=
  BoldfaceRel.comp inferInstance hf hg

lemma comp₃ {k} {P : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel₃ P]
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂) (hf₃ : Sg-[m +
      1].BoldfaceFunction f₃) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  BoldfaceRel₃.comp inferInstance hf₁ hf₂ hf₃

lemma comp₄ {k} {P : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel₄ P]
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂)
    (hf₃ : Sg-[m + 1].BoldfaceFunction f₃) (hf₄ : Sg-[m + 1].BoldfaceFunction f₄) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  BoldfaceRel₄.comp inferInstance hf₁ hf₂ hf₃ hf₄

lemma comp₅ {k} {P : V → V → V → V → V → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel₅ P]
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂)
    (hf₃ : Sg-[m + 1].BoldfaceFunction f₃) (hf₄ : Sg-[m + 1].BoldfaceFunction f₄)
    (hf₅ : Sg-[m + 1].BoldfaceFunction f₅) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  BoldfaceRel₅.comp inferInstance hf₁ hf₂ hf₃ hf₄ hf₅

end Boldface

section «lp_section_3»

variable {ℌ : HierarchySymbol}

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfacePred.of_iff {P Q : V → Prop}
    (H : ℌ.BoldfacePred Q) (h : ∀ x, P x ↔ Q x) : ℌ.BoldfacePred P := by
  rwa [show P = Q from by funext v; simp [h]]

instance _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₁.graph {f : V → V} [h :
    ℌ.BoldfaceFunction₁ f] :
  ℌ.BoldfaceRel (Function.Graph f) := h

instance _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₂.graph {f : V → V → V} [h :
    ℌ.BoldfaceFunction₂ f] :
  ℌ.BoldfaceRel₃ (Function.Graph₂ f) := h

instance _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₃.graph {f : V → V → V → V} [h :
    ℌ.BoldfaceFunction₃ f] :
  ℌ.BoldfaceRel₄ (Function.Graph₃ f) := h

end «lp_section_3»

namespace BoldfaceFunction

variable {ℌ : HierarchySymbol}

lemma graph_delta {k} {f : (Fin k → V) → V}
    (h : Sg-[m].BoldfaceFunction f) : Dlt-[m].BoldfaceFunction f := by
  rcases h with ⟨φ, h⟩
  exact ⟨φ.graphDelta, by
    rcases m with _ | m <;> simp only [HierarchySymbol.Semiformula.graphDelta,
      Semiformula.ProperWithParamOn.of_zero]
    intro e
    simp only [Semiformula.sigma_mkDelta, h.df.iff, Semiformula.pi_mkDelta,
      Semiformula.val_mkPi, Semiformula.eval_all, Nat.succ_eq_add_one,
      LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Matrix.comp_vecCons',
      Semiterm.val_bvar, Matrix.vecCons_zero, Matrix.vecCons_succ, Semiformula.eval_operator₂,
      Matrix.cons_val_one, Structure.Eq.eq, LogicalConnective.Prop.arrow_eq, forall_eq]
    exact eq_comm, by
    intro v; simp [h.df.iff]⟩

instance {k} {f : (Fin k → V) → V} [h : Sg-[m].BoldfaceFunction f] : Dlt-[m].BoldfaceFunction f :=
  BoldfaceFunction.graph_delta h

instance {k} {f : (Fin k → V) → V} [Sg0.BoldfaceFunction f] : ℌ.BoldfaceFunction f := inferInstance

lemma of_sigmaOne {k} {f : (Fin k → V) → V}
    (h : Sg1.BoldfaceFunction f) {Γ m} : Γ-[m + 1].BoldfaceFunction f :=
      Boldface.of_deltaOne (graph_delta h)

@[simp 1100] lemma var {k} (i : Fin k) : ℌ.BoldfaceFunction (fun v : Fin k → V ↦ v i) :=
  .of_zero (Γ' := Sg) ⟨.mkSigma “x. x = !!#i.succ” (by simp), by intro _; simp⟩

@[simp] lemma const {k} (c : V) : ℌ.BoldfaceFunction (fun _ : Fin k → V ↦ c) :=
  .of_zero (Γ' := Sg) ⟨.mkSigma “x. #0 = &c” (by simp), by intro v; simp⟩

@[simp] lemma term_retraction (t : Semiterm ℒₒᵣ V n) (e : Fin n → Fin k) :
    ℌ.BoldfaceFunction fun v : Fin k → V ↦ Semiterm.valm V (fun x ↦ v (e x)) id t :=
  .of_zero (Γ' := Sg)
    ⟨.mkSigma “x. x = !!(Rew.substs (fun x ↦ #(e x).succ) t)” (by simp),
      by intro v; simp [Semiterm.val_substs]⟩

@[simp 1100] lemma term (t : Semiterm ℒₒᵣ V k) :
    ℌ.BoldfaceFunction fun v : Fin k → V ↦ Semiterm.valm V v id t :=
  .of_zero (Γ' :=
    Sg) ⟨.mkSigma “x. x = !!(Rew.bShift t)” (by simp), by intro v; simp [Semiterm.val_bShift']⟩

lemma of_eq {f : (Fin k → V) → V} (g) (h : ∀ v, f v = g v) (H : ℌ.BoldfaceFunction f) :
    ℌ.BoldfaceFunction g := by rwa [show g = f from by funext v; simp [h]]

lemma retraction {n k} {f : (Fin k → V) → V} (hf : ℌ.BoldfaceFunction f) (e : Fin k → Fin n) :
    ℌ.BoldfaceFunction fun v ↦ f (fun i ↦ v (e i)) := by
  have := Boldface.retraction (n := n + 1) hf (0 :> fun i ↦ (e i).succ); simp at this
  exact this.of_iff (by intro x; simp)

lemma retractiont {n k} {f : (Fin k → V) → V} (hf : ℌ.BoldfaceFunction f) (t :
    Fin k → Semiterm ℒₒᵣ V n) :
    ℌ.BoldfaceFunction fun v ↦ f (fun i ↦ Semiterm.valm V v id (t i)) := by
  have := Boldface.retractiont (n := n + 1) hf (#0 :> fun i ↦ Rew.bShift (t i)); simp at this
  exact this.of_iff (by intro x; simp [Semiterm.val_bShift'])

lemma rel {f : (Fin k → V) → V} (h : ℌ.BoldfaceFunction f) :
  ℌ.Boldface (fun v ↦ v 0 = f (v ·.succ)) := h

lemma nth (ℌ : HierarchySymbol) (i : Fin k) : ℌ.BoldfaceFunction fun w : Fin k → V ↦ w i := by
  apply Boldface.of_zero (Γ' := Sg)
  exact ⟨.mkSigma “x. x = #i.succ” (by simp), by intro v; simp⟩

lemma substitution {f : Fin k → (Fin l → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction F) (hf : ∀ i, Sg-[m + 1].BoldfaceFunction (f i)) :
    Γ-[m + 1].BoldfaceFunction fun z ↦ F (fun i ↦ f i z) := by
  simpa using Boldface.substitution (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF <| by
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using Boldface.retraction (hf i) (0 :> (·.succ.succ))

end BoldfaceFunction

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₁.comp {k} {F : V → V} {f :
    (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₁ F) (hf : Sg-[m + 1].BoldfaceFunction f) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f v)) :=
  BoldfaceFunction.substitution (f := ![f]) hF (by simp [hf])

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₂.comp {k} {F : V → V → V} {f₁ f₂ :
    (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₂ F)
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  BoldfaceFunction.substitution (f :=
    ![f₁, f₂]) hF (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₃.comp {k} {F :
    V → V → V → V} {f₁ f₂ f₃ :
    (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₃ F)
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂)
    (hf₃ : Sg-[m + 1].BoldfaceFunction f₃) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  BoldfaceFunction.substitution (f :=
    ![f₁, f₂, f₃]) hF (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₄.comp {k} {F :
    V → V → V → V → V} {f₁ f₂ f₃ f₄ :
    (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₄ F)
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂)
    (hf₃ : Sg-[m + 1].BoldfaceFunction f₃) (hf₄ : Sg-[m + 1].BoldfaceFunction f₄) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  BoldfaceFunction.substitution (f :=
    ![f₁, f₂, f₃, f₄]) hF (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₅.comp {k} {F :
    V → V → V → V → V → V} {f₁ f₂ f₃ f₄ f₅ :
    (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₅ F)
    (hf₁ : Sg-[m + 1].BoldfaceFunction f₁) (hf₂ : Sg-[m + 1].BoldfaceFunction f₂)
    (hf₃ : Sg-[m + 1].BoldfaceFunction f₃) (hf₄ : Sg-[m + 1].BoldfaceFunction f₄)
    (hf₅ : Sg-[m + 1].BoldfaceFunction f₅) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  BoldfaceFunction.substitution (f :=
    ![f₁, f₂, f₃, f₄, f₅]) hF (by simp [forall_fin_iff_zero_and_forall_succ, *])

namespace BoldfaceFunction

lemma comp₁ {k} {f : V → V} [Γ-[m + 1].BoldfaceFunction₁ f]
    {g : (Fin k → V) → V} (hg : Sg-[m + 1].BoldfaceFunction g) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g v)) :=
  BoldfaceFunction₁.comp inferInstance hg

lemma comp₂ {k} {f : V → V → V} [Γ-[m + 1].BoldfaceFunction₂ f]
    {g₁ g₂ : (Fin k → V) → V} (hg₁ : Sg-[m + 1].BoldfaceFunction g₁) (hg₂ : Sg-[m +
      1].BoldfaceFunction g₂) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v)) :=
  BoldfaceFunction₂.comp inferInstance hg₁ hg₂

lemma comp₃ {k} {f : V → V → V → V} [Γ-[m + 1].BoldfaceFunction₃ f]
    {g₁ g₂ g₃ : (Fin k → V) → V}
    (hg₁ : Sg-[m + 1].BoldfaceFunction g₁) (hg₂ : Sg-[m + 1].BoldfaceFunction g₂) (hg₃ : Sg-[m +
      1].BoldfaceFunction g₃) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) :=
  BoldfaceFunction₃.comp inferInstance hg₁ hg₂ hg₃

lemma comp₄ {k} {f : V → V → V → V → V} [Γ-[m + 1].BoldfaceFunction₄ f]
    {g₁ g₂ g₃ g₄ : (Fin k → V) → V}
    (hg₁ : Sg-[m + 1].BoldfaceFunction g₁) (hg₂ : Sg-[m + 1].BoldfaceFunction g₂)
    (hg₃ : Sg-[m + 1].BoldfaceFunction g₃) (hg₄ : Sg-[m + 1].BoldfaceFunction g₄) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v)) :=
  BoldfaceFunction₄.comp inferInstance hg₁ hg₂ hg₃ hg₄

lemma comp₅ {k} {f : V → V → V → V → V → V} [Γ-[m + 1].BoldfaceFunction₅ f]
    {g₁ g₂ g₃ g₄ g₅ : (Fin k → V) → V}
    (hg₁ : Sg-[m + 1].BoldfaceFunction g₁) (hg₂ : Sg-[m + 1].BoldfaceFunction g₂)
    (hg₃ : Sg-[m + 1].BoldfaceFunction g₃) (hg₄ : Sg-[m + 1].BoldfaceFunction g₄)
    (hg₅ : Sg-[m + 1].BoldfaceFunction g₅) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v) (g₅ v)) :=
  BoldfaceFunction₅.comp inferInstance hg₁ hg₂ hg₃ hg₄ hg₅

end BoldfaceFunction

namespace Boldface

lemma ball_lt {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : Sg-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ x < f v, P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨φ, hp⟩
  match Γ with
  | Sg => exact
    ⟨ .mkSigma (∃' (bf.val ⋏ (∀[“#0 < #1”] φ.val <~ (#0 :> (#·.succ.succ))))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | Pg => exact
    ⟨ .mkPi (∀' (bf.val ==> (∀[“#0 < #1”] φ.val <~ (#0 :> (#·.succ.succ))))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | Dlt =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃' (bf.val ⋏ (∀[“#0 < #1”] φ.sigma.val <~ (#0 :> (#·.succ.succ))))) (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma] ⟩
      ⟨ .mkPi (∀' (bf.val ==> (∀[“#0 < #1”] φ.pi.val <~ (#0 :> (#·.succ.succ))))) (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

lemma bex_lt {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : Sg-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∃ x < f v, P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨φ, hp⟩
  match Γ with
  | Sg => exact
    ⟨ .mkSigma (∃' (bf.val ⋏ (∃[“#0 < #1”] φ.val <~ (#0 :> (#·.succ.succ))))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | Pg => exact
    ⟨ .mkPi (∀' (bf.val ==> (∃[“#0 < #1”] φ.val <~ (#0 :> (#·.succ.succ))))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | Dlt =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃' (bf.val ⋏ (∃[“#0 < #1”] φ.sigma.val <~ (#0 :> (#·.succ.succ))))) (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma] ⟩
      ⟨ .mkPi (∀' (bf.val ==> (∃[“#0 < #1”] φ.pi.val <~ (#0 :> (#·.succ.succ))))) (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

lemma ball_le [V ⊧ₘ* 𝐏𝐀⁻] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : Sg-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ x ≤ f v, P v x) := by
  have : Γ-[m + 1].Boldface (fun v ↦ ∀ x < f v + 1, P v x) :=
    ball_lt (BoldfaceFunction₂.comp inferInstance hf (BoldfaceFunction.const 1)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma bex_le [V ⊧ₘ* 𝐏𝐀⁻] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : Sg-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∃ x ≤ f v, P v x) := by
  have : Γ-[m + 1].Boldface (fun v ↦ ∃ x < f v + 1, P v x) :=
    bex_lt (BoldfaceFunction₂.comp inferInstance hf (BoldfaceFunction.const 1)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma ball_lt' {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : Sg-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ {x}, x < f v → P v x) := ball_lt hf h

lemma ball_le' [V ⊧ₘ* 𝐏𝐀⁻] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : Sg-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ {x}, x ≤ f v → P v x) := ball_le hf h

end Boldface

end «lp_section_2»

end HierarchySymbol
end Arith

end FirstOrder
end LO
