/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arith.D3
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental
import LeanPool.Incompleteness.ToFoundation.Basic

/-! # Second -/


noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith
namespace Formalized

open LO.FirstOrder LO.FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Formalized.substNumeral (φ x : V) : V := ⌜ℒₒᵣ⌝.substs₁ (numeral x) φ

lemma _root_.LO.Arith.Formalized.substNumeral_app_quote (σ : Semisentence ℒₒᵣ 1) (n : ℕ) :
    substNumeral ⌜σ⌝ (n : V) = ⌜(σ/[‘↑n’] : Sentence ℒₒᵣ)⌝ := by
  dsimp [substNumeral]
  let w : Fin 1 → Semiterm ℒₒᵣ Empty 0 := ![‘↑n’]
  have : ?[numeral (n : V)] = (⌜fun i : Fin 1 ↦ ⌜w i⌝⌝ : V) :=
    nth_ext' 1 (by simp) (by simp) (by simp [w, quote_cons, quote_matrix_empty,
      Matrix.constant_eq_singleton])
  rw [Language.substs₁, this, quote_substs' (L := ℒₒᵣ)]

lemma _root_.LO.Arith.Formalized.substNumeral_app_quote_quote (σ π : Semisentence ℒₒᵣ 1) :
    substNumeral (⌜σ⌝ : V) ⌜π⌝ = ⌜(σ/[⌜π⌝] : Sentence ℒₒᵣ)⌝ := by
  have h := substNumeral_app_quote (V := V) σ ⌜π⌝
  simp only [quote_eq_encode] at h ⊢
  exact h

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Formalized.substNumerals (φ : V) (v : Fin k → V) :
    V :=
  ⌜ℒₒᵣ⌝.substs ⌜fun i ↦ numeral (v i)⌝ φ

lemma _root_.LO.Arith.Formalized.substNumerals_app_quote (σ : Semisentence ℒₒᵣ k) (v : Fin k → ℕ) :
    (substNumerals ⌜σ⌝ (v ·) : V) = ⌜((Rew.substs (fun i ↦ ‘↑(v i)’)) ▹ σ : Sentence ℒₒᵣ)⌝ := by
  dsimp [substNumerals]
  let w : Fin k → Semiterm ℒₒᵣ Empty 0 := fun i ↦ ‘↑(v i)’
  have : ⌜fun i ↦ numeral (v i : V)⌝ = (⌜fun i : Fin k ↦ ⌜w i⌝⌝ : V) := by
    apply nth_ext' (k : V) (by simp) (by simp)
    intro i hi; rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    simp [w]
  rw [this, quote_substs' (L := ℒₒᵣ)]

lemma _root_.LO.Arith.Formalized.substNumerals_app_quote_quote (σ : Semisentence ℒₒᵣ k) (π :
    Fin k → Semisentence ℒₒᵣ k) :
    substNumerals (⌜σ⌝ : V) (fun i ↦ ⌜π i⌝) =
        ⌜((Rew.substs (fun i ↦ ⌜π i⌝)) ▹ σ : Sentence ℒₒᵣ)⌝ := by
  have h := substNumerals_app_quote (V := V) σ (fun i ↦ ⌜π i⌝)
  simp only [quote_eq_encode] at h ⊢
  exact h

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.ssnum : Sg1.Semisentence 3 := .mkSigma
  “y p x. ∃ n, !numeralDef n x ∧ !p⌜ℒₒᵣ⌝.substs₁Def y n p” (by simp)

lemma _root_.LO.Arith.Formalized.substNumeral_defined : Sg1-Function₂ (substNumeral :
    V → V → V) via ssnum := by intro v; simp [ssnum, ⌜ℒₒᵣ⌝.substs₁_defined.df.iff, substNumeral]

@[simp] lemma _root_.LO.Arith.Formalized.eval_ssnum (v) :
    Semiformula.Evalbm V v ssnum.val ↔ v 0 = substNumeral (v 1) (v 2) :=
      substNumeral_defined.df.iff v

lemma _root_.LO.Arith.Formalized.eval_ssnum_oring {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1] (v :
    Fin 3 → V) :
    Semiformula.Evalbm V v ssnum.val ↔ v 0 = substNumeral (v 1) (v 2) := eval_ssnum v

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.ssnums : Sg1.Semisentence (k + 2) := .mkSigma
  “y p. ∃ n, !lenDef ↑k n ∧
    (⋀ i, ∃ z, !nthDef z n ↑(i : Fin k) ∧ !numeralDef z #i.succ.succ.succ.succ) ∧
    !p⌜ℒₒᵣ⌝.substsDef y n p” (by simp)

lemma _root_.LO.Arith.Formalized.substNumerals_defined :
    Arith.HierarchySymbol.DefinedFunction (fun v ↦ substNumerals (v 0) (v ·.succ) :
        (Fin (k + 1) → V) → V) ssnums := by
  intro v
  suffices
    (v 0 = ⌜ℒₒᵣ⌝.substs ⌜fun (i : Fin k) ↦ numeral (v i.succ.succ)⌝ (v 1)) ↔
      ∃ x, ↑k = len x ∧ (∀ (i : Fin k), x.[↑↑i] = numeral (v i.succ.succ)) ∧ v 0 =
        ⌜ℒₒᵣ⌝.substs x (v 1) by
    simpa [ssnums, ⌜ℒₒᵣ⌝.substs_defined.df.iff, substNumerals, numeral_eq_natCast] using this
  constructor
  · intro e
    refine ⟨_, by simp, by intro i; simp, e⟩
  · rintro ⟨w, hk, h, e⟩
    have : w = ⌜fun (i : Fin k) ↦ numeral (v i.succ.succ)⌝ := nth_ext' (k : V) hk.symm (by simp)
      (by intro i hi; rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩; simp [h])
    rcases this; exact e

@[simp] lemma _root_.LO.Arith.Formalized.eval_ssnums (v : Fin (k + 2) → V) :
    Semiformula.Evalbm V v ssnums.val ↔ v 0 = substNumerals (v 1) (fun i ↦ v i.succ.succ) :=
      substNumerals_defined.df.iff v

end «lp_section_1»

end Formalized
end Arith
end LO

namespace LO
namespace FirstOrder
namespace Arith

open LO.Arith LO.Arith.Formalized

variable {T : Theory ℒₒᵣ} [𝐈Sg1 wkn T]

section «lp_section_2»

/--
$\mathrm{diag}_i(\vec{x}) := (\forall \vec{y})\left[ \left(\bigwedge_j \mathrm{ssnums}(y_j, x_j,
\vec{x})\right) \to \theta_i(\vec{y}) \right]$
-/
def _root_.LO.FirstOrder.Arith.multidiag (θ : Semisentence ℒₒᵣ k) : Semisentence ℒₒᵣ k :=
  ∀^[k] (
    (Matrix.conjVec fun j : Fin k ↦ (Rew.substs <|
        #(j.addCast k) :> #(j.addNat k) :> fun l ↦ #(l.addNat k)) ▹ ssnums.val) ==>
    (Rew.substs fun j ↦ #(j.addCast k)) ▹ θ)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.multifixpoint (θ : Fin k → Semisentence ℒₒᵣ k) (i : Fin k) :
    Sentence ℒₒᵣ :=
  (Rew.substs fun j ↦ ⌜multidiag (θ j)⌝) ▹ (multidiag (θ i))

theorem _root_.LO.FirstOrder.Arith.multidiagonal (θ : Fin k → Semisentence ℒₒᵣ k) :
    T ⊢!. multifixpoint θ i <=> (Rew.substs fun j ↦ ⌜multifixpoint θ j⌝) ▹ (θ i) :=
  haveI : 𝐄𝐐 wkn T := Entailment.WeakerThan.trans (𝓣 := 𝐈Sg1) inferInstance inferInstance
  complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈Sg1 := ModelsTheory.of_provably_subtheory V 𝐈Sg1 T inferInstance
    suffices V ⊧/![] (multifixpoint θ i) ↔
      V ⊧/(fun i ↦ ⌜multifixpoint θ i⌝) (θ i) by simpa [models_iff]
    let t : Fin k → V := fun i ↦ ⌜multidiag (θ i)⌝
    have ht : ∀ i, substNumerals (t i) t = ⌜multifixpoint θ i⌝ := by
      intro i; simp [t, multifixpoint, substNumerals_app_quote_quote]
    calc
      V ⊧/![] (multifixpoint θ i) ↔ V ⊧/t (multidiag (θ i))                 := by
        simp [t, multifixpoint]
      _                      ↔ V ⊧/(fun i ↦ substNumerals (t i) t) (θ i) := by
        simp [multidiag, ← funext_iff]
      _                      ↔ V ⊧/(fun i ↦ ⌜multifixpoint θ i⌝) (θ i) := by simp [ht]

end «lp_section_2»

section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.diag (θ : Semisentence ℒₒᵣ 1) : Semisentence ℒₒᵣ 1 := multidiag θ

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.fixpoint (θ : Semisentence ℒₒᵣ 1) :
    Sentence ℒₒᵣ :=
  (diag θ)/[⌜diag θ⌝]

theorem _root_.LO.FirstOrder.Arith.diagonal (θ : Semisentence ℒₒᵣ 1) :
    T ⊢!. fixpoint θ <=> θ/[⌜fixpoint θ⌝] := by
  simpa [fixpoint, diag, multifixpoint, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    quote_cons, quote_matrix_empty] using
    (multidiagonal (T := T) (θ := fun _ : Fin 1 ↦ θ) (i := (0 : Fin 1)))

end «lp_section_3»

section «lp_section_4»

variable (U : Theory ℒₒᵣ) [U.Delta1Definable]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.bewₐ (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := U.provableₐ/[⌜σ⌝]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.consistentₐ : Sentence ℒₒᵣ := ∼U.bewₐ ⊥

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Consistentₐ : Theory ℒₒᵣ := {↑U.consistentₐ}

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐂𝐨𝐧[" U "]" => LO.FirstOrder.Theory.Consistentₐ U

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Inconsistentₐ : Theory ℒₒᵣ := {∼↑U.consistentₐ}

/-- Imported declaration from the Incompleteness formalization. -/
notation "¬𝐂𝐨𝐧[" U "]" => LO.FirstOrder.Theory.Inconsistentₐ U

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Theory.goedelₐ : Sentence ℒₒᵣ := fixpoint (∼U.provableₐ)

end «lp_section_4»

section «lp_section_5»

variable {U : Theory ℒₒᵣ} [U.Delta1Definable]

theorem _root_.LO.FirstOrder.Arith.provableₐ_D1 {σ} : U ⊢!. σ → T ⊢!. U.bewₐ σ := by
  intro h
  haveI : 𝐄𝐐 wkn T := Entailment.WeakerThan.trans (𝓣 := 𝐈Sg1) inferInstance inferInstance
  apply complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈Sg1 := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using provableₐ_of_provable (T := U) (V := V) h

theorem _root_.LO.FirstOrder.Arith.provableₐ_D2 {σ π} :
    T ⊢!. U.bewₐ (σ ==> π) ==> U.bewₐ σ ==> U.bewₐ π :=
  haveI : 𝐄𝐐 wkn T := Entailment.WeakerThan.trans (𝓣 := 𝐈Sg1) inferInstance inferInstance
  complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈Sg1 := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simp only [LogicalConnective.HomClass.map_imply, models_iff, Semiformula.eval_emb,
      Semiformula.eval_substs, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_fin_one,
      val_quote, Matrix.constant_eq_singleton, eval_provableₐ, Fin.isValue,
      LogicalConnective.Prop.arrow_eq, forall_const]
    intro hσπ hσ
    exact provableₐ_iff.mpr <| (by simpa using provableₐ_iff.mp hσπ) ⨀ provableₐ_iff.mp hσ

lemma _root_.LO.FirstOrder.Arith.provableₐ_sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ :
    Hierarchy Sg 1 σ) :
    T ⊢!. σ ==> U.bewₐ σ :=
  haveI : 𝐄𝐐 wkn T := Entailment.WeakerThan.trans (𝓣 := 𝐈Sg1) inferInstance inferInstance
  complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈Sg1 := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using sigma₁_complete (T := U) (V := V) hσ

theorem _root_.LO.FirstOrder.Arith.provableₐ_D3 {σ : Sentence ℒₒᵣ} :
    T ⊢!. U.bewₐ σ ==> U.bewₐ (U.bewₐ σ) := provableₐ_sigma₁_complete (by simp)

lemma _root_.LO.FirstOrder.Arith.goedel_iff_unprovable_goedel :
    T ⊢!. U.goedelₐ <=> ∼U.bewₐ U.goedelₐ := by
  simpa [Theory.goedelₐ, Theory.bewₐ] using diagonal (∼U.provableₐ)

open LO.Entailment LO.Entailment.FiniteContext

lemma _root_.LO.FirstOrder.Arith.provableₐ_D2_context {Γ σ π} (hσπ :
    Γ ⊢[T.alt]! (U.bewₐ (σ ==> π))) (hσ :
    Γ ⊢[T.alt]! U.bewₐ σ) :
    Γ ⊢[T.alt]! U.bewₐ π := of'! provableₐ_D2 ⨀ hσπ ⨀ hσ

lemma _root_.LO.FirstOrder.Arith.provableₐ_D3_context {Γ σ} (hσπ : Γ ⊢[T.alt]! U.bewₐ σ) :
    Γ ⊢[T.alt]! U.bewₐ (U.bewₐ σ) :=
  of'! provableₐ_D3 ⨀ hσπ

variable [ℕ ⊧ₘ* T] [𝐑₀ wkn U]

omit [𝐈Sg1 wkn T] in
lemma _root_.LO.FirstOrder.Arith.provableₐ_sound {σ} : T ⊢!. U.bewₐ σ → U ⊢! ↑σ := by
  intro h
  have : U.Provableₐ (⌜σ⌝ : ℕ) := by
    simpa [models₀_iff] using consequence_iff.mp (sound! (T := T) h) ℕ inferInstance
  simpa using this

lemma _root_.LO.FirstOrder.Arith.provableₐ_complete {σ} :
    U ⊢! ↑σ ↔ T ⊢!. U.bewₐ σ :=
  ⟨provableₐ_D1, provableₐ_sound⟩

end «lp_section_5»

section «lp_section_6»

variable (T)

variable [T.Delta1Definable]

open LO.Entailment LO.Entailment.FiniteContext

local notation "Gd" => T.goedelₐ

local notation "Con" => T.consistentₐ

local prefix:max "□" => T.bewₐ

lemma _root_.LO.FirstOrder.Arith.goedel_unprovable [Entailment.Consistent T] : T ⊬ ↑Gd := by
  intro h
  have hp : T ⊢! ↑□Gd := provableₐ_D1 h
  have hn : T ⊢! ∼↑□Gd := by simpa [provable₀_iff] using and_left! goedel_iff_unprovable_goedel ⨀ h
  exact not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable hp hn)
    inferInstance

lemma _root_.LO.FirstOrder.Arith.not_goedel_unprovable [ℕ ⊧ₘ* T] : T ⊬ ∼↑Gd := fun h ↦ by
  haveI : 𝐑₀ wkn T := Entailment.WeakerThan.trans (𝓣 := 𝐈Sg1) inferInstance inferInstance
  have : T ⊢!. □Gd :=
    Entailment.contra₂'! (and_right! goedel_iff_unprovable_goedel) ⨀ (by simpa [provable₀_iff]
      using h)
  have : T ⊢! ↑Gd := provableₐ_sound this
  exact not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable this h)
    (Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩)

lemma _root_.LO.FirstOrder.Arith.consistent_iff_goedel : T ⊢! ↑Con <=> ↑Gd := by
  apply iff_intro!
  · have bew_G : [∼Gd] ⊢[T.alt]! □Gd :=
    deductInv'! <| contra₂'! <| and_right! goedel_iff_unprovable_goedel
    have bew_not_bew_G : [∼Gd] ⊢[T.alt]! □(∼□Gd) := by
      have : T ⊢!. □(Gd ==> ∼□Gd) := provableₐ_D1 <| and_left! goedel_iff_unprovable_goedel
      exact provableₐ_D2_context (of'! this) bew_G
    have bew_bew_G : [∼Gd] ⊢[T.alt]! □□Gd := provableₐ_D3_context bew_G
    have : [∼Gd] ⊢[T.alt]! □⊥ :=
      provableₐ_D2_context (provableₐ_D2_context (of'! <| provableₐ_D1 <|
          efqImplyNot₁!) bew_not_bew_G) bew_bew_G
    simpa [provable₀_iff] using contra₂'! (deduct'! this)
  · have : [□⊥] ⊢[T.alt]! □Gd := by
      have : T ⊢!. □(⊥ ==> Gd) := provableₐ_D1 efq!
      exact provableₐ_D2_context (of'! this) (by simp)
    have : [□⊥] ⊢[T.alt]! ∼Gd :=
      of'! (contra₁'! <| and_left! <| goedel_iff_unprovable_goedel) ⨀ this
    simpa [provable₀_iff] using  contra₁'! (deduct'! this)

/-- Gödel's Second Incompleteness Theorem -/
theorem _root_.LO.FirstOrder.Arith.goedel_second_incompleteness [Entailment.Consistent T] :
    T ⊬ ↑Con :=
  fun h ↦
  goedel_unprovable T <| and_left! (consistent_iff_goedel T) ⨀ h

theorem _root_.LO.FirstOrder.Arith.inconsistent_unprovable [ℕ ⊧ₘ* T] : T ⊬ ∼↑Con := fun h ↦
  not_goedel_unprovable T <| contra₀'! (and_right! (consistent_iff_goedel T)) ⨀ h

theorem _root_.LO.FirstOrder.Arith.inconsistent_undecidable [ℕ ⊧ₘ* T] :
    Entailment.Undecidable T ↑Con := by
  haveI : Consistent T := Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩
  constructor
  · exact goedel_second_incompleteness T
  · exact inconsistent_unprovable T

instance [Entailment.Consistent T] : T swkn T + 𝐂𝐨𝐧[T] :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable (φ := ↑Con)
    (goedel_second_incompleteness T) (Entailment.by_axm _ (by simp))

instance [Entailment.Consistent T] : ℕ ⊧ₘ* 𝐂𝐨𝐧[T] := by
  suffices ℕ ⊧ₘ₀ T.consistentₐ by simpa [Models₀] using this
  suffices ¬T.Provableₐ ⌜⊥⌝ by simpa [models₀_iff] using  this
  intro H
  haveI : 𝐑₀ wkn T := Entailment.WeakerThan.trans (𝓣 := 𝐈Sg1) inferInstance inferInstance
  have : T ⊢! ⊥ := Arith.provableₐ_iff_provable₀.mp H
  have : Entailment.Inconsistent T := inconsistent_iff_provable_bot.mpr this
  exact Consistent.not_inconsistent this

instance [ℕ ⊧ₘ* T] : ℕ ⊧ₘ* T + 𝐂𝐨𝐧[T] :=
  haveI : Entailment.Consistent T := Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩
  ModelsTheory.add_iff.mpr ⟨inferInstance, inferInstance⟩

instance [ℕ ⊧ₘ* T] : T swkn T + ¬𝐂𝐨𝐧[T] :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable (φ := ∼↑Con)
    (inconsistent_unprovable T) (Entailment.by_axm _ (by simp))

end «lp_section_6»

end Arith
end FirstOrder
end LO

end «lp_nc_section_1»
