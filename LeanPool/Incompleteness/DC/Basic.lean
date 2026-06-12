/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Theory
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental
import LeanPool.Incompleteness.ToFoundation.Basic

/-! # Basic -/


namespace LO
namespace FirstOrder

namespace Theory
namespace Alt

variable {L : Language} {T U : Theory L}

instance [s : T wkn U] : T wkn U.alt.thy := s

instance [s : T wkn U] : T.alt wkn U.alt := ⟨fun _ b ↦ s.pbl b⟩

end Alt
end Theory


namespace DerivabilityCondition

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

/-- Imported declaration from the Incompleteness formalization. -/
structure ProvabilityPredicate (T₀ : Theory L) (T : Theory L) where
  /-- Imported declaration from the Incompleteness formalization. -/
  prov : Semisentence L 1
  spec {σ : Sentence L} : T ⊢!. σ → T₀ ⊢!. prov/[⌜σ⌝]

namespace ProvabilityPredicate

variable {T₀ T : Theory L}

/-- Imported declaration from the Incompleteness formalization. -/
@[coe] def pr (𝔅 : ProvabilityPredicate T₀ T) (σ : Sentence L) : Sentence L := 𝔅.prov/[⌜σ⌝]

instance : CoeFun (ProvabilityPredicate T₀ T) (fun _ => Sentence L → Sentence L) := ⟨pr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def con (𝔅 : ProvabilityPredicate T₀ T) : Sentence L := ∼(𝔅 ⊥)

end ProvabilityPredicate

/-- Imported declaration from the Incompleteness formalization. -/
class Diagonalization (T : Theory L) where
  /-- Imported declaration from the Incompleteness formalization. -/
  fixpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢!. fixpoint θ <=> θ/[⌜fixpoint θ⌝]

namespace ProvabilityPredicate

variable {T₀ T : Theory L}

/-- Imported declaration from the Incompleteness formalization. -/
class HBL2 (𝔅 : ProvabilityPredicate T₀ T) where
  D2 {σ τ : Sentence L} : T₀ ⊢!. 𝔅 (σ ==> τ) ==> (𝔅 σ) ==> (𝔅 τ)

/-- Imported declaration from the Incompleteness formalization. -/
class HBL3 (𝔅 : ProvabilityPredicate T₀ T) where
  D3 {σ : Sentence L} : T₀ ⊢!. (𝔅 σ) ==> 𝔅 (𝔅 σ)

/-- Imported declaration from the Incompleteness formalization. -/
class HBL (𝔅 : ProvabilityPredicate T₀ T) extends 𝔅.HBL2, 𝔅.HBL3

/-- Imported declaration from the Incompleteness formalization. -/
class Loeb (𝔅 : ProvabilityPredicate T₀ T) where
  LT {σ : Sentence L} : T ⊢!. (𝔅 σ) ==> σ → T ⊢!. σ

/-- Imported declaration from the Incompleteness formalization. -/
class FormalizedLoeb (𝔅 : ProvabilityPredicate T₀ T) where
  FLT {σ : Sentence L} : T₀ ⊢!. 𝔅 ((𝔅 σ) ==> σ) ==> (𝔅 σ)

/-- Imported declaration from the Incompleteness formalization. -/
class Rosser (𝔅 : ProvabilityPredicate T₀ T) where
  Ro {σ : Sentence L} : T ⊢!. ∼σ → T₀ ⊢!. ∼(𝔅 σ)

section «lp_section_1»

open LO.Entailment

variable [L.DecidableEq]
         {T₀ T : Theory L} [T₀ wkn T]
         {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL]
         {σ τ : Sentence L}

omit [L.DecidableEq] [T₀ wkn T] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D1 : T ⊢!. σ → T₀ ⊢!. (𝔅 σ) := 𝔅.spec
alias D2 := HBL2.D2
alias D3 := HBL3.D3
alias LT := Loeb.LT
alias FLT := FormalizedLoeb.FLT
alias Ro := Rosser.Ro

omit [L.DecidableEq] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D1_shift : T ⊢!. σ → T ⊢!. (𝔅 σ) := by
  intro h;
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt);
  apply D1 h;

omit [L.DecidableEq] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D2_shift [𝔅.HBL2] : T ⊢!. 𝔅 (σ ==> τ) ==> (𝔅 σ) ==> (𝔅 τ) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt);
  apply D2;

omit [L.DecidableEq] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D3_shift [𝔅.HBL3] : T ⊢!. (𝔅 σ) ==> 𝔅 (𝔅 σ) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt);
  apply D3;

omit [L.DecidableEq] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma FLT_shift [𝔅.FormalizedLoeb] : T ⊢!. 𝔅 ((𝔅 σ) ==> σ) ==> (𝔅 σ) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt);
  apply 𝔅.FLT;

omit [L.DecidableEq] [T₀ wkn T] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D2' [𝔅.HBL2] [Entailment.ModusPonens T] : T₀ ⊢!. 𝔅 (σ ==> τ) → T₀ ⊢!. (𝔅 σ) ==> (𝔅 τ) := by
  intro h;
  exact D2 ⨀ h;

omit [L.DecidableEq] [T₀ wkn T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_distribute_imply (h : T ⊢!. σ ==> τ) : T₀ ⊢!. (𝔅 σ) ==> (𝔅 τ) := D2' <| D1 h

omit [L.DecidableEq] [T₀ wkn T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_distribute_iff (h : T ⊢!. σ <=> τ) : T₀ ⊢!. (𝔅 σ) <=> (𝔅 τ) := by
  apply iff_intro!;
  · exact prov_distribute_imply <| and₁'! h;
  · exact prov_distribute_imply <| and₂'! h;

omit [L.DecidableEq] [T₀ wkn T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_distribute_and : T₀ ⊢!. 𝔅 (σ ⋏ τ) ==> (𝔅 σ) ⋏ (𝔅 τ) := by
  have h₁ : T₀ ⊢!. 𝔅 (σ ⋏ τ) ==> (𝔅 σ) := D2' <| D1 and₁!;
  have h₂ : T₀ ⊢!. 𝔅 (σ ⋏ τ) ==> (𝔅 τ) := D2' <| D1 and₂!;
  exact imply_right_and! h₁ h₂;

omit [L.DecidableEq] [T₀ wkn T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_distribute_and' :
    T₀ ⊢!. 𝔅 (σ ⋏ τ) → T₀ ⊢!. (𝔅 σ) ⋏ (𝔅 τ) :=
  fun h => prov_distribute_and ⨀ h

omit [L.DecidableEq] [T₀ wkn T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_collect_and : T₀ ⊢!. (𝔅 σ) ⋏ (𝔅 τ) ==> 𝔅 (σ ⋏ τ) := by
  have h₁ : T₀ ⊢!. (𝔅 σ) ==> 𝔅 (τ ==> σ ⋏ τ) := prov_distribute_imply <| and₃!;
  have h₂ : T₀ ⊢!. 𝔅 (τ ==> σ ⋏ τ) ==> (𝔅 τ) ==> 𝔅 (σ ⋏ τ) := D2;
  apply and_imply_iff_imply_imply'!.mpr;
  exact imp_trans''! h₁ h₂;

end «lp_section_1»

end ProvabilityPredicate

variable {T₀ T : Theory L} {𝔅 : ProvabilityPredicate T₀ T}

open LO.Entailment
open Diagonalization
open ProvabilityPredicate

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate.goedel [Diagonalization T₀] (𝔅 :
    ProvabilityPredicate T₀ T) :
    Sentence L :=
  fixpoint T₀ “x. ¬!𝔅.prov x”

section «lp_section_2»

variable [Diagonalization T₀]

local notation "γ" => 𝔅.goedel

lemma goedel_spec : T₀ ⊢!. γ <=> ∼𝔅 γ := by
  convert (diag (T := T₀) “x. ¬!𝔅.prov x”);
  simp [goedel, ← TransitiveRewriting.comp_app, Rew.substs_comp_substs];
  rfl;

variable [T₀ wkn T]

private lemma goedel_specAux₁ : T ⊢!. γ <=> ∼𝔅 γ := WeakerThan.pbl (𝓢 := T₀.alt) goedel_spec

private lemma goedel_specAux₂ [L.DecidableEq] :
    T ⊢!. ∼γ ==> 𝔅 γ :=
  contra₂'! <| and₂'! goedel_specAux₁

end «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate.GoedelSound (𝔅 :
    ProvabilityPredicate T₀ T) [Diagonalization T₀] where
  γ_sound : T ⊢!. 𝔅 𝔅.goedel → T ⊢!. 𝔅.goedel

open GoedelSound

section «lp_section_3»

variable [L.DecidableEq] [T₀ wkn T] [Diagonalization T₀]

local notation "γ" => 𝔅.goedel

variable [Entailment.Consistent T]

omit [L.DecidableEq] in
theorem unprovable_goedel : T ⊬. γ := by
  intro h;
  have h₁ : T ⊢!. 𝔅 γ := Entailment.WeakerThan.pbl (𝓢 := T₀.alt) (𝔅.spec h);
  have h₂ : T ⊢!. ∼𝔅 γ := (and₁'! goedel_specAux₁) ⨀ h;
  have : T ⊢!. ⊥ := (negEquiv'!.mp h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this)
  contradiction;

theorem unrefutable_goedel [𝔅.GoedelSound] :
    T ⊬. ∼γ := by
  classical
  intro h₂;
  have h₁ : T ⊢!. γ := γ_sound <| goedel_specAux₂ ⨀ h₂;
  have : T ⊢!. ⊥ := (negEquiv'!.mp h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this);
  contradiction;

omit [L.DecidableEq] in
theorem goedel_independent [𝔅.GoedelSound] : Entailment.Undecidable T ↑γ := by
  classical
  suffices T ⊬. γ ∧ T ⊬. ∼γ by simpa [Entailment.Undecidable, not_or, unprovable₀_iff] using this
  constructor
  · apply unprovable_goedel
  · apply unrefutable_goedel

omit [L.DecidableEq] in
theorem first_incompleteness [𝔅.GoedelSound]
  : ¬Entailment.Complete T :=
    Entailment.incomplete_iff_exists_undecidable.mpr ⟨γ, goedel_independent⟩

end «lp_section_3»

section «lp_section_4»

variable [𝔅.HBL]

section

variable [L.DecidableEq]

local notation "γ" => 𝔅.goedel

lemma formalized_consistent_of_existance_unprovable :
    T₀ ⊢!. ∼(𝔅 σ) ==> 𝔅.con :=
  contra₀'! <| 𝔅.D2 ⨀ (D1 efq!)

private lemma consistency_lemma_1 [T₀ wkn U] :
    (U ⊢!. 𝔅.con ==> ∼(𝔅 σ)) ↔ (U ⊢!. (𝔅 σ) ==> 𝔅 (∼σ)) := by
  constructor;
  · intro H;
    exact contra₃'! <| imp_trans''! (WeakerThan.pbl (𝓢 :=
      T₀.alt) formalized_consistent_of_existance_unprovable) H;
  · intro H
    apply contra₀'!
    have : T₀ ⊢!. (𝔅 σ) ⋏ 𝔅 (∼σ) ==> 𝔅 ⊥ :=
      imp_trans''! prov_collect_and <| prov_distribute_imply lac!;
    have : U ⊢!. (𝔅 σ) ==> 𝔅 (∼σ) ==> 𝔅 ⊥ :=
      WeakerThan.pbl <| and_imply_iff_imply_imply'!.mp <| this;
    exact this ⨀₁ H;

omit [L.DecidableEq] in
private lemma consistency_lemma_2 : T₀ ⊢!. ((𝔅 σ) ==> 𝔅 (∼σ)) ==> (𝔅 σ) ==> 𝔅 ⊥ := by
  have : T ⊢!. σ ==> ∼σ ==> ⊥ := and_imply_iff_imply_imply'!.mp lac!
  have : T₀ ⊢!. (𝔅 σ) ==> 𝔅 (∼σ ==> ⊥)  := prov_distribute_imply this;
  have : T₀ ⊢!. (𝔅 σ) ==> (𝔅 (∼σ) ==> 𝔅 ⊥) := imp_trans''! this D2;
  -- TODO: more simple proof
  apply FiniteContext.deduct'!;
  apply FiniteContext.deduct!;
  have d₁ : [(𝔅 σ), (𝔅 σ) ==> 𝔅 (∼σ)] ⊢[T₀.alt]! (𝔅 σ) := FiniteContext.by_axm!;
  have d₂ : [(𝔅 σ), (𝔅 σ) ==> 𝔅 (∼σ)] ⊢[T₀.alt]! (𝔅 σ) ==> 𝔅 (∼σ) := FiniteContext.by_axm!;
  have d₃ : [(𝔅 σ), (𝔅 σ) ==> 𝔅 (∼σ)] ⊢[T₀.alt]! 𝔅 (∼σ) := d₂ ⨀ d₁;
  exact ((FiniteContext.of'! this) ⨀ d₁) ⨀ d₃;

end

variable [Diagonalization T₀]

local notation "γ" => 𝔅.goedel

/-- Formalized First Incompleteness Theorem -/
theorem _root_.LO.FirstOrder.DerivabilityCondition.formalized_unprovable_goedel
    [L.DecidableEq] [T₀ wkn T] :
    T ⊢!. 𝔅.con ==> ∼𝔅 γ := by
  have h₁ : T₀ ⊢!. 𝔅 γ ==> 𝔅 (𝔅 γ) := D3;
  have h₂ : T ⊢!. 𝔅 γ ==> ∼γ := WeakerThan.pbl <| contra₁'! <| and₁'! goedel_spec;
  have h₃ : T₀ ⊢!. 𝔅 (𝔅 γ) ==> 𝔅 (∼γ) := prov_distribute_imply h₂;
  exact WeakerThan.pbl <| contra₀'! <| consistency_lemma_2 ⨀ (imp_trans''! h₁ h₃);

theorem _root_.LO.FirstOrder.DerivabilityCondition.iff_goedel_consistency
    [L.DecidableEq] [T₀ wkn T] : T ⊢!. γ <=> 𝔅.con :=
  iff_trans''! goedel_specAux₁ <| iff_intro! (WeakerThan.pbl (𝓢 :=
    T₀.alt) formalized_consistent_of_existance_unprovable) formalized_unprovable_goedel

theorem _root_.LO.FirstOrder.DerivabilityCondition.unprovable_consistency
    [L.DecidableEq] [T₀ wkn T] [Entailment.Consistent T] :
    T ⊬. 𝔅.con :=
  unprovable_iff! iff_goedel_consistency |>.mp <| unprovable_goedel

theorem _root_.LO.FirstOrder.DerivabilityCondition.unrefutable_consistency
    [L.DecidableEq] [T₀ wkn T] [Entailment.Consistent T] [𝔅.GoedelSound] :
    T ⊬. ∼𝔅.con :=
  unprovable_iff! (neg_replace_iff'! <| iff_goedel_consistency) |>.mp <| unrefutable_goedel

end «lp_section_4»


section «lp_section_5»

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate.kreisel [Diagonalization T₀]
    (𝔅 : ProvabilityPredicate T₀ T)
    (σ : Sentence L) : Sentence L := fixpoint T₀ “x. !𝔅.prov x → !σ”

section «lp_section_6»

variable {𝔅 : ProvabilityPredicate T₀ T} [L.DecidableEq] [𝔅.HBL] [Diagonalization T₀]

local notation "κ(" σ ")" => 𝔅.kreisel σ

omit [L.DecidableEq] [𝔅.HBL] in
lemma _root_.LO.FirstOrder.DerivabilityCondition.kreisel_spec
    (σ : Sentence L) : T₀ ⊢!. κ(σ) <=> (𝔅 (κ(σ)) ==> σ) := by
  convert (diag (T := T₀) “x. !𝔅.prov x → !σ”);
  simp [kreisel, ← TransitiveRewriting.comp_app, Rew.substs_comp_substs];
  rfl;

omit [L.DecidableEq] in
private lemma kreisel_specAux₁ [T₀ wkn T] (σ : Sentence L) :
    T₀ ⊢!. 𝔅 κ(σ) ==> (𝔅 σ) :=
  (imp_trans''! (D2 ⨀ (D1 (WeakerThan.pbl <| and₁'! (kreisel_spec σ)))) D2) ⨀₁ D3

omit [L.DecidableEq] [𝔅.HBL] in
private lemma kreisel_specAux₂ (σ : Sentence L) :
    T₀ ⊢!. (𝔅 κ(σ) ==> σ) ==> κ(σ) :=
  and₂'! (kreisel_spec σ)

end «lp_section_6»

section «lp_section_7»

variable [L.DecidableEq] [T₀ wkn T] [Diagonalization T₀] [𝔅.HBL]

local notation "κ(" σ ")" => 𝔅.kreisel σ

omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.loeb_theorm
    (H : T ⊢!. (𝔅 σ) ==> σ) : T ⊢!. σ := by
  have d₁ : T ⊢!. 𝔅 (𝔅.kreisel σ) ==> σ := imp_trans''! (WeakerThan.pbl (kreisel_specAux₁ σ)) H;
  have d₂ : T ⊢!. 𝔅 (𝔅.kreisel σ)     :=
    WeakerThan.pbl (𝓢 := T₀.alt) (D1 <| WeakerThan.pbl (kreisel_specAux₂ σ) ⨀ d₁);
  exact d₁ ⨀ d₂;

instance : 𝔅.Loeb := ⟨loeb_theorm (T := T)⟩

omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.formalized_loeb_theorem
    [L.DecidableEq] : T₀ ⊢!. 𝔅 ((𝔅 σ) ==> σ) ==> (𝔅 σ) := by
  have hκ₁ : T₀ ⊢!. 𝔅 (κ(σ)) ==> (𝔅 σ) := kreisel_specAux₁ σ;
  have : T₀ ⊢!. ((𝔅 σ) ==> σ) ==> (𝔅 κ(σ) ==> σ) := replace_imply_left! hκ₁;
  have : T ⊢!. ((𝔅 σ) ==> σ) ==> κ(σ) :=
    WeakerThan.pbl (𝓢 := T₀.alt) <| imp_trans''! this (kreisel_specAux₂ σ);
  exact imp_trans''! (D2 ⨀ (D1 this)) hκ₁;

instance : 𝔅.FormalizedLoeb := ⟨formalized_loeb_theorem (T := T)⟩

end «lp_section_7»

variable [Entailment.Consistent T]

lemma _root_.LO.FirstOrder.DerivabilityCondition.unprovable_consistency_via_loeb
    [𝔅.Loeb] : T ⊬. 𝔅.con := by
  by_contra hC;
  have : T ⊢!. ⊥ := Loeb.LT <| negEquiv'!.mp hC;
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <|
        inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this)
  contradiction

variable [L.DecidableEq] [Diagonalization T₀] [T₀ wkn T] [𝔅.HBL] [𝔅.GoedelSound]

lemma _root_.LO.FirstOrder.DerivabilityCondition.formalized_unprovable_not_consistency
  : T ⊬. 𝔅.con ==> ∼𝔅 (∼𝔅.con) := by
  by_contra hC;
  have : T ⊢!. ∼𝔅.con := Loeb.LT <| contra₁'! hC;
  have : T ⊬. ∼𝔅.con := unrefutable_consistency;
  contradiction;

lemma _root_.LO.FirstOrder.DerivabilityCondition.formalized_unrefutable_goedel
  : T ⊬. 𝔅.con ==> ∼𝔅 (∼𝔅.goedel) := by
  by_contra hC;
  have : T ⊬. 𝔅.con ==> ∼𝔅 (∼𝔅.con)  := formalized_unprovable_not_consistency;
  have : T ⊢!. 𝔅.con ==> ∼𝔅 (∼𝔅.con) :=
    imp_trans''! hC <| WeakerThan.pbl <| and₁'! <| neg_replace_iff'! <| prov_distribute_iff <|
        neg_replace_iff'! iff_goedel_consistency;
  contradiction;

end «lp_section_5»

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate.rosser
    [Diagonalization T₀]
    (𝔅 : ProvabilityPredicate T₀ T) : Sentence L :=
  fixpoint T₀ “x. ¬!𝔅.prov x”

section «lp_section_8»

local notation "ρ" => 𝔅.rosser

variable [Diagonalization T₀] [𝔅.Rosser]

omit [𝔅.Rosser] in
lemma _root_.LO.FirstOrder.DerivabilityCondition.rosser_spec : T₀ ⊢!. ρ <=> ∼(𝔅 ρ) :=
  goedel_spec

omit [𝔅.Rosser] in
private lemma rosser_specAux₁ [T₀ wkn T] : T ⊢!. ρ <=> ∼(𝔅 ρ) := goedel_specAux₁

end «lp_section_8»

section «lp_section_9»

variable [L.DecidableEq] [Diagonalization T₀] [T₀ wkn T] [Entailment.Consistent T] [𝔅.Rosser]

local notation "ρ" => 𝔅.rosser

omit [L.DecidableEq] [𝔅.Rosser] in
lemma _root_.LO.FirstOrder.DerivabilityCondition.unprovable_rosser : T ⊬. ρ :=
  unprovable_goedel

omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.unrefutable_rosser : T ⊬. ∼ρ := by
  intro hnρ;
  have hρ : T ⊢!. ρ := WeakerThan.pbl <| (and₂'! rosser_spec) ⨀ (Ro hnρ);
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr <|
    by simpa [provable₀_iff] using (negEquiv'!.mp hnρ) ⨀ hρ;
  contradiction

omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.rosser_independent :
    Entailment.Undecidable T ↑ρ := by
  suffices T ⊬. ρ ∧ T ⊬. ∼ρ by simpa [Entailment.Undecidable, not_or, unprovable₀_iff] using this;
  constructor
  · apply unprovable_rosser
  · apply unrefutable_rosser

omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.rosser_first_incompleteness
    (𝔅 : ProvabilityPredicate T₀ T) [𝔅.Rosser] :
    ¬Entailment.Complete T :=
  Entailment.incomplete_iff_exists_undecidable.mpr ⟨𝔅.rosser, rosser_independent  ⟩

omit [Diagonalization T₀] [Consistent T]
omit [L.DecidableEq] in
/-- If `𝔅` satisfies Rosser provability condition, then `𝔅.con` is provable in `T`. -/
theorem _root_.LO.FirstOrder.DerivabilityCondition.kriesel_remark : T ⊢!. 𝔅.con := by
  have : T₀ ⊢!. ∼𝔅 ⊥ := Ro (negEquiv'!.mpr (by simp));
  exact WeakerThan.pbl <| this;

end «lp_section_9»

end DerivabilityCondition

end FirstOrder
end LO
