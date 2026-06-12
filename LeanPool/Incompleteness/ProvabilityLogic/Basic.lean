/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arith.DC
import LeanPool.Incompleteness.DC.Basic
import LeanPool.Incompleteness.Foundation.Modal.Logic.WellKnown

/-! # Basic -/


namespace LO

open LO.FirstOrder LO.FirstOrder.DerivabilityCondition
open LO.Modal
open LO.Modal.Hilbert

variable {α : Type u}
variable [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T U : Theory L}


namespace ProvabilityLogic

/-- Mapping modal prop vars to first-order sentence -/
def Realization (L) := ℕ → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def _root_.LO.ProvabilityLogic.Realization.interpret
  {T U : FirstOrder.Theory L}
  (f : Realization L) (𝔅 : ProvabilityPredicate T U) : Formula ℕ → FirstOrder.Sentence L
  | .atom a => f a
  | □φ => 𝔅 (f.interpret 𝔅 φ)
  | ⊥ => ⊥
  | φ ==> ψ => (f.interpret 𝔅 φ) ==> (f.interpret 𝔅 ψ)

/-- Imported declaration from the Incompleteness formalization. -/
class ArithmeticalSound (Λ : Modal.Logic) (𝔅 : ProvabilityPredicate T U) where
  sound : ∀ {φ}, (φ ∈ Λ) → (∀ {f : Realization L}, U ⊢!. (f.interpret 𝔅 φ))

/-- Imported declaration from the Incompleteness formalization. -/
class ArithmeticalComplete (Λ : Modal.Logic) (𝔅 : ProvabilityPredicate T U) where
  complete : ∀ {φ}, (∀ {f : Realization L}, U ⊢!. (f.interpret 𝔅 φ)) → (φ ∈ Λ)

section «lp_section_1»

open Entailment
open Modal
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [T wkn U]
         {𝔅 : ProvabilityPredicate T U}

lemma arithmetical_soundness_N (h : (Hilbert.N) ⊢! φ) : ∀ {f :
    Realization L}, U ⊢!. (f.interpret 𝔅 φ) := by
  intro f;
  induction h using Hilbert.Deduction.rec! with
  | maxm hp => simp at hp;
  | nec ihp => exact Entailment.WeakerThan.pbl (𝓢 := T.alt) (𝔅.spec ihp);
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | imply₁ => exact imply₁!;
  | imply₂ => exact imply₂!;
  | ec => exact elimContraNeg!;


lemma arithmetical_soundness_GL [Diagonalization T] [𝔅.HBL] (h : (Hilbert.GL) ⊢! φ) : ∀ {f :
    Realization L}, U ⊢!. (f.interpret 𝔅 φ) := by
  intro f;
  induction h using Hilbert.Deduction.rec! with
  | maxm hp =>
    rcases (by simpa using hp) with (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact D2_shift;
    · exact FLT_shift;
  | nec ihp => exact D1_shift ihp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | imply₁ => exact imply₁!;
  | imply₂ => exact imply₂!;
  | ec => exact elimContraNeg!;

end «lp_section_1»


section «lp_section_2»

instance (T : Theory ℒₒᵣ) [𝐈Sg1 wkn T] [T.Delta1Definable] :
    ArithmeticalSound (Logic.GL) (T.standardDP T) :=
  ⟨arithmetical_soundness_GL⟩

end «lp_section_2»


end ProvabilityLogic
end LO
