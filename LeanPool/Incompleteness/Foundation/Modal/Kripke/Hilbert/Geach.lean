/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Hilbert.Geach
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Completeness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness

/-! # Geach -/


namespace LO
namespace Modal

open Formula.Kripke

namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev MultiGeacheanConfluentFrameClass (G : Set Geachean.Taple) :
    FrameClass :=
  { F | (MultiGeachean G) F.Rel }

instance : (MultiGeacheanConfluentFrameClass G).IsNonempty := by
  use ⟨Unit, fun _ _ => True⟩;
  intros t ht x y z h;
  use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }

instance _root_.LO.Modal.Kripke.MultiGeacheanFrameClass.isDefinedByGeachAxioms (G) :
    (MultiGeacheanConfluentFrameClass G).DefinedBy
      (G.image (fun t => Axioms.Geach t (.atom 0))) := by
  unfold MultiGeacheanConfluentFrameClass MultiGeachean Axioms.Geach;
  constructor;
  intro F;
  constructor;
  · rintro hF φ ⟨g, ⟨hg, rfl⟩⟩ V x h;
    obtain ⟨y, Rxy, hbp⟩ := Satisfies.multidia_def.mp h;
    apply Satisfies.multibox_def.mpr;
    intro z Rxz;
    apply Satisfies.multidia_def.mpr;
    obtain ⟨u, Ryu, Rzu⟩ := hF g hg ⟨Rxy, Rxz⟩;
    use u;
    constructor;
    · assumption;
    · exact (Satisfies.multibox_def.mp hbp) Ryu;
  · rintro h g hg x y z ⟨Rxy, Rxz⟩;
    let V : Kripke.Valuation F := fun v _ => y ≺^[g.m] v;
    have : Satisfies ⟨F, V⟩ x (◇^[g.i](□^[g.m](.atom 0))) := by
      apply Satisfies.multidia_def.mpr;
      use y;
      constructor;
      · assumption;
      · apply Satisfies.multibox_def.mpr;
        aesop;
    have : Satisfies ⟨F, V⟩ x (□^[g.j](◇^[g.n]Formula.atom 0)) :=
      h (Axioms.Geach g (.atom 0)) (by tauto) V x this;
    have : Satisfies ⟨F, V⟩ z (◇^[g.n]Formula.atom 0) := Satisfies.multibox_def.mp this Rxz;
    obtain ⟨u, Rzu, Ryu⟩ := Satisfies.multidia_def.mp this;
    exact ⟨u, Ryu, Rzu⟩;

instance _root_.LO.Modal.Kripke.MultiGeacheanFrameClass.isDefinedByGeachHilbertAxioms (ts)
  : (MultiGeacheanConfluentFrameClass ts).DefinedBy (Hilbert.Geach ts).axioms :=
  FrameClass.definedBy_with_axiomK (MultiGeacheanFrameClass.isDefinedByGeachAxioms ts)


section «lp_section_1»

variable {F : Frame}

lemma reflexive_of_validate_AxiomT (h : F ⊧ (Axioms.T (.atom 0))) : Std.Refl F.Rel := by
  have : ValidOnFrame F (Axioms.T (.atom 0)) → Std.Refl F.Rel := by
    simpa [Axioms.Geach, MultiGeachean, ←Geachean.reflexive_def] using
    MultiGeacheanFrameClass.isDefinedByGeachAxioms {⟨0, 0, 1, 0⟩} |>.defines F |>.mpr;
  exact this h;

lemma transitive_of_validate_AxiomFour (h : F ⊧ (Axioms.Four (.atom 0))) : IsTrans F.World F.Rel :=
  by
  have : ValidOnFrame F (Axioms.Four (.atom 0)) → IsTrans F.World F.Rel := by
    simpa [Axioms.Geach, MultiGeachean, ←Geachean.transitive_def] using
    MultiGeacheanFrameClass.isDefinedByGeachAxioms {⟨0, 2, 1, 0⟩} |>.defines F |>.mpr;
  exact this h;

end «lp_section_1»

end Kripke



namespace Kripke

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Entailment
open FormulaSet
open canonicalFrame
open MaximalConsistentSet

lemma _root_.LO.Modal.Kripke.canonicalFrame.multigeachean_of_provable_geach
  (hG : ∀ g ∈ G, ∀ φ, 𝓢 ⊢! ◇^[g.i](□^[g.m]φ) ==> □^[g.j](◇^[g.n]φ))
  : MultiGeachean G (canonicalFrame 𝓢).Rel := by
  intro t ht;
  rintro X Y Z ⟨RXY, RXZ⟩;
  have ⟨U, hU⟩ := lindenbaum (𝓢 := 𝓢) (T := □''⁻¹^[t.m]Y.1 ∪ □''⁻¹^[t.n]Z.1) <| by
    apply intro_union_consistent;
    rintro Γ Δ ⟨hΓ, hΔ⟩ hC;
    replace hΓ : ∀ φ ∈ Γ, □^[t.m]φ ∈ Y := fun φ hpp => hΓ φ hpp;
    have hΓconj : □^[t.m]⋀Γ ∈ Y := iff_mem_multibox_conj.mpr hΓ;
    replace hΔ : ∀ φ ∈ Δ, □^[t.n]φ ∈ Z := fun φ hpp => hΔ φ hpp;
    have hZ₁ : □^[t.n]⋀Δ ∈ Z := iff_mem_multibox_conj.mpr hΔ;
    have : □^[t.j](◇^[t.n]⋀Γ) ∈ X := MaximalConsistentSet.mdp
      (membership_iff.mpr <| Context.of! (hG t ht _))
      (multirel_def_multidia.mp RXY hΓconj)
    have hZ₂ : ◇^[t.n]⋀Γ ∈ Z := multirel_def_multibox.mp RXZ this;
    have : 𝓢 ⊢! □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ==> ⊥ := by {
      apply and_imply_iff_imply_imply'!.mpr;
      exact imp_trans''!
        (show _ ⊢! □^[t.n]⋀Δ ==> □^[t.n](∼⋀Γ) by
          exact imply_multibox_distribute'! <| contra₁'! <|
            imp_trans''! (and_imply_iff_imply_imply'!.mp hC) (and₂'! negEquiv!))
        (show _ ⊢! □^[t.n](∼⋀Γ) ==> (◇^[t.n]⋀Γ) ==> ⊥ by
          exact imp_trans''! (contra₁'! <| and₁'! <| multidia_duality!) (and₁'! negEquiv!));
    }
    have : 𝓢 ⊬ □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ==> ⊥ :=
      (def_consistent.mp (Z.consistent)) (Γ := [□^[t.n]⋀Δ, ◇^[t.n]⋀Γ]) <| by
      suffices □^[t.n]⋀Δ ∈ ↑Z ∧ ◇^[t.n]⋀Γ ∈ ↑Z by simpa;
      constructor <;> assumption;
    contradiction;
  use U;
  simp only [Set.union_subset_iff] at hU;
  constructor;
  · apply multirel_def_multibox.mpr; apply hU.1;
  · apply multirel_def_multibox.mpr; apply hU.2;

end Kripke


namespace Hilbert
namespace Geach

open Kripke

instance _root_.LO.Modal.Hilbert.Geach.Kripke.sound :
    Sound (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) :=
  inferInstance

instance _root_.LO.Modal.Hilbert.Geach.Kripke.Consistent :
    Entailment.Consistent (Hilbert.Geach G) :=
  Kripke.Hilbert.consistent_of_FrameClass (Kripke.MultiGeacheanConfluentFrameClass G)

instance _root_.LO.Modal.Hilbert.Geach.Kripke.Canonical :
    Canonical (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) :=
  ⟨by
  apply canonicalFrame.multigeachean_of_provable_geach;
  intro t ht φ;
  apply Hilbert.Deduction.maxm!;
  unfold Hilbert.axiomInstances;
  use Axioms.Geach t (.atom 0);
  constructor;
  · simp only [];
    right;
    aesop;
  · use (fun _ => φ); simp;
⟩

instance _root_.LO.Modal.Hilbert.Geach.Kripke.Complete :
    Complete (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) :=
  inferInstance

end Geach
end Hilbert


end Modal
end LO
