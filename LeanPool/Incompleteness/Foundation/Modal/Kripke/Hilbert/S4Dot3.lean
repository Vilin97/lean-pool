/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S4
import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomDot3

/-! # S4Dot3 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveTransitiveConnectedFrameClass :
    FrameClass :=
  { F | Std.Refl F ∧ IsTrans F.World F.Rel ∧ Connected F }

instance _root_.LO.Modal.Kripke.ReflexiveTransitiveConnectedFrameClass.DefinedByS4Dot3Axioms
  : FrameClass.DefinedBy Kripke.ReflexiveTransitiveConnectedFrameClass Hilbert.S4Dot3.axioms := by
  rw [
    (show ReflexiveTransitiveConnectedFrameClass =
      ReflexiveTransitiveFrameClass ∩ ConnectedFrameClass by aesop),
    (show Hilbert.S4Dot3.axioms = Hilbert.S4.axioms ∪ {Axioms.Dot3 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter Kripke.ReflexiveTransitiveFrameClass (Hilbert.S4.axioms)
    ConnectedFrameClass {Axioms.Dot3 (.atom 0) (.atom 1)};

instance : Kripke.ReflexiveTransitiveConnectedFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => True⟩;
  constructor
  · exact ⟨fun _ => trivial⟩
  · constructor
    · exact ⟨fun _ _ _ _ _ => trivial⟩
    · intro _ _ _ _
      exact Or.inl trivial


namespace Hilbert
namespace S4Dot3

instance _root_.LO.Modal.Hilbert.S4Dot3.Kripke.sound :
    Sound (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass :=
  inferInstance

instance _root_.LO.Modal.Hilbert.S4Dot3.Kripke.consistent :
    Entailment.Consistent (Hilbert.S4Dot3) :=
  Kripke.Hilbert.consistent_of_FrameClass Kripke.ReflexiveTransitiveConnectedFrameClass


open
  Kripke
  MaximalConsistentSet
in
instance _root_.LO.Modal.Hilbert.S4Dot3.Kripke.canonical :
    Canonical (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass := by
  have hS4 :=
    canonicalFrame.multigeachean_of_provable_geach (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1,
      0⟩}) (𝓢 := Hilbert.S4Dot3) (by simp);
  constructor;
  refine ⟨?_, ?_, ?_⟩;
  · simpa [reflexive_def, Geachean] using @hS4 (⟨0, 0, 1, 0⟩) <| by tauto;
  · simpa [transitive_def, Geachean] using @hS4 ⟨0, 2, 1, 0⟩ <| by tauto;
  · intro X Y Z ⟨hXY, hXZ⟩;
    by_contra hC;
    push Not at hC;
    have ⟨hnYZ, hnZY⟩ := hC; clear hC;
    simp only [Set.not_subset] at hnYZ hnZY;
    obtain ⟨φ, hpY, hpZ⟩ := hnYZ; replace hpY : □φ ∈ Y := hpY;
    obtain ⟨ψ, hqZ, hqY⟩ := hnZY; replace hqZ : □ψ ∈ Z := hqZ;
    have hpqX : □(□φ ==> ψ) ∉ X := by
      apply iff_mem_box.not.mpr;
      push Not;
      use Y;
      constructor;
      · assumption;
      · apply iff_mem_imp.not.mpr;
        aesop;
    have hqpX : □(□ψ ==> φ) ∉ X := by
      apply iff_mem_box.not.mpr; push Not;
      use Z;
      constructor;
      · assumption;
      · apply iff_mem_imp.not.mpr;
        aesop;
    have : (□(□φ ==> ψ) ⋎ □(□ψ ==> φ)) ∉ X := by
      apply iff_mem_or.not.mpr; push Not; exact ⟨hpqX, hqpX⟩;
    have : □(□φ ==> ψ) ⋎ □(□ψ ==> φ) ∈ X := by
      apply membership_iff.mpr;
      exact Entailment.axiomDot3!;
    contradiction;

instance _root_.LO.Modal.Hilbert.S4Dot3.Kripke.complete :
    Complete (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass :=
  inferInstance

end S4Dot3
end Hilbert


end Modal
end LO
