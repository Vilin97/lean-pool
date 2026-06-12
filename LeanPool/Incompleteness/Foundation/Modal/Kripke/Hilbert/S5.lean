/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Preservation
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KT4B

/-! # S5 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveEuclideanFrameClass :
    FrameClass :=
  { F | Std.Refl F ∧ Euclidean F }

namespace Hilbert
namespace S5

instance _root_.LO.Modal.Hilbert.S5.Kripke.sound :
    Sound (Hilbert.S5) (Kripke.ReflexiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩})
  · exact eq_Geach
  · unfold ReflexiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.euclidean_def];

instance _root_.LO.Modal.Hilbert.S5.Kripke.consistent : Entailment.Consistent (Hilbert.S5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.S5.Kripke.complete :
    Complete (Hilbert.S5) (Kripke.ReflexiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold ReflexiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.euclidean_def];

end S5
end Hilbert


namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev UniversalFrameClass : FrameClass := { F | Universal F }

lemma iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass :
    UniversalFrameClass ⊧ φ ↔ ReflexiveEuclideanFrameClass ⊧ φ := by
  constructor;
  · intro h F hF V r;
    let M : Model := ⟨F, V⟩;
    apply Model.PointGenerated.modal_equivalent_at_root  (M :=
      ⟨F, V⟩) (by exact ⟨trans_of_refl_eucl hF.1.refl hF.2⟩) r |>.mp;
    apply @h (F↾r).toFrame (Frame.PointGenerated.rel_universal hF.1 hF.2) (M↾r).Val;
  · rintro h F F_univ;
    exact @h F (⟨⟨refl_of_universal F_univ⟩, eucl_of_universal F_univ⟩);

end Kripke


namespace Hilbert
namespace S5

instance _root_.LO.Modal.Hilbert.S5.Kripke.soundUniversal :
    Sound (Hilbert.S5) (Kripke.UniversalFrameClass) :=
  ⟨by
  intro φ hF;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mpr;
  exact Kripke.sound.sound hF;
⟩

instance _root_.LO.Modal.Hilbert.S5.Kripke.completeUniversal :
    Complete (Hilbert.S5) (Kripke.UniversalFrameClass) :=
  ⟨by
  intro φ hF;
  apply Kripke.complete.complete;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mp;
  exact hF;
⟩

end S5
end Hilbert


/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveEuclideanFiniteFrameClass :
    FiniteFrameClass :=
  { F | Std.Refl F.Rel ∧ Euclidean F.Rel }

namespace Kripke

lemma eq_ReflexiveTransitiveSymmetricFiniteFrameClass_ReflexiveEuclideanFiniteFrameClass :
    ReflexiveTransitiveSymmetricFiniteFrameClass = ReflexiveEuclideanFiniteFrameClass := by
  ext F;
  constructor;
  · rintro ⟨hRefl, hTrans, hSymm⟩;
    constructor;
    · assumption;
    · exact eucl_of_symm_trans hSymm hTrans.trans;
  · rintro ⟨hRefl, hEucl⟩;
    refine ⟨hRefl, ?_, ?_⟩;
    · exact ⟨trans_of_refl_eucl hRefl.refl hEucl⟩;
    · exact symm_of_refl_eucl hRefl.refl hEucl;

end Kripke

end Modal
end LO
