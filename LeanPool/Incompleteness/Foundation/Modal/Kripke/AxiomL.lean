/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Vorspiel.BinaryRelations
import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame

/-! # AxiomL -/


namespace LO
namespace Modal

open Formula.Kripke

namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev TransitiveConverseWellFoundedFrameClass :
    FrameClass :=
  { F | IsTrans F.World F.Rel ∧ ConverseWellFounded F.Rel }
/-- Imported declaration from the Incompleteness formalization. -/
abbrev TransitiveIrreflexiveFiniteFrameClass :
    FiniteFrameClass :=
  { F | IsTrans F.World F.Rel ∧ Std.Irrefl F.Rel }

variable {F : Frame}

lemma validate_L_of_trans_and_cwf (hTrans : IsTrans F.World F.Rel) (hCWF :
    ConverseWellFounded F.Rel) :
    F ⊧ (Axioms.L (.atom 0)) := by
  rintro V w;
  apply Satisfies.imp_def.mpr;
  contrapose;
  intro h;
  obtain ⟨x, Rwx, h⟩ := by simpa using Satisfies.box_def.not.mp h;
  obtain ⟨m, ⟨⟨rwm, hm⟩, hm₂⟩⟩ :=
    hCWF.has_min ({ x | (F.Rel w x) ∧ ¬(Satisfies ⟨F, V⟩ x (.atom 0)) }) <| by use x; tauto;
  replace hm₂ : ∀ x, w ≺ x → ¬Satisfies ⟨F, V⟩ x (.atom 0) → ¬m ≺ x :=
    fun y hwy hny => hm₂ y ⟨hwy, hny⟩;
  apply Satisfies.box_def.not.mpr;
  push Not;
  use m;
  constructor;
  · assumption;
  · apply Satisfies.imp_def.not.mpr;
    push Not;
    constructor;
    · intro n rmn;
      apply not_imp_not.mp <| hm₂ n (hTrans.trans _ _ _ rwm rmn);
      exact rmn;
    · assumption;

lemma trans_of_validate_L : F ⊧ (Axioms.L (.atom 0)) → IsTrans F.World F.Rel := by
  contrapose;
  intro hT;
  have hNotTrans : ¬∀ (w v u : F.World), F.Rel w v → F.Rel v u → F.Rel w u := by
    intro h
    exact hT ⟨h⟩
  push Not at hNotTrans
  obtain ⟨w, v, u, Rwv, Rvu, nRwu⟩ := hNotTrans
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (fun w _ => w ≠ v ∧ w ≠ u), w;
  apply Satisfies.imp_def.not.mpr;
  push Not;
  constructor;
  · intro x Rwx hx;
    by_cases exv : x = v;
    · subst x;
      simpa using Satisfies.atom_def.mp <| @hx u Rvu;
    · apply Satisfies.atom_def.mpr;
      constructor;
      · assumption;
      · by_contra hC;
        subst x;
        contradiction;
  · apply Satisfies.box_def.not.mpr;
    push Not;
    use v;
    constructor;
    · assumption;
    · simp [Semantics.Realize, Satisfies];

lemma cwf_of_validate_L : F ⊧ (Axioms.L (.atom 0)) → ConverseWellFounded F.Rel := by
  contrapose;
  intro hCF;
  obtain ⟨X, ⟨x, _⟩, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (fun w _ => w ∉ X), x;
  apply Satisfies.imp_def.not.mpr;
  push Not;
  constructor;
  · intro y Rxy;
    by_cases hys : y ∈ X
    · obtain ⟨z, _, Rxz⟩ := hX₂ y hys;
      intro hy;
      have : z ∉ X := by simpa using Satisfies.atom_def.mp <| hy z Rxz;
      contradiction;
    · intro _;
      apply Satisfies.atom_def.mpr;
      simpa;
  · obtain ⟨y, _, _⟩ := hX₂ x (by assumption);
    apply Satisfies.box_def.not.mpr;
    push Not;
    use y;
    constructor;
    · assumption;
    · simpa [Semantics.Realize, Satisfies];

instance _root_.LO.Modal.Kripke.TransitiveConverseWellFoundedFrameClass.DefinedByL :
    TransitiveConverseWellFoundedFrameClass.DefinedByFormula (Axioms.L (.atom 0)) :=
  ⟨by
  intro F;
  constructor;
  · simpa using validate_L_of_trans_and_cwf;
  · intro h;
    constructor;
    · apply trans_of_validate_L; simp_all;
    · apply cwf_of_validate_L; simp_all;
⟩

instance _root_.LO.Modal.Kripke.TransitiveIrreflexiveFiniteFrameClass.DefinedByL :
    TransitiveIrreflexiveFiniteFrameClass.DefinedByFormula (Axioms.L (.atom 0)) :=
  ⟨by
  intro F;
  constructor;
  · rintro ⟨hTrans, hIrrefl⟩ φ ⟨_, rfl⟩;
    apply validate_L_of_trans_and_cwf;
    · assumption;
    · apply Finite.converseWellFounded_of_trans_irrefl'
      · exact F.world_finite;
      · intro _ _ _
        exact hTrans.trans _ _ _
      · exact hIrrefl.irrefl;
  · intro h;
    simp only [Set.mem_singleton_iff, forall_eq] at h;
    refine ⟨?_, ?_⟩;
    · apply trans_of_validate_L;
      exact h;
    · exact ⟨fun w =>
        by
          simpa using ConverseWellFounded.iff_has_max.mp
            (cwf_of_validate_L (by exact h)) {w} (by simp)⟩;
⟩

end Kripke

end Modal
end LO
