/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.LyndonSublanguage
import LeanPool.InfinitaryLogic.Methods.Interpolation.LyndonRelationalize
import LeanPool.InfinitaryLogic.Methods.Interpolation.CraigArbitrary
/-!
# Lyndon interpolation, arbitrary language (issue #14, Unit 7)

The hypothesis-free endpoint: **no** relationality assumption, **no** countability assumption.

```
lyndon_interpolation (r₁ r₂ : L.Sentenceω) : Sentenceω.Entails r₁ r₂ →
  ∃ θ, θ.functionsIn ⊆ r₁.functionsIn ∩ r₂.functionsIn ∧
       θ.positiveRelationsIn ⊆ r₁.positiveRelationsIn ∩ r₂.positiveRelationsIn ∧
       θ.negativeRelationsIn ⊆ r₁.negativeRelationsIn ∩ r₂.negativeRelationsIn ∧
       Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂
```

The relation-polarity / logical-equality form of López–Escobar 1965, Theorem 4.1 (clause (.4) in
full; clause (.3)'s equality-occurrence condition is not claimed), now over an arbitrary language.

The assembly is Craig's, reused verbatim wherever polarity is irrelevant:

* `entails_graphTranslation` — the one semantic gate, unchanged;
* the **relational Lyndon theorem** applied inside `graphLanguage L`;
* the **function-symbol** bound comes from the *unsigned* graph bound, obtained from the two signed
  bounds by `lyndon_interpolant_is_craig` composed with Craig's exact occurrence identities and
  `relSym_inter` — exactly the route `craig_interpolation` takes;
* the **signed base-relation** bounds come from Unit 6: the signed back-translation identity plus
  the two preimage root corollaries (`preimage_baseRelSym_graphAnd/Imp`);
* both entailments are Craig's graph-expansion arguments, unchanged.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}}

/-- **Lyndon interpolation for `L_ω₁ω`, arbitrary language.** An entailment `r₁ ⊨ r₂` over *any*
language has an interpolant whose function symbols lie in the intersection of the roots' function
occurrences, whose **positive** relation occurrences lie in the intersection of the roots' positive
occurrences, and whose **negative** ones lie in the intersection of the roots' negative
occurrences.

The relation-polarity / logical-equality form of López–Escobar 1965, Theorem 4.1: clause (.4) in
full, with clause (.3)'s equality-occurrence condition deliberately not claimed. -/
theorem lyndon_interpolation (r₁ r₂ : L.Sentenceω) (h : Sentenceω.Entails r₁ r₂) :
    ∃ θ : L.Sentenceω,
      θ.functionsIn ⊆ r₁.functionsIn ∩ r₂.functionsIn ∧
      θ.positiveRelationsIn ⊆ r₁.positiveRelationsIn ∩ r₂.positiveRelationsIn ∧
      θ.negativeRelationsIn ⊆ r₁.negativeRelationsIn ∩ r₂.negativeRelationsIn ∧
      Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂ := by
  let : Countable ↥r₁.functionsIn := r₁.functionsIn_countable.to_subtype
  let : Countable ↥r₂.functionsIn := r₂.functionsIn_countable.to_subtype
  -- Relational Lyndon in the graph language, on the translated entailment.
  obtain ⟨θg, -, hθP, hθN, hE₁, hE₂⟩ :=
    lyndon_interpolation_relational _ _ (entails_graphTranslation r₁ r₂ h)
  -- The UNSIGNED graph bound, for the function-symbol side: Craig's route, fed by the two signed
  -- bounds through the Craig-recovery consumer.
  have hbound : θg.relationsIn ⊆
      relSym L (r₁.functionsIn ∩ r₂.functionsIn) (r₁.relationsIn ∩ r₂.relationsIn) := by
    have hAB : ((graphAxioms r₁.functionsIn).and (relationalizeFormula r₁)).relationsIn ∩
        ((graphAxioms r₂.functionsIn).imp (relationalizeFormula r₂)).relationsIn =
        relSym L (r₁.functionsIn ∩ r₂.functionsIn) (r₁.relationsIn ∩ r₂.relationsIn) := by
      rw [relationsIn_graphAntecedent, relationsIn_graphConsequent]
      exact relSym_inter _ _ _ _
    exact hAB ▸ lyndon_interpolant_is_craig hθP hθN
  refine ⟨backTranslateFormula θg, functionsIn_backTranslate_subset hbound, ?_, ?_, ?_, ?_⟩
  · -- positive base relations: signed back-translation + the antecedent/consequent preimages
    rw [positiveRelationsIn_backTranslateFormula]
    refine Set.subset_inter (fun p hp => ?_) (fun p hp => ?_)
    · have h3 : p ∈ baseRelSym L ⁻¹' relationsInSigned true
          ((graphAxioms r₁.functionsIn).and (relationalizeFormula r₁)) := (hθP hp).1
      rw [preimage_baseRelSym_graphAnd true r₁.functionsIn r₁] at h3
      exact h3
    · have h3 : p ∈ baseRelSym L ⁻¹' relationsInSigned true
          ((graphAxioms r₂.functionsIn).imp (relationalizeFormula r₂)) := (hθP hp).2
      rw [preimage_baseRelSym_graphImp true r₂.functionsIn r₂] at h3
      exact h3
  · -- negative base relations: the same, at the other sign
    rw [negativeRelationsIn_backTranslateFormula]
    refine Set.subset_inter (fun p hp => ?_) (fun p hp => ?_)
    · have h3 : p ∈ baseRelSym L ⁻¹' relationsInSigned false
          ((graphAxioms r₁.functionsIn).and (relationalizeFormula r₁)) := (hθN hp).1
      rw [preimage_baseRelSym_graphAnd false r₁.functionsIn r₁] at h3
      exact h3
    · have h3 : p ∈ baseRelSym L ⁻¹' relationsInSigned false
          ((graphAxioms r₂.functionsIn).imp (relationalizeFormula r₂)) := (hθN hp).2
      rw [preimage_baseRelSym_graphImp false r₂.functionsIn r₂] at h3
      exact h3
  · -- `r₁ ⊨ θ`: graph-expand, feed the antecedent, back-translate.  Craig's argument, unchanged.
    rw [Sentenceω.entails_iff]
    intro M instM neM hr₁
    let := graphExpansion L M
    have hA : Sentenceω.Realize
        ((graphAxioms r₁.functionsIn).and (relationalizeFormula r₁)) M :=
      (BoundedFormulaω.realize_and _ _).mpr
        ⟨graphExpansion_realizes_graphAxioms r₁.functionsIn M,
          (realize_relationalizeFormula r₁ Empty.elim Fin.elim0).mpr hr₁⟩
    exact (realize_backTranslateFormula θg Empty.elim Fin.elim0).mpr
      (Sentenceω.entails_iff.mp hE₁ M hA)
  · -- `θ ⊨ r₂`: graph-expand, supply `Ax(F₂)` from the expansion, recover `r₂`.
    rw [Sentenceω.entails_iff]
    intro M instM neM hθ
    let := graphExpansion L M
    have hB := Sentenceω.entails_iff.mp hE₂ M
      ((realize_backTranslateFormula θg Empty.elim Fin.elim0).mp hθ)
    exact (realize_relationalizeFormula r₂ Empty.elim Fin.elim0).mp
      ((BoundedFormulaω.realize_imp _ _).mp hB
        (graphExpansion_realizes_graphAxioms r₂.functionsIn M))

end FirstOrder.Language
