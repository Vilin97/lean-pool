/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.CraigSublanguage
import LeanPool.InfinitaryLogic.Methods.Interpolation.GraphReconstruction
import LeanPool.InfinitaryLogic.Methods.Interpolation.BackTranslate
/-!
# Craig interpolation for `L_ω₁ω` over an arbitrary language (Craig Layer 3, Unit 7a)

The full Craig interpolation theorem: **no hypotheses on `L`**. The proof is the algebraic
assembly of the relationalization layer over the relational core:

1. `entails_graphTranslation` — the one semantic gate: `r₁ ⊨ r₂` translates to
   `Ax(F₁) ∧ r₁ʳᵉˡ ⊨ Ax(F₂) → r₂ʳᵉˡ` in the graph language, by **reconstructing** an
   `L`-structure over `F₁ ∪ F₂` from the combined graph axioms. This is the *only* place
   Unit 7 reconstructs anything.
2. The relational core `craig_interpolation_relational` applies in `graphLanguage L`
   (relational by construction, no countability hypothesis).
3. The interpolant's vocabulary bound rewrites through the exact occurrence identities
   `relationsIn_graphAntecedent`/`relationsIn_graphConsequent` and `relSym_inter` down to
   `relSym L (F₁ ∩ F₂) (R₁ ∩ R₂)`.
4. `θ := backTranslateFormula θg`; the sharp bounds are Unit 6's consumer lemmas.
5. Both entailments are pure graph-expansion transport (`graphExpansion_realizes_graphAxioms`
   plus the Unit 4/Unit 6 realize bridges) — no reconstruction.

`craig_pcSeparation` is the arbitrary-language PC-separation wrapper (the relational
`craig_pcSeparation_relational` stays, in the exact form issue #10 consumes).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- Every formula mentions only countably many function symbols — as an instance on the
subtype, so `graphAxioms φ.functionsIn` needs no explicit countability bookkeeping. -/
instance BoundedFormulaω.instCountableFunctionsIn {α : Type} {n : ℕ}
    (φ : L.BoundedFormulaω α n) : Countable ↥φ.functionsIn :=
  φ.functionsIn_countable.to_subtype

/-! ## The exact occurrence identities of the two translated sides -/

/-- The graph antecedent `Ax(F₁) ∧ r₁ʳᵉˡ` mentions exactly the relationalization of `r₁`'s own
symbols. -/
theorem relationsIn_graphAntecedent (r : L.Sentenceω) :
    ((graphAxioms r.functionsIn).and (relationalizeFormula r)).relationsIn =
      relSym L r.functionsIn r.relationsIn := by
  rw [BoundedFormulaω.relationsIn_and, relationsIn_graphAxioms,
    relationsIn_relationalizeFormula]
  exact Set.union_eq_self_of_subset_left Set.subset_union_right

/-- The graph consequent `Ax(F₂) → r₂ʳᵉˡ` mentions exactly the relationalization of `r₂`'s own
symbols. -/
theorem relationsIn_graphConsequent (r : L.Sentenceω) :
    ((graphAxioms r.functionsIn).imp (relationalizeFormula r)).relationsIn =
      relSym L r.functionsIn r.relationsIn := by
  change (graphAxioms r.functionsIn).relationsIn ∪ (relationalizeFormula r).relationsIn = _
  rw [relationsIn_graphAxioms, relationsIn_relationalizeFormula]
  exact Set.union_eq_self_of_subset_left Set.subset_union_right

/-! ## The semantic gate: entailment translates to the graph language -/

/-- **The graph translation of an entailment** — the one semantic gate of the assembly, and the
only place reconstruction is used: a model of `Ax(F₁) ∧ r₁ʳᵉˡ` that also satisfies `Ax(F₂)`
carries the graph axioms of `F₁ ∪ F₂`, so it reconstructs to an `L`-structure in which `r₁`
holds; `r₁ ⊨ r₂` there, and `r₂` translates back. -/
theorem entails_graphTranslation (r₁ r₂ : L.Sentenceω) (h : Sentenceω.Entails r₁ r₂) :
    Sentenceω.Entails ((graphAxioms r₁.functionsIn).and (relationalizeFormula r₁))
      ((graphAxioms r₂.functionsIn).imp (relationalizeFormula r₂)) := by
  rw [Sentenceω.entails_iff]
  intro M instM neM hA
  obtain ⟨hAx₁, hr₁⟩ := (BoundedFormulaω.realize_and _ _).mp hA
  change BoundedFormulaω.Realize _ _ _
  rw [BoundedFormulaω.realize_imp]
  intro hAx₂
  let : Countable ↥(r₁.functionsIn ∪ r₂.functionsIn) :=
    ((Set.countable_coe_iff.mp inferInstance).union
      (Set.countable_coe_iff.mp inferInstance)).to_subtype
  have hAxU : Sentenceω.Realize (graphAxioms (r₁.functionsIn ∪ r₂.functionsIn)) M :=
    (realize_graphAxioms_union r₁.functionsIn r₂.functionsIn).mpr ⟨hAx₁, hAx₂⟩
  let recon : L.Structure M := reconstructStructure _ hAxU
  have h₁ : @BoundedFormulaω.Realize L M recon Empty 0 r₁ Empty.elim Fin.elim0 :=
    (realize_relationalize_reconstruct hAxU r₁ Set.subset_union_left Empty.elim Fin.elim0).mp hr₁
  have h₂ : @Sentenceω.Realize L r₂ M recon := Sentenceω.entails_iff.mp h M h₁
  exact (realize_relationalize_reconstruct hAxU r₂ Set.subset_union_right
    Empty.elim Fin.elim0).mpr h₂

/-! ## The theorem -/

/-- **Craig interpolation for `L_ω₁ω`, arbitrary language.** An `L_ω₁ω`-entailment `r₁ ⊨ r₂`
over *any* language has an interpolant `θ` whose function and relation symbols each lie in the
intersection of the two roots' occurrence sets, with `r₁ ⊨ θ` and `θ ⊨ r₂`. -/
theorem craig_interpolation (r₁ r₂ : L.Sentenceω) (h : Sentenceω.Entails r₁ r₂) :
    ∃ θ : L.Sentenceω,
      θ.functionsIn ⊆ r₁.functionsIn ∩ r₂.functionsIn ∧
      θ.relationsIn ⊆ r₁.relationsIn ∩ r₂.relationsIn ∧
      Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂ := by
  -- Relational Craig in the graph language, on the translated entailment.
  obtain ⟨θg, _, hθR, hE₁, hE₂⟩ :=
    craig_interpolation_relational _ _ (entails_graphTranslation r₁ r₂ h)
  -- The vocabulary bound, through the exact identities and the shared-vocabulary identity.
  have hbound : θg.relationsIn ⊆
      relSym L (r₁.functionsIn ∩ r₂.functionsIn) (r₁.relationsIn ∩ r₂.relationsIn) := by
    have hAB : ((graphAxioms r₁.functionsIn).and (relationalizeFormula r₁)).relationsIn ∩
        ((graphAxioms r₂.functionsIn).imp (relationalizeFormula r₂)).relationsIn =
        relSym L (r₁.functionsIn ∩ r₂.functionsIn) (r₁.relationsIn ∩ r₂.relationsIn) := by
      rw [relationsIn_graphAntecedent, relationsIn_graphConsequent]
      exact relSym_inter _ _ _ _
    exact hAB ▸ hθR
  refine ⟨backTranslateFormula θg, functionsIn_backTranslate_subset hbound,
    relationsIn_backTranslate_subset hbound, ?_, ?_⟩
  · -- `r₁ ⊨ θ`: graph-expand, feed the antecedent, back-translate. No reconstruction.
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

/-! ## PC-separation, arbitrary language -/

/-- **Craig separation (PC-separation), arbitrary language.** If `ψ₁` and `ψ₂` have no common
model (`ψ₁ ⊨ ¬ψ₂`), a single shared-vocabulary sentence `θ₀` separates them: it holds in the
shared-vocabulary reduct of every model of `ψ₁` and fails in that of every model of `ψ₂`. -/
theorem craig_pcSeparation (ψ₁ ψ₂ : L.Sentenceω) (h : Sentenceω.Entails ψ₁ ψ₂.not) :
    ∃ θ₀ : (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
        (ψ₁.relationsIn ∩ ψ₂.relationsIn)).Sentenceω,
      (∀ (M : Type) [L.Structure M] [Nonempty M], Sentenceω.Realize ψ₁ M →
          @Sentenceω.Realize (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
            (ψ₁.relationsIn ∩ ψ₂.relationsIn)) θ₀ M
            ((symbSublangIncl _ _).reduct M)) ∧
      (∀ (M : Type) [L.Structure M] [Nonempty M], Sentenceω.Realize ψ₂ M →
          ¬ @Sentenceω.Realize (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
            (ψ₁.relationsIn ∩ ψ₂.relationsIn)) θ₀ M
            ((symbSublangIncl _ _).reduct M)) := by
  obtain ⟨θ, hθF, hθR, hE1, hE2⟩ := craig_interpolation ψ₁ ψ₂.not h
  rw [BoundedFormulaω.functionsIn_not] at hθF
  rw [BoundedFormulaω.relationsIn_not] at hθR
  set F₀ : Set (Σ n, L.Functions n) := ψ₁.functionsIn ∩ ψ₂.functionsIn with hF₀
  set R₀ : Set (Σ n, L.Relations n) := ψ₁.relationsIn ∩ ψ₂.relationsIn with hR₀
  refine ⟨θ.restrictSymbols hθF hθR, ?_, ?_⟩
  · intro M instM neM hψ₁
    let instM' : (symbSublang (L := L) F₀ R₀).Structure M := (symbSublangIncl F₀ R₀).reduct M
    have : (symbSublangIncl F₀ R₀).IsExpansionOn M :=
      LHom.isExpansionOn_reduct (symbSublangIncl F₀ R₀) M
    have hiff := BoundedFormulaω.realize_mapLanguage (symbSublangIncl F₀ R₀)
      (θ.restrictSymbols hθF hθR) (Empty.elim : Empty → M) Fin.elim0
    rw [BoundedFormulaω.mapLanguage_restrictSymbols] at hiff
    exact hiff.mp ((Sentenceω.entails_iff.mp hE1) M hψ₁)
  · intro M instM neM hψ₂ hcon
    let instM' : (symbSublang (L := L) F₀ R₀).Structure M := (symbSublangIncl F₀ R₀).reduct M
    have : (symbSublangIncl F₀ R₀).IsExpansionOn M :=
      LHom.isExpansionOn_reduct (symbSublangIncl F₀ R₀) M
    have hiff := BoundedFormulaω.realize_mapLanguage (symbSublangIncl F₀ R₀)
      (θ.restrictSymbols hθF hθR) (Empty.elim : Empty → M) Fin.elim0
    rw [BoundedFormulaω.mapLanguage_restrictSymbols] at hiff
    have hMnot := (Sentenceω.entails_iff.mp hE2) M (hiff.mpr hcon)
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hMnot
    exact hMnot hψ₂

end FirstOrder.Language
