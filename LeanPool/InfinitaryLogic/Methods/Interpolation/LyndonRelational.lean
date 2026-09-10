/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.LyndonRootGate
import LeanPool.InfinitaryLogic.Methods.Interpolation.LyndonPairedCP
import LeanPool.InfinitaryLogic.Methods.Interpolation.CraigRelational
/-!
# Lyndon interpolation, countable relational core (issue #14, Unit 5, commit 2)

The internal countable joint-language theorem: over a countable relational vocabulary, an
entailment `r₁ ⊨ r₂` admits an interpolant whose **positive** relation occurrences lie in both
roots' positive occurrences and whose **negative** occurrences lie in both roots' negative ones.

This is the relation-polarity / logical-equality form of López–Escobar 1965, Theorem 4.1: clause
(.4) in full, with (.3)'s equality-occurrence condition deliberately not claimed (equality is
logical here and unconstrained in the interpolant).

The skeleton is Craig's, unchanged: assume no interpolant, observe that the mapped root pair is
then inseparable at empty support (an empty-support separator would strip, through the **signed**
root gate, to a base interpolant with all three bounds), and feed the inseparable pair to the
polarity-refined paired model existence.  The resulting single model realizes `r₁` and refutes
`r₂`, contradicting the entailment.

**The root orientation is cited, not re-derived.** The `Δ`-root is `r₂.not` carrying *its own*
polarity bounds `(Pos (r₂.not), Neg (r₂.not))`, so the engine maintains the class
`(Pos r₁ ∩ Neg (r₂.not), Neg r₁ ∩ Pos (r₂.not))`; `lyndon_root_class_eq` is what turns that into
the endpoint's `(Pos r₁ ∩ Pos r₂, Neg r₁ ∩ Neg r₂)`.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}}

/-- **Lyndon interpolation, countable relational core.** -/
theorem lyndon_interpolation_relational_countable [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (r₁ r₂ : L.Sentenceω) (h : Sentenceω.Entails r₁ r₂) :
    ∃ θ : L.Sentenceω,
      θ.functionsIn ⊆ r₁.functionsIn ∩ r₂.functionsIn ∧
      θ.positiveRelationsIn ⊆ r₁.positiveRelationsIn ∩ r₂.positiveRelationsIn ∧
      θ.negativeRelationsIn ⊆ r₁.negativeRelationsIn ∩ r₂.negativeRelationsIn ∧
      Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂ := by
  by_contra hcon
  push Not at hcon
  set g := L.lhomWithConstants ℕ with hg
  -- The root-class acceptance equation (audit §D4a): the class the engine maintains for the
  -- roots `r₁` and `r₂.not` **is** the endpoint's pair of intersections.
  have hclassP : r₁.positiveRelationsIn ∩ (r₂.not).negativeRelationsIn =
      r₁.positiveRelationsIn ∩ r₂.positiveRelationsIn :=
    congrArg Prod.fst (lyndon_root_class_eq r₁ r₂)
  have hclassN : r₁.negativeRelationsIn ∩ (r₂.not).positiveRelationsIn =
      r₁.negativeRelationsIn ∩ r₂.negativeRelationsIn :=
    congrArg Prod.snd (lyndon_root_class_eq r₁ r₂)
  -- The mapped root pair is inseparable at empty support.
  have hroot : LyndonInsepAt (r₁.functionsIn ∩ r₂.functionsIn)
      (r₁.positiveRelationsIn ∩ (r₂.not).negativeRelationsIn)
      (r₁.negativeRelationsIn ∩ (r₂.not).positiveRelationsIn) ∅
      {BoundedFormulaω.mapLanguage g r₁} {(BoundedFormulaω.mapLanguage g r₂).not} := by
    rintro ⟨σ, hbf, hbp, hbn, hsupp, hΓσ, hΔσ⟩
    have hsupp0 : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ ∅ := by simpa using hsupp
    have hΓmap : Theoryω.Entails (BoundedFormulaω.mapLanguage g '' {r₁}) σ := by
      rwa [Set.image_singleton]
    have hΔmap : Theoryω.Entails (BoundedFormulaω.mapLanguage g '' {r₂.not}) σ.not := by
      rw [Set.image_singleton, BoundedFormulaω.mapLanguage_not]; exact hΔσ
    obtain ⟨θ₀, hθf, hθp, hθn, hθΓ, hθΔ⟩ :=
      base_lyndon_interpolant_of_empty_support_separator σ hsupp0 hΓmap hΔmap
    -- here the maintained class is rewritten into the endpoint's class
    refine hcon θ₀ (hθf.trans hbf) ?_ ?_ hθΓ (entails_singleton_of_neg_entails_neg hθΔ)
    · rw [← hclassP]; exact hθp.trans hbp
    · rw [← hclassN]; exact hθn.trans hbn
  -- The right root's side bounds, in the negated root's own polarity classes.
  have hP2 : ((BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r₂).not).basePositiveRelations
      ⊆ (r₂.not).positiveRelationsIn := by
    rw [basePositiveRelations_not, baseNegativeRelations_mapLanguage_withConstants,
      positiveRelationsIn_not]
  have hN2 : ((BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r₂).not).baseNegativeRelations
      ⊆ (r₂.not).negativeRelationsIn := by
    rw [baseNegativeRelations_not, basePositiveRelations_mapLanguage_withConstants,
      negativeRelationsIn_not]
  -- A single model realizing `r₁` and refuting `r₂`.
  obtain ⟨M, instM, neM, hM1, hM2⟩ := exists_lyndon_paired_model_neg
    r₁.functionsIn r₁.positiveRelationsIn r₁.negativeRelationsIn
    r₂.functionsIn (r₂.not).positiveRelationsIn (r₂.not).negativeRelationsIn
    (BoundedFormulaω.mapLanguage g r₁) (BoundedFormulaω.mapLanguage g r₂)
    (by rw [sentenceJConsts_mapLanguage_withConstants]; exact Set.finite_empty)
    (by rw [sentenceJConsts_mapLanguage_withConstants]; exact Set.finite_empty)
    ⟨(baseFunctionsIn_mapLanguage_withConstants r₁).le,
      (baseRelationsInSigned_mapLanguage_withConstants true r₁).le,
      (baseRelationsInSigned_mapLanguage_withConstants false r₁).le⟩
    ⟨((baseFunctionsIn_not _).trans (baseFunctionsIn_mapLanguage_withConstants r₂)).le, hP2, hN2⟩
    ∅
    (by simp only [hg, sentenceJConsts_not, sentenceJConsts_mapLanguage_withConstants,
        Set.union_self, Finset.coe_empty, Set.subset_empty_iff])
    hroot
  -- The base reduct contradicts `r₁ ⊨ r₂`.
  let : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  have hb1 : @Sentenceω.Realize L r₁ M _ :=
    (BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) r₁ Empty.elim Fin.elim0).mp hM1
  have hb2 : ¬ @Sentenceω.Realize L r₂ M _ := fun hc =>
    hM2 ((BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) r₂
      Empty.elim Fin.elim0).mpr hc)
  exact hb2 (h M (fun ψ hψ => by rw [Set.mem_singleton_iff] at hψ; subst hψ; exact hb1))

end FirstOrder.Language
