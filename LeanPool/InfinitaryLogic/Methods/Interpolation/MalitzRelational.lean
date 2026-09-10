/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.MalitzRootGate
import LeanPool.InfinitaryLogic.Methods.Interpolation.BudgetedPairModel
/-!
# Malitz interpolation, countable relational core (issue #15)

The internal countable joint-language theorem: over a countable relational vocabulary, an entailment
`r₁ ⊨ r₂` with **universal** consequent admits a **universal** interpolant whose occurrences lie in
both roots'.

The skeleton is Craig's and Lyndon's, unchanged.  Assume no interpolant; observe that the mapped
root pair is then budget-inseparable — a budgeted separator would collapse (universal because the
right root carries no universal occurrence, constant-free because the left root's support is empty)
and strip, through the Malitz root gate, to a base interpolant with both bounds.  Feed the
inseparable pair to the model endpoint; the resulting model realizes `r₁` and refutes `r₂`,
contradicting the entailment.

**Why universality is available at the separator.**  The engine's right root is `r₂.not`, and `r₂`
being universal means exactly that `r₂.not` has no positive universal occurrence.  The right
quantifier permission is therefore unusable, which is what `isUniversal_of_budgetedPairSeparates`
converts into universality of the separator.  This is the sense in which the labelled budget "pays
for" the interpolant's class.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}}

/-- **Malitz interpolation, countable relational core.** -/
theorem malitz_interpolation_relational_countable [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (r₁ r₂ : L.Sentenceω) (h₂ : IsUniversal r₂)
    (h : Sentenceω.Entails r₁ r₂) :
    ∃ θ : L.Sentenceω,
      IsUniversal θ ∧
      θ.functionsIn ⊆ r₁.functionsIn ∩ r₂.functionsIn ∧
      θ.relationsIn ⊆ r₁.relationsIn ∩ r₂.relationsIn ∧
      Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂ := by
  by_contra hcon
  push Not at hcon
  set g := L.lhomWithConstants ℕ with hg
  set r₁' := BoundedFormulaω.mapLanguage g r₁ with hr₁'
  set r₂' := BoundedFormulaω.mapLanguage g r₂ with hr₂'
  -- the two labelled root supports are empty
  have hsj₁ : sentenceJConsts (L' := L) (J := ℕ) r₁' = ∅ := by
    rw [hr₁', hg, sentenceJConsts_mapLanguage_withConstants]
  have hc₁ : theoryJConsts (L := L) {r₁'} = ∅ := by
    simp [theoryJConsts, hsj₁]
  -- the right root carries no universal occurrence, because `r₂` is universal
  have hnoU : ¬ Theoryω.HasQuantSigned true ({r₂'.not} : Set L[[ℕ]].Sentenceω) := by
    rintro ⟨ρ, hρ, hq⟩
    rw [Set.mem_singleton_iff] at hρ; subst hρ
    rw [hasQuantSigned_not] at hq
    exact (isUniversal_iff_not_hasExistential r₂').mp
      ((universalSigned_mapLanguage g true r₂).mpr h₂) hq
  -- the mapped root pair is budget-inseparable
  have hroot : BudgetedPairInsep (r₁.functionsIn) (r₁.relationsIn)
      (r₂.functionsIn) (r₂.relationsIn) {r₁'} {r₂'.not} := by
    intro hsep
    obtain ⟨σ, hsepσ⟩ := hsep
    have hσU : IsUniversal σ := isUniversal_of_budgetedPairSeparates hsepσ hnoU
    have hsupp0 : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ ∅ :=
      (sentenceJConsts_eq_empty_of_budgetedPairSeparates hsepσ hc₁).le
    have hΓmap : Theoryω.Entails (BoundedFormulaω.mapLanguage g '' {r₁}) σ := by
      rw [Set.image_singleton]; exact hsepσ.1
    have hΔmap : Theoryω.Entails (BoundedFormulaω.mapLanguage g '' {r₂.not}) σ.not := by
      rw [Set.image_singleton, BoundedFormulaω.mapLanguage_not]; exact hsepσ.2.1
    obtain ⟨θ₀, hθU, hθf, hθr, hθΓ, hθΔ⟩ :=
      base_malitz_interpolant_of_empty_support_separator σ hσU hsupp0 hΓmap hΔmap
    exact hcon θ₀ hθU (hθf.trans hsepσ.2.2.1.1) (hθr.trans hsepσ.2.2.1.2) hθΓ
      (entails_singleton_of_neg_entails_neg hθΔ)
  -- package it as a family member and extract the countermodel
  obtain ⟨M, instM, neM, hM1, hM2⟩ :=
    exists_budgetedPair_model
      (F₁ := r₁.functionsIn) (R₁ := r₁.relationsIn)
      (F₂ := r₂.functionsIn) (R₂ := r₂.relationsIn)
      (by rw [sentenceJConsts_mapLanguage_withConstants]; exact Set.finite_empty)
      (by rw [sentenceJConsts_mapLanguage_withConstants]; exact Set.finite_empty)
      (budgetedPairMem_root (mapLanguage_withConstants_mem_sentBnd r₁)
        (mapLanguage_withConstants_not_mem_sentBnd r₂) hroot)
  -- the base reduct contradicts `r₁ ⊨ r₂`
  let : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  have hb1 : @Sentenceω.Realize L r₁ M _ :=
    (BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) r₁ Empty.elim Fin.elim0).mp hM1
  have hb2 : ¬ @Sentenceω.Realize L r₂ M _ := fun hc =>
    hM2 ((BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) r₂ Empty.elim
      Fin.elim0).mpr hc)
  exact hb2 (h M (fun ψ hψ => by rw [Set.mem_singleton_iff] at hψ; subst hψ; exact hb1))

end FirstOrder.Language
