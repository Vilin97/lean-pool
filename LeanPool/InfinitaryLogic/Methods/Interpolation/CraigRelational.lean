/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.PairedInsepFamily
import LeanPool.InfinitaryLogic.Methods.Interpolation.RootGate
import LeanPool.InfinitaryLogic.Methods.Interpolation.BaseOccurrenceProjections
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
import LeanPool.InfinitaryLogic.Methods.LanguageMapOccurrence
import LeanPool.InfinitaryLogic.Methods.Interpolation.RootGate
import LeanPool.InfinitaryLogic.Methods.SchemaCompletion
/-!
# Craig interpolation for `L_ω₁ω`, countable relational core (issue #8, Layer 1)

The internal countable joint-language Craig theorem.  Its conclusion is already a **base-`L`
interpolant** — `L[[ℕ]]` occurs only inside the proof, at the abstraction boundary given by the
three constant-expansion transport equalities below.

```
craig_interpolation_relational_countable :
  Sentenceω.Entails r₁ r₂ →
    ∃ θ, θ.functionsIn ⊆ r₁.functionsIn ∩ r₂.functionsIn ∧
         θ.relationsIn ⊆ r₁.relationsIn ∩ r₂.relationsIn ∧
         Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂
```

No coverage or side-bound hypotheses are needed: the side vocabularies are specialized to the roots'
exact occurrence sets, and the paired family (`PairedInsepFamily.lean`) maintains coordinatewise
side membership field-by-field, so the audit's global `GenU ⊆ Sent₁ ∪ Sent₂` coverage invariant —
and with it the coverage hypothesis — is unnecessary (an audit correction).

## The root argument

Assume no interpolant.  Then the mapped root pair `({r₁'}, {r₂'.not})` is inseparable at empty
support: an empty-support separator would strip (`base_interpolant_of_empty_support_separator`) to a
base interpolant `θ₀` with `r₁ ⊨ θ₀` and `{r₂.not} ⊨ θ₀.not`, and the latter is `θ₀ ⊨ r₂` by
semantic contraposition — contradiction.  Feeding the inseparable root pair to `exists_paired_model_neg`
gives one model with `M ⊨ r₁` and `¬ M ⊨ r₂`; its base reduct contradicts `r₁ ⊨ r₂`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}




/-! ## The countable relational Craig theorem -/

/-- **Craig interpolation for `L_ω₁ω` — countable relational core.** Over a relational language with
countably many relation symbols, an `L_ω₁ω`-entailment `r₁ ⊨ r₂` has a base-`L` interpolant whose
function/relation symbols lie in the intersection of the roots' occurrence sets. -/
theorem craig_interpolation_relational_countable [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (r₁ r₂ : L.Sentenceω) (h : Sentenceω.Entails r₁ r₂) :
    ∃ θ : L.Sentenceω,
      θ.functionsIn ⊆ r₁.functionsIn ∩ r₂.functionsIn ∧
      θ.relationsIn ⊆ r₁.relationsIn ∩ r₂.relationsIn ∧
      Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂ := by
  by_contra hcon
  push Not at hcon
  set g := L.lhomWithConstants ℕ with hg
  -- The mapped root pair is inseparable at empty support.
  have hroot : InsepAt (r₁.functionsIn ∩ r₂.functionsIn) (r₁.relationsIn ∩ r₂.relationsIn) ∅
      {BoundedFormulaω.mapLanguage g r₁} {(BoundedFormulaω.mapLanguage g r₂).not} := by
    rintro ⟨σ, hbf, hbr, hsupp, hΓσ, hΔσ⟩
    have hsupp0 : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ ∅ := by simpa using hsupp
    have hΓmap : Theoryω.Entails (BoundedFormulaω.mapLanguage g '' {r₁}) σ := by
      rwa [Set.image_singleton]
    have hΔmap : Theoryω.Entails (BoundedFormulaω.mapLanguage g '' {r₂.not}) σ.not := by
      rw [Set.image_singleton, BoundedFormulaω.mapLanguage_not]; exact hΔσ
    obtain ⟨θ₀, hθf, hθr, hθΓ, hθΔ⟩ :=
      base_interpolant_of_empty_support_separator σ hsupp0 hΓmap hΔmap
    exact hcon θ₀ (hθf.trans hbf) (hθr.trans hbr) hθΓ (entails_singleton_of_neg_entails_neg hθΔ)
  -- A single model of both sides.
  obtain ⟨M, instM, neM, hM1, hM2⟩ := exists_paired_model_neg
    r₁.functionsIn r₁.relationsIn r₂.functionsIn r₂.relationsIn
    (BoundedFormulaω.mapLanguage g r₁) (BoundedFormulaω.mapLanguage g r₂)
    (by rw [sentenceJConsts_mapLanguage_withConstants]; exact Set.finite_empty)
    (by rw [sentenceJConsts_mapLanguage_withConstants]; exact Set.finite_empty)
    ⟨(baseFunctionsIn_mapLanguage_withConstants r₁).le,
      (baseRelationsIn_mapLanguage_withConstants r₁).le⟩
    ⟨((baseFunctionsIn_not _).trans (baseFunctionsIn_mapLanguage_withConstants r₂)).le,
      ((baseRelationsIn_not _).trans (baseRelationsIn_mapLanguage_withConstants r₂)).le⟩
    ∅
    (by simp only [hg, sentenceJConsts_not, sentenceJConsts_mapLanguage_withConstants,
        Set.union_self, Finset.coe_empty, Set.subset_empty_iff])
    hroot
  -- The base reduct contradicts `r₁ ⊨ r₂`.
  let : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  have hb1 : @Sentenceω.Realize L r₁ M _ :=
    (BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) r₁ Empty.elim Fin.elim0).mp hM1
  have hb2 : ¬ @Sentenceω.Realize L r₂ M _ := fun hc =>
    hM2 ((BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) r₂ Empty.elim Fin.elim0).mpr hc)
  exact hb2 (h M (fun ψ hψ => by rw [Set.mem_singleton_iff] at hψ; subst hψ; exact hb1))

end FirstOrder.Language
