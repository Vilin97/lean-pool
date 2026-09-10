/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.CraigSublanguage
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
/-!
# Craig separation (PC-separation) for `L_ω₁ω`, relational (issue #8, audit §10)

The disjunction form of Craig interpolation, in the shared-vocabulary `symbSublang` packaging
frozen by the audit (§10).  Two sentences `ψ₁, ψ₂` with **no common model** (`ψ₁ ⊨ ¬ψ₂`) are
separated by a single sentence `θ₀` of their shared vocabulary `L₀ = symbSublang (F₁∩F₂) (R₁∩R₂)`:
`θ₀` holds in the `L₀`-reduct of every model of `ψ₁` and fails in the `L₀`-reduct of every model
of `ψ₂`.

```
craig_pcSeparation_relational [L.IsRelational] :
  Sentenceω.Entails ψ₁ ψ₂.not →
    ∃ θ₀ : (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
                        (ψ₁.relationsIn ∩ ψ₂.relationsIn)).Sentenceω,
      (∀ M ⊨ ψ₁, the L₀-reduct of M realizes θ₀) ∧
      (∀ M ⊨ ψ₂, the L₀-reduct of M refutes θ₀)
```

This is the `#8`-side deliverable consumed by `#10`; `#10` owns the general PC-class packaging and
may re-express the shared vocabulary through its own `Language`-inclusion representation.  The
derivation is the audited one: interpolate `ψ₁ ⊨ ¬ψ₂`, whose interpolant `θ` has symbols in the
intersection (`functionsIn_not`/`relationsIn_not` strip the negation), then `restrictSymbols` it
into `L₀` and read both directions off the reduct realization bridge (`realize_mapLanguage`).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- **Craig separation (PC-separation), relational.** If `ψ₁` and `ψ₂` have no common model
(`ψ₁ ⊨ ¬ψ₂`), a single shared-vocabulary sentence `θ₀` separates them: it holds in the
shared-vocabulary reduct of every model of `ψ₁` and fails in that of every model of `ψ₂`. -/
theorem craig_pcSeparation_relational [L.IsRelational] (ψ₁ ψ₂ : L.Sentenceω)
    (h : Sentenceω.Entails ψ₁ ψ₂.not) :
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
  obtain ⟨θ, hθF, hθR, hE1, hE2⟩ := craig_interpolation_relational ψ₁ ψ₂.not h
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
