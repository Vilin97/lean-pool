/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.InseparablePairFamily
/-!
# Paired inseparability: the cross-coordinate gates (issue #8, commit 4c — risky core)

Commits 4a/4b built a *one-sided* consistency family (`InsepFamilyMem`: only the `Γ` coordinate,
with `Δ` fixed externally).  That completes only the `Γ`-side: the Henkin limit `S*` contains `r₁`
but nothing forces `r₂`, so the truth lemma yields `M ⊨ r₁` with no handle on `r₂`.  The Craig
contradiction needs **one model of both sides at once**.

This file restores the audit's **paired** finite conditions `S = Γ ∪ Δ` (`docs/craig-audit.md`
§4, §7): `Γ ⊆ Sent₁`, `Δ ⊆ Sent₂` over the two side vocabularies, inseparable at the shared
vocabulary `(F₀, R₀)`.  The one-sided closures of `InseparablePairFamily.lean` remain the
**left-coordinate engine**; the right coordinate is obtained by the swap below, and the genuinely
new content is the three *cross-coordinate* gates the audit flagged as load-bearing.

## The gates (all proved here)

* `insepAt_swap` — **dualization**: inseparability is symmetric under `(Γ, Δ) ↦ (Δ, Γ)` with
  `σ ↦ σ.not`.  This turns every left-coordinate closure into its right-coordinate twin.
* `insepAt_shared_contradiction` — **cross-coordinate contradiction ⟹ shared separator**: a shared
  sentence `φ` with `Γ ⊨ φ` and `Δ ⊨ φ.not` (support in `A`) *is* a separator, so it cannot occur;
  this is the global `C0` for the union (the case `φ ∈ Γ`, `φ.not ∈ Δ`).  A `φ` occurring on both
  sides is automatically shared: `φ ∈ Sent₁` and `φ.not ∈ Sent₂` force `φ`'s base symbols into
  `F₁ ∩ F₂ = F₀`.
* `insepAt_insert_of_shared_entails` — **shared-hypothesis transfer**: if `σ` is shared and
  `Δ ⊨ σ`, and `φ` is a consequence of `Γ ∪ {σ}`, then `φ` may be added to the `Γ` coordinate.  A
  separator `ρ` of the enlarged pair yields the shared separator `σ.imp ρ`.  This single lemma
  discharges both the plain shared-equality transfer and the **cross-coordinate relation
  congruence** (`σ = constEq (g i) b ∈ Δ`, `φ = relInst R (Function.update g i b)`, a consequence
  of `relInst R g ∈ Γ` together with `σ`).

The full paired family (`Sent₁`/`Sent₂` predicates, `PairedInsepFamilyMem`, the right-coordinate
closures, the `ConsistencyPropertyEqOn` instance over the union, and the `{r₁, r₂}` Henkin
endpoint yielding `M ⊨ r₁ ∧ ¬ M ⊨ r₂`) is assembled on top of these gates in the next tranche.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}
variable {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
  {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- **Swap (dualization).** Inseparability is symmetric under `(Γ, Δ) ↦ (Δ, Γ)` with `σ ↦ σ.not`:
a separator `σ` of `(Δ, Γ)` gives the separator `σ.not` of `(Γ, Δ)` (double negation on the `Δ`
side). Applied to swapped arguments this is an iff; every left-coordinate closure becomes a
right-coordinate one through it. -/
theorem insepAt_swap (h : InsepAt F R A Γ Δ) : InsepAt F R A Δ Γ := by
  rintro ⟨σ, hbf, hbr, hsupp, hΔσ, hΓσnot⟩
  refine h ⟨σ.not, ?_, ?_, ?_, hΓσnot, ?_⟩
  · rw [baseFunctionsIn_not]; exact hbf
  · rw [baseRelationsIn_not]; exact hbr
  · rw [sentenceJConsts_not]; exact hsupp
  · intro M _ _ hmodel
    have hσ := hΔσ M hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, not_not]
    exact hσ

/-- **Gate (a): cross-coordinate contradiction gives a shared separator.** A shared sentence `φ`
entailed by `Γ` and refuted on `Δ` (base symbols in `(F, R)`, support in `A`) is itself a separator,
so it is incompatible with inseparability. This is the union-level `C0` for the mixed case
`φ ∈ Γ`, `φ.not ∈ Δ`. -/
theorem insepAt_shared_contradiction {φ : L[[ℕ]].Sentenceω}
    (hφF : φ.baseFunctionsIn ⊆ F) (hφR : φ.baseRelationsIn ⊆ R)
    (hφA : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ))
    (hΓφ : Theoryω.Entails Γ φ) (hΔφ : Theoryω.Entails Δ φ.not)
    (h : InsepAt F R A Γ Δ) : False :=
  h ⟨φ, hφF, hφR, hφA, hΓφ, hΔφ⟩

/-- **Gates (b) and (c): shared-hypothesis transfer.** If `σ` is shared (base symbols in `(F, R)`,
support in `A`) and entailed by `Δ`, and `φ` is a consequence of `Γ ∪ {σ}`, then `φ` may be added to
the `Γ` coordinate without breaking inseparability. A separator `ρ` of the enlarged pair yields the
shared separator `σ.imp ρ`. Instantiating `φ := σ` gives the plain shared-formula transfer (gate b);
instantiating `σ := constEq (g i) b ∈ Δ`, `φ := relInst R (Function.update g i b)` (a consequence of
`relInst R g ∈ Γ` and `σ`) gives the cross-coordinate relation congruence (gate c). -/
theorem insepAt_insert_of_shared_entails {σ φ : L[[ℕ]].Sentenceω}
    (hσF : σ.baseFunctionsIn ⊆ F) (hσR : σ.baseRelationsIn ⊆ R)
    (hσA : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ (↑A : Set ℕ))
    (hΔσ : Theoryω.Entails Δ σ) (hcons : Theoryω.Entails (insert σ Γ) φ)
    (h : InsepAt F R A Γ Δ) : InsepAt F R A (insert φ Γ) Δ := by
  rintro ⟨ρ, hbf, hbr, hsupp, hΓφρ, hΔρnot⟩
  refine h ⟨σ.imp ρ, baseFunctionsIn_imp_subset hσF hbf, baseRelationsIn_imp_subset hσR hbr,
    sentenceJConsts_imp_subset hσA hsupp, ?_, ?_⟩
  · intro M _ _ hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_imp]
    intro hσreal
    have hφreal : Sentenceω.Realize φ M := hcons M (by
      intro μ hμ
      rcases Set.mem_insert_iff.mp hμ with rfl | hμ
      · exact hσreal
      · exact hmodel μ hμ)
    exact hΓφρ M (by
      intro μ hμ
      rcases Set.mem_insert_iff.mp hμ with rfl | hμ
      · exact hφreal
      · exact hmodel μ hμ)
  · intro M _ _ hmodel
    have hσ := hΔσ M hmodel
    have hρn := hΔρnot M hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp,
      Classical.not_imp] at hσ hρn ⊢
    exact ⟨hσ, hρn⟩

/-! ## The allowed-support budget: variance and fresh growth

The paired family carries the invariant `support Γ ∪ support Δ ⊆ ↑A` — `A` is an allowed-support
*budget*, not an exact support. Shrinking the budget is free; growing it by a **fresh** constant
(supplied by the invariant whenever `c ∉ A`) is the one non-trivial move, and it is exactly
constant abstraction. -/



/-- **Fresh growth.** Enlarging the allowed-support budget by a constant `c` fresh for `Δ` preserves
inseparability: a separator using `c` abstracts to `genEx c σ`, whose support lies back in `A`. Only
the `Δ`-side (∀-generalization) needs the freshness; the `Γ`-side is `∃`-weakening. Under the family
invariant, `c ∉ A` already gives `c ∉ support Δ`. -/
theorem insepAt_grow_fresh (c : ℕ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : InsepAt F R A Γ Δ) : InsepAt F R (insert c A) Γ Δ := by
  rintro ⟨σ, hbf, hbr, hsupp, hΓσ, hΔσ⟩
  refine h ⟨genEx c σ, (baseFunctionsIn_genEx_subset c σ).trans hbf, ?_, ?_, ?_, ?_⟩
  · rw [baseRelationsIn_genEx]; exact hbr
  · intro k hk
    have hk2 : k ≠ c := fun heq => notMem_sentenceJConsts_genEx c σ (heq ▸ hk)
    have hmem := hsupp (sentenceJConsts_genEx_subset c σ hk)
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hmem
    exact hmem.resolve_left hk2
  · exact entails_genEx_of_entails_plain c σ hΓσ
  · exact entails_not_genEx_of_entails_not hcΔ hΔσ

end FirstOrder.Language
