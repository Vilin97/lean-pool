/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.PolarityCalculus
import LeanPool.InfinitaryLogic.Methods.Interpolation.InseparablePairFamily
import LeanPool.InfinitaryLogic.Methods.Interpolation.BaseOccurrenceProjections
/-!
# Polarity-refined inseparability and the mixed closures (issue #14, Unit 2 — the stop/go gate)

The single definitional change of the Lyndon refinement (audit v2 §D4): the separator class of
`InsepAt` is refined from "base symbols in `(F, R)`" to "base functions in `F`, base **positive**
relations in `P`, base **negative** relations in `N`".

`LyndonInsepAt F P N A Γ Δ` says the pair `(Γ, Δ)` admits no such separator at allowed constant
support `A`.  Everything else about the engine is untouched.

This file contains **only** the stop/go gate of the audit: the definition, the three genuinely
mixed closures, the equality corollary they are consumed at, and the root-class acceptance
equation.  `SentBndPol`, the one-sided closure suite, and the paired family are Unit 3+.

* `lyndonInsepAt_swap` — dualization is **class-exchanging**: its separator map is `σ ↦ σ.not`,
  which swaps the two polarity classes, so the conclusion is at `(F, N, P)`;
* `lyndonInsepAt_imp_dichotomy` (C1) — polarity-clean: the separator `(σ₁.not).imp σ₂` has
  `pos = pos σ₁ ∪ pos σ₂` and `neg = neg σ₁ ∪ neg σ₂`, the antecedent's two flips cancelling;
* `lyndonInsepAt_insert_of_shared_entails` — the **only** flipped-antecedent gate: its separator
  is `σ.imp ρ`, so the shared hypothesis enters with reversed polarity and the general statement
  must demand `σ` in the **swapped** class (`Pos σ ⊆ N`, `Neg σ ⊆ P`);
* `lyndonInsepAt_insert_of_shared_constEq_entails` — the specialization actually consumed by the
  kernel's cross-coordinate transfers, where the shared sentence is a constant equality and the
  swapped-class hypotheses are discharged by `baseRelationsInSigned_constEq`.  The dependency on
  "equality is logical" is thereby visible in the API, not hidden inside a generic theorem;
* `lyndon_root_class_eq` — the acceptance equation of audit §D4a: with the `Γ`-root `φ` and the
  `Δ`-root `ψ.not`, the maintained class `(P₁ ∩ N₂, N₁ ∩ P₂)` **is** the endpoint's
  `(Pos φ ∩ Pos ψ, Neg φ ∩ Neg ψ)`.  This is the machine-checked form of the side flip in
  López–Escobar 1965, Theorem 4.0(.4).
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}}

/-! ## The refined separator class -/

/-- **Polarity-refined support-parameterized inseparability**: no separator whose base function
symbols lie in `F`, whose base **positively** occurring relations lie in `P` and **negatively**
occurring ones in `N`, whose constant support lies in `A`, entailed by `Γ` and refuted on `Δ`. -/
def LyndonInsepAt (F : Set (Σ n, L.Functions n)) (P N : Set (Σ n, L.Relations n))
    (A : Finset ℕ) (Γ Δ : Set L[[ℕ]].Sentenceω) : Prop :=
  ¬ ∃ σ : L[[ℕ]].Sentenceω,
    σ.baseFunctionsIn ⊆ F ∧ σ.basePositiveRelations ⊆ P ∧ σ.baseNegativeRelations ⊆ N ∧
    sentenceJConsts (L' := L) (J := ℕ) σ ⊆ (↑A : Set ℕ) ∧
    Theoryω.Entails Γ σ ∧ Theoryω.Entails Δ σ.not

variable {F : Set (Σ n, L.Functions n)} {P N : Set (Σ n, L.Relations n)}
  {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-! ## Gate 1: dualization exchanges the classes -/

/-- **Dualization is class-exchanging.** Inseparability at `(F, P, N)` for `(Γ, Δ)` is
inseparability at `(F, N, P)` for `(Δ, Γ)`: the separator map `σ ↦ σ.not` swaps the polarity
classes. -/
theorem lyndonInsepAt_swap (h : LyndonInsepAt F P N A Γ Δ) : LyndonInsepAt F N P A Δ Γ := by
  rintro ⟨σ, hbf, hbp, hbn, hsupp, hΔσ, hΓσnot⟩
  refine h ⟨σ.not, ?_, ?_, ?_, ?_, hΓσnot, ?_⟩
  · rw [baseFunctionsIn_not]; exact hbf
  · rw [basePositiveRelations_not]; exact hbn
  · rw [baseNegativeRelations_not]; exact hbp
  · rw [sentenceJConsts_not]; exact hsupp
  · intro M _ _ hmodel
    have hσ := hΔσ M hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, not_not]
    exact hσ

/-! ## Gate 2: the implication dichotomy (the polarity-clean mixed closure) -/

/-- **C1 (implication), polarity-refined.** An implication in `Γ` yields one of the two possible
refinements.  The combined separator `(σ₁.not).imp σ₂` stays in the *same* class: the antecedent
is negated and then flipped again by the implication, so the two flips cancel. -/
theorem lyndonInsepAt_imp_dichotomy {φ ψ : L[[ℕ]].Sentenceω} (hmem : φ.imp ψ ∈ Γ)
    (h : LyndonInsepAt F P N A Γ Δ) :
    LyndonInsepAt F P N A (insert φ.not Γ) Δ ∨ LyndonInsepAt F P N A (insert ψ Γ) Δ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [LyndonInsepAt, not_not] at h1 h2
  obtain ⟨σ₁, hbf₁, hbp₁, hbn₁, hsupp₁, hΓσ₁, hΔσ₁⟩ := h1
  obtain ⟨σ₂, hbf₂, hbp₂, hbn₂, hsupp₂, hΓσ₂, hΔσ₂⟩ := h2
  apply h
  refine ⟨(σ₁.not).imp σ₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact baseFunctionsIn_imp_subset (by rw [baseFunctionsIn_not]; exact hbf₁) hbf₂
  · refine baseRelationsInSigned_imp_subset ?_ hbp₂
    show baseRelationsInSigned false σ₁.not ⊆ P
    rw [baseRelationsInSigned_not]
    exact hbp₁
  · refine baseRelationsInSigned_imp_subset ?_ hbn₂
    show baseRelationsInSigned true σ₁.not ⊆ N
    rw [baseRelationsInSigned_not]
    exact hbn₁
  · exact sentenceJConsts_imp_subset (by rw [sentenceJConsts_not]; exact hsupp₁) hsupp₂
  · intro M _ _ hmodel
    have himp := hmodel _ hmem
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_imp] at himp
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_imp, BoundedFormulaω.realize_not]
    intro hnσ₁
    by_cases hφ : BoundedFormulaω.Realize φ (Empty.elim : Empty → M) Fin.elim0
    · exact hΓσ₂ M (by
        intro ρ hρ
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · exact himp hφ
        · exact hmodel ρ hρ)
    · exact absurd (hΓσ₁ M (by
        intro ρ hρ
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not]; exact hφ
        · exact hmodel ρ hρ)) hnσ₁
  · intro M _ _ hmodel
    have h1' := hΔσ₁ M hmodel
    have h2' := hΔσ₂ M hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp]
      at h1' h2' ⊢
    intro hf
    exact h2' (hf h1')

/-! ## Gate 3: shared-hypothesis transfer, with the swapped-class signature -/

/-- **Shared-hypothesis transfer, polarity-refined.** If `σ` is shared **in the swapped class**
(its positive relations bounded by `N` and its negative ones by `P`), is entailed by `Δ`, and `φ`
is a consequence of `Γ ∪ {σ}`, then `φ` may be added to the `Γ` coordinate.

The swap is forced by the separator this gate builds, `σ.imp ρ`: since
`Pos (σ → ρ) = Neg σ ∪ Pos ρ` and `Neg (σ → ρ) = Pos σ ∪ Neg ρ`, the shared hypothesis enters
with reversed polarity.  Keeping that in the *signature* is deliberate: a future transfer of a
non-equality shared sentence must supply these bounds rather than silently break the theorem. -/
private theorem lyndonInsepAt_insert_of_shared_entails {σ φ : L[[ℕ]].Sentenceω}
    (hσF : σ.baseFunctionsIn ⊆ F)
    (hσP : σ.basePositiveRelations ⊆ N)
    (hσN : σ.baseNegativeRelations ⊆ P)
    (hσA : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ (↑A : Set ℕ))
    (hΔσ : Theoryω.Entails Δ σ) (hcons : Theoryω.Entails (insert σ Γ) φ)
    (h : LyndonInsepAt F P N A Γ Δ) : LyndonInsepAt F P N A (insert φ Γ) Δ := by
  rintro ⟨ρ, hbf, hbp, hbn, hsupp, hΓφρ, hΔρnot⟩
  refine h ⟨σ.imp ρ, baseFunctionsIn_imp_subset hσF hbf, ?_, ?_,
    sentenceJConsts_imp_subset hσA hsupp, ?_, ?_⟩
  · exact baseRelationsInSigned_imp_subset hσN hbp
  · exact baseRelationsInSigned_imp_subset hσP hbn
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

/-- **The equality specialization** — the form the kernel's four cross-coordinate transfers
actually consume.  A constant equality has empty base polarity sets in both signs, so the
swapped-class hypotheses of the general gate are discharged outright: this is exactly where
"equality is logical" does its work, in the open. -/
theorem lyndonInsepAt_insert_of_shared_constEq_entails {φ : L[[ℕ]].Sentenceω} (a b : ℕ)
    (hσA : sentenceJConsts (L' := L) (J := ℕ) (constEq (L := L) a b) ⊆ (↑A : Set ℕ))
    (hΔσ : Theoryω.Entails Δ (constEq (L := L) a b))
    (hcons : Theoryω.Entails (insert (constEq (L := L) a b) Γ) φ)
    (h : LyndonInsepAt F P N A Γ Δ) : LyndonInsepAt F P N A (insert φ Γ) Δ :=
  lyndonInsepAt_insert_of_shared_entails
    (by rw [baseFunctionsIn_constEq]; exact Set.empty_subset _)
    (by simp [BoundedFormulaω.basePositiveRelations])
    (by simp [BoundedFormulaω.baseNegativeRelations])
    hσA hΔσ hcons h

/-! ## The root-class acceptance equation (audit §D4a) -/

/-- **The root orientation, as an equation.**  The engine runs with the `Γ`-root `φ` bounded by
`(Pos φ, Neg φ)` and the `Δ`-root `ψ.not` bounded by `(Pos (ψ.not), Neg (ψ.not))`, maintaining
the separator class `(P₁ ∩ N₂, N₁ ∩ P₂)`.  That class **is** the endpoint's pair of
intersections — which is the machine-checked form of the side flip in López–Escobar 1965,
Theorem 4.0(.4). -/
theorem lyndon_root_class_eq (φ ψ : L.Sentenceω) :
    (φ.positiveRelationsIn ∩ (ψ.not).negativeRelationsIn,
      φ.negativeRelationsIn ∩ (ψ.not).positiveRelationsIn) =
      (φ.positiveRelationsIn ∩ ψ.positiveRelationsIn,
        φ.negativeRelationsIn ∩ ψ.negativeRelationsIn) := by
  rw [negativeRelationsIn_not, positiveRelationsIn_not]

end FirstOrder.Language
