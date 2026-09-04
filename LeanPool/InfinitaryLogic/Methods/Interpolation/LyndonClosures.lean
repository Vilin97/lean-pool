/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.LyndonInseparability
import LeanPool.InfinitaryLogic.Methods.Interpolation.BaseOccurrenceProjections
/-!
# The polarity side bound and the one-sided closures (issue #14, Unit 3)

`SentBndPol F P N` is the polarity refinement of `SentBnd F R`: a sentence whose base function
symbols lie in `F`, whose base **positively** occurring relations lie in `P`, and whose base
**negatively** occurring relations lie in `N`.

**The directional discipline.**  Negation does *not* preserve the class — it **exchanges** the two
polarity components:

```
σ.not ∈ SentBndPol F P N  ↔  σ ∈ SentBndPol F N P
```

so the unsigned `sentBnd_not_iff` must **not** be ported as a same-class equivalence.  The
subformula rules are correspondingly directional: from `φ.imp ψ ∈ SentBndPol F P N` one gets
`φ.not` and `ψ` in the *same* class (never `φ` itself), and from `(φ.imp ψ).not ∈ SentBndPol F P N`
one gets `φ` and `ψ.not` in the same class.  These are exactly the shapes the consistency-property
fields consume, and they are what make the side bound stable under the closure rules.

Atoms: a constant equality lies in **every** class (empty signed sets — equality is logical), while
an atomic relation instance is **positive-only**: `relInst R g ∈ SentBndPol F P N ↔ ⟨l, R⟩ ∈ P`,
never requiring or granting `⟨l, R⟩ ∈ N`.

The rest of the file is the one-sided `LyndonInsepAt` closure suite: entailment insertion and
support monotonicity (separator unchanged), the `iSup` / negated-`iInf` component selections
(separator `⨆ σ`), falsum and internal contradiction (separator `⊥`), and the fresh-support and
quantifier round-trip steps (separator `genEx c σ`) — every one of them polarity-clean, by the
signed calculus.

Not here (Unit 4+): the paired-family predicate, the cross-coordinate `C0` and relation-congruence
assembly, the `ConsistencyPropertyEqOn` instance, and any Henkin invocation — and, as of the
Unit-3 layering cleanup, **not in the dependency cone either**: the unsigned base-symbol
projections this file consumes now live in the neutral
`Methods/Interpolation/BaseOccurrenceProjections.lean`, whose own cone stops at the generated
universe.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}}

/-! ## The polarity side bound -/

/-- **Side vocabulary bound, polarity-refined.** -/
def SentBndPol (F : Set (Σ n, L.Functions n)) (P N : Set (Σ n, L.Relations n)) :
    Set L[[ℕ]].Sentenceω :=
  {σ | σ.baseFunctionsIn ⊆ F ∧ σ.basePositiveRelations ⊆ P ∧ σ.baseNegativeRelations ⊆ N}

variable {F : Set (Σ n, L.Functions n)} {P N : Set (Σ n, L.Relations n)}



/-- **Negation exchanges the polarity components** — the directional fact that replaces the
unsigned `sentBnd_not_iff`.  It is *not* a same-class equivalence. -/
theorem sentBndPol_not_iff {σ : L[[ℕ]].Sentenceω} :
    σ.not ∈ SentBndPol F P N ↔ σ ∈ SentBndPol F N P := by
  simp only [SentBndPol, Set.mem_ofPred_eq, baseFunctionsIn_not, basePositiveRelations_not,
    baseNegativeRelations_not]
  tauto

/-! ## Directional subformula rules -/

/-- From an implication in the class, the **negated** antecedent is in the *same* class (the
antecedent itself need not be). -/
theorem sentBndPol_imp_neg_left {φ ψ : L[[ℕ]].Sentenceω} (h : φ.imp ψ ∈ SentBndPol F P N) :
    φ.not ∈ SentBndPol F P N := by
  refine ⟨?_, ?_, ?_⟩
  · rw [baseFunctionsIn_not]
    exact baseFunctionsIn_imp_left.trans h.1
  · rw [basePositiveRelations_not]
    exact (baseRelationsInSigned_imp_left (s := true) (ψ := ψ)).trans h.2.1
  · rw [baseNegativeRelations_not]
    exact (baseRelationsInSigned_imp_left (s := false) (ψ := ψ)).trans h.2.2

/-- From an implication in the class, the consequent is in the same class. -/
theorem sentBndPol_imp_right {φ ψ : L[[ℕ]].Sentenceω} (h : φ.imp ψ ∈ SentBndPol F P N) :
    ψ ∈ SentBndPol F P N :=
  ⟨baseFunctionsIn_imp_right.trans h.1,
   (baseRelationsInSigned_imp_right (s := true) (φ := φ)).trans h.2.1,
   (baseRelationsInSigned_imp_right (s := false) (φ := φ)).trans h.2.2⟩

/-- From a **negated** implication in the class, the antecedent is in the same class. -/
theorem sentBndPol_neg_imp_left {φ ψ : L[[ℕ]].Sentenceω}
    (h : (φ.imp ψ).not ∈ SentBndPol F P N) : φ ∈ SentBndPol F P N := by
  rw [sentBndPol_not_iff] at h
  exact sentBndPol_not_iff.mp (sentBndPol_imp_neg_left h)

/-- From a **negated** implication in the class, the negated consequent is in the same class. -/
theorem sentBndPol_neg_imp_right {φ ψ : L[[ℕ]].Sentenceω}
    (h : (φ.imp ψ).not ∈ SentBndPol F P N) : ψ.not ∈ SentBndPol F P N := by
  rw [sentBndPol_not_iff] at h ⊢
  exact sentBndPol_imp_right h

/-- Double negation stays in the class. -/
theorem sentBndPol_not_not {φ : L[[ℕ]].Sentenceω} (h : φ.not.not ∈ SentBndPol F P N) :
    φ ∈ SentBndPol F P N :=
  sentBndPol_not_iff.mp (sentBndPol_not_iff.mp h)

/-! ## Components of the countable connectives -/

theorem sentBndPol_component_iInf {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ)
    (h : BoundedFormulaω.iInf φs ∈ SentBndPol F P N) : φs k ∈ SentBndPol F P N :=
  ⟨(baseFunctionsIn_component_iInf k).trans h.1,
   (baseRelationsInSigned_component_iInf (s := true) k).trans h.2.1,
   (baseRelationsInSigned_component_iInf (s := false) k).trans h.2.2⟩

theorem sentBndPol_component_iSup {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ)
    (h : BoundedFormulaω.iSup φs ∈ SentBndPol F P N) : φs k ∈ SentBndPol F P N :=
  ⟨(baseFunctionsIn_component_iSup k).trans h.1,
   (baseRelationsInSigned_component_iSup (s := true) k).trans h.2.1,
   (baseRelationsInSigned_component_iSup (s := false) k).trans h.2.2⟩

/-- The negated-component rules used by `C3'` and `C4'`: a negated countable connective in the
class yields negated components in the same class. -/
theorem sentBndPol_neg_component_iInf {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ)
    (h : (BoundedFormulaω.iInf φs).not ∈ SentBndPol F P N) : (φs k).not ∈ SentBndPol F P N := by
  rw [sentBndPol_not_iff] at h ⊢
  exact sentBndPol_component_iInf k h

theorem sentBndPol_neg_component_iSup {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ)
    (h : (BoundedFormulaω.iSup φs).not ∈ SentBndPol F P N) : (φs k).not ∈ SentBndPol F P N := by
  rw [sentBndPol_not_iff] at h ⊢
  exact sentBndPol_component_iSup k h

/-! ## Substitution and the atoms -/

/-- Universal instantiation stays in the class. -/
theorem sentBndPol_instConst {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c : ℕ)
    (h : BoundedFormulaω.all φ ∈ SentBndPol F P N) : instConst c φ ∈ SentBndPol F P N := by
  refine ⟨(baseFunctionsIn_instConst_subset c φ).trans h.1, ?_, ?_⟩
  · rw [show (instConst c φ).basePositiveRelations = (BoundedFormulaω.all φ).basePositiveRelations
      from baseRelationsInSigned_instConst c true φ]
    exact h.2.1
  · rw [show (instConst c φ).baseNegativeRelations = (BoundedFormulaω.all φ).baseNegativeRelations
      from baseRelationsInSigned_instConst c false φ]
    exact h.2.2

/-- A constant equality lies in **every** side class: its signed base sets are empty in both
signs.  This is the syntactic form of "equality is logical". -/
theorem sentBndPol_constEq (a b : ℕ) : constEq (L := L) a b ∈ SentBndPol F P N :=
  ⟨by rw [baseFunctionsIn_constEq]; exact Set.empty_subset _,
   by rw [show (constEq (L := L) a b).basePositiveRelations = ∅ from
     baseRelationsInSigned_constEq true a b]; exact Set.empty_subset _,
   by rw [show (constEq (L := L) a b).baseNegativeRelations = ∅ from
     baseRelationsInSigned_constEq false a b]; exact Set.empty_subset _⟩

/-- **Atomic relation instances are positive-only**: membership in the side class is exactly
membership of the symbol in the *positive* component.  It never requires — and never grants —
membership in `N`. -/
private theorem sentBndPol_relInst_iff {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) :
    relInst R g ∈ SentBndPol F P N ↔ (⟨l, R⟩ : Σ n, L.Relations n) ∈ P := by
  constructor
  · intro h
    exact h.2.1 (by rw [basePositiveRelations_relInst_eq]; exact Set.mem_singleton _)
  · intro hR
    refine ⟨by rw [baseFunctionsIn_relInst]; exact Set.empty_subset _, ?_, ?_⟩
    · rw [basePositiveRelations_relInst_eq]
      exact Set.singleton_subset_iff.mpr hR
    · rw [show (relInst R g).baseNegativeRelations = ∅ from baseNegativeRelations_relInst R g]
      exact Set.empty_subset _

/-- Congruence: the side class does not see the constant tuple of an atomic instance. -/
theorem sentBndPol_relInst_congr {l : ℕ} (R : L.Relations l) {g : Fin l → ℕ} (g' : Fin l → ℕ)
    (h : relInst R g ∈ SentBndPol F P N) : relInst R g' ∈ SentBndPol F P N :=
  (sentBndPol_relInst_iff R g').mpr ((sentBndPol_relInst_iff R g).mp h)

/-! ## The one-sided closures: separator unchanged -/

variable {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- Adding a `Γ`-consequence keeps inseparability (the separator is unchanged). -/
theorem lyndonInsepAt_insert_of_entails {φ : L[[ℕ]].Sentenceω}
    (hcons : Theoryω.Entails Γ φ) (h : LyndonInsepAt F P N A Γ Δ) :
    LyndonInsepAt F P N A (insert φ Γ) Δ := by
  rintro ⟨σ, hbf, hbp, hbn, hsupp, hΓφσ, hΔσ⟩
  exact h ⟨σ, hbf, hbp, hbn, hsupp, Theoryω.Entails.cut hcons hΓφσ, hΔσ⟩



/-! ## The one-sided closures: component selection (separator `⨆ σ`) -/

/-- **C4 (countable disjunction)**: a disjunction in `Γ` has a component preserving
inseparability. -/
theorem lyndonInsepAt_iSup_component (φs : ℕ → L[[ℕ]].Sentenceω)
    (hmem : BoundedFormulaω.iSup φs ∈ Γ) (h : LyndonInsepAt F P N A Γ Δ) :
    ∃ k, LyndonInsepAt F P N A (insert (φs k) Γ) Δ := by
  by_contra hcon
  push Not at hcon
  simp only [LyndonInsepAt, not_not] at hcon
  choose σ hbf hbp hbn hsupp hΓσ hΔσ using hcon
  refine h ⟨BoundedFormulaω.iSup σ, baseFunctionsIn_iSup_subset σ hbf,
    baseRelationsInSigned_iSup_subset σ hbp, baseRelationsInSigned_iSup_subset σ hbn,
    sentenceJConsts_iSup_subset σ hsupp, ?_, ?_⟩
  · intro M _ _ hmodel
    have hsup := hmodel _ hmem
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_iSup] at hsup ⊢
    obtain ⟨k, hk⟩ := hsup
    exact ⟨k, hΓσ k M (by
      intro ρ hρ
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact hk
      · exact hmodel ρ hρ)⟩
  · intro M _ _ hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iSup,
      not_exists]
    intro k
    have hk := hΔσ k M hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hk
    exact hk

/-- **C3' (negated conjunction)**: a negated conjunction in `Γ` splits off a negated component. -/
theorem lyndonInsepAt_neg_iInf_component (φs : ℕ → L[[ℕ]].Sentenceω)
    (hmem : (BoundedFormulaω.iInf φs).not ∈ Γ) (h : LyndonInsepAt F P N A Γ Δ) :
    ∃ k, LyndonInsepAt F P N A (insert (φs k).not Γ) Δ := by
  by_contra hcon
  push Not at hcon
  simp only [LyndonInsepAt, not_not] at hcon
  choose σ hbf hbp hbn hsupp hΓσ hΔσ using hcon
  refine h ⟨BoundedFormulaω.iSup σ, baseFunctionsIn_iSup_subset σ hbf,
    baseRelationsInSigned_iSup_subset σ hbp, baseRelationsInSigned_iSup_subset σ hbn,
    sentenceJConsts_iSup_subset σ hsupp, ?_, ?_⟩
  · intro M _ _ hmodel
    have hnotinf := hmodel _ hmem
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iInf,
      not_forall] at hnotinf
    obtain ⟨k, hk⟩ := hnotinf
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_iSup]
    exact ⟨k, hΓσ k M (by
      intro ρ hρ
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not]; exact hk
      · exact hmodel ρ hρ)⟩
  · intro M _ _ hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iSup,
      not_exists]
    intro k
    have hk := hΔσ k M hmodel
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hk
    exact hk

/-! ## The one-sided closures: falsum and internal contradiction (separator `⊥`) -/

theorem lyndonInsepAt_falsum_absurd
    (hmem : (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) ∈ Γ)
    (h : LyndonInsepAt F P N A Γ Δ) : False := by
  apply h
  refine ⟨BoundedFormulaω.falsum, ?_, ?_, ?_, ?_, Theoryω.entails_of_mem hmem, ?_⟩
  · rw [baseFunctionsIn_falsum]; exact Set.empty_subset _
  · rw [show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).basePositiveRelations = ∅ from
      baseRelationsInSigned_falsum true]; exact Set.empty_subset _
  · rw [show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseNegativeRelations = ∅ from
      baseRelationsInSigned_falsum false]; exact Set.empty_subset _
  · rw [sentenceJConsts_falsum]; exact Set.empty_subset _
  · intro M _ _ _
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_falsum,
      not_false_eq_true]

theorem lyndonInsepAt_contradiction_absurd {φ : L[[ℕ]].Sentenceω}
    (h1 : φ ∈ Γ) (h2 : φ.not ∈ Γ) (h : LyndonInsepAt F P N A Γ Δ) : False := by
  apply h
  refine ⟨BoundedFormulaω.falsum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [baseFunctionsIn_falsum]; exact Set.empty_subset _
  · rw [show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).basePositiveRelations = ∅ from
      baseRelationsInSigned_falsum true]; exact Set.empty_subset _
  · rw [show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseNegativeRelations = ∅ from
      baseRelationsInSigned_falsum false]; exact Set.empty_subset _
  · rw [sentenceJConsts_falsum]; exact Set.empty_subset _
  · intro M _ _ hmodel
    have hφ := hmodel _ h1
    have hnφ := hmodel _ h2
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hnφ
    exact absurd hφ hnφ
  · intro M _ _ _
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_falsum,
      not_false_eq_true]

/-! ## The one-sided closures: fresh support and the quantifier round trip (separator `genEx`) -/

/-- **Fresh-support growth**: the budget may be grown by a constant fresh for `Δ`; the separator
is existentially generalized, which is sign-preserving (two flips cancel). -/
theorem lyndonInsepAt_grow_fresh (c : ℕ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : LyndonInsepAt F P N A Γ Δ) : LyndonInsepAt F P N (insert c A) Γ Δ := by
  rintro ⟨σ, hbf, hbp, hbn, hsupp, hΓσ, hΔσ⟩
  refine h ⟨genEx c σ, (baseFunctionsIn_genEx_subset c σ).trans hbf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (genEx c σ).basePositiveRelations = σ.basePositiveRelations from
      baseRelationsInSigned_genEx c true σ]; exact hbp
  · rw [show (genEx c σ).baseNegativeRelations = σ.baseNegativeRelations from
      baseRelationsInSigned_genEx c false σ]; exact hbn
  · intro k hk
    have hk2 : k ≠ c := fun heq => notMem_sentenceJConsts_genEx c σ (heq ▸ hk)
    have hmem := hsupp (sentenceJConsts_genEx_subset c σ hk)
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hmem
    exact hmem.resolve_left hk2
  · exact entails_genEx_of_entails_plain c σ hΓσ
  · exact entails_not_genEx_of_entails_not hcΔ hΔσ

/-- **The quantifier round trip (C7)**: a separator of the witness-instantiated pair at support
`insert c A` abstracts to a separator of the existential pair at `A`, so inseparability descends
to the witness instance.  The separator is `genEx c σ`, again sign-preserving. -/
theorem lyndonInsepAt_witness_of_genEx (c : ℕ) (φc : L[[ℕ]].Sentenceω)
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : LyndonInsepAt F P N A (insert (genEx c φc) Γ) Δ) :
    LyndonInsepAt F P N (insert c A) (insert φc Γ) Δ := by
  rintro ⟨σ, hbf, hbp, hbn, hsupp, hΓσ, hΔσ⟩
  refine h ⟨genEx c σ, (baseFunctionsIn_genEx_subset c σ).trans hbf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (genEx c σ).basePositiveRelations = σ.basePositiveRelations from
      baseRelationsInSigned_genEx c true σ]; exact hbp
  · rw [show (genEx c σ).baseNegativeRelations = σ.baseNegativeRelations from
      baseRelationsInSigned_genEx c false σ]; exact hbn
  · intro k hk
    have hk1 : k ∈ sentenceJConsts (L' := L) (J := ℕ) σ := sentenceJConsts_genEx_subset c σ hk
    have hk2 : k ≠ c := fun heq => notMem_sentenceJConsts_genEx c σ (heq ▸ hk)
    have hmem := hsupp hk1
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hmem
    exact hmem.resolve_left hk2
  · exact entails_genEx_of_entails hcΓ hΓσ
  · exact entails_not_genEx_of_entails_not hcΔ hΔσ

end FirstOrder.Language
