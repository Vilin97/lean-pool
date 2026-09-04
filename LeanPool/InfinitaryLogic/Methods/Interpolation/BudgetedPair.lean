/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.ConstantSurgery
import LeanPool.InfinitaryLogic.Methods.Interpolation.ConstantGeneralization
import LeanPool.InfinitaryLogic.Methods.Interpolation.PairedInsepFamily
import LeanPool.InfinitaryLogic.Lomega1omega.QuantifierOccurrence
/-!
# The budgeted labelled pair (issue #15, side-labelled restart)

The certificate selected by `docs/malitz-source-reconstruction-2.md`: Feferman's Theorem 4.3 keeps the
two sides **labelled** — formulas are retained on their derivational side, never reprojected by
vocabulary — and carries three conditions along the derivation beside the two entailments:

* the **shared vocabulary** condition on the separator;
* the **shared constant** condition, `sentenceJConsts θ ⊆ theoryJConsts Γ ∩ theoryJConsts Δ`
  (Feferman's `Free₀(θ) ⊆ Free₀(ϕ) ∩ Free₀(ψ)`, in the constant presentation);
* the **two quantifier permissions**, `hasQuantSigned true θ → HasQuantSigned true Γ` and
  `hasQuantSigned false θ → HasQuantSigned true Δ`.

The second permission reads `true` on the right because `Δ` holds the **negated** consequent: at the
root `Un({r₂.not}) = Ex(r₂)`.

The shared-constant condition is **primary**, not derived from the permissions.  That is the source's
own account: "in building up an interpolant following a cut-free derivation … we are forced to
introduce quantifiers into the interpolant only as required to maintain the condition (iii), and that
turns out to lead to (iv)" (Feferman, *"Ah, Chu!"*, pp. 2–3).  The earlier `FefermanAllowed` had the
dependency backwards, charging constants into the permissions as a standing assumption.

Everything the canonical-projection experiment needed disappears here.  A fresh witness constant is
added to **one** labelled side; being absent from the other, the shared-constant condition forbids the
separator from mentioning it, so the separator **transports unchanged** — no `genEx`, no `genAll`, no
support parameter to strip, no projection coverage, and no root tags.  Quantifier non-growth is
likewise immediate, because the quantified parent already sits on the same labelled side.

`Methods/Interpolation/FefermanProjection.lean` is **not imported**: it is retained as experimental
evidence for the canonical-projection route and its C1 failure, not as a dependency.

## Provenance

The labelled architecture is **source-backed** by Feferman's split-sequent proof, which he describes
explicitly.  The *semantic consistency-property* implementation below is this repository's adaptation:
Stern's model-theoretic forcing proof is identified as the semantic dual, but its exact invariant is
**unverified** — the paper has not been read.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} {M : Type}

/-! ## The constant support of a labelled side -/

/-- The Henkin constants occurring anywhere in a set of sentences. -/
def theoryJConsts (T : Set L[[ℕ]].Sentenceω) : Set ℕ :=
  ⋃ σ ∈ T, sentenceJConsts (L' := L) (J := ℕ) σ

variable {T T' : Set L[[ℕ]].Sentenceω} {σ : L[[ℕ]].Sentenceω} {c : ℕ}

private theorem sentenceJConsts_subset_theoryJConsts (hmem : σ ∈ T) :
    sentenceJConsts (L' := L) (J := ℕ) σ ⊆ theoryJConsts T :=
  Set.subset_biUnion_of_mem hmem

private theorem theoryJConsts_mono (h : T ⊆ T') : theoryJConsts (L := L) T ⊆ theoryJConsts T' := by
  intro k hk
  simp only [theoryJConsts, Set.mem_iUnion] at hk ⊢
  obtain ⟨ρ, hρ, hk⟩ := hk
  exact ⟨ρ, h hρ, hk⟩

@[simp] theorem theoryJConsts_insert :
    theoryJConsts (L := L) (insert σ T)
      = sentenceJConsts (L' := L) (J := ℕ) σ ∪ theoryJConsts T := by
  ext k
  simp only [theoryJConsts, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_union]
  constructor
  · rintro ⟨ρ, rfl | hρ, hk⟩
    · exact Or.inl hk
    · exact Or.inr ⟨ρ, hρ, hk⟩
  · rintro (hk | ⟨ρ, hρ, hk⟩)
    · exact ⟨σ, Or.inl rfl, hk⟩
    · exact ⟨ρ, Or.inr hρ, hk⟩

/-- **Insertion non-growth for constants**: inserting a sentence whose constants the side already
carries does not enlarge the side's support.  Every branch rule needs exactly this. -/
private theorem theoryJConsts_insert_of_subset
    (h : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ theoryJConsts T) :
    theoryJConsts (L := L) (insert σ T) = theoryJConsts T := by
  rw [theoryJConsts_insert, Set.union_eq_self_of_subset_left h]

/-- Freshness for a side is exactly non-membership in its support. -/
private theorem notMem_theoryJConsts_iff :
    c ∉ theoryJConsts (L := L) T ↔ ∀ γ ∈ T, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ := by
  constructor
  · intro h γ hγ hk
    exact h (sentenceJConsts_subset_theoryJConsts hγ hk)
  · intro h hk
    simp only [theoryJConsts, Set.mem_iUnion] at hk
    obtain ⟨γ, hγ, hk⟩ := hk
    exact h γ hγ hk

/-! ## The certificate -/

variable {F₁ F₂ : Set (Σ n, L.Functions n)} {R₁ R₂ : Set (Σ n, L.Relations n)}
  {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- **A budgeted separator of the labelled pair `(Γ, Δ)`.**  Five conditions: the two entailments, the
shared vocabulary, the **shared constants**, and the two quantifier permissions. -/
def BudgetedPairSeparates (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (Γ Δ : Set L[[ℕ]].Sentenceω) (θ : L[[ℕ]].Sentenceω) : Prop :=
  Theoryω.Entails Γ θ ∧
  Theoryω.Entails Δ θ.not ∧
  θ ∈ SentBnd (F₁ ∩ F₂) (R₁ ∩ R₂) ∧
  sentenceJConsts (L' := L) (J := ℕ) θ ⊆ theoryJConsts Γ ∩ theoryJConsts Δ ∧
  (hasQuantSigned true θ → Theoryω.HasQuantSigned true Γ) ∧
  (hasQuantSigned false θ → Theoryω.HasQuantSigned true Δ)

/-- **The invariant**: the labelled pair admits no budgeted separator. -/
def BudgetedPairInsep (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (Γ Δ : Set L[[ℕ]].Sentenceω) : Prop :=
  ¬ ∃ θ, BudgetedPairSeparates F₁ R₁ F₂ R₂ Γ Δ θ

/-! ## Order behaviour of the invariant

Inseparability is **antitone**: a separator of a smaller labelled pair is still a separator of any
larger one, because all five conditions weaken the right way — entailment survives adding premises,
the constant condition survives enlarging the supports, and both permissions survive enlarging the
sides.  Contrapositively, inseparability of the larger pair gives it for every sub-pair.

This is what lets a discharge transfer a premise onto a side temporarily and then drop it again. -/

/-- **Antitonicity in both labels.** -/
private theorem budgetedPairInsep_antitone {Γ' Δ' : Set L[[ℕ]].Sentenceω}
    (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ')
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ' Δ') :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ := by
  rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
  refine h ⟨θ, ?_, ?_, hbnd, ?_, ?_, ?_⟩
  · exact fun N instN neN hmodel => @hE N instN neN fun ρ hρ => hmodel ρ (hΓ hρ)
  · exact fun N instN neN hmodel => @hN N instN neN fun ρ hρ => hmodel ρ (hΔ hρ)
  · exact fun k hk => ⟨theoryJConsts_mono hΓ (hc hk).1, theoryJConsts_mono hΔ (hc hk).2⟩
  · exact fun hq => Theoryω.hasQuantSigned_mono hΓ (hu hq)
  · exact fun hq => Theoryω.hasQuantSigned_mono hΔ (hx hq)

/-- Antitonicity on the left alone — the form that drops a temporarily transferred premise. -/
private theorem budgetedPairInsep_antitone_left {Γ' : Set L[[ℕ]].Sentenceω} (hΓ : Γ ⊆ Γ')
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ' Δ) : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ :=
  budgetedPairInsep_antitone hΓ (subset_refl Δ) h

/-- Antitonicity on the right alone. -/
private theorem budgetedPairInsep_antitone_right {Δ' : Set L[[ℕ]].Sentenceω} (hΔ : Δ ⊆ Δ')
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ') : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ :=
  budgetedPairInsep_antitone (subset_refl Γ) hΔ h

/-! ## C0 — the mixed contradiction gate

The diagnostic case for the labelled architecture: a sentence on the left with its negation on the
right.  All five conditions are paid by the two memberships themselves. -/

/-- **Mixed C0.**  If `σ ∈ Γ` and `σ.not ∈ Δ` then `σ` *is* a budgeted separator: its vocabulary is
shared because the two sides bound the same sentence, its constants occur in both, its universal
occurrences are paid by `Γ`, and its existential occurrences are paid by the **universal** occurrences
of `σ.not` in `Δ`. -/
private theorem not_budgetedPairInsep_of_mixed (hΓ : Γ ⊆ SentBnd F₁ R₁) (hΔ : Δ ⊆ SentBnd F₂ R₂)
    (hσΓ : σ ∈ Γ) (hσΔ : σ.not ∈ Δ) : ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ := by
  intro h
  have hb₁ : σ ∈ SentBnd (L := L) F₁ R₁ := hΓ hσΓ
  have hb₂ : σ ∈ SentBnd (L := L) F₂ R₂ := sentBnd_not_iff.mp (hΔ hσΔ)
  refine h ⟨σ, Theoryω.entails_of_mem hσΓ, Theoryω.entails_of_mem hσΔ,
    ⟨Set.subset_inter hb₁.1 hb₂.1, Set.subset_inter hb₁.2 hb₂.2⟩, ?_, ?_, ?_⟩
  · refine Set.subset_inter (sentenceJConsts_subset_theoryJConsts hσΓ) ?_
    rw [← sentenceJConsts_not (L' := L) σ]
    exact sentenceJConsts_subset_theoryJConsts hσΔ
  · exact fun hq => Theoryω.hasQuantSigned_of_mem hσΓ hq
  · intro hq
    exact Theoryω.hasQuantSigned_of_mem hσΔ ((hasQuantSigned_not true σ).mpr hq)

/-- **Mixed C0, reverse labels.**  The other cross combination: the negation on the left and the
sentence itself on the right.  `σ.not` separates directly — no double-negation detour through
`not_budgetedPairInsep_of_mixed`, which would need `σ.not.not ∈ Δ`.

Both permissions flip with the sign: the *universal* occurrences of `σ.not` are paid by its own
membership in `Γ`, and its *existential* occurrences are the universal occurrences of `σ`, paid by
`σ ∈ Δ`. -/
private theorem not_budgetedPairInsep_of_mixed_rev (hΓ : Γ ⊆ SentBnd F₁ R₁) (hΔ : Δ ⊆ SentBnd F₂ R₂)
    (hσΓ : σ.not ∈ Γ) (hσΔ : σ ∈ Δ) : ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ := by
  intro h
  have hb₁ : σ.not ∈ SentBnd (L := L) F₁ R₁ := hΓ hσΓ
  have hb₂ : σ.not ∈ SentBnd (L := L) F₂ R₂ := sentBnd_not_iff.mpr (hΔ hσΔ)
  refine h ⟨σ.not, Theoryω.entails_of_mem hσΓ, ?_,
    ⟨Set.subset_inter hb₁.1 hb₂.1, Set.subset_inter hb₁.2 hb₂.2⟩, ?_, ?_, ?_⟩
  · -- `Δ ⊨ ¬¬σ` by double-negation introduction from `σ ∈ Δ`
    intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    intro hcon
    rw [BoundedFormulaω.realize_not] at hcon
    exact hcon (hmodel _ hσΔ)
  · refine Set.subset_inter (sentenceJConsts_subset_theoryJConsts hσΓ) ?_
    rw [sentenceJConsts_not (L' := L) σ]
    exact sentenceJConsts_subset_theoryJConsts hσΔ
  · exact fun hq => Theoryω.hasQuantSigned_of_mem hσΓ hq
  · intro hq
    rw [hasQuantSigned_not] at hq
    exact Theoryω.hasQuantSigned_of_mem hσΔ hq

/-- **Same-side C0.**  A sentence and its negation on one side make it inconsistent, and the
quantifier-free, constant-free `⊥` (resp. `⊤`) separates. -/
private theorem not_budgetedPairInsep_of_left_contradiction (hσ : σ ∈ Γ) (hnσ : σ.not ∈ Γ) :
    ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ := by
  intro h
  refine h ⟨BoundedFormulaω.falsum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN _ hmodel
    have h1 := hmodel σ hσ
    have h2 := hmodel σ.not hnσ
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at h2
    exact absurd h1 h2
  · intro N instN _ _
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    exact fun hf => hf
  · exact ⟨by rw [baseFunctionsIn_falsum]; exact Set.empty_subset _,
      by rw [show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseRelationsIn = ∅ from
        baseRelationsIn_falsum]; exact Set.empty_subset _⟩
  · rw [sentenceJConsts_falsum]; exact Set.empty_subset _
  · exact fun hq => absurd hq (hasQuantSigned_falsum true)
  · exact fun hq => absurd hq (hasQuantSigned_falsum false)

/-- **C0a, left.**  `⊥` on a side is its own separator: `Γ ⊨ ⊥` by membership, `Δ ⊨ ¬⊥` vacuously,
and `⊥` carries no symbol, constant or quantifier. -/
private theorem not_budgetedPairInsep_of_falsum_left
    (hmem : (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) ∈ Γ) :
    ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ := by
  intro h
  refine h ⟨BoundedFormulaω.falsum, fun N instN _ hmodel => hmodel _ hmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN _ _
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    exact fun hf => hf
  · exact ⟨by rw [baseFunctionsIn_falsum]; exact Set.empty_subset _,
      by rw [show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseRelationsIn = ∅ from
        baseRelationsIn_falsum]; exact Set.empty_subset _⟩
  · rw [sentenceJConsts_falsum]; exact Set.empty_subset _
  · exact fun hq => absurd hq (hasQuantSigned_falsum true)
  · exact fun hq => absurd hq (hasQuantSigned_falsum false)

/-- **C0a, right.**  Dual: `⊤` separates, since `Δ` holding `⊥` has no models at all. -/
private theorem not_budgetedPairInsep_of_falsum_right
    (hmem : (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) ∈ Δ) :
    ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ := by
  intro h
  refine h ⟨(BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).not, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN _ _
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    exact fun hf => hf
  · intro N instN _ hmodel
    exact absurd (hmodel _ hmem) (fun hf => hf)
  · exact ⟨by rw [baseFunctionsIn_not, baseFunctionsIn_falsum]; exact Set.empty_subset _,
      by rw [baseRelationsIn_not,
        show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseRelationsIn = ∅ from
          baseRelationsIn_falsum]; exact Set.empty_subset _⟩
  · rw [sentenceJConsts_not, sentenceJConsts_falsum]; exact Set.empty_subset _
  · intro hq
    rw [BoundedFormulaω.hasQuantSigned_not] at hq
    exact absurd hq (hasQuantSigned_falsum false)
  · intro hq
    rw [BoundedFormulaω.hasQuantSigned_not] at hq
    exact absurd hq (hasQuantSigned_falsum true)

/-! ## C1 — implication branching

The source's rule verbatim: disjunction when the principal formula is on the **left**, conjunction
when on the **right**.  There is no leakage case to consider — the branch sentences join the side
their parent is on, and nowhere else. -/

/-- **C1, left.**  Separator `τ₁ ∨ τ₂`, written `(τ₁.not).imp τ₂`. -/
private theorem budgetedPairInsep_imp_left (φ ψ : L[[ℕ]].Sentenceω) (hmem : φ.imp ψ ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert φ.not Γ) Δ ∨
      BudgetedPairInsep F₁ R₁ F₂ R₂ (insert ψ Γ) Δ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [BudgetedPairInsep, not_not] at h1 h2
  obtain ⟨τ₁, hE₁, hN₁, hb₁, hc₁, hu₁, hx₁⟩ := h1
  obtain ⟨τ₂, hE₂, hN₂, hb₂, hc₂, hu₂, hx₂⟩ := h2
  -- neither branch enlarges the left side's constant support or its universal budget
  have hcφ : theoryJConsts (L := L) (insert φ.not Γ) = theoryJConsts Γ :=
    theoryJConsts_insert_of_subset (by
      rw [sentenceJConsts_not]
      exact (sentenceJConsts_imp_left φ ψ).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have hcψ : theoryJConsts (L := L) (insert ψ Γ) = theoryJConsts Γ :=
    theoryJConsts_insert_of_subset
      ((sentenceJConsts_imp_right φ ψ).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have huφ : Theoryω.HasQuantSigned true (insert φ.not Γ) ↔ Theoryω.HasQuantSigned true Γ :=
    Theoryω.hasQuantSigned_insert_of_le fun hq =>
      Theoryω.hasQuantSigned_of_mem hmem (Or.inl ((hasQuantSigned_not true φ).mp hq))
  have huψ : Theoryω.HasQuantSigned true (insert ψ Γ) ↔ Theoryω.HasQuantSigned true Γ :=
    Theoryω.hasQuantSigned_insert_of_le fun hq => Theoryω.hasQuantSigned_of_mem hmem (Or.inr hq)
  rw [hcφ] at hc₁; rw [hcψ] at hc₂; rw [huφ] at hu₁; rw [huψ] at hu₂
  refine h ⟨(τ₁.not).imp τ₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `Γ ⊨ τ₁ ∨ τ₂`, by the implication member
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_imp, BoundedFormulaω.realize_not]
    intro hnτ₁
    have hφtrue : @Sentenceω.Realize L[[ℕ]] φ N instN := by
      by_contra hnφ
      refine hnτ₁ (@hE₁ N instN neN fun ρ hρ => ?_)
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]; exact hnφ
      · exact hmodel ρ hρ
    have himp := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_imp] at himp
    refine @hE₂ N instN neN fun ρ hρ => ?_
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact himp hφtrue
    · exact hmodel ρ hρ
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp,
      BoundedFormulaω.realize_not]
    intro hcontra
    have hn₁ := @hN₁ N instN neN hmodel
    have hn₂ := @hN₂ N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hn₁ hn₂
    exact hn₂ (hcontra hn₁)
  · exact ⟨baseFunctionsIn_imp_subset (by rw [baseFunctionsIn_not]; exact hb₁.1) hb₂.1,
      baseRelationsIn_imp_subset (by rw [baseRelationsIn_not]; exact hb₁.2) hb₂.2⟩
  · refine (sentenceJConsts_imp_subset ?_ hc₂)
    rw [sentenceJConsts_not]; exact hc₁
  · intro hq
    replace hq : hasQuantSigned true ((τ₁.not).imp τ₂) := hq
    rw [hasQuantSigned_imp, hasQuantSigned_not] at hq
    exact hq.elim hu₁ hu₂
  · intro hq
    replace hq : hasQuantSigned false ((τ₁.not).imp τ₂) := hq
    rw [hasQuantSigned_imp, hasQuantSigned_not] at hq
    exact hq.elim hx₁ hx₂

/-- **C1, right.**  Separator `τ₁ ∧ τ₂`. -/
private theorem budgetedPairInsep_imp_right (φ ψ : L[[ℕ]].Sentenceω) (hmem : φ.imp ψ ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert φ.not Δ) ∨
      BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert ψ Δ) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [BudgetedPairInsep, not_not] at h1 h2
  obtain ⟨τ₁, hE₁, hN₁, hb₁, hc₁, hu₁, hx₁⟩ := h1
  obtain ⟨τ₂, hE₂, hN₂, hb₂, hc₂, hu₂, hx₂⟩ := h2
  have hcφ : theoryJConsts (L := L) (insert φ.not Δ) = theoryJConsts Δ :=
    theoryJConsts_insert_of_subset (by
      rw [sentenceJConsts_not]
      exact (sentenceJConsts_imp_left φ ψ).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have hcψ : theoryJConsts (L := L) (insert ψ Δ) = theoryJConsts Δ :=
    theoryJConsts_insert_of_subset
      ((sentenceJConsts_imp_right φ ψ).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have huφ : Theoryω.HasQuantSigned true (insert φ.not Δ) ↔ Theoryω.HasQuantSigned true Δ :=
    Theoryω.hasQuantSigned_insert_of_le fun hq =>
      Theoryω.hasQuantSigned_of_mem hmem (Or.inl ((hasQuantSigned_not true φ).mp hq))
  have huψ : Theoryω.HasQuantSigned true (insert ψ Δ) ↔ Theoryω.HasQuantSigned true Δ :=
    Theoryω.hasQuantSigned_insert_of_le fun hq => Theoryω.hasQuantSigned_of_mem hmem (Or.inr hq)
  rw [hcφ] at hc₁; rw [hcψ] at hc₂; rw [huφ] at hx₁; rw [huψ] at hx₂
  refine h ⟨τ₁.and τ₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_and]
    exact ⟨@hE₁ N instN neN hmodel, @hE₂ N instN neN hmodel⟩
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_and]
    have himp := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_imp] at himp
    by_cases hφtrue : @Sentenceω.Realize L[[ℕ]] φ N instN
    · have hn := @hN₂ N instN neN fun ρ hρ => by
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · exact himp hφtrue
        · exact hmodel ρ hρ
      rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hn
      exact fun hand => hn hand.2
    · have hn := @hN₁ N instN neN fun ρ hρ => by
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]; exact hφtrue
        · exact hmodel ρ hρ
      rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hn
      exact fun hand => hn hand.1
  · refine ⟨?_, ?_⟩
    · rw [show (τ₁.and τ₂).baseFunctionsIn = ((τ₁.imp τ₂.not).not).baseFunctionsIn from rfl,
        baseFunctionsIn_not]
      exact baseFunctionsIn_imp_subset hb₁.1 (by rw [baseFunctionsIn_not]; exact hb₂.1)
    · rw [show (τ₁.and τ₂).baseRelationsIn = ((τ₁.imp τ₂.not).not).baseRelationsIn from rfl,
        baseRelationsIn_not]
      exact baseRelationsIn_imp_subset hb₁.2 (by rw [baseRelationsIn_not]; exact hb₂.2)
  · rw [show sentenceJConsts (L' := L) (J := ℕ) (τ₁.and τ₂)
      = sentenceJConsts (L' := L) (J := ℕ) ((τ₁.imp τ₂.not).not) from rfl, sentenceJConsts_not]
    refine sentenceJConsts_imp_subset hc₁ ?_
    rw [sentenceJConsts_not]; exact hc₂
  · intro hq
    replace hq : hasQuantSigned true (τ₁.and τ₂) := hq
    rw [hasQuantSigned_and] at hq
    exact hq.elim hu₁ hu₂
  · intro hq
    replace hq : hasQuantSigned false (τ₁.and τ₂) := hq
    rw [hasQuantSigned_and] at hq
    exact hq.elim hx₁ hx₂

/-! ## The fresh-witness rules

The payoff of labelling.  A witness constant `c` fresh for **both** sides is added to **one** of them.
Freshness on the *opposite* side is what forbids the separator from mentioning `c` — via the
shared-constant condition — so the separator transports **unchanged**; freshness on the *own* side is
what moves the entailment.  No constant abstraction appears anywhere. -/



/-- The kernel's `neg_all_witness` shape: parent `(φ.all).not`, inserted witness
`(instConst c φ).not`. -/
private theorem entails_of_entails_insert_negInstConst_of_fresh (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (τ : L[[ℕ]].Sentenceω) (hpar : (BoundedFormulaω.all φ).not ∈ T)
    (hcT : ∀ γ ∈ T, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcτ : c ∉ sentenceJConsts (L' := L) (J := ℕ) τ)
    (h : Theoryω.Entails (insert ((instConst c φ).not) T) τ) : Theoryω.Entails T τ := by
  have hcφ : c ∉ sentenceJConsts (L' := L) (J := ℕ) φ := by
    have := hcT _ hpar
    rwa [sentenceJConsts_not, sentenceJConsts_all] at this
  intro N instN neN hmodel
  set base := (L.lhomWithConstants ℕ).reduct N with hbase
  set hm := ambientConstMap (L := L) N with hh
  have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ρ N instN
        ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
    fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
  have hnall : ¬ ∀ x : N, @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 1 φ Empty.elim
      (Fin.snoc Fin.elim0 x) := (bridge _).mp (hmodel _ hpar)
  obtain ⟨x, hx⟩ := not_forall.mp hnall
  have hsnoc : (Fin.snoc Fin.elim0 x : Fin 1 → N) = (fun _ => x) := by
    funext i; simp [Fin.snoc, Fin.eq_zero i]
  rw [hsnoc] at hx
  have hT : ∀ γ ∈ T,
      @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0 γ
        Empty.elim Fin.elim0 := by
    intro γ hγ
    have hg : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 γ Empty.elim Fin.elim0 :=
      (bridge _).mp (hmodel _ hγ)
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) γ, hm k = Function.update hm c x k := by
      intro k hk
      have hkc : (k : ℕ) ≠ c := fun heq => hcT γ hγ (heq ▸ hk)
      exact (Function.update_of_ne (α := ℕ) hkc x hm).symm
    rwa [BoundedFormulaω.realize_congr_const base γ hcongr Empty.elim Fin.elim0] at hg
  have hwit : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0
      ((instConst c φ).not) Empty.elim Fin.elim0 := by
    intro hcontra
    have h1 := (realize_instConst base (Function.update hm c x) c φ).mp hcontra
    rw [show (fun _ : Fin 1 => Function.update hm c x c) = (fun _ : Fin 1 => x) from
      funext fun _ => Function.update_self c x hm] at h1
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) φ,
        Function.update hm c x k = hm k := by
      intro k hk
      have hkc : (k : ℕ) ≠ c := fun heq => hcφ (heq ▸ hk)
      exact Function.update_of_ne (α := ℕ) hkc x hm
    exact hx ((BoundedFormulaω.realize_congr_const base φ hcongr Empty.elim (fun _ => x)).mp h1)
  have hτ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0 τ
      Empty.elim Fin.elim0 :=
    @h N (wc base (Function.update hm c x)) neN (fun ρ hρ => by
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact hwit
      · exact hT ρ hρ)
  have hback : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) τ, Function.update hm c x k = hm k := by
    intro k hk
    have hkc : (k : ℕ) ≠ c := fun heq => hcτ (heq ▸ hk)
    exact Function.update_of_ne (α := ℕ) hkc x hm
  exact (bridge _).mpr
    ((BoundedFormulaω.realize_congr_const base τ hback Empty.elim Fin.elim0).mp hτ)

/-- **Fresh witness on the left.**  The separator is transported unchanged: opposite-side freshness
plus the shared-constant condition force `c ∉ sentenceJConsts θ`. -/
private theorem budgetedPairInsep_witness_left (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hpar : (BoundedFormulaω.all φ).not ∈ Γ)
    (hcΓ : c ∉ theoryJConsts (L := L) Γ) (hcΔ : c ∉ theoryJConsts (L := L) Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert ((instConst c φ).not) Γ) Δ := by
  rintro ⟨θ, hE, hN, hb, hc, hu, hx⟩
  have hcθ : c ∉ sentenceJConsts (L' := L) (J := ℕ) θ := fun hk => hcΔ (hc hk).2
  -- the left support and budget do not grow past what the parent already licenses
  have hcΓ' : theoryJConsts (L := L) (insert ((instConst c φ).not) Γ)
      ⊆ insert c (theoryJConsts Γ) := by
    rw [theoryJConsts_insert, sentenceJConsts_not]
    refine Set.union_subset (fun k hk => ?_) (Set.subset_insert _ _)
    rcases sentenceJConsts_instConst_subset c φ hk with hk | hk
    · exact Set.mem_insert_of_mem _ ((sentenceJConsts_subset_theoryJConsts hpar)
        (by rwa [sentenceJConsts_not]))
    · exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hk))
  have huΓ' : Theoryω.HasQuantSigned true (insert ((instConst c φ).not) Γ)
      → Theoryω.HasQuantSigned true Γ := by
    intro hq
    rcases Theoryω.hasQuantSigned_insert.mp hq with hq | hq
    · refine Theoryω.hasQuantSigned_of_mem hpar ?_
      rw [hasQuantSigned_not, hasQuantSigned_all]
      refine Or.inr ?_
      rw [hasQuantSigned_not] at hq
      rw [show (instConst c φ) = (φ.openBounds).subst (fun _ => constTerm c) from rfl,
        hasQuantSigned_subst] at hq
      rwa [hasQuantSigned_openBounds] at hq
    · exact hq
  refine h ⟨θ, ?_, hN, hb, ?_, fun hq => huΓ' (hu hq), hx⟩
  · exact entails_of_entails_insert_negInstConst_of_fresh c φ θ hpar
      (notMem_theoryJConsts_iff.mp hcΓ) hcθ hE
  · refine Set.subset_inter (fun k hk => ?_) (fun k hk => (hc hk).2)
    rcases hcΓ' (hc hk).1 with hk' | hk'
    · exact absurd (hk' ▸ hk) hcθ
    · exact hk'

/-- **Fresh witness on the right**, the mirror image. -/
private theorem budgetedPairInsep_witness_right (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hpar : (BoundedFormulaω.all φ).not ∈ Δ)
    (hcΓ : c ∉ theoryJConsts (L := L) Γ) (hcΔ : c ∉ theoryJConsts (L := L) Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert ((instConst c φ).not) Δ) := by
  rintro ⟨θ, hE, hN, hb, hc, hu, hx⟩
  have hcθ : c ∉ sentenceJConsts (L' := L) (J := ℕ) θ := fun hk => hcΓ (hc hk).1
  have hcΔ' : theoryJConsts (L := L) (insert ((instConst c φ).not) Δ)
      ⊆ insert c (theoryJConsts Δ) := by
    rw [theoryJConsts_insert, sentenceJConsts_not]
    refine Set.union_subset (fun k hk => ?_) (Set.subset_insert _ _)
    rcases sentenceJConsts_instConst_subset c φ hk with hk | hk
    · exact Set.mem_insert_of_mem _ ((sentenceJConsts_subset_theoryJConsts hpar)
        (by rwa [sentenceJConsts_not]))
    · exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hk))
  have huΔ' : Theoryω.HasQuantSigned true (insert ((instConst c φ).not) Δ)
      → Theoryω.HasQuantSigned true Δ := by
    intro hq
    rcases Theoryω.hasQuantSigned_insert.mp hq with hq | hq
    · refine Theoryω.hasQuantSigned_of_mem hpar ?_
      rw [hasQuantSigned_not, hasQuantSigned_all]
      refine Or.inr ?_
      rw [hasQuantSigned_not] at hq
      rw [show (instConst c φ) = (φ.openBounds).subst (fun _ => constTerm c) from rfl,
        hasQuantSigned_subst] at hq
      rwa [hasQuantSigned_openBounds] at hq
    · exact hq
  refine h ⟨θ, hE, ?_, hb, ?_, hu, fun hq => huΔ' (hx hq)⟩
  · exact entails_of_entails_insert_negInstConst_of_fresh c φ θ.not hpar
      (notMem_theoryJConsts_iff.mp hcΔ) (by rwa [sentenceJConsts_not]) hN
  · refine Set.subset_inter (fun k hk => (hc hk).1) (fun k hk => ?_)
    rcases hcΔ' (hc hk).2 with hk' | hk'
    · exact absurd (hk' ▸ hk) hcθ
    · exact hk'

/-! ## The root collapse and the interpolant equation -/

/-- **Root collapse.**  A budgeted separator against a right side with no universal occurrence is
universal; against constant-free sides it is constant-free. -/
theorem isUniversal_of_budgetedPairSeparates {θ : L[[ℕ]].Sentenceω}
    (h : BudgetedPairSeparates F₁ R₁ F₂ R₂ Γ Δ θ) (hΔ : ¬ Theoryω.HasQuantSigned true Δ) :
    IsUniversal θ :=
  (isUniversal_iff_not_hasExistential θ).mpr fun hq => hΔ (h.2.2.2.2.2 hq)

theorem sentenceJConsts_eq_empty_of_budgetedPairSeparates {θ : L[[ℕ]].Sentenceω}
    (h : BudgetedPairSeparates F₁ R₁ F₂ R₂ Γ Δ θ) (hΓ : theoryJConsts (L := L) Γ = ∅) :
    sentenceJConsts (L' := L) (J := ℕ) θ = ∅ := by
  refine Set.subset_empty_iff.mp fun k hk => ?_
  rw [← hΓ]
  exact (h.2.2.2.1 hk).1

/-- **The root equation.**  Failure of the invariant at the root pair `({r₁}, {r₂.not})` — with `r₂`
carrying no existential occurrence, i.e. universal, and the roots constant-free — delivers exactly a
Malitz interpolant: universal, shared-vocabulary, constant-free, `r₁ ⊨ θ` and `θ ⊨ r₂`. -/
private theorem exists_universal_interpolant_of_not_budgetedPairInsep {r₁ r₂ : L[[ℕ]].Sentenceω}
    (hr₂ : ¬ hasQuantSigned false r₂) (hc₁ : sentenceJConsts (L' := L) (J := ℕ) r₁ = ∅)
    (h : ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ {r₁} {r₂.not}) :
    ∃ θ : L[[ℕ]].Sentenceω, IsUniversal θ ∧ θ ∈ SentBnd (F₁ ∩ F₂) (R₁ ∩ R₂) ∧
      sentenceJConsts (L' := L) (J := ℕ) θ = ∅ ∧
      Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂ := by
  simp only [BudgetedPairInsep, not_not] at h
  obtain ⟨θ, hsep⟩ := h
  have hΔ : ¬ Theoryω.HasQuantSigned true ({r₂.not} : Set L[[ℕ]].Sentenceω) := by
    rintro ⟨ρ, hρ, hq⟩
    rw [Set.mem_singleton_iff] at hρ
    subst hρ
    exact hr₂ ((hasQuantSigned_not true r₂).mp hq)
  have hΓ : theoryJConsts (L := L) ({r₁} : Set L[[ℕ]].Sentenceω) = ∅ := by
    refine Set.subset_empty_iff.mp fun k hk => ?_
    simp only [theoryJConsts, Set.mem_iUnion, Set.mem_singleton_iff] at hk
    obtain ⟨ρ, rfl, hk⟩ := hk
    rw [hc₁] at hk
    exact hk
  refine ⟨θ, isUniversal_of_budgetedPairSeparates hsep hΔ, hsep.2.2.1,
    sentenceJConsts_eq_empty_of_budgetedPairSeparates hsep hΓ, hsep.1, ?_⟩
  intro N instN neN hmodel
  by_contra hnr₂
  have := @hsep.2.1 N instN neN (fun ρ hρ => by
    rw [Set.mem_singleton_iff] at hρ
    subst hρ
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    exact hnr₂)
  rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at this
  exact this (hmodel _ rfl)


/-! ## The family shell

`BudgetedPairMem` is the **existential labelled decomposition**: the scheduler still completes the
single set `S`, while every membership proof retains the labels the closure argument uses.  A shared
formula is never *automatically* duplicated — but, `S = Γ ∪ Δ` permitting overlap, a discharge may
*choose* a decomposition in which it appears on both sides, which is exactly what the cross-label
transfer gates below license. -/

/-- Membership in the labelled family: some finite, `GenU`-bounded, side-typed decomposition of `S`
whose labelled pair is budget-inseparable. -/
def BudgetedPairMem (r₁ r₂ : L[[ℕ]].Sentenceω)
    (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (S : Set L[[ℕ]].Sentenceω) : Prop :=
  ∃ Γ Δ : Set L[[ℕ]].Sentenceω,
    Γ.Finite ∧ Δ.Finite ∧
    Γ ⊆ GenU r₁ r₂ ∧ Δ ⊆ GenU r₁ r₂ ∧
    Γ ⊆ SentBnd F₁ R₁ ∧ Δ ⊆ SentBnd F₂ R₂ ∧
    S = Γ ∪ Δ ∧ BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ

variable {r₁ r₂ : L[[ℕ]].Sentenceω}

/-- Left-label insertion bookkeeping: the union re-decomposes with `σ` on the left. -/
private theorem budgetedPairMem_insert_left {S : Set L[[ℕ]].Sentenceω}
    (hΓfin : Γ.Finite) (hΔfin : Δ.Finite)
    (hΓU : Γ ⊆ GenU r₁ r₂) (hΔU : Δ ⊆ GenU r₁ r₂)
    (hΓb : Γ ⊆ SentBnd F₁ R₁) (hΔb : Δ ⊆ SentBnd F₂ R₂)
    (hS : S = Γ ∪ Δ)
    (hσU : σ ∈ GenU r₁ r₂) (hσb : σ ∈ SentBnd (L := L) F₁ R₁)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ (insert σ Γ) Δ) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (insert σ S) := by
  refine ⟨insert σ Γ, Δ, hΓfin.insert σ, hΔfin, ?_, hΔU, ?_, hΔb, ?_, h⟩
  · exact Set.insert_subset hσU hΓU
  · exact Set.insert_subset hσb hΓb
  · rw [hS, Set.insert_union]

/-- Right-label insertion bookkeeping. -/
private theorem budgetedPairMem_insert_right {S : Set L[[ℕ]].Sentenceω}
    (hΓfin : Γ.Finite) (hΔfin : Δ.Finite)
    (hΓU : Γ ⊆ GenU r₁ r₂) (hΔU : Δ ⊆ GenU r₁ r₂)
    (hΓb : Γ ⊆ SentBnd F₁ R₁) (hΔb : Δ ⊆ SentBnd F₂ R₂)
    (hS : S = Γ ∪ Δ)
    (hσU : σ ∈ GenU r₁ r₂) (hσb : σ ∈ SentBnd (L := L) F₂ R₂)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert σ Δ)) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (insert σ S) := by
  refine ⟨Γ, insert σ Δ, hΓfin, hΔfin.insert σ, hΓU, ?_, hΓb, ?_, ?_, h⟩
  · exact Set.insert_subset hσU hΔU
  · exact Set.insert_subset hσb hΔb
  · rw [hS, Set.union_insert]

/-! ### Fresh constants for a labelled pair

`Γ.Finite` alone is **not** enough: a single infinitary sentence can mention infinitely many
constants.  Finiteness of the *support* needs the `GenU` bound as well, via `genU_finite_support`,
together with finite constant support of the two roots. -/

/-- The constant support of a finite, `GenU`-bounded side is finite. -/
private theorem theoryJConsts_finite_of_subset_genU
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite)
    (hΓfin : Γ.Finite) (hΓU : Γ ⊆ GenU r₁ r₂) :
    (theoryJConsts (L := L) Γ).Finite :=
  hΓfin.biUnion fun γ hγ => genU_finite_support hr₁ hr₂ γ (hΓU hγ)

/-- **A constant fresh for both labels exists.**  Consumed only by the fresh-witness fields; the root
finiteness hypotheses enter the package for this reason alone. -/
private theorem exists_fresh_budgetedPair
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite)
    (hΓfin : Γ.Finite) (hΔfin : Δ.Finite)
    (hΓU : Γ ⊆ GenU r₁ r₂) (hΔU : Δ ⊆ GenU r₁ r₂) :
    ∃ c, c ∉ theoryJConsts (L := L) Γ ∧ c ∉ theoryJConsts (L := L) Δ := by
  obtain ⟨c, hc⟩ := ((theoryJConsts_finite_of_subset_genU hr₁ hr₂ hΓfin hΓU).union
    (theoryJConsts_finite_of_subset_genU hr₁ hr₂ hΔfin hΔU)).exists_notMem
  exact ⟨c, fun hmem => hc (Or.inl hmem), fun hmem => hc (Or.inr hmem)⟩

/-! ## C0, the remaining label combination -/

/-- **Same-side C0, right.**  An inconsistent right side is separated by `⊤`, the mirror of the `⊥`
separator for an inconsistent left side. -/
private theorem not_budgetedPairInsep_of_right_contradiction (hσ : σ ∈ Δ) (hnσ : σ.not ∈ Δ) :
    ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ := by
  intro h
  have hincon : ∀ (N : Type) [inst : L[[ℕ]].Structure N], Theoryω.Model Δ N → False := by
    intro N inst hmodel
    have h1 := hmodel σ hσ
    have h2 := hmodel σ.not hnσ
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at h2
    exact h2 h1
  refine h ⟨(BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).not, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN _ _
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    exact fun hf => hf
  · intro N instN _ hmodel
    exact absurd hmodel (fun hm => hincon N hm)
  · refine ⟨?_, ?_⟩
    · rw [baseFunctionsIn_not, baseFunctionsIn_falsum]; exact Set.empty_subset _
    · rw [baseRelationsIn_not,
        show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseRelationsIn = ∅ from
          baseRelationsIn_falsum]
      exact Set.empty_subset _
  · rw [sentenceJConsts_not, sentenceJConsts_falsum]; exact Set.empty_subset _
  · intro hq
    exact absurd ((hasQuantSigned_not true _).mp hq) (hasQuantSigned_falsum false)
  · intro hq
    exact absurd ((hasQuantSigned_not false _).mp hq) (hasQuantSigned_falsum true)

/-! ## Shared-hypothesis transfer

Duplicating a **quantifier-free shared** sentence onto the other label.  The separator becomes
`σ.imp θ` (resp. `σ.and θ`), and the price is exactly that `σ`'s constants already occur on the
receiving side — the shared-constant condition is what charges it. -/

/-- **Transfer right → left.**  A quantifier-free shared `σ ∈ Δ` whose constants `Γ` already carries
may be duplicated onto the left. -/
private theorem budgetedPairInsep_insert_shared_left (hσΔ : σ ∈ Δ)
    (hb₁ : σ ∈ SentBnd (L := L) F₁ R₁) (hb₂ : σ ∈ SentBnd (L := L) F₂ R₂)
    (hcσ : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ theoryJConsts Γ)
    (hq : ∀ s : Bool, ¬ hasQuantSigned s σ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert σ Γ) Δ := by
  rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
  have hcΓ' : theoryJConsts (L := L) (insert σ Γ) = theoryJConsts Γ :=
    theoryJConsts_insert_of_subset hcσ
  have huΓ' : Theoryω.HasQuantSigned true (insert σ Γ) ↔ Theoryω.HasQuantSigned true Γ :=
    Theoryω.hasQuantSigned_insert_of_le fun hqσ => absurd hqσ (hq true)
  rw [hcΓ'] at hc
  rw [huΓ'] at hu
  refine h ⟨σ.imp θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_imp]
    intro hσtrue
    refine @hE N instN neN fun ρ hρ => ?_
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact hσtrue
    · exact hmodel ρ hρ
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp]
    intro hcontra
    have hn := @hN N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hn
    exact hn (hcontra (hmodel σ hσΔ))
  · exact ⟨baseFunctionsIn_imp_subset (Set.subset_inter hb₁.1 hb₂.1) hbnd.1,
      baseRelationsIn_imp_subset (Set.subset_inter hb₁.2 hb₂.2) hbnd.2⟩
  · exact sentenceJConsts_imp_subset
      (Set.subset_inter hcσ (sentenceJConsts_subset_theoryJConsts hσΔ)) hc
  · intro hqθ
    replace hqθ : hasQuantSigned true (σ.imp θ) := hqθ
    rw [hasQuantSigned_imp] at hqθ
    exact hqθ.elim (fun hh => absurd hh (hq false)) hu
  · intro hqθ
    replace hqθ : hasQuantSigned false (σ.imp θ) := hqθ
    rw [hasQuantSigned_imp] at hqθ
    exact hqθ.elim (fun hh => absurd hh (hq true)) hx

/-- **Transfer left → right.**  The mirror: separator `σ.and θ`. -/
private theorem budgetedPairInsep_insert_shared_right (hσΓ : σ ∈ Γ)
    (hb₁ : σ ∈ SentBnd (L := L) F₁ R₁) (hb₂ : σ ∈ SentBnd (L := L) F₂ R₂)
    (hcσ : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ theoryJConsts Δ)
    (hq : ∀ s : Bool, ¬ hasQuantSigned s σ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert σ Δ) := by
  rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
  have hcΔ' : theoryJConsts (L := L) (insert σ Δ) = theoryJConsts Δ :=
    theoryJConsts_insert_of_subset hcσ
  have huΔ' : Theoryω.HasQuantSigned true (insert σ Δ) ↔ Theoryω.HasQuantSigned true Δ :=
    Theoryω.hasQuantSigned_insert_of_le fun hqσ => absurd hqσ (hq true)
  rw [hcΔ'] at hc
  rw [huΔ'] at hx
  refine h ⟨σ.and θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_and]
    exact ⟨hmodel σ hσΓ, @hE N instN neN hmodel⟩
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_and]
    by_cases hσtrue : @Sentenceω.Realize L[[ℕ]] σ N instN
    · have hn := @hN N instN neN fun ρ hρ => by
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · exact hσtrue
        · exact hmodel ρ hρ
      rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hn
      exact fun hand => hn hand.2
    · exact fun hand => hσtrue hand.1
  · refine ⟨?_, ?_⟩
    · rw [show (σ.and θ).baseFunctionsIn = ((σ.imp θ.not).not).baseFunctionsIn from rfl,
        baseFunctionsIn_not]
      exact baseFunctionsIn_imp_subset (Set.subset_inter hb₁.1 hb₂.1)
        (by rw [baseFunctionsIn_not]; exact hbnd.1)
    · rw [show (σ.and θ).baseRelationsIn = ((σ.imp θ.not).not).baseRelationsIn from rfl,
        baseRelationsIn_not]
      exact baseRelationsIn_imp_subset (Set.subset_inter hb₁.2 hb₂.2)
        (by rw [baseRelationsIn_not]; exact hbnd.2)
  · rw [show sentenceJConsts (L' := L) (J := ℕ) (σ.and θ)
      = sentenceJConsts (L' := L) (J := ℕ) ((σ.imp θ.not).not) from rfl, sentenceJConsts_not]
    refine sentenceJConsts_imp_subset
      (Set.subset_inter (sentenceJConsts_subset_theoryJConsts hσΓ) hcσ) ?_
    rw [sentenceJConsts_not]; exact hc
  · intro hqθ
    replace hqθ : hasQuantSigned true (σ.and θ) := hqθ
    rw [hasQuantSigned_and] at hqθ
    exact hqθ.elim (fun hh => absurd hh (hq true)) hu
  · intro hqθ
    replace hqθ : hasQuantSigned false (σ.and θ) := hqθ
    rw [hasQuantSigned_and] at hqθ
    exact hqθ.elim (fun hh => absurd hh (hq false)) hx


/-! ## Cross-label equality and relation transfer

The mixed `rel_congr` case, which was load-bearing in Craig's paired construction and is the
likeliest hidden obstruction here: the relation atom is on the **left**, the equality atom on the
**right**.  The derived atom mentions a constant `b` that only the right side carries, so the
separator of the extended pair may mention `b`; substituting the equality's shared partner `g i` for
`b` removes it, and the **shared-constant condition pays for it** — `g i` occurs on both sides.  No
quantifier is introduced, so both budgets are untouched. -/

/-- **Mixed-label relation congruence.**  `relInst R g ∈ Γ`, `constEq (g i) b ∈ Δ`, `b` fresh for the
left: the derived atom may be inserted on the left.  The separator is transported by
`substConst b (g i)`. -/
private theorem budgetedPairInsep_relCongr_mixed {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) (i : Fin l)
    (b : ℕ) (hrel : relInst R g ∈ Γ) (heq : constEq (g i) b ∈ Δ)
    (hbΓ : b ∉ theoryJConsts (L := L) Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (relInst R (Function.update g i b)) Γ) Δ := by
  have hgΓ : ∀ j, g j ∈ theoryJConsts (L := L) Γ := fun j =>
    (sentenceJConsts_subset_theoryJConsts hrel)
      (by rw [sentenceJConsts_relInst_eq]; exact Set.mem_range_self j)
  have hgb : ∀ j, g j ≠ b := fun j hj => hbΓ (hj ▸ hgΓ j)
  have hgiΔ : g i ∈ theoryJConsts (L := L) Δ :=
    (sentenceJConsts_subset_theoryJConsts heq) (mem_sentenceJConsts_constEq_left (g i) b)
  rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
  set τ := substConst b (g i) θ with hτ
  have hbτ : b ∉ sentenceJConsts (L' := L) (J := ℕ) τ :=
    notMem_sentenceJConsts_substConst b (g i) (fun heqb => hgb i heqb.symm) θ
  refine h ⟨τ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `Γ ⊨ τ`: reinterpret the fresh `b` at `g i`'s value; the inserted atom becomes `relInst R g`
  · intro N instN neN hmodel
    set base := (L.lhomWithConstants ℕ).reduct N with hbase
    set hm := ambientConstMap (L := L) N with hh
    have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
        @Sentenceω.Realize L[[ℕ]] ρ N instN
          ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
      fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
    have hΓ' : ∀ γ ∈ Γ,
        @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm b (hm (g i)))) Empty 0 γ
          Empty.elim Fin.elim0 := by
      intro γ hγ
      have hg : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 γ Empty.elim Fin.elim0 :=
        (bridge _).mp (hmodel _ hγ)
      have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) γ,
          hm k = Function.update hm b (hm (g i)) k := by
        intro k hk
        have hkb : (k : ℕ) ≠ b := fun heqk =>
          hbΓ (heqk ▸ (sentenceJConsts_subset_theoryJConsts hγ) hk)
        exact (Function.update_of_ne (α := ℕ) hkb _ hm).symm
      rwa [BoundedFormulaω.realize_congr_const base γ hcongr Empty.elim Fin.elim0] at hg
    have hatom : @BoundedFormulaω.Realize L[[ℕ]] N
        (wc base (Function.update hm b (hm (g i)))) Empty 0 (relInst R (Function.update g i b))
        Empty.elim Fin.elim0 := by
      have hval : (fun j => Function.update hm b (hm (g i)) (Function.update g i b j))
          = fun j => hm (g j) := by
        funext j
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hji, Function.update_of_ne (hgb j)]
      show @Structure.RelMap L N base l R
        (fun j => Function.update hm b (hm (g i)) (Function.update g i b j))
      rw [hval]
      exact (bridge _).mp (hmodel _ hrel)
    have hθ : @BoundedFormulaω.Realize L[[ℕ]] N
        (wc base (Function.update hm b (hm (g i)))) Empty 0 θ Empty.elim Fin.elim0 :=
      @hE N (wc base (Function.update hm b (hm (g i)))) neN (fun ρ hρ => by
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · exact hatom
        · exact hΓ' ρ hρ)
    exact (bridge _).mpr ((realize_substConst base hm b (g i) θ).mpr hθ)
  -- `Δ ⊨ τ.not`: `Δ` proves `g i = b`, so the substitution is invisible to it
  · intro N instN neN hmodel
    set base := (L.lhomWithConstants ℕ).reduct N with hbase
    set hm := ambientConstMap (L := L) N with hh
    have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
        @Sentenceω.Realize L[[ℕ]] ρ N instN
          ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
      fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
    have hval : hm (g i) = hm b := (bridge _).mp (hmodel _ heq)
    have hupd : Function.update hm b (hm (g i)) = hm := by
      rw [hval, Function.update_eq_self]
    show @Sentenceω.Realize L[[ℕ]] τ.not N instN
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    intro hcontra
    have hθ := (realize_substConst base hm b (g i) θ).mp ((bridge _).mp hcontra)
    rw [hupd] at hθ
    have hn := @hN N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hn
    exact hn ((bridge _).mpr hθ)
  · exact ⟨(baseFunctionsIn_substConst_subset b (g i) θ).trans hbnd.1,
      (baseRelationsIn_substConst b (g i) θ).trans hbnd.2⟩
  -- the constants: `b` is gone, and `g i` occurs on both sides
  · intro k hk
    rcases sentenceJConsts_substConst_subset b (g i) θ hk with hk' | hk'
    · have hkb : k ≠ b := fun heqk => hbτ (heqk ▸ hk)
      refine ⟨?_, (hc hk').2⟩
      have := (hc hk').1
      rw [theoryJConsts_insert] at this
      rcases this with hthis | hthis
      · rw [sentenceJConsts_relInst_eq] at hthis
        obtain ⟨j, rfl⟩ := hthis
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self] at hkb
          exact absurd rfl hkb
        · rw [Function.update_of_ne hji]
          exact hgΓ j
      · exact hthis
    · rw [Set.mem_singleton_iff] at hk'
      subst hk'
      exact ⟨hgΓ i, hgiΔ⟩
  -- budgets: substitution introduces no quantifier, and the inserted atom has none
  · intro hq
    have hqθ : hasQuantSigned true θ := (hasQuantSigned_substConst b (g i) true θ).mp hq
    rcases Theoryω.hasQuantSigned_insert.mp (hu hqθ) with hq' | hq'
    · exact hq'.elim
    · exact hq'
  · intro hq
    exact hx ((hasQuantSigned_substConst b (g i) false θ).mp hq)


/-! ## Generic insertion drivers

Every deterministic field is an instance of the same statement: the new sentence is **entailed** by
the side that receives it, and both its constants and its positive quantifier occurrences are already
carried there.  The three obligations stay separate on purpose — the proof's content is which label
received the formula. -/

/-- **Left driver.** -/
private theorem budgetedPairInsep_insert_entailed_left (hent : Theoryω.Entails Γ σ)
    (hcσ : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ theoryJConsts Γ)
    (hqσ : hasQuantSigned true σ → Theoryω.HasQuantSigned true Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert σ Γ) Δ := by
  rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
  rw [theoryJConsts_insert_of_subset hcσ] at hc
  rw [Theoryω.hasQuantSigned_insert_of_le hqσ] at hu
  refine h ⟨θ, ?_, hN, hbnd, hc, hu, hx⟩
  intro N instN neN hmodel
  refine @hE N instN neN fun ρ hρ => ?_
  rcases Set.mem_insert_iff.mp hρ with rfl | hρ
  · exact @hent N instN neN hmodel
  · exact hmodel ρ hρ

/-- **Right driver.** -/
private theorem budgetedPairInsep_insert_entailed_right (hent : Theoryω.Entails Δ σ)
    (hcσ : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ theoryJConsts Δ)
    (hqσ : hasQuantSigned true σ → Theoryω.HasQuantSigned true Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert σ Δ) := by
  rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
  rw [theoryJConsts_insert_of_subset hcσ] at hc
  rw [Theoryω.hasQuantSigned_insert_of_le hqσ] at hx
  refine h ⟨θ, hE, ?_, hbnd, hc, hu, hx⟩
  intro N instN neN hmodel
  refine @hN N instN neN fun ρ hρ => ?_
  rcases Set.mem_insert_iff.mp hρ with rfl | hρ
  · exact @hent N instN neN hmodel
  · exact hmodel ρ hρ

/-- The recurring shape: the new sentence is licensed by a **member** `ρ` of the side. -/
private theorem budgetedPairInsep_insert_of_member_left {ρ : L[[ℕ]].Sentenceω} (hρ : ρ ∈ Γ)
    (hent : Theoryω.Entails Γ σ)
    (hc : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ sentenceJConsts (L' := L) (J := ℕ) ρ)
    (hq : hasQuantSigned true σ → hasQuantSigned true ρ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert σ Γ) Δ :=
  budgetedPairInsep_insert_entailed_left hent
    (hc.trans (sentenceJConsts_subset_theoryJConsts hρ))
    (fun hqσ => Theoryω.hasQuantSigned_of_mem hρ (hq hqσ)) h

private theorem budgetedPairInsep_insert_of_member_right {ρ : L[[ℕ]].Sentenceω} (hρ : ρ ∈ Δ)
    (hent : Theoryω.Entails Δ σ)
    (hc : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ sentenceJConsts (L' := L) (J := ℕ) ρ)
    (hq : hasQuantSigned true σ → hasQuantSigned true ρ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert σ Δ) :=
  budgetedPairInsep_insert_entailed_right hent
    (hc.trans (sentenceJConsts_subset_theoryJConsts hρ))
    (fun hqσ => Theoryω.hasQuantSigned_of_mem hρ (hq hqσ)) h

/-! ## The deterministic connective fields

C2 (double negation), C1′ (negated implication, both components), C3 (conjunction component) and C4′
(negated-disjunction component), on each label.  Each is three obligations against the parent. -/

section Deterministic

variable {φ ψ : L[[ℕ]].Sentenceω} {φs : ℕ → L[[ℕ]].Sentenceω} {k : ℕ}

/-- C2, left. -/
private theorem budgetedPairInsep_not_not_left (hmem : φ.not.not ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert φ Γ) Δ := by
  refine budgetedPairInsep_insert_of_member_left hmem ?_ ?_ ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_not,
      not_not] at this
    exact this
  · rw [sentenceJConsts_not, sentenceJConsts_not]
  · intro hq
    rw [hasQuantSigned_not, hasQuantSigned_not]
    exact hq

/-- C2, right. -/
private theorem budgetedPairInsep_not_not_right (hmem : φ.not.not ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert φ Δ) := by
  refine budgetedPairInsep_insert_of_member_right hmem ?_ ?_ ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_not,
      not_not] at this
    exact this
  · rw [sentenceJConsts_not, sentenceJConsts_not]
  · intro hq
    rw [hasQuantSigned_not, hasQuantSigned_not]
    exact hq

/-- C1′ antecedent, left. -/
private theorem budgetedPairInsep_neg_imp_left₁ (hmem : (φ.imp ψ).not ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert φ Γ) Δ := by
  refine budgetedPairInsep_insert_of_member_left hmem ?_ ?_ ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp,
      Classical.not_imp] at this
    exact this.1
  · rw [sentenceJConsts_not]; exact sentenceJConsts_imp_left φ ψ
  · intro hq
    rw [hasQuantSigned_not, hasQuantSigned_imp]
    exact Or.inl hq

/-- C1′ consequent, left. -/
private theorem budgetedPairInsep_neg_imp_left₂ (hmem : (φ.imp ψ).not ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert ψ.not Γ) Δ := by
  refine budgetedPairInsep_insert_of_member_left hmem ?_ ?_ ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp,
      Classical.not_imp] at this
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    exact this.2
  · rw [sentenceJConsts_not, sentenceJConsts_not]; exact sentenceJConsts_imp_right φ ψ
  · intro hq
    rw [hasQuantSigned_not, hasQuantSigned_imp]
    rw [hasQuantSigned_not] at hq
    exact Or.inr hq

/-- C1′ antecedent, right. -/
private theorem budgetedPairInsep_neg_imp_right₁ (hmem : (φ.imp ψ).not ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert φ Δ) := by
  refine budgetedPairInsep_insert_of_member_right hmem ?_ ?_ ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp,
      Classical.not_imp] at this
    exact this.1
  · rw [sentenceJConsts_not]; exact sentenceJConsts_imp_left φ ψ
  · intro hq
    rw [hasQuantSigned_not, hasQuantSigned_imp]
    exact Or.inl hq

/-- C1′ consequent, right. -/
private theorem budgetedPairInsep_neg_imp_right₂ (hmem : (φ.imp ψ).not ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert ψ.not Δ) := by
  refine budgetedPairInsep_insert_of_member_right hmem ?_ ?_ ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp,
      Classical.not_imp] at this
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    exact this.2
  · rw [sentenceJConsts_not, sentenceJConsts_not]; exact sentenceJConsts_imp_right φ ψ
  · intro hq
    rw [hasQuantSigned_not, hasQuantSigned_imp]
    rw [hasQuantSigned_not] at hq
    exact Or.inr hq

/-- C3, left: a conjunction component. -/
private theorem budgetedPairInsep_iInf_component_left (hmem : BoundedFormulaω.iInf φs ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (φs k) Γ) Δ := by
  refine budgetedPairInsep_insert_of_member_left hmem ?_ (sentenceJConsts_component_iInf φs k) ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_iInf] at this
    exact this k
  · intro hq
    rw [hasQuantSigned_iInf]
    exact ⟨k, hq⟩

/-- C3, right. -/
private theorem budgetedPairInsep_iInf_component_right (hmem : BoundedFormulaω.iInf φs ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (φs k) Δ) := by
  refine budgetedPairInsep_insert_of_member_right hmem ?_ (sentenceJConsts_component_iInf φs k) ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_iInf] at this
    exact this k
  · intro hq
    rw [hasQuantSigned_iInf]
    exact ⟨k, hq⟩

/-- C4′, left: a negated-disjunction component. -/
private theorem budgetedPairInsep_neg_iSup_component_left (hmem : (BoundedFormulaω.iSup φs).not ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (φs k).not Γ) Δ := by
  refine budgetedPairInsep_insert_of_member_left hmem ?_ ?_ ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iSup,
      not_exists] at this
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    exact this k
  · rw [sentenceJConsts_not, sentenceJConsts_not]
    exact sentenceJConsts_component_iSup φs k
  · intro hq
    rw [hasQuantSigned_not, hasQuantSigned_iSup]
    rw [hasQuantSigned_not] at hq
    exact ⟨k, hq⟩

/-- C4′, right. -/
private theorem budgetedPairInsep_neg_iSup_component_right (hmem : (BoundedFormulaω.iSup φs).not ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (φs k).not Δ) := by
  refine budgetedPairInsep_insert_of_member_right hmem ?_ ?_ ?_ h
  · intro N instN _ hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iSup,
      not_exists] at this
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    exact this k
  · rw [sentenceJConsts_not, sentenceJConsts_not]
    exact sentenceJConsts_component_iSup φs k
  · intro hq
    rw [hasQuantSigned_not, hasQuantSigned_iSup]
    rw [hasQuantSigned_not] at hq
    exact ⟨k, hq⟩

end Deterministic


/-! ## Countable branching — the last isolated gate

The `⋁`-style fields, where the consumer must *choose* a component.  Each is proved by
contraposition: assume every component extension is separable, choose its separator `θₙ`, combine
with `iSup` or `iInf` according to the label, and check the five conditions **componentwise**.

Three things are worth watching, and all three come out clean:

* the combined separator's constant support is the **union** of the component supports, and each
  component support already lies in both theory supports — because inserting a component does not
  enlarge the receiving side's support, the parent already carrying its constants;
* `hasQuantSigned` on `iSup`/`iInf` **exposes one offending component**, so the permission flows from
  that component's separator and then from the parent formula, again by non-growth;
* no label projection and no support enlargement appears anywhere.
-/

section CountableBranching

variable {φs : ℕ → L[[ℕ]].Sentenceω}

/-- The `iInf`-analogues of the `iSup` union bounds. -/
private theorem baseFunctionsIn_iInf_subset {A : Set (Σ n, L.Functions n)}
    (τ : ℕ → L[[ℕ]].Sentenceω) (hτ : ∀ k, (τ k).baseFunctionsIn ⊆ A) :
    (BoundedFormulaω.iInf τ).baseFunctionsIn ⊆ A := by
  intro s hs
  simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_iUnion] at hs
  obtain ⟨k, hk⟩ := hs
  exact hτ k hk

private theorem baseRelationsIn_iInf_subset {A : Set (Σ n, L.Relations n)}
    (τ : ℕ → L[[ℕ]].Sentenceω) (hτ : ∀ k, (τ k).baseRelationsIn ⊆ A) :
    (BoundedFormulaω.iInf τ).baseRelationsIn ⊆ A := by
  intro s hs
  simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_ofPred_eq,
    Set.mem_iUnion] at hs
  obtain ⟨k, hk⟩ := hs
  exact hτ k hk

private theorem sentenceJConsts_iInf_subset {A : Set ℕ} (τ : ℕ → L[[ℕ]].Sentenceω)
    (hτ : ∀ k, sentenceJConsts (L' := L) (J := ℕ) (τ k) ⊆ A) :
    sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iInf τ) ⊆ A := by
  intro j hj
  simp only [sentenceJConsts, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq, Set.mem_iUnion] at hj
  obtain ⟨k, hk⟩ := hj
  exact hτ k hk

/-- **C4, left: countable disjunction.**  Separator `⋁ₙ θₙ`. -/
private theorem budgetedPairInsep_iSup_left (hmem : BoundedFormulaω.iSup φs ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    ∃ k, BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (φs k) Γ) Δ := by
  by_contra hcon
  push Not at hcon
  simp only [BudgetedPairInsep, not_not] at hcon
  choose θ hsep using hcon
  have hcΓ : ∀ n, theoryJConsts (L := L) (insert (φs n) Γ) = theoryJConsts Γ := fun n =>
    theoryJConsts_insert_of_subset
      ((sentenceJConsts_component_iSup φs n).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have huΓ : ∀ n, Theoryω.HasQuantSigned true (insert (φs n) Γ)
      ↔ Theoryω.HasQuantSigned true Γ := fun n =>
    Theoryω.hasQuantSigned_insert_of_le fun hq =>
      Theoryω.hasQuantSigned_of_mem hmem ((hasQuantSigned_iSup true φs).mpr ⟨n, hq⟩)
  refine h ⟨BoundedFormulaω.iSup θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN neN hmodel
    have hiSup := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_iSup] at hiSup
    obtain ⟨n, hn⟩ := hiSup
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_iSup]
    have hEn := (hsep n).1
    exact ⟨n, @hEn N instN neN fun ρ hρ => by
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact hn
      · exact hmodel ρ hρ⟩
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iSup, not_exists]
    intro n hn
    have hNn := (hsep n).2.1
    have := @hNn N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at this
    exact this hn
  · exact ⟨baseFunctionsIn_iSup_subset θ fun n => (hsep n).2.2.1.1,
      baseRelationsIn_iSup_subset θ fun n => (hsep n).2.2.1.2⟩
  · refine sentenceJConsts_iSup_subset θ fun n => ?_
    have := (hsep n).2.2.2.1
    rwa [hcΓ n] at this
  · intro hq
    replace hq : hasQuantSigned true (BoundedFormulaω.iSup θ) := hq
    rw [hasQuantSigned_iSup] at hq
    obtain ⟨n, hn⟩ := hq
    exact (huΓ n).mp ((hsep n).2.2.2.2.1 hn)
  · intro hq
    replace hq : hasQuantSigned false (BoundedFormulaω.iSup θ) := hq
    rw [hasQuantSigned_iSup] at hq
    obtain ⟨n, hn⟩ := hq
    exact (hsep n).2.2.2.2.2 hn

/-- **C4, right: countable disjunction.**  Separator `⋀ₙ θₙ`. -/
private theorem budgetedPairInsep_iSup_right (hmem : BoundedFormulaω.iSup φs ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    ∃ k, BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (φs k) Δ) := by
  by_contra hcon
  push Not at hcon
  simp only [BudgetedPairInsep, not_not] at hcon
  choose θ hsep using hcon
  have hcΔ : ∀ n, theoryJConsts (L := L) (insert (φs n) Δ) = theoryJConsts Δ := fun n =>
    theoryJConsts_insert_of_subset
      ((sentenceJConsts_component_iSup φs n).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have huΔ : ∀ n, Theoryω.HasQuantSigned true (insert (φs n) Δ)
      ↔ Theoryω.HasQuantSigned true Δ := fun n =>
    Theoryω.hasQuantSigned_insert_of_le fun hq =>
      Theoryω.hasQuantSigned_of_mem hmem ((hasQuantSigned_iSup true φs).mpr ⟨n, hq⟩)
  refine h ⟨BoundedFormulaω.iInf θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_iInf]
    intro n
    have hEn := (hsep n).1
    exact @hEn N instN neN hmodel
  · intro N instN neN hmodel
    have hiSup := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_iSup] at hiSup
    obtain ⟨n, hn⟩ := hiSup
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iInf, not_forall]
    have hNn := (hsep n).2.1
    have := @hNn N instN neN fun ρ hρ => by
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact hn
      · exact hmodel ρ hρ
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at this
    exact ⟨n, this⟩
  · exact ⟨baseFunctionsIn_iInf_subset θ fun n => (hsep n).2.2.1.1,
      baseRelationsIn_iInf_subset θ fun n => (hsep n).2.2.1.2⟩
  · refine sentenceJConsts_iInf_subset θ fun n => ?_
    have := (hsep n).2.2.2.1
    rwa [hcΔ n] at this
  · intro hq
    replace hq : hasQuantSigned true (BoundedFormulaω.iInf θ) := hq
    rw [hasQuantSigned_iInf] at hq
    obtain ⟨n, hn⟩ := hq
    exact (hsep n).2.2.2.2.1 hn
  · intro hq
    replace hq : hasQuantSigned false (BoundedFormulaω.iInf θ) := hq
    rw [hasQuantSigned_iInf] at hq
    obtain ⟨n, hn⟩ := hq
    exact (huΔ n).mp ((hsep n).2.2.2.2.2 hn)

/-- **C3′, left: negated countable conjunction.**  Separator `⋁ₙ θₙ`. -/
private theorem budgetedPairInsep_neg_iInf_left (hmem : (BoundedFormulaω.iInf φs).not ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    ∃ k, BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (φs k).not Γ) Δ := by
  by_contra hcon
  push Not at hcon
  simp only [BudgetedPairInsep, not_not] at hcon
  choose θ hsep using hcon
  have hcΓ : ∀ n, theoryJConsts (L := L) (insert (φs n).not Γ) = theoryJConsts Γ := fun n =>
    theoryJConsts_insert_of_subset (by
      rw [sentenceJConsts_not]
      refine (sentenceJConsts_component_iInf φs n).trans ?_
      rw [← sentenceJConsts_not (L' := L) (BoundedFormulaω.iInf φs)]
      exact sentenceJConsts_subset_theoryJConsts hmem)
  have huΓ : ∀ n, Theoryω.HasQuantSigned true (insert (φs n).not Γ)
      ↔ Theoryω.HasQuantSigned true Γ := fun n =>
    Theoryω.hasQuantSigned_insert_of_le fun hq => by
      refine Theoryω.hasQuantSigned_of_mem hmem ?_
      rw [hasQuantSigned_not, hasQuantSigned_iInf]
      rw [hasQuantSigned_not] at hq
      exact ⟨n, hq⟩
  refine h ⟨BoundedFormulaω.iSup θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN neN hmodel
    have hneg := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iInf,
      not_forall] at hneg
    obtain ⟨n, hn⟩ := hneg
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_iSup]
    have hEn := (hsep n).1
    exact ⟨n, @hEn N instN neN fun ρ hρ => by
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]; exact hn
      · exact hmodel ρ hρ⟩
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iSup, not_exists]
    intro n hn
    have hNn := (hsep n).2.1
    have := @hNn N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at this
    exact this hn
  · exact ⟨baseFunctionsIn_iSup_subset θ fun n => (hsep n).2.2.1.1,
      baseRelationsIn_iSup_subset θ fun n => (hsep n).2.2.1.2⟩
  · refine sentenceJConsts_iSup_subset θ fun n => ?_
    have := (hsep n).2.2.2.1
    rwa [hcΓ n] at this
  · intro hq
    replace hq : hasQuantSigned true (BoundedFormulaω.iSup θ) := hq
    rw [hasQuantSigned_iSup] at hq
    obtain ⟨n, hn⟩ := hq
    exact (huΓ n).mp ((hsep n).2.2.2.2.1 hn)
  · intro hq
    replace hq : hasQuantSigned false (BoundedFormulaω.iSup θ) := hq
    rw [hasQuantSigned_iSup] at hq
    obtain ⟨n, hn⟩ := hq
    exact (hsep n).2.2.2.2.2 hn

/-- **C3′, right: negated countable conjunction.**  Separator `⋀ₙ θₙ`. -/
private theorem budgetedPairInsep_neg_iInf_right (hmem : (BoundedFormulaω.iInf φs).not ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    ∃ k, BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (φs k).not Δ) := by
  by_contra hcon
  push Not at hcon
  simp only [BudgetedPairInsep, not_not] at hcon
  choose θ hsep using hcon
  have hcΔ : ∀ n, theoryJConsts (L := L) (insert (φs n).not Δ) = theoryJConsts Δ := fun n =>
    theoryJConsts_insert_of_subset (by
      rw [sentenceJConsts_not]
      refine (sentenceJConsts_component_iInf φs n).trans ?_
      rw [← sentenceJConsts_not (L' := L) (BoundedFormulaω.iInf φs)]
      exact sentenceJConsts_subset_theoryJConsts hmem)
  have huΔ : ∀ n, Theoryω.HasQuantSigned true (insert (φs n).not Δ)
      ↔ Theoryω.HasQuantSigned true Δ := fun n =>
    Theoryω.hasQuantSigned_insert_of_le fun hq => by
      refine Theoryω.hasQuantSigned_of_mem hmem ?_
      rw [hasQuantSigned_not, hasQuantSigned_iInf]
      rw [hasQuantSigned_not] at hq
      exact ⟨n, hq⟩
  refine h ⟨BoundedFormulaω.iInf θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_iInf]
    intro n
    have hEn := (hsep n).1
    exact @hEn N instN neN hmodel
  · intro N instN neN hmodel
    have hneg := hmodel _ hmem
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iInf,
      not_forall] at hneg
    obtain ⟨n, hn⟩ := hneg
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_iInf, not_forall]
    have hNn := (hsep n).2.1
    have := @hNn N instN neN fun ρ hρ => by
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]; exact hn
      · exact hmodel ρ hρ
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at this
    exact ⟨n, this⟩
  · exact ⟨baseFunctionsIn_iInf_subset θ fun n => (hsep n).2.2.1.1,
      baseRelationsIn_iInf_subset θ fun n => (hsep n).2.2.1.2⟩
  · refine sentenceJConsts_iInf_subset θ fun n => ?_
    have := (hsep n).2.2.2.1
    rwa [hcΔ n] at this
  · intro hq
    replace hq : hasQuantSigned true (BoundedFormulaω.iInf θ) := hq
    rw [hasQuantSigned_iInf] at hq
    obtain ⟨n, hn⟩ := hq
    exact (hsep n).2.2.2.2.1 hn
  · intro hq
    replace hq : hasQuantSigned false (BoundedFormulaω.iInf θ) := hq
    rw [hasQuantSigned_iInf] at hq
    obtain ⟨n, hn⟩ := hq
    exact (huΔ n).mp ((hsep n).2.2.2.2.2 hn)

end CountableBranching


/-! ## The substitution cut, and the mixed equality cases

Mixed `eq_trans` is the one equality case the shared-hypothesis transfer cannot reach: with `a = b` on
the left and `b = d` on the right, neither side's support contains both endpoints — the pivot `b` is
the only automatically shared constant.  The substitution mechanism that solved mixed `rel_congr`
solves it too, and the two statements genuinely align, so the common core is extracted once.
-/

/-- **Substitution cut, left.**  Insert `ψ` on the left, where `ψ` mentions a constant `c` that only
the right side carries.  If the left entails the `c := b` image of `ψ` and the right proves `b = c`,
then a separator of the extended pair substitutes down to one of the original pair — mentioning the
shared pivot `b` instead of the remote `c`.  `hasQuantSigned_substConst` keeps both budgets fixed. -/
private theorem budgetedPairInsep_substCut_left (b c : ℕ) (ψ : L[[ℕ]].Sentenceω)
    (hcΓ : c ∉ theoryJConsts (L := L) Γ)
    (hbΓ : b ∈ theoryJConsts (L := L) Γ) (hbΔ : b ∈ theoryJConsts (L := L) Δ)
    (hΔeq : Theoryω.Entails Δ (constEq (L := L) b c))
    (hcψ : sentenceJConsts (L' := L) (J := ℕ) ψ ⊆ insert c (theoryJConsts Γ))
    (hqψ : ∀ s : Bool, ¬ hasQuantSigned s ψ)
    (hΓψ : Theoryω.Entails Γ (substConst c b ψ))
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert ψ Γ) Δ := by
  have hcb : c ≠ b := fun hcb' => hcΓ (hcb' ▸ hbΓ)
  rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
  have hcτ : c ∉ sentenceJConsts (L' := L) (J := ℕ) (substConst c b θ) :=
    notMem_sentenceJConsts_substConst c b hcb θ
  refine h ⟨substConst c b θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN neN hmodel
    set base := (L.lhomWithConstants ℕ).reduct N with hbase
    set hm := ambientConstMap (L := L) N with hh
    have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
        @Sentenceω.Realize L[[ℕ]] ρ N instN
          ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
      fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
    have hΓ' : ∀ γ ∈ Γ,
        @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c (hm b))) Empty 0 γ
          Empty.elim Fin.elim0 := by
      intro γ hγ
      have hg : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 γ Empty.elim Fin.elim0 :=
        (bridge _).mp (hmodel _ hγ)
      have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) γ,
          hm k = Function.update hm c (hm b) k := by
        intro k hk
        have hkc : (k : ℕ) ≠ c := fun heqk =>
          hcΓ (heqk ▸ (sentenceJConsts_subset_theoryJConsts hγ) hk)
        exact (Function.update_of_ne (α := ℕ) hkc _ hm).symm
      rwa [BoundedFormulaω.realize_congr_const base γ hcongr Empty.elim Fin.elim0] at hg
    have hψ' : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c (hm b))) Empty 0 ψ
        Empty.elim Fin.elim0 :=
      (realize_substConst base hm c b ψ).mp ((bridge _).mp (@hΓψ N instN neN hmodel))
    have hθ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c (hm b))) Empty 0 θ
        Empty.elim Fin.elim0 :=
      @hE N (wc base (Function.update hm c (hm b))) neN (fun ρ hρ => by
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · exact hψ'
        · exact hΓ' ρ hρ)
    exact (bridge _).mpr ((realize_substConst base hm c b θ).mpr hθ)
  · intro N instN neN hmodel
    set base := (L.lhomWithConstants ℕ).reduct N with hbase
    set hm := ambientConstMap (L := L) N with hh
    have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
        @Sentenceω.Realize L[[ℕ]] ρ N instN
          ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
      fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
    have hval : hm b = hm c := (bridge _).mp (@hΔeq N instN neN hmodel)
    have hupd : Function.update hm c (hm b) = hm := by
      rw [hval, Function.update_eq_self]
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    intro hcontra
    have hθ := (realize_substConst base hm c b θ).mp ((bridge _).mp hcontra)
    rw [hupd] at hθ
    have hn := @hN N instN neN hmodel
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hn
    exact hn ((bridge _).mpr hθ)
  · exact ⟨(baseFunctionsIn_substConst_subset c b θ).trans hbnd.1,
      (baseRelationsIn_substConst c b θ).trans hbnd.2⟩
  · intro k hk
    rcases sentenceJConsts_substConst_subset c b θ hk with hk' | hk'
    · have hkc : k ≠ c := fun heqk => hcτ (heqk ▸ hk)
      refine ⟨?_, (hc hk').2⟩
      have hmem := (hc hk').1
      rw [theoryJConsts_insert] at hmem
      rcases hmem with hmem | hmem
      · rcases hcψ hmem with hmem' | hmem'
        · exact absurd hmem' hkc
        · exact hmem'
      · exact hmem
    · rw [Set.mem_singleton_iff] at hk'
      subst hk'
      exact ⟨hbΓ, hbΔ⟩
  · intro hq
    have hqθ : hasQuantSigned true θ := (hasQuantSigned_substConst c b true θ).mp hq
    rcases Theoryω.hasQuantSigned_insert.mp (hu hqθ) with hq' | hq'
    · exact absurd hq' (hqψ true)
    · exact hq'
  · intro hq
    exact hx ((hasQuantSigned_substConst c b false θ).mp hq)

/-- **Substitution cut, right.**  The mirror of `budgetedPairInsep_substCut_left`: `ψ` goes onto the
right, mentioning a constant `c` that only the *left* side carries, and it is the left that proves
`b = c`.  Same separator operation, sides exchanged. -/
private theorem budgetedPairInsep_substCut_right (b c : ℕ) (ψ : L[[ℕ]].Sentenceω)
    (hcΔ : c ∉ theoryJConsts (L := L) Δ)
    (hbΓ : b ∈ theoryJConsts (L := L) Γ) (hbΔ : b ∈ theoryJConsts (L := L) Δ)
    (hΓeq : Theoryω.Entails Γ (constEq (L := L) b c))
    (hcψ : sentenceJConsts (L' := L) (J := ℕ) ψ ⊆ insert c (theoryJConsts Δ))
    (hqψ : ∀ s : Bool, ¬ hasQuantSigned s ψ)
    (hΔψ : Theoryω.Entails Δ (substConst c b ψ))
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert ψ Δ) := by
  have hcb : c ≠ b := fun hcb' => hcΔ (hcb' ▸ hbΔ)
  rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
  have hcτ : c ∉ sentenceJConsts (L' := L) (J := ℕ) (substConst c b θ) :=
    notMem_sentenceJConsts_substConst c b hcb θ
  refine h ⟨substConst c b θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the left side proves `b = c`, so the reinterpretation is the identity there
    intro N instN neN hmodel
    set base := (L.lhomWithConstants ℕ).reduct N with hbase
    set hm := ambientConstMap (L := L) N with hh
    have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
        @Sentenceω.Realize L[[ℕ]] ρ N instN
          ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
      fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
    have hval : hm b = hm c := (bridge _).mp (@hΓeq N instN neN hmodel)
    have hupd : Function.update hm c (hm b) = hm := by rw [hval, Function.update_eq_self]
    have hθ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 θ Empty.elim Fin.elim0 :=
      (bridge _).mp (@hE N instN neN hmodel)
    refine (bridge _).mpr ((realize_substConst base hm c b θ).mpr ?_)
    rw [hupd]; exact hθ
  · -- the right side received `ψ`; reinterpret `c` at `b`'s value to rebuild its model
    intro N instN neN hmodel
    set base := (L.lhomWithConstants ℕ).reduct N with hbase
    set hm := ambientConstMap (L := L) N with hh
    have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
        @Sentenceω.Realize L[[ℕ]] ρ N instN
          ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
      fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
    have hΔ' : ∀ δ ∈ Δ,
        @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c (hm b))) Empty 0 δ
          Empty.elim Fin.elim0 := by
      intro δ hδ
      have hg : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 δ Empty.elim Fin.elim0 :=
        (bridge _).mp (hmodel _ hδ)
      have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) δ,
          hm k = Function.update hm c (hm b) k := by
        intro k hk
        have hkc : (k : ℕ) ≠ c := fun heqk =>
          hcΔ (heqk ▸ (sentenceJConsts_subset_theoryJConsts hδ) hk)
        exact (Function.update_of_ne (α := ℕ) hkc _ hm).symm
      rwa [BoundedFormulaω.realize_congr_const base δ hcongr Empty.elim Fin.elim0] at hg
    have hψ' : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c (hm b))) Empty 0 ψ
        Empty.elim Fin.elim0 :=
      (realize_substConst base hm c b ψ).mp ((bridge _).mp (@hΔψ N instN neN hmodel))
    rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
    intro hcontra
    have hθ := (realize_substConst base hm c b θ).mp ((bridge _).mp hcontra)
    exact (@hN N (wc base (Function.update hm c (hm b))) neN (fun ρ hρ => by
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact hψ'
      · exact hΔ' ρ hρ)) hθ
  · exact ⟨(baseFunctionsIn_substConst_subset c b θ).trans hbnd.1,
      (baseRelationsIn_substConst c b θ).trans hbnd.2⟩
  · intro k hk
    rcases sentenceJConsts_substConst_subset c b θ hk with hk' | hk'
    · have hkc : k ≠ c := fun heqk => hcτ (heqk ▸ hk)
      refine ⟨(hc hk').1, ?_⟩
      have hmem := (hc hk').2
      rw [theoryJConsts_insert] at hmem
      rcases hmem with hmem | hmem
      · rcases hcψ hmem with hmem' | hmem'
        · exact absurd hmem' hkc
        · exact hmem'
      · exact hmem
    · rw [Set.mem_singleton_iff] at hk'
      subst hk'
      exact ⟨hbΓ, hbΔ⟩
  · intro hq
    exact hu ((hasQuantSigned_substConst c b true θ).mp hq)
  · intro hq
    have hqθ : hasQuantSigned false θ := (hasQuantSigned_substConst c b false θ).mp hq
    rcases Theoryω.hasQuantSigned_insert.mp (hx hqθ) with hq' | hq'
    · exact absurd hq' (hqψ true)
    · exact hq'

/-- Every atomic relation instance is quantifier-free at both signs. -/
private theorem hasQuantSigned_relInst_false (s : Bool) {l : ℕ} (Rr : L.Relations l)
    (g : Fin l → ℕ) : ¬ hasQuantSigned s (relInst Rr g) := fun hq => hq

/-- Local restatement of the atomic realization equation (definitional; the WellOrdering arc has the
same fact but is not in this file's import closure). -/
private theorem realize_relInst_wc' {M : Type} (base : L.Structure M) (hm : ℕ → M)
    {l : ℕ} (Rr : L.Relations l) (g : Fin l → ℕ) :
    @BoundedFormulaω.Realize L[[ℕ]] M (wc base hm) Empty 0 (relInst Rr g) Empty.elim Fin.elim0
      ↔ @Structure.RelMap L M base l Rr (fun j => hm (g j)) := Iff.rfl

/-- The `b := g i` image of the congruent atom is the original atom, semantically: substituting the
remote constant back at the pivot's value undoes the one-coordinate update. -/
private theorem entails_substConst_relInst {l : ℕ} (Rr : L.Relations l) (g : Fin l → ℕ) (i : Fin l)
    (b : ℕ) (hgb : ∀ j, g j ≠ b) (hmem : relInst Rr g ∈ Δ) :
    Theoryω.Entails Δ (substConst b (g i) (relInst Rr (Function.update g i b))) := by
  intro N instN neN hmodel
  set base := (L.lhomWithConstants ℕ).reduct N with hbase
  set hm := ambientConstMap (L := L) N with hh
  have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ρ N instN
        ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
    fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
  have hr : @Structure.RelMap L N base l Rr (fun j => hm (g j)) :=
    (realize_relInst_wc' base hm Rr g).mp ((bridge _).mp (hmodel _ hmem))
  have key : ∀ j, Function.update hm b (hm (g i)) (Function.update g i b j) = hm (g j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne (hgb j)]
  refine (bridge _).mpr ((realize_substConst base hm b (g i) _).mpr ?_)
  refine (realize_relInst_wc' base (Function.update hm b (hm (g i))) Rr
    (Function.update g i b)).mpr ?_
  convert hr using 2 with j
  exact key j

/-- **Mixed relation congruence, reverse labels.**  The fourth `rel_congr` distribution: the atom on
the right, the equation on the left.  A short application of the right substitution cut — the pivot
is `g i` (shared: on the right by the atom, on the left by the equation) and the remote constant is
the replacement `b`, which only the left carries. -/
private theorem budgetedPairInsep_relCongr_mixed_rev {l : ℕ} (Rr : L.Relations l) (g : Fin l → ℕ)
    (i : Fin l) (b : ℕ) (hrel : relInst Rr g ∈ Δ) (heq : constEq (L := L) (g i) b ∈ Γ)
    (hbΔ : b ∉ theoryJConsts (L := L) Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (relInst Rr (Function.update g i b)) Δ) := by
  have hgΔ : ∀ j, g j ∈ theoryJConsts (L := L) Δ := fun j =>
    (sentenceJConsts_subset_theoryJConsts hrel)
      (by rw [sentenceJConsts_relInst_eq]; exact Set.mem_range_self j)
  have hgb : ∀ j, g j ≠ b := fun j hj => hbΔ (hj ▸ hgΔ j)
  refine budgetedPairInsep_substCut_right (g i) b _ hbΔ ?_ (hgΔ i) ?_ ?_ ?_
    (entails_substConst_relInst Rr g i b hgb hrel) h
  · exact (sentenceJConsts_subset_theoryJConsts heq) (mem_sentenceJConsts_constEq_left (g i) b)
  · exact Theoryω.entails_of_mem heq
  · intro k hk
    rw [sentenceJConsts_relInst_eq] at hk
    obtain ⟨j, rfl⟩ := hk
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact Set.mem_insert _ _
    · rw [Function.update_of_ne hj]; exact Set.mem_insert_of_mem _ (hgΔ j)
  · intro s; exact hasQuantSigned_relInst_false s Rr _

section Equality

variable {a b d : ℕ}

/-- `Γ` proves the `c := b` image of `a = c` exactly when it proves `a = b`. -/
private theorem entails_substConst_constEq (hac : a ≠ c) (hmem : constEq (L := L) a b ∈ Γ) :
    Theoryω.Entails Γ (substConst c b (constEq (L := L) a c)) := by
  intro N instN neN hmodel
  set base := (L.lhomWithConstants ℕ).reduct N with hbase
  set hm := ambientConstMap (L := L) N with hh
  have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ρ N instN
        ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
    fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
  refine (bridge _).mpr ((realize_substConst base hm c b (constEq a c)).mpr ?_)
  show Function.update hm c (hm b) a = Function.update hm c (hm b) c
  rw [Function.update_of_ne hac, Function.update_self]
  exact (bridge _).mp (hmodel _ hmem)

/-- **Mixed transitivity, remote right endpoint.**  `a = b` on the left, `b = d` on the right, `d`
absent from the left: insert `a = d` on the left, substituting the pivot `b` for `d`. -/
private theorem budgetedPairInsep_eq_trans_mixed_right (hab : constEq (L := L) a b ∈ Γ)
    (hbd : constEq (L := L) b d ∈ Δ) (hdΓ : d ∉ theoryJConsts (L := L) Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (constEq (L := L) a d) Γ) Δ := by
  have haΓ : a ∈ theoryJConsts (L := L) Γ :=
    (sentenceJConsts_subset_theoryJConsts hab) (mem_sentenceJConsts_constEq_left a b)
  have hbΓ : b ∈ theoryJConsts (L := L) Γ :=
    (sentenceJConsts_subset_theoryJConsts hab) (mem_sentenceJConsts_constEq_right a b)
  have hbΔ : b ∈ theoryJConsts (L := L) Δ :=
    (sentenceJConsts_subset_theoryJConsts hbd) (mem_sentenceJConsts_constEq_left b d)
  have had : a ≠ d := fun heq => hdΓ (heq ▸ haΓ)
  refine budgetedPairInsep_substCut_left b d _ hdΓ hbΓ hbΔ (Theoryω.entails_of_mem hbd) ?_ ?_
    (entails_substConst_constEq had hab) h
  · refine (sentenceJConsts_constEq_subset a d).trans ?_
    intro k hk
    rcases hk with hk | hk
    · exact Set.mem_insert_of_mem _ (hk ▸ haΓ)
    · exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hk))
  · intro s hq
    exact hq

/-- **Mixed transitivity, remote left endpoint.**  `a = b` on the right, `b = d` on the left, `a`
absent from the left: insert `a = d` on the left, substituting the pivot `b` for `a`. -/
private theorem budgetedPairInsep_eq_trans_mixed_left (hab : constEq (L := L) a b ∈ Δ)
    (hbd : constEq (L := L) b d ∈ Γ) (haΓ : a ∉ theoryJConsts (L := L) Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (constEq (L := L) a d) Γ) Δ := by
  have hbΓ : b ∈ theoryJConsts (L := L) Γ :=
    (sentenceJConsts_subset_theoryJConsts hbd) (mem_sentenceJConsts_constEq_left b d)
  have hdΓ : d ∈ theoryJConsts (L := L) Γ :=
    (sentenceJConsts_subset_theoryJConsts hbd) (mem_sentenceJConsts_constEq_right b d)
  have hbΔ : b ∈ theoryJConsts (L := L) Δ :=
    (sentenceJConsts_subset_theoryJConsts hab) (mem_sentenceJConsts_constEq_right a b)
  have hda : d ≠ a := fun heq => haΓ (heq ▸ hdΓ)
  -- the right side proves `b = a`, the pivot form the cut needs
  have hΔeq : Theoryω.Entails Δ (constEq (L := L) b a) := by
    intro N instN neN hmodel
    have := hmodel _ hab
    rw [Sentenceω.realize_def] at this ⊢
    exact this.symm
  -- and the left entails the `a := b` image of `a = d`, namely `b = d` read symmetrically
  have hΓψ : Theoryω.Entails Γ (substConst a b (constEq (L := L) a d)) := by
    intro N instN neN hmodel
    set base := (L.lhomWithConstants ℕ).reduct N with hbase
    set hm := ambientConstMap (L := L) N with hh
    have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
        @Sentenceω.Realize L[[ℕ]] ρ N instN
          ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
      fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
    refine (bridge _).mpr ((realize_substConst base hm a b (constEq a d)).mpr ?_)
    show Function.update hm a (hm b) a = Function.update hm a (hm b) d
    rw [Function.update_self, Function.update_of_ne hda]
    exact (bridge _).mp (hmodel _ hbd)
  refine budgetedPairInsep_substCut_left b a _ haΓ hbΓ hbΔ hΔeq ?_ ?_ hΓψ h
  · refine (sentenceJConsts_constEq_subset a d).trans ?_
    intro k hk
    rcases hk with hk | hk
    · exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hk))
    · exact Set.mem_insert_of_mem _ (hk ▸ hdΓ)
  · intro s hq
    exact hq

end Equality


/-! ## The remaining equality fields

`eq_refl`, `eq_symm`, and same-label `eq_trans`, on each label.  All are entailed-insertion driver
applications: the atoms are quantifier-free, so the budget obligations are vacuous, and only the
constant obligation carries information. -/

section EqualityFields

variable {a b d c : ℕ}

/-- Every constant equality atom is quantifier-free at both signs. -/
private theorem hasQuantSigned_constEq_false (s : Bool) (a b : ℕ) :
    ¬ hasQuantSigned s (constEq (L := L) a b) := fun hq => hq

/-- `eq_refl`, left.  Legal whenever `c` is already on the left, or absent from the right — together
with the right twin this covers every constant. -/
private theorem budgetedPairInsep_eq_refl_left
    (hc : c ∈ theoryJConsts (L := L) Γ ∨ c ∉ theoryJConsts (L := L) Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (constEq (L := L) c c) Γ) Δ := by
  rcases hc with hc | hc
  · refine budgetedPairInsep_insert_entailed_left (entails_constEq_refl c) ?_ ?_ h
    · exact (sentenceJConsts_constEq_subset c c).trans (by
        intro k hk; rcases hk with hk | hk <;> exact hk ▸ hc)
    · intro hq; exact absurd hq (hasQuantSigned_constEq_false true c c)
  -- `c` is on neither side's right support, so it cannot enter the separator at all
  · rintro ⟨θ, hE, hN, hbnd, hcθ, hu, hx⟩
    refine h ⟨θ, ?_, hN, hbnd, ?_, ?_, hx⟩
    · intro N instN neN hmodel
      refine @hE N instN neN fun ρ hρ => ?_
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact @entails_constEq_refl L Γ c N instN neN hmodel
      · exact hmodel ρ hρ
    · intro k hk
      refine ⟨?_, (hcθ hk).2⟩
      have hkc : k ≠ c := fun heqk => hc (heqk ▸ (hcθ hk).2)
      have hmem := (hcθ hk).1
      rw [theoryJConsts_insert] at hmem
      rcases hmem with hmem | hmem
      · rcases sentenceJConsts_constEq_subset c c hmem with hmem' | hmem'
        · exact absurd hmem' hkc
        · exact absurd (Set.mem_singleton_iff.mp hmem') hkc
      · exact hmem
    · intro hq
      rcases Theoryω.hasQuantSigned_insert.mp (hu hq) with hq' | hq'
      · exact absurd hq' (hasQuantSigned_constEq_false true c c)
      · exact hq'

/-- `eq_symm`, left. -/
private theorem budgetedPairInsep_eq_symm_left (hmem : constEq (L := L) a b ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (constEq (L := L) b a) Γ) Δ := by
  refine budgetedPairInsep_insert_of_member_left hmem ?_ ?_ ?_ h
  · intro N instN neN hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def] at this ⊢
    exact this.symm
  · rw [← sentenceJConsts_constEq_comm]
  · intro hq; exact absurd hq (hasQuantSigned_constEq_false true b a)

/-- `eq_symm`, right. -/
private theorem budgetedPairInsep_eq_symm_right (hmem : constEq (L := L) a b ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (constEq (L := L) b a) Δ) := by
  refine budgetedPairInsep_insert_of_member_right hmem ?_ ?_ ?_ h
  · intro N instN neN hmodel
    have := hmodel _ hmem
    rw [Sentenceω.realize_def] at this ⊢
    exact this.symm
  · rw [← sentenceJConsts_constEq_comm]
  · intro hq; exact absurd hq (hasQuantSigned_constEq_false true b a)

/-- `eq_trans`, both premises on the left. -/
private theorem budgetedPairInsep_eq_trans_left (hab : constEq (L := L) a b ∈ Γ)
    (hbd : constEq (L := L) b d ∈ Γ) (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (constEq (L := L) a d) Γ) Δ := by
  refine budgetedPairInsep_insert_entailed_left ?_ ?_ ?_ h
  · intro N instN neN hmodel
    have h1 := hmodel _ hab
    have h2 := hmodel _ hbd
    rw [Sentenceω.realize_def] at h1 h2 ⊢
    exact h1.trans h2
  · refine (sentenceJConsts_constEq_subset a d).trans ?_
    intro k hk
    rcases hk with hk | hk
    · exact hk ▸ (sentenceJConsts_subset_theoryJConsts hab) (mem_sentenceJConsts_constEq_left a b)
    · exact (Set.mem_singleton_iff.mp hk) ▸
        (sentenceJConsts_subset_theoryJConsts hbd) (mem_sentenceJConsts_constEq_right b d)
  · intro hq; exact absurd hq (hasQuantSigned_constEq_false true a d)

/-- `eq_trans`, both premises on the right. -/
private theorem budgetedPairInsep_eq_trans_right (hab : constEq (L := L) a b ∈ Δ)
    (hbd : constEq (L := L) b d ∈ Δ) (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (constEq (L := L) a d) Δ) := by
  refine budgetedPairInsep_insert_entailed_right ?_ ?_ ?_ h
  · intro N instN neN hmodel
    have h1 := hmodel _ hab
    have h2 := hmodel _ hbd
    rw [Sentenceω.realize_def] at h1 h2 ⊢
    exact h1.trans h2
  · refine (sentenceJConsts_constEq_subset a d).trans ?_
    intro k hk
    rcases hk with hk | hk
    · exact hk ▸ (sentenceJConsts_subset_theoryJConsts hab) (mem_sentenceJConsts_constEq_left a b)
    · exact (Set.mem_singleton_iff.mp hk) ▸
        (sentenceJConsts_subset_theoryJConsts hbd) (mem_sentenceJConsts_constEq_right b d)
  · intro hq; exact absurd hq (hasQuantSigned_constEq_false true a d)

end EqualityFields

/-! ## Same-side relation congruence, and the right `eq_refl` twin

The two remaining atomic fields.  Both are deterministic: the new sentence is entailed by the
receiving side, its constants are already carried there, and being atomic it contributes no
quantifier occurrence at either sign — so each is an instance of the corresponding driver. -/

section AtomicFields

variable {F₁ F₂ : Set (Σ n, L.Functions n)} {R₁ R₂ : Set (Σ n, L.Relations n)}
  {Γ Δ : Set L[[ℕ]].Sentenceω} {c : ℕ}


/-- `eq_refl`, right — the twin of `budgetedPairInsep_eq_refl_left`; together they cover every
constant. -/
private theorem budgetedPairInsep_eq_refl_right
    (hc : c ∈ theoryJConsts (L := L) Δ ∨ c ∉ theoryJConsts (L := L) Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (constEq (L := L) c c) Δ) := by
  rcases hc with hc | hc
  · refine budgetedPairInsep_insert_entailed_right (entails_constEq_refl c) ?_ ?_ h
    · exact (sentenceJConsts_constEq_subset c c).trans (by
        intro k hk; rcases hk with hk | hk <;> exact hk ▸ hc)
    · intro hq; exact absurd hq (hasQuantSigned_constEq_false true c c)
  · rintro ⟨θ, hE, hN, hbnd, hcθ, hu, hx⟩
    refine h ⟨θ, hE, ?_, hbnd, ?_, hu, ?_⟩
    · intro N instN neN hmodel
      refine @hN N instN neN fun ρ hρ => ?_
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact @entails_constEq_refl L Δ c N instN neN hmodel
      · exact hmodel ρ hρ
    · intro k hk
      refine ⟨(hcθ hk).1, ?_⟩
      have hkc : k ≠ c := fun heqk => hc (heqk ▸ (hcθ hk).1)
      have hmem := (hcθ hk).2
      rw [theoryJConsts_insert] at hmem
      rcases hmem with hmem | hmem
      · rcases sentenceJConsts_constEq_subset c c hmem with hmem' | hmem'
        · exact absurd hmem' hkc
        · exact absurd (Set.mem_singleton_iff.mp hmem') hkc
      · exact hmem
    · intro hq
      rcases Theoryω.hasQuantSigned_insert.mp (hx hq) with hq' | hq'
      · exact absurd hq' (hasQuantSigned_constEq_false true c c)
      · exact hq'

/-- **Same-side relation congruence, left.**  Both premises on `Γ`: the congruent atom is entailed
there, and every constant it mentions — including the replacement `b` — is already carried, `b` by
the equation `constEq (g i) b ∈ Γ` itself.  Contrast `budgetedPairInsep_relCongr_mixed`, where the
equation sits on the opposite side and the separator must be substituted. -/
private theorem budgetedPairInsep_relCongr_left {l : ℕ} (Rr : L.Relations l) (g : Fin l → ℕ) (i : Fin l)
    (b : ℕ) (hrel : relInst Rr g ∈ Γ) (heq : constEq (L := L) (g i) b ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (relInst Rr (Function.update g i b)) Γ) Δ := by
  refine budgetedPairInsep_insert_entailed_left (entails_rel_congr Rr g i b hrel heq) ?_ ?_ h
  · intro k hk
    rw [sentenceJConsts_relInst_eq] at hk
    obtain ⟨j, rfl⟩ := hk
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact (sentenceJConsts_subset_theoryJConsts heq) (mem_sentenceJConsts_constEq_right (g j) b)
    · rw [Function.update_of_ne hj]
      exact (sentenceJConsts_subset_theoryJConsts hrel)
        (by rw [sentenceJConsts_relInst_eq]; exact Set.mem_range_self j)
  · intro hq; exact absurd hq (hasQuantSigned_relInst_false true Rr _)

/-- **Same-side relation congruence, right.** -/
private theorem budgetedPairInsep_relCongr_right {l : ℕ} (Rr : L.Relations l) (g : Fin l → ℕ) (i : Fin l)
    (b : ℕ) (hrel : relInst Rr g ∈ Δ) (heq : constEq (L := L) (g i) b ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (relInst Rr (Function.update g i b)) Δ) := by
  refine budgetedPairInsep_insert_entailed_right (entails_rel_congr Rr g i b hrel heq) ?_ ?_ h
  · intro k hk
    rw [sentenceJConsts_relInst_eq] at hk
    obtain ⟨j, rfl⟩ := hk
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact (sentenceJConsts_subset_theoryJConsts heq) (mem_sentenceJConsts_constEq_right (g j) b)
    · rw [Function.update_of_ne hj]
      exact (sentenceJConsts_subset_theoryJConsts hrel)
        (by rw [sentenceJConsts_relInst_eq]; exact Set.mem_range_self j)
  · intro hq; exact absurd hq (hasQuantSigned_relInst_false true Rr _)

end AtomicFields

/-! ## Universal instantiation — the `all_inst` gate

The first field whose new sentence can carry a constant the side does not yet own.  Two facts make
it go through without strengthening the invariant:

* the **quantifier budget collapses**: the inserted instance can only add occurrences that the
  universal parent `φ.all`, already on the same side, pays for;
* the **constant support grows by at most `{c}`**, so a separator that survives the insertion either
  never mentioned `c` (and transports unchanged) or can be universally generalized over it.
-/

section AllInst

variable {F₁ F₂ : Set (Σ n, L.Functions n)} {R₁ R₂ : Set (Σ n, L.Relations n)}
  {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- `genAll` keeps a sentence inside a side's vocabulary bound: generalization removes a constant,
it never introduces a base symbol. -/
private theorem sentBnd_genAll {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)} (c : ℕ)
    {θ : L[[ℕ]].Sentenceω} (h : θ ∈ SentBnd F R) : genAll c θ ∈ SentBnd F R :=
  ⟨(baseFunctionsIn_genAll_subset c θ).trans h.1,
    (baseRelationsIn_genAll c θ).subset.trans h.2⟩

/-- **Support growth of an instance.**  Inserting `instConst c φ` beside its universal parent
enlarges the side's constant support by at most `{c}`. -/
private theorem theoryJConsts_insert_instConst_subset {φ : L[[ℕ]].BoundedFormulaω Empty 1} {c : ℕ}
    (hmem : φ.all ∈ Γ) :
    theoryJConsts (L := L) (insert (instConst c φ) Γ) ⊆ insert c (theoryJConsts Γ) := by
  intro k hk
  rw [theoryJConsts_insert] at hk
  rcases hk with hk | hk
  · rcases sentenceJConsts_instConst_subset c φ hk with hk | hk
    · exact Set.mem_insert_of_mem _ (sentenceJConsts_subset_theoryJConsts hmem hk)
    · exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hk))
  · exact Set.mem_insert_of_mem _ hk

/-- **Quantifier-budget collapse.**  A side holding a universal sentence has a universal budget
outright — `hasQuantSigned true φ.all` is `true = true ∨ _`, so the parent alone witnesses it.

Stated unconditionally rather than as
`HasQuantSigned true (insert (instConst c φ) Γ) → HasQuantSigned true Γ`: the implication is what the
gate consumes, but it holds vacuously, because the conclusion never depended on the inserted
instance.  Every universal permission demanded of the augmented left side is discharged by this. -/
private theorem hasQuantSigned_true_of_all_mem {φ : L[[ℕ]].BoundedFormulaω Empty 1}
    (hmem : φ.all ∈ Γ) : Theoryω.HasQuantSigned true Γ :=
  ⟨φ.all, hmem, Or.inl rfl⟩

/-- **`all_inst`, left.**  A universal on the left admits *every* constant instance — including
constants the left side does not yet carry, and constants already shared with a separator.  No
freshness hypothesis is required.

The proof splits on whether `Γ` already owns `c`.

* If it does, the instance adds no constant and the separator transports unchanged
  (`budgetedPairInsep_insert_entailed_left`).
* If it does not, a separator of the augmented pair may mention `c`; universally generalizing it to
  `genAll c θ` removes `c`, and freshness for `Γ` — which is exactly this branch's hypothesis —
  licenses `∀`-introduction on the left.  The right side needs no freshness: it refutes `∀x θ(x)` by
  instantiating at `c`'s own interpretation.

Both branches pay the universal permission with `φ.all` itself, never with the instance. -/
private theorem budgetedPairInsep_all_inst_left {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c : ℕ)
    (hmem : φ.all ∈ Γ) (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (instConst c φ) Γ) Δ := by
  have hentΓ : Theoryω.Entails Γ (instConst c φ) :=
    entails_of_mem_of_entails hmem (all_entails_instConst c φ)
  by_cases hcΓ : c ∈ theoryJConsts (L := L) Γ
  · -- the instance introduces nothing new: the deterministic driver applies verbatim
    refine budgetedPairInsep_insert_entailed_left hentΓ ?_
      (fun _ => hasQuantSigned_true_of_all_mem hmem) h
    intro k hk
    rcases sentenceJConsts_instConst_subset c φ hk with hk | hk
    · exact sentenceJConsts_subset_theoryJConsts hmem hk
    · exact Set.mem_singleton_iff.mp hk ▸ hcΓ
  · -- `c` is fresh for `Γ`: abstract it out of the separator
    rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
    have hfresh : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ :=
      notMem_theoryJConsts_iff.mp hcΓ
    have hEΓ : Theoryω.Entails Γ θ := by
      intro N instN neN hmodel
      refine @hE N instN neN fun ρ hρ => ?_
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact @hentΓ N instN neN hmodel
      · exact hmodel ρ hρ
    refine h ⟨genAll c θ, entails_genAll_of_entails hfresh hEΓ,
      entails_not_genAll_of_entails_not_self hN, sentBnd_genAll c hbnd, ?_,
      fun _ => hasQuantSigned_true_of_all_mem hmem, ?_⟩
    · -- every surviving constant is not `c`, hence already on the left
      intro k hk
      have hkθ : k ∈ sentenceJConsts (L' := L) (J := ℕ) θ := sentenceJConsts_genAll_subset c θ hk
      have hkc : k ≠ c := fun hEq => notMem_sentenceJConsts_genAll c θ (hEq ▸ hk)
      refine ⟨?_, (hc hkθ).2⟩
      rcases theoryJConsts_insert_instConst_subset hmem (hc hkθ).1 with hk' | hk'
      · exact absurd hk' hkc
      · exact hk'
    · -- `genAll` adds no negative occurrence
      intro hq
      rw [hasQuantSigned_genAll] at hq
      exact hx (hq.resolve_left (by simp))

/-- `genEx` keeps a sentence inside a side's vocabulary bound. -/
private theorem sentBnd_genEx {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)} (c : ℕ)
    {θ : L[[ℕ]].Sentenceω} (h : θ ∈ SentBnd F R) : genEx c θ ∈ SentBnd F R :=
  ⟨(baseFunctionsIn_genEx_subset c θ).trans h.1,
    (baseRelationsIn_genEx c θ).subset.trans h.2⟩

/-- **The right gate's semantic core.**  If `Δ` together with the instance `φ(c)` refutes `θ`, and
`c` is fresh for `Δ` while the universal parent `φ.all` sits in `Δ`, then `Δ` alone refutes
`∃x θ(x)`.

Given a witness `x` for `genEx c θ`, reinterpret `c` as `x`: freshness preserves every member of
`Δ`, the parent `φ.all ∈ Δ` re-supplies the instance under that reinterpretation, and the hypothesis
then refutes the corresponding instance of `θ`.

Neutral in content — belongs in the eventual `#39` constant-surgery consolidation rather than here. -/
private theorem entails_not_genEx_of_all_inst_entails_not {φ : L[[ℕ]].BoundedFormulaω Empty 1} {c : ℕ}
    {θ : L[[ℕ]].Sentenceω}
    (hfresh : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ) (hmem : φ.all ∈ Δ)
    (hyp : Theoryω.Entails (insert (instConst c φ) Δ) θ.not) :
    Theoryω.Entails Δ (genEx c θ).not := by
  intro M instM neM hmodel
  set base := (L.lhomWithConstants ℕ).reduct M with hbase
  set h := ambientConstMap (L := L) M with hh
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ M instM
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instM) ψ Empty.elim Fin.elim0
  show @Sentenceω.Realize L[[ℕ]] (genEx c θ).not M instM
  rw [Sentenceω.realize_def, BoundedFormulaω.realize_not]
  intro hcon
  obtain ⟨x, hx⟩ := (realize_genEx base h c θ).mp ((bridge _).mp hcon)
  -- freshness transports every member of `Δ` across the reinterpretation `c := x`
  have hΔ : ∀ δ ∈ Δ,
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h c x)) Empty 0 δ
        Empty.elim Fin.elim0 := by
    intro δ hδ
    have hg : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 δ Empty.elim Fin.elim0 :=
      (bridge _).mp (hmodel _ hδ)
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) δ, h k = Function.update h c x k := by
      intro k hk
      have hkc : (k : ℕ) ≠ c := fun heq => hfresh δ hδ (heq ▸ hk)
      exact (Function.update_of_ne (α := ℕ) hkc x h).symm
    rwa [BoundedFormulaω.realize_congr_const base δ hcongr Empty.elim Fin.elim0] at hg
  -- the parent re-supplies the instance under the reinterpretation
  have hinst : @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h c x)) Empty 0
      (instConst c φ) Empty.elim Fin.elim0 :=
    @all_entails_instConst L c φ M (wc base (Function.update h c x)) neM
      (fun ρ hρ => (Set.mem_singleton_iff.mp hρ) ▸ hΔ _ hmem)
  exact (@hyp M (wc base (Function.update h c x)) neM (fun ρ hρ => by
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact hinst
    · exact hΔ ρ hρ)) hx

/-- **`all_inst`, right.**  The mirror of `budgetedPairInsep_all_inst_left`, with `genEx` in place of
`genAll`.

The asymmetry is only in which side abstracts: here `Γ ⊨ genEx c θ` is freshness-free
(`∃`-introduction is weakening), and the work moves to `Δ`, where the fresh-case hypothesis is
exactly what `entails_not_genEx_of_all_inst_entails_not` consumes.  The new *existential* occurrence
is paid outright by `φ.all ∈ Δ`, which witnesses a universal budget on the receiving side. -/
private theorem budgetedPairInsep_all_inst_right {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c : ℕ)
    (hmem : φ.all ∈ Δ) (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (instConst c φ) Δ) := by
  have hentΔ : Theoryω.Entails Δ (instConst c φ) :=
    entails_of_mem_of_entails hmem (all_entails_instConst c φ)
  by_cases hcΔ : c ∈ theoryJConsts (L := L) Δ
  · refine budgetedPairInsep_insert_entailed_right hentΔ ?_
      (fun _ => hasQuantSigned_true_of_all_mem hmem) h
    intro k hk
    rcases sentenceJConsts_instConst_subset c φ hk with hk | hk
    · exact sentenceJConsts_subset_theoryJConsts hmem hk
    · exact Set.mem_singleton_iff.mp hk ▸ hcΔ
  · rintro ⟨θ, hE, hN, hbnd, hc, hu, hx⟩
    have hfresh : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ :=
      notMem_theoryJConsts_iff.mp hcΔ
    refine h ⟨genEx c θ, entails_genEx_of_entails_plain c θ hE,
      entails_not_genEx_of_all_inst_entails_not hfresh hmem hN, sentBnd_genEx c hbnd, ?_, ?_, ?_⟩
    · intro k hk
      have hkθ : k ∈ sentenceJConsts (L' := L) (J := ℕ) θ := sentenceJConsts_genEx_subset c θ hk
      have hkc : k ≠ c := fun hEq => notMem_sentenceJConsts_genEx c θ (hEq ▸ hk)
      refine ⟨(hc hkθ).1, ?_⟩
      rcases theoryJConsts_insert_instConst_subset (Γ := Δ) hmem (hc hkθ).2 with hk' | hk'
      · exact absurd hk' hkc
      · exact hk'
    · -- `genEx` adds no positive occurrence, so the left permission passes through
      intro hq
      rw [hasQuantSigned_genEx] at hq
      exact hu (hq.resolve_left (by simp))
    · -- the new existential occurrence is paid by the universal parent on the right
      intro _
      exact hasQuantSigned_true_of_all_mem hmem

end AllInst


/-! ## The family-level field helpers

One helper per `ConsistencyPropertyEqOn` field, each stated in the structure's own `S ∪ {φ}` shape so
that the final package is pure eta-application.  Every body follows the same four steps: unpack the
labelled decomposition, dispatch on the label of the parent, apply **one** `BudgetedPairInsep` gate,
and repackage with `budgetedPairMem_insert_left`/`_right`.  The `insert`-versus-union normalization is
hidden here via `Set.union_singleton`.

No semantic realization proof appears below; if one is ever needed, a gate is missing. -/

section FamilyFields

variable {F₁ F₂ : Set (Σ n, L.Functions n)} {R₁ R₂ : Set (Σ n, L.Relations n)}
  {r₁ r₂ : L[[ℕ]].Sentenceω} {S : Set L[[ℕ]].Sentenceω}

private theorem budgetedPairMem_subset_U (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S) :
    S ⊆ GenU r₁ r₂ := by
  obtain ⟨Γ, Δ, -, -, hΓU, hΔU, -, -, hSeq, -⟩ := hS
  rw [hSeq]; exact Set.union_subset hΓU hΔU

private theorem budgetedPairMem_C0_no_falsum (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S) :
    (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) ∉ S := by
  obtain ⟨Γ, Δ, -, -, -, -, -, -, hSeq, hA⟩ := hS
  rw [hSeq]
  rintro (hmem | hmem)
  · exact not_budgetedPairInsep_of_falsum_left hmem hA
  · exact not_budgetedPairInsep_of_falsum_right hmem hA

/-- All four label combinations, visibly. -/
private theorem budgetedPairMem_C0_no_contradiction (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φ : L[[ℕ]].Sentenceω) : ¬(φ ∈ S ∧ φ.not ∈ S) := by
  obtain ⟨Γ, Δ, -, -, -, -, hΓb, hΔb, hSeq, hA⟩ := hS
  rintro ⟨hφ, hφn⟩
  rw [hSeq] at hφ hφn
  rcases hφ with hφΓ | hφΔ
  · rcases hφn with hφnΓ | hφnΔ
    · exact not_budgetedPairInsep_of_left_contradiction hφΓ hφnΓ hA
    · exact not_budgetedPairInsep_of_mixed hΓb hΔb hφΓ hφnΔ hA
  · rcases hφn with hφnΓ | hφnΔ
    · exact not_budgetedPairInsep_of_mixed_rev hΓb hΔb hφnΓ hφΔ hA
    · exact not_budgetedPairInsep_of_right_contradiction hφΔ hφnΔ hA

/-- **C1.**  The first field that builds a new member, so it is the one that exercises the whole
repackaging path: label dispatch, the gate's own disjunction, and the `insert`-versus-union
normalization — which is confined to the `simpa only [Set.union_singleton]` at each boundary. -/
private theorem budgetedPairMem_C1_imp (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φ ψ : L[[ℕ]].Sentenceω) (hmem : φ.imp ψ ∈ S) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {φ.not}) ∨
      BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {ψ}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · rcases budgetedPairInsep_imp_left φ ψ hΓ hA with h | h
    · exact Or.inl (by
        simpa only [Set.union_singleton] using
          budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
            (imp_negleft_mem (hΓU hΓ)) (sentBnd_not_iff.mpr (sentBnd_imp_left (hΓb hΓ))) h)
    · exact Or.inr (by
        simpa only [Set.union_singleton] using
          budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
            (imp_right_mem (hΓU hΓ)) (sentBnd_imp_right (hΓb hΓ)) h)
  · rcases budgetedPairInsep_imp_right φ ψ hΔ hA with h | h
    · exact Or.inl (by
        simpa only [Set.union_singleton] using
          budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
            (imp_negleft_mem (hΔU hΔ)) (sentBnd_not_iff.mpr (sentBnd_imp_left (hΔb hΔ))) h)
    · exact Or.inr (by
        simpa only [Set.union_singleton] using
          budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
            (imp_right_mem (hΔU hΔ)) (sentBnd_imp_right (hΔb hΔ)) h)

/-- **C1′.**  A conjunction of two insertions per label, so four gate applications. -/
private theorem budgetedPairMem_C1_neg_imp (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φ ψ : L[[ℕ]].Sentenceω) (hmem : (φ.imp ψ).not ∈ S) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {φ}) ∧
      BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {ψ.not}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · refine ⟨by
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (negimp_left_mem (hΓU hΓ)) (sentBnd_imp_left (sentBnd_not_iff.mp (hΓb hΓ)))
          (budgetedPairInsep_neg_imp_left₁ hΓ hA), by
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (negimp_right_mem (hΓU hΓ))
          (sentBnd_not_iff.mpr (sentBnd_imp_right (sentBnd_not_iff.mp (hΓb hΓ))))
          (budgetedPairInsep_neg_imp_left₂ hΓ hA)⟩
  · refine ⟨by
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (negimp_left_mem (hΔU hΔ)) (sentBnd_imp_left (sentBnd_not_iff.mp (hΔb hΔ)))
          (budgetedPairInsep_neg_imp_right₁ hΔ hA), by
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (negimp_right_mem (hΔU hΔ))
          (sentBnd_not_iff.mpr (sentBnd_imp_right (sentBnd_not_iff.mp (hΔb hΔ))))
          (budgetedPairInsep_neg_imp_right₂ hΔ hA)⟩

/-- **C2.** -/
private theorem budgetedPairMem_C2_not_not (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φ : L[[ℕ]].Sentenceω) (hmem : φ.not.not ∈ S) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {φ}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (negimp_left_mem (φ := φ) (ψ := (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω)) (hΓU hΓ))
        (sentBnd_not_iff.mp (sentBnd_not_iff.mp (hΓb hΓ)))
        (budgetedPairInsep_not_not_left hΓ hA)
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (negimp_left_mem (φ := φ) (ψ := (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω)) (hΔU hΔ))
        (sentBnd_not_iff.mp (sentBnd_not_iff.mp (hΔb hΔ)))
        (budgetedPairInsep_not_not_right hΔ hA)

/-! ### The four countable-connective fields

The two `∀ k` fields select the component up front; the two `∃ k` fields unpack the gate's witness
and return the **same** `k`, so the `GenU`, `SentBnd` and insertion obligations visibly concern one
component.  No witness is constructed here. -/

/-- **C3.** -/
private theorem budgetedPairMem_C3_iInf (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φs : ℕ → L[[ℕ]].Sentenceω) (hmem : BoundedFormulaω.iInf φs ∈ S) (k : ℕ) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {φs k}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (iInf_comp_mem k (hΓU hΓ)) (sentBnd_component_iInf k (hΓb hΓ))
        (budgetedPairInsep_iInf_component_left (k := k) hΓ hA)
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (iInf_comp_mem k (hΔU hΔ)) (sentBnd_component_iInf k (hΔb hΔ))
        (budgetedPairInsep_iInf_component_right (k := k) hΔ hA)

/-- **C4′.** -/
private theorem budgetedPairMem_C4_neg_iSup (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φs : ℕ → L[[ℕ]].Sentenceω) (hmem : (BoundedFormulaω.iSup φs).not ∈ S) (k : ℕ) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {(φs k).not}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (negiSup_comp_mem k (hΓU hΓ))
        (sentBnd_not_iff.mpr (sentBnd_component_iSup k (sentBnd_not_iff.mp (hΓb hΓ))))
        (budgetedPairInsep_neg_iSup_component_left (k := k) hΓ hA)
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (negiSup_comp_mem k (hΔU hΔ))
        (sentBnd_not_iff.mpr (sentBnd_component_iSup k (sentBnd_not_iff.mp (hΔb hΔ))))
        (budgetedPairInsep_neg_iSup_component_right (k := k) hΔ hA)

/-- **C4.**  The gate's witness is returned unchanged. -/
private theorem budgetedPairMem_C4_iSup (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φs : ℕ → L[[ℕ]].Sentenceω) (hmem : BoundedFormulaω.iSup φs ∈ S) :
    ∃ k, BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {φs k}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · obtain ⟨k, hk⟩ := budgetedPairInsep_iSup_left hΓ hA
    exact ⟨k, by
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (iSup_comp_mem k (hΓU hΓ)) (sentBnd_component_iSup k (hΓb hΓ)) hk⟩
  · obtain ⟨k, hk⟩ := budgetedPairInsep_iSup_right hΔ hA
    exact ⟨k, by
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (iSup_comp_mem k (hΔU hΔ)) (sentBnd_component_iSup k (hΔb hΔ)) hk⟩

/-- **C3′.**  The gate's witness is returned unchanged. -/
private theorem budgetedPairMem_C3_neg_iInf (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φs : ℕ → L[[ℕ]].Sentenceω) (hmem : (BoundedFormulaω.iInf φs).not ∈ S) :
    ∃ k, BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {(φs k).not}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · obtain ⟨k, hk⟩ := budgetedPairInsep_neg_iInf_left hΓ hA
    exact ⟨k, by
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (negiInf_comp_mem k (hΓU hΓ))
          (sentBnd_not_iff.mpr (sentBnd_component_iInf k (sentBnd_not_iff.mp (hΓb hΓ)))) hk⟩
  · obtain ⟨k, hk⟩ := budgetedPairInsep_neg_iInf_right hΔ hA
    exact ⟨k, by
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (negiInf_comp_mem k (hΔU hΔ))
          (sentBnd_not_iff.mpr (sentBnd_component_iInf k (sentBnd_not_iff.mp (hΔb hΔ)))) hk⟩

/-! ### The equality fields -/

/-- **`eq_refl`.**  One case split suffices: if the left already carries `c`, insert there; otherwise
`c ∉ theoryJConsts Γ` is exactly the right gate's second disjunct.  The right support is never
inspected. -/
private theorem budgetedPairMem_eq_refl (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S) (c : ℕ) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {constEq (L := L) c c}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  by_cases hcΓ : c ∈ theoryJConsts (L := L) Γ
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (eqRefl_mem c) (sentBnd_constEq c c) (budgetedPairInsep_eq_refl_left (Or.inl hcΓ) hA)
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (eqRefl_mem c) (sentBnd_constEq c c) (budgetedPairInsep_eq_refl_right (Or.inr hcΓ) hA)

/-- **`eq_symm`.** -/
private theorem budgetedPairMem_eq_symm (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S) (a b : ℕ)
    (hmem : constEq (L := L) a b ∈ S) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {constEq (L := L) b a}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (constEq_mem b a) (sentBnd_constEq b a) (budgetedPairInsep_eq_symm_left hΓ hA)
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (constEq_mem b a) (sentBnd_constEq b a) (budgetedPairInsep_eq_symm_right hΔ hA)

/-- **`eq_trans`.**  All four premise distributions, visibly.  Note both mixed gates *derive on `Γ`*
by eliminating a `Γ`-fresh remote endpoint — they are not mirrors indexed by receiving side — so
three of the four cases insert on the left.

When the "remote" endpoint is not actually remote, the mixed gate does not apply: instead transfer
the opposite side's equality onto `Γ` (legal, since it is quantifier-free and `Γ` already carries
both its constants), apply the same-side gate, and drop the transferred premise with
`budgetedPairInsep_antitone_left`. -/
private theorem budgetedPairMem_eq_trans (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S) (a b d : ℕ)
    (hab : constEq (L := L) a b ∈ S) (hbd : constEq (L := L) b d ∈ S) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {constEq (L := L) a d}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hab hbd
  have mkL : ∀ {ρ : L[[ℕ]].Sentenceω}, ρ = constEq (L := L) a d →
      BudgetedPairInsep F₁ R₁ F₂ R₂ (insert ρ Γ) Δ →
      BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {constEq (L := L) a d}) := by
    rintro ρ rfl hins
    simpa only [Set.union_singleton] using
      budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (constEq_mem a d) (sentBnd_constEq a d) hins
  rcases hab with habΓ | habΔ
  · rcases hbd with hbdΓ | hbdΔ
    · -- Γ/Γ
      exact mkL rfl (budgetedPairInsep_eq_trans_left habΓ hbdΓ hA)
    · -- Γ/Δ: remote endpoint `d`
      by_cases hdΓ : d ∈ theoryJConsts (L := L) Γ
      · -- not actually remote: transfer `b = d` left, then drop it
        have htr : BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (constEq (L := L) b d) Γ) Δ :=
          budgetedPairInsep_insert_shared_left hbdΔ (sentBnd_constEq b d) (sentBnd_constEq b d)
            (by
              refine (sentenceJConsts_constEq_subset b d).trans ?_
              intro k hk
              rcases hk with hk | hk
              · exact hk ▸ (sentenceJConsts_subset_theoryJConsts habΓ)
                  (mem_sentenceJConsts_constEq_right a b)
              · exact hk ▸ hdΓ)
            (fun s => hasQuantSigned_constEq_false s b d) hA
        exact mkL rfl (budgetedPairInsep_antitone_left (Set.insert_subset_insert (Set.subset_insert _ _))
          (budgetedPairInsep_eq_trans_left (Set.mem_insert_of_mem _ habΓ)
            (Set.mem_insert _ _) htr))
      · exact mkL rfl (budgetedPairInsep_eq_trans_mixed_right habΓ hbdΔ hdΓ hA)
  · rcases hbd with hbdΓ | hbdΔ
    · -- Δ/Γ: remote endpoint `a`
      by_cases haΓ : a ∈ theoryJConsts (L := L) Γ
      · have htr : BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (constEq (L := L) a b) Γ) Δ :=
          budgetedPairInsep_insert_shared_left habΔ (sentBnd_constEq a b) (sentBnd_constEq a b)
            (by
              refine (sentenceJConsts_constEq_subset a b).trans ?_
              intro k hk
              rcases hk with hk | hk
              · exact hk ▸ haΓ
              · exact hk ▸ (sentenceJConsts_subset_theoryJConsts hbdΓ)
                  (mem_sentenceJConsts_constEq_left b d))
            (fun s => hasQuantSigned_constEq_false s a b) hA
        exact mkL rfl (budgetedPairInsep_antitone_left (Set.insert_subset_insert (Set.subset_insert _ _))
          (budgetedPairInsep_eq_trans_left (Set.mem_insert _ _)
            (Set.mem_insert_of_mem _ hbdΓ) htr))
      · exact mkL rfl (budgetedPairInsep_eq_trans_mixed_left habΔ hbdΓ haΓ hA)
    · -- Δ/Δ
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (constEq_mem a d) (sentBnd_constEq a d)
          (budgetedPairInsep_eq_trans_right habΔ hbdΔ hA)

/-- **`rel_congr`.**  Four distributions.  Same-side cases use the same-side gates; each mixed case
splits on whether the replacement constant is fresh for the *receiving* side, and if it is not,
transfers the equality across, applies the same-side gate, and drops the transferred premise with
antitonicity.  The transfer is legal because the atom supplies the pivot `g i` and the non-fresh
branch supplies `b`. -/
private theorem budgetedPairMem_rel_congr (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    {l : ℕ} (Rr : L.Relations l) (g : Fin l → ℕ) (i : Fin l) (b : ℕ)
    (hrel : relInst Rr g ∈ S) (heq : constEq (L := L) (g i) b ∈ S) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {relInst Rr (Function.update g i b)}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hrel heq
  rcases hrel with hrΓ | hrΔ
  · -- atom on the left
    have hpivΓ : g i ∈ theoryJConsts (L := L) Γ :=
      (sentenceJConsts_subset_theoryJConsts hrΓ)
        (by rw [sentenceJConsts_relInst_eq]; exact Set.mem_range_self i)
    have mk : BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (relInst Rr (Function.update g i b)) Γ) Δ →
        BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {relInst Rr (Function.update g i b)}) := by
      intro hins
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (relInst_mem Rr (Function.update g i b))
          (sentBnd_relInst_congr Rr (Function.update g i b) (hΓb hrΓ)) hins
    rcases heq with heqΓ | heqΔ
    · exact mk (budgetedPairInsep_relCongr_left Rr g i b hrΓ heqΓ hA)
    · by_cases hbΓ : b ∈ theoryJConsts (L := L) Γ
      · have htr : BudgetedPairInsep F₁ R₁ F₂ R₂ (insert (constEq (L := L) (g i) b) Γ) Δ :=
          budgetedPairInsep_insert_shared_left heqΔ (sentBnd_constEq _ _) (sentBnd_constEq _ _)
            (by
              refine (sentenceJConsts_constEq_subset (g i) b).trans ?_
              intro k hk
              rcases hk with hk | hk
              · exact hk ▸ hpivΓ
              · exact hk ▸ hbΓ)
            (fun s => hasQuantSigned_constEq_false s _ _) hA
        exact mk (budgetedPairInsep_antitone_left
          (Set.insert_subset_insert (Set.subset_insert _ _))
          (budgetedPairInsep_relCongr_left Rr g i b (Set.mem_insert_of_mem _ hrΓ)
            (Set.mem_insert _ _) htr))
      · exact mk (budgetedPairInsep_relCongr_mixed Rr g i b hrΓ heqΔ hbΓ hA)
  · -- atom on the right
    have hpivΔ : g i ∈ theoryJConsts (L := L) Δ :=
      (sentenceJConsts_subset_theoryJConsts hrΔ)
        (by rw [sentenceJConsts_relInst_eq]; exact Set.mem_range_self i)
    have mk : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (relInst Rr (Function.update g i b)) Δ) →
        BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {relInst Rr (Function.update g i b)}) := by
      intro hins
      simpa only [Set.union_singleton] using
        budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
          (relInst_mem Rr (Function.update g i b))
          (sentBnd_relInst_congr Rr (Function.update g i b) (hΔb hrΔ)) hins
    rcases heq with heqΓ | heqΔ
    · by_cases hbΔ : b ∈ theoryJConsts (L := L) Δ
      · have htr : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert (constEq (L := L) (g i) b) Δ) :=
          budgetedPairInsep_insert_shared_right heqΓ (sentBnd_constEq _ _) (sentBnd_constEq _ _)
            (by
              refine (sentenceJConsts_constEq_subset (g i) b).trans ?_
              intro k hk
              rcases hk with hk | hk
              · exact hk ▸ hpivΔ
              · exact hk ▸ hbΔ)
            (fun s => hasQuantSigned_constEq_false s _ _) hA
        exact mk (budgetedPairInsep_antitone_right
          (Set.insert_subset_insert (Set.subset_insert _ _))
          (budgetedPairInsep_relCongr_right Rr g i b (Set.mem_insert_of_mem _ hrΔ)
            (Set.mem_insert _ _) htr))
      · exact mk (budgetedPairInsep_relCongr_mixed_rev Rr g i b hrΔ heqΓ hbΔ hA)
    · exact mk (budgetedPairInsep_relCongr_right Rr g i b hrΔ heqΔ hA)

/-- **`all_inst`.**  Plain label dispatch: neither gate takes a freshness hypothesis. -/
private theorem budgetedPairMem_all_inst (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φ : L[[ℕ]].BoundedFormulaω Empty 1) (hmem : BoundedFormulaω.all φ ∈ S) (c : ℕ) :
    BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {instConst c φ}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (all_inst_mem c (hΓU hΓ)) (sentBnd_instConst c (hΓb hΓ))
        (budgetedPairInsep_all_inst_left c hΓ hA)
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (all_inst_mem c (hΔU hΔ)) (sentBnd_instConst c (hΔb hΔ))
        (budgetedPairInsep_all_inst_right c hΔ hA)

/-- **`neg_all_witness`.**  The only helper that constructs anything: the witness constant is chosen
*before* the label dispatch, since both gates demand freshness for **both** supports and the
requirement is symmetric.  This is also the only consumer of root-support finiteness, which is why
those hypotheses appear here and nowhere else in the layer. -/
private theorem budgetedPairMem_neg_all_witness
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite)
    (hS : BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S)
    (φ : L[[ℕ]].BoundedFormulaω Empty 1) (hmem : (BoundedFormulaω.all φ).not ∈ S) :
    ∃ c, BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ (S ∪ {(instConst c φ).not}) := by
  obtain ⟨Γ, Δ, hΓfin, hΔfin, hΓU, hΔU, hΓb, hΔb, hSeq, hA⟩ := hS
  obtain ⟨c, hcΓ, hcΔ⟩ := exists_fresh_budgetedPair hr₁ hr₂ hΓfin hΔfin hΓU hΔU
  refine ⟨c, ?_⟩
  rw [hSeq] at hmem
  rcases hmem with hΓ | hΔ
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_left hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (negall_inst_mem c (hΓU hΓ))
        (sentBnd_not_iff.mpr (sentBnd_instConst c (sentBnd_not_iff.mp (hΓb hΓ))))
        (budgetedPairInsep_witness_left c φ hΓ hcΓ hcΔ hA)
  · simpa only [Set.union_singleton] using
      budgetedPairMem_insert_right hΓfin hΔfin hΓU hΔU hΓb hΔb hSeq
        (negall_inst_mem c (hΔU hΔ))
        (sentBnd_not_iff.mpr (sentBnd_instConst c (sentBnd_not_iff.mp (hΔb hΔ))))
        (budgetedPairInsep_witness_right c φ hΔ hcΓ hcΔ hA)

/-! ## The initial family member

Two named facts, deliberately separate.  The **structural** one is pure packaging: a labelled pair of
singletons, with the generated universe instantiated at those very roots so both `GenU` obligations
are literally `root₁_mem`/`root₂_mem`.  The **logical** one supplies its hypothesis, and is where the
interpolation assumption enters — note the root pair is inseparable *because no admissible
interpolant exists*, not because of the entailment `r₁ ⊨ r₂`, which is consumed only at the very end
against the extracted model. -/

/-- **Structural root member.**  Packaging only; no semantic content. -/
theorem budgetedPairMem_root {ρ₁ ρ₂ : L[[ℕ]].Sentenceω}
    (hb₁ : ρ₁ ∈ SentBnd (L := L) F₁ R₁) (hb₂ : ρ₂ ∈ SentBnd (L := L) F₂ R₂)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ {ρ₁} {ρ₂}) :
    BudgetedPairMem ρ₁ ρ₂ F₁ R₁ F₂ R₂ ({ρ₁} ∪ {ρ₂}) :=
  ⟨{ρ₁}, {ρ₂}, Set.finite_singleton _, Set.finite_singleton _,
    Set.singleton_subset_iff.mpr root₁_mem, Set.singleton_subset_iff.mpr root₂_mem,
    Set.singleton_subset_iff.mpr hb₁, Set.singleton_subset_iff.mpr hb₂, rfl, h⟩

/-- **Root inseparability from failure of interpolation.**  The contrapositive of the root equation:
if the labelled root pair were separable, the collapse would hand back exactly the admissible
universal interpolant assumed not to exist. -/
theorem budgetedPairInsep_root_of_no_interpolant {r₁ r₂ : L[[ℕ]].Sentenceω}
    (hr₂ : ¬ hasQuantSigned false r₂) (hc₁ : sentenceJConsts (L' := L) (J := ℕ) r₁ = ∅)
    (hno : ¬ ∃ θ : L[[ℕ]].Sentenceω, IsUniversal θ ∧ θ ∈ SentBnd (F₁ ∩ F₂) (R₁ ∩ R₂) ∧
      sentenceJConsts (L' := L) (J := ℕ) θ = ∅ ∧
      Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ {r₁} {r₂.not} :=
  not_not.mp fun hsep =>
    hno (exists_universal_interpolant_of_not_budgetedPairInsep hr₂ hc₁ hsep)



/-! ## The consistency property

Pure wiring: every field is its named helper.  Nothing below reasons about separators, labels or
supports — if a field ever needs more than an application, the corresponding helper is missing. -/

/-- **The budgeted labelled-pair consistency property.**  The finite labelled family over the
generated universe `GenU r₁ r₂`.  Root-support finiteness is consumed only by `neg_all_witness`. -/
def budgetedPairConsistencyProperty
    (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (r₁ r₂ : L[[ℕ]].Sentenceω)
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite) :
    ConsistencyPropertyEqOn (GenU r₁ r₂) where
  sets := {S | BudgetedPairMem r₁ r₂ F₁ R₁ F₂ R₂ S}
  subset_U := fun _ hS => budgetedPairMem_subset_U hS
  C0_no_falsum := fun _ hS => budgetedPairMem_C0_no_falsum hS
  C0_no_contradiction := fun _ hS φ => budgetedPairMem_C0_no_contradiction hS φ
  C1_imp := fun _ hS φ ψ hmem => budgetedPairMem_C1_imp hS φ ψ hmem
  C1_neg_imp := fun _ hS φ ψ hmem => budgetedPairMem_C1_neg_imp hS φ ψ hmem
  C2_not_not := fun _ hS φ hmem => budgetedPairMem_C2_not_not hS φ hmem
  C3_iInf := fun _ hS φs hmem k => budgetedPairMem_C3_iInf hS φs hmem k
  C3_neg_iInf := fun _ hS φs hmem => budgetedPairMem_C3_neg_iInf hS φs hmem
  C4_iSup := fun _ hS φs hmem => budgetedPairMem_C4_iSup hS φs hmem
  C4_neg_iSup := fun _ hS φs hmem k => budgetedPairMem_C4_neg_iSup hS φs hmem k
  eq_refl := fun _ hS c => budgetedPairMem_eq_refl hS c
  eq_symm := fun _ hS a b hmem => budgetedPairMem_eq_symm hS a b hmem
  eq_trans := fun _ hS a b d hab hbd => budgetedPairMem_eq_trans hS a b d hab hbd
  rel_congr := fun _ hS _ Rr g i b hrel heq => budgetedPairMem_rel_congr hS Rr g i b hrel heq
  all_inst := fun _ hS φ hmem c => budgetedPairMem_all_inst hS φ hmem c
  neg_all_witness := fun _ hS φ hmem => budgetedPairMem_neg_all_witness hr₁ hr₂ hS φ hmem

end FamilyFields

end FirstOrder.Language






