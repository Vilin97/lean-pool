/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.MarkExtension
/-!
# The closure fields (issue #12, commit 4b part 3 — Exercise 4.28)

The fifteen closure rules of the well-ordering consistency property, as `WOMem`-preservation
theorems, in the reviewed order: C0 and deterministic connectives; branching through the
cofinal-fiber lemma; equality/relation congruence; constant-sensitive rules through the
range split and `mark_rat`; the fresh odd witness (whose index is chosen **separately** to
avoid the finite remainder support — parity only places it outside the rational range).

Every rule opens with the `∈ Bφ` split (`WOMem.union_of_mem_base`: adding a base member
changes nothing); the genuine extensions go through `WOMem.extend`, whose three obligations
(universe, finite support, and (*) at every level) are discharged per-rule from the
`GenU` reachability lemmas, the `sentenceJConsts` monotonicity calculus, and the
`StarWitness` operations of the previous commits.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {φ : L.Sentenceω} {lt : L.Relations 2}

/-! ## The split and extension steps -/

/-- Adding a base member changes nothing. -/
private theorem WOMem.union_of_mem_base {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    {χ : L[[ℕ]].Sentenceω} (hχ : χ ∈ baseDiagram φ lt) : WOMem φ lt (S ∪ {χ}) := by
  have heq : S ∪ {χ} = S := by
    rw [Set.union_singleton, Set.insert_eq_self.mpr (hS.base_subset hχ)]
  rw [heq]
  exact hS

/-- **The generic extension step**: adding a non-base sentence to a member preserves
membership, given the universe, finite-support, and (*) obligations. -/
theorem WOMem.extend {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    {χ : L[[ℕ]].Sentenceω} (hχnb : χ ∉ baseDiagram φ lt)
    (hχU : χ ∈ GenU (φ.mapLanguage (L.lhomWithConstants ℕ))
      (φ.mapLanguage (L.lhomWithConstants ℕ)))
    (hχsupp : (sentenceJConsts (L' := L) (J := ℕ) χ).Finite)
    (hstar : ∀ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord →
      StarCondition φ lt ((S \ baseDiagram φ lt) ∪ {χ}) α) :
    WOMem φ lt (S ∪ {χ}) := by
  have hrem : (S ∪ {χ}) \ baseDiagram φ lt = (S \ baseDiagram φ lt) ∪ {χ} := by
    ext ψ
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hψ | rfl, hnb⟩
      · exact Or.inl ⟨hψ, hnb⟩
      · exact Or.inr rfl
    · rintro (⟨hψ, hnb⟩ | rfl)
      · exact ⟨Or.inl hψ, hnb⟩
      · exact ⟨Or.inr rfl, hχnb⟩
  refine ⟨fun ψ hψ => Or.inl (hS.base_subset hψ), ?_, ?_, ?_, ?_⟩
  · rw [hrem]
    exact hS.rem_finite.union (Set.finite_singleton χ)
  · rw [hrem]
    refine Set.Finite.subset (hS.rem_support.union hχsupp) ?_
    intro c hc
    simp only [Set.mem_iUnion, exists_prop] at hc
    obtain ⟨ψ, hψ, hcψ⟩ := hc
    rcases hψ with hψ | hψ
    · exact Set.mem_union_left _ (Set.mem_biUnion hψ hcψ)
    · rw [Set.mem_singleton_iff] at hψ
      exact Set.mem_union_right _ (hψ ▸ hcψ)
  · rintro ψ (hψ | hψ)
    · exact hS.subset_U hψ
    · rw [Set.mem_singleton_iff] at hψ
      exact hψ ▸ hχU
  · intro α hα
    rw [hrem]
    exact hstar α hα

/-- The support of any member sentence is finite (base: the lift is constant-free, atoms have
two constants; remainder: the member's finite-support field). -/
private theorem WOMem.jConsts_finite_of_mem {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    {χ : L[[ℕ]].Sentenceω} (hχ : χ ∈ S) :
    (sentenceJConsts (L' := L) (J := ℕ) χ).Finite := by
  by_cases hb : χ ∈ baseDiagram φ lt
  · rcases mem_baseDiagram_elim hb with rfl | ⟨_, _, _, rfl⟩
    · rw [sentenceJConsts_lift_eq_empty]
      exact Set.finite_empty
    · rw [sentenceJConsts_ratLtAtom]
      exact (Set.finite_singleton _).insert _
  · refine Set.Finite.subset hS.rem_support ?_
    exact Set.subset_biUnion_of_mem (⟨hχ, hb⟩ : χ ∈ S \ baseDiagram φ lt)

/-- A remainder-or-root sentence is realized by every star witness. -/
private theorem StarWitness.realize_source {Γ : Set L[[ℕ]].Sentenceω} {α : Ordinal.{0}}
    (W : StarWitness φ lt Γ α) {χ : L[[ℕ]].Sentenceω}
    (hχ : χ ∈ Γ ∨ χ = φ.mapLanguage (L.lhomWithConstants ℕ)) :
    @Sentenceω.Realize L[[ℕ]] χ W.M (wc W.inst W.h) := by
  rcases hχ with hχ | rfl
  · exact W.rem_realize χ hχ
  · exact (realize_lift_wc W.inst W.h φ).mpr W.base_realize

/-- Rationals mentioned by a sentence with support inside a remainder member's support are
marked. -/
private theorem StarWitness.hsupp_of_subset {Γ : Set L[[ℕ]].Sentenceω} {α : Ordinal.{0}}
    (W : StarWitness φ lt Γ α) {χ ψ : L[[ℕ]].Sentenceω} (hψ : ψ ∈ Γ)
    (hsub : sentenceJConsts (L' := L) (J := ℕ) χ ⊆ sentenceJConsts (L' := L) (J := ℕ) ψ) :
    ∀ q : ℚ, ratConstIdx q ∈ sentenceJConsts (L' := L) (J := ℕ) χ →
      q ∈ Set.range W.mark :=
  fun _ hq => W.mark_cover ⟨ψ, hψ, hsub hq⟩

/-- Locating a member of `S` for the (*) argument: it lies in the remainder, or it is the
lifted root, or it is a positive diagram atom. -/
private theorem WOMem.mem_cases {S : Set L[[ℕ]].Sentenceω} (_ : WOMem φ lt S)
    {χ : L[[ℕ]].Sentenceω} (hχ : χ ∈ S) :
    χ ∈ (S \ baseDiagram φ lt) ∨ χ = φ.mapLanguage (L.lhomWithConstants ℕ) ∨
      ∃ q r : ℚ, q < r ∧ χ = ratLtAtom lt q r := by
  by_cases hb : χ ∈ baseDiagram φ lt
  · rcases mem_baseDiagram_elim hb with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl ⟨hχ, hb⟩

/-- `1 < ω₁`. -/
private theorem one_lt_omega1 : (1 : Ordinal.{0}) < (Cardinal.aleph 1).ord := by
  rw [Cardinal.lt_ord, Ordinal.card_one]
  exact lt_trans Cardinal.one_lt_aleph0 Cardinal.aleph0_lt_aleph_one

/-! ## The deterministic extension driver -/

/-- **Deterministic extension**: a target whose support lies inside a non-atomic source
member's support, and which is semantically forced by the source at every controlled
expansion, extends the member. -/
private theorem WOMem.extend_det {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    {σ χ : L[[ℕ]].Sentenceω} (hσ : σ ∈ S)
    (hσnotatom : ∀ q r : ℚ, σ ≠ ratLtAtom lt q r)
    (hχnb : χ ∉ baseDiagram φ lt)
    (hχU : χ ∈ GenU (φ.mapLanguage (L.lhomWithConstants ℕ))
      (φ.mapLanguage (L.lhomWithConstants ℕ)))
    (hsub : sentenceJConsts (L' := L) (J := ℕ) χ ⊆ sentenceJConsts (L' := L) (J := ℕ) σ)
    (hforce : ∀ (M : Type) (inst : L.Structure M), Nonempty M → ∀ h : ℕ → M,
      @Sentenceω.Realize L[[ℕ]] σ M (wc inst h) → @Sentenceω.Realize L[[ℕ]] χ M (wc inst h)) :
    WOMem φ lt (S ∪ {χ}) := by
  refine hS.extend hχnb hχU (Set.Finite.subset (hS.jConsts_finite_of_mem hσ) hsub) ?_
  intro α hα
  obtain ⟨W⟩ := hS.star α hα
  rcases hS.mem_cases hσ with hσΓ | hσroot | ⟨q, r, _, hatom⟩
  · exact ⟨W.add_sentence (hforce _ W.inst W.ne _ (W.realize_source (Or.inl hσΓ)))
      (W.hsupp_of_subset hσΓ hsub)⟩
  · refine ⟨W.add_sentence
      (hforce _ W.inst W.ne _ (W.realize_source (Or.inr hσroot))) ?_⟩
    intro q hq
    rw [hσroot, sentenceJConsts_lift_eq_empty] at hsub
    exact absurd (hsub hq) (Set.notMem_empty _)
  · exact absurd hatom (hσnotatom q r)

/-! ## C0 -/

/-- (C0a) No member contains `falsum`. -/
theorem WOMem.no_falsum {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S) :
    (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) ∉ S := by
  intro hf
  obtain ⟨W⟩ := hS.star 1 one_lt_omega1
  rcases hS.mem_cases hf with hΓ | hroot | ⟨q, r, _, hatom⟩
  · exact W.rem_realize _ hΓ
  · obtain ⟨M, inst, ne, hreal⟩ : ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M),
        Sentenceω.Realize φ M := ⟨W.M, W.inst, W.ne, W.base_realize⟩
    rw [lift_eq_falsum_reflect hroot.symm] at hreal
    exact hreal
  · exact absurd hatom (by simp [ratLtAtom, relInst])

/-- (C0b) No member contains a sentence and its negation — the symmetric four-case
base/remainder argument through the C0 helper. -/
theorem WOMem.no_contradiction {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (χ : L[[ℕ]].Sentenceω) : ¬(χ ∈ S ∧ χ.not ∈ S) := by
  rintro ⟨hχ, hnχ⟩
  obtain ⟨W⟩ := hS.star 1 one_lt_omega1
  let : L[[ℕ]].Structure W.M := wc W.inst W.h
  rcases hS.mem_cases hnχ with hnΓ | hnroot | ⟨q, r, _, hnatom⟩
  · -- the opposite lies in the remainder
    have hnreal := W.rem_realize _ hnΓ
    rcases hS.mem_cases hχ with hΓ | hroot | ⟨q, r, hqr, hatom⟩
    · exact (BoundedFormulaω.realize_not χ).mp hnreal (W.rem_realize _ hΓ)
    · exact (BoundedFormulaω.realize_not χ).mp hnreal
        (W.realize_base_of_opposite (hroot ▸ mapLanguage_mem_baseDiagram φ lt) hnΓ)
    · exact (BoundedFormulaω.realize_not χ).mp hnreal
        (W.realize_base_of_opposite (hatom ▸ ratLtAtom_mem_baseDiagram φ lt hqr) hnΓ)
  · -- the negation is the lifted root
    have hnreal : @Sentenceω.Realize L[[ℕ]] χ.not W.M (wc W.inst W.h) :=
      hnroot ▸ W.realize_source (Or.inr rfl)
    rcases hS.mem_cases hχ with hΓ | hroot | ⟨q, r, hqr, hatom⟩
    · exact (BoundedFormulaω.realize_not χ).mp hnreal (W.rem_realize _ hΓ)
    · exact BoundedFormulaω.not_ne_self χ (hnroot.trans hroot.symm)
    · -- an atom's support is nonempty, the root's is empty
      have hsupp := sentenceJConsts_lift_eq_empty (L := L) φ
      rw [← hnroot, sentenceJConsts_not, hatom, sentenceJConsts_ratLtAtom] at hsupp
      have : ratConstIdx q ∈ ({ratConstIdx q, ratConstIdx r} : Set ℕ) := Set.mem_insert _ _
      rw [hsupp] at this
      exact Set.notMem_empty _ this
  · -- a negation cannot be a positive atom
    exact absurd hnatom (by simp [BoundedFormulaω.not, BoundedFormulaInf.not, ratLtAtom, relInst])

/-! ## Deterministic connective fields -/

/-- (C2) Double negation. -/
theorem WOMem.C2_not_not {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (ψ : L[[ℕ]].Sentenceω) (hσ : ψ.not.not ∈ S) : WOMem φ lt (S ∪ {ψ}) := by
  by_cases hb : ψ ∈ baseDiagram φ lt
  · exact hS.union_of_mem_base hb
  · refine hS.extend_det hσ (fun q r h => by simp [BoundedFormulaω.not, BoundedFormulaInf.not, ratLtAtom, relInst] at h)
      hb (negimp_left_mem (hS.subset_U hσ)) ?_ ?_
    · rw [sentenceJConsts_not, sentenceJConsts_not]
    · intro M inst _ h hr
      let : L[[ℕ]].Structure M := wc inst h
      have h1 := (BoundedFormulaω.realize_not ψ.not).mp hr
      rw [BoundedFormulaω.realize_not] at h1
      exact not_not.mp h1
/-- (C1') Negated implication: both halves. -/
theorem WOMem.C1_neg_imp {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (ψ₁ ψ₂ : L[[ℕ]].Sentenceω) (hσ : (ψ₁.imp ψ₂).not ∈ S) :
    WOMem φ lt (S ∪ {ψ₁}) ∧ WOMem φ lt (S ∪ {ψ₂.not}) := by
  constructor
  · by_cases hb : ψ₁ ∈ baseDiagram φ lt
    · exact hS.union_of_mem_base hb
    · refine hS.extend_det hσ
        (fun q r h => by simp [BoundedFormulaω.not, BoundedFormulaInf.not, ratLtAtom, relInst] at h) hb
        (negimp_left_mem (hS.subset_U hσ)) ?_ ?_
      · rw [sentenceJConsts_not]
        exact sentenceJConsts_imp_left ψ₁ ψ₂
      · intro M inst _ h hr
        let : L[[ℕ]].Structure M := wc inst h
        have h1 := (BoundedFormulaω.realize_not _).mp hr
        rw [BoundedFormulaω.realize_imp] at h1
        exact (Classical.not_imp.mp h1).1
  · by_cases hb : ψ₂.not ∈ baseDiagram φ lt
    · exact hS.union_of_mem_base hb
    · refine hS.extend_det hσ
        (fun q r h => by simp [BoundedFormulaω.not, BoundedFormulaInf.not, ratLtAtom, relInst] at h) hb
        (negimp_right_mem (hS.subset_U hσ)) ?_ ?_
      · rw [sentenceJConsts_not, sentenceJConsts_not]
        exact sentenceJConsts_imp_right ψ₁ ψ₂
      · intro M inst _ h hr
        let : L[[ℕ]].Structure M := wc inst h
        have h1 := (BoundedFormulaω.realize_not _).mp hr
        rw [BoundedFormulaω.realize_imp] at h1
        exact (BoundedFormulaω.realize_not ψ₂).mpr (Classical.not_imp.mp h1).2

/-- (C3) Countable conjunction: every component. -/
theorem WOMem.C3_iInf {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (φs : ℕ → L[[ℕ]].Sentenceω) (hσ : BoundedFormulaω.iInf φs ∈ S) (k : ℕ) :
    WOMem φ lt (S ∪ {φs k}) := by
  by_cases hb : φs k ∈ baseDiagram φ lt
  · exact hS.union_of_mem_base hb
  · refine hS.extend_det hσ (fun q r h => by simp [ratLtAtom, relInst] at h) hb
      (iInf_comp_mem k (hS.subset_U hσ)) (sentenceJConsts_component_iInf φs k) ?_
    intro M inst _ h hr
    let : L[[ℕ]].Structure M := wc inst h
    exact (BoundedFormulaω.realize_iInf φs).mp hr k

/-- (C4') Negated disjunction: every negated component. -/
theorem WOMem.C4_neg_iSup {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (φs : ℕ → L[[ℕ]].Sentenceω) (hσ : (BoundedFormulaω.iSup φs).not ∈ S) (k : ℕ) :
    WOMem φ lt (S ∪ {(φs k).not}) := by
  by_cases hb : (φs k).not ∈ baseDiagram φ lt
  · exact hS.union_of_mem_base hb
  · refine hS.extend_det hσ
      (fun q r h => by simp [BoundedFormulaω.not, BoundedFormulaInf.not, ratLtAtom, relInst] at h) hb
      (negiSup_comp_mem k (hS.subset_U hσ)) ?_ ?_
    · rw [sentenceJConsts_not, sentenceJConsts_not]
      exact sentenceJConsts_component_iSup φs k
    · intro M inst _ h hr
      let : L[[ℕ]].Structure M := wc inst h
      have h1 := (BoundedFormulaω.realize_not _).mp hr
      rw [BoundedFormulaω.realize_iSup] at h1
      exact (BoundedFormulaω.realize_not (φs k)).mpr fun hk => h1 ⟨k, hk⟩

/-! ## The branching driver -/

/-- Upgrading (*) from an unbounded set of levels to every level (downward closure). -/
private theorem star_all_of_unbounded {Γ : Set L[[ℕ]].Sentenceω}
    (h : ∀ β : Ordinal.{0}, β < (Cardinal.aleph 1).ord →
      ∃ α, β ≤ α ∧ α < (Cardinal.aleph 1).ord ∧ StarCondition φ lt Γ α) :
    ∀ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord → StarCondition φ lt Γ α := by
  intro α hα
  obtain ⟨α', hle, _, hst⟩ := h α hα
  exact hst.mono hle

/-- **The branching driver**: if every level admits some branch, one branch works at every
level — the cofinal-fiber pigeonhole plus downward closure. -/
theorem WOMem.branch_choice {S : Set L[[ℕ]].Sentenceω} (_ : WOMem φ lt S)
    {ι : Type} [Countable ι] [Nonempty ι] (tgt : ι → L[[ℕ]].Sentenceω)
    (hchoice : ∀ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord →
      ∃ i, StarCondition φ lt ((S \ baseDiagram φ lt) ∪ {tgt i}) α) :
    ∃ i, ∀ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord →
      StarCondition φ lt ((S \ baseDiagram φ lt) ∪ {tgt i}) α := by
  classical
  set F : Ordinal.{0} → ι := fun α =>
    if hα : α < (Cardinal.aleph 1).ord then (hchoice α hα).choose
    else Classical.arbitrary ι with hF
  obtain ⟨i, hi⟩ := exists_unbounded_fiber F
  refine ⟨i, star_all_of_unbounded ?_⟩
  intro β hβ
  obtain ⟨α, hle, hlt, hFα⟩ := hi β hβ
  refine ⟨α, hle, hlt, ?_⟩
  have hspec := (hchoice α hlt).choose_spec
  have hFeq : F α = (hchoice α hlt).choose := by
    simp only [hF]
    rw [dite_eq_left hlt]
  rw [hFeq] at hFα
  rwa [hFα] at hspec

/-- (C1) Implication: one of the two branches extends. -/
theorem WOMem.C1_imp {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (ψ₁ ψ₂ : L[[ℕ]].Sentenceω) (hσ : ψ₁.imp ψ₂ ∈ S) :
    WOMem φ lt (S ∪ {ψ₁.not}) ∨ WOMem φ lt (S ∪ {ψ₂}) := by
  by_cases hb1 : ψ₁.not ∈ baseDiagram φ lt
  · exact Or.inl (hS.union_of_mem_base hb1)
  by_cases hb2 : ψ₂ ∈ baseDiagram φ lt
  · exact Or.inr (hS.union_of_mem_base hb2)
  -- locate the source once
  have hsrcloc : (ψ₁.imp ψ₂) ∈ (S \ baseDiagram φ lt) ∨
      (ψ₁.imp ψ₂) = φ.mapLanguage (L.lhomWithConstants ℕ) := by
    rcases hS.mem_cases hσ with h | h | ⟨q, r, _, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (by simp [ratLtAtom, relInst])
  have hsub : ∀ q : ℚ, ∀ {χ : L[[ℕ]].Sentenceω},
      sentenceJConsts (L' := L) (J := ℕ) χ ⊆
        sentenceJConsts (L' := L) (J := ℕ) (ψ₁.imp ψ₂) →
      ∀ {Γ α} (W : StarWitness φ lt Γ α), (ψ₁.imp ψ₂) ∈ Γ ∨
        (ψ₁.imp ψ₂) = φ.mapLanguage (L.lhomWithConstants ℕ) →
      ratConstIdx q ∈ sentenceJConsts (L' := L) (J := ℕ) χ → q ∈ Set.range W.mark := by
    intro q χ hsub Γ α W hloc hq
    rcases hloc with hloc | hloc
    · exact W.mark_cover ⟨_, hloc, hsub hq⟩
    · rw [hloc, sentenceJConsts_lift_eq_empty] at hsub
      exact absurd (hsub hq) (Set.notMem_empty _)
  have hchoice : ∀ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord →
      ∃ b : Bool, StarCondition φ lt
        ((S \ baseDiagram φ lt) ∪ {cond b ψ₁.not ψ₂}) α := by
    intro α hα
    obtain ⟨W⟩ := hS.star α hα
    let : L[[ℕ]].Structure W.M := wc W.inst W.h
    have hreal := W.realize_source hsrcloc
    by_cases hψ₁ : @Sentenceω.Realize L[[ℕ]] ψ₁ W.M (wc W.inst W.h)
    · refine ⟨false, ⟨W.add_sentence ?_ ?_⟩⟩
      · exact (BoundedFormulaω.realize_imp ψ₁ ψ₂).mp hreal hψ₁
      · exact fun q hq => hsub q (sentenceJConsts_imp_right ψ₁ ψ₂) W hsrcloc hq
    · refine ⟨true, ⟨W.add_sentence ((BoundedFormulaω.realize_not ψ₁).mpr hψ₁) ?_⟩⟩
      · intro q hq
        rw [Bool.cond_true, sentenceJConsts_not] at hq
        exact hsub q (sentenceJConsts_imp_left ψ₁ ψ₂) W hsrcloc hq
  obtain ⟨b, hb⟩ := hS.branch_choice (fun b : Bool => cond b ψ₁.not ψ₂) hchoice
  cases b
  · refine Or.inr (hS.extend hb2 (imp_right_mem (hS.subset_U hσ))
      (Set.Finite.subset (hS.jConsts_finite_of_mem hσ) (sentenceJConsts_imp_right ψ₁ ψ₂))
      hb)
  · refine Or.inl (hS.extend hb1 (imp_negleft_mem (hS.subset_U hσ))
      (Set.Finite.subset (hS.jConsts_finite_of_mem hσ) ?_) hb)
    rw [sentenceJConsts_not]
    exact sentenceJConsts_imp_left ψ₁ ψ₂

/-- (C4) Countable disjunction: some component extends. -/
theorem WOMem.C4_iSup {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (φs : ℕ → L[[ℕ]].Sentenceω) (hσ : BoundedFormulaω.iSup φs ∈ S) :
    ∃ k, WOMem φ lt (S ∪ {φs k}) := by
  by_cases hb : ∃ k, φs k ∈ baseDiagram φ lt
  · obtain ⟨k, hk⟩ := hb
    exact ⟨k, hS.union_of_mem_base hk⟩
  push Not at hb
  have hsrcloc : BoundedFormulaω.iSup φs ∈ (S \ baseDiagram φ lt) ∨
      BoundedFormulaω.iSup φs = φ.mapLanguage (L.lhomWithConstants ℕ) := by
    rcases hS.mem_cases hσ with h | h | ⟨q, r, _, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (by simp [ratLtAtom, relInst])
  have hchoice : ∀ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord →
      ∃ k : ℕ, StarCondition φ lt ((S \ baseDiagram φ lt) ∪ {φs k}) α := by
    intro α hα
    obtain ⟨W⟩ := hS.star α hα
    let : L[[ℕ]].Structure W.M := wc W.inst W.h
    have hreal := W.realize_source hsrcloc
    obtain ⟨k, hk⟩ := (BoundedFormulaω.realize_iSup φs).mp hreal
    refine ⟨k, ⟨W.add_sentence hk ?_⟩⟩
    intro q hq
    rcases hsrcloc with hloc | hloc
    · exact W.mark_cover ⟨_, hloc, sentenceJConsts_component_iSup φs k hq⟩
    · have := sentenceJConsts_component_iSup φs k hq
      rw [hloc, sentenceJConsts_lift_eq_empty] at this
      exact absurd this (Set.notMem_empty _)
  obtain ⟨k, hk⟩ := hS.branch_choice φs hchoice
  exact ⟨k, hS.extend (hb k) (iSup_comp_mem k (hS.subset_U hσ))
    (Set.Finite.subset (hS.jConsts_finite_of_mem hσ) (sentenceJConsts_component_iSup φs k))
    hk⟩

/-- (C3') Negated conjunction: some negated component extends. -/
theorem WOMem.C3_neg_iInf {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (φs : ℕ → L[[ℕ]].Sentenceω) (hσ : (BoundedFormulaω.iInf φs).not ∈ S) :
    ∃ k, WOMem φ lt (S ∪ {(φs k).not}) := by
  by_cases hb : ∃ k, (φs k).not ∈ baseDiagram φ lt
  · obtain ⟨k, hk⟩ := hb
    exact ⟨k, hS.union_of_mem_base hk⟩
  push Not at hb
  have hsrcloc : (BoundedFormulaω.iInf φs).not ∈ (S \ baseDiagram φ lt) ∨
      (BoundedFormulaω.iInf φs).not = φ.mapLanguage (L.lhomWithConstants ℕ) := by
    rcases hS.mem_cases hσ with h | h | ⟨q, r, _, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (by simp [BoundedFormulaω.not, BoundedFormulaInf.not, ratLtAtom, relInst])
  have hchoice : ∀ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord →
      ∃ k : ℕ, StarCondition φ lt ((S \ baseDiagram φ lt) ∪ {(φs k).not}) α := by
    intro α hα
    obtain ⟨W⟩ := hS.star α hα
    let : L[[ℕ]].Structure W.M := wc W.inst W.h
    have hreal := W.realize_source hsrcloc
    have h1 := (BoundedFormulaω.realize_not _).mp hreal
    rw [BoundedFormulaω.realize_iInf] at h1
    push Not at h1
    obtain ⟨k, hk⟩ := h1
    refine ⟨k, ⟨W.add_sentence ((BoundedFormulaω.realize_not (φs k)).mpr hk) ?_⟩⟩
    intro q hq
    rw [sentenceJConsts_not] at hq
    have hsubk := sentenceJConsts_component_iInf φs k hq
    rcases hsrcloc with hloc | hloc
    · refine W.mark_cover ⟨_, hloc, ?_⟩
      rw [sentenceJConsts_not]
      exact hsubk
    · have h2 : ratConstIdx q ∈
          sentenceJConsts (L' := L) (J := ℕ) ((BoundedFormulaω.iInf φs).not) := by
        rw [sentenceJConsts_not]
        exact hsubk
      rw [hloc, sentenceJConsts_lift_eq_empty] at h2
      exact absurd h2 (Set.notMem_empty _)
  obtain ⟨k, hk⟩ := hS.branch_choice (fun k => (φs k).not) hchoice
  refine ⟨k, hS.extend (hb k) (negiInf_comp_mem k (hS.subset_U hσ))
    (Set.Finite.subset (hS.jConsts_finite_of_mem hσ) ?_) hk⟩
  rw [sentenceJConsts_not, sentenceJConsts_not]
  exact sentenceJConsts_component_iInf φs k

/-! ## Equality congruence -/

/-- A constant equality in a member lies in the remainder (its support is nonempty, and it is
not relation-shaped). -/
private theorem WOMem.constEq_mem_rem {S : Set L[[ℕ]].Sentenceω} (_ : WOMem φ lt S) {a b : ℕ}
    (h : constEq a b ∈ S) : constEq a b ∈ S \ baseDiagram φ lt := by
  refine ⟨h, fun hb => ?_⟩
  rcases mem_baseDiagram_elim hb with heq | ⟨q, r, _, heq⟩
  · have hsupp := sentenceJConsts_lift_eq_empty (L := L) φ
    rw [← heq] at hsupp
    have := mem_sentenceJConsts_constEq_left (L := L) a b
    rw [hsupp] at this
    exact Set.notMem_empty _ this
  · exact absurd heq (by simp [constEq, ratLtAtom, relInst])

/-- Equality congruence targets: realized and covered from remainder equalities. -/
private theorem WOMem.extend_constEq {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S) {a b : ℕ}
    (hab : constEq a b ∉ baseDiagram φ lt)
    (hsupp : sentenceJConsts (L' := L) (J := ℕ) (constEq a b) ⊆
      ⋃ χ ∈ (S \ baseDiagram φ lt), sentenceJConsts (L' := L) (J := ℕ) χ)
    (hval : ∀ α (_ : α < (Cardinal.aleph 1).ord) (W : StarWitness φ lt
      (S \ baseDiagram φ lt) α), W.h a = W.h b) :
    WOMem φ lt (S ∪ {constEq a b}) := by
  refine hS.extend hab (constEq_mem a b) (Set.Finite.subset hS.rem_support hsupp) ?_
  intro α hα
  obtain ⟨W⟩ := hS.star α hα
  refine ⟨W.add_sentence ((realize_constEq_wc (base := W.inst) (h := W.h) a b).mpr
    (hval α hα W)) ?_⟩
  intro q hq
  obtain ⟨χ, hχ, hcχ⟩ := by
    have := hsupp hq
    simpa only [Set.mem_iUnion, exists_prop] using this
  exact W.mark_cover ⟨χ, hχ, hcχ⟩

/-- **Equality symmetry.** -/
theorem WOMem.eq_symm {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S) (a b : ℕ)
    (hσ : constEq a b ∈ S) : WOMem φ lt (S ∪ {constEq b a}) := by
  by_cases hb : constEq b a ∈ baseDiagram φ lt
  · exact hS.union_of_mem_base hb
  have hrem := hS.constEq_mem_rem hσ
  refine hS.extend_constEq hb ?_ ?_
  · intro c hc
    rw [sentenceJConsts_constEq_comm] at hc
    exact Set.mem_biUnion hrem hc
  · intro α hα W
    exact ((realize_constEq_wc (base := W.inst) (h := W.h) a b).mp
      (W.rem_realize _ hrem)).symm

/-- **Equality transitivity.** -/
theorem WOMem.eq_trans {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S) (a b d : ℕ)
    (h₁ : constEq a b ∈ S) (h₂ : constEq b d ∈ S) :
    WOMem φ lt (S ∪ {constEq a d}) := by
  by_cases hb : constEq a d ∈ baseDiagram φ lt
  · exact hS.union_of_mem_base hb
  have hrem₁ := hS.constEq_mem_rem h₁
  have hrem₂ := hS.constEq_mem_rem h₂
  refine hS.extend_constEq hb ?_ ?_
  · intro c hc
    rcases sentenceJConsts_constEq_subset a d hc with hc | hc
    · exact Set.mem_biUnion hrem₁ (hc ▸ mem_sentenceJConsts_constEq_left a b)
    · exact Set.mem_biUnion hrem₂ (hc ▸ mem_sentenceJConsts_constEq_right b d)
  · intro α hα W
    exact ((realize_constEq_wc (base := W.inst) (h := W.h) a b).mp
        (W.rem_realize _ hrem₁)).trans
      ((realize_constEq_wc (base := W.inst) (h := W.h) b d).mp (W.rem_realize _ hrem₂))

/-! ## Constant-sensitive fields -/

/-- Updating the constant map at a non-rational-range index outside the remainder's support
preserves the star witness (the marking is untouched). -/
private def StarWitness.update_nonrat {Γ : Set L[[ℕ]].Sentenceω} {α : Ordinal.{0}}
    (W : StarWitness φ lt Γ α) {c : ℕ} (hcr : c ∉ Set.range ratConstIdx)
    (hcΓ : ∀ χ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) χ) (v : W.M) :
    StarWitness φ lt Γ α where
  M := W.M
  inst := W.inst
  ne := W.ne
  h := Function.update W.h c v
  base_realize := W.base_realize
  rem_realize := W.rem_realize_update hcΓ v
  m := W.m
  mark := W.mark
  mark_mono := W.mark_mono
  mark_cover := W.mark_cover
  witness := by
    have htup : (fun i => Function.update W.h c v (ratConstIdx (W.mark i))) =
        (fun i => W.h (ratConstIdx (W.mark i))) := by
      funext i
      have hne : ratConstIdx (W.mark i) ≠ c := fun he => hcr ⟨W.mark i, he⟩
      exact Function.update_of_ne hne v W.h
    rw [htup]
    exact W.witness

/-- A fresh Henkin index avoiding any finite set exists. -/
private theorem exists_fresh_henkin {F : Set ℕ} (hF : F.Finite) :
    ∃ n : ℕ, henkinConstIdx n ∉ F := by
  by_contra h
  push Not at h
  exact Set.infinite_range_of_injective henkinConstIdx_injective
    (hF.subset (Set.range_subset_iff.mpr h))

/-- The one-variable constant environment is the snoc environment. -/
private theorem snoc_elim0_eq_const {M : Type} (v : M) :
    (Fin.snoc Fin.elim0 v : Fin 1 → M) = fun _ => v := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [Fin.snoc_last]
  | cast j => exact j.elim0

/-- **Equality reflexivity** (constant-sensitive: the range split). -/
theorem WOMem.eq_refl {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S) (c : ℕ) :
    WOMem φ lt (S ∪ {constEq c c}) := by
  classical
  by_cases hb : constEq c c ∈ baseDiagram φ lt
  · exact hS.union_of_mem_base hb
  refine hS.extend hb (constEq_mem c c) (Set.Finite.subset
    ((Set.finite_singleton c).insert c) (sentenceJConsts_constEq_subset c c)) ?_
  intro α hα
  by_cases hcr : c ∈ Set.range ratConstIdx
  · obtain ⟨q₀, rfl⟩ := hcr
    obtain ⟨W⟩ := hS.star _ (add_one_lt_omega1 (add_lt_omega1 hα hα))
    obtain ⟨W', hq₀, -⟩ := W.mark_rat (lt_add_one _) q₀
    refine ⟨W'.add_sentence
      ((realize_constEq_wc (base := W'.inst) (h := W'.h) _ _).mpr rfl) ?_⟩
    intro q hq
    have := sentenceJConsts_constEq_subset _ _ hq
    have hqq : q = q₀ := by
      rcases this with h | h <;> exact ratConstIdx_injective h
    exact hqq ▸ hq₀
  · obtain ⟨W⟩ := hS.star α hα
    refine ⟨W.add_sentence
      ((realize_constEq_wc (base := W.inst) (h := W.h) _ _).mpr rfl) ?_⟩
    intro q hq
    have := sentenceJConsts_constEq_subset _ _ hq
    have : ratConstIdx q = c := by rcases this with h | h <;> exact h
    exact absurd ⟨q, this⟩ hcr

/-- **Universal instantiation** (constant-sensitive: the range split). -/
theorem WOMem.all_inst {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (ψ : L[[ℕ]].BoundedFormulaω Empty 1) (hσ : ψ.all ∈ S) (c : ℕ) :
    WOMem φ lt (S ∪ {instConst c ψ}) := by
  classical
  by_cases hb : instConst c ψ ∈ baseDiagram φ lt
  · exact hS.union_of_mem_base hb
  have hsrcloc : ψ.all ∈ (S \ baseDiagram φ lt) ∨
      ψ.all = φ.mapLanguage (L.lhomWithConstants ℕ) := by
    rcases hS.mem_cases hσ with h | h | ⟨q, r, _, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (by simp [ratLtAtom, relInst])
  have hsupp : ∀ {Γ' α'} (W : StarWitness φ lt Γ' α'), ψ.all ∈ Γ' ∨
      ψ.all = φ.mapLanguage (L.lhomWithConstants ℕ) →
      (∀ q : ℚ, ratConstIdx q = c → q ∈ Set.range W.mark) →
      ∀ q : ℚ, ratConstIdx q ∈ sentenceJConsts (L' := L) (J := ℕ) (instConst c ψ) →
        q ∈ Set.range W.mark := by
    intro Γ' α' W hloc hc q hq
    rcases sentenceJConsts_instConst_subset c ψ hq with h | h
    · rcases hloc with hloc | hloc
      · exact W.mark_cover ⟨_, hloc, h⟩
      · rw [hloc, sentenceJConsts_lift_eq_empty] at h
        exact absurd h (Set.notMem_empty _)
    · exact hc q h
  have hforce : ∀ {Γ' α'} (W : StarWitness φ lt Γ' α'), ψ.all ∈ Γ' ∨
      ψ.all = φ.mapLanguage (L.lhomWithConstants ℕ) →
      @Sentenceω.Realize L[[ℕ]] (instConst c ψ) W.M (wc W.inst W.h) := by
    intro Γ' α' W hloc
    let : L[[ℕ]].Structure W.M := wc W.inst W.h
    have hall := W.realize_source hloc
    rw [show @Sentenceω.Realize L[[ℕ]] ψ.all W.M (wc W.inst W.h) =
      @BoundedFormulaω.Realize L[[ℕ]] W.M (wc W.inst W.h) Empty 0 ψ.all
        Empty.elim Fin.elim0 from rfl, BoundedFormulaω.realize_all] at hall
    refine (realize_instConst W.inst W.h c ψ).mpr ?_
    have := hall (W.h c)
    rwa [snoc_elim0_eq_const] at this
  refine hS.extend hb (all_inst_mem c (hS.subset_U hσ)) ?_ ?_
  · refine Set.Finite.subset ((hS.jConsts_finite_of_mem hσ).union
      (Set.finite_singleton c)) (sentenceJConsts_instConst_subset c ψ)
  · intro α hα
    by_cases hcr : c ∈ Set.range ratConstIdx
    · obtain ⟨q₀, hq₀c⟩ := hcr
      obtain ⟨W⟩ := hS.star _ (add_one_lt_omega1 (add_lt_omega1 hα hα))
      obtain ⟨W', hq₀, -⟩ := W.mark_rat (lt_add_one _) q₀
      refine ⟨W'.add_sentence (hforce W' hsrcloc) (hsupp W' hsrcloc ?_)⟩
      intro q hq
      have : q = q₀ := ratConstIdx_injective (hq.trans hq₀c.symm)
      exact this ▸ hq₀
    · obtain ⟨W⟩ := hS.star α hα
      refine ⟨W.add_sentence (hforce W hsrcloc) (hsupp W hsrcloc ?_)⟩
      intro q hq
      exact absurd ⟨q, hq⟩ hcr

/-- **The fresh existential witness**: syntactic freshness is chosen against the finite
remainder-and-source support; parity (oddness) separately places the constant outside the
rational range. -/
theorem WOMem.neg_all_witness {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S)
    (ψ : L[[ℕ]].BoundedFormulaω Empty 1) (hσ : ψ.all.not ∈ S) :
    ∃ c : ℕ, WOMem φ lt (S ∪ {(instConst c ψ).not}) := by
  classical
  obtain ⟨n, hn⟩ := exists_fresh_henkin (F := (⋃ χ ∈ (S \ baseDiagram φ lt),
      sentenceJConsts (L' := L) (J := ℕ) χ) ∪ sentenceJConsts (L' := L) (J := ℕ) (ψ.all.not))
    (hS.rem_support.union (hS.jConsts_finite_of_mem hσ))
  set c := henkinConstIdx n with hcdef
  have hcr : c ∉ Set.range ratConstIdx := henkinConstIdx_notMem_range_ratConstIdx n
  have hcΓ : ∀ χ ∈ (S \ baseDiagram φ lt), c ∉ sentenceJConsts (L' := L) (J := ℕ) χ :=
    fun χ hχ hc => hn (Set.mem_union_left _ (Set.mem_biUnion hχ hc))
  have hcσ : c ∉ sentenceJConsts (L' := L) (J := ℕ) (ψ.all.not) :=
    fun hc => hn (Set.mem_union_right _ hc)
  have hcψ : c ∉ sentenceJConsts (L' := L) (J := ℕ) ψ := by
    rw [sentenceJConsts_not, sentenceJConsts_all] at hcσ
    exact hcσ
  by_cases hb : (instConst c ψ).not ∈ baseDiagram φ lt
  · exact ⟨c, hS.union_of_mem_base hb⟩
  have hsrcloc : ψ.all.not ∈ (S \ baseDiagram φ lt) ∨
      ψ.all.not = φ.mapLanguage (L.lhomWithConstants ℕ) := by
    rcases hS.mem_cases hσ with h | h | ⟨q, r, _, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (by simp [BoundedFormulaω.not, BoundedFormulaInf.not, ratLtAtom, relInst])
  refine ⟨c, hS.extend hb (negall_inst_mem c (hS.subset_U hσ)) ?_ ?_⟩
  · refine Set.Finite.subset ((hS.jConsts_finite_of_mem hσ).union
      (Set.finite_singleton c)) ?_
    intro d hd
    rw [sentenceJConsts_not] at hd
    rcases sentenceJConsts_instConst_subset c ψ hd with h | h
    · refine Or.inl ?_
      rw [sentenceJConsts_not]
      exact h
    · exact Or.inr h
  · intro α hα
    obtain ⟨W⟩ := hS.star α hα
    let : L[[ℕ]].Structure W.M := wc W.inst W.h
    have hsrc := W.realize_source hsrcloc
    have h1 := (BoundedFormulaω.realize_not _).mp hsrc
    rw [BoundedFormulaω.realize_all] at h1
    push Not at h1
    obtain ⟨v, hv⟩ := h1
    -- this occurrence carries the sentence semantics' `default` rather than `Fin.elim0`; the two
    -- are definitionally equal, so the shared lemma still proves it in the shape the goal has
    have hdef : (Fin.snoc (default : Fin 0 → W.M) v : Fin 1 → W.M) = fun _ => v :=
      snoc_elim0_eq_const v
    rw [hdef] at hv
    refine ⟨(W.update_nonrat hcr hcΓ v).add_sentence ?_ ?_⟩
    · show @Sentenceω.Realize L[[ℕ]] ((instConst c ψ).not) W.M
        (wc W.inst (Function.update W.h c v))
      let : L[[ℕ]].Structure W.M := wc W.inst (Function.update W.h c v)
      -- normalize the empty tuple to `Fin.elim0` first, the spelling the downstream lemmas use
      rw [Sentenceω.realize_def]
      refine (BoundedFormulaω.realize_not _).mpr ?_
      intro hcon
      rw [realize_instConst W.inst (Function.update W.h c v) c ψ] at hcon
      have henv : (fun _ : Fin 1 => Function.update W.h c v c) = fun _ : Fin 1 => v := by
        funext i
        rw [Function.update_self]
      rw [henv] at hcon
      refine hv ?_
      refine (BoundedFormulaω.realize_congr_const W.inst ψ (fun k hk => ?_) _ _).mpr hcon
      have hkc : k ≠ c := fun hkc => hcψ (hkc ▸ hk)
      exact (Function.update_of_ne hkc v W.h).symm
    · intro q hq
      rw [sentenceJConsts_not] at hq
      rcases sentenceJConsts_instConst_subset c ψ hq with h | h
      · rcases hsrcloc with hloc | hloc
        · refine W.mark_cover ⟨_, hloc, ?_⟩
          rw [sentenceJConsts_not]
          exact h
        · have h2 : ratConstIdx q ∈
              sentenceJConsts (L' := L) (J := ℕ) (ψ.all.not) := by
            rw [sentenceJConsts_not]
            exact h
          rw [hloc, sentenceJConsts_lift_eq_empty] at h2
          exact absurd h2 (Set.notMem_empty _)
      · exact absurd ⟨q, h⟩ hcr

/-- A relation instance with an inhabited coordinate that lies in the base diagram is a
positive diagram atom: the lifted-root alternative is eliminated by constant support (the
instance mentions `g i`, the root mentions nothing). -/
private theorem relInst_mem_baseDiagram_of_nonempty {l : ℕ} {R : L.Relations l} {g : Fin l → ℕ}
    (i : Fin l) (hb : relInst R g ∈ baseDiagram φ lt) :
    ∃ q r : ℚ, q < r ∧ relInst R g = ratLtAtom lt q r := by
  rcases mem_baseDiagram_elim hb with heq | h
  · have hsupp := sentenceJConsts_lift_eq_empty (L := L) φ
    rw [← heq, sentenceJConsts_relInst_eq] at hsupp
    have : g i ∈ Set.range g := ⟨i, rfl⟩
    rw [hsupp] at this
    exact absurd this (Set.notMem_empty _)
  · exact h

/-- **Relation congruence** (the fifteenth field): one-coordinate replacement along a
remainder equality.  Remainder/root sources use ordinary equality congruence in the
approximating model; a diagram-atom source first marks both endpoints at a positive level,
obtains the atom through the chain, and descends. -/
theorem WOMem.rel_congr {S : Set L[[ℕ]].Sentenceω} (hS : WOMem φ lt S) (l : ℕ)
    (R : L.Relations l) (g : Fin l → ℕ) (i : Fin l) (b : ℕ)
    (hσ : relInst R g ∈ S) (heq : constEq (g i) b ∈ S) :
    WOMem φ lt (S ∪ {relInst R (Function.update g i b)}) := by
  classical
  by_cases hbb : relInst R (Function.update g i b) ∈ baseDiagram φ lt
  · exact hS.union_of_mem_base hbb
  have heqrem := hS.constEq_mem_rem heq
  refine hS.extend hbb (relInst_mem R _) ?_ ?_
  · -- finite support: coordinates from the source, the replacement from the equality
    rw [sentenceJConsts_relInst_eq]
    refine Set.Finite.subset ((hS.jConsts_finite_of_mem hσ).union
      (hS.jConsts_finite_of_mem heq)) ?_
    rintro c ⟨j, rfl⟩
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self]
      exact Or.inr (mem_sentenceJConsts_constEq_right _ _)
    · rw [Function.update_of_ne hji]
      exact Or.inl (by rw [sentenceJConsts_relInst_eq]; exact ⟨j, rfl⟩)
  · intro α hα
    by_cases hbrel : relInst R g ∈ baseDiagram φ lt
    · -- diagram-atom source: mark both endpoints at a positive level, then descend
      obtain ⟨q, r, hqr, hatom⟩ := relInst_mem_baseDiagram_of_nonempty i hbrel
      have hβ₁lt : (α + 1) + (α + 1) + 1 < (Cardinal.aleph 1).ord :=
        add_one_lt_omega1 (add_lt_omega1 (add_one_lt_omega1 hα) (add_one_lt_omega1 hα))
      obtain ⟨W₀⟩ := hS.star _ (add_one_lt_omega1 (add_lt_omega1 hβ₁lt hβ₁lt))
      obtain ⟨W₁, hq₁, -⟩ := W₀.mark_rat (lt_add_one _) q
      obtain ⟨W₂, hr₂, hsub₂⟩ := W₁.mark_rat (lt_add_one _) r
      have hq₂ : q ∈ Set.range W₂.mark := hsub₂ hq₁
      obtain ⟨iq, hiq⟩ := hq₂
      obtain ⟨ir, hir⟩ := hr₂
      have hij : iq < ir := by
        rw [← W₂.mark_mono.lt_iff_lt, hiq, hir]
        exact hqr
      have hpos : (0 : Ordinal.{0}) < α + 1 := lt_of_lt_of_le zero_lt_one le_add_self
      have hatomreal := W₂.realize_marked_atom hpos hij
      rw [hiq, hir] at hatomreal
      have hsrcreal : @Sentenceω.Realize L[[ℕ]] (relInst R g) W₂.M (wc W₂.inst W₂.h) := by
        rw [hatom]
        exact hatomreal
      have heqval : W₂.h (g i) = W₂.h b :=
        (realize_constEq_wc (base := W₂.inst) (h := W₂.h) _ _).mp (W₂.rem_realize _ heqrem)
      have htup : (fun j => W₂.h (Function.update g i b j)) = fun j => W₂.h (g j) := by
        funext j
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self]
          exact heqval.symm
        · rw [Function.update_of_ne hji]
      have htgt : @Sentenceω.Realize L[[ℕ]] (relInst R (Function.update g i b)) W₂.M
          (wc W₂.inst W₂.h) := by
        refine (realize_relInst_wc (base := W₂.inst) (h := W₂.h) R _).mpr ?_
        rw [htup]
        exact (realize_relInst_wc (base := W₂.inst) (h := W₂.h) R g).mp hsrcreal
      have hcov : ∀ q' : ℚ, ratConstIdx q' ∈
          sentenceJConsts (L' := L) (J := ℕ) (relInst R (Function.update g i b)) →
          q' ∈ Set.range W₂.mark := by
        intro q' hq'
        rw [sentenceJConsts_relInst_eq] at hq'
        obtain ⟨j, hj⟩ := hq'
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self] at hj
          refine W₂.mark_cover ⟨_, heqrem, ?_⟩
          rw [← hj]
          exact mem_sentenceJConsts_constEq_right _ _
        · rw [Function.update_of_ne hji] at hj
          have hmem : ratConstIdx q' ∈
              sentenceJConsts (L' := L) (J := ℕ) (relInst R g) := by
            rw [sentenceJConsts_relInst_eq]
            exact ⟨j, hj⟩
          rw [hatom, sentenceJConsts_ratLtAtom] at hmem
          rcases hmem with h' | h'
          · exact (ratConstIdx_injective h') ▸ ⟨iq, hiq⟩
          · exact (ratConstIdx_injective h') ▸ ⟨ir, hir⟩
      exact StarCondition.mono le_self_add ⟨W₂.add_sentence htgt hcov⟩
    · -- remainder source: ordinary equality congruence at the same witness
      have hrel : relInst R g ∈ (S \ baseDiagram φ lt) := ⟨hσ, hbrel⟩
      obtain ⟨W⟩ := hS.star α hα
      have hsrcreal := W.rem_realize _ hrel
      have heqval : W.h (g i) = W.h b :=
        (realize_constEq_wc (base := W.inst) (h := W.h) _ _).mp (W.rem_realize _ heqrem)
      have htup : (fun j => W.h (Function.update g i b j)) = fun j => W.h (g j) := by
        funext j
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self]
          exact heqval.symm
        · rw [Function.update_of_ne hji]
      have htgt : @Sentenceω.Realize L[[ℕ]] (relInst R (Function.update g i b)) W.M
          (wc W.inst W.h) := by
        refine (realize_relInst_wc (base := W.inst) (h := W.h) R _).mpr ?_
        rw [htup]
        exact (realize_relInst_wc (base := W.inst) (h := W.h) R g).mp hsrcreal
      refine ⟨W.add_sentence htgt ?_⟩
      intro q' hq'
      rw [sentenceJConsts_relInst_eq] at hq'
      obtain ⟨j, hj⟩ := hq'
      by_cases hji : j = i
      · subst hji
        rw [Function.update_self] at hj
        refine W.mark_cover ⟨_, heqrem, ?_⟩
        rw [← hj]
        exact mem_sentenceJConsts_constEq_right _ _
      · rw [Function.update_of_ne hji] at hj
        refine W.mark_cover ⟨_, hrel, ?_⟩
        rw [sentenceJConsts_relInst_eq]
        exact ⟨j, hj⟩

end FirstOrder.Language
