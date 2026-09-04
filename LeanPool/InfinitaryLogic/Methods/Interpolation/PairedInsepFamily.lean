/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.BaseOccurrenceProjections
import LeanPool.InfinitaryLogic.Methods.Interpolation.PairedInseparability
import LeanPool.InfinitaryLogic.Methods.Interpolation.InseparablePairFamily
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.ConsistencyPropertyEqOn
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.FairEnumeration
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.QuotientTruthLemma
/-!
# The paired inseparable-pair consistency family and its model (issue #8, commit 4c part 2)

This file assembles the **paired** finite inseparable-pair family on top of the validated
cross-coordinate gates (`PairedInseparability.lean`) and the one-sided left closures
(`InseparablePairFamily.lean`).  A family member is a `U`-bounded, symmetrically support-budgeted
pair `(Γ, Δ)` with `Γ ⊆ SentBnd F₁ R₁`, `Δ ⊆ SentBnd F₂ R₂`, inseparable at the shared vocabulary
`(F₁ ∩ F₂, R₁ ∩ R₂)`.

* `SentBnd F R` — the side vocabulary predicate (base symbols in `(F, R)`).
* `PairedInsepFamilyMem` — the family membership predicate (the `∃ Γ Δ A` decomposition).
* `pairedInsepConsistencyProperty` — the `ConsistencyPropertyEqOn (GenU rL rR)` bundle.  Each field
  case-splits the trigger between `Γ` and `Δ`: the `Γ` case reuses the one-sided left closure; the
  `Δ` case dualizes it through `insepAt_swap`; the cross cases (`C0`, shared-equality/relation
  transfer) use the `PairedInseparability` gates.
* `exists_paired_model` — from a root inseparable pair `{rL}` / `{rR}`, a single model realizing both
  roots (over a countable relational vocabulary).
* `exists_paired_model_neg` — the public wrapper: instantiating `rR := r₂.not` yields a model with
  `M ⊨ r₁ ∧ ¬ M ⊨ r₂`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## The side vocabulary predicate `SentBnd` -/

/-- **Side vocabulary bound.** A sentence whose base function/relation symbols lie in `(F, R)`. -/
def SentBnd (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) :
    Set L[[ℕ]].Sentenceω :=
  {σ | σ.baseFunctionsIn ⊆ F ∧ σ.baseRelationsIn ⊆ R}

/-! ## `SentBnd` closure lemmas -/

variable {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}

theorem sentBnd_not_iff {σ : L[[ℕ]].Sentenceω} : σ.not ∈ SentBnd F R ↔ σ ∈ SentBnd F R := by
  simp only [SentBnd, Set.mem_ofPred_eq, baseFunctionsIn_not, baseRelationsIn_not]

theorem sentBnd_imp_left {φ ψ : L[[ℕ]].Sentenceω} (h : φ.imp ψ ∈ SentBnd F R) : φ ∈ SentBnd F R :=
  ⟨baseFunctionsIn_imp_left.trans h.1, baseRelationsIn_imp_left.trans h.2⟩

theorem sentBnd_imp_right {φ ψ : L[[ℕ]].Sentenceω} (h : φ.imp ψ ∈ SentBnd F R) : ψ ∈ SentBnd F R :=
  ⟨baseFunctionsIn_imp_right.trans h.1, baseRelationsIn_imp_right.trans h.2⟩

theorem sentBnd_component_iInf {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ)
    (h : BoundedFormulaω.iInf φs ∈ SentBnd F R) : φs k ∈ SentBnd F R :=
  ⟨(baseFunctionsIn_component_iInf k).trans h.1, (baseRelationsIn_component_iInf k).trans h.2⟩

theorem sentBnd_component_iSup {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ)
    (h : BoundedFormulaω.iSup φs ∈ SentBnd F R) : φs k ∈ SentBnd F R :=
  ⟨(baseFunctionsIn_component_iSup k).trans h.1, (baseRelationsIn_component_iSup k).trans h.2⟩

theorem sentBnd_instConst {φ : L[[ℕ]].BoundedFormulaω Empty 1} (c : ℕ)
    (h : BoundedFormulaω.all φ ∈ SentBnd F R) : instConst c φ ∈ SentBnd F R :=
  ⟨(baseFunctionsIn_instConst_subset c φ).trans h.1,
   (baseRelationsIn_instConst_subset c φ).trans h.2⟩

theorem sentBnd_constEq (a b : ℕ) : constEq (L := L) a b ∈ SentBnd F R :=
  ⟨by rw [baseFunctionsIn_constEq]; exact Set.empty_subset _,
   by rw [baseRelationsIn_constEq]; exact Set.empty_subset _⟩

/-! ### Constant-expansion roots as side-bounded sentences

The two shapes every countable interpolation core needs of its labelled roots.  Each replaces a
four-part tuple of base-occurrence and negation rewrites at the call site. -/

/-- A constant-expansion image is bounded by its own base symbols. -/
theorem mapLanguage_withConstants_mem_sentBnd (r : L.Sentenceω) :
    BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r ∈ SentBnd r.functionsIn r.relationsIn :=
  ⟨(baseFunctionsIn_mapLanguage_withConstants r).le,
    (baseRelationsIn_mapLanguage_withConstants r).le⟩

/-- …and so is its negation, `SentBnd` being negation-invariant. -/
theorem mapLanguage_withConstants_not_mem_sentBnd (r : L.Sentenceω) :
    (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r).not
      ∈ SentBnd r.functionsIn r.relationsIn :=
  ⟨((baseFunctionsIn_not _).trans (baseFunctionsIn_mapLanguage_withConstants r)).le,
    ((baseRelationsIn_not _).trans (baseRelationsIn_mapLanguage_withConstants r)).le⟩

theorem sentBnd_relInst_congr {l : ℕ} (Rr : L.Relations l) {g : Fin l → ℕ} (g' : Fin l → ℕ)
    (h : relInst Rr g ∈ SentBnd F R) : relInst Rr g' ∈ SentBnd F R :=
  ⟨by rw [baseFunctionsIn_relInst]; exact Set.empty_subset _,
   by rw [baseRelationsIn_relInst Rr g' g]; exact h.2⟩

/-! ## Atomic constant-support facts -/

private theorem mem_constTermS_jConsts (c : ℕ) :
    c ∈ Term.jConsts (L' := L) (constTermS (L := L) c) := by
  show (⟨0, Sum.inr c⟩ : Σ n, L[[ℕ]].Functions n) ∈ (constTermS (L := L) c).functionsIn
  simp only [constTermS, Term.functionsIn, Set.iUnion_of_empty, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false]

theorem mem_sentenceJConsts_constEq_left (a b : ℕ) :
    a ∈ sentenceJConsts (L' := L) (J := ℕ) (constEq a b) :=
  Set.mem_union_left _ (mem_constTermS_jConsts a)

theorem mem_sentenceJConsts_constEq_right (a b : ℕ) :
    b ∈ sentenceJConsts (L' := L) (J := ℕ) (constEq a b) :=
  Set.mem_union_right _ (mem_constTermS_jConsts b)

theorem sentenceJConsts_constEq_subset (a b : ℕ) :
    sentenceJConsts (L' := L) (J := ℕ) (constEq a b) ⊆ ({a, b} : Set ℕ) := by
  intro k hk
  rcases hk with hk | hk
  · exact Or.inl (constTermS_jConsts a hk)
  · exact Or.inr (constTermS_jConsts b hk)

theorem sentenceJConsts_constEq_comm (a b : ℕ) :
    sentenceJConsts (L' := L) (J := ℕ) (constEq a b) =
      sentenceJConsts (L' := L) (J := ℕ) (constEq b a) := by
  ext k
  simp only [constEq, sentenceJConsts, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_union]
  tauto

theorem sentenceJConsts_relInst_eq {l : ℕ} (Rr : L.Relations l) (g : Fin l → ℕ) :
    sentenceJConsts (L' := L) (J := ℕ) (relInst Rr g) = Set.range g := by
  ext k
  simp only [relInst, sentenceJConsts, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, (constTermS_jConsts (g i) hi).symm⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, mem_constTermS_jConsts (g i)⟩

/-! ## The paired family -/

/-- **A paired family member**: a symmetrically support-budgeted, `U`-bounded, side-typed pair
`(Γ, Δ)` inseparable at the shared vocabulary `(F₁ ∩ F₂, R₁ ∩ R₂)`. -/
def PairedInsepFamilyMem (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω) (S : Set L[[ℕ]].Sentenceω) : Prop :=
  ∃ (Γ Δ : Set L[[ℕ]].Sentenceω) (A : Finset ℕ),
    Γ.Finite ∧ Δ.Finite ∧ Γ ⊆ GenU rL rR ∧ Δ ⊆ GenU rL rR ∧
    Γ ⊆ SentBnd F₁ R₁ ∧ Δ ⊆ SentBnd F₂ R₂ ∧
    ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
     (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ) ⊆ (↑A : Set ℕ)) ∧
    S = Γ ∪ Δ ∧ InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) A Γ Δ

variable {F₁ : Set (Σ n, L.Functions n)} {R₁ : Set (Σ n, L.Relations n)}
  {F₂ : Set (Σ n, L.Functions n)} {R₂ : Set (Σ n, L.Relations n)}
  {rL rR : L[[ℕ]].Sentenceω}

/-! ### Support and freshness bookkeeping -/

theorem support_mem_left {Γ Δ : Set L[[ℕ]].Sentenceω} {A : Finset ℕ} {φ : L[[ℕ]].Sentenceω}
    (hmem : φ ∈ Γ)
    (hsupp : ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ)) :
    sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) :=
  (Set.subset_biUnion_of_mem hmem).trans (Set.subset_union_left.trans hsupp)

theorem support_mem_right {Γ Δ : Set L[[ℕ]].Sentenceω} {A : Finset ℕ} {φ : L[[ℕ]].Sentenceω}
    (hmem : φ ∈ Δ)
    (hsupp : ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ)) :
    sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) :=
  (Set.subset_biUnion_of_mem hmem).trans (Set.subset_union_right.trans hsupp)

theorem support_mem {Γ Δ : Set L[[ℕ]].Sentenceω} {A : Finset ℕ} {φ : L[[ℕ]].Sentenceω}
    (hmem : φ ∈ Γ ∪ Δ)
    (hsupp : ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ)) :
    sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) := by
  rcases hmem with h | h
  · exact support_mem_left h hsupp
  · exact support_mem_right h hsupp

theorem support_insert_left {Γ Δ : Set L[[ℕ]].Sentenceω} {φ : L[[ℕ]].Sentenceω} {A : Finset ℕ}
    (hφ : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ))
    (h : ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ)) :
    ((⋃ γ ∈ insert φ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ) := by
  rw [Set.biUnion_insert, Set.union_assoc]
  exact Set.union_subset hφ h

theorem support_insert_right {Γ Δ : Set L[[ℕ]].Sentenceω} {φ : L[[ℕ]].Sentenceω} {A : Finset ℕ}
    (hφ : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ))
    (h : ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ)) :
    ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ insert φ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ) := by
  rw [Set.biUnion_insert]
  exact Set.union_subset ((Set.subset_union_left).trans h)
    (Set.union_subset hφ ((Set.subset_union_right).trans h))

theorem fresh_left {Γ Δ : Set L[[ℕ]].Sentenceω} {A : Finset ℕ} (c : ℕ) (hc : c ∉ (↑A : Set ℕ))
    (hsupp : ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ)) :
    ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ :=
  fun _ hγ hmem => hc (hsupp (Set.mem_union_left _ (Set.mem_biUnion hγ hmem)))

theorem fresh_right {Γ Δ : Set L[[ℕ]].Sentenceω} {A : Finset ℕ} (c : ℕ) (hc : c ∉ (↑A : Set ℕ))
    (hsupp : ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ)) :
    ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ :=
  fun _ hδ hmem => hc (hsupp (Set.mem_union_right _ (Set.mem_biUnion hδ hmem)))

/-- Grow the `Δ`-coordinate by an entailed sentence (the right-coordinate twin of
`insepAt_insert_of_entails`, obtained through `insepAt_swap`). -/
private theorem insepAt_insert_right_of_entails {F' : Set (Σ n, L.Functions n)}
    {R' : Set (Σ n, L.Relations n)} {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}
    {φ : L[[ℕ]].Sentenceω} (hcons : Theoryω.Entails Δ φ) (h : InsepAt F' R' A Γ Δ) :
    InsepAt F' R' A Γ (insert φ Δ) :=
  insepAt_swap (insepAt_insert_of_entails hcons (insepAt_swap h))

/-! ### The two coordinate-growth constructors -/

/-- Add `φ` to the `Γ`-coordinate of a paired family member. -/
private theorem pairedInsep_insert_left {S Γ Δ : Set L[[ℕ]].Sentenceω} {A : Finset ℕ}
    {φ : L[[ℕ]].Sentenceω} (hSeq : S = Γ ∪ Δ)
    (hΓfin : Γ.Finite) (hΔfin : Δ.Finite)
    (hΓU : Γ ⊆ GenU rL rR) (hΔU : Δ ⊆ GenU rL rR)
    (hΓS : Γ ⊆ SentBnd F₁ R₁) (hΔS : Δ ⊆ SentBnd F₂ R₂)
    (hφU : φ ∈ GenU rL rR) (hφS : φ ∈ SentBnd F₁ R₁)
    (hsupp : ((⋃ γ ∈ insert φ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ))
    (hA : InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) A (insert φ Γ) Δ) :
    PairedInsepFamilyMem F₁ R₁ F₂ R₂ rL rR (S ∪ {φ}) := by
  rw [hSeq, Set.union_singleton, ← Set.insert_union]
  exact ⟨insert φ Γ, Δ, A, hΓfin.insert φ, hΔfin,
    Set.insert_subset_iff.mpr ⟨hφU, hΓU⟩, hΔU,
    Set.insert_subset_iff.mpr ⟨hφS, hΓS⟩, hΔS, hsupp, rfl, hA⟩

/-- Add `φ` to the `Δ`-coordinate of a paired family member. -/
private theorem pairedInsep_insert_right {S Γ Δ : Set L[[ℕ]].Sentenceω} {A : Finset ℕ}
    {φ : L[[ℕ]].Sentenceω} (hSeq : S = Γ ∪ Δ)
    (hΓfin : Γ.Finite) (hΔfin : Δ.Finite)
    (hΓU : Γ ⊆ GenU rL rR) (hΔU : Δ ⊆ GenU rL rR)
    (hΓS : Γ ⊆ SentBnd F₁ R₁) (hΔS : Δ ⊆ SentBnd F₂ R₂)
    (hφU : φ ∈ GenU rL rR) (hφS : φ ∈ SentBnd F₂ R₂)
    (hsupp : ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ insert φ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ))
    (hA : InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) A Γ (insert φ Δ)) :
    PairedInsepFamilyMem F₁ R₁ F₂ R₂ rL rR (S ∪ {φ}) := by
  rw [hSeq, Set.union_singleton, ← Set.union_insert]
  exact ⟨Γ, insert φ Δ, A, hΓfin, hΔfin.insert φ, hΓU,
    Set.insert_subset_iff.mpr ⟨hφU, hΔU⟩, hΓS,
    Set.insert_subset_iff.mpr ⟨hφS, hΔS⟩, hsupp, rfl, hA⟩

/-! ## The paired inseparable-pair consistency property -/

/-- **The paired inseparable-pair consistency property.** The finite paired family over the
generated universe `GenU rL rR`, with each `ConsistencyPropertyEqOn` closure field discharged by a
`Γ`/`Δ` case split: the `Γ` case reuses the one-sided left closure, the `Δ` case dualizes it through
`insepAt_swap`, and the cross cases use the `PairedInseparability` gates. The root finiteness
hypotheses enter only in `neg_all_witness` (to choose a fresh witness). -/
private def pairedInsepConsistencyProperty (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω)
    (hrL : (sentenceJConsts (L' := L) (J := ℕ) rL).Finite)
    (hrR : (sentenceJConsts (L' := L) (J := ℕ) rR).Finite) :
    ConsistencyPropertyEqOn (GenU rL rR) where
  sets := {S | PairedInsepFamilyMem F₁ R₁ F₂ R₂ rL rR S}
  subset_U := fun S hS => by
    obtain ⟨Γ, Δ, A, _, _, hΓU, hΔU, _, _, _, hSeq, _⟩ := hS
    rw [hSeq]; exact Set.union_subset hΓU hΔU
  C0_no_falsum := fun S hS hmem => by
    obtain ⟨Γ, Δ, A, _, _, _, _, _, _, _, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with h | h
    · exact insepAt_falsum_absurd h hA
    · exact insepAt_falsum_absurd h (insepAt_swap hA)
  C0_no_contradiction := fun S hS φ => by
    obtain ⟨Γ, Δ, A, _, _, _, _, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rintro ⟨hφ, hφn⟩
    rw [hSeq] at hφ hφn
    rcases hφ with hφΓ | hφΔ
    · rcases hφn with hφnΓ | hφnΔ
      · exact insepAt_contradiction_absurd hφΓ hφnΓ hA
      · refine insepAt_shared_contradiction ?_ ?_ (support_mem_left hφΓ hsupp)
          (Theoryω.entails_of_mem hφΓ) (Theoryω.entails_of_mem hφnΔ) hA
        · exact Set.subset_inter (hΓS hφΓ).1 (by rw [← baseFunctionsIn_not]; exact (hΔS hφnΔ).1)
        · exact Set.subset_inter (hΓS hφΓ).2 (by rw [← baseRelationsIn_not]; exact (hΔS hφnΔ).2)
    · rcases hφn with hφnΓ | hφnΔ
      · refine insepAt_shared_contradiction ?_ ?_ (support_mem_right hφΔ hsupp)
          (Theoryω.entails_of_mem hφΔ) (Theoryω.entails_of_mem hφnΓ) (insepAt_swap hA)
        · exact Set.subset_inter (by rw [← baseFunctionsIn_not]; exact (hΓS hφnΓ).1) (hΔS hφΔ).1
        · exact Set.subset_inter (by rw [← baseRelationsIn_not]; exact (hΓS hφnΓ).2) (hΔS hφΔ).2
      · exact insepAt_contradiction_absurd hφΔ hφnΔ (insepAt_swap hA)
  C1_imp := fun S hS φ ψ hmem => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · rcases insepAt_imp_dichotomy hΓ hA with h | h
      · have hns : sentenceJConsts (L' := L) (J := ℕ) φ.not ⊆ (↑A : Set ℕ) := by
          rw [sentenceJConsts_not]
          exact (sentenceJConsts_imp_left φ ψ).trans (support_mem_left hΓ hsupp)
        exact Or.inl (pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (imp_negleft_mem (hΓU hΓ)) (sentBnd_not_iff.mpr (sentBnd_imp_left (hΓS hΓ)))
          (support_insert_left hns hsupp) h)
      · exact Or.inr (pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (imp_right_mem (hΓU hΓ)) (sentBnd_imp_right (hΓS hΓ))
          (support_insert_left ((sentenceJConsts_imp_right φ ψ).trans (support_mem_left hΓ hsupp))
            hsupp) h)
    · rcases insepAt_imp_dichotomy hΔ (insepAt_swap hA) with h | h
      · have hns : sentenceJConsts (L' := L) (J := ℕ) φ.not ⊆ (↑A : Set ℕ) := by
          rw [sentenceJConsts_not]
          exact (sentenceJConsts_imp_left φ ψ).trans (support_mem_right hΔ hsupp)
        exact Or.inl (pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (imp_negleft_mem (hΔU hΔ)) (sentBnd_not_iff.mpr (sentBnd_imp_left (hΔS hΔ)))
          (support_insert_right hns hsupp) (insepAt_swap h))
      · exact Or.inr (pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (imp_right_mem (hΔU hΔ)) (sentBnd_imp_right (hΔS hΔ))
          (support_insert_right ((sentenceJConsts_imp_right φ ψ).trans (support_mem_right hΔ hsupp))
            hsupp) (insepAt_swap h))
  C1_neg_imp := fun S hS φ ψ hmem => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · have himpsupp : sentenceJConsts (L' := L) (J := ℕ) (φ.imp ψ) ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]; exact support_mem_left hΓ hsupp
      have hφsupp : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) :=
        (sentenceJConsts_imp_left φ ψ).trans himpsupp
      have hψnsupp : sentenceJConsts (L' := L) (J := ℕ) ψ.not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]; exact (sentenceJConsts_imp_right φ ψ).trans himpsupp
      exact ⟨pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (negimp_left_mem (hΓU hΓ)) (sentBnd_imp_left (sentBnd_not_iff.mp (hΓS hΓ)))
          (support_insert_left hφsupp hsupp)
          (insepAt_insert_of_entails (entails_of_mem_of_entails hΓ (negimp_entails_left φ ψ)) hA),
        pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (negimp_right_mem (hΓU hΓ))
          (sentBnd_not_iff.mpr (sentBnd_imp_right (sentBnd_not_iff.mp (hΓS hΓ))))
          (support_insert_left hψnsupp hsupp)
          (insepAt_insert_of_entails (entails_of_mem_of_entails hΓ (negimp_entails_right φ ψ)) hA)⟩
    · have himpsupp : sentenceJConsts (L' := L) (J := ℕ) (φ.imp ψ) ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]; exact support_mem_right hΔ hsupp
      have hφsupp : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) :=
        (sentenceJConsts_imp_left φ ψ).trans himpsupp
      have hψnsupp : sentenceJConsts (L' := L) (J := ℕ) ψ.not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]; exact (sentenceJConsts_imp_right φ ψ).trans himpsupp
      exact ⟨pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (negimp_left_mem (hΔU hΔ)) (sentBnd_imp_left (sentBnd_not_iff.mp (hΔS hΔ)))
          (support_insert_right hφsupp hsupp)
          (insepAt_insert_right_of_entails
            (entails_of_mem_of_entails hΔ (negimp_entails_left φ ψ)) hA),
        pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (negimp_right_mem (hΔU hΔ))
          (sentBnd_not_iff.mpr (sentBnd_imp_right (sentBnd_not_iff.mp (hΔS hΔ))))
          (support_insert_right hψnsupp hsupp)
          (insepAt_insert_right_of_entails
            (entails_of_mem_of_entails hΔ (negimp_entails_right φ ψ)) hA)⟩
  C2_not_not := fun S hS φ hmem => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · have hφsupp : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not, ← sentenceJConsts_not]; exact support_mem_left hΓ hsupp
      exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negimp_left_mem (φ := φ) (ψ := (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω)) (hΓU hΓ))
        (sentBnd_not_iff.mp (sentBnd_not_iff.mp (hΓS hΓ))) (support_insert_left hφsupp hsupp)
        (insepAt_insert_of_entails (entails_of_mem_of_entails hΓ (not_not_entails φ)) hA)
    · have hφsupp : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not, ← sentenceJConsts_not]; exact support_mem_right hΔ hsupp
      exact pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negimp_left_mem (φ := φ) (ψ := (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω)) (hΔU hΔ))
        (sentBnd_not_iff.mp (sentBnd_not_iff.mp (hΔS hΔ))) (support_insert_right hφsupp hsupp)
        (insepAt_insert_right_of_entails (entails_of_mem_of_entails hΔ (not_not_entails φ)) hA)
  C3_iInf := fun S hS φs hmem k => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · refine pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (iInf_comp_mem k (hΓU hΓ)) (sentBnd_component_iInf k (hΓS hΓ)) ?_
        (insepAt_insert_of_entails (entails_of_mem_of_entails hΓ (iInf_entails_component φs k)) hA)
      exact support_insert_left
        ((sentenceJConsts_component_iInf φs k).trans (support_mem_left hΓ hsupp)) hsupp
    · refine pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (iInf_comp_mem k (hΔU hΔ)) (sentBnd_component_iInf k (hΔS hΔ)) ?_
        (insepAt_insert_right_of_entails (entails_of_mem_of_entails hΔ (iInf_entails_component φs k)) hA)
      exact support_insert_right
        ((sentenceJConsts_component_iInf φs k).trans (support_mem_right hΔ hsupp)) hsupp
  C3_neg_iInf := fun S hS φs hmem => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · obtain ⟨k, hk⟩ := insepAt_neg_iInf_component φs hΓ hA
      have hinfsupp : sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iInf φs) ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]; exact support_mem_left hΓ hsupp
      have hns : sentenceJConsts (L' := L) (J := ℕ) (φs k).not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]; exact (sentenceJConsts_component_iInf φs k).trans hinfsupp
      exact ⟨k, pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negiInf_comp_mem k (hΓU hΓ))
        (sentBnd_not_iff.mpr (sentBnd_component_iInf k (sentBnd_not_iff.mp (hΓS hΓ))))
        (support_insert_left hns hsupp) hk⟩
    · obtain ⟨k, hk⟩ := insepAt_neg_iInf_component φs hΔ (insepAt_swap hA)
      have hinfsupp : sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iInf φs) ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]; exact support_mem_right hΔ hsupp
      have hns : sentenceJConsts (L' := L) (J := ℕ) (φs k).not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]; exact (sentenceJConsts_component_iInf φs k).trans hinfsupp
      exact ⟨k, pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negiInf_comp_mem k (hΔU hΔ))
        (sentBnd_not_iff.mpr (sentBnd_component_iInf k (sentBnd_not_iff.mp (hΔS hΔ))))
        (support_insert_right hns hsupp) (insepAt_swap hk)⟩
  C4_iSup := fun S hS φs hmem => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · obtain ⟨k, hk⟩ := insepAt_iSup_component φs hΓ hA
      refine ⟨k, pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (iSup_comp_mem k (hΓU hΓ)) (sentBnd_component_iSup k (hΓS hΓ)) ?_ hk⟩
      exact support_insert_left
        ((sentenceJConsts_component_iSup φs k).trans (support_mem_left hΓ hsupp)) hsupp
    · obtain ⟨k, hk⟩ := insepAt_iSup_component φs hΔ (insepAt_swap hA)
      refine ⟨k, pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (iSup_comp_mem k (hΔU hΔ)) (sentBnd_component_iSup k (hΔS hΔ)) ?_ (insepAt_swap hk)⟩
      exact support_insert_right
        ((sentenceJConsts_component_iSup φs k).trans (support_mem_right hΔ hsupp)) hsupp
  C4_neg_iSup := fun S hS φs hmem k => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · have hsupsupp : sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iSup φs) ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]; exact support_mem_left hΓ hsupp
      have hns : sentenceJConsts (L' := L) (J := ℕ) (φs k).not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]; exact (sentenceJConsts_component_iSup φs k).trans hsupsupp
      exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negiSup_comp_mem k (hΓU hΓ))
        (sentBnd_not_iff.mpr (sentBnd_component_iSup k (sentBnd_not_iff.mp (hΓS hΓ))))
        (support_insert_left hns hsupp)
        (insepAt_insert_of_entails
          (entails_of_mem_of_entails hΓ (neg_iSup_entails_neg_component φs k)) hA)
    · have hsupsupp : sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iSup φs) ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]; exact support_mem_right hΔ hsupp
      have hns : sentenceJConsts (L' := L) (J := ℕ) (φs k).not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]; exact (sentenceJConsts_component_iSup φs k).trans hsupsupp
      exact pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negiSup_comp_mem k (hΔU hΔ))
        (sentBnd_not_iff.mpr (sentBnd_component_iSup k (sentBnd_not_iff.mp (hΔS hΔ))))
        (support_insert_right hns hsupp)
        (insepAt_insert_right_of_entails
          (entails_of_mem_of_entails hΔ (neg_iSup_entails_neg_component φs k)) hA)
  eq_refl := fun S hS c => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    have hccsupp : sentenceJConsts (L' := L) (J := ℕ) (constEq c c) ⊆ (↑(insert c A) : Set ℕ) := by
      refine (sentenceJConsts_constEq_subset c c).trans ?_
      rw [Finset.coe_insert]
      exact Set.insert_subset_iff.mpr
        ⟨Set.mem_insert c _, Set.singleton_subset_iff.mpr (Set.mem_insert c _)⟩
    have hA' : InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) (insert c A) (insert (constEq c c) Γ) Δ := by
      by_cases hcA : c ∈ A
      · rw [Finset.insert_eq_self.mpr hcA]; exact insepAt_insert_of_entails (entails_constEq_refl c) hA
      · exact insepAt_insert_of_entails (entails_constEq_refl c)
          (insepAt_grow_fresh c (fresh_right c (fun h => hcA (Finset.mem_coe.mp h)) hsupp) hA)
    exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (eqRefl_mem c) (sentBnd_constEq c c)
      (support_insert_left hccsupp (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hA'
  eq_symm := fun S hS a b hmem => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    have hbasupp : sentenceJConsts (L' := L) (J := ℕ) (constEq b a) ⊆ (↑A : Set ℕ) := by
      rw [← sentenceJConsts_constEq_comm a b]; exact support_mem hmem hsupp
    rcases hmem with hΓ | hΔ
    · exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (constEq_mem b a)
        (sentBnd_constEq b a) (support_insert_left hbasupp hsupp)
        (insepAt_insert_of_entails (entails_constEq_symm hΓ) hA)
    · exact pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (constEq_mem b a)
        (sentBnd_constEq b a) (support_insert_right hbasupp hsupp)
        (insepAt_insert_right_of_entails (entails_constEq_symm hΔ) hA)
  eq_trans := fun S hS a b d hmem1 hmem2 => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem1 hmem2
    have haA : a ∈ (↑A : Set ℕ) := support_mem hmem1 hsupp (mem_sentenceJConsts_constEq_left a b)
    have hdA : d ∈ (↑A : Set ℕ) := support_mem hmem2 hsupp (mem_sentenceJConsts_constEq_right b d)
    have hadsupp : sentenceJConsts (L' := L) (J := ℕ) (constEq a d) ⊆ (↑A : Set ℕ) :=
      (sentenceJConsts_constEq_subset a d).trans
        (Set.insert_subset_iff.mpr ⟨haA, Set.singleton_subset_iff.mpr hdA⟩)
    have habsupp : sentenceJConsts (L' := L) (J := ℕ) (constEq a b) ⊆ (↑A : Set ℕ) :=
      support_mem hmem1 hsupp
    have hbdsupp : sentenceJConsts (L' := L) (J := ℕ) (constEq b d) ⊆ (↑A : Set ℕ) :=
      support_mem hmem2 hsupp
    rcases hmem1 with h1Γ | h1Δ <;> rcases hmem2 with h2Γ | h2Δ
    · exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (constEq_mem a d)
        (sentBnd_constEq a d) (support_insert_left hadsupp hsupp)
        (insepAt_insert_of_entails (entails_constEq_trans h1Γ h2Γ) hA)
    · exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (constEq_mem a d)
        (sentBnd_constEq a d) (support_insert_left hadsupp hsupp)
        (insepAt_insert_of_shared_entails
          (by rw [baseFunctionsIn_constEq]; exact Set.empty_subset _)
          (by rw [baseRelationsIn_constEq]; exact Set.empty_subset _)
          hbdsupp (Theoryω.entails_of_mem h2Δ)
          (entails_constEq_trans (Set.mem_insert_of_mem _ h1Γ) (Set.mem_insert _ _)) hA)
    · exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (constEq_mem a d)
        (sentBnd_constEq a d) (support_insert_left hadsupp hsupp)
        (insepAt_insert_of_shared_entails
          (by rw [baseFunctionsIn_constEq]; exact Set.empty_subset _)
          (by rw [baseRelationsIn_constEq]; exact Set.empty_subset _)
          habsupp (Theoryω.entails_of_mem h1Δ)
          (entails_constEq_trans (Set.mem_insert _ _) (Set.mem_insert_of_mem _ h2Γ)) hA)
    · exact pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (constEq_mem a d)
        (sentBnd_constEq a d) (support_insert_right hadsupp hsupp)
        (insepAt_swap (insepAt_insert_of_entails (entails_constEq_trans h1Δ h2Δ) (insepAt_swap hA)))
  rel_congr := fun S hS l R g i b hmem1 hmem2 => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem1 hmem2
    have hconstsupp : sentenceJConsts (L' := L) (J := ℕ) (constEq (g i) b) ⊆ (↑A : Set ℕ) :=
      support_mem hmem2 hsupp
    have hbA : b ∈ (↑A : Set ℕ) := hconstsupp (mem_sentenceJConsts_constEq_right (g i) b)
    have hrelsupp : sentenceJConsts (L' := L) (J := ℕ) (relInst R g) ⊆ (↑A : Set ℕ) :=
      support_mem hmem1 hsupp
    have hupdsupp : sentenceJConsts (L' := L) (J := ℕ) (relInst R (Function.update g i b))
        ⊆ (↑A : Set ℕ) := by
      rw [sentenceJConsts_relInst_eq]
      intro k hk
      obtain ⟨j, rfl⟩ := hk
      by_cases hji : j = i
      · subst hji; rw [Function.update_self]; exact hbA
      · rw [Function.update_of_ne hji]
        exact hrelsupp (by rw [sentenceJConsts_relInst_eq]; exact ⟨j, rfl⟩)
    rcases hmem1 with h1Γ | h1Δ
    · rcases hmem2 with h2Γ | h2Δ
      · exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (relInst_mem R (Function.update g i b))
          (sentBnd_relInst_congr R (Function.update g i b) (hΓS h1Γ))
          (support_insert_left hupdsupp hsupp)
          (insepAt_insert_of_entails (entails_rel_congr R g i b h1Γ h2Γ) hA)
      · exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (relInst_mem R (Function.update g i b))
          (sentBnd_relInst_congr R (Function.update g i b) (hΓS h1Γ))
          (support_insert_left hupdsupp hsupp)
          (insepAt_insert_of_shared_entails
            (by rw [baseFunctionsIn_constEq]; exact Set.empty_subset _)
            (by rw [baseRelationsIn_constEq]; exact Set.empty_subset _)
            hconstsupp (Theoryω.entails_of_mem h2Δ)
            (entails_rel_congr R g i b (Set.mem_insert_of_mem _ h1Γ) (Set.mem_insert _ _)) hA)
    · rcases hmem2 with h2Γ | h2Δ
      · exact pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (relInst_mem R (Function.update g i b))
          (sentBnd_relInst_congr R (Function.update g i b) (hΔS h1Δ))
          (support_insert_right hupdsupp hsupp)
          (insepAt_swap (insepAt_insert_of_shared_entails
            (by rw [baseFunctionsIn_constEq]; exact Set.empty_subset _)
            (by rw [baseRelationsIn_constEq]; exact Set.empty_subset _)
            hconstsupp (Theoryω.entails_of_mem h2Γ)
            (entails_rel_congr R g i b (Set.mem_insert_of_mem _ h1Δ) (Set.mem_insert _ _))
            (insepAt_swap hA)))
      · exact pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (relInst_mem R (Function.update g i b))
          (sentBnd_relInst_congr R (Function.update g i b) (hΔS h1Δ))
          (support_insert_right hupdsupp hsupp)
          (insepAt_swap (insepAt_insert_of_entails (entails_rel_congr R g i b h1Δ h2Δ) (insepAt_swap hA)))
  all_inst := fun S hS φ hmem c => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · have hinstsupp : sentenceJConsts (L' := L) (J := ℕ) (instConst c φ)
          ⊆ (↑(insert c A) : Set ℕ) := by
        refine (sentenceJConsts_instConst_subset c φ).trans ?_
        rw [Finset.coe_insert]
        exact Set.union_subset ((support_mem_left hΓ hsupp).trans (Set.subset_insert c _))
          (Set.singleton_subset_iff.mpr (Set.mem_insert c _))
      have hA' : InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) (insert c A) (insert (instConst c φ) Γ) Δ := by
        by_cases hcA : c ∈ A
        · rw [Finset.insert_eq_self.mpr hcA]
          exact insepAt_insert_of_entails (entails_of_mem_of_entails hΓ (all_entails_instConst c φ)) hA
        · exact insepAt_insert_of_entails (entails_of_mem_of_entails hΓ (all_entails_instConst c φ))
            (insepAt_grow_fresh c (fresh_right c (fun h => hcA (Finset.mem_coe.mp h)) hsupp) hA)
      exact pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (all_inst_mem c (hΓU hΓ)) (sentBnd_instConst c (hΓS hΓ))
        (support_insert_left hinstsupp
          (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hA'
    · have hinstsupp : sentenceJConsts (L' := L) (J := ℕ) (instConst c φ)
          ⊆ (↑(insert c A) : Set ℕ) := by
        refine (sentenceJConsts_instConst_subset c φ).trans ?_
        rw [Finset.coe_insert]
        exact Set.union_subset ((support_mem_right hΔ hsupp).trans (Set.subset_insert c _))
          (Set.singleton_subset_iff.mpr (Set.mem_insert c _))
      have hA' : InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) (insert c A) Γ (insert (instConst c φ) Δ) := by
        by_cases hcA : c ∈ A
        · rw [Finset.insert_eq_self.mpr hcA]
          exact insepAt_insert_right_of_entails
            (entails_of_mem_of_entails hΔ (all_entails_instConst c φ)) hA
        · exact insepAt_insert_right_of_entails
            (entails_of_mem_of_entails hΔ (all_entails_instConst c φ))
            (insepAt_grow_fresh c (fresh_right c (fun h => hcA (Finset.mem_coe.mp h)) hsupp) hA)
      exact pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (all_inst_mem c (hΔU hΔ)) (sentBnd_instConst c (hΔS hΔ))
        (support_insert_right hinstsupp
          (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hA'
  neg_all_witness := fun S hS φ hmem => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · have hmemU : (BoundedFormulaω.all φ).not ∈ GenU rL rR := hΓU hΓ
      have hφfin : (sentenceJConsts (L' := L) (J := ℕ) φ).Finite := by
        have hx := genU_finite_support hrL hrR _ hmemU
        rwa [sentenceJConsts_not, sentenceJConsts_all] at hx
      obtain ⟨c, hc⟩ := (A.finite_toSet.union hφfin).exists_notMem
      simp only [Set.mem_union, not_or] at hc
      obtain ⟨hcA, hcφ⟩ := hc
      have hAins : InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) A (insert (BoundedFormulaω.all φ).not Γ) Δ := by
        rw [Set.insert_eq_self.mpr hΓ]; exact hA
      have hins := insepAt_not_instConst_of_insepAt_not_all c φ
        (by rw [sentenceJConsts_not]; exact hcφ) (fresh_left c hcA hsupp) (fresh_right c hcA hsupp) hAins
      rw [instConst_not] at hins
      have hinstsupp : sentenceJConsts (L' := L) (J := ℕ) ((instConst c φ).not)
          ⊆ (↑(insert c A) : Set ℕ) := by
        rw [sentenceJConsts_not]
        refine (sentenceJConsts_instConst_subset c φ).trans ?_
        rw [Finset.coe_insert]
        refine Set.union_subset ?_ (Set.singleton_subset_iff.mpr (Set.mem_insert c _))
        refine (?_ : sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.all φ)
          ⊆ (↑A : Set ℕ)).trans (Set.subset_insert c _)
        have hx := support_mem_left hΓ hsupp
        rwa [sentenceJConsts_not] at hx
      exact ⟨c, pairedInsep_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (negall_inst_mem c hmemU)
        (sentBnd_not_iff.mpr (sentBnd_instConst c (sentBnd_not_iff.mp (hΓS hΓ))))
        (support_insert_left hinstsupp
          (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hins⟩
    · have hmemU : (BoundedFormulaω.all φ).not ∈ GenU rL rR := hΔU hΔ
      have hφfin : (sentenceJConsts (L' := L) (J := ℕ) φ).Finite := by
        have hx := genU_finite_support hrL hrR _ hmemU
        rwa [sentenceJConsts_not, sentenceJConsts_all] at hx
      obtain ⟨c, hc⟩ := (A.finite_toSet.union hφfin).exists_notMem
      simp only [Set.mem_union, not_or] at hc
      obtain ⟨hcA, hcφ⟩ := hc
      have hAins : InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) A (insert (BoundedFormulaω.all φ).not Δ) Γ := by
        rw [Set.insert_eq_self.mpr hΔ]; exact insepAt_swap hA
      have hins := insepAt_not_instConst_of_insepAt_not_all c φ
        (by rw [sentenceJConsts_not]; exact hcφ) (fresh_right c hcA hsupp) (fresh_left c hcA hsupp) hAins
      rw [instConst_not] at hins
      have hins' := insepAt_swap hins
      have hinstsupp : sentenceJConsts (L' := L) (J := ℕ) ((instConst c φ).not)
          ⊆ (↑(insert c A) : Set ℕ) := by
        rw [sentenceJConsts_not]
        refine (sentenceJConsts_instConst_subset c φ).trans ?_
        rw [Finset.coe_insert]
        refine Set.union_subset ?_ (Set.singleton_subset_iff.mpr (Set.mem_insert c _))
        refine (?_ : sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.all φ)
          ⊆ (↑A : Set ℕ)).trans (Set.subset_insert c _)
        have hx := support_mem_right hΔ hsupp
        rwa [sentenceJConsts_not] at hx
      exact ⟨c, pairedInsep_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (negall_inst_mem c hmemU)
        (sentBnd_not_iff.mpr (sentBnd_instConst c (sentBnd_not_iff.mp (hΔS hΔ))))
        (support_insert_right hinstsupp
          (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hins'⟩

/-! ## The paired model endpoint -/

/-- **Paired model existence.** From a root inseparable pair `{rL}` / `{rR}` (support-budgeted at
`A₀`, side-typed at `(F₁, R₁)` / `(F₂, R₂)`, inseparable at the shared vocabulary), over a countable
relational vocabulary, there is a single `L[[ℕ]]`-model realizing **both** roots. The fair
enumeration produces a Henkin-complete `S* ⊇ {rL, rR}`; its quotient term model realizes every
positive member, and both roots enter positively. -/
private theorem exists_paired_model [L.IsRelational] [Countable (Σ l, L.Relations l)]
    (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω)
    (hrL : (sentenceJConsts (L' := L) (J := ℕ) rL).Finite)
    (hrR : (sentenceJConsts (L' := L) (J := ℕ) rR).Finite)
    (hrLsent : rL ∈ SentBnd F₁ R₁) (hrRsent : rR ∈ SentBnd F₂ R₂)
    (A₀ : Finset ℕ)
    (hsupp : sentenceJConsts (L' := L) (J := ℕ) rL ∪ sentenceJConsts (L' := L) (J := ℕ) rR
      ⊆ (↑A₀ : Set ℕ))
    (hroot : InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) A₀ {rL} {rR}) :
    ∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M),
      Sentenceω.Realize rL M ∧ Sentenceω.Realize rR M := by
  have : Countable ↥(GenU (L := L) rL rR) := genU_countable.to_subtype
  have hmem : PairedInsepFamilyMem F₁ R₁ F₂ R₂ rL rR ({rL} ∪ {rR}) := by
    refine ⟨{rL}, {rR}, A₀, Set.finite_singleton _, Set.finite_singleton _,
      Set.singleton_subset_iff.mpr root₁_mem, Set.singleton_subset_iff.mpr root₂_mem,
      Set.singleton_subset_iff.mpr hrLsent, Set.singleton_subset_iff.mpr hrRsent, ?_, rfl, hroot⟩
    rw [Set.biUnion_singleton, Set.biUnion_singleton]
    exact hsupp
  obtain ⟨Sstar, hsub, _, hsc⟩ := exists_henkinComplete
    (P := pairedInsepConsistencyProperty F₁ R₁ F₂ R₂ rL rR hrL hrR) ⟨{rL} ∪ {rR}, hmem⟩
  obtain ⟨M, instM, neM, hpos, _⟩ := exists_model_of_henkinComplete hsc
  exact ⟨M, instM, neM, hpos rL (hsub (Set.mem_union_left _ rfl)),
    hpos rR (hsub (Set.mem_union_right _ rfl))⟩

/-- **Public wrapper (interpolation polarity).** Instantiating `rR := r₂.not` yields a single model
with `M ⊨ r₁` and `¬ M ⊨ r₂` — the seed `{r₁, r₂.not}` (not `{r₁, r₂}`). -/
theorem exists_paired_model_neg [L.IsRelational] [Countable (Σ l, L.Relations l)]
    (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (r₁ r₂ : L[[ℕ]].Sentenceω)
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite)
    (hr₁sent : r₁ ∈ SentBnd F₁ R₁) (hr₂sent : r₂.not ∈ SentBnd F₂ R₂)
    (A₀ : Finset ℕ)
    (hsupp : sentenceJConsts (L' := L) (J := ℕ) r₁ ∪ sentenceJConsts (L' := L) (J := ℕ) r₂.not
      ⊆ (↑A₀ : Set ℕ))
    (hroot : InsepAt (F₁ ∩ F₂) (R₁ ∩ R₂) A₀ {r₁} {r₂.not}) :
    ∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M),
      Sentenceω.Realize r₁ M ∧ ¬ Sentenceω.Realize r₂ M := by
  obtain ⟨M, instM, neM, hr1, hr2not⟩ := exists_paired_model F₁ R₁ F₂ R₂ r₁ r₂.not hr₁
    (by rw [sentenceJConsts_not]; exact hr₂) hr₁sent hr₂sent A₀ hsupp hroot
  refine ⟨M, instM, neM, hr1, ?_⟩
  simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hr2not
  exact hr2not

end FirstOrder.Language
