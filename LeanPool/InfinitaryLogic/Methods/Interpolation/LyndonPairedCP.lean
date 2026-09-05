/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.LyndonPairedFamily
/-!
# The polarity-refined consistency property and paired model (issue #14, Unit 4b)

The sixteen `ConsistencyPropertyEqOn` fields for the polarity-refined paired family, and the
model endpoint the Lyndon argument will consume.

The port is field-for-field with the Craig instance; only the *side-bound* reasoning changes,
and it changes exactly where the audit predicted:

* deterministic and branching fields consume Unit 3's **directional** rules
  (`sentBndPol_imp_neg_left`, `sentBndPol_neg_imp_right`, `sentBndPol_neg_component_*`, …)
  rather than a same-class negation equivalence;
* every right-coordinate case is the left case conjugated by the class-exchanging
  `lyndonInsepAt_swap` (through the Unit-4a right twins), never a duplicated proof;
* the mixed `C0` cases are `lyndonInsepAt_shared_contradiction`: a sentence on one side whose
  negation is on the other lies in the flipped intersection class and is itself a separator;
* the equality fields are class-free, and the cross-coordinate equality/congruence transfers go
  through `lyndonInsepAt_insert_of_shared_constEq_entails`, whose swapped-class hypotheses the
  empty polarity sets of `constEq` discharge;
* `rel_congr` moves along `sentBndPol_relInst_congr`, i.e. the positive-only `iff` — an atomic
  instance is in the side class exactly when its symbol is in `P`;
* the constant rules reuse the unchanged support/freshness machinery verbatim.

This is the first Lyndon file to invoke the countable-completion kernel: `exists_henkinComplete`
and `exists_model_of_henkinComplete` are consumed exactly as the Craig development consumes them,
with no `MaximalConsistent` machinery — a fact the truth-lemma dependency-cone guard now checks
for `exists_lyndon_paired_model_neg`.

Root inseparability itself is **not** proved here; that (and interpolation) is Unit 5.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}}

variable {F : Set (Σ n, L.Functions n)} {P N : Set (Σ n, L.Relations n)}
  {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-! ## The remaining quantifier round-trip consumers, in signed form -/

/-- Replacing a hypothesis by a semantically equivalent one does not change inseparability (the
separator is untouched, so the polarity classes are irrelevant). -/
private theorem lyndonInsepAt_insert_congr {σ₁ σ₂ : L[[ℕ]].Sentenceω}
    (hequiv : ∀ (M : Type) [L[[ℕ]].Structure M] [Nonempty M],
      Sentenceω.Realize σ₁ M ↔ Sentenceω.Realize σ₂ M) :
    LyndonInsepAt F P N A (insert σ₁ Γ) Δ ↔ LyndonInsepAt F P N A (insert σ₂ Γ) Δ := by
  unfold LyndonInsepAt
  constructor <;> intro h ⟨σ, hbf, hbp, hbn, hsupp, hΓσ, hΔσ⟩ <;> apply h
  · exact ⟨σ, hbf, hbp, hbn, hsupp, (entails_insert_congr hequiv).mpr hΓσ, hΔσ⟩
  · exact ⟨σ, hbf, hbp, hbn, hsupp, (entails_insert_congr hequiv).mp hΓσ, hΔσ⟩

/-- **C7 consumer (existential)**, signed. -/
private theorem lyndonInsepAt_instConst_of_ex (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hcψ : c ∉ sentenceJConsts (L' := L) (J := ℕ) ψ)
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : LyndonInsepAt F P N A (insert ψ.ex Γ) Δ) :
    LyndonInsepAt F P N (insert c A) (insert (instConst c ψ) Γ) Δ := by
  have h' : LyndonInsepAt F P N A (insert (genEx c (instConst c ψ)) Γ) Δ :=
    (lyndonInsepAt_insert_congr (fun M _ _ => realize_genEx_instConst_iff_ex c ψ hcψ M)).mpr h
  exact lyndonInsepAt_witness_of_genEx c (instConst c ψ) hcΓ hcΔ h'

/-- **C7 consumer (negated universal)**, signed: `¬∀x ψ` is `∃x ¬ψ`, witnessed by `¬ψ(c)`. -/
private theorem lyndonInsepAt_not_instConst_of_not_all (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hcψ : c ∉ sentenceJConsts (L' := L) (J := ℕ) ψ.not)
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : LyndonInsepAt F P N A (insert (ψ.all).not Γ) Δ) :
    LyndonInsepAt F P N (insert c A) (insert (instConst c ψ.not) Γ) Δ := by
  have hequiv : ∀ (M : Type) [L[[ℕ]].Structure M] [Nonempty M],
      Sentenceω.Realize (ψ.all).not M ↔ Sentenceω.Realize (ψ.not).ex M := by
    intro M _ _
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_all,
      BoundedFormulaω.realize_ex, not_forall]
  have h' : LyndonInsepAt F P N A (insert (ψ.not).ex Γ) Δ :=
    (lyndonInsepAt_insert_congr (fun M _ _ => hequiv M)).mp h
  exact lyndonInsepAt_instConst_of_ex c ψ.not hcψ hcΓ hcΔ h'

/-- The right twin of the negated-universal `C7` consumer, again by conjugation. -/
private theorem lyndonInsepAt_not_instConst_of_not_all_right (c : ℕ)
    (ψ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hcψ : c ∉ sentenceJConsts (L' := L) (J := ℕ) ψ.not)
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : LyndonInsepAt F P N A Γ (insert (ψ.all).not Δ)) :
    LyndonInsepAt F P N (insert c A) Γ (insert (instConst c ψ.not) Δ) :=
  lyndonInsepAt_swap
    (lyndonInsepAt_not_instConst_of_not_all c ψ hcψ hcΔ hcΓ (lyndonInsepAt_swap h))

/-! ## The consistency property -/

private structure CountableConnectiveClosureFields
    (Family : Set L[[ℕ]].Sentenceω → Prop) : Prop where
  iInf : ∀ S, Family S → ∀ φs : ℕ → L[[ℕ]].Sentenceω,
    BoundedFormulaω.iInf φs ∈ S → ∀ k, Family (S ∪ {φs k})
  negIInf : ∀ S, Family S → ∀ φs : ℕ → L[[ℕ]].Sentenceω,
    (BoundedFormulaω.iInf φs).not ∈ S → ∃ k, Family (S ∪ {(φs k).not})
  iSup : ∀ S, Family S → ∀ φs : ℕ → L[[ℕ]].Sentenceω,
    BoundedFormulaω.iSup φs ∈ S → ∃ k, Family (S ∪ {φs k})
  negISup : ∀ S, Family S → ∀ φs : ℕ → L[[ℕ]].Sentenceω,
    (BoundedFormulaω.iSup φs).not ∈ S → ∀ k, Family (S ∪ {(φs k).not})

private structure AtomicClosureFields
    (Family : Set L[[ℕ]].Sentenceω → Prop) : Prop where
  refl : ∀ S, Family S → ∀ c, Family (S ∪ {constEq c c})
  symm : ∀ S, Family S → ∀ a b, constEq a b ∈ S → Family (S ∪ {constEq b a})
  trans : ∀ S, Family S → ∀ a b d,
    constEq a b ∈ S → constEq b d ∈ S → Family (S ∪ {constEq a d})
  rel : ∀ S, Family S → ∀ l (R : L.Relations l) (g : Fin l → ℕ) i b,
    relInst R g ∈ S → constEq (g i) b ∈ S →
      Family (S ∪ {relInst R (Function.update g i b)})

private structure QuantifierClosureFields
    (Family : Set L[[ℕ]].Sentenceω → Prop) : Prop where
  all : ∀ S, Family S → ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1,
    φ.all ∈ S → ∀ c, Family (S ∪ {instConst c φ})
  negAll : ∀ S, Family S → ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1,
    φ.all.not ∈ S → ∃ c, Family (S ∪ {(instConst c φ).not})

private theorem lyndonPaired_countableConnectiveClosureFields
    (F₁ : Set (Σ n, L.Functions n)) (P₁ N₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (P₂ N₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω) :
    CountableConnectiveClosureFields
      (LyndonPairedMem F₁ P₁ N₁ F₂ P₂ N₂ rL rR) := by
  refine { iInf := ?_, negIInf := ?_, iSup := ?_, negISup := ?_ }
  · intro S hS φs hmem k
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · refine lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (iInf_comp_mem k (hΓU hΓ)) (sentBndPol_component_iInf k (hΓS hΓ)) ?_
        (lyndonInsepAt_insert_of_entails
          (entails_of_mem_of_entails hΓ (iInf_entails_component φs k)) hA)
      exact support_insert_left
        ((sentenceJConsts_component_iInf φs k).trans (support_mem_left hΓ hsupp)) hsupp
    · refine lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (iInf_comp_mem k (hΔU hΔ)) (sentBndPol_component_iInf k (hΔS hΔ)) ?_
        (lyndonInsepAt_insert_right_of_entails
          (entails_of_mem_of_entails hΔ (iInf_entails_component φs k)) hA)
      exact support_insert_right
        ((sentenceJConsts_component_iInf φs k).trans (support_mem_right hΔ hsupp)) hsupp
  · intro S hS φs hmem
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · obtain ⟨k, hk⟩ := lyndonInsepAt_neg_iInf_component φs hΓ hA
      have hinfsupp :
          sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iInf φs) ⊆
            (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]
        exact support_mem_left hΓ hsupp
      have hns : sentenceJConsts (L' := L) (J := ℕ) (φs k).not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]
        exact (sentenceJConsts_component_iInf φs k).trans hinfsupp
      exact ⟨k, lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negiInf_comp_mem k (hΓU hΓ))
        (sentBndPol_neg_component_iInf k (hΓS hΓ))
        (support_insert_left hns hsupp) hk⟩
    · obtain ⟨k, hk⟩ :=
        lyndonInsepAt_neg_iInf_component φs hΔ (lyndonInsepAt_swap hA)
      have hinfsupp :
          sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iInf φs) ⊆
            (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]
        exact support_mem_right hΔ hsupp
      have hns : sentenceJConsts (L' := L) (J := ℕ) (φs k).not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]
        exact (sentenceJConsts_component_iInf φs k).trans hinfsupp
      exact ⟨k, lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negiInf_comp_mem k (hΔU hΔ))
        (sentBndPol_neg_component_iInf k (hΔS hΔ))
        (support_insert_right hns hsupp) (lyndonInsepAt_swap hk)⟩
  · intro S hS φs hmem
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · obtain ⟨k, hk⟩ := lyndonInsepAt_iSup_component φs hΓ hA
      refine ⟨k, lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (iSup_comp_mem k (hΓU hΓ)) (sentBndPol_component_iSup k (hΓS hΓ)) ?_ hk⟩
      exact support_insert_left
        ((sentenceJConsts_component_iSup φs k).trans (support_mem_left hΓ hsupp)) hsupp
    · obtain ⟨k, hk⟩ := lyndonInsepAt_iSup_component φs hΔ (lyndonInsepAt_swap hA)
      refine ⟨k, lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (iSup_comp_mem k (hΔU hΔ)) (sentBndPol_component_iSup k (hΔS hΔ)) ?_
        (lyndonInsepAt_swap hk)⟩
      exact support_insert_right
        ((sentenceJConsts_component_iSup φs k).trans (support_mem_right hΔ hsupp)) hsupp
  · intro S hS φs hmem k
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · have hsupsupp :
          sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iSup φs) ⊆
            (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]
        exact support_mem_left hΓ hsupp
      have hns : sentenceJConsts (L' := L) (J := ℕ) (φs k).not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]
        exact (sentenceJConsts_component_iSup φs k).trans hsupsupp
      exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negiSup_comp_mem k (hΓU hΓ))
        (sentBndPol_neg_component_iSup k (hΓS hΓ))
        (support_insert_left hns hsupp)
        (lyndonInsepAt_insert_of_entails
          (entails_of_mem_of_entails hΓ (neg_iSup_entails_neg_component φs k)) hA)
    · have hsupsupp :
          sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.iSup φs) ⊆
            (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]
        exact support_mem_right hΔ hsupp
      have hns : sentenceJConsts (L' := L) (J := ℕ) (φs k).not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]
        exact (sentenceJConsts_component_iSup φs k).trans hsupsupp
      exact lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negiSup_comp_mem k (hΔU hΔ))
        (sentBndPol_neg_component_iSup k (hΔS hΔ))
        (support_insert_right hns hsupp)
        (lyndonInsepAt_insert_right_of_entails
          (entails_of_mem_of_entails hΔ (neg_iSup_entails_neg_component φs k)) hA)

private theorem lyndonPaired_atomicClosureFields
    (F₁ : Set (Σ n, L.Functions n)) (P₁ N₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (P₂ N₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω) :
    AtomicClosureFields (LyndonPairedMem F₁ P₁ N₁ F₂ P₂ N₂ rL rR) := by
  refine { refl := ?_, symm := ?_, trans := ?_, rel := ?_ }
  · intro S hS c
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    have hccsupp :
        sentenceJConsts (L' := L) (J := ℕ) (constEq c c) ⊆
          (↑(insert c A) : Set ℕ) := by
      refine (sentenceJConsts_constEq_subset c c).trans ?_
      rw [Finset.coe_insert]
      exact Set.insert_subset_iff.mpr
        ⟨Set.mem_insert c _, Set.singleton_subset_iff.mpr (Set.mem_insert c _)⟩
    have hA' :
        LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) (insert c A)
          (insert (constEq c c) Γ) Δ := by
      by_cases hcA : c ∈ A
      · rw [Finset.insert_eq_self.mpr hcA]
        exact lyndonInsepAt_insert_of_entails (entails_constEq_refl c) hA
      · exact lyndonInsepAt_insert_of_entails (entails_constEq_refl c)
          (lyndonInsepAt_grow_fresh c
            (fresh_right c (fun h => hcA (Finset.mem_coe.mp h)) hsupp) hA)
    exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
      (eqRefl_mem c) (sentBndPol_constEq c c)
      (support_insert_left hccsupp
        (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hA'
  · intro S hS a b hmem
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    have hbasupp : sentenceJConsts (L' := L) (J := ℕ) (constEq b a) ⊆ (↑A : Set ℕ) := by
      rw [← sentenceJConsts_constEq_comm a b]
      exact support_mem hmem hsupp
    rcases hmem with hΓ | hΔ
    · exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (constEq_mem b a) (sentBndPol_constEq b a)
        (support_insert_left hbasupp hsupp)
        (lyndonInsepAt_insert_of_entails (entails_constEq_symm hΓ) hA)
    · exact lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (constEq_mem b a) (sentBndPol_constEq b a)
        (support_insert_right hbasupp hsupp)
        (lyndonInsepAt_insert_right_of_entails (entails_constEq_symm hΔ) hA)
  · intro S hS a b d hmem1 hmem2
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem1 hmem2
    have haA : a ∈ (↑A : Set ℕ) :=
      support_mem hmem1 hsupp (mem_sentenceJConsts_constEq_left a b)
    have hdA : d ∈ (↑A : Set ℕ) :=
      support_mem hmem2 hsupp (mem_sentenceJConsts_constEq_right b d)
    have hadsupp : sentenceJConsts (L' := L) (J := ℕ) (constEq a d) ⊆ (↑A : Set ℕ) :=
      (sentenceJConsts_constEq_subset a d).trans
        (Set.insert_subset_iff.mpr ⟨haA, Set.singleton_subset_iff.mpr hdA⟩)
    have habsupp : sentenceJConsts (L' := L) (J := ℕ) (constEq a b) ⊆ (↑A : Set ℕ) :=
      support_mem hmem1 hsupp
    have hbdsupp : sentenceJConsts (L' := L) (J := ℕ) (constEq b d) ⊆ (↑A : Set ℕ) :=
      support_mem hmem2 hsupp
    rcases hmem1 with h1Γ | h1Δ <;> rcases hmem2 with h2Γ | h2Δ
    · exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (constEq_mem a d) (sentBndPol_constEq a d)
        (support_insert_left hadsupp hsupp)
        (lyndonInsepAt_insert_of_entails (entails_constEq_trans h1Γ h2Γ) hA)
    · exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (constEq_mem a d) (sentBndPol_constEq a d)
        (support_insert_left hadsupp hsupp)
        (lyndonInsepAt_insert_of_shared_constEq_entails b d hbdsupp
          (Theoryω.entails_of_mem h2Δ)
          (entails_constEq_trans (Set.mem_insert_of_mem _ h1Γ) (Set.mem_insert _ _)) hA)
    · exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (constEq_mem a d) (sentBndPol_constEq a d)
        (support_insert_left hadsupp hsupp)
        (lyndonInsepAt_insert_of_shared_constEq_entails a b habsupp
          (Theoryω.entails_of_mem h1Δ)
          (entails_constEq_trans (Set.mem_insert _ _) (Set.mem_insert_of_mem _ h2Γ)) hA)
    · exact lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (constEq_mem a d) (sentBndPol_constEq a d)
        (support_insert_right hadsupp hsupp)
        (lyndonInsepAt_insert_right_of_entails (entails_constEq_trans h1Δ h2Δ) hA)
  · intro S hS l R g i b hmem1 hmem2
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem1 hmem2
    have hconstsupp :
        sentenceJConsts (L' := L) (J := ℕ) (constEq (g i) b) ⊆ (↑A : Set ℕ) :=
      support_mem hmem2 hsupp
    have hbA : b ∈ (↑A : Set ℕ) :=
      hconstsupp (mem_sentenceJConsts_constEq_right (g i) b)
    have hrelsupp : sentenceJConsts (L' := L) (J := ℕ) (relInst R g) ⊆ (↑A : Set ℕ) :=
      support_mem hmem1 hsupp
    have hupdsupp :
        sentenceJConsts (L' := L) (J := ℕ) (relInst R (Function.update g i b)) ⊆
          (↑A : Set ℕ) := by
      rw [sentenceJConsts_relInst_eq]
      intro k hk
      obtain ⟨j, rfl⟩ := hk
      by_cases hji : j = i
      · subst hji
        rw [Function.update_self]
        exact hbA
      · rw [Function.update_of_ne hji]
        exact hrelsupp (by rw [sentenceJConsts_relInst_eq]; exact ⟨j, rfl⟩)
    rcases hmem1 with h1Γ | h1Δ
    · rcases hmem2 with h2Γ | h2Δ
      · exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (relInst_mem R (Function.update g i b))
          (sentBndPol_relInst_congr R (Function.update g i b) (hΓS h1Γ))
          (support_insert_left hupdsupp hsupp)
          (lyndonInsepAt_insert_of_entails (entails_rel_congr R g i b h1Γ h2Γ) hA)
      · exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (relInst_mem R (Function.update g i b))
          (sentBndPol_relInst_congr R (Function.update g i b) (hΓS h1Γ))
          (support_insert_left hupdsupp hsupp)
          (lyndonInsepAt_insert_of_shared_constEq_entails (g i) b hconstsupp
            (Theoryω.entails_of_mem h2Δ)
            (entails_rel_congr R g i b (Set.mem_insert_of_mem _ h1Γ)
              (Set.mem_insert _ _)) hA)
    · rcases hmem2 with h2Γ | h2Δ
      · exact lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (relInst_mem R (Function.update g i b))
          (sentBndPol_relInst_congr R (Function.update g i b) (hΔS h1Δ))
          (support_insert_right hupdsupp hsupp)
          (lyndonInsepAt_insert_right_of_shared_constEq_entails (g i) b hconstsupp
            (Theoryω.entails_of_mem h2Γ)
            (entails_rel_congr R g i b (Set.mem_insert_of_mem _ h1Δ)
              (Set.mem_insert _ _)) hA)
      · exact lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (relInst_mem R (Function.update g i b))
          (sentBndPol_relInst_congr R (Function.update g i b) (hΔS h1Δ))
          (support_insert_right hupdsupp hsupp)
          (lyndonInsepAt_swap <| lyndonInsepAt_insert_of_entails
            (entails_rel_congr R g i b h1Δ h2Δ) (lyndonInsepAt_swap hA))

private theorem lyndonPaired_quantifierClosureFields
    (F₁ : Set (Σ n, L.Functions n)) (P₁ N₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (P₂ N₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω)
    (hrL : (sentenceJConsts (L' := L) (J := ℕ) rL).Finite)
    (hrR : (sentenceJConsts (L' := L) (J := ℕ) rR).Finite) :
    QuantifierClosureFields (LyndonPairedMem F₁ P₁ N₁ F₂ P₂ N₂ rL rR) := by
  refine { all := ?_, negAll := ?_ }
  · intro S hS φ hmem c
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · have hinstsupp : sentenceJConsts (L' := L) (J := ℕ) (instConst c φ) ⊆
          (↑(insert c A) : Set ℕ) := by
        refine (sentenceJConsts_instConst_subset c φ).trans ?_
        rw [Finset.coe_insert]
        exact Set.union_subset ((support_mem_left hΓ hsupp).trans (Set.subset_insert c _))
          (Set.singleton_subset_iff.mpr (Set.mem_insert c _))
      have hA' :
          LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) (insert c A)
            (insert (instConst c φ) Γ) Δ := by
        by_cases hcA : c ∈ A
        · rw [Finset.insert_eq_self.mpr hcA]
          exact lyndonInsepAt_insert_of_entails
            (entails_of_mem_of_entails hΓ (all_entails_instConst c φ)) hA
        · exact lyndonInsepAt_insert_of_entails
            (entails_of_mem_of_entails hΓ (all_entails_instConst c φ))
            (lyndonInsepAt_grow_fresh c
              (fresh_right c (fun h => hcA (Finset.mem_coe.mp h)) hsupp) hA)
      exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (all_inst_mem c (hΓU hΓ)) (sentBndPol_instConst c (hΓS hΓ))
        (support_insert_left hinstsupp
          (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hA'
    · have hinstsupp : sentenceJConsts (L' := L) (J := ℕ) (instConst c φ) ⊆
          (↑(insert c A) : Set ℕ) := by
        refine (sentenceJConsts_instConst_subset c φ).trans ?_
        rw [Finset.coe_insert]
        exact Set.union_subset ((support_mem_right hΔ hsupp).trans (Set.subset_insert c _))
          (Set.singleton_subset_iff.mpr (Set.mem_insert c _))
      have hA' :
          LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) (insert c A) Γ
            (insert (instConst c φ) Δ) := by
        by_cases hcA : c ∈ A
        · rw [Finset.insert_eq_self.mpr hcA]
          exact lyndonInsepAt_insert_right_of_entails
            (entails_of_mem_of_entails hΔ (all_entails_instConst c φ)) hA
        · exact lyndonInsepAt_insert_right_of_entails
            (entails_of_mem_of_entails hΔ (all_entails_instConst c φ))
            (lyndonInsepAt_grow_fresh c
              (fresh_right c (fun h => hcA (Finset.mem_coe.mp h)) hsupp) hA)
      exact lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (all_inst_mem c (hΔU hΔ)) (sentBndPol_instConst c (hΔS hΔ))
        (support_insert_right hinstsupp
          (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hA'
  · intro S hS φ hmem
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
      have hAins :
          LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) A
            (insert (BoundedFormulaω.all φ).not Γ) Δ := by
        rw [Set.insert_eq_self.mpr hΓ]
        exact hA
      have hins := lyndonInsepAt_not_instConst_of_not_all c φ
        (by rw [sentenceJConsts_not]; exact hcφ) (fresh_left c hcA hsupp)
        (fresh_right c hcA hsupp) hAins
      rw [instConst_not] at hins
      have hinstsupp : sentenceJConsts (L' := L) (J := ℕ) ((instConst c φ).not) ⊆
          (↑(insert c A) : Set ℕ) := by
        rw [sentenceJConsts_not]
        refine (sentenceJConsts_instConst_subset c φ).trans ?_
        rw [Finset.coe_insert]
        refine Set.union_subset ?_ (Set.singleton_subset_iff.mpr (Set.mem_insert c _))
        refine (?_ : sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.all φ) ⊆
          (↑A : Set ℕ)).trans (Set.subset_insert c _)
        have hx := support_mem_left hΓ hsupp
        rwa [sentenceJConsts_not] at hx
      exact ⟨c, lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negall_inst_mem c hmemU)
        (sentBndPol_not_iff.mpr
          (sentBndPol_instConst c (sentBndPol_not_iff.mp (hΓS hΓ))))
        (support_insert_left hinstsupp
          (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hins⟩
    · have hmemU : (BoundedFormulaω.all φ).not ∈ GenU rL rR := hΔU hΔ
      have hφfin : (sentenceJConsts (L' := L) (J := ℕ) φ).Finite := by
        have hx := genU_finite_support hrL hrR _ hmemU
        rwa [sentenceJConsts_not, sentenceJConsts_all] at hx
      obtain ⟨c, hc⟩ := (A.finite_toSet.union hφfin).exists_notMem
      simp only [Set.mem_union, not_or] at hc
      obtain ⟨hcA, hcφ⟩ := hc
      have hAins :
          LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) A Γ
            (insert (BoundedFormulaω.all φ).not Δ) := by
        rw [Set.insert_eq_self.mpr hΔ]
        exact hA
      have hins' := lyndonInsepAt_not_instConst_of_not_all_right c φ
        (by rw [sentenceJConsts_not]; exact hcφ) (fresh_left c hcA hsupp)
        (fresh_right c hcA hsupp) hAins
      rw [instConst_not] at hins'
      have hinstsupp : sentenceJConsts (L' := L) (J := ℕ) ((instConst c φ).not) ⊆
          (↑(insert c A) : Set ℕ) := by
        rw [sentenceJConsts_not]
        refine (sentenceJConsts_instConst_subset c φ).trans ?_
        rw [Finset.coe_insert]
        refine Set.union_subset ?_ (Set.singleton_subset_iff.mpr (Set.mem_insert c _))
        refine (?_ : sentenceJConsts (L' := L) (J := ℕ) (BoundedFormulaω.all φ) ⊆
          (↑A : Set ℕ)).trans (Set.subset_insert c _)
        have hx := support_mem_right hΔ hsupp
        rwa [sentenceJConsts_not] at hx
      exact ⟨c, lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negall_inst_mem c hmemU)
        (sentBndPol_not_iff.mpr
          (sentBndPol_instConst c (sentBndPol_not_iff.mp (hΔS hΔ))))
        (support_insert_right hinstsupp
          (hsupp.trans (Finset.coe_subset.mpr (Finset.subset_insert c A)))) hins'⟩

private theorem lyndonPaired_sets_subset_generatedUniverse
    (F₁ : Set (Σ n, L.Functions n)) (P₁ N₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (P₂ N₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω) (S : Set L[[ℕ]].Sentenceω)
    (hS : LyndonPairedMem F₁ P₁ N₁ F₂ P₂ N₂ rL rR S) : S ⊆ GenU rL rR := by
  obtain ⟨Γ, Δ, _, _, _, hΓU, hΔU, _, _, _, hSeq, _⟩ := hS
  rw [hSeq]
  exact Set.union_subset hΓU hΔU

private def lyndonPairedConsistencyProperty (F₁ : Set (Σ n, L.Functions n))
    (P₁ N₁ : Set (Σ n, L.Relations n)) (F₂ : Set (Σ n, L.Functions n))
    (P₂ N₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω)
    (hrL : (sentenceJConsts (L' := L) (J := ℕ) rL).Finite)
    (hrR : (sentenceJConsts (L' := L) (J := ℕ) rR).Finite) :
    ConsistencyPropertyEqOn (GenU rL rR) where
  sets := {S | LyndonPairedMem F₁ P₁ N₁ F₂ P₂ N₂ rL rR S}
  subset_U := lyndonPaired_sets_subset_generatedUniverse F₁ P₁ N₁ F₂ P₂ N₂ rL rR
  C0_no_falsum := fun S hS hmem => by
    obtain ⟨Γ, Δ, A, _, _, _, _, _, _, _, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with h | h
    · exact lyndonInsepAt_falsum_absurd h hA
    · exact lyndonInsepAt_falsum_absurd h (lyndonInsepAt_swap hA)
  C0_no_contradiction := fun S hS φ => by
    obtain ⟨Γ, Δ, A, _, _, _, _, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rintro ⟨hφ, hφn⟩
    rw [hSeq] at hφ hφn
    rcases hφ with hφΓ | hφΔ
    · rcases hφn with hφnΓ | hφnΔ
      · exact lyndonInsepAt_contradiction_absurd hφΓ hφnΓ hA
      · -- mixed C0: `φ` on the left, `φ.not` on the right, so `φ` is itself a separator
        exact lyndonInsepAt_shared_contradiction (hΓS hφΓ) (hΔS hφnΔ)
          (support_mem_left hφΓ hsupp) (Theoryω.entails_of_mem hφΓ)
          (Theoryω.entails_of_mem hφnΔ) hA
    · rcases hφn with hφnΓ | hφnΔ
      · -- mixed C0, mirrored: `φ` on the right, `φ.not` on the left.  The swap exchanges the
        -- polarity components, and the two intersections commute into the mirrored class.
        have hswap : LyndonInsepAt (F₂ ∩ F₁) (P₂ ∩ N₁) (N₂ ∩ P₁) A Δ Γ := by
          rw [Set.inter_comm F₂ F₁, Set.inter_comm P₂ N₁, Set.inter_comm N₂ P₁]
          exact lyndonInsepAt_swap hA
        exact lyndonInsepAt_shared_contradiction (hΔS hφΔ) (hΓS hφnΓ)
          (support_mem_right hφΔ hsupp) (Theoryω.entails_of_mem hφΔ)
          (Theoryω.entails_of_mem hφnΓ) hswap
      · exact lyndonInsepAt_contradiction_absurd hφΔ hφnΔ (lyndonInsepAt_swap hA)
  C1_imp := fun S hS φ ψ hmem => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · rcases lyndonInsepAt_imp_dichotomy hΓ hA with h | h
      · have hns : sentenceJConsts (L' := L) (J := ℕ) φ.not ⊆ (↑A : Set ℕ) := by
          rw [sentenceJConsts_not]
          exact (sentenceJConsts_imp_left φ ψ).trans (support_mem_left hΓ hsupp)
        exact Or.inl (lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (imp_negleft_mem (hΓU hΓ)) (sentBndPol_imp_neg_left (hΓS hΓ))
          (support_insert_left hns hsupp) h)
      · exact Or.inr (lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (imp_right_mem (hΓU hΓ)) (sentBndPol_imp_right (hΓS hΓ))
          (support_insert_left ((sentenceJConsts_imp_right φ ψ).trans (support_mem_left hΓ hsupp))
            hsupp) h)
    · rcases lyndonInsepAt_imp_dichotomy hΔ (lyndonInsepAt_swap hA) with h | h
      · have hns : sentenceJConsts (L' := L) (J := ℕ) φ.not ⊆ (↑A : Set ℕ) := by
          rw [sentenceJConsts_not]
          exact (sentenceJConsts_imp_left φ ψ).trans (support_mem_right hΔ hsupp)
        exact Or.inl (lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (imp_negleft_mem (hΔU hΔ)) (sentBndPol_imp_neg_left (hΔS hΔ))
          (support_insert_right hns hsupp) (lyndonInsepAt_swap h))
      · exact Or.inr (lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (imp_right_mem (hΔU hΔ)) (sentBndPol_imp_right (hΔS hΔ))
          (support_insert_right ((sentenceJConsts_imp_right φ ψ).trans (support_mem_right hΔ hsupp))
            hsupp) (lyndonInsepAt_swap h))
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
      exact ⟨lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (negimp_left_mem (hΓU hΓ)) (sentBndPol_neg_imp_left (hΓS hΓ))
          (support_insert_left hφsupp hsupp)
          (lyndonInsepAt_insert_of_entails
            (entails_of_mem_of_entails hΓ (negimp_entails_left φ ψ)) hA),
        lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (negimp_right_mem (hΓU hΓ))
          (sentBndPol_neg_imp_right (hΓS hΓ))
          (support_insert_left hψnsupp hsupp)
          (lyndonInsepAt_insert_of_entails
            (entails_of_mem_of_entails hΓ (negimp_entails_right φ ψ)) hA)⟩
    · have himpsupp : sentenceJConsts (L' := L) (J := ℕ) (φ.imp ψ) ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not]; exact support_mem_right hΔ hsupp
      have hφsupp : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) :=
        (sentenceJConsts_imp_left φ ψ).trans himpsupp
      have hψnsupp : sentenceJConsts (L' := L) (J := ℕ) ψ.not ⊆ (↑A : Set ℕ) := by
        rw [sentenceJConsts_not]; exact (sentenceJConsts_imp_right φ ψ).trans himpsupp
      exact ⟨lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
          (negimp_left_mem (hΔU hΔ)) (sentBndPol_neg_imp_left (hΔS hΔ))
          (support_insert_right hφsupp hsupp)
          (lyndonInsepAt_insert_right_of_entails
            (entails_of_mem_of_entails hΔ (negimp_entails_left φ ψ)) hA),
        lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS (negimp_right_mem (hΔU hΔ))
          (sentBndPol_neg_imp_right (hΔS hΔ))
          (support_insert_right hψnsupp hsupp)
          (lyndonInsepAt_insert_right_of_entails
            (entails_of_mem_of_entails hΔ (negimp_entails_right φ ψ)) hA)⟩
  C2_not_not := fun S hS φ hmem => by
    obtain ⟨Γ, Δ, A, hΓfin, hΔfin, hΓU, hΔU, hΓS, hΔS, hsupp, hSeq, hA⟩ := hS
    rw [hSeq] at hmem
    rcases hmem with hΓ | hΔ
    · have hφsupp : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not, ← sentenceJConsts_not]; exact support_mem_left hΓ hsupp
      exact lyndonPaired_insert_left hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negimp_left_mem (φ := φ) (ψ := (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω)) (hΓU hΓ))
        (sentBndPol_not_not (hΓS hΓ)) (support_insert_left hφsupp hsupp)
        (lyndonInsepAt_insert_of_entails (entails_of_mem_of_entails hΓ (not_not_entails φ)) hA)
    · have hφsupp : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ) := by
        rw [← sentenceJConsts_not, ← sentenceJConsts_not]; exact support_mem_right hΔ hsupp
      exact lyndonPaired_insert_right hSeq hΓfin hΔfin hΓU hΔU hΓS hΔS
        (negimp_left_mem (φ := φ) (ψ := (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω)) (hΔU hΔ))
        (sentBndPol_not_not (hΔS hΔ)) (support_insert_right hφsupp hsupp)
        (lyndonInsepAt_insert_right_of_entails
          (entails_of_mem_of_entails hΔ (not_not_entails φ)) hA)
  C3_iInf :=
    (lyndonPaired_countableConnectiveClosureFields
      F₁ P₁ N₁ F₂ P₂ N₂ rL rR).iInf
  C3_neg_iInf :=
    (lyndonPaired_countableConnectiveClosureFields
      F₁ P₁ N₁ F₂ P₂ N₂ rL rR).negIInf
  C4_iSup :=
    (lyndonPaired_countableConnectiveClosureFields
      F₁ P₁ N₁ F₂ P₂ N₂ rL rR).iSup
  C4_neg_iSup :=
    (lyndonPaired_countableConnectiveClosureFields
      F₁ P₁ N₁ F₂ P₂ N₂ rL rR).negISup
  eq_refl :=
    (lyndonPaired_atomicClosureFields F₁ P₁ N₁ F₂ P₂ N₂ rL rR).refl
  eq_symm :=
    (lyndonPaired_atomicClosureFields F₁ P₁ N₁ F₂ P₂ N₂ rL rR).symm
  eq_trans :=
    (lyndonPaired_atomicClosureFields F₁ P₁ N₁ F₂ P₂ N₂ rL rR).trans
  rel_congr :=
    (lyndonPaired_atomicClosureFields F₁ P₁ N₁ F₂ P₂ N₂ rL rR).rel
  all_inst :=
    (lyndonPaired_quantifierClosureFields
      F₁ P₁ N₁ F₂ P₂ N₂ rL rR hrL hrR).all
  neg_all_witness :=
    (lyndonPaired_quantifierClosureFields
      F₁ P₁ N₁ F₂ P₂ N₂ rL rR hrL hrR).negAll
/-! ## The paired model endpoint -/

/-- **Paired model existence, polarity-refined.** From a root pair side-typed at the two polarity
classes and inseparable at the flipped intersection class, the fair enumeration produces a
Henkin-complete set containing both roots, whose quotient term model realizes them. -/
private theorem exists_lyndon_paired_model [L.IsRelational] [Countable (Σ l, L.Relations l)]
    (F₁ : Set (Σ n, L.Functions n)) (P₁ N₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (P₂ N₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω)
    (hrL : (sentenceJConsts (L' := L) (J := ℕ) rL).Finite)
    (hrR : (sentenceJConsts (L' := L) (J := ℕ) rR).Finite)
    (hrLsent : rL ∈ SentBndPol F₁ P₁ N₁) (hrRsent : rR ∈ SentBndPol F₂ P₂ N₂)
    (A₀ : Finset ℕ)
    (hsupp : sentenceJConsts (L' := L) (J := ℕ) rL ∪ sentenceJConsts (L' := L) (J := ℕ) rR
      ⊆ (↑A₀ : Set ℕ))
    (hroot : LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) A₀ {rL} {rR}) :
    ∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M),
      Sentenceω.Realize rL M ∧ Sentenceω.Realize rR M := by
  have : Countable ↥(GenU (L := L) rL rR) := genU_countable.to_subtype
  have hmem : LyndonPairedMem F₁ P₁ N₁ F₂ P₂ N₂ rL rR ({rL} ∪ {rR}) := by
    refine ⟨{rL}, {rR}, A₀, Set.finite_singleton _, Set.finite_singleton _,
      Set.singleton_subset_iff.mpr root₁_mem, Set.singleton_subset_iff.mpr root₂_mem,
      Set.singleton_subset_iff.mpr hrLsent, Set.singleton_subset_iff.mpr hrRsent, ?_, rfl, hroot⟩
    rw [Set.biUnion_singleton, Set.biUnion_singleton]
    exact hsupp
  obtain ⟨Sstar, hsub, _, hsc⟩ := exists_henkinComplete
    (P := lyndonPairedConsistencyProperty F₁ P₁ N₁ F₂ P₂ N₂ rL rR hrL hrR) ⟨{rL} ∪ {rR}, hmem⟩
  obtain ⟨M, instM, neM, hpos, _⟩ := exists_model_of_henkinComplete hsc
  exact ⟨M, instM, neM, hpos rL (hsub (Set.mem_union_left _ rfl)),
    hpos rR (hsub (Set.mem_union_right _ rfl))⟩

/-- **The Unit-5 consumer endpoint**: instantiating the right root at `r₂.not` gives one model
realizing the left root and **refuting** the (un-negated) right root.  Root inseparability is a
hypothesis here; establishing it from a failed interpolant is Unit 5's business. -/
theorem exists_lyndon_paired_model_neg [L.IsRelational] [Countable (Σ l, L.Relations l)]
    (F₁ : Set (Σ n, L.Functions n)) (P₁ N₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (P₂ N₂ : Set (Σ n, L.Relations n))
    (r₁ r₂ : L[[ℕ]].Sentenceω)
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite)
    (hr₁sent : r₁ ∈ SentBndPol F₁ P₁ N₁) (hr₂sent : r₂.not ∈ SentBndPol F₂ P₂ N₂)
    (A₀ : Finset ℕ)
    (hsupp : sentenceJConsts (L' := L) (J := ℕ) r₁ ∪ sentenceJConsts (L' := L) (J := ℕ) r₂.not
      ⊆ (↑A₀ : Set ℕ))
    (hroot : LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) A₀ {r₁} {r₂.not}) :
    ∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M),
      Sentenceω.Realize r₁ M ∧ ¬ Sentenceω.Realize r₂ M := by
  obtain ⟨M, instM, neM, hr1, hr2not⟩ := exists_lyndon_paired_model F₁ P₁ N₁ F₂ P₂ N₂ r₁ r₂.not
    hr₁ (by rw [sentenceJConsts_not]; exact hr₂) hr₁sent hr₂sent A₀ hsupp hroot
  refine ⟨M, instM, neM, hr1, ?_⟩
  simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not] at hr2not
  exact hr2not

end FirstOrder.Language
