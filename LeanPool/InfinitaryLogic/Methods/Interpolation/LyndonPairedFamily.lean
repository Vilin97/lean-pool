/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.LyndonClosures
import LeanPool.InfinitaryLogic.Methods.Interpolation.PairedInsepFamily
/-!
# The polarity-refined paired family and its cross gates (issue #14, Unit 4a)

The first genuinely *paired* layer of the Lyndon refinement.  A family member is a
support-budgeted, `GenU`-bounded, **side-typed** pair carrying the refined inseparability at the
flipped intersection class:

```
Γ ⊆ SentBndPol F₁ P₁ N₁        Δ ⊆ SentBndPol F₂ P₂ N₂
LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) A Γ Δ
```

The flip on the `Δ` coordinate is the audit's §D4a orientation, and it is what makes the mixed
`C0` gate go through: a sentence `φ` occurring on the left with `φ.not` on the right satisfies

```
Pos φ ⊆ P₁  and  Pos φ ⊆ N₂          Neg φ ⊆ N₁  and  Neg φ ⊆ P₂
```

— the first pair because `φ ∈ SentBndPol F₁ P₁ N₁`, the second because `φ.not ∈ SentBndPol F₂ P₂ N₂`
*exchanges* the components (`sentBndPol_not_iff`).  So `φ` lies in the maintained separator class
and is itself a separator: the configuration cannot occur.  That calculation is
`sentBndPol_flip_inter`, stated on its own so the orientation is checkable in isolation.

**Right-coordinate gates are never duplicated**: each is the left gate conjugated by
`lyndonInsepAt_swap`, which exchanges `(P, N)`.  The unsigned support/freshness bookkeeping
(`support_mem_*`, `support_insert_*`, `fresh_*`) is reused verbatim from the Craig engine — it
carries no polarity content.

Unit 4b adds the sixteen consistency-property fields, the Henkin completion, and the model
endpoint.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}}

/-! ## The mixed-`C0` class calculation -/

variable {F₁ F₂ : Set (Σ n, L.Functions n)} {P₁ N₁ P₂ N₂ : Set (Σ n, L.Relations n)}

/-- **The flipped intersection calculation** (mixed `C0`, audit §D4a).  A sentence bounded on the
left, whose *negation* is bounded on the right, lies in the maintained separator class:

* `Pos φ ⊆ P₁` (left bound) and `Pos φ ⊆ N₂` (right bound, after the negation exchange);
* `Neg φ ⊆ N₁` (left bound) and `Neg φ ⊆ P₂` (right bound, after the exchange).
-/
private theorem sentBndPol_flip_inter {φ : L[[ℕ]].Sentenceω}
    (h₁ : φ ∈ SentBndPol F₁ P₁ N₁) (h₂ : φ.not ∈ SentBndPol F₂ P₂ N₂) :
    φ ∈ SentBndPol (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) := by
  rw [sentBndPol_not_iff] at h₂
  exact ⟨Set.subset_inter h₁.1 h₂.1, Set.subset_inter h₁.2.1 h₂.2.1,
    Set.subset_inter h₁.2.2 h₂.2.2⟩

variable {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- **Mixed `C0`**: a sentence entailed on the left whose negation is entailed on the right *is* a
separator in the flipped intersection class, so it cannot occur under inseparability. -/
theorem lyndonInsepAt_shared_contradiction {φ : L[[ℕ]].Sentenceω}
    (hφ₁ : φ ∈ SentBndPol F₁ P₁ N₁) (hφ₂ : φ.not ∈ SentBndPol F₂ P₂ N₂)
    (hφA : sentenceJConsts (L' := L) (J := ℕ) φ ⊆ (↑A : Set ℕ))
    (hΓφ : Theoryω.Entails Γ φ) (hΔφ : Theoryω.Entails Δ φ.not)
    (h : LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) A Γ Δ) : False :=
  have hcls := sentBndPol_flip_inter hφ₁ hφ₂
  h ⟨φ, hcls.1, hcls.2.1, hcls.2.2, hφA, hΓφ, hΔφ⟩

/-! ## Right-coordinate gates, by conjugation with `lyndonInsepAt_swap` -/

variable {F : Set (Σ n, L.Functions n)} {P N : Set (Σ n, L.Relations n)}

/-- Grow the `Δ`-coordinate by an entailed sentence — the right twin of
`lyndonInsepAt_insert_of_entails`, obtained purely by conjugation with the class-exchanging
swap. -/
theorem lyndonInsepAt_insert_right_of_entails {φ : L[[ℕ]].Sentenceω}
    (hcons : Theoryω.Entails Δ φ) (h : LyndonInsepAt F P N A Γ Δ) :
    LyndonInsepAt F P N A Γ (insert φ Δ) :=
  lyndonInsepAt_swap (lyndonInsepAt_insert_of_entails hcons (lyndonInsepAt_swap h))

/-- The right twin of the equality-transfer gate: a shared constant equality entailed by `Γ`
transfers a consequence into the `Δ` coordinate.  Again pure conjugation — the `(P, N)` exchange
happens twice and cancels. -/
theorem lyndonInsepAt_insert_right_of_shared_constEq_entails {φ : L[[ℕ]].Sentenceω} (a b : ℕ)
    (hσA : sentenceJConsts (L' := L) (J := ℕ) (constEq (L := L) a b) ⊆ (↑A : Set ℕ))
    (hΓσ : Theoryω.Entails Γ (constEq (L := L) a b))
    (hcons : Theoryω.Entails (insert (constEq (L := L) a b) Δ) φ)
    (h : LyndonInsepAt F P N A Γ Δ) : LyndonInsepAt F P N A Γ (insert φ Δ) :=
  lyndonInsepAt_swap
    (lyndonInsepAt_insert_of_shared_constEq_entails a b hσA hΓσ hcons (lyndonInsepAt_swap h))











/-! ## The paired family -/

/-- **A polarity-refined paired family member**: a symmetrically support-budgeted, `GenU`-bounded,
side-typed pair `(Γ, Δ)`, inseparable at the **flipped** intersection class
`(F₁ ∩ F₂, P₁ ∩ N₂, N₁ ∩ P₂)`. -/
def LyndonPairedMem (F₁ : Set (Σ n, L.Functions n)) (P₁ N₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (P₂ N₂ : Set (Σ n, L.Relations n))
    (rL rR : L[[ℕ]].Sentenceω) (S : Set L[[ℕ]].Sentenceω) : Prop :=
  ∃ (Γ Δ : Set L[[ℕ]].Sentenceω) (A : Finset ℕ),
    Γ.Finite ∧ Δ.Finite ∧ Γ ⊆ GenU rL rR ∧ Δ ⊆ GenU rL rR ∧
    Γ ⊆ SentBndPol F₁ P₁ N₁ ∧ Δ ⊆ SentBndPol F₂ P₂ N₂ ∧
    ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
     (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ) ⊆ (↑A : Set ℕ)) ∧
    S = Γ ∪ Δ ∧ LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) A Γ Δ

variable {rL rR : L[[ℕ]].Sentenceω}



/-! ### The two coordinate-growth constructors -/

/-- Add `φ` to the `Γ`-coordinate of a family member. -/
theorem lyndonPaired_insert_left {S Γ Δ : Set L[[ℕ]].Sentenceω} {A : Finset ℕ}
    {φ : L[[ℕ]].Sentenceω} (hSeq : S = Γ ∪ Δ)
    (hΓfin : Γ.Finite) (hΔfin : Δ.Finite)
    (hΓU : Γ ⊆ GenU rL rR) (hΔU : Δ ⊆ GenU rL rR)
    (hΓS : Γ ⊆ SentBndPol F₁ P₁ N₁) (hΔS : Δ ⊆ SentBndPol F₂ P₂ N₂)
    (hφU : φ ∈ GenU rL rR) (hφS : φ ∈ SentBndPol F₁ P₁ N₁)
    (hsupp : ((⋃ γ ∈ insert φ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ))
    (hA : LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) A (insert φ Γ) Δ) :
    LyndonPairedMem F₁ P₁ N₁ F₂ P₂ N₂ rL rR (S ∪ {φ}) := by
  rw [hSeq, Set.union_singleton, ← Set.insert_union]
  exact ⟨insert φ Γ, Δ, A, hΓfin.insert φ, hΔfin,
    Set.insert_subset_iff.mpr ⟨hφU, hΓU⟩, hΔU,
    Set.insert_subset_iff.mpr ⟨hφS, hΓS⟩, hΔS, hsupp, rfl, hA⟩

/-- Add `φ` to the `Δ`-coordinate of a family member. -/
theorem lyndonPaired_insert_right {S Γ Δ : Set L[[ℕ]].Sentenceω} {A : Finset ℕ}
    {φ : L[[ℕ]].Sentenceω} (hSeq : S = Γ ∪ Δ)
    (hΓfin : Γ.Finite) (hΔfin : Δ.Finite)
    (hΓU : Γ ⊆ GenU rL rR) (hΔU : Δ ⊆ GenU rL rR)
    (hΓS : Γ ⊆ SentBndPol F₁ P₁ N₁) (hΔS : Δ ⊆ SentBndPol F₂ P₂ N₂)
    (hφU : φ ∈ GenU rL rR) (hφS : φ ∈ SentBndPol F₂ P₂ N₂)
    (hsupp : ((⋃ γ ∈ Γ, sentenceJConsts (L' := L) (J := ℕ) γ) ∪
      (⋃ δ ∈ insert φ Δ, sentenceJConsts (L' := L) (J := ℕ) δ)) ⊆ (↑A : Set ℕ))
    (hA : LyndonInsepAt (F₁ ∩ F₂) (P₁ ∩ N₂) (N₁ ∩ P₂) A Γ (insert φ Δ)) :
    LyndonPairedMem F₁ P₁ N₁ F₂ P₂ N₂ rL rR (S ∪ {φ}) := by
  rw [hSeq, Set.union_singleton, ← Set.union_insert]
  exact ⟨Γ, insert φ Δ, A, hΓfin, hΔfin.insert φ, hΓU,
    Set.insert_subset_iff.mpr ⟨hφU, hΔU⟩, hΓS,
    Set.insert_subset_iff.mpr ⟨hφS, hΔS⟩, hsupp, rfl, hA⟩

end FirstOrder.Language
