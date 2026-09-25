/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueSubsetBij

/-!
# Subset sums split across a single cut

A weight that vanishes off the pairing-closed subsets sums the same
over all subsets of `W` as over the lifts of the subsets of the glued
fragment.  At a closed cut the lifts are indexed by a `Bool` — whether
the cut edge is taken — and at an open cut there is one lift per glued
subset.

This is the reindexing half of a one-cut descent: it says that summing
over `W`'s subsets *is* summing over the glued fragment's subsets and
the cut's own data, with nothing left over.  Both halves are the round
trips of `GlueSubsetBij`: `dropSubset` recovers the glued subset,
`liftSubsetClosed`/`liftSubsetOpen` recover the original, and a
pairing-closed subset is always a lift.
-/

@[expose] public section

namespace RS



namespace Fragment

variable {α : Type} {W : Fragment α} {i j : α}

/-! ### The cut's two ends -/

/-- The extension takes the prescribed value at the first cut
label. -/
theorem extendPair_left {k ℓ : ℕ} {α : Type} (i j : α)
    (st : GenBoundaryState k ℓ (SurvivingLabel α i j))
    (c c' : Fin k ⊕ Fin (2 * ℓ)) :
    GenBoundaryState.extendPair i j st c c' i = c := by
  classical
  unfold GenBoundaryState.extendPair
  rw [dite_eq_left rfl]

/-- And at the second, when the two are distinct. -/
theorem extendPair_right {k ℓ : ℕ} {α : Type} {i j : α}
    (hij : i ≠ j)
    (st : GenBoundaryState k ℓ (SurvivingLabel α i j))
    (c c' : Fin k ⊕ Fin (2 * ℓ)) :
    GenBoundaryState.extendPair i j st c c' j = c' := by
  classical
  unfold GenBoundaryState.extendPair
  rw [dite_eq_right (Ne.symm hij), dite_eq_left rfl]

/-- And the restriction elsewhere. -/
theorem extendPair_surviving {k ℓ : ℕ} {α : Type} (i j : α)
    (st : GenBoundaryState k ℓ (SurvivingLabel α i j))
    (c c' : Fin k ⊕ Fin (2 * ℓ)) (x : SurvivingLabel α i j) :
    GenBoundaryState.extendPair i j st c c' x.val = st x := by
  classical
  unfold GenBoundaryState.extendPair
  rw [dite_eq_right x.prop.1, dite_eq_right x.prop.2]

/-! ### The closed cut -/

/-- At a closed cut the two lifts of distinct glued subsets are
distinct, and a lift determines which of the two it is. -/
theorem liftSubsetClosed_injective (hij : i ≠ j) :
    Function.Injective
      (fun p : Finset (SurvivingFlag W i j) × Bool =>
        liftSubsetClosed p.1 p.2) := by
  rintro ⟨s₁, b₁⟩ ⟨s₂, b₂⟩ hst
  have hst' : liftSubsetClosed s₁ b₁ = liftSubsetClosed s₂ b₂ := hst
  have hs : s₁ = s₂ := by
    have h1 := dropSubset_liftSubsetClosed (W := W) (i := i) (j := j)
      s₁ b₁
    have h2 := dropSubset_liftSubsetClosed (W := W) (i := i) (j := j)
      s₂ b₂
    rw [← h1, ← h2, hst']
  have hb : b₁ = b₂ := by
    have h1 := boundaryFlagI_mem_liftClosed_iff (W := W) (i := i)
      (j := j) hij s₁ b₁
    have h2 := boundaryFlagI_mem_liftClosed_iff (W := W) (i := i)
      (j := j) hij s₂ b₂
    rw [hst'] at h1
    simpa using h1.symm.trans h2
  exact Prod.ext hs hb

open Finset in
/-- **The subset sum splits at a closed cut.**  A weight vanishing off
the pairing-closed subsets sums over all subsets of `W` exactly as it
sums over the glued subsets and the two lifts. -/
theorem sum_split_closed (hij : i ≠ j)
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (X : Finset W.Flag → ℂ)
    (hz : ∀ sb : Finset W.Flag,
      ¬ (∀ f ∈ sb, W.pairing f ∈ sb) → X sb = 0) :
    (∑ sb : Finset W.Flag, X sb)
      = ∑ s' : Finset (SurvivingFlag W i j), ∑ b : Bool,
          X (liftSubsetClosed s' b) := by
  classical
  have himg : ∀ sb ∈ (univ : Finset (Finset W.Flag)),
      sb ∉ (univ : Finset (Finset (SurvivingFlag W i j) × Bool)).image
        (fun p => liftSubsetClosed p.1 p.2) → X sb = 0 := by
    intro sb _ hnot
    refine hz sb (fun hcl => hnot ?_)
    exact mem_image.mpr
      ⟨(W.dropSubset i j sb, decide (W.boundaryFlag i ∈ sb)),
        mem_univ _, liftSubsetClosed_dropSubset hij hclosed sb hcl⟩
  calc (∑ sb : Finset W.Flag, X sb)
      = ∑ sb ∈ (univ : Finset (Finset (SurvivingFlag W i j) × Bool)).image
          (fun p => liftSubsetClosed p.1 p.2), X sb :=
        (Finset.sum_subset (Finset.subset_univ _) himg).symm
    _ = ∑ p : Finset (SurvivingFlag W i j) × Bool,
          X (liftSubsetClosed p.1 p.2) :=
        Finset.sum_image
          (fun x _ y _ hxy => liftSubsetClosed_injective hij hxy)
    _ = ∑ s' : Finset (SurvivingFlag W i j), ∑ b : Bool,
          X (liftSubsetClosed s' b) := Fintype.sum_prod_type _

/-! ### The open cut -/

/-- At an open cut distinct glued subsets have distinct lifts. -/
theorem liftSubsetOpen_injective
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    Function.Injective
      (fun s' : Finset (SurvivingFlag W i j) =>
        liftSubsetOpen hopen s') := by
  intro s₁ s₂ hst
  have hst' : liftSubsetOpen hopen s₁ = liftSubsetOpen hopen s₂ :=
    hst
  have h1 := dropSubset_liftSubsetOpen (W := W) (i := i) (j := j)
    hopen s₁
  have h2 := dropSubset_liftSubsetOpen (W := W) (i := i) (j := j)
    hopen s₂
  rw [← h1, ← h2, hst']

open Finset in
/-- **The subset sum splits at an open cut.** -/
theorem sum_split_open (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (X : Finset W.Flag → ℂ)
    (hz : ∀ sb : Finset W.Flag,
      ¬ (∀ f ∈ sb, W.pairing f ∈ sb) → X sb = 0) :
    (∑ sb : Finset W.Flag, X sb)
      = ∑ s' : Finset (SurvivingFlag W i j),
          X (liftSubsetOpen hopen s') := by
  classical
  have himg : ∀ sb ∈ (univ : Finset (Finset W.Flag)),
      sb ∉ (univ : Finset (Finset (SurvivingFlag W i j))).image
        (fun s' => liftSubsetOpen hopen s') → X sb = 0 := by
    intro sb _ hnot
    refine hz sb (fun hcl => hnot ?_)
    exact mem_image.mpr ⟨W.dropSubset i j sb, mem_univ _,
      liftSubsetOpen_dropSubset hij hopen sb hcl⟩
  calc (∑ sb : Finset W.Flag, X sb)
      = ∑ sb ∈ (univ : Finset (Finset (SurvivingFlag W i j))).image
          (fun s' => liftSubsetOpen hopen s'), X sb :=
        (Finset.sum_subset (Finset.subset_univ _) himg).symm
    _ = ∑ s' : Finset (SurvivingFlag W i j),
          X (liftSubsetOpen hopen s') :=
        Finset.sum_image
          (fun x _ y _ hxy => liftSubsetOpen_injective hopen hxy)

end Fragment

end RS
