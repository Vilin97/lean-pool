/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexVanish

/-!
# The fibre bijection

Closed-pattern fibres are pure; their sums reindex over the
colouring data through the diagonal parametrization.
-/

namespace RS

open CategoryTheory Finset


variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- Closed patterns force purity. -/
theorem pairPure_of_pattern_closed (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (s : Finset W.Flag)
    (hfibre : colourFlags W c = s)
    (hclosed : ∀ g ∈ s, W.pairing g ∈ s) :
    PairPure c := by
  intro i
  have hmem_iff : ∀ t : Fin (edgeCount W + edgeCount W),
      ((starFlagEnum W).symm t ∈ s) ↔
      (c t).isRight = true := by
    intro t
    rw [← hfibre, mem_colourFlags_iff,
      _root_.Equiv.apply_symm_apply]
  by_cases h1 : (c (Fin.castAdd (edgeCount W) i)).isRight =
      true
  · rw [h1]
    have hmem := (hmem_iff _).mpr h1
    have hmem2 := hclosed _ hmem
    rw [pairing_starFlagEnum_symm W i] at hmem2
    exact ((hmem_iff _).mp hmem2).symm
  · rw [Bool.not_eq_true] at h1
    rw [h1]
    by_cases h2 : (c (Fin.natAdd (edgeCount W)
        i)).isRight = true
    · exfalso
      have hmem := (hmem_iff _).mpr h2
      have hmem2 := hclosed _ hmem
      rw [show W.pairing ((starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) i)) =
        (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i) from by
        rw [← pairing_starFlagEnum_symm W i,
          W.pairing_invol]] at hmem2
      have := (hmem_iff _).mp hmem2
      rw [this] at h1
      exact Bool.noConfusion h1
    · rw [Bool.not_eq_true] at h2
      rw [h2]

private theorem oddColouringOf_congr (W : ClosedFragment)
    (F : EdgeSubset W)
    (c₁ c₂ : MixedColouring k ℓ
      (edgeCount W + edgeCount W))
    (h : c₁ = c₂) (h₁ : colourFlags W c₁ = F.flags)
    (h₂ : colourFlags W c₂ = F.flags) :
    oddColouringOf W F c₁ h₁ = oddColouringOf W F c₂ h₂ := by
  subst h; rfl

private theorem evenColouringOf_congr (W : ClosedFragment)
    (F : EdgeSubset W)
    (c₁ c₂ : MixedColouring k ℓ
      (edgeCount W + edgeCount W))
    (h : c₁ = c₂) (h₁ : colourFlags W c₁ = F.flags)
    (h₂ : colourFlags W c₂ = F.flags)
    (hd₁ : Diagonal W c₁) (hd₂ : Diagonal W c₂) :
    evenColouringOf W F c₁ h₁ hd₁ =
    evenColouringOf W F c₂ h₂ hd₂ := by
  subst h; rfl

-- Raised budget: the fibre sum is reindexed along the
-- data bijection, which unfolds the colouring construction on
-- both the even and the odd side.
/-- **The fibre sum reindexes over the colouring data.** -/
theorem fibreSum_eq_dataSum (W : ClosedFragment)
    (F : EdgeSubset W) :
    (∑ c ∈ Finset.univ.filter
        (fun c : {c : MixedColouring k ℓ
            (edgeCount W + edgeCount W) // c.IsEven} =>
          colourFlags W c.val = F.flags),
      masterSummand f P e' W c.val) =
    ∑ ψ : F.EvenColouring k, ∑ φ : F.OddColouring ℓ,
      masterSummand f P e' W (colouringOf W F ψ φ) := by
  classical
  have hrestrict : (∑ c ∈ Finset.univ.filter
      (fun c : {c : MixedColouring k ℓ
          (edgeCount W + edgeCount W) // c.IsEven} =>
        colourFlags W c.val = F.flags),
      masterSummand f P e' W c.val) =
    ∑ c ∈ Finset.univ.filter
      (fun c : {c : MixedColouring k ℓ
          (edgeCount W + edgeCount W) // c.IsEven} =>
        colourFlags W c.val = F.flags ∧
        Diagonal W c.val),
      masterSummand f P e' W c.val := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨hc.1, hc.2.1⟩
    · intro c hcA hcnB
      rw [Finset.mem_filter] at hcA
      have hdiagfail : ¬ Diagonal W c.val := by
        intro hd
        exact hcnB (by
          rw [Finset.mem_filter]
          exact ⟨hcA.1, hcA.2, hd⟩)
      exact masterSummand_vanish_of_not_diagonal f P e' W
        c.val (pairPure_of_pattern_closed W c.val F.flags
          hcA.2 F.pairing_mem) hdiagfail
  have hbij : (∑ p : F.EvenColouring k × F.OddColouring ℓ,
      masterSummand f P e' W (colouringOf W F p.1 p.2)) =
    ∑ c ∈ Finset.univ.filter
      (fun c : {c : MixedColouring k ℓ
          (edgeCount W + edgeCount W) // c.IsEven} =>
        colourFlags W c.val = F.flags ∧
        Diagonal W c.val),
      masterSummand f P e' W c.val := by
    refine Finset.sum_bij
      (i := fun p _ =>
        (⟨colouringOf W F p.1 p.2,
          colouringOf_isEven W F p.1 p.2⟩ :
          {c : MixedColouring k ℓ
            (edgeCount W + edgeCount W) // c.IsEven}))
      ?_ ?_ ?_ ?_
    · intro p _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        colourFlags_colouringOf W F p.1 p.2,
        colouringOf_diagonal W F p.1 p.2⟩
    · intro p _ q _ hpq
      have hval := congrArg Subtype.val hpq
      have heven : p.1 = q.1 :=
        (evenColouringOf_colouringOf W F p.1 p.2).symm.trans
          ((evenColouringOf_congr W F _ _ hval _ _ _ _).trans
            (evenColouringOf_colouringOf W F q.1 q.2))
      have hodd : p.2 = q.2 :=
        (oddColouringOf_colouringOf W F p.1 p.2).symm.trans
          ((oddColouringOf_congr W F _ _ hval _ _).trans
            (oddColouringOf_colouringOf W F q.1 q.2))
      exact Prod.ext heven hodd
    · intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨-, hfib, hdiag⟩ := hb
      refine ⟨(evenColouringOf W F b.val hfib hdiag,
        oddColouringOf W F b.val hfib),
        Finset.mem_univ _, ?_⟩
      exact Subtype.ext
        (colouringOf_reconstruct W F b.val hfib hdiag)
    · intro p _
      rfl
  refine hrestrict.trans (Eq.trans hbij.symm ?_)
  exact Fintype.sum_prod_type
    (f := fun p : F.EvenColouring k × F.OddColouring ℓ =>
      masterSummand f P e' W (colouringOf W F p.1 p.2))

open Classical in
/-- The edge set of an edge subset: representative slots whose
flags participate. -/
noncomputable def edgeIndexSet (W : ClosedFragment)
    (F : EdgeSubset W) : Finset (Fin (edgeCount W)) :=
  Finset.univ.filter (fun i =>
    (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈
      F.flags)

open Classical in
/-- **The crossings of a data colouring**: both-participating
pairs. -/
theorem koszulCrossings_colouringOf (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    koszulCrossings
      (MixedColouring.firstHalf (a := edgeCount W)
        (b := edgeCount W) (colouringOf W F ψ φ))
      (MixedColouring.secondHalf (a := edgeCount W)
        (b := edgeCount W) (colouringOf W F ψ φ)) =
    (Finset.univ.filter
      (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
        p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
        p.2 ∈ edgeIndexSet W F)).card := by
  unfold koszulCrossings
  refine congrArg Finset.card (Finset.filter_congr
    (fun p _ => ?_))
  have hmem : ∀ t : Fin (edgeCount W + edgeCount W),
      ((colouringOf W F ψ φ) t).isRight = true ↔
      (starFlagEnum W).symm t ∈ F.flags := by
    intro t
    constructor
    · intro h
      rw [← colourFlags_colouringOf W F ψ φ]
      rw [mem_colourFlags_iff,
        _root_.Equiv.apply_symm_apply]
      exact h
    · intro h
      rw [← colourFlags_colouringOf W F ψ φ] at h
      rw [mem_colourFlags_iff,
        _root_.Equiv.apply_symm_apply] at h
      exact h
  constructor
  · rintro ⟨hlt, h2, h1⟩
    refine ⟨hlt, ?_, ?_⟩
    · rw [edgeIndexSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have := (hmem (Fin.natAdd (edgeCount W) p.1)).mp h1
      rw [show (starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) p.1) =
        W.pairing ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) p.1)) from
        (pairing_starFlagEnum_symm W p.1).symm] at this
      have h3 := F.pairing_mem _ this
      rw [W.pairing_invol] at h3
      exact h3
    · rw [edgeIndexSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        (hmem (Fin.castAdd (edgeCount W) p.2)).mp h2⟩
  · rintro ⟨hlt, h1, h2⟩
    rw [edgeIndexSet, Finset.mem_filter] at h1 h2
    refine ⟨hlt, ?_, ?_⟩
    · exact (hmem (Fin.castAdd (edgeCount W) p.2)).mpr h2.2
    · refine (hmem (Fin.natAdd (edgeCount W) p.1)).mpr ?_
      rw [show (starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) p.1) =
        W.pairing ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) p.1)) from
        (pairing_starFlagEnum_symm W p.1).symm]
      exact F.pairing_mem _ h1.2

end RS
