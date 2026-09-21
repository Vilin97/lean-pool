/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.Reindex

/-!
# The fibre parametrization

The colouring of an edge subset with colouring data: participating
flags carry the odd edge colour on the representative slot and its
partner on the partner slot; the rest carry the even colour.
-/

namespace RS

open CategoryTheory Finset
open Classical

variable {k ℓ : ℕ}

/-- The colouring of an edge subset with colouring data. -/
noncomputable def colouringOf (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    MixedColouring k ℓ (edgeCount W + edgeCount W) :=
  fun slot =>
    if h : (starFlagEnum W).symm slot ∈ F.flags then
      Sum.inr (if slot.val < edgeCount W then
        φ.val ⟨(starFlagEnum W).symm slot, h⟩
      else
        oddPartner ℓ (φ.val ⟨(starFlagEnum W).symm slot, h⟩))
    else
      Sum.inl (ψ.val ⟨(starFlagEnum W).symm slot, h⟩)

/-- The pattern of the data colouring is the subset. -/
theorem colourFlags_colouringOf (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    colourFlags W (colouringOf W F ψ φ) = F.flags := by
  ext g
  rw [colourFlags, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [MixedColouring.oddSet, Finset.mem_filter] at hs
    obtain ⟨-, hodd⟩ := hs
    by_contra hnot
    rw [colouringOf] at hodd
    rw [dif_neg hnot] at hodd
    exact Bool.noConfusion hodd
  · intro hg
    refine ⟨starFlagEnum W g, ?_, ?_⟩
    · rw [MixedColouring.oddSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [colouringOf]
      rw [dif_pos (show (starFlagEnum W).symm
          (starFlagEnum W g) ∈ F.flags from by
        rw [Equiv.symm_apply_apply]; exact hg)]
      rfl
    · exact _root_.Equiv.symm_apply_apply _ _

/-- Closed subsets have evenly many flags. -/
theorem EdgeSubset.card_even {α : Type} {W : Fragment α}
    (F : EdgeSubset W) : Even F.flags.card := by
  classical
  suffices h : ∀ (n : ℕ) (s : Finset W.Flag), s.card = n →
      (∀ g ∈ s, W.pairing g ∈ s) → Even s.card from
    h F.flags.card F.flags rfl F.pairing_mem
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hcard hclosed
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
    · simp
    · have hpa : W.pairing a ∈ s := hclosed a ha
      have hne : W.pairing a ≠ a := W.pairing_ne a
      have hmem2 : W.pairing a ∈ s.erase a :=
        Finset.mem_erase.mpr ⟨hne, hpa⟩
      set s' := (s.erase a).erase (W.pairing a) with hs'
      have hcard' : s'.card = n - 2 := by
        rw [hs', Finset.card_erase_of_mem hmem2,
          Finset.card_erase_of_mem ha, hcard]
        omega
      have hclosed' : ∀ g ∈ s', W.pairing g ∈ s' := by
        intro g hg
        rw [hs', Finset.mem_erase, Finset.mem_erase] at hg ⊢
        obtain ⟨hgp, hga, hgs⟩ := hg
        refine ⟨?_, ?_, hclosed g hgs⟩
        · exact fun h => hga (by
            rw [← W.pairing_invol g, h, W.pairing_invol])
        · exact fun h => hgp (by
            rw [← W.pairing_invol g, h])
      have h2n : 2 ≤ n := by
        rw [← hcard]
        exact Finset.one_lt_card.mpr
          ⟨a, ha, W.pairing a, hpa, hne.symm⟩
      have hn2 : n - 2 < n := by omega
      have heven' := ih (n - 2) hn2 s' hcard' hclosed'
      rw [hcard'] at heven'
      rw [hcard, show n = (n - 2) + 2 from by omega]
      exact heven'.add even_two

/-- The data colouring is even. -/
theorem colouringOf_isEven (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    (colouringOf W F ψ φ).IsEven := by
  rw [MixedColouring.IsEven]
  have hcardeq : (MixedColouring.oddSet
      (colouringOf W F ψ φ)).card =
    (colourFlags W (colouringOf W F ψ φ)).card := by
    rw [colourFlags]
    exact (Finset.card_image_of_injective _
      (Equiv.injective _)).symm
  rw [hcardeq, colourFlags_colouringOf]
  exact F.card_even

/-- The diagonal partner of a colour: even colours repeat, odd
colours pair symplectically. -/
def diagPartner (x : Fin k ⊕ Fin (2 * ℓ)) :
    Fin k ⊕ Fin (2 * ℓ) :=
  match x with
  | Sum.inl a => Sum.inl a
  | Sum.inr u => Sum.inr (oddPartner ℓ u)

/-- Diagonal colourings: the partner slot carries the diagonal
partner of the representative slot. -/
def Diagonal (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W)) :
    Prop :=
  ∀ i : Fin (edgeCount W),
    c (Fin.natAdd (edgeCount W) i) =
    diagPartner (c (Fin.castAdd (edgeCount W) i))

/-- The data colouring is diagonal. -/
theorem colouringOf_diagonal (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    Diagonal W (colouringOf W F ψ φ) := by
  intro i
  rw [colouringOf, colouringOf]
  have hpair : (starFlagEnum W).symm
      (Fin.natAdd (edgeCount W) i) =
    W.pairing ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) i)) :=
    (pairing_starFlagEnum_symm W i).symm
  by_cases h : (starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) i) ∈ F.flags
  · have h' : (starFlagEnum W).symm
        (Fin.natAdd (edgeCount W) i) ∈ F.flags := by
      rw [hpair]
      exact F.pairing_mem _ h
    rw [dif_pos h, dif_pos h']
    rw [if_pos (show (Fin.castAdd (edgeCount W) i).val <
      edgeCount W from i.isLt)]
    rw [if_neg (show ¬ ((Fin.natAdd (edgeCount W) i).val <
      edgeCount W) from by
      show ¬ (edgeCount W + i.val < edgeCount W); omega)]
    show Sum.inr (oddPartner ℓ (φ.val ⟨_, h'⟩)) =
      diagPartner (Sum.inr (φ.val ⟨_, h⟩))
    rw [show φ.val ⟨(starFlagEnum W).symm
        (Fin.natAdd (edgeCount W) i), h'⟩ =
      φ.val ⟨(starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i), h⟩ from by
      rw [show (⟨(starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) i), h'⟩ :
          {f : W.Flag // f ∈ F.flags}) =
        ⟨W.pairing ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)),
          F.pairing_mem _ h⟩ from Subtype.ext hpair]
      exact φ.property ⟨_, h⟩]
    rfl
  · have h' : (starFlagEnum W).symm
        (Fin.natAdd (edgeCount W) i) ∉ F.flags := by
      rw [hpair]
      intro hmem
      refine h ?_
      have := F.pairing_mem _ hmem
      rw [W.pairing_invol] at this
      exact this
    rw [dif_neg h, dif_neg h']
    show Sum.inl (ψ.val ⟨_, h'⟩) =
      diagPartner (Sum.inl (ψ.val ⟨_, h⟩))
    rw [show ψ.val ⟨(starFlagEnum W).symm
        (Fin.natAdd (edgeCount W) i), h'⟩ =
      ψ.val ⟨(starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i), h⟩ from by
      rw [show (⟨(starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) i), h'⟩ :
          {f : W.Flag // f ∉ F.flags}) =
        ⟨W.pairing ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)),
          F.pairing_not_mem h⟩ from Subtype.ext hpair]
      exact ψ.property ⟨_, h⟩]
    rfl

/-- Pattern membership is slot oddness. -/
theorem mem_colourFlags_iff (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (g : W.Flag) :
    g ∈ colourFlags W c ↔
      (c (starFlagEnum W g)).isRight = true := by
  rw [colourFlags, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [MixedColouring.oddSet, Finset.mem_filter] at hs
    rw [show starFlagEnum W ((starFlagEnum W).symm s) = s
      from _root_.Equiv.apply_symm_apply _ _]
    exact hs.2
  · intro h
    exact ⟨starFlagEnum W g, by
      rw [MixedColouring.oddSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h⟩,
      _root_.Equiv.symm_apply_apply _ _⟩

/-- The even data of a pattern colouring. -/
noncomputable def evenDataOf (W : ClosedFragment)
    (F : EdgeSubset W)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hfibre : colourFlags W c = F.flags) :
    {f : W.Flag // f ∉ F.flags} → Fin k := fun p =>
  (c (starFlagEnum W p.val)).getLeft (by
    obtain ⟨g, hg⟩ := p
    have hp : ¬ (g ∈ colourFlags W c) := by
      rw [hfibre]; exact hg
    rw [mem_colourFlags_iff] at hp
    rcases hx : c (starFlagEnum W g) with a | u
    · rfl
    · exact absurd (by rw [hx]; rfl) hp)

/-- Slot oddness of a participating flag. -/
theorem isRight_of_mem (W : ClosedFragment)
    (F : EdgeSubset W)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hfibre : colourFlags W c = F.flags)
    (g : W.Flag) (hg : g ∈ F.flags) :
    (c (starFlagEnum W g)).isRight = true := by
  have hp : g ∈ colourFlags W c := by
    rw [hfibre]; exact hg
  rw [mem_colourFlags_iff] at hp
  exact hp

/-- The odd data of a pattern colouring: the value at the
representative slot of the flag's edge. -/
noncomputable def oddDataOf (W : ClosedFragment)
    (F : EdgeSubset W)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hfibre : colourFlags W c = F.flags) :
    {f : W.Flag // f ∈ F.flags} → Fin (2 * ℓ) := fun p =>
  if (starFlagEnum W p.val).val < edgeCount W then
    (c (starFlagEnum W p.val)).getRight
      (isRight_of_mem W F c hfibre p.val p.prop)
  else
    (c (starFlagEnum W (W.pairing p.val))).getRight
      (isRight_of_mem W F c hfibre _
        (F.pairing_mem _ p.prop))

private theorem getLeft_congr {α β : Type*} {x y : α ⊕ β}
    (h : x = y) (hx : x.isLeft = true) (hy : y.isLeft = true) :
    x.getLeft hx = y.getLeft hy := by subst h; rfl

private theorem getRight_congr {α β : Type*} {x y : α ⊕ β}
    (h : x = y) (hx : x.isRight = true)
    (hy : y.isRight = true) :
    x.getRight hx = y.getRight hy := by subst h; rfl

/-- The pairing flips low slots high. -/
theorem starFlagEnum_pairing_low (W : ClosedFragment)
    (g : W.Flag) (h : (starFlagEnum W g).val < edgeCount W) :
    starFlagEnum W (W.pairing g) =
      Fin.natAdd (edgeCount W)
        ⟨(starFlagEnum W g).val, h⟩ := by
  have hg : g = (starFlagEnum W).symm
      (Fin.castAdd (edgeCount W)
        ⟨(starFlagEnum W g).val, h⟩) := by
    rw [show Fin.castAdd (edgeCount W)
        ⟨(starFlagEnum W g).val, h⟩ =
      starFlagEnum W g from Fin.ext rfl]
    exact (_root_.Equiv.symm_apply_apply _ _).symm
  refine Eq.trans (congrArg
    (fun x => starFlagEnum W (W.pairing x)) hg) ?_
  refine Eq.trans (congrArg (starFlagEnum W)
    (pairing_starFlagEnum_symm W
      ⟨(starFlagEnum W g).val, h⟩)) ?_
  exact _root_.Equiv.apply_symm_apply _ _

/-- The pairing flips high slots low. -/
theorem starFlagEnum_pairing_high (W : ClosedFragment)
    (g : W.Flag)
    (h : ¬ (starFlagEnum W g).val < edgeCount W) :
    starFlagEnum W (W.pairing g) =
      Fin.castAdd (edgeCount W)
        ⟨(starFlagEnum W g).val - edgeCount W, by
          have := (starFlagEnum W g).isLt; omega⟩ := by
  set j : Fin (edgeCount W) :=
    ⟨(starFlagEnum W g).val - edgeCount W, by
      have := (starFlagEnum W g).isLt; omega⟩ with hj
  have hg : g = (starFlagEnum W).symm
      (Fin.natAdd (edgeCount W) j) := by
    rw [show Fin.natAdd (edgeCount W) j =
      starFlagEnum W g from Fin.ext (by
        show edgeCount W + ((starFlagEnum W g).val -
          edgeCount W) = (starFlagEnum W g).val
        omega)]
    exact (_root_.Equiv.symm_apply_apply _ _).symm
  refine Eq.trans (congrArg
    (fun x => starFlagEnum W (W.pairing x)) hg) ?_
  refine Eq.trans (congrArg (starFlagEnum W)
    (show W.pairing ((starFlagEnum W).symm
        (Fin.natAdd (edgeCount W) j)) =
      (starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) j) from by
      rw [← pairing_starFlagEnum_symm W j,
        W.pairing_invol])) ?_
  exact _root_.Equiv.apply_symm_apply _ _

/-- The odd data is pairing-constant. -/
theorem oddDataOf_constancy (W : ClosedFragment)
    (F : EdgeSubset W)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hfibre : colourFlags W c = F.flags)
    (p : {f : W.Flag // f ∈ F.flags}) :
    oddDataOf W F c hfibre
      ⟨W.pairing p.val, F.pairing_mem _ p.prop⟩ =
    oddDataOf W F c hfibre p := by
  obtain ⟨g, hg⟩ := p
  rw [oddDataOf, oddDataOf]
  by_cases hlow : (starFlagEnum W g).val < edgeCount W
  · rw [if_pos hlow]
    rw [if_neg (show ¬ ((starFlagEnum W
        (W.pairing g)).val < edgeCount W) from by
      rw [starFlagEnum_pairing_low W g hlow]
      show ¬ (edgeCount W + (starFlagEnum W g).val <
        edgeCount W)
      omega)]
    exact getRight_congr (congrArg c (congrArg _
      (W.pairing_invol g))) _ _
  · rw [if_neg hlow]
    rw [if_pos (show (starFlagEnum W
        (W.pairing g)).val < edgeCount W from by
      rw [starFlagEnum_pairing_high W g hlow]
      show (starFlagEnum W g).val - edgeCount W <
        edgeCount W
      have := (starFlagEnum W g).isLt; omega)]

/-- The even data is pairing-constant on diagonal
colourings. -/
theorem evenDataOf_constancy (W : ClosedFragment)
    (F : EdgeSubset W)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hfibre : colourFlags W c = F.flags)
    (hdiag : Diagonal W c)
    (p : {f : W.Flag // f ∉ F.flags}) :
    evenDataOf W F c hfibre
      ⟨W.pairing p.val, F.pairing_not_mem p.prop⟩ =
    evenDataOf W F c hfibre p := by
  obtain ⟨g, hg⟩ := p
  rw [evenDataOf, evenDataOf]
  by_cases hlow : (starFlagEnum W g).val < edgeCount W
  · have hpart := hdiag ⟨(starFlagEnum W g).val, hlow⟩
    rw [show Fin.castAdd (edgeCount W)
        ⟨(starFlagEnum W g).val, hlow⟩ =
      starFlagEnum W g from Fin.ext rfl] at hpart
    rw [show Fin.natAdd (edgeCount W)
        ⟨(starFlagEnum W g).val, hlow⟩ =
      starFlagEnum W (W.pairing g) from
      (starFlagEnum_pairing_low W g hlow).symm] at hpart
    refine getLeft_congr ?_ _ _
    rw [hpart]
    rcases hx : c (starFlagEnum W g) with a | u
    · rfl
    · exfalso
      have hp : ¬ (g ∈ colourFlags W c) := by
        rw [hfibre]; exact hg
      rw [mem_colourFlags_iff, hx] at hp
      exact hp rfl
  · have hlow' : (starFlagEnum W
        (W.pairing g)).val < edgeCount W := by
      rw [starFlagEnum_pairing_high W g hlow]
      show (starFlagEnum W g).val - edgeCount W <
        edgeCount W
      have := (starFlagEnum W g).isLt; omega
    have hpart := hdiag ⟨(starFlagEnum W
      (W.pairing g)).val, hlow'⟩
    rw [show Fin.castAdd (edgeCount W)
        ⟨(starFlagEnum W (W.pairing g)).val, hlow'⟩ =
      starFlagEnum W (W.pairing g) from Fin.ext rfl]
      at hpart
    rw [show Fin.natAdd (edgeCount W)
        ⟨(starFlagEnum W (W.pairing g)).val, hlow'⟩ =
      starFlagEnum W g from by
      rw [show starFlagEnum W g = starFlagEnum W
          (W.pairing (W.pairing g)) from by
        rw [W.pairing_invol]]
      exact (starFlagEnum_pairing_low W (W.pairing g)
        hlow').symm] at hpart
    refine getLeft_congr ?_ _ _
    rw [hpart]
    rcases hx : c (starFlagEnum W (W.pairing g)) with a | u
    · rfl
    · exfalso
      have hp : ¬ (W.pairing g ∈ colourFlags W c) := by
        rw [hfibre]; exact F.pairing_not_mem hg
      rw [mem_colourFlags_iff, hx] at hp
      exact hp rfl

/-- The even colouring of a diagonal pattern colouring. -/
noncomputable def evenColouringOf (W : ClosedFragment)
    (F : EdgeSubset W)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hfibre : colourFlags W c = F.flags)
    (hdiag : Diagonal W c) : F.EvenColouring k :=
  ⟨evenDataOf W F c hfibre,
    evenDataOf_constancy W F c hfibre hdiag⟩

/-- The odd colouring of a pattern colouring. -/
noncomputable def oddColouringOf (W : ClosedFragment)
    (F : EdgeSubset W)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hfibre : colourFlags W c = F.flags) :
    F.OddColouring ℓ :=
  ⟨oddDataOf W F c hfibre,
    oddDataOf_constancy W F c hfibre⟩

-- Raised budget: reconstruction is checked slot by slot, each slot
-- unfolding the star enumeration and the membership dichotomy.
/-- **Reconstruction**: a diagonal pattern colouring is the data
colouring of its extracted data. -/
theorem colouringOf_reconstruct (W : ClosedFragment)
    (F : EdgeSubset W)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hfibre : colourFlags W c = F.flags)
    (hdiag : Diagonal W c) :
    colouringOf W F (evenColouringOf W F c hfibre hdiag)
      (oddColouringOf W F c hfibre) = c := by
  funext slot
  have henum : starFlagEnum W ((starFlagEnum W).symm slot) =
      slot := _root_.Equiv.apply_symm_apply _ _
  rw [colouringOf]
  by_cases h : (starFlagEnum W).symm slot ∈ F.flags
  · rw [dif_pos h]
    have hodd : (c slot).isRight = true := by
      have hm := isRight_of_mem W F c hfibre _ h
      rw [henum] at hm
      exact hm
    by_cases hrep : slot.val < edgeCount W
    · rw [if_pos hrep]
      show Sum.inr (oddDataOf W F c hfibre
        ⟨(starFlagEnum W).symm slot, h⟩) = c slot
      rw [oddDataOf]
      rw [if_pos (show (starFlagEnum W
          ((starFlagEnum W).symm slot)).val <
          edgeCount W from by rw [henum]; exact hrep)]
      exact Eq.trans (congrArg Sum.inr
        (getRight_congr (congrArg c henum) _ hodd))
        (Sum.inr_getRight _ hodd)
    · rw [if_neg hrep]
      show Sum.inr (oddPartner ℓ (oddDataOf W F c hfibre
        ⟨(starFlagEnum W).symm slot, h⟩)) = c slot
      rw [oddDataOf]
      rw [if_neg (show ¬ ((starFlagEnum W
          ((starFlagEnum W).symm slot)).val <
          edgeCount W) from by rw [henum]; exact hrep)]
      set i₀ : Fin (edgeCount W) :=
        ⟨slot.val - edgeCount W, by
          have := slot.isLt; omega⟩ with hi₀
      have hpair_enum : starFlagEnum W
          (W.pairing ((starFlagEnum W).symm slot)) =
          Fin.castAdd (edgeCount W) i₀ := by
        refine Eq.trans (starFlagEnum_pairing_high W _
          (by rw [henum]; exact hrep)) ?_
        refine congrArg (Fin.castAdd (edgeCount W)) ?_
        refine Fin.ext ?_
        show (starFlagEnum W
          ((starFlagEnum W).symm slot)).val -
          edgeCount W = slot.val - edgeCount W
        rw [henum]
      have hnat : Fin.natAdd (edgeCount W) i₀ = slot :=
        Fin.ext (by
          show edgeCount W + (slot.val - edgeCount W) =
            slot.val
          omega)
      have hd := hdiag i₀
      rw [hnat] at hd
      have hrepmem : W.pairing
          ((starFlagEnum W).symm slot) ∈ F.flags :=
        F.pairing_mem _ h
      have hrepodd : (c (Fin.castAdd (edgeCount W)
          i₀)).isRight = true := by
        have hm := isRight_of_mem W F c hfibre _ hrepmem
        rw [hpair_enum] at hm
        exact hm
      rw [show ((c (starFlagEnum W (W.pairing
          ((starFlagEnum W).symm slot)))).getRight
          (isRight_of_mem W F c hfibre _
            (F.pairing_mem _ h))) =
        ((c (Fin.castAdd (edgeCount W) i₀)).getRight
          hrepodd) from
        getRight_congr (congrArg c hpair_enum) _ _]
      obtain ⟨u, hu⟩ : ∃ u, c (Fin.castAdd
          (edgeCount W) i₀) = Sum.inr u :=
        ⟨(c _).getRight hrepodd,
          (Sum.inr_getRight _ hrepodd).symm⟩
      rw [show (c (Fin.castAdd (edgeCount W)
          i₀)).getRight hrepodd = u from
        getRight_congr hu hrepodd rfl]
      rw [hd, hu]
      rfl
  · rw [dif_neg h]
    have hnotodd : ¬ ((c slot).isRight = true) := by
      have hm : ¬ ((starFlagEnum W).symm slot ∈
          colourFlags W c) := by
        rw [hfibre]; exact h
      rw [mem_colourFlags_iff, henum] at hm
      exact hm
    have hleft : (c slot).isLeft = true := by
      rcases hx : c slot with a | u
      · rfl
      · exact absurd (by rw [hx]; rfl) hnotodd
    show Sum.inl (evenDataOf W F c hfibre
      ⟨(starFlagEnum W).symm slot, h⟩) = c slot
    exact Eq.trans (congrArg Sum.inl
      (getLeft_congr (congrArg c henum) _ hleft))
      (Sum.inl_getLeft _ hleft)

-- As for reconstruction: the round trip is checked flag by flag.
/-- **Round trip, odd data**: extraction inverts construction. -/
theorem oddColouringOf_colouringOf (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    oddColouringOf W F (colouringOf W F ψ φ)
      (colourFlags_colouringOf W F ψ φ) = φ := by
  refine Subtype.ext (funext (fun p => ?_))
  obtain ⟨g, hg⟩ := p
  have hgoal : oddDataOf W F (colouringOf W F ψ φ)
      (colourFlags_colouringOf W F ψ φ) ⟨g, hg⟩ =
    φ.val ⟨g, hg⟩ := ?_
  · exact hgoal
  rw [oddDataOf]
  by_cases hlow : (starFlagEnum W g).val < edgeCount W
  · rw [if_pos hlow]
    have hval : colouringOf W F ψ φ (starFlagEnum W g) =
        Sum.inr (φ.val ⟨g, hg⟩) := by
      rw [colouringOf]
      rw [dif_pos (show (starFlagEnum W).symm
          (starFlagEnum W g) ∈ F.flags from by
        rw [_root_.Equiv.symm_apply_apply]; exact hg)]
      rw [if_pos hlow]
      refine congrArg Sum.inr ?_
      refine congrArg φ.val (Subtype.ext ?_)
      exact _root_.Equiv.symm_apply_apply _ _
    exact Eq.trans (getRight_congr hval _ rfl) rfl
  · rw [if_neg hlow]
    have hglow : (starFlagEnum W
        (W.pairing g)).val < edgeCount W := by
      rw [starFlagEnum_pairing_high W g hlow]
      show (starFlagEnum W g).val - edgeCount W <
        edgeCount W
      have := (starFlagEnum W g).isLt; omega
    have hval : colouringOf W F ψ φ
        (starFlagEnum W (W.pairing g)) =
        Sum.inr (φ.val ⟨g, hg⟩) := by
      rw [colouringOf]
      rw [dif_pos (show (starFlagEnum W).symm
          (starFlagEnum W (W.pairing g)) ∈ F.flags from by
        rw [_root_.Equiv.symm_apply_apply]
        exact F.pairing_mem _ hg)]
      rw [if_pos hglow]
      refine congrArg Sum.inr ?_
      refine Eq.trans (congrArg φ.val
        (show (⟨(starFlagEnum W).symm (starFlagEnum W
            (W.pairing g)), by
          rw [_root_.Equiv.symm_apply_apply]
          exact F.pairing_mem _ hg⟩ :
          {f : W.Flag // f ∈ F.flags}) =
          ⟨W.pairing g, F.pairing_mem _ hg⟩ from
          Subtype.ext
            (_root_.Equiv.symm_apply_apply _ _))) ?_
      exact φ.property ⟨g, hg⟩
    exact Eq.trans (getRight_congr hval _ rfl) rfl

/-- **Round trip, even data.** -/
theorem evenColouringOf_colouringOf (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    evenColouringOf W F (colouringOf W F ψ φ)
      (colourFlags_colouringOf W F ψ φ)
      (colouringOf_diagonal W F ψ φ) = ψ := by
  refine Subtype.ext (funext (fun p => ?_))
  obtain ⟨g, hg⟩ := p
  have hgoal : evenDataOf W F (colouringOf W F ψ φ)
      (colourFlags_colouringOf W F ψ φ) ⟨g, hg⟩ =
    ψ.val ⟨g, hg⟩ := ?_
  · exact hgoal
  rw [evenDataOf]
  have hval : colouringOf W F ψ φ (starFlagEnum W g) =
      Sum.inl (ψ.val ⟨g, hg⟩) := by
    rw [colouringOf]
    rw [dif_neg (show ¬ ((starFlagEnum W).symm
        (starFlagEnum W g) ∈ F.flags) from by
      rw [_root_.Equiv.symm_apply_apply]; exact hg)]
    refine congrArg Sum.inl ?_
    refine congrArg ψ.val (Subtype.ext ?_)
    exact _root_.Equiv.symm_apply_apply _ _
  exact Eq.trans (getLeft_congr hval _ rfl) rfl

end RS
