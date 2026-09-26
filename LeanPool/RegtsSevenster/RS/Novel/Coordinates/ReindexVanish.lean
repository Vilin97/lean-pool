/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockParity
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaDiagForm
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.FibreParam

/-!
# Vanishing branches of the fibre identity

Non-Eulerian patterns kill every master summand in their fibre:
the odd-degree vertex is a block of odd parity.
-/

@[expose] public section

namespace RS

open CategoryTheory Finset


variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- **Non-Eulerian vanishing**: a colouring whose pattern is a
closed non-Eulerian subset has vanishing master summand. -/
theorem masterSummand_vanish_of_not_eulerian
    (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (s : Finset W.Flag)
    (hclosed : ∀ g ∈ s, W.pairing g ∈ s)
    (hfibre : colourFlags W c = s)
    (hnotE : ¬ (EdgeSubset.mk s hclosed).Eulerian) :
    masterSummand f P e' W c = 0 := by
  rw [EdgeSubset.Eulerian] at hnotE
  push Not at hnotE
  obtain ⟨v₀, hv₀⟩ := hnotE
  obtain ⟨v, hv⟩ : ∃ v, blockVertex W v = v₀ :=
    ⟨(finCongr (degList_length (starAssignEnum W))).symm
      (Fintype.equivFin W.Vertex v₀), by
      rw [blockVertex, _root_.Equiv.apply_symm_apply,
        _root_.Equiv.symm_apply_apply]⟩
  refine masterSummand_vanish_of_block_odd f P e' W c v ?_
  rw [blockRestrict_parity]
  intro hEvenFlags
  refine hv₀ ?_
  rw [EdgeSubset.deg]
  convert hEvenFlags using 2
  ext g
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hgs, hga⟩
    refine ⟨hfibre ▸ hgs, ?_⟩
    rw [hv]
    have h2 := ClosedFragment.attach_eq_vertexOf W g
    rw [hga] at h2
    exact (Sum.inl.inj h2).symm
  · rintro ⟨hgc, hgv⟩
    refine ⟨hfibre ▸ hgc, ?_⟩
    rw [ClosedFragment.attach_eq_vertexOf W g, hgv, hv]

/-- **Impure vanishing**: a colouring with a mixed-parity pair
has vanishing master summand. -/
theorem masterSummand_vanish_of_impure
    (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (himpure : ¬ PairPure c) :
    masterSummand f P e' W c = 0 := by
  rw [PairPure] at himpure
  push Not at himpure
  obtain ⟨i, hi⟩ := himpure
  rw [masterSummand]
  rw [betaDiag_eq_betaColour (edgeCount W) c]
  rw [betaColour_eq_zero_of_mixed i (show
      ((MixedColouring.firstHalf (a := edgeCount W)
        (b := edgeCount W) c) i).isRight ≠
      ((MixedColouring.secondHalf (a := edgeCount W)
        (b := edgeCount W) c) i).isRight from hi)]
  rw [mul_zero]

/-- **Non-closed vanishing**: a colouring whose pattern is not
pairing-closed has vanishing master summand. -/
theorem masterSummand_vanish_of_not_closed
    (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (s : Finset W.Flag)
    (hfibre : colourFlags W c = s)
    (hnc : ¬ ∀ g ∈ s, W.pairing g ∈ s) :
    masterSummand f P e' W c = 0 := by
  refine masterSummand_vanish_of_impure f P e' W c ?_
  intro hpure
  refine hnc ?_
  rw [← hfibre]
  exact colourFlags_pairing_mem W c hpure

/-- The entry of a non-partner odd pair vanishes. -/
theorem colourFormEntry_inr_ne {u v : Fin (2 * ℓ)}
    (h : v ≠ oddPartner ℓ u) :
    colourFormEntry k ℓ (Sum.inr u) (Sum.inr v) = 0 := by
  rw [colourFormEntry_odd, stdFormOdd_stdF, ite_eq_right h]

-- The vanishing is located at one off-diagonal
-- slot, but reaching it unfolds the whole summand.
/-- **Off-diagonal vanishing**: a pure non-diagonal colouring
has vanishing master summand. -/
theorem masterSummand_vanish_of_not_diagonal
    {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)
    (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hpure : PairPure c)
    (hnd : ¬ Diagonal W c) :
    masterSummand f P e' W c = 0 := by
  rw [Diagonal] at hnd
  push Not at hnd
  obtain ⟨i, hi⟩ := hnd
  rw [masterSummand]
  rw [betaDiag_eq_betaColour (edgeCount W) c]
  rw [show betaColour
      (MixedColouring.firstHalf (a := edgeCount W)
        (b := edgeCount W) c)
      (MixedColouring.secondHalf (a := edgeCount W)
        (b := edgeCount W) c) = 0 from ?_]
  · rw [mul_zero]
  unfold betaColour
  rw [show (∏ j, colourFormEntry k ℓ
      ((MixedColouring.firstHalf (a := edgeCount W)
        (b := edgeCount W) c) j)
      ((MixedColouring.secondHalf (a := edgeCount W)
        (b := edgeCount W) c) j)) = 0 from ?_]
  · rw [mul_zero]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  change colourFormEntry k ℓ (c (Fin.castAdd (edgeCount W) i))
    (c (Fin.natAdd (edgeCount W) i)) = 0
  have hp := hpure i
  rcases hx : c (Fin.castAdd (edgeCount W) i) with a | u
  · rcases hy : c (Fin.natAdd (edgeCount W) i) with b | v
    · rw [show colourFormEntry k ℓ (Sum.inl a)
          (Sum.inl b) = if a = b then 1 else 0 from rfl]
      rw [ite_eq_right (fun hab => hi (by
        rw [hy, hx, hab]
        rfl))]
    · exfalso
      rw [hx, hy] at hp
      exact Bool.noConfusion hp
  · rcases hy : c (Fin.natAdd (edgeCount W) i) with b | v
    · exfalso
      rw [hx, hy] at hp
      exact Bool.noConfusion hp
    · refine colourFormEntry_inr_ne (fun hv => hi ?_)
      rw [hy, hx, hv]
      rfl

end RS
