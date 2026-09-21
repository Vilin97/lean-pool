/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarRepeat
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SlotPairing
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.EulerianIndependence

/-!
# The Eulerian reindex

The master summand, the flag pattern of a colouring, and the
fibrewise partition of the master colour sum over flag patterns.
-/

namespace RS

open CategoryTheory MonoidalCategory Finset
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- The master summand of a colouring. -/
noncomputable def masterSummand (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W)) :
    ℂ :=
  ((-1 : ℂ) ^ oddInversions (sortSplitPerm W)
      (c ∘ finCongr (degList_sum (starAssignEnum W))) *
    ∏ v, starCoord f P e'
      ((degList (starAssignEnum W)).get v)
      (blockRestrict (degList (starAssignEnum W))
        ((c ∘ finCongr
          (degList_sum (starAssignEnum W))) ∘
          sortSplitPerm W) v)) *
  betaDiag (edgeCount W) c

/-- The master colour sum, in summand form. -/
theorem parameter_masterSummand (W : ClosedFragment)
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (hform :
      letI := P.braided
      SuperVect.Hom.comp
        (μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫
          η P.ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ) :
    f.val W = circleVal f ^ W.circles *
      ∑ c : {c : MixedColouring k ℓ
          (edgeCount W + edgeCount W) // c.IsEven},
        masterSummand f P e' W c.val :=
  parameter_colour_sum f P e e' W hee' hform

open Classical in
/-- The flag pattern of a colouring: the flags at odd slots. -/
noncomputable def colourFlags (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W)) :
    Finset W.Flag :=
  (MixedColouring.oddSet c).image
    (fun s => (starFlagEnum W).symm s)

open Classical in
/-- **The pattern partition of the master sum.** -/
theorem masterSum_partition (W : ClosedFragment) :
    (∑ c : {c : MixedColouring k ℓ
        (edgeCount W + edgeCount W) // c.IsEven},
      masterSummand f P e' W c.val) =
    ∑ s : Finset W.Flag,
      ∑ c ∈ Finset.univ.filter
        (fun c : {c : MixedColouring k ℓ
            (edgeCount W + edgeCount W) // c.IsEven} =>
          colourFlags W c.val = s),
        masterSummand f P e' W c.val :=
  (Finset.sum_fiberwise _ _ _).symm

/-- Parity purity: cap-paired slots share parity. -/
def PairPure {m : ℕ} (c : MixedColouring k ℓ (m + m)) :
    Prop :=
  ∀ i : Fin m,
    (c (Fin.castAdd m i)).isRight =
    (c (Fin.natAdd m i)).isRight

open Classical in
/-- **Pure patterns are pairing-closed.** -/
theorem colourFlags_pairing_mem (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (hpure : PairPure c) :
    ∀ g ∈ colourFlags W c,
      W.pairing g ∈ colourFlags W c := by
  intro g hg
  rw [colourFlags, Finset.mem_image] at hg ⊢
  obtain ⟨s, hs, rfl⟩ := hg
  rw [MixedColouring.oddSet, Finset.mem_filter] at hs
  obtain ⟨-, hodd⟩ := hs
  cases s using Fin.addCases with
  | left i =>
    refine ⟨Fin.natAdd (edgeCount W) i, ?_, ?_⟩
    · rw [MixedColouring.oddSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        rw [show ((c (Fin.natAdd (edgeCount W) i)).isRight :
          Prop) = ((c (Fin.castAdd (edgeCount W)
            i)).isRight : Prop) from by rw [hpure i]]
        exact hodd⟩
    · exact (pairing_starFlagEnum_symm W i).symm
  | right i =>
    refine ⟨Fin.castAdd (edgeCount W) i, ?_, ?_⟩
    · rw [MixedColouring.oddSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        rw [show ((c (Fin.castAdd (edgeCount W)
            i)).isRight : Prop) =
          ((c (Fin.natAdd (edgeCount W) i)).isRight :
            Prop) from by rw [hpure i]]
        exact hodd⟩
    · rw [show W.pairing ((starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) i)) =
        (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i) from by
        rw [← pairing_starFlagEnum_symm W i,
          W.pairing_invol]]

end RS
