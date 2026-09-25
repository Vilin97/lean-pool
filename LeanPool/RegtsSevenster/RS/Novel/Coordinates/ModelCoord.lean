/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourMerge
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ClosedTransition
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.HRS

/-!
# Coordinates of the assembled star vector

The coordinates of the model star vector factor into star
coordinates over the degree blocks: the merge coordinate product
rule threaded through the sum casts and the block enumeration.
-/

namespace RS

variable {k ℓ : ℕ}

/-- Parity is invariant under an index cast. -/
theorem isEven_comp_finCongr {n₁ n₂ : ℕ} (h : n₁ = n₂)
    (c : MixedColouring k ℓ n₂) :
    MixedColouring.IsEven (c ∘ finCongr h) ↔ c.IsEven := by
  subst h
  exact Iff.rfl

/-- The head block is the first half through the sum cast. -/
theorem blockRestrict_cons_head (d : ℕ) (ds : List ℕ)
    (c : MixedColouring k ℓ ((d :: ds).sum)) :
    blockRestrict (d :: ds) c ⟨0, by simp⟩ =
      MixedColouring.firstHalf ((c ∘ finCongr
        (List.sum_cons.symm : d + ds.sum = (d :: ds).sum)) :
        MixedColouring k ℓ (d + ds.sum)) := by
  funext j
  exact congrArg c (Fin.ext
    (blockSigmaEquiv_cons_zero_val d ds j))

/-- The tail blocks are block restrictions of the second half
through the sum cast. -/
theorem blockRestrict_cons_tail (d : ℕ) (ds : List ℕ)
    (c : MixedColouring k ℓ ((d :: ds).sum))
    (v : Fin ds.length) :
    blockRestrict (d :: ds) c v.succ =
      blockRestrict ds (MixedColouring.secondHalf
        ((c ∘ finCongr (List.sum_cons.symm :
          d + ds.sum = (d :: ds).sum)) :
          MixedColouring k ℓ (d + ds.sum))) v := by
  funext j
  exact congrArg c (Fin.ext
    (blockSigmaEquiv_cons_succ_val d ds v j))

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

-- Raised budget: the coordinate factorisation is proved by
-- recursion on the degree list, carrying the merge equivalence at
-- every step.
/-- **The assembled coordinates factor over the blocks.** -/
theorem coordOf_modelStarVec :
    ∀ (ds : List ℕ) (c : MixedColouring k ℓ ds.sum)
      (_hc : c.IsEven),
      coordOf (modelStarVec f P e' ds) c =
        ∏ v : Fin ds.length,
          starCoord f P e' (ds.get v) (blockRestrict ds c v)
  | [], c, hc => by
    have : IsEmpty (Fin ([] : List ℕ).length) :=
      inferInstanceAs (IsEmpty (Fin 0))
    rw [show (∏ v : Fin ([] : List ℕ).length,
        starCoord f P e' (([] : List ℕ).get v)
          (blockRestrict [] c v)) = 1 from
      Finset.prod_of_isEmpty _]
    unfold coordOf
    rw [dite_eq_left hc]
    rfl
  | d :: ds, c, hc => by
    -- Push through the cast.
    have hcast : coordOf (modelStarVec f P e' (d :: ds)) c =
        coordOf (((powMerge (stdSuperPair k ℓ) d ds.sum) :
          SuperVect.Hom _ _).evenMap
          (evenPair
            (((stdFromOmega f P e' d) :
              SuperVect.Hom _ _).evenMap (starVec f P d))
            (modelStarVec f P e' ds)))
          (c ∘ finCongr (List.sum_cons.symm :
            d + ds.sum = (d :: ds).sum)) :=
      coordOf_cast (List.sum_cons.symm :
        d + ds.sum = (d :: ds).sum) _ c
    rw [hcast]
    have hc' : MixedColouring.IsEven (c ∘ finCongr
        (List.sum_cons.symm : d + ds.sum = (d :: ds).sum)) :=
      (isEven_comp_finCongr _ c).mpr hc
    unfold coordOf
    rw [dite_eq_left hc']
    rw [colourMerge_coord d ds.sum _ _ _ hc']
    have hsucc : (∏ v : Fin ((d :: ds).length),
        starCoord f P e' ((d :: ds).get v)
          (blockRestrict (d :: ds) c v)) =
        starCoord f P e' ((d :: ds).get 0)
          (blockRestrict (d :: ds) c 0) *
        ∏ v : Fin ds.length,
          starCoord f P e' ((d :: ds).get v.succ)
            (blockRestrict (d :: ds) c v.succ) :=
      Fin.prod_univ_succ _
    rw [hsucc]
    by_cases hfe : MixedColouring.IsEven
        (MixedColouring.firstHalf ((c ∘ finCongr
          (List.sum_cons.symm : d + ds.sum = (d :: ds).sum)) :
          MixedColouring k ℓ (d + ds.sum)))
    · rw [dite_eq_left hfe]
      -- Head factor is the star coordinate.
      rw [show ((colourPowerEquiv k ℓ d).evenEquiv
          (((stdFromOmega f P e' d) :
            SuperVect.Hom _ _).evenMap (starVec f P d))
          ⟨MixedColouring.firstHalf ((c ∘ finCongr
            (List.sum_cons.symm :
              d + ds.sum = (d :: ds).sum)) :
            MixedColouring k ℓ (d + ds.sum)), hfe⟩) =
        starCoord f P e' d (blockRestrict (d :: ds) c
          ⟨0, by simp⟩) from by
        rw [blockRestrict_cons_head]
        unfold starCoord
        rw [dite_eq_left hfe]]
      -- Tail factor is the induction.
      rw [show ((colourPowerEquiv k ℓ ds.sum).evenEquiv
          (modelStarVec f P e' ds)
          ⟨MixedColouring.secondHalf ((c ∘ finCongr
            (List.sum_cons.symm :
              d + ds.sum = (d :: ds).sum)) :
            MixedColouring k ℓ (d + ds.sum)), _⟩) =
        coordOf (modelStarVec f P e' ds)
          (MixedColouring.secondHalf ((c ∘ finCongr
            (List.sum_cons.symm :
              d + ds.sum = (d :: ds).sum)) :
            MixedColouring k ℓ (d + ds.sum))) from by
        unfold coordOf
        rw [dite_eq_left (MixedColouring.secondHalf_isEven _
          hc' hfe)]]
      rw [coordOf_modelStarVec ds _
        (MixedColouring.secondHalf_isEven _ hc' hfe)]
      refine congrArg₂ (fun a b => a * b) rfl ?_
      refine Finset.prod_congr rfl (fun v _ => ?_)
      rw [blockRestrict_cons_tail]
      rfl
    · rw [dite_eq_right hfe]
      have hzero : starCoord f P e' ((d :: ds).get 0)
          (blockRestrict (d :: ds) c 0) = 0 := by
        rw [show blockRestrict (d :: ds) c
            (0 : Fin (ds.length + 1)) =
          blockRestrict (d :: ds) c ⟨0, by simp⟩ from rfl]
        rw [blockRestrict_cons_head]
        exact starCoord_odd f P e' d _ hfe
      rw [hzero, zero_mul]

end RS
