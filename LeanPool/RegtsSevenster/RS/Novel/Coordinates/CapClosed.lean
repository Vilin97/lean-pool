/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelPermCoord
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaDiag

/-!
# The cap closed form

The peel induction: the cap value on colour basis vectors is the
diagonal cap pairing.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped TensorProduct

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}

-- Raised budget: the cap value is computed on a basis vector
-- through the fibre transport, which unfolds the tensorator, the
-- evaluation and the standard form together.
/-- **The cap closed form.** -/
theorem capVal_closed
    (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
    (hform :
      letI := P.braided
      SuperVect.Hom.comp
        (μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ)
    (m : ℕ) :
    ∀ (c : MixedColouring k ℓ (m + m)) (hc : c.IsEven),
      capVal f P e m (evenBasisVec (⟨c, hc⟩ :
        {c : MixedColouring k ℓ (m + m) // c.IsEven})) =
        betaDiag m c := by
  -- ═══════ INDUCTION ON THE NUMBER OF CAPS ═══════
  -- The zero cap reads off the scalar; each step peels one cap,
  -- splits the value, and applies the smaller closed form.
  induction m with
  | zero =>
    intro c hc
    rw [capVal_zero, evenBasisVec_zeroArity, betaDiag_zero]
  | succ m ih =>
    intro c hc
    let := P.braided
    rw [capVal_succ, splitCapVal_expansion, betaDiag_succ]
    have hterm : ∀ c' :
        {c' : MixedColouring k ℓ ((m + m) + 2) // c'.IsEven},
        coordOf (((modelPermMap (capPeelPerm m) ≫
            eqToHom (congrArg (superPow (stdSuperPair k ℓ))
              (capPeelArity m))) :
          SuperVect.Hom _ _).evenMap
          (evenBasisVec (⟨c, hc⟩ :
            {c : MixedColouring k ℓ
              ((m + 1) + (m + 1)) // c.IsEven}))) c'.val =
        wordSign (adjWord (capPeelPerm m))
            (c'.val ∘ ⇑(finCongr (capPeelArity m))) *
          (if (c'.val ∘ ⇑(finCongr (capPeelArity m))) ∘
              ⇑(capPeelPerm m) = c then (1 : ℂ) else 0) := by
      intro c'
      rw [show (((modelPermMap (capPeelPerm m) ≫
          eqToHom (congrArg (superPow (stdSuperPair k ℓ))
            (capPeelArity m))) :
        SuperVect.Hom _ _).evenMap
        (evenBasisVec (⟨c, hc⟩ :
          {c : MixedColouring k ℓ
            ((m + 1) + (m + 1)) // c.IsEven}))) =
        (((eqToHom (congrArg (superPow (stdSuperPair k ℓ))
            (capPeelArity m)) :
          superPow (stdSuperPair k ℓ) ((m + 1) + (m + 1)) ⟶
            superPow (stdSuperPair k ℓ) ((m + m) + 2)) :
          SuperVect.Hom _ _).evenMap
          (((modelPermMap (capPeelPerm m)) :
            SuperVect.Hom _ _).evenMap
            (evenBasisVec ⟨c, hc⟩))) from rfl]
      rw [coordOf_cast (capPeelArity m)]
      rw [coordOf_modelPermMap]
      rw [coordOf_evenBasisVec]
    refine Eq.trans (Finset.sum_congr rfl
      (fun c' _ => by rw [hterm c'])) ?_
    refine Eq.trans (Finset.sum_eq_single
      (⟨peelColour m c, peelColour_isEven m hc⟩ :
        {c' : MixedColouring k ℓ
          ((m + m) + 2) // c'.IsEven}) ?_ ?_) ?_
    · intro b _ hb
      rw [ite_eq_right (fun hspec => hb
        (Subtype.ext (eq_peelColour_of m hspec)))]
      rw [mul_zero, zero_mul]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
    · rw [ite_eq_left (peelColour_spec m c), mul_one]
      congr 1
      rw [show evenBasisVec
          (⟨peelColour m c, peelColour_isEven m hc⟩ :
            {c' : MixedColouring k ℓ
              ((m + m) + 2) // c'.IsEven}) =
        evenBasisVec (⟨peelColour m c,
            peelColour_isEven m hc⟩ :
          {c' : MixedColouring k ℓ
            ((m + m) + 2) // c'.IsEven}) from rfl]
      by_cases hfh : MixedColouring.IsEven
          (MixedColouring.firstHalf (a := m + m) (b := 2)
            (peelColour m c))
      · rw [dite_eq_left hfh]
        rw [show evenBasisVec
            (⟨peelColour m c, peelColour_isEven m hc⟩ :
              {c' : MixedColouring k ℓ
                ((m + m) + 2) // c'.IsEven}) =
          ((powMerge (stdSuperPair k ℓ) (m + m) 2) :
            SuperVect.Hom _ _).evenMap
            (evenPair
              (evenBasisVec ⟨MixedColouring.firstHalf
                (peelColour m c), hfh⟩)
              (evenBasisVec ⟨MixedColouring.secondHalf
                  (peelColour m c),
                (peelColour m c).secondHalf_isEven
                  (peelColour_isEven m hc) hfh⟩)) from by
          rw [evenBasisVec_split (peelColour m c)
            (peelColour_isEven m hc), dite_eq_left hfh]]
        rw [splitCapVal_merge]
        rw [ih (MixedColouring.firstHalf (peelColour m c)) hfh]
        rw [omegaFun_ev_basis f P e hform
          (MixedColouring.secondHalf (peelColour m c))
          ((peelColour m c).secondHalf_isEven
            (peelColour_isEven m hc) hfh)]
      · rw [dite_eq_right hfh]
        rw [show evenBasisVec
            (⟨peelColour m c, peelColour_isEven m hc⟩ :
              {c' : MixedColouring k ℓ
                ((m + m) + 2) // c'.IsEven}) =
          ((powMerge (stdSuperPair k ℓ) (m + m) 2) :
            SuperVect.Hom _ _).evenMap
            (((0 : (superPow (stdSuperPair k ℓ)
                (m + m)).even ⊗[ℂ]
                (superPow (stdSuperPair k ℓ) 2).even),
              oddBasisVec ⟨MixedColouring.firstHalf
                (peelColour m c), hfh⟩ ⊗ₜ[ℂ]
                oddBasisVec ⟨MixedColouring.secondHalf
                    (peelColour m c),
                  (peelColour m c).secondHalf_not_isEven'
                    (peelColour_isEven m hc) hfh⟩) :
              (SuperVect.tensorObj
                (superPow (stdSuperPair k ℓ) (m + m))
                (superPow (stdSuperPair k ℓ) 2)).even) from by
          rw [evenBasisVec_split (peelColour m c)
            (peelColour_isEven m hc), dite_eq_right hfh]]
        rw [splitCapVal_oddMerge]

end RS
