/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OneBasis

/-!
# The evaluation leaf

The base of the cap recursion: the strand evaluation on a
transported two-position basis vector is the colour form entry of
the two colours.  Both mixed-parity colourings are excluded by
evenness; the pure branches route through the one-position basis
presentations and the standard-form identification.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped TensorProduct

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}

/-- The standard form on even pairs is the even form. -/
theorem stdForm_evenPair (x y : (stdSuperPair k ℓ).even) :
    (stdForm k ℓ).evenMap (evenPair x y) = stdFormEven k x y := by
  change LinearMap.coprod
      (TensorProduct.lift (stdFormEvenBilin k))
      (TensorProduct.lift (stdFormOddBilin ℓ))
      (x ⊗ₜ[ℂ] y, 0) = _
  rw [LinearMap.coprod_apply, map_zero, add_zero]
  exact TensorProduct.lift.tmul x y

/-- The standard form on odd pairs is the odd form. -/
theorem stdForm_oddPair (x y : (stdSuperPair k ℓ).odd) :
    (stdForm k ℓ).evenMap (oddPair x y) = stdFormOdd ℓ x y := by
  change LinearMap.coprod
      (TensorProduct.lift (stdFormEvenBilin k))
      (TensorProduct.lift (stdFormOddBilin ℓ))
      (0, x ⊗ₜ[ℂ] y) = _
  rw [LinearMap.coprod_apply, map_zero, zero_add]
  exact TensorProduct.lift.tmul x y

-- The evaluation is computed on a two-position
-- basis vector through the transport, unfolding the tensorator and
-- the standard form.
/-- **The evaluation leaf**: the strand evaluation on a
transported two-position basis vector is the colour form entry of
the two colours. -/
theorem omegaFun_ev_basis
    (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
    (hform :
      letI := P.braided
      SuperVect.Hom.comp
        (μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫ η P.ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ)
    (c : MixedColouring k ℓ 2) (hc : c.IsEven) :
    letI := P.braided
    omegaFun f P (evClass f)
        (((stdToOmega f P e 2) : SuperVect.Hom _ _).evenMap
          (evenBasisVec (⟨c, hc⟩ :
            {c : MixedColouring k ℓ 2 // c.IsEven}))) =
      colourFormEntry k ℓ (c 0) (c 1) := by
  let := P.braided
  have hsplit := evenBasisVec_split (a := 1) (b := 1) c hc
  -- ═══════ FOUR PARITY PATTERNS AT THE TWO POSITIONS ═══════
  -- Evenness of the colouring excludes the two mixed ones.
  rcases h0 : c 0 with i | a <;> rcases h1 : c 1 with j | b
  · -- Both even colours.
    have hfh : MixedColouring.firstHalf (a := 1) (b := 1) c =
        oneColourE k ℓ i :=
      oneColour_ext (show MixedColouring.firstHalf (a := 1) (b := 1) c 0 =
        oneColourE k ℓ i 0 from h0)
    have hsh : MixedColouring.secondHalf (a := 1) (b := 1) c =
        oneColourE k ℓ j :=
      oneColour_ext (show MixedColouring.secondHalf (a := 1) (b := 1) c 0 =
        oneColourE k ℓ j 0 from h1)
    have hfe : MixedColouring.IsEven
        (MixedColouring.firstHalf (a := 1) (b := 1) c) := by
      rw [hfh]; exact oneColourE_isEven i
    rw [hsplit, dite_eq_left hfe]
    rw [show (⟨MixedColouring.firstHalf (a := 1) (b := 1) c, hfe⟩ :
        {c' : MixedColouring k ℓ 1 // c'.IsEven}) =
      ⟨oneColourE k ℓ i, oneColourE_isEven i⟩ from
      Subtype.ext hfh]
    rw [show (⟨MixedColouring.secondHalf (a := 1) (b := 1) c,
        by rw [hsh]; exact oneColourE_isEven j⟩ :
        {c' : MixedColouring k ℓ 1 // c'.IsEven}) =
      ⟨oneColourE k ℓ j, oneColourE_isEven j⟩ from
      Subtype.ext hsh]
    rw [evenBasisVec_one, evenBasisVec_one]
    refine Eq.trans ?_ (colourFormEntry_even k ℓ i j).symm
    refine Eq.trans ?_ (stdForm_evenPair (ℓ := ℓ) (stdE k i) (stdE k j))
    refine Eq.trans ?_
      (evForm f P e hform (stdE k i) (stdE k j))
    have hmerge := congrArg (fun z :
        (superPow (stdSuperPair k ℓ) 1 ⊗
          superPow (stdSuperPair k ℓ) 1 ⟶
          P.ω.obj (SkeinObj.mk (1 + 1))) =>
      (z : SuperVect.Hom _ _).evenMap
        (evenPair
          ((evenPair (1 : ℂ) (stdE k i) :
            (superPow (stdSuperPair k ℓ) 1).even))
          ((evenPair (1 : ℂ) (stdE k j) :
            (superPow (stdSuperPair k ℓ) 1).even))))
      (stdToOmega_merge f P e 1 1)
    refine Eq.trans (congrArg (omegaFun f P (evClass f))
      hmerge.symm) ?_
    change omegaFun f P (evClass f)
      (((μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) :
        SuperVect.Hom _ _).evenMap
        (((stdToOmega f P e 1 ⊗ₘ stdToOmega f P e 1) :
          SuperVect.Hom _ _).evenMap
          (evenPair (evenPair (1 : ℂ) (stdE k i))
            (evenPair (1 : ℂ) (stdE k j))))) = _
    rw [show ((stdToOmega f P e 1 ⊗ₘ stdToOmega f P e 1) :
        SuperVect.Hom _ _).evenMap
        (evenPair (evenPair (1 : ℂ) (stdE k i))
          (evenPair (1 : ℂ) (stdE k j))) =
      evenPair
        ((stdToOmega f P e 1 : SuperVect.Hom _ _).evenMap
          (evenPair (1 : ℂ) (stdE k i)))
        ((stdToOmega f P e 1 : SuperVect.Hom _ _).evenMap
          (evenPair (1 : ℂ) (stdE k j))) from
      tensorHom_evenPair _ _ _ _]
    rw [stdToOmega_one_even f P e (stdE k i),
      stdToOmega_one_even f P e (stdE k j)]
    rfl
  · -- Mixed parity: excluded by evenness.
    exfalso
    refine ((c.isEven_succ_right b
      (show c (Fin.last 1) = Sum.inr b from h1)).mp hc) ?_
    rw [show MixedColouring.tail c = oneColourE k ℓ i from
      oneColour_ext (show MixedColouring.tail c 0 =
        oneColourE k ℓ i 0 from h0)]
    exact oneColourE_isEven i
  · -- Mixed parity: excluded by evenness.
    exfalso
    refine oneColourO_not_isEven (k := k) a ?_
    rw [show oneColourO k ℓ a = MixedColouring.tail c from
      (oneColour_ext (show MixedColouring.tail c 0 =
        oneColourO k ℓ a 0 from h0)).symm]
    exact (c.isEven_succ_left j
      (show c (Fin.last 1) = Sum.inl j from h1)).mp hc
  · -- Both odd colours.
    have hfh : MixedColouring.firstHalf (a := 1) (b := 1) c =
        oneColourO k ℓ a :=
      oneColour_ext (show MixedColouring.firstHalf (a := 1) (b := 1) c 0 =
        oneColourO k ℓ a 0 from h0)
    have hsh : MixedColouring.secondHalf (a := 1) (b := 1) c =
        oneColourO k ℓ b :=
      oneColour_ext (show MixedColouring.secondHalf (a := 1) (b := 1) c 0 =
        oneColourO k ℓ b 0 from h1)
    have hfo : ¬ MixedColouring.IsEven
        (MixedColouring.firstHalf (a := 1) (b := 1) c) := by
      rw [hfh]; exact oneColourO_not_isEven a
    rw [hsplit, dite_eq_right hfo]
    rw [show (⟨MixedColouring.firstHalf (a := 1) (b := 1) c, hfo⟩ :
        {c' : MixedColouring k ℓ 1 // ¬ c'.IsEven}) =
      ⟨oneColourO k ℓ a, oneColourO_not_isEven a⟩ from
      Subtype.ext hfh]
    rw [show (⟨MixedColouring.secondHalf (a := 1) (b := 1) c,
        by rw [hsh]; exact oneColourO_not_isEven b⟩ :
        {c' : MixedColouring k ℓ 1 // ¬ c'.IsEven}) =
      ⟨oneColourO k ℓ b, oneColourO_not_isEven b⟩ from
      Subtype.ext hsh]
    rw [oddBasisVec_one, oddBasisVec_one]
    refine Eq.trans ?_ (colourFormEntry_odd k ℓ a b).symm
    refine Eq.trans ?_ (stdForm_oddPair (k := k) (stdF ℓ a) (stdF ℓ b))
    refine Eq.trans ?_
      (evFormOdd f P e hform (stdF ℓ a) (stdF ℓ b))
    have hmerge := congrArg (fun z :
        (superPow (stdSuperPair k ℓ) 1 ⊗
          superPow (stdSuperPair k ℓ) 1 ⟶
          P.ω.obj (SkeinObj.mk (1 + 1))) =>
      (z : SuperVect.Hom _ _).evenMap
        (((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
            (superPow (stdSuperPair k ℓ) 1).even),
          oddUnitPad (stdF ℓ a) ⊗ₜ[ℂ] oddUnitPad (stdF ℓ b)) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) 1)
            (superPow (stdSuperPair k ℓ) 1)).even))
      (stdToOmega_merge f P e 1 1)
    refine Eq.trans (congrArg (omegaFun f P (evClass f))
      hmerge.symm) ?_
    change omegaFun f P (evClass f)
      (((μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) :
        SuperVect.Hom _ _).evenMap
        (((stdToOmega f P e 1 ⊗ₘ stdToOmega f P e 1) :
          SuperVect.Hom _ _).evenMap
          (((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
              (superPow (stdSuperPair k ℓ) 1).even),
            oddUnitPad (stdF ℓ a) ⊗ₜ[ℂ]
              oddUnitPad (stdF ℓ b)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) 1)
              (superPow (stdSuperPair k ℓ) 1)).even))) = _
    rw [show ((stdToOmega f P e 1 ⊗ₘ stdToOmega f P e 1) :
        SuperVect.Hom _ _).evenMap
        (((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
            (superPow (stdSuperPair k ℓ) 1).even),
          oddUnitPad (stdF ℓ a) ⊗ₜ[ℂ] oddUnitPad (stdF ℓ b)) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) 1)
            (superPow (stdSuperPair k ℓ) 1)).even) =
      oddPair
        ((stdToOmega f P e 1 : SuperVect.Hom _ _).oddMap
          (oddUnitPad (stdF ℓ a)))
        ((stdToOmega f P e 1 : SuperVect.Hom _ _).oddMap
          (oddUnitPad (stdF ℓ b))) from
      tensorHom_oddPair _ _ _ _]
    rw [stdToOmega_one_odd f P e (stdF ℓ a),
      stdToOmega_one_odd f P e (stdF ℓ b)]
    rfl

end RS
