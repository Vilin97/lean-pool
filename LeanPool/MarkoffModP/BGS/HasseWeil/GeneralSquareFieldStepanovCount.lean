/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.RationalPlace
import LeanPool.MarkoffModP.BGS.HasseWeil.SquareFieldResidue
import LeanPool.MarkoffModP.BGS.HasseWeil.SquareFieldStepanovZeroCount
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalDifferentDivisor
import Mathlib.Tactic

/-!
# A square-field Stepanov bound for arbitrary function fields

The one-point Stepanov construction is intrinsic to a finite separable
extension of a rational function field.  This file applies it to the complete
type of degree-one places, rather than to the regular affine points of a
chosen plane model.

Choose one rational place as the pole.  Every rational finite place away from
it is a zero-counting place; at most one rational finite place is omitted.
The rational places above infinity contribute at most the degree of the
function-field extension, by the fundamental ramification-inertia equality.
This gives a uniform estimate suitable for the Frobenius fixed-field twists.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [Fintype S] [DecidableEq S] [Algebra K S]
  [DecidableEq (RatFunc S)]
variable (L : Type*) [Field L] [Algebra (RatFunc S) L]
  [FiniteDimensional (RatFunc S) L]
  [Algebra.IsSeparable (RatFunc S) L]

local instance generalSquareFieldConstantAlgebra : Algebra S L :=
  RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
    (algebraMap S (RatFunc S)))

local instance generalSquareFieldConstantTower :
    IsScalarTower S (RatFunc S) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance generalSquareFieldInfinityModuleFinite :
    Module.Finite (RatFuncInfinityIntegers S)
      (RatFuncInfinityIntegralClosure S L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers S) (RatFunc S) L
    (RatFuncInfinityIntegralClosure S L)

local instance generalSquareFieldInfinityIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers S)
      (RatFuncInfinityIntegralClosure S L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers S) L

local instance generalSquareFieldInfinityTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers S)
      (RatFuncInfinityIntegralClosure S L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers S) L

local instance generalSquareFieldInfinityDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure S L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers S)
    (RatFunc S) L (RatFuncInfinityIntegralClosure S L)

omit [Fintype S] in
/-- The number of rational places above infinity is at most the function-field
degree. -/
theorem rationalInfinityPlace_card_le_finrank :
    Nat.card (FiniteExtensionRationalInfinityPlace S L) ≤
      Module.finrank (RatFunc S) L := by
  letI : Fintype (FiniteExtensionInfinityPlace S L) :=
    Set.Finite.fintype (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace S).asIdeal
      (RatFuncInfinityIntegralClosure S L))
  calc
    Nat.card (FiniteExtensionRationalInfinityPlace S L) ≤
        Nat.card (FiniteExtensionInfinityPlace S L) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = Fintype.card (FiniteExtensionInfinityPlace S L) :=
      Nat.card_eq_fintype_card
    _ = ∑ P : FiniteExtensionInfinityPlace S L, 1 := by simp
    _ ≤ ∑ P : FiniteExtensionInfinityPlace S L,
        P.1.ramificationIdx (RatFuncInfinityIntegers S) *
          P.1.inertiaDeg (RatFuncInfinityIntegers S) := by
      apply Finset.sum_le_sum
      intro P _
      exact Right.one_le_mul
        (Ideal.ramificationIdx_pos P.1 (RatFuncInfinityIntegers S))
        (Ideal.inertiaDeg_pos P.1 (RatFuncInfinityIntegers S))
    _ = Module.finrank (RatFunc S) L :=
      finiteExtensionInfinity_sum_ramification_inertia_eq_finrank S L

/-- The intrinsic one-point square-field Stepanov bound for all degree-one
places of a finite separable function field, using Riemann's inequality only
at rational finite places.

If a rational finite place exists, it is chosen as the pole in the Stepanov
construction.  If none exists, all rational places lie above infinity and the
fundamental ramification--inertia equality gives the required bound directly.
Thus no Riemann inequality at an infinity place is needed. -/
theorem finiteExtensionRationalPlaceCount_le_squareFieldStepanov_of_finitePlaceRiemann
    (g : Nat)
    (hcard : Fintype.card S = (Fintype.card K) ^ 2)
    (hconstants : algebraicClosure S L = ⊥)
    (hriemann : ∀ (Q : FiniteExtensionRationalFinitePlace S L) N,
      N + 1 ≤ Module.finrank S
        (finiteExtensionOnePointRiemannSpace S L (.inl Q.1) N) + g)
    (hlarge : (g + 1) * (g + 2) ≤ Fintype.card K) :
    finiteExtensionRationalPlaceCount S L ≤
      Fintype.card S + (2 * g + 1) * Fintype.card K +
        Module.finrank (RatFunc S) L := by
  classical
  let s := Fintype.card K
  let ell := stepanovEll s
  let m := stepanovM g s
  have hs : 0 < s := Fintype.card_pos
  have hbudget : ell + s * m + 1 =
      Fintype.card S + (2 * g + 1) * s := by
    calc
      ell + s * m + 1 = (s - 1) + s * (s + 2 * g) + 1 := by
        rfl
      _ = s + s * (s + 2 * g) := by omega
      _ = s ^ 2 + (2 * g + 1) * s := by ring
      _ = Fintype.card S + (2 * g + 1) * s := by rw [hcard]
  by_cases hnonempty :
      Nonempty (FiniteExtensionRationalFinitePlace S L)
  · let Q0 : FiniteExtensionRationalFinitePlace S L :=
      Classical.choice hnonempty
    let P : FiniteExtensionPlace S L := .inl Q0.1
    have hdegreeP : finiteExtensionPlaceDegree S L P = 1 := Q0.2
    obtain ⟨u, du, v, dv, c, hu, hv, _hc, hsecond, hfirst⟩ :=
      exists_squareField_onePointStepanovAuxiliary_of_degree_one
        K S L P g hconstants hdegreeP (hriemann Q0) hlarge
    let p : FiniteExtensionRationalFinitePlace S L → Prop := fun Q =>
      (Sum.inl Q.1 : FiniteExtensionPlace S L) = P
    let Away := {Q : FiniteExtensionRationalFinitePlace S L // ¬ p Q}
    letI : Fintype Away := Fintype.ofFinite _
    let place : Away → FiniteExtensionFinitePlace S L := fun Q => Q.1.1
    have hplaceInjective : Function.Injective place := by
      intro Q R hQR
      apply Subtype.ext
      apply Subtype.ext
      exact hQR
    have haway : ∀ Q : Away,
        (Sum.inl (place Q) : FiniteExtensionPlace S L) ≠ P := by
      intro Q
      exact Q.2
    have hsquare : ∀ (Q : Away) (z : (place Q).asIdeal.ResidueField),
        z ^ (Fintype.card K) ^ 2 = z := by
      intro Q
      exact finiteExtensionFinitePlace_residue_squareFrobenius_of_degree_one
        K S L hcard (place Q) Q.1.2
    have hAway : Nat.card Away ≤ ell + s * m := by
      have h := Fintype.card_le_of_squareFieldStepanovAuxiliary
        K S L P ell m u du v dv c hu hv hdegreeP place
          hplaceInjective haway hsquare hsecond hfirst
      simpa only [Nat.card_eq_fintype_card] using h
    have hpSubsingleton : Subsingleton
        {Q : FiniteExtensionRationalFinitePlace S L // p Q} := by
      constructor
      intro Q R
      apply Subtype.ext
      apply Subtype.ext
      exact Sum.inl.inj (Q.2.trans R.2.symm)
    have hpCard : Nat.card
        {Q : FiniteExtensionRationalFinitePlace S L // p Q} ≤ 1 := by
      letI := hpSubsingleton
      simpa using Nat.card_le_card_of_injective
        (fun _ : {Q : FiniteExtensionRationalFinitePlace S L // p Q} =>
          (Unit.unit : Unit))
        (fun Q R _ => Subsingleton.elim Q R)
    have hfinite : Nat.card (FiniteExtensionRationalFinitePlace S L) ≤
        ell + s * m + 1 := by
      calc
        Nat.card (FiniteExtensionRationalFinitePlace S L) =
            Nat.card
              ({Q : FiniteExtensionRationalFinitePlace S L // p Q} ⊕ Away) :=
          Nat.card_congr (Equiv.sumCompl p).symm
        _ = Nat.card
              {Q : FiniteExtensionRationalFinitePlace S L // p Q} +
              Nat.card Away := Nat.card_sum
        _ ≤ 1 + (ell + s * m) := Nat.add_le_add hpCard hAway
        _ = ell + s * m + 1 := by omega
    rw [finiteExtensionRationalPlaceCount, Nat.card_sum]
    calc
      Nat.card (FiniteExtensionRationalFinitePlace S L) +
          Nat.card (FiniteExtensionRationalInfinityPlace S L) ≤
          (ell + s * m + 1) + Module.finrank (RatFunc S) L :=
        Nat.add_le_add hfinite (rationalInfinityPlace_card_le_finrank S L)
      _ = Fintype.card S + (2 * g + 1) * Fintype.card K +
          Module.finrank (RatFunc S) L := by rw [hbudget]
  · letI : IsEmpty (FiniteExtensionRationalFinitePlace S L) :=
      ⟨fun Q => hnonempty ⟨Q⟩⟩
    rw [finiteExtensionRationalPlaceCount, Nat.card_sum]
    simp only [Nat.card_of_isEmpty, zero_add]
    exact (rationalInfinityPlace_card_le_finrank S L).trans
      (Nat.le_add_left (Module.finrank (RatFunc S) L)
        (Fintype.card S + (2 * g + 1) * Fintype.card K))

/-- The intrinsic one-point square-field Stepanov bound for all degree-one
places of a finite separable function field.

This compatibility wrapper preserves the original API.  Its stronger
hypothesis supplies the finite-place Riemann inequalities required by
`finiteExtensionRationalPlaceCount_le_squareFieldStepanov_of_finitePlaceRiemann`.
-/
theorem finiteExtensionRationalPlaceCount_le_squareFieldStepanov
    (g : Nat)
    (hcard : Fintype.card S = (Fintype.card K) ^ 2)
    (hconstants : algebraicClosure S L = ⊥)
    (hriemann : ∀ (P : FiniteExtensionPlace S L),
      finiteExtensionPlaceDegree S L P = 1 → ∀ N,
        N + 1 ≤ Module.finrank S
          (finiteExtensionOnePointRiemannSpace S L P N) + g)
    (hlarge : (g + 1) * (g + 2) ≤ Fintype.card K) :
    finiteExtensionRationalPlaceCount S L ≤
      Fintype.card S + (2 * g + 1) * Fintype.card K +
        Module.finrank (RatFunc S) L := by
  apply finiteExtensionRationalPlaceCount_le_squareFieldStepanov_of_finitePlaceRiemann
    K S L g hcard hconstants _ hlarge
  intro Q N
  exact hriemann (.inl Q.1) Q.2 N

end

end BGS.HasseWeil
