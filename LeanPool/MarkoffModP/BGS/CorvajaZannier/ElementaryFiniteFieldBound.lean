/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic

/-!
# Elementary finite-field torsion bounds

This file records the part of the finite-field Corvaja--Zannier estimate that
uses only the fact that a nonzero polynomial has at most its degree many roots.
It does not use curve geometry or the Corvaja--Zannier Wronskian argument.
-/

namespace BGS.External

noncomputable section

/-- The torsion intersection injects into the product of the two groups of
roots of unity.  Consequently its cardinality is at most the product of the
two specified orders. -/
theorem torusCurveTorsionIntersection_card_le_orders
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ)
    (hfirst : 0 < firstOrder) (hsecond : 0 < secondOrder) :
    (torusCurveTorsionIntersection K f firstOrder secondOrder).card ≤
      firstOrder * secondOrder := by
  let S := torusCurveTorsionIntersection K f firstOrder secondOrder
  let : NeZero firstOrder := ⟨hfirst.ne'⟩
  let : NeZero secondOrder := ⟨hsecond.ne'⟩
  let : Fintype (rootsOfUnity firstOrder K) := Fintype.ofFinite _
  let : Fintype (rootsOfUnity secondOrder K) := Fintype.ofFinite _
  let toRoots : {z // z ∈ S} →
      rootsOfUnity firstOrder K × rootsOfUnity secondOrder K := fun z ↦
    (⟨z.1.1, (mem_rootsOfUnity firstOrder z.1.1).2
      (mem_torusCurveTorsionIntersection_iff.1 z.2).2.1⟩,
     ⟨z.1.2, (mem_rootsOfUnity secondOrder z.1.2).2
      (mem_torusCurveTorsionIntersection_iff.1 z.2).2.2⟩)
  have hInjective : Function.Injective toRoots := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun q ↦ (q.1 : Kˣ)) hzw
    · exact congrArg (fun q ↦ (q.2 : Kˣ)) hzw
  calc
    S.card = Fintype.card {z // z ∈ S} := by simp
    _ ≤ Fintype.card
        (rootsOfUnity firstOrder K × rootsOfUnity secondOrder K) :=
      Fintype.card_le_of_injective toRoots hInjective
    _ = Nat.card (rootsOfUnity firstOrder K) *
        Nat.card (rootsOfUnity secondOrder K) := by
      simp only [Fintype.card_prod, Nat.card_eq_fintype_card]
    _ ≤ firstOrder * secondOrder :=
      Nat.mul_le_mul (card_rootsOfUnity K firstOrder)
        (card_rootsOfUnity K secondOrder)

/-- In the small-characteristic regime `p ≤ 12 d₁ d₂`, the second
branch of the Corvaja--Zannier numerical maximum follows from the elementary
finite-group cardinality bound. -/
theorem torusCurveTorsionIntersection_le_corvajaZannierBound_of_smallChar
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [CharP K p]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hfirstOrder : 0 < firstOrder) (hsecondOrder : 0 < secondOrder)
    (hsmall : p ≤ 12 * firstDegree * secondDegree) :
    ((torusCurveTorsionIntersection K f firstOrder secondOrder).card : ℝ) ≤
      BGS.Markoff.corvajaZannierCorollaryTwoNumericalBound
        p firstOrder secondOrder firstDegree secondDegree
          (planeTorusEulerCharacteristicBound firstDegree secondDegree) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcardNat := torusCurveTorsionIntersection_card_le_orders
    f firstOrder secondOrder hfirstOrder hsecondOrder
  have hcardReal :
      ((torusCurveTorsionIntersection K f firstOrder secondOrder).card : ℝ) ≤
        ((firstOrder * secondOrder : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hscaledNat :
      p * (firstOrder * secondOrder) ≤
        12 * (firstOrder * secondOrder * firstDegree * secondDegree) := by
    have := Nat.mul_le_mul_right (firstOrder * secondOrder) hsmall
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hscaledReal' :
      (p : ℝ) * ((firstOrder * secondOrder : ℕ) : ℝ) ≤
        12 * ((firstOrder * secondOrder * firstDegree * secondDegree : ℕ) : ℝ) := by
    exact_mod_cast hscaledNat
  have hscaledReal :
      ((firstOrder * secondOrder : ℕ) : ℝ) * (p : ℝ) ≤
        12 * ((firstOrder * secondOrder * firstDegree * secondDegree : ℕ) : ℝ) := by
    simpa [mul_comm] using hscaledReal'
  have hsecond :
      ((firstOrder * secondOrder : ℕ) : ℝ) ≤
        12 * ((firstOrder * secondOrder * firstDegree * secondDegree : ℕ) : ℝ) /
          (p : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hp)).2
    simpa [mul_comm] using hscaledReal
  unfold BGS.Markoff.corvajaZannierCorollaryTwoNumericalBound
  exact hcardReal.trans (hsecond.trans (le_max_right _ _))

/-- The part of the general plane-curve statement lying strictly outside the
elementary range `p ≤ 12 d₁ d₂`.  This is an ordinary proposition, not an
additional assumption or axiom. -/
def GeneralCorvajaZannierPlaneCurveTheoremAboveElementaryRange : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K p]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ),
    0 < firstDegree →
    0 < secondDegree →
    HasBidegreeAtMost (K := K) f firstDegree secondDegree →
    IsCorvajaZannierPlaneCurve f →
    0 < firstOrder →
    0 < secondOrder →
    ¬ p ∣ firstOrder →
    ¬ p ∣ secondOrder →
    12 * firstDegree * secondDegree < p →
    ((torusCurveTorsionIntersection
        K f firstOrder secondOrder).card : ℝ) ≤
      BGS.Markoff.corvajaZannierCorollaryTwoNumericalBound
        p firstOrder secondOrder firstDegree secondDegree
          (planeTorusEulerCharacteristicBound firstDegree secondDegree)

/-- The full general plane-curve theorem is equivalent to its restriction to
the complementary range `12 d₁ d₂ < p`; the omitted range is exactly the
elementary small-characteristic theorem above. -/
theorem generalCorvajaZannierPlaneCurveTheorem_iff_aboveElementaryRange :
    GeneralCorvajaZannierPlaneCurveTheorem ↔
      GeneralCorvajaZannierPlaneCurveTheoremAboveElementaryRange := by
  constructor
  · intro hGeneral
    unfold GeneralCorvajaZannierPlaneCurveTheoremAboveElementaryRange
    intro p _ K _ _ _ _ f firstDegree secondDegree firstOrder secondOrder
      hfirstDegree hsecondDegree hbidegree hcurve hfirstOrder hsecondOrder
      hfirstPrimeToChar hsecondPrimeToChar _hlarge
    exact hGeneral p (K := K) f
      firstDegree secondDegree firstOrder secondOrder
      hfirstDegree hsecondDegree hbidegree hcurve hfirstOrder hsecondOrder
      hfirstPrimeToChar hsecondPrimeToChar
  · intro hLarge
    unfold GeneralCorvajaZannierPlaneCurveTheorem
    intro p _ K _ _ _ _ f firstDegree secondDegree firstOrder secondOrder
      hfirstDegree hsecondDegree hbidegree hcurve hfirstOrder hsecondOrder
      hfirstPrimeToChar hsecondPrimeToChar
    by_cases hsmall : p ≤ 12 * firstDegree * secondDegree
    · exact
        torusCurveTorsionIntersection_le_corvajaZannierBound_of_smallChar
          p K f firstDegree secondDegree firstOrder secondOrder
          hfirstOrder hsecondOrder hsmall
    · exact hLarge p (K := K) f
        firstDegree secondDegree firstOrder secondOrder
        hfirstDegree hsecondDegree hbidegree hcurve hfirstOrder hsecondOrder
        hfirstPrimeToChar hsecondPrimeToChar (Nat.lt_of_not_ge hsmall)

end

end BGS.External
