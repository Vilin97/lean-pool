/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneFrobeniusDegenerate

/-!
# Closed Frobenius reduction for affine plane curves

This module conjugates first-coordinate deflation by the coordinate swap and
thereby handles either inseparable coordinate.  An absolutely irreducible
plane equation over a finite field either has an absent coordinate, in which
case its affine point count is exactly the field cardinality, or it admits a
same-count equation with both coordinate partial derivatives nonzero and no
larger supplied bidegree bounds.
-/

namespace BGS.HasseWeil

open MvPolynomial

noncomputable section

variable (R : Type*) [CommRing R]

/-- Swap the two variables of a plane polynomial. -/
def planeSwapAlgEquiv :
    MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1)

@[simp] theorem planeSwapAlgEquiv_apply (f : MvPolynomial (Fin 2) R) :
    planeSwapAlgEquiv R f =
      MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f := rfl

theorem pderiv_zero_planeSwapAlgEquiv
    (f : MvPolynomial (Fin 2) R) :
    pderiv 0 (planeSwapAlgEquiv R f) =
      planeSwapAlgEquiv R (pderiv 1 f) := by
  simpa [planeSwapAlgEquiv] using
    (MvPolynomial.pderiv_rename
      (Equiv.swap (0 : Fin 2) 1).injective (1 : Fin 2) f)

theorem pderiv_one_planeSwapAlgEquiv
    (f : MvPolynomial (Fin 2) R) :
    pderiv 1 (planeSwapAlgEquiv R f) =
      planeSwapAlgEquiv R (pderiv 0 f) := by
  simpa [planeSwapAlgEquiv] using
    (MvPolynomial.pderiv_rename
      (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2) f)

theorem pderiv_zero_planeSwapAlgEquiv_ne_zero
    {f : MvPolynomial (Fin 2) R} (hf : pderiv 1 f ≠ 0) :
    pderiv 0 (planeSwapAlgEquiv R f) ≠ 0 := by
  rw [pderiv_zero_planeSwapAlgEquiv]
  exact (planeSwapAlgEquiv R).injective.ne hf

theorem pderiv_one_planeSwapAlgEquiv_ne_zero
    {f : MvPolynomial (Fin 2) R} (hf : pderiv 0 f ≠ 0) :
    pderiv 1 (planeSwapAlgEquiv R f) ≠ 0 := by
  rw [pderiv_one_planeSwapAlgEquiv]
  exact (planeSwapAlgEquiv R).injective.ne hf

theorem degreeOf_zero_planeSwapAlgEquiv
    (f : MvPolynomial (Fin 2) R) :
    degreeOf 0 (planeSwapAlgEquiv R f) = degreeOf 1 f := by
  simpa [planeSwapAlgEquiv] using
    (MvPolynomial.degreeOf_rename_of_injective
      (Equiv.swap (0 : Fin 2) 1).injective (1 : Fin 2) (p := f))

theorem hasBidegreeAtMost_planeSwapAlgEquiv
    {f : MvPolynomial (Fin 2) R} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree) :
    BGS.External.HasBidegreeAtMost
      (planeSwapAlgEquiv R f) secondDegree firstDegree := by
  classical
  intro m hm
  rw [planeSwapAlgEquiv_apply,
    MvPolynomial.support_rename_of_injective
      (Equiv.swap (0 : Fin 2) 1).injective] at hm
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  have hd := hdegree n hn
  have hzero :
      Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) n 0 = n 1 := by
    simpa using Finsupp.mapDomain_apply
      (Equiv.swap (0 : Fin 2) 1).injective n (1 : Fin 2)
  have hone :
      Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) n 1 = n 0 := by
    simpa using Finsupp.mapDomain_apply
      (Equiv.swap (0 : Fin 2) 1).injective n (0 : Fin 2)
  simpa [hzero, hone] using And.intro hd.2 hd.1

theorem map_planeSwapAlgEquiv
    {S : Type*} [CommRing S] (φ : R →+* S)
    (f : MvPolynomial (Fin 2) R) :
    map φ (planeSwapAlgEquiv R f) =
      planeSwapAlgEquiv S (map φ f) := by
  simp [planeSwapAlgEquiv, MvPolynomial.map_rename]

theorem absolutelyIrreducible_planeSwapAlgEquiv
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f)) :
    Irreducible
      (map (algebraMap K (AlgebraicClosure K))
        (planeSwapAlgEquiv K f)) := by
  rw [map_planeSwapAlgEquiv]
  exact hf.map (planeSwapAlgEquiv (AlgebraicClosure K)).toMulEquiv

theorem eval_planeSwapAlgEquiv
    (f : MvPolynomial (Fin 2) R) (x y : R) :
    eval ![y, x] (planeSwapAlgEquiv R f) = eval ![x, y] f := by
  simp [planeSwapAlgEquiv, MvPolynomial.eval_rename]

section FiniteField

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

def planeSwapAffineZeroEquiv (f : MvPolynomial (Fin 2) K) :
    {z // z ∈ BGS.External.affinePlaneCurveZeros K
      (planeSwapAlgEquiv K f)} ≃
      {z // z ∈ BGS.External.affinePlaneCurveZeros K f} :=
  (Equiv.prodComm K K).subtypeEquiv fun z => by
    simp only [BGS.External.mem_affinePlaneCurveZeros_iff]
    exact (eval_planeSwapAlgEquiv K f z.2 z.1).congr_left

theorem card_affinePlaneCurveZeros_planeSwapAlgEquiv
    (f : MvPolynomial (Fin 2) K) :
    (BGS.External.affinePlaneCurveZeros K
      (planeSwapAlgEquiv K f)).card =
      (BGS.External.affinePlaneCurveZeros K f).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (planeSwapAffineZeroEquiv K f)

end FiniteField

/-- Frobenius deflation in whichever coordinate is inseparable.  The only
alternative to a same-count separating equation is the exact univariate
point count. -/
theorem separatingFrobeniusDeflation_or_exactPointCount
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstDegree secondDegree : ℕ)
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (habsolute : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f)) :
    (BGS.External.affinePlaneCurveZeros K f).card = Fintype.card K ∨
      ∃ g : MvPolynomial (Fin 2) K,
        BGS.External.HasBidegreeAtMost g firstDegree secondDegree ∧
        Irreducible (map (algebraMap K (AlgebraicClosure K)) g) ∧
        pderiv 0 g ≠ 0 ∧ pderiv 1 g ≠ 0 ∧
        (BGS.External.affinePlaneCurveZeros K g).card =
          (BGS.External.affinePlaneCurveZeros K f).card := by
  by_cases hpartialSecond : pderiv 1 f ≠ 0
  · rcases exists_planeFirstSeparatingDeflation_or_degreeOf_zero
      K f firstDegree secondDegree hdegree habsolute hpartialSecond with
      hdegreeZero | ⟨g, hgdegree, hgabsolute, hgpartialFirst,
        hgpartialSecond, hgcard⟩
    · exact Or.inl
        (card_affinePlaneCurveZeros_eq_card_of_degreeOf_zero
          K habsolute hdegreeZero)
    · exact Or.inr ⟨g, hgdegree, hgabsolute, hgpartialFirst,
        hgpartialSecond, hgcard⟩
  · have hpartialFirst : pderiv 0 f ≠ 0 := by
      rcases
        pderiv_zero_ne_zero_or_pderiv_one_ne_zero_of_absolutelyIrreducible
          K f habsolute with h | h
      · exact h
      · exact (hpartialSecond h).elim
    let fSwap := planeSwapAlgEquiv K f
    have hdegreeSwap : BGS.External.HasBidegreeAtMost
        fSwap secondDegree firstDegree :=
      hasBidegreeAtMost_planeSwapAlgEquiv K hdegree
    have habsoluteSwap : Irreducible
        (map (algebraMap K (AlgebraicClosure K)) fSwap) :=
      absolutelyIrreducible_planeSwapAlgEquiv habsolute
    have hpartialSecondSwap : pderiv 1 fSwap ≠ 0 :=
      pderiv_one_planeSwapAlgEquiv_ne_zero K hpartialFirst
    rcases exists_planeFirstSeparatingDeflation_or_degreeOf_zero
      K fSwap secondDegree firstDegree hdegreeSwap habsoluteSwap
        hpartialSecondSwap with hdegreeZero | ⟨g, hgdegree,
          hgabsolute, hgpartialFirst, hgpartialSecond, hgcard⟩
    · left
      rw [← card_affinePlaneCurveZeros_planeSwapAlgEquiv K f]
      exact card_affinePlaneCurveZeros_eq_card_of_degreeOf_zero
        K habsoluteSwap hdegreeZero
    · right
      refine ⟨planeSwapAlgEquiv K g,
        hasBidegreeAtMost_planeSwapAlgEquiv K hgdegree,
        absolutelyIrreducible_planeSwapAlgEquiv hgabsolute,
        pderiv_zero_planeSwapAlgEquiv_ne_zero K hgpartialSecond,
        pderiv_one_planeSwapAlgEquiv_ne_zero K hgpartialFirst, ?_⟩
      rw [card_affinePlaneCurveZeros_planeSwapAlgEquiv, hgcard,
        card_affinePlaneCurveZeros_planeSwapAlgEquiv]

/-- Any coefficient-`8` affine Hasse bound proved for separating equations
extends to every absolutely irreducible plane equation.  This theorem is the
composition boundary between Frobenius reduction and the zeta/spectral
argument. -/
theorem abs_affinePlaneCurveZeros_card_sub_card_le_of_separating_case
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstDegree secondDegree : ℕ)
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (habsolute : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f))
    (hseparating :
      ∀ g : MvPolynomial (Fin 2) K,
        BGS.External.HasBidegreeAtMost g firstDegree secondDegree →
        Irreducible (map (algebraMap K (AlgebraicClosure K)) g) →
        pderiv 0 g ≠ 0 → pderiv 1 g ≠ 0 →
        |((BGS.External.affinePlaneCurveZeros K g).card : ℝ) -
            (Fintype.card K : ℝ)| ≤
          8 * Real.sqrt (Fintype.card K : ℝ) *
            (firstDegree : ℝ) * (secondDegree : ℝ)) :
    |((BGS.External.affinePlaneCurveZeros K f).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      8 * Real.sqrt (Fintype.card K : ℝ) *
        (firstDegree : ℝ) * (secondDegree : ℝ) := by
  rcases separatingFrobeniusDeflation_or_exactPointCount
      K f firstDegree secondDegree hdegree habsolute with
    hcard | ⟨g, hgdegree, hgabsolute, hgpartialFirst,
      hgpartialSecond, hgcard⟩
  · rw [hcard]
    simp only [sub_self, abs_zero]
    positivity
  · rw [← hgcard]
    exact hseparating g hgdegree hgabsolute hgpartialFirst hgpartialSecond

end

end BGS.HasseWeil
