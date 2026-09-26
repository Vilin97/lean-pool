/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Cage.HasseWeilAssumption

/-!
# Witness-preserving equations for the cage fiber product

This file gives the exact algebraic bridge for the canonical pair of axes.
It deliberately retains the two intersection witnesses.  No point-count or
irreducibility assertion is made here.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- Scalar coordinates of the two incidence witnesses with common third
coordinate.  The roots record the two quadratic choices separately. -/
structure CageIncidenceEquationWitness
    (p : ℕ) [Fact p.Prime] (xi eta : ZMod p) where
  /-- The common coordinate of the two incidence points. -/
  middle : ZMod p
  /-- The discriminant root retaining the first incidence point. -/
  firstRoot : ZMod p
  /-- The discriminant root retaining the second incidence point. -/
  secondRoot : ZMod p
  /-- The quadratic incidence equation for the first fixed trace. -/
  firstEquation :
    (xi ^ 2 - 4) * middle ^ 2 - firstRoot ^ 2 = 4 * xi ^ 2
  /-- The quadratic incidence equation for the second fixed trace. -/
  secondEquation :
    (eta ^ 2 - 4) * middle ^ 2 - secondRoot ^ 2 = 4 * eta ^ 2

@[ext]
theorem CageIncidenceEquationWitness.ext
    {p : ℕ} [Fact p.Prime] {xi eta : ZMod p}
    {x y : CageIncidenceEquationWitness p xi eta}
    (hmiddle : x.middle = y.middle)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot) : x = y := by
  cases x
  cases y
  simp_all

private theorem first_incidence_discriminant_equation
    {K : Type*} [CommRing K] (xi other middle : K)
    (hSurface :
      normalizedPolynomial
        (⟨xi, other, middle⟩ : NormalizedPoint K) = 0) :
    (xi ^ 2 - 4) * middle ^ 2 - (xi * middle - 2 * other) ^ 2 =
      4 * xi ^ 2 := by
  simp only [normalizedPolynomial] at hSurface ⊢
  linear_combination -4 * hSurface

private theorem second_incidence_discriminant_equation
    {K : Type*} [CommRing K] (other eta middle : K)
    (hSurface :
      normalizedPolynomial
        (⟨other, eta, middle⟩ : NormalizedPoint K) = 0) :
    (eta ^ 2 - 4) * middle ^ 2 - (eta * middle - 2 * other) ^ 2 =
      4 * eta ^ 2 := by
  simp only [normalizedPolynomial] at hSurface ⊢
  linear_combination -4 * hSurface

/-- A first-coordinate discriminant equation reconstructs a normalized Markoff point. -/
theorem normalized_first_third_point_of_discriminant_equation
    {K : Type*} [Field K] (hTwo : (2 : K) ≠ 0)
    (xi middle root : K)
    (hEquation :
      (xi ^ 2 - 4) * middle ^ 2 - root ^ 2 = 4 * xi ^ 2) :
    normalizedPolynomial
        (⟨xi, (xi * middle - root) / 2, middle⟩ : NormalizedPoint K) = 0 := by
  simp only [normalizedPolynomial]
  field_simp [hTwo]
  linear_combination -hEquation

/-- A second-coordinate discriminant equation reconstructs a normalized Markoff point. -/
theorem normalized_second_third_point_of_discriminant_equation
    {K : Type*} [Field K] (hTwo : (2 : K) ≠ 0)
    (eta middle root : K)
    (hEquation :
      (eta ^ 2 - 4) * middle ^ 2 - root ^ 2 = 4 * eta ^ 2) :
    normalizedPolynomial
        (⟨(eta * middle - root) / 2, eta, middle⟩ : NormalizedPoint K) = 0 := by
  change normalizedPolynomial
      (normalizedSwap12
        (⟨eta, (eta * middle - root) / 2, middle⟩ : NormalizedPoint K)) = 0
  rw [normalizedPolynomial_swap12]
  exact normalized_first_third_point_of_discriminant_equation
    hTwo eta middle root hEquation

/-- A canonical cage witness pair gives the two quadratic incidence roots,
without projecting either root away. -/
def canonicalCageWitnessToEquations
    (p : ℕ) [Fact p.Prime] (xi eta : ZMod p) :
    CageMiddleWitnessPair p .first .second xi eta →
      CageIncidenceEquationWitness p xi eta := fun z =>
  { middle := z.1.1.u3
    firstRoot := xi * z.1.1.u3 - 2 * z.1.1.u2
    secondRoot := eta * z.1.1.u3 - 2 * z.1.2.u1
    firstEquation := by
      apply first_incidence_discriminant_equation xi z.1.1.u2 z.1.1.u3
      have hxi : z.1.1.u1 = xi := by
        simpa [normalizedFiberAt] using z.2.1.2
      have hSurface : normalizedPolynomial z.1.1 = 0 := by
        simpa [normalizedFiberAt, IsNormalizedMarkoff] using z.2.1.1
      calc
        normalizedPolynomial
            (⟨xi, z.1.1.u2, z.1.1.u3⟩ : NormalizedPoint (ZMod p)) =
            normalizedPolynomial z.1.1 := by
              congr 1
              exact NormalizedPoint.ext hxi.symm rfl rfl
        _ = 0 := hSurface
    secondEquation := by
      apply second_incidence_discriminant_equation z.1.2.u1 eta z.1.1.u3
      have hSurface : normalizedPolynomial z.1.2 = 0 := by
        simpa [normalizedFiberAt, IsNormalizedMarkoff] using z.2.2.1.1
      have heta : z.1.2.u2 = eta := by
        simpa [normalizedFiberAt] using z.2.2.1.2
      have hmiddle : z.1.1.u3 = z.1.2.u3 := by
        simpa [normalizedCoordinateAt, cageBridgeAxis] using z.2.2.2
      calc
        normalizedPolynomial
            (⟨z.1.2.u1, eta, z.1.1.u3⟩ : NormalizedPoint (ZMod p)) =
            normalizedPolynomial z.1.2 := by
              congr 1
              exact NormalizedPoint.ext rfl heta.symm hmiddle
        _ = 0 := hSurface }

/-- Reconstruct both actual Markoff points from the common coordinate and
the two retained roots. -/
def canonicalCageEquationsToWitness
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (xi eta : ZMod p) :
    CageIncidenceEquationWitness p xi eta →
      CageMiddleWitnessPair p .first .second xi eta := fun z => by
  have hTwo : (2 : ZMod p) ≠ 0 := by
    have hpPrime : p.Prime := Fact.out
    exact two_ne_zero_zmod
      (lt_of_le_of_ne hpPrime.two_le (Ne.symm hpTwo))
  let firstPoint : NormalizedPoint (ZMod p) :=
    ⟨xi, (xi * z.middle - z.firstRoot) / 2, z.middle⟩
  let secondPoint : NormalizedPoint (ZMod p) :=
    ⟨(eta * z.middle - z.secondRoot) / 2, eta, z.middle⟩
  refine ⟨(firstPoint, secondPoint), ?_⟩
  refine ⟨⟨?_, rfl⟩, ⟨⟨?_, rfl⟩, rfl⟩⟩
  · exact normalized_first_third_point_of_discriminant_equation
      hTwo xi z.middle z.firstRoot z.firstEquation
  · exact normalized_second_third_point_of_discriminant_equation
      hTwo eta z.middle z.secondRoot z.secondEquation

/-- For odd characteristic, the canonical witness pair is exactly the pair
of quadratic equations.  In particular this equivalence exposes the
diagonal case: the two root fields remain independent even when the two
equations coincide. -/
def canonicalCageWitnessEquivIncidenceEquations
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (xi eta : ZMod p) :
    CageMiddleWitnessPair p .first .second xi eta ≃
      CageIncidenceEquationWitness p xi eta where
  toFun := canonicalCageWitnessToEquations p xi eta
  invFun := canonicalCageEquationsToWitness p hpTwo xi eta
  left_inv := by
    intro z
    have hpPrime : p.Prime := Fact.out
    have hTwo : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod
      (lt_of_le_of_ne hpPrime.two_le (Ne.symm hpTwo))
    have hxi : xi = z.1.1.u1 := by
      simpa [normalizedFiberAt] using z.2.1.2.symm
    have heta : eta = z.1.2.u2 := by
      simpa [normalizedFiberAt] using z.2.2.1.2.symm
    have hmiddle : z.1.1.u3 = z.1.2.u3 := by
      simpa [normalizedCoordinateAt, cageBridgeAxis] using z.2.2.2
    apply Subtype.ext
    apply Prod.ext <;> apply NormalizedPoint.ext <;>
      simp [canonicalCageWitnessToEquations,
        canonicalCageEquationsToWitness, hTwo, hxi, heta, hmiddle]
  right_inv := by
    intro z
    have hpPrime : p.Prime := Fact.out
    have hTwo : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod
      (lt_of_le_of_ne hpPrime.two_le (Ne.symm hpTwo))
    apply CageIncidenceEquationWitness.ext
    · rfl
    · simp only [canonicalCageWitnessToEquations,
      canonicalCageEquationsToWitness]
      field_simp [hTwo]
      ring
    · simp only [canonicalCageWitnessToEquations,
      canonicalCageEquationsToWitness]
      field_simp [hTwo]
      ring

end

end BGS.Markoff
