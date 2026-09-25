/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Cage.HasseWeilAssumption

/-!
# Coordinate-axis invariance of cage witnesses

The cage geometry is symmetric in the three normalized coordinates, but its
point-count argument is written for the canonical ordered pair of outer axes
`(.first, .second)`.  The two incidence witnesses are independent points, so
they may be permuted independently while their common bridge coordinate is
sent to the third coordinate.  This file records that symmetry as an actual
equivalence, retaining the common trace exactly.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- Swapping the first two normalized coordinates as an equivalence. -/
private def normalizedSwap12Equiv (R : Type*) :
    NormalizedPoint R ≃ NormalizedPoint R where
  toFun := normalizedSwap12
  invFun := normalizedSwap12
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl

/-- Swapping the last two normalized coordinates as an equivalence. -/
private def normalizedSwap23Equiv (R : Type*) :
    NormalizedPoint R ≃ NormalizedPoint R where
  toFun := normalizedSwap23
  invFun := normalizedSwap23
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl

/-- Permute the first incidence point so that its outer coordinate is first
and its bridge coordinate is third. -/
private def cageFirstPointCanonicalEquiv (R : Type*)
    (axis other : NormalizedCoordinateAxis) :
    NormalizedPoint R ≃ NormalizedPoint R :=
  match axis, other with
  | .first, .first => normalizedSwap23Equiv R
  | .first, .second => Equiv.refl _
  | .first, .third => normalizedSwap23Equiv R
  | .second, .first => normalizedSwap12Equiv R
  | .second, .second =>
      (normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)
  | .second, .third =>
      (normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)
  | .third, .first =>
      (normalizedSwap23Equiv R).trans (normalizedSwap12Equiv R)
  | .third, .second =>
      ((normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)).trans
        (normalizedSwap12Equiv R)
  | .third, .third =>
      ((normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)).trans
        (normalizedSwap12Equiv R)

/-- Permute the second incidence point so that its outer coordinate is second
and its bridge coordinate is third. -/
private def cageSecondPointCanonicalEquiv (R : Type*)
    (axis other : NormalizedCoordinateAxis) :
    NormalizedPoint R ≃ NormalizedPoint R :=
  match axis, other with
  | .first, .first =>
      (normalizedSwap23Equiv R).trans (normalizedSwap12Equiv R)
  | .first, .second => Equiv.refl _
  | .first, .third => normalizedSwap23Equiv R
  | .second, .first => normalizedSwap12Equiv R
  | .second, .second =>
      ((normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)).trans
        (normalizedSwap12Equiv R)
  | .second, .third =>
      (normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)
  | .third, .first =>
      (normalizedSwap23Equiv R).trans (normalizedSwap12Equiv R)
  | .third, .second =>
      ((normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)).trans
        (normalizedSwap12Equiv R)
  | .third, .third =>
      (normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)

private theorem cageFirstPointCanonical_mem
    {R : Type*} [CommRing R]
    (axis other : NormalizedCoordinateAxis) (xi middle : R)
    {x : NormalizedPoint R}
    (hOuter : x ∈ normalizedFiberAt axis xi)
    (hMiddle : normalizedCoordinateAt (cageBridgeAxis axis other) x = middle) :
    (cageFirstPointCanonicalEquiv R axis other) x ∈
      normalizedFiberAt .first xi ∧
    normalizedCoordinateAt .third
      ((cageFirstPointCanonicalEquiv R axis other) x) = middle := by
  cases axis <;> cases other <;>
    simp only [cageFirstPointCanonicalEquiv, normalizedSwap12Equiv,
      normalizedSwap23Equiv, Equiv.trans_apply, Equiv.refl_apply,
      normalizedFiberAt, normalizedCoordinateAt, cageBridgeAxis]
      at hOuter hMiddle ⊢
  all_goals
    refine ⟨⟨?_, hOuter.2⟩, ?_⟩
    · have hSurface := hOuter.1
      dsimp [IsNormalizedMarkoff, normalizedPolynomial] at hSurface
      dsimp [IsNormalizedMarkoff, normalizedPolynomial,
        normalizedSwap12, normalizedSwap23]
      ring_nf at hSurface ⊢
      exact hSurface
    · exact hMiddle

private theorem cageSecondPointCanonical_mem
    {R : Type*} [CommRing R]
    (axis other : NormalizedCoordinateAxis) (eta middle : R)
    {x : NormalizedPoint R}
    (hOuter : x ∈ normalizedFiberAt other eta)
    (hMiddle : normalizedCoordinateAt (cageBridgeAxis axis other) x = middle) :
    (cageSecondPointCanonicalEquiv R axis other) x ∈
      normalizedFiberAt .second eta ∧
    normalizedCoordinateAt .third
      ((cageSecondPointCanonicalEquiv R axis other) x) = middle := by
  cases axis <;> cases other <;>
    simp only [cageSecondPointCanonicalEquiv, normalizedSwap12Equiv,
      normalizedSwap23Equiv, Equiv.trans_apply, Equiv.refl_apply,
      normalizedFiberAt, normalizedCoordinateAt, cageBridgeAxis]
      at hOuter hMiddle ⊢
  all_goals
    refine ⟨⟨?_, hOuter.2⟩, ?_⟩
    · have hSurface := hOuter.1
      dsimp [IsNormalizedMarkoff, normalizedPolynomial] at hSurface
      dsimp [IsNormalizedMarkoff, normalizedPolynomial,
        normalizedSwap12, normalizedSwap23]
      ring_nf at hSurface ⊢
      exact hSurface
    · exact hMiddle

/-- Send an arbitrary ordered pair of cage axes to the canonical ordered pair.
The two points are permuted independently and their common bridge coordinate
becomes the common third coordinate. -/
def cageMiddleWitnessToCanonical
    (p : ℕ) [Fact p.Prime]
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p) :
    CageMiddleWitnessPair p axis other xi eta →
      CageMiddleWitnessPair p .first .second xi eta := fun z => by
  let firstPoint :=
    (cageFirstPointCanonicalEquiv (ZMod p) axis other) z.1.1
  let secondPoint :=
    (cageSecondPointCanonicalEquiv (ZMod p) axis other) z.1.2
  have hFirst := cageFirstPointCanonical_mem axis other xi
    (normalizedCoordinateAt (cageBridgeAxis axis other) z.1.1)
    z.2.1 rfl
  have hSecondMiddle :
      normalizedCoordinateAt (cageBridgeAxis axis other) z.1.2 =
        normalizedCoordinateAt (cageBridgeAxis axis other) z.1.1 :=
    z.2.2.2.symm
  have hSecond := cageSecondPointCanonical_mem axis other eta
    (normalizedCoordinateAt (cageBridgeAxis axis other) z.1.1)
    z.2.2.1 hSecondMiddle
  exact ⟨(firstPoint, secondPoint), hFirst.1, hSecond.1,
    hFirst.2.trans hSecond.2.symm⟩

private theorem cageFirstPointCanonicalEquiv_preserves_surface
    {R : Type*} [CommRing R]
    (axis other : NormalizedCoordinateAxis) (x : NormalizedPoint R) :
    IsNormalizedMarkoff ((cageFirstPointCanonicalEquiv R axis other) x) ↔
      IsNormalizedMarkoff x := by
  cases axis <;> cases other <;>
    simp [cageFirstPointCanonicalEquiv, normalizedSwap12Equiv,
      normalizedSwap23Equiv, IsNormalizedMarkoff,
      normalizedPolynomial_swap12, normalizedPolynomial_swap23]

private theorem cageSecondPointCanonicalEquiv_preserves_surface
    {R : Type*} [CommRing R]
    (axis other : NormalizedCoordinateAxis) (x : NormalizedPoint R) :
    IsNormalizedMarkoff ((cageSecondPointCanonicalEquiv R axis other) x) ↔
      IsNormalizedMarkoff x := by
  cases axis <;> cases other <;>
    simp [cageSecondPointCanonicalEquiv, normalizedSwap12Equiv,
      normalizedSwap23Equiv, IsNormalizedMarkoff,
      normalizedPolynomial_swap12, normalizedPolynomial_swap23]

/-- The inverse coordinate permutations reconstruct a witness on the original
ordered pair of axes. -/
def canonicalCageMiddleWitnessToAxes
    (p : ℕ) [Fact p.Prime]
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p) :
    CageMiddleWitnessPair p .first .second xi eta →
      CageMiddleWitnessPair p axis other xi eta := fun z => by
  let firstPoint :=
    (cageFirstPointCanonicalEquiv (ZMod p) axis other).symm z.1.1
  let secondPoint :=
    (cageSecondPointCanonicalEquiv (ZMod p) axis other).symm z.1.2
  refine ⟨(firstPoint, secondPoint), ?_⟩
  cases axis <;> cases other <;>
    simp [firstPoint, secondPoint, cageFirstPointCanonicalEquiv,
      cageSecondPointCanonicalEquiv, normalizedSwap12Equiv,
      normalizedSwap23Equiv,
      normalizedSwap12, normalizedSwap23, normalizedFiberAt,
      normalizedCoordinateAt, cageBridgeAxis] at z ⊢
  all_goals
    rcases z.2 with ⟨⟨hFirstSurface, hxi⟩,
      ⟨⟨hSecondSurface, heta⟩, hmiddle⟩⟩
    exact ⟨⟨by
      dsimp [IsNormalizedMarkoff, normalizedPolynomial,
        normalizedSwap12, normalizedSwap23] at hFirstSurface ⊢
      ring_nf at hFirstSurface ⊢
      exact hFirstSurface, hxi⟩,
      ⟨⟨by
        dsimp [IsNormalizedMarkoff, normalizedPolynomial,
          normalizedSwap12, normalizedSwap23] at hSecondSurface ⊢
        ring_nf at hSecondSurface ⊢
        exact hSecondSurface, heta⟩,
        hmiddle⟩⟩

/-- Cage witness pairs for arbitrary axes are canonically equivalent to the
first--second model used by the plane equations. -/
def cageMiddleWitnessEquivCanonical
    (p : ℕ) [Fact p.Prime]
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p) :
    CageMiddleWitnessPair p axis other xi eta ≃
      CageMiddleWitnessPair p .first .second xi eta where
  toFun := cageMiddleWitnessToCanonical p axis other xi eta
  invFun := canonicalCageMiddleWitnessToAxes p axis other xi eta
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> apply NormalizedPoint.ext <;>
      cases axis <;> cases other <;> rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> apply NormalizedPoint.ext <;>
      cases axis <;> cases other <;> rfl

/-- Canonicalizing the axes preserves the common middle trace exactly. -/
@[simp]
theorem cageMiddleWitnessEquivCanonical_trace
    (p : ℕ) [Fact p.Prime]
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p)
    (z : CageMiddleWitnessPair p axis other xi eta) :
    cageMiddleWitnessTrace
        (cageMiddleWitnessEquivCanonical p axis other xi eta z) =
      cageMiddleWitnessTrace z := by
  cases axis <;> cases other <;> rfl

/-- Axis canonicalization extends to the one-sided power-range solutions used
by the cage point count. -/
def cageMiddleWitnessPowerRangeEquivCanonical
    (p : ℕ) [Fact p.Prime]
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p) (d : ℕ) :
    cageMiddleWitnessPowerRangeSolutions p axis other xi eta d ≃
      cageMiddleWitnessPowerRangeSolutions p .first .second xi eta d where
  toFun z := ⟨(cageMiddleWitnessEquivCanonical p axis other xi eta z.1.1, z.1.2), by
    simpa using z.2⟩
  invFun z := ⟨((cageMiddleWitnessEquivCanonical p axis other xi eta).symm z.1.1,
      z.1.2), by
    have htrace := cageMiddleWitnessEquivCanonical_trace
      p axis other xi eta
      ((cageMiddleWitnessEquivCanonical p axis other xi eta).symm z.1.1)
    calc
      cageMiddleWitnessTrace
          ((cageMiddleWitnessEquivCanonical p axis other xi eta).symm z.1.1) =
          cageMiddleWitnessTrace
            (cageMiddleWitnessEquivCanonical p axis other xi eta
              ((cageMiddleWitnessEquivCanonical p axis other xi eta).symm z.1.1)) :=
        htrace.symm
      _ = cageMiddleWitnessTrace z.1.1 := by
        rw [(cageMiddleWitnessEquivCanonical p axis other xi eta).apply_symm_apply]
      _ = splitTorusTrace z.1.2 := z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (cageMiddleWitnessEquivCanonical p axis other xi eta).left_inv z.1.1
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (cageMiddleWitnessEquivCanonical p axis other xi eta).right_inv z.1.1
    · rfl

/-- The witness-bearing cage count is independent of the chosen ordered pair
of outer coordinate axes. -/
theorem natCard_cageMiddleWitnessPowerRangeSolutions_eq_canonical
    (p : ℕ) [Fact p.Prime]
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod p) (d : ℕ) :
    Nat.card (cageMiddleWitnessPowerRangeSolutions p axis other xi eta d) =
      Nat.card (cageMiddleWitnessPowerRangeSolutions
        p .first .second xi eta d) :=
  Nat.card_congr
    (cageMiddleWitnessPowerRangeEquivCanonical p axis other xi eta d)

end

end BGS.Markoff
