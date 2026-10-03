/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Cage.WitnessEquations
public import LeanPool.MarkoffModP.BGS.Markoff.Incidence.CoordinateRing
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.Diagonalization

/-!
# Geometry of the normalized cage incidence curve

The cage uses normalized trace coordinates, whereas the incidence geometry
already proved in `IncidenceCoordinateRing` uses the paper's original Markoff
coordinates.  This file supplies the missing exact scaling bridge.  Dividing
the trace, common coordinate, and both retained roots by three identifies the
two pairs of quadratic equations.

The off-diagonal geometric-integrality theorem below therefore reuses the
existing biquadratic coordinate-ring proof.  It does not assert geometric
integrality of the subsequent power-trace pullback; that is the next Kummer
obligation in the cage Hasse--Weil argument.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

/-- The two retained incidence equations in normalized trace coordinates. -/
def NormalizedIncidenceAux (xi eta middle firstRoot secondRoot : K) : Prop :=
  (xi ^ 2 - 4) * middle ^ 2 - firstRoot ^ 2 = 4 * xi ^ 2 ∧
    (eta ^ 2 - 4) * middle ^ 2 - secondRoot ^ 2 = 4 * eta ^ 2

/-- A witness-bearing point of the original-coordinate incidence auxiliary curve. -/
structure IncidenceAuxEquationWitness (K : Type*) [Field K] (a b : K) where
  /-- The common original-coordinate incidence parameter. -/
  middle : K
  /-- The retained root for the first quadratic equation. -/
  firstRoot : K
  /-- The retained root for the second quadratic equation. -/
  secondRoot : K
  /-- Both original-coordinate incidence equations. -/
  equations : IncidenceAux a b middle firstRoot secondRoot

@[ext]
theorem IncidenceAuxEquationWitness.ext
    {a b : K} {x y : IncidenceAuxEquationWitness K a b}
    (hmiddle : x.middle = y.middle)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot) : x = y := by
  cases x
  cases y
  simp_all

/-- Dividing all five normalized coordinates by three gives exactly the
original-coordinate incidence equations. -/
theorem normalizedIncidenceAux_iff_incidenceAux_div_three
    (h3 : (3 : K) ≠ 0) (xi eta middle firstRoot secondRoot : K) :
    NormalizedIncidenceAux xi eta middle firstRoot secondRoot ↔
      IncidenceAux (xi / 3) (eta / 3) (middle / 3)
        (firstRoot / 3) (secondRoot / 3) := by
  have scaledEquation (trace root : K) :
      (trace ^ 2 - 4) * middle ^ 2 - root ^ 2 = 4 * trace ^ 2 ↔
        (9 * (trace / 3) ^ 2 - 4) * (middle / 3) ^ 2 - (root / 3) ^ 2 =
          4 * (trace / 3) ^ 2 := by
    let originalResidual :=
      (trace ^ 2 - 4) * middle ^ 2 - root ^ 2 - 4 * trace ^ 2
    let scaledResidual :=
      (9 * (trace / 3) ^ 2 - 4) * (middle / 3) ^ 2 - (root / 3) ^ 2 -
        4 * (trace / 3) ^ 2
    have hscale : (9 : K) * scaledResidual = originalResidual := by
      dsimp [scaledResidual, originalResidual]
      field_simp [h3]
      ring
    have h9 : (9 : K) ≠ 0 := by
      convert mul_ne_zero h3 h3 using 1
      norm_num
    constructor
    · intro h
      have hOriginal : originalResidual = 0 := by
        dsimp [originalResidual]
        exact sub_eq_zero.mpr h
      have hScaled : scaledResidual = 0 := by
        apply (mul_eq_zero.mp (hscale.trans hOriginal)).resolve_left h9
      dsimp [scaledResidual] at hScaled
      exact sub_eq_zero.mp hScaled
    · intro h
      have hScaled : scaledResidual = 0 := by
        dsimp [scaledResidual]
        exact sub_eq_zero.mpr h
      have hOriginal : originalResidual = 0 := by
        rw [← hscale, hScaled, mul_zero]
      dsimp [originalResidual] at hOriginal
      exact sub_eq_zero.mp hOriginal
  constructor
  · rintro ⟨hfirst, hsecond⟩
    exact ⟨(scaledEquation xi firstRoot).mp hfirst,
      (scaledEquation eta secondRoot).mp hsecond⟩
  · rintro ⟨hfirst, hsecond⟩
    exact ⟨(scaledEquation xi firstRoot).mpr hfirst,
      (scaledEquation eta secondRoot).mpr hsecond⟩

/-- The normalized nondegeneracy conditions imply geometric integrality of
the proved original-coordinate model. -/
theorem normalizedIncidenceAuxGeometricallyIntegral_of_nondegenerate
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {xi eta : K}
    (hxi : xi ≠ 0) (heta : eta ≠ 0)
    (hXi : xi ^ 2 - 4 ≠ 0) (hEta : eta ^ 2 - 4 ≠ 0)
    (hneq : xi ^ 2 ≠ eta ^ 2) :
    IncidenceAuxGeometricallyIntegral (xi / 3) (eta / 3) := by
  apply incidenceAuxGeometricallyIntegral_of_nondegenerate h2
  · exact div_ne_zero hxi h3
  · exact div_ne_zero heta h3
  · have heq : 9 * (xi / 3) ^ 2 - 4 = xi ^ 2 - 4 := by
      field_simp [h3]
      ring
    rw [heq]
    exact hXi
  · have heq : 9 * (eta / 3) ^ 2 - 4 = eta ^ 2 - 4 := by
      field_simp [h3]
      ring
    rw [heq]
    exact hEta
  · intro h
    apply hneq
    calc
      xi ^ 2 = 9 * (xi / 3) ^ 2 := by field_simp [h3]; ring
      _ = 9 * (eta / 3) ^ 2 := by rw [h]
      _ = eta ^ 2 := by field_simp [h3]; ring

/-- The original-coordinate coordinate-ring model of the normalized cage
incidence curve.  The accompanying point equivalence below records the
coordinate scaling, rather than identifying the two coordinate systems. -/
abbrev NormalizedCageIncidenceCoordinateRing
    (K : Type*) [Field K] (xi eta : K) :=
  IncidenceAuxCoordinateRing K (xi / 3) (eta / 3)

/-- Geometric integrality of the normalized incidence curve through its
explicit original-coordinate model. -/
def NormalizedCageIncidenceGeometricallyIntegral
    {K : Type*} [Field K] (xi eta : K) : Prop :=
  IncidenceAuxGeometricallyIntegral (xi / 3) (eta / 3)

/-- A split-maximal cage trace is nonzero for the primes used by the cage. -/
theorem splitMaximalTrace_ne_zero
    (p : Nat) [Fact p.Prime] (hpSeven : 7 ≤ p) (t : ZMod p)
    (hmax : IsSplitMaximalTrace p t) : t ≠ 0 := by
  intro ht
  subst t
  have hle := rotationOrder_zero_le_four p
  rw [IsSplitMaximalTrace] at hmax
  rw [hmax] at hle
  omega

/-- A split-maximal cage trace is not parabolic. -/
theorem splitMaximalTrace_sq_ne_four
    (p : Nat) [Fact p.Prime] (hpSeven : 7 ≤ p) (t : ZMod p)
    (hmax : IsSplitMaximalTrace p t) : t ^ 2 ≠ 4 := by
  intro ht
  have htCases : t = 2 ∨ t = -2 := by
    apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    calc
      t ^ 2 = 4 := ht
      _ = (2 : ZMod p) ^ 2 := by norm_num
  rw [IsSplitMaximalTrace] at hmax
  rcases htCases with rfl | rfl
  · rw [rotationOrder_two] at hmax
    omega
  · rw [rotationOrder_neg_two p (by omega)] at hmax
    omega

/-- The off-diagonal base incidence curve occurring in the cage is
geometrically integral under the cage's actual split-maximal hypotheses. -/
theorem normalizedCageIncidence_offDiagonal_geometricallyIntegral
    (p : Nat) [Fact p.Prime] (hpSeven : 7 ≤ p) (xi eta : ZMod p)
    (hxi : IsSplitMaximalTrace p xi) (heta : IsSplitMaximalTrace p eta)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) :
    NormalizedCageIncidenceGeometricallyIntegral xi eta := by
  apply normalizedIncidenceAuxGeometricallyIntegral_of_nondegenerate
  · exact natCast_ne_zero_zmod_of_pos_of_lt (n := 2) (p := p) (by norm_num) (by omega)
  · exact natCast_ne_zero_zmod_of_pos_of_lt (n := 3) (p := p) (by norm_num) (by omega)
  · exact splitMaximalTrace_ne_zero p hpSeven xi hxi
  · exact splitMaximalTrace_ne_zero p hpSeven eta heta
  · exact sub_ne_zero.mpr (splitMaximalTrace_sq_ne_four p hpSeven xi hxi)
  · exact sub_ne_zero.mpr (splitMaximalTrace_sq_ne_four p hpSeven eta heta)
  · exact hoffDiagonal

/-- Witness-preserving equivalence between the normalized cage equations and
the original-coordinate incidence equations. -/
def cageIncidenceEquationWitnessScaleEquiv
    {p : Nat} [Fact p.Prime] (h3 : (3 : ZMod p) ≠ 0) (xi eta : ZMod p) :
    CageIncidenceEquationWitness p xi eta ≃
      IncidenceAuxEquationWitness (ZMod p) (xi / 3) (eta / 3) where
  toFun z :=
    { middle := z.middle / 3
      firstRoot := z.firstRoot / 3
      secondRoot := z.secondRoot / 3
      equations :=
        (normalizedIncidenceAux_iff_incidenceAux_div_three h3 xi eta
          z.middle z.firstRoot z.secondRoot).mp ⟨z.firstEquation, z.secondEquation⟩ }
  invFun z :=
    { middle := 3 * z.middle
      firstRoot := 3 * z.firstRoot
      secondRoot := 3 * z.secondRoot
      firstEquation := by
        have hscaled :
            IncidenceAux (xi / 3) (eta / 3) ((3 * z.middle) / 3)
              ((3 * z.firstRoot) / 3) ((3 * z.secondRoot) / 3) := by
          simpa [h3] using z.equations
        exact ((normalizedIncidenceAux_iff_incidenceAux_div_three h3 xi eta
          (3 * z.middle) (3 * z.firstRoot) (3 * z.secondRoot)).mpr hscaled).1
      secondEquation := by
        have hscaled :
            IncidenceAux (xi / 3) (eta / 3) ((3 * z.middle) / 3)
              ((3 * z.firstRoot) / 3) ((3 * z.secondRoot) / 3) := by
          simpa [h3] using z.equations
        exact ((normalizedIncidenceAux_iff_incidenceAux_div_three h3 xi eta
          (3 * z.middle) (3 * z.firstRoot) (3 * z.secondRoot)).mpr hscaled).2 }
  left_inv z := by
    apply CageIncidenceEquationWitness.ext <;> field_simp [h3]
  right_inv z := by
    apply IncidenceAuxEquationWitness.ext <;> simp [h3]

end

end BGS.Markoff
