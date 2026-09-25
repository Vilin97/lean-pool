/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Cage.PlaneHasseWeil
public import LeanPool.MarkoffModP.BGS.Markoff.Cage.WitnessEquations

/-!
# The one-sided power cover of the cage witness equations

This file identifies the exact `d`-fold cover counted before passage to the
power-map range with the two pulled radicand equations.  Both incidence roots
remain part of the data.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

/-- Clearing the denominator in one incidence equation gives exactly the
pulled radicand. -/
lemma scaled_incidenceEquation_iff_pulledRadicand
    (u xi root : K) (hu : u ≠ 0) (d : ℕ) :
    (xi ^ 2 - 4) * (u ^ d + (u ^ d)⁻¹) ^ 2 - root ^ 2 = 4 * xi ^ 2 ↔
      (u ^ d * root) ^ 2 = (cagePulledRadicand xi d).eval u := by
  rw [cagePulledRadicand]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_one]
  have hpow : u ^ (2 * d) = (u ^ d) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [hpow]
  have hud : u ^ d ≠ 0 := pow_ne_zero d hu
  have hclear :
      (u ^ d) ^ 2 *
          ((xi ^ 2 - 4) * (u ^ d + (u ^ d)⁻¹) ^ 2 - root ^ 2) =
        (xi ^ 2 - 4) * ((u ^ d) ^ 2 + 1) ^ 2 -
          (u ^ d) ^ 2 * root ^ 2 := by
    field_simp [hud]
  constructor
  · intro h
    have hscaled :
        (xi ^ 2 - 4) * ((u ^ d) ^ 2 + 1) ^ 2 -
            (u ^ d) ^ 2 * root ^ 2 =
          (u ^ d) ^ 2 * (4 * xi ^ 2) := by
      rw [← hclear, h]
    calc
      (u ^ d * root) ^ 2 = (u ^ d) ^ 2 * root ^ 2 := by ring
      _ = (xi ^ 2 - 4) * ((u ^ d) ^ 2 + 1) ^ 2 -
          4 * xi ^ 2 * (u ^ d) ^ 2 := by
        linear_combination -hscaled
  · intro h
    apply (mul_left_cancel₀ (pow_ne_zero 2 hud))
    calc
      (u ^ d) ^ 2 *
          ((xi ^ 2 - 4) * (u ^ d + (u ^ d)⁻¹) ^ 2 - root ^ 2) =
        (xi ^ 2 - 4) * ((u ^ d) ^ 2 + 1) ^ 2 -
          (u ^ d) ^ 2 * root ^ 2 := hclear
      _ = (u ^ d) ^ 2 * (4 * xi ^ 2) := by
        linear_combination -h
      _ = (u ^ d) ^ 2 * (4 * xi ^ 2) := rfl

/-- The exact pulled pair of quadratic roots over a nonzero power parameter. -/
structure CagePulledRootPair
    (p : ℕ) [Fact p.Prime] (xi eta : ZMod p) (d : ℕ) where
  /-- The parameter before applying the `d`-th power map. -/
  parameter : (ZMod p)ˣ
  /-- The first denominator-cleared incidence root. -/
  firstRoot : ZMod p
  /-- The second denominator-cleared incidence root. -/
  secondRoot : ZMod p
  /-- First pulled radicand equation. -/
  firstEquation :
    firstRoot ^ 2 = (cagePulledRadicand xi d).eval (parameter : ZMod p)
  /-- Second pulled radicand equation. -/
  secondEquation :
    secondRoot ^ 2 = (cagePulledRadicand eta d).eval (parameter : ZMod p)

@[ext]
lemma CagePulledRootPair.ext
    {p : ℕ} [Fact p.Prime] {xi eta : ZMod p} {d : ℕ}
    {x y : CagePulledRootPair p xi eta d}
    (hparameter : x.parameter = y.parameter)
    (hfirst : x.firstRoot = y.firstRoot)
    (hsecond : x.secondRoot = y.secondRoot) : x = y := by
  cases x
  cases y
  simp_all

/-- The canonical witness-bearing one-sided cover. -/
abbrev canonicalCagePowerCoverSolutions
    (p : ℕ) [Fact p.Prime] (xi eta : ZMod p) (d : ℕ) :=
  BGS.rightPowerTraceCoverSolutions
    (cageMiddleWitnessTrace (p := p) (axis := .first) (other := .second)
      (xi := xi) (eta := eta))
    (splitTorusTrace : (ZMod p)ˣ → ZMod p) d

/-- Scale the two retained incidence roots by the common denominator. -/
def canonicalCagePowerCoverToPulled
    (p : ℕ) [Fact p.Prime] (xi eta : ZMod p) (d : ℕ) :
    canonicalCagePowerCoverSolutions p xi eta d →
      CagePulledRootPair p xi eta d := fun z => by
  let equations := canonicalCageWitnessToEquations p xi eta z.1.1
  let parameter := z.1.2
  have hmiddle : equations.middle = splitTorusTrace (parameter ^ d) := by
    simpa [equations, parameter, canonicalCageWitnessToEquations,
      cageMiddleWitnessTrace, normalizedCoordinateAt, cageBridgeAxis] using z.2
  refine
    { parameter := parameter
      firstRoot := (parameter : ZMod p) ^ d * equations.firstRoot
      secondRoot := (parameter : ZMod p) ^ d * equations.secondRoot
      firstEquation := ?_
      secondEquation := ?_ }
  · apply (scaled_incidenceEquation_iff_pulledRadicand
      (parameter : ZMod p) xi equations.firstRoot parameter.ne_zero d).mp
    have htrace :
        (parameter : ZMod p) ^ d + ((parameter : ZMod p) ^ d)⁻¹ =
          splitTorusTrace (parameter ^ d) := by
      simp [splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact equations.firstEquation
  · apply (scaled_incidenceEquation_iff_pulledRadicand
      (parameter : ZMod p) eta equations.secondRoot parameter.ne_zero d).mp
    have htrace :
        (parameter : ZMod p) ^ d + ((parameter : ZMod p) ^ d)⁻¹ =
          splitTorusTrace (parameter ^ d) := by
      simp [splitTorusTrace]
    rw [htrace, ← hmiddle]
    exact equations.secondEquation

/-- Recover the unscaled incidence roots and the two actual Markoff points. -/
def canonicalCagePulledToPowerCover
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) (d : ℕ) :
    CagePulledRootPair p xi eta d →
      canonicalCagePowerCoverSolutions p xi eta d := fun z => by
  let q : ZMod p := (z.parameter : ZMod p) ^ d
  have hq : q ≠ 0 := pow_ne_zero d z.parameter.ne_zero
  let equations : CageIncidenceEquationWitness p xi eta :=
    { middle := splitTorusTrace (z.parameter ^ d)
      firstRoot := q⁻¹ * z.firstRoot
      secondRoot := q⁻¹ * z.secondRoot
      firstEquation := by
        have h := (scaled_incidenceEquation_iff_pulledRadicand
          (z.parameter : ZMod p) xi (q⁻¹ * z.firstRoot)
          z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.firstEquation)
        simpa [splitTorusTrace] using h
      secondEquation := by
        have h := (scaled_incidenceEquation_iff_pulledRadicand
          (z.parameter : ZMod p) eta (q⁻¹ * z.secondRoot)
          z.parameter.ne_zero d).mpr (by
            simpa [q, hq] using z.secondEquation)
        simpa [splitTorusTrace] using h }
  let witness := canonicalCageEquationsToWitness p hpTwo xi eta equations
  refine ⟨(witness, z.parameter), ?_⟩
  simp [witness, equations, canonicalCageEquationsToWitness,
    cageMiddleWitnessTrace, normalizedCoordinateAt, cageBridgeAxis]

@[simp]
lemma canonicalCageWitnessToEquations_equationsToWitness
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) (z : CageIncidenceEquationWitness p xi eta) :
    canonicalCageWitnessToEquations p xi eta
        (canonicalCageEquationsToWitness p hpTwo xi eta z) = z := by
  exact (canonicalCageWitnessEquivIncidenceEquations
    p hpTwo xi eta).apply_symm_apply z

/-- The canonical one-sided cage power cover is exactly the pulled pair of
radicand equations. -/
def canonicalCagePowerCoverEquivPulled
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) (d : ℕ) :
    canonicalCagePowerCoverSolutions p xi eta d ≃
      CagePulledRootPair p xi eta d where
  toFun := canonicalCagePowerCoverToPulled p xi eta d
  invFun := canonicalCagePulledToPowerCover p hpTwo xi eta d
  left_inv := by
    intro z
    have hTwo : (2 : ZMod p) ≠ 0 := by
      exact two_ne_zero_zmod
        (lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hpTwo))
    have hxiCoordinate : z.1.1.1.1.u1 = xi := by
      simpa [normalizedFiberAt] using z.1.1.2.1.2
    have hetaCoordinate : z.1.1.1.2.u2 = eta := by
      simpa [normalizedFiberAt] using z.1.1.2.2.1.2
    have hmiddleFirst : z.1.1.1.1.u3 = splitTorusTrace (z.1.2 ^ d) := by
      simpa [cageMiddleWitnessTrace, normalizedCoordinateAt,
        cageBridgeAxis] using z.2
    have hmiddleCommon : z.1.1.1.1.u3 = z.1.1.1.2.u3 := by
      simpa [normalizedCoordinateAt, cageBridgeAxis] using z.1.1.2.2.2
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext <;> apply NormalizedPoint.ext
      · simpa [canonicalCagePowerCoverToPulled,
          canonicalCagePulledToPowerCover,
          canonicalCageWitnessToEquations,
          canonicalCageEquationsToWitness] using hxiCoordinate.symm
      · simp [canonicalCagePowerCoverToPulled,
          canonicalCagePulledToPowerCover,
          canonicalCageWitnessToEquations,
          canonicalCageEquationsToWitness]
        rw [← hmiddleFirst]
        field_simp [hTwo]
        ring
      · simpa [canonicalCagePowerCoverToPulled,
          canonicalCagePulledToPowerCover,
          canonicalCageWitnessToEquations,
          canonicalCageEquationsToWitness] using hmiddleFirst.symm
      · simp [canonicalCagePowerCoverToPulled,
          canonicalCagePulledToPowerCover,
          canonicalCageWitnessToEquations,
          canonicalCageEquationsToWitness]
        rw [← hmiddleFirst]
        field_simp [hTwo]
        ring
      · simpa [canonicalCagePowerCoverToPulled,
          canonicalCagePulledToPowerCover,
          canonicalCageWitnessToEquations,
          canonicalCageEquationsToWitness] using hetaCoordinate.symm
      · simpa [canonicalCagePowerCoverToPulled,
          canonicalCagePulledToPowerCover,
          canonicalCageWitnessToEquations,
          canonicalCageEquationsToWitness] using
            hmiddleFirst.symm.trans hmiddleCommon
    · rfl
  right_inv := by
    intro z
    apply CagePulledRootPair.ext
    · rfl
    · simp [canonicalCagePowerCoverToPulled,
        canonicalCagePulledToPowerCover,
        canonicalCageWitnessToEquations_equationsToWitness]
    · simp [canonicalCagePowerCoverToPulled,
        canonicalCagePulledToPowerCover,
        canonicalCageWitnessToEquations_equationsToWitness]

/-- Exact division of the pulled affine cover by the `d`-th power-map
fibers. -/
theorem natCard_cagePulledRootPair_eq_mul_canonicalPowerRange
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (xi eta : ZMod p) (d : ℕ) (hd : d ∣ p - 1) :
    Nat.card (CagePulledRootPair p xi eta d) =
      d * Nat.card (cageMiddleWitnessPowerRangeSolutions
        p .first .second xi eta d) := by
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hdCard : d ∣ Nat.card (ZMod p)ˣ := by
    rw [hcard]
    exact hd
  let : Finite (CageMiddleWitnessPair p .first .second xi eta) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  calc
    Nat.card (CagePulledRootPair p xi eta d) =
        Nat.card (canonicalCagePowerCoverSolutions p xi eta d) :=
      Nat.card_congr (canonicalCagePowerCoverEquivPulled
        p hpTwo xi eta d).symm
    _ = d * Nat.card (cageMiddleWitnessPowerRangeSolutions
          p .first .second xi eta d) := by
      simpa [canonicalCagePowerCoverSolutions,
        cageMiddleWitnessPowerRangeSolutions] using
          (BGS.natCard_rightPowerTraceCoverSolutions_of_dvd
            (cageMiddleWitnessTrace
              (p := p) (axis := .first) (other := .second)
              (xi := xi) (eta := eta))
            (splitTorusTrace : (ZMod p)ˣ → ZMod p) d hdCard)

end

end BGS.Markoff
