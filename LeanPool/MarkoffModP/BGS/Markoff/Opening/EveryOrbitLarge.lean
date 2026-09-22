/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Opening.OrbitCardBound
import LeanPool.MarkoffModP.BGS.Markoff.Core.Statements

/-!
# The logarithmic lower-bound half of Theorem 1

The opening proves the exact inequality `p ≤ 20 ^ m ^ 3` for every punctured orbit of cardinality
`m`.  This file performs the analytic conversion that the paper calls immediate and packages it
with the quantifiers of `EveryOrbitLargeAt` and `TheoremOneStatement`.
-/

namespace BGS.Markoff

noncomputable section

/-- Forgetting the proof that a point is nonzero maps its punctured orbit onto its orbit in the
full Markoff surface. -/
theorem subtypeVal_image_puncturedGammaOrbit
    {R : Type*} [CommRing R] (x : PuncturedMarkoffSurface R) :
    Subtype.val '' puncturedGammaOrbit x = gammaOrbit x.1 := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ∃ g : Gamma R, g • x.1 = z.1
    change ∃ g : Gamma R, g • x = z at hz
    obtain ⟨g, rfl⟩ := hz
    exact ⟨g, rfl⟩
  · intro hy
    change ∃ g : Gamma R, g • x.1 = y at hy
    obtain ⟨g, hgy⟩ := hy
    refine ⟨g • x, ?_, ?_⟩
    · change ∃ h : Gamma R, h • x = g • x
      exact ⟨g, rfl⟩
    · exact hgy

/-- Puncturing does not change the cardinality of a nonzero Gamma orbit. -/
theorem puncturedGammaOrbit_ncard_eq_gammaOrbit_ncard
    {R : Type*} [CommRing R] (x : PuncturedMarkoffSurface R) :
    (puncturedGammaOrbit x).ncard = (gammaOrbit x.1).ncard := by
  rw [← subtypeVal_image_puncturedGammaOrbit x]
  exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm

/-- Punctured-orbit form of the exact opening inequality. -/
theorem prime_le_twenty_pow_puncturedGammaOrbit_ncard_cube
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (hpThree : p ≠ 3)
    (x : PuncturedMarkoffSurface (ZMod p)) :
    p ≤ 20 ^ (puncturedGammaOrbit x).ncard ^ 3 := by
  have hxne : x.1.1 ≠ origin := by
    intro hx
    apply x.2
    apply Subtype.ext
    exact hx
  have h := prime_le_twenty_pow_gammaOrbit_ncard_cube p hpTwo hpThree x.1 hxne
  rwa [puncturedGammaOrbit_ncard_eq_gammaOrbit_ncard]

/-- The exact exponential opening bound implies a uniform cube-root logarithmic lower bound.
The deliberately coarse constant `1 / 3` avoids introducing an artificial transcendental
constant into Theorem 1. -/
theorem one_third_mul_log_rpow_le_of_prime_le_twenty_pow_cube
    (p orbitCard : ℕ) (hp : p.Prime)
    (hbound : p ≤ 20 ^ orbitCard ^ 3) :
    (1 / 3 : ℝ) * Real.rpow (Real.log p) (1 / 3 : ℝ) ≤ orbitCard := by
  have hpOne : 1 ≤ p := hp.one_le
  have hpRealPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogNonnegative : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpOne)
  have hboundReal : (p : ℝ) ≤ (20 : ℝ) ^ (orbitCard ^ 3) := by
    exact_mod_cast hbound
  have hlogBound :
      Real.log (p : ℝ) ≤ (orbitCard ^ 3 : ℕ) * Real.log (20 : ℝ) := by
    calc
      Real.log (p : ℝ) ≤ Real.log ((20 : ℝ) ^ (orbitCard ^ 3)) :=
        Real.log_le_log hpRealPos hboundReal
      _ = (orbitCard ^ 3 : ℕ) * Real.log (20 : ℝ) := by
        rw [Real.log_pow]
  have hlogTwenty : Real.log (20 : ℝ) ≤ 27 := by
    calc
      Real.log (20 : ℝ) ≤ 20 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ ≤ 27 := by norm_num
  have hlogBoundCoarse :
      Real.log (p : ℝ) ≤ 27 * (orbitCard : ℝ) ^ 3 := by
    calc
      Real.log (p : ℝ) ≤ (orbitCard ^ 3 : ℕ) * Real.log (20 : ℝ) := hlogBound
      _ ≤ (orbitCard ^ 3 : ℕ) * 27 := by
        gcongr
      _ = 27 * (orbitCard : ℝ) ^ 3 := by
        norm_num [mul_comm]
  have hcuberootNonnegative :
      0 ≤ Real.rpow (Real.log (p : ℝ)) (1 / 3 : ℝ) :=
    Real.rpow_nonneg hlogNonnegative _
  have hcuberootCube :
      (Real.rpow (Real.log (p : ℝ)) (1 / 3 : ℝ)) ^ 3 = Real.log (p : ℝ) := by
    calc
      (Real.rpow (Real.log (p : ℝ)) (1 / 3 : ℝ)) ^ 3 =
          Real.rpow (Real.log (p : ℝ)) ((1 / 3 : ℝ) * (3 : ℕ)) :=
        (Real.rpow_mul_natCast hlogNonnegative (1 / 3 : ℝ) 3).symm
      _ = Real.log (p : ℝ) := by norm_num
  have hleftNonnegative :
      0 ≤ (1 / 3 : ℝ) * Real.rpow (Real.log (p : ℝ)) (1 / 3 : ℝ) := by
    positivity
  have horbitNonnegative : (0 : ℝ) ≤ orbitCard := by positivity
  apply (pow_le_pow_iff_left₀ hleftNonnegative horbitNonnegative (by norm_num : 3 ≠ 0)).mp
  rw [mul_pow, hcuberootCube]
  norm_num
  nlinarith

/-- Every punctured orbit over every prime `p ≥ 5` satisfies the lower bound in Theorem 1 with
the absolute constant `1 / 3`. -/
theorem everyOrbitLargeAt_one_third
    (p : ℕ) (hp : p.Prime) (hpFive : 5 ≤ p) :
    EveryOrbitLargeAt p hp (1 / 3 : ℝ) := by
  let : Fact p.Prime := ⟨hp⟩
  intro x
  exact one_third_mul_log_rpow_le_of_prime_le_twenty_pow_cube
    p (puncturedGammaOrbit x).ncard hp
    (prime_le_twenty_pow_puncturedGammaOrbit_ncard_cube p (by omega) (by omega) x)

/-- The second conjunct of `TheoremOneStatement`, including its absolute constant and threshold,
is completely formalized. -/
theorem theoremOne_everyOrbitLarge :
    ∃ c : ℝ, 0 < c ∧
      ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → EveryOrbitLargeAt p hp c := by
  refine ⟨1 / 3, by norm_num, 5, ?_⟩
  intro p hp hpFive
  exact everyOrbitLargeAt_one_third p hp hpFive

/-- With the every-orbit lower bound now proved, `TheoremOneStatement` is reduced exactly to its
giant-orbit conjunct. -/
theorem theoremOneStatement_of_eventually_hasGiantOrbit
    (hgiant :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → HasGiantOrbitAt p hp epsilon) :
    TheoremOneStatement :=
  ⟨hgiant, theoremOne_everyOrbitLarge⟩

end


end BGS.Markoff
