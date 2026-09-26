/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.Statements
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.OrbitDivisibility

/-!
# From a giant divisible orbit to transitivity

The published version observes that a giant orbit with complement smaller than `p` is the whole
punctured Markoff surface if every orbit cardinality is divisible by `p`.  This module proves that
finite-orbit argument and combines it with Chen's component-divisibility theorem, using Martin's
later elementary proof.
-/

@[expose] public section

namespace BGS.Markoff

/-- If one orbit has complement smaller than `p` and every orbit cardinality is divisible by `p`,
then the action is transitive. -/
theorem puncturedMarkoffTransitiveAt_of_small_orbitComplement_and_orbitCard_dvd
    (p : ℕ) [Fact p.Prime]
    (x : PuncturedMarkoffSurface (ZMod p))
    (hsmall : orbitComplementCard x < p)
    (hdiv : ∀ y : PuncturedMarkoffSurface (ZMod p),
      p ∣ (puncturedGammaOrbit y).ncard) :
    PuncturedMarkoffTransitiveAt p Fact.out := by
  intro a b
  have hxAll : ∀ y : PuncturedMarkoffSurface (ZMod p),
      SamePuncturedComponent x y := by
    intro y
    by_contra hy
    have horbitSubset : puncturedGammaOrbit y ⊆ Set.univ \ puncturedGammaOrbit x := by
      intro z hz
      refine ⟨Set.mem_univ z, ?_⟩
      intro hzx
      apply hy
      exact samePuncturedComponent_trans hzx (samePuncturedComponent_symm hz)
    have horbitPos : 0 < (puncturedGammaOrbit y).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨y, samePuncturedComponent_refl y⟩
    have hpLeOrbit : p ≤ (puncturedGammaOrbit y).ncard :=
      Nat.le_of_dvd horbitPos (hdiv y)
    have horbitLeComplement :
        (puncturedGammaOrbit y).ncard ≤ orbitComplementCard x := by
      rw [orbitComplementCard]
      exact Set.ncard_le_ncard horbitSubset
    omega
  obtain ⟨ga, hga⟩ := (samePuncturedComponent_iff_exists x a).1 (hxAll a)
  obtain ⟨gb, hgb⟩ := (samePuncturedComponent_iff_exists x b).1 (hxAll b)
  refine ⟨gb * ga⁻¹, ?_⟩
  calc
    (gb * ga⁻¹) • a = gb • (ga⁻¹ • a) := mul_smul _ _ _
    _ = gb • x := by rw [← hga]; simp
    _ = b := hgb

/-- A `p^epsilon` giant-orbit bound with `epsilon < 1` has complement strictly smaller than `p`. -/
theorem exists_orbitComplementCard_lt_prime_of_hasGiantOrbitAt
    (p : ℕ) (hp : p.Prime) (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hgiant : HasGiantOrbitAt p hp epsilon) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ x : PuncturedMarkoffSurface (ZMod p), orbitComplementCard x < p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := hgiant
  refine ⟨x, ?_⟩
  have hpReal : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hrpow : (p : ℝ) ^ epsilon < (p : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hpReal hepsilon
  have hreal : (orbitComplementCard x : ℝ) < (p : ℝ) := hx.trans_lt hrpow
  exact_mod_cast hreal

/-- The published short route from a giant orbit and orbit-cardinality divisibility to
punctured finite-field transitivity at the given prime. -/
theorem puncturedMarkoffTransitiveAt_of_hasGiantOrbitAt_and_orbitCard_dvd
    (p : ℕ) (hp : p.Prime) (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hgiant : HasGiantOrbitAt p hp epsilon)
    (hdiv : letI : Fact p.Prime := ⟨hp⟩
      ∀ y : PuncturedMarkoffSurface (ZMod p),
        p ∣ (puncturedGammaOrbit y).ncard) :
    PuncturedMarkoffTransitiveAt p hp := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ :=
    exists_orbitComplementCard_lt_prime_of_hasGiantOrbitAt
      p hp epsilon hepsilon hgiant
  exact puncturedMarkoffTransitiveAt_of_small_orbitComplement_and_orbitCard_dvd p x hx hdiv

/-- Eventual giant-orbit control with any fixed exponent below one, combined with orbit
divisibility for primes larger than three, gives eventual punctured finite-field transitivity. -/
theorem eventually_puncturedMarkoffTransitiveAt_of_giantOrbit_and_orbitCard_dvd
    (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hgiant : ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p →
      HasGiantOrbitAt p hp epsilon)
    (hdiv : ∀ (p : ℕ) (hp : p.Prime), 3 < p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ y : PuncturedMarkoffSurface (ZMod p),
        p ∣ (puncturedGammaOrbit y).ncard) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p →
      PuncturedMarkoffTransitiveAt p hp := by
  obtain ⟨p0, hp0⟩ := hgiant
  refine ⟨max p0 4, fun p hp hple => ?_⟩
  have hp0le : p0 ≤ p := (Nat.le_max_left p0 4).trans hple
  have hpThree : 3 < p := by omega
  exact puncturedMarkoffTransitiveAt_of_hasGiantOrbitAt_and_orbitCard_dvd
    p hp epsilon hepsilon (hp0 p hp hp0le) (hdiv p hp hpThree)

/-- Chen's component-divisibility theorem, through Martin's elementary proof, turns any eventual
giant-orbit estimate with exponent below one into eventual punctured finite-field transitivity. -/
theorem eventually_puncturedMarkoffTransitiveAt_of_giantOrbit
    (epsilon : ℝ) (hepsilon : epsilon < 1)
    (hgiant : ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p →
      HasGiantOrbitAt p hp epsilon) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p →
      PuncturedMarkoffTransitiveAt p hp := by
  apply eventually_puncturedMarkoffTransitiveAt_of_giantOrbit_and_orbitCard_dvd
    epsilon hepsilon hgiant
  intro p hp hpThree
  let : Fact p.Prime := ⟨hp⟩
  intro y
  exact prime_dvd_puncturedGammaOrbit_ncard p hpThree y

end BGS.Markoff
