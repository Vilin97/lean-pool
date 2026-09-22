/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.GeneralFiniteExtensionRiemannLower
import Mathlib.Order.OrderIsoNat
import Mathlib.Tactic

/-!
# Eventual exact growth of one-point Riemann spaces

A coarse Riemann lower bound and the one-place principal-parts upper bound
already force eventual exact linear growth.  For a place `P`, define the
surplus

`dim L(nP) + g - (n deg(P) + 1)`.

The lower bound makes this a natural number without truncation, while the
one-place increment bound makes it antitone.  Since a decreasing sequence of
natural numbers is eventually constant, `dim L((n+1)P) - dim L(nP)` is
eventually exactly `deg(P)`.

This is the elementary stabilization input used in the divisor-class proof
of zeta rationality; it does not assume Riemann--Roch or a zeta theorem.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The bounded nonnegative error in a one-point Riemann lower bound. -/
def finiteExtensionOnePointRiemannSurplus
    (P : FiniteExtensionPlace K L) (g n : ℕ) : ℕ :=
  Module.finrank K (finiteExtensionOnePointRiemannSpace K L P n) + g -
    (n * finiteExtensionPlaceDegree K L P + 1)

/-- The Riemann surplus is antitone: adding one copy of the pole place raises
dimension by at most the degree of that place. -/
theorem finiteExtensionOnePointRiemannSurplus_antitone_of_lower
    (P : FiniteExtensionPlace K L) (g : ℕ)
    (hLower : ∀ n : ℕ,
      n * finiteExtensionPlaceDegree K L P + 1 ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P n) + g) :
    Antitone (finiteExtensionOnePointRiemannSurplus K L P g) := by
  apply antitone_nat_of_succ_le
  intro n
  let D : FiniteExtensionDivisor K L := Finsupp.single P (n : ℤ)
  have hD : ∀ v, 0 ≤ D v := by
    intro v
    by_cases hv : v = P
    · subst v
      simp [D]
    · simp [D, Finsupp.single_eq_of_ne hv]
  let : Module.Finite K (finiteExtensionRiemannSpace K L D) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L D hD
  have hinc := finiteExtensionRiemannSpace_place_increment K L D hD P
  have hdivisor : D + Finsupp.single P 1 =
      Finsupp.single P ((n + 1 : ℕ) : ℤ) := by
    ext v
    by_cases hv : v = P
    · subst v
      simp [D]
    · simp [D, Finsupp.single_eq_of_ne hv]
  have hfinrank :
      Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P (n + 1)) ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P n) +
            finiteExtensionPlaceDegree K L P := by
    change Module.finrank K (finiteExtensionRiemannSpace K L
        (Finsupp.single P (((n + 1 : ℕ) : ℤ)))) ≤
      Module.finrank K (finiteExtensionRiemannSpace K L
        (Finsupp.single P (n : ℤ))) + finiteExtensionPlaceDegree K L P
    rw [← hdivisor]
    simpa only [D] using hinc.2
  have hn := hLower n
  have hsucc := hLower (n + 1)
  simp only [finiteExtensionOnePointRiemannSurplus, Nat.succ_mul] at hsucc ⊢
  omega

/-- Any one-point Riemann lower bound implies that the dimension increment is
eventually exactly the place degree. -/
theorem finiteExtensionOnePointRiemannSpace_eventually_exact_increment
    (P : FiniteExtensionPlace K L) (g : ℕ)
    (hLower : ∀ n : ℕ,
      n * finiteExtensionPlaceDegree K L P + 1 ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P n) + g) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P (n + 1)) =
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P n) +
          finiteExtensionPlaceDegree K L P := by
  have hanti :=
    finiteExtensionOnePointRiemannSurplus_antitone_of_lower
      K L P g hLower
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨N, ?_⟩
  intro n hn
  have heq : finiteExtensionOnePointRiemannSurplus K L P g n =
      finiteExtensionOnePointRiemannSurplus K L P g (n + 1) :=
    (hN n hn).symm.trans (hN (n + 1) (hn.trans (Nat.le_succ n)))
  have hlowN := hLower n
  have hlowSucc := hLower (n + 1)
  simp only [finiteExtensionOnePointRiemannSurplus, Nat.succ_mul] at heq hlowSucc
  omega

end

end BGS.HasseWeil
