/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannEventualGrowth
public import Mathlib.Tactic

/-!
# Eventual growth after an effective divisor shift

The one-point stabilization theorem is extended here from `L(nP)` to
`L(D + nP)`, where `D` is any effective exhaustive divisor.  The hypotheses
retain only the two estimates used in the proof:

* principal parts bound each one-step dimension increase by `deg(P)`; and
* an arbitrary coarse affine lower bound prevents an unbounded deficit.

Thus the lower-bound intercept is a parameter rather than a genus formula.
Once the associated natural-number surplus stabilizes, dimensions grow by
exactly `deg(P)` at every subsequent step.  Over a finite constant field this
also gives an exact formula for the cardinalities of the shifted Riemann
spaces.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The divisor obtained by adding `n` copies of `P` to `D`. -/
abbrev finiteExtensionRiemannShiftDivisor
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L)
    (n : ℕ) : FiniteExtensionDivisor K L :=
  D + Finsupp.single P (n : ℤ)

/-- The nonnegative error in an affine lower bound for
`dim L(D + nP)`. -/
def finiteExtensionShiftedRiemannSurplus
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L)
    (intercept error n : ℕ) : ℕ :=
  Module.finrank K
      (finiteExtensionRiemannSpace K L
        (finiteExtensionRiemannShiftDivisor K L D P n)) + error -
    (n * finiteExtensionPlaceDegree K L P + intercept)

/-- For effective `D`, a coarse affine lower bound makes the shifted
Riemann surplus antitone. -/
theorem finiteExtensionShiftedRiemannSurplus_antitone_of_lower
    (D : FiniteExtensionDivisor K L) (hD : ∀ v, 0 ≤ D v)
    (P : FiniteExtensionPlace K L) (intercept error : ℕ)
    (hLower : ∀ n : ℕ,
      n * finiteExtensionPlaceDegree K L P + intercept ≤
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P n)) + error) :
    Antitone
      (finiteExtensionShiftedRiemannSurplus K L D P intercept error) := by
  apply antitone_nat_of_succ_le
  intro n
  let E : FiniteExtensionDivisor K L :=
    finiteExtensionRiemannShiftDivisor K L D P n
  have hE : ∀ v, 0 ≤ E v := by
    intro v
    by_cases hv : v = P
    · subst v
      have hn : (0 : ℤ) ≤ n := by positivity
      simpa [E, finiteExtensionRiemannShiftDivisor] using
        add_nonneg (hD P) hn
    · simpa [E, finiteExtensionRiemannShiftDivisor,
          Finsupp.single_eq_of_ne hv] using hD v
  let : Module.Finite K (finiteExtensionRiemannSpace K L E) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L E hE
  have hinc := finiteExtensionRiemannSpace_place_increment K L E hE P
  have hdivisor : E + Finsupp.single P 1 =
      finiteExtensionRiemannShiftDivisor K L D P (n + 1) := by
    ext v
    by_cases hv : v = P
    · subst v
      simp [E, finiteExtensionRiemannShiftDivisor]
      ring
    · simp [E, finiteExtensionRiemannShiftDivisor,
        Finsupp.single_eq_of_ne hv]
  have hfinrank :
      Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P (n + 1))) ≤
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P n)) +
          finiteExtensionPlaceDegree K L P := by
    rw [← hdivisor]
    simpa only [E] using hinc.2
  have hn := hLower n
  have hsucc := hLower (n + 1)
  simp only [finiteExtensionShiftedRiemannSurplus, Nat.succ_mul] at hsucc ⊢
  omega

/-- A coarse affine lower bound forces the dimensions of `L(D + nP)` to
eventually increase by exactly `deg(P)` at every step. -/
theorem finiteExtensionRiemannSpace_shift_eventually_exact_increment
    (D : FiniteExtensionDivisor K L) (hD : ∀ v, 0 ≤ D v)
    (P : FiniteExtensionPlace K L) (intercept error : ℕ)
    (hLower : ∀ n : ℕ,
      n * finiteExtensionPlaceDegree K L P + intercept ≤
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P n)) + error) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P (n + 1))) =
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P n)) +
          finiteExtensionPlaceDegree K L P := by
  have hanti :=
    finiteExtensionShiftedRiemannSurplus_antitone_of_lower
      K L D hD P intercept error hLower
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨N, ?_⟩
  intro n hn
  have heq :
      finiteExtensionShiftedRiemannSurplus K L D P intercept error n =
        finiteExtensionShiftedRiemannSurplus K L D P intercept error (n + 1) :=
    (hN n hn).symm.trans (hN (n + 1) (hn.trans (Nat.le_succ n)))
  have hlowN := hLower n
  have hlowSucc := hLower (n + 1)
  simp only [finiteExtensionShiftedRiemannSurplus, Nat.succ_mul] at heq hlowSucc
  omega

/-- Iterating exact successive increments gives the closed dimension formula
from any stabilization index. -/
theorem finiteExtensionRiemannSpace_shift_closedFormula_of_exact_increment
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L)
    (N : ℕ)
    (hIncrement : ∀ n : ℕ, N ≤ n →
      Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P (n + 1))) =
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P n)) +
          finiteExtensionPlaceDegree K L P) :
    ∀ m : ℕ,
      Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P (N + m))) =
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P N)) +
          m * finiteExtensionPlaceDegree K L P := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := hIncrement (N + m) (Nat.le_add_right N m)
      calc
        Module.finrank K
            (finiteExtensionRiemannSpace K L
              (finiteExtensionRiemannShiftDivisor K L D P (N + (m + 1)))) =
            Module.finrank K
              (finiteExtensionRiemannSpace K L
                (finiteExtensionRiemannShiftDivisor K L D P ((N + m) + 1))) := by
              rw [Nat.add_succ]
        _ = Module.finrank K
              (finiteExtensionRiemannSpace K L
                (finiteExtensionRiemannShiftDivisor K L D P (N + m))) +
              finiteExtensionPlaceDegree K L P := hstep
        _ = (Module.finrank K
              (finiteExtensionRiemannSpace K L
                (finiteExtensionRiemannShiftDivisor K L D P N)) +
              m * finiteExtensionPlaceDegree K L P) +
              finiteExtensionPlaceDegree K L P := by rw [ih]
        _ = Module.finrank K
              (finiteExtensionRiemannSpace K L
                (finiteExtensionRiemannShiftDivisor K L D P N)) +
              (m + 1) * finiteExtensionPlaceDegree K L P := by
                rw [Nat.add_mul, one_mul]
                omega

/-- Eventual exact affine dimension growth for `L(D + nP)`. -/
theorem finiteExtensionRiemannSpace_shift_eventually_closedFormula
    (D : FiniteExtensionDivisor K L) (hD : ∀ v, 0 ≤ D v)
    (P : FiniteExtensionPlace K L) (intercept error : ℕ)
    (hLower : ∀ n : ℕ,
      n * finiteExtensionPlaceDegree K L P + intercept ≤
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P n)) + error) :
    ∃ N : ℕ, ∀ m : ℕ,
      Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P (N + m))) =
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P N)) +
          m * finiteExtensionPlaceDegree K L P := by
  obtain ⟨N, hN⟩ :=
    finiteExtensionRiemannSpace_shift_eventually_exact_increment
      K L D hD P intercept error hLower
  exact ⟨N,
    finiteExtensionRiemannSpace_shift_closedFormula_of_exact_increment
      K L D P N hN⟩

/-- Cardinality form of eventual exact affine growth.  It is stated without
division: after stabilization, adding `mP` multiplies the number of Riemann
space elements by `|K| ^ (m * deg(P))`. -/
theorem finiteExtensionRiemannSpace_shift_eventually_cardinality_formula
    (D : FiniteExtensionDivisor K L) (hD : ∀ v, 0 ≤ D v)
    (P : FiniteExtensionPlace K L) (intercept error : ℕ)
    (hLower : ∀ n : ℕ,
      n * finiteExtensionPlaceDegree K L P + intercept ≤
        Module.finrank K
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P n)) + error) :
    ∃ N : ℕ, ∀ m : ℕ,
      Nat.card
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P (N + m))) =
        Nat.card
          (finiteExtensionRiemannSpace K L
            (finiteExtensionRiemannShiftDivisor K L D P N)) *
          Nat.card K ^ (m * finiteExtensionPlaceDegree K L P) := by
  obtain ⟨N, hN⟩ := finiteExtensionRiemannSpace_shift_eventually_closedFormula
    K L D hD P intercept error hLower
  refine ⟨N, ?_⟩
  intro m
  have hDN : ∀ v,
      0 ≤ finiteExtensionRiemannShiftDivisor K L D P N v := by
    intro v
    by_cases hv : v = P
    · subst v
      have hNnonneg : (0 : ℤ) ≤ N := by positivity
      simpa [finiteExtensionRiemannShiftDivisor] using
        add_nonneg (hD P) hNnonneg
    · simpa [finiteExtensionRiemannShiftDivisor,
          Finsupp.single_eq_of_ne hv] using hD v
  have hDNm : ∀ v,
      0 ≤ finiteExtensionRiemannShiftDivisor K L D P (N + m) v := by
    intro v
    by_cases hv : v = P
    · subst v
      have hNmnonneg : (0 : ℤ) ≤ N + m := by positivity
      simpa [finiteExtensionRiemannShiftDivisor] using
        add_nonneg (hD P) hNmnonneg
    · simpa [finiteExtensionRiemannShiftDivisor,
          Finsupp.single_eq_of_ne hv] using hD v
  let : Module.Finite K
      (finiteExtensionRiemannSpace K L
        (finiteExtensionRiemannShiftDivisor K L D P N)) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L _ hDN
  let : Module.Finite K
      (finiteExtensionRiemannSpace K L
        (finiteExtensionRiemannShiftDivisor K L D P (N + m))) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L _ hDNm
  rw [Module.natCard_eq_pow_finrank (K := K), hN m, pow_add,
    ← Module.natCard_eq_pow_finrank (K := K)]

end

end BGS.HasseWeil
