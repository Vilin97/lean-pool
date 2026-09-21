/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.SuccessorLeibniz
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.LoweringDerivation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.DerivAtInjective

/-!
# API checks for the Leibniz identities on the spaces `P_α`

The degree-one approach-zero series `a` has a nonzero class in `P_1`. Its
square exercises the two-term identity `eventually_of_derivAt_mul_of_pos`; the check
records that neither endpoint term is degenerate, because the class of `a` is nonzero and the
values `∂(a)(γ)` are not eventually zero. A nonzero constant `k`, of degree `0`, against
`a` exercises the one-term identity `eventually_of_derivAt_mul_of_eq_zero`, and the
Leibniz rule `principalSubringDerivation_mul` of `∂ : P̂ → Fun_{0⁻}(P̂)` then reads
`∂(a k) = k ∂(a)`, since `∂` vanishes on scalars. The zero series is the degenerate case.

The nearest wrong statement is an unconditional two-term identity in which the factor of degree
`0` or a limit ordinal contributes `π_α(u) π_β(v^{|γ})` with `π_β(v^{|γ})` the class of the
translated truncation in `P_β` itself. At degree `β = 0` that class vanishes termwise, which the
last check records, so the present fixture certifies the branch where the degree is a limit ordinal
but does not separate it from the unconditional identity; the two differ only when `β ≥ ω` is a
limit ordinal, for which there
there is no fixture in the test suite.
-/

open Filter Topology
open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Tests

open Berarducci

private theorem one_constantCoeff_pos : 0 < (1 : NatOrdinal).constantCoeff := by
  have hcoeff : (1 : NatOrdinal).constantCoeff = 1 := by
    simpa only [Nat.cast_one] using NatOrdinal.constantCoeff_natCast (1 : ℕ)
  rw [hcoeff]
  decide

private theorem approachZero_ordinalValue_bound :
    ordinalValue approachZeroNonpositive < ω^ ((1 : NatOrdinal) + 1) := by
  rw [ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal approachZero_degree_eq_one]
  exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one (1 : NatOrdinal))

/-- The degree-one class of the approach-zero series. -/
def approachZeroClass : PrincipalComponent ℚ 1 :=
  principalComponentMk 1 approachZeroNonpositive approachZero_ordinalValue_bound

/-- The approach-zero class is nonzero in `P_1`. -/
theorem approachZeroClass_ne_zero : approachZeroClass ≠ 0 := by
  intro hzero
  have hlower := (principalComponentMk_eq_zero_iff 1 approachZeroNonpositive
    approachZero_ordinalValue_bound).mp hzero
  rw [ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal approachZero_degree_eq_one]
    at hlower
  exact lt_irrefl _ hlower

/-! ### Both grades successors: two endpoint terms -/

/-- The Leibniz identity for `a · a` in `P_{(1+1)⁻}`: near zero, the cutoff class of `(a a)^{|γ}`
is `π_{1⁻}(a^{|γ}) π_1(a) + π_1(a) π_{1⁻}(a^{|γ})`. -/
theorem approachZero_sq_leibniz :
    ∀ᶠ γ in 𝓝[<] (0 : ℝ),
      DirectSum.of (PrincipalComponent ℚ) (((1 : NatOrdinal) + 1).removeNat 1)
          (derivAt (1 + 1) (approachZeroNonpositive * approachZeroNonpositive) γ) =
        DirectSum.of (PrincipalComponent ℚ) ((1 : NatOrdinal).removeNat 1)
              (derivAt 1 approachZeroNonpositive γ) *
            DirectSum.of (PrincipalComponent ℚ) 1 approachZeroClass +
          DirectSum.of (PrincipalComponent ℚ) 1 approachZeroClass *
            DirectSum.of (PrincipalComponent ℚ) ((1 : NatOrdinal).removeNat 1)
              (derivAt 1 approachZeroNonpositive γ) :=
  eventually_of_derivAt_mul_of_pos one_constantCoeff_pos one_constantCoeff_pos
    approachZeroNonpositive approachZeroNonpositive approachZero_ordinalValue_bound
    approachZero_ordinalValue_bound

/-- Neither endpoint term of `approachZero_sq_leibniz` is degenerate: the values `∂(a)(γ)` are
not eventually zero, because `∂` of the class of `a` is nonzero. -/
theorem approachZero_derivAt_not_eventually_zero :
    ¬ ∀ᶠ γ in 𝓝[<] (0 : ℝ), derivAt 1 approachZeroNonpositive γ = 0 := by
  intro h
  apply principalComponentDerivAt_ne_zero 1 one_constantCoeff_pos
    approachZeroClass_ne_zero
  rw [approachZeroClass, principalComponentDerivAt_principalComponentMk, ← Filter.Germ.coe_zero,
    Filter.Germ.coe_eq]
  exact h

/-! ### A limit-grade factor: one endpoint term -/

/-- The Leibniz identity for `a · k` with `k` a constant of limit grade `0`: near zero, the
cutoff class of `(a k)^{|γ}` in `P_{(1+0)⁻}` is the single term `π_{1⁻}(a^{|γ}) π_0(k)`. -/
theorem approachZero_mul_C_leibniz (k : ℚ) :
    ∀ᶠ γ in 𝓝[<] (0 : ℝ),
      DirectSum.of (PrincipalComponent ℚ) (((1 : NatOrdinal) + 0).removeNat 1)
          (derivAt (1 + 0)
            (approachZeroNonpositive * HahnSeries.Nonpositive.C k) γ) =
        DirectSum.of (PrincipalComponent ℚ) ((1 : NatOrdinal).removeNat 1)
            (derivAt 1 approachZeroNonpositive γ) *
          DirectSum.of (PrincipalComponent ℚ) 0
            (principalComponentMk 0 (HahnSeries.Nonpositive.C k) (ordinalValue_C_lt_wpow_one k)) :=
  eventually_of_derivAt_mul_of_eq_zero one_constantCoeff_pos
    NatOrdinal.constantCoeff_zero approachZeroNonpositive _ approachZero_ordinalValue_bound
    (ordinalValue_C_lt_wpow_one k)

/-- The homogeneous inclusion of the approach-zero class in `P̂`. -/
def approachZeroElement : PrincipalSubring ℚ :=
  DirectSum.of (PrincipalComponent ℚ) 1 approachZeroClass

/-- The Leibniz rule of `Δ` against a scalar: `Δ(a k) = k • Δ(a)`, the scalar term vanishing
because `Δ` is zero on the limit grade `0`. -/
theorem principalSubringDerivation_approachZero_mul_algebraMap (k : ℚ) :
    principalSubringDerivation ℚ
        (approachZeroElement * algebraMap ℚ (PrincipalSubring ℚ) k) =
      k • principalSubringDerivation ℚ approachZeroElement := by
  rw [principalSubringDerivation_mul, principalSubringDerivation_algebraMap, mul_zero, add_zero,
    FunAtZeroMinus.mul_const_algebraMap]

/-- At grade `0` the would-be second endpoint term vanishes termwise: for `γ < 0` the cutoff
class of a constant is zero, since its translated truncation at `γ` is the zero series. -/
theorem derivAt_C_eq_zero (k : ℚ) {γ : ℝ} (hγ : γ < 0) :
    derivAt 0 (HahnSeries.Nonpositive.C k) γ = 0 := by
  have hzero : translatedTruncation ((HahnSeries.Nonpositive.C k : Series ℚ) : ℚ⟦ℝ⟧) γ = 0 := by
    apply Subtype.ext
    ext δ
    rw [coeff_translatedTruncation, HahnSeries.Nonpositive.coe_C, HahnSeries.C_apply,
      HahnSeries.coeff_single, ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
    split_ifs with hδ hsum
    · exact absurd hsum (by linarith)
    · rfl
    · rfl
  have hbound : ordinalValue (translatedTruncation ((HahnSeries.Nonpositive.C k : Series ℚ) : ℚ⟦ℝ⟧)
      γ) <
      ω^ ((0 : NatOrdinal).removeNat 1 + 1) := by
    rw [hzero, ordinalValue_zero]
    exact NatOrdinal.wpow_pos _
  rw [derivAt_eq 0 _ γ hbound, principalComponentMk_eq_zero_iff, hzero, ordinalValue_zero]
  exact NatOrdinal.wpow_pos _

/-! ### The degenerate case -/

/-- The values `∂(0)(γ)` of the zero series are zero. -/
theorem derivAt_zero (γ : ℝ) :
    derivAt 1 (0 : Series ℚ) γ = 0 := by
  have hbound : ordinalValue (translatedTruncation ((0 : Series ℚ) : ℚ⟦ℝ⟧) γ) <
      ω^ ((1 : NatOrdinal).removeNat 1 + 1) := by
    rw [ZeroMemClass.coe_zero, translatedTruncation_zero_input, ordinalValue_zero]
    exact NatOrdinal.wpow_pos _
  rw [derivAt_eq 1 0 γ hbound, principalComponentMk_eq_zero_iff, ZeroMemClass.coe_zero,
    translatedTruncation_zero_input, ordinalValue_zero]
  exact NatOrdinal.wpow_pos _

/-- The Leibniz rule at the zero element: both sides of `principalSubringDerivation_mul` vanish. -/
theorem principalSubringDerivation_zero_mul (x : PrincipalSubring ℚ) :
    principalSubringDerivation ℚ (0 * x) = 0 ∧
      principalSubringDerivation ℚ 0 * (x : FunAtZeroMinus (PrincipalSubring ℚ)) +
        ((0 : PrincipalSubring ℚ) : FunAtZeroMinus (PrincipalSubring ℚ)) *
          principalSubringDerivation ℚ x = 0 := by
  refine ⟨by rw [zero_mul, map_zero], ?_⟩
  rw [map_zero, zero_mul, FunAtZeroMinus.const_zero, zero_mul, add_zero]

end Tests
