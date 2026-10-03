/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.AverageRemainder
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.QuadraticTrap.AmbientEstimate

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Line-integral endpoint estimates

This file packages the calculus bookkeeping used at the final Taylor-expansion step of the
Aleksandrov proof. Once a line-restriction increment is represented by an integral whose
integrand is uniformly close to the affine model
`inner ℝ p z + t * inner ℝ z (B z)`, the endpoint affine remainder is close to the quadratic
model `(1 / 2) * inner ℝ z (B z)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open Set
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Line-restriction version of interval-integrability of the right derivative on an interval
contained in the interior line domain. -/
theorem ConvexOn.lineRestriction_intervalIntegrable_rightDeriv_of_uIcc_subset_interior
    {s : Set E} {u : E → ℝ} {x v : E} {a b : ℝ}
    (hu : ConvexOn ℝ s u)
    (hinterval : Set.uIcc a b ⊆ interior (lineDomain s x v)) :
    IntervalIntegrable
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v)) volume a b :=
  ConvexOn.intervalIntegrable_rightDeriv_of_uIcc_subset_interior
    (S := lineDomain s x v)
    (f := AleksandrovDifferentiability.lineRestriction u x v)
    (ConvexOn.lineRestriction (x := x) (v := v) hu) hinterval

/-- Line-restriction version of the right-derivative FTC identity on an interval contained in the
interior line domain. -/
theorem ConvexOn.lineRestriction_integral_rightDeriv_eq_sub_of_uIcc_subset_interior
    {s : Set E} {u : E → ℝ} {x v : E} {a b : ℝ}
    (hu : ConvexOn ℝ s u)
    (hinterval : Set.uIcc a b ⊆ interior (lineDomain s x v)) :
    ∫ t in a..b, rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t =
      AleksandrovDifferentiability.lineRestriction u x v b -
        AleksandrovDifferentiability.lineRestriction u x v a :=
  ConvexOn.integral_rightDeriv_eq_sub_of_uIcc_subset_interior
    (S := lineDomain s x v)
    (f := AleksandrovDifferentiability.lineRestriction u x v)
    (ConvexOn.lineRestriction (x := x) (v := v) hu) hinterval

/-- Endpoint-subtraction orientation of
`ConvexOn.lineRestriction_integral_rightDeriv_eq_sub_of_uIcc_subset_interior`. -/
theorem ConvexOn.lineRestriction_sub_eq_integral_rightDeriv_of_uIcc_subset_interior
    {s : Set E} {u : E → ℝ} {x v : E} {a b : ℝ}
    (hu : ConvexOn ℝ s u)
    (hinterval : Set.uIcc a b ⊆ interior (lineDomain s x v)) :
    AleksandrovDifferentiability.lineRestriction u x v b -
        AleksandrovDifferentiability.lineRestriction u x v a =
      ∫ t in a..b, rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t :=
  (ConvexOn.lineRestriction_integral_rightDeriv_eq_sub_of_uIcc_subset_interior
    (x := x) (v := v) hu hinterval).symm

/-- Ambient endpoint form of the unit-interval integration estimate.

In the source proof this is the last line-segment integration step: for
`φ(t) = u (x + t • z)`, a uniform model bound on the derivative-like integrand by
`p · z + t z · B z` gives the quadratic Taylor remainder estimate at `x + z`. -/
theorem norm_affineRemainder_sub_quadratic_le_of_line_integral_model_bound
    {u : E → ℝ} {x p z : E} {B : E →L[ℝ] E} {g : ℝ → ℝ} {R : ℝ}
    (hrepr :
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, g t)
    (hint : IntervalIntegrable g volume (0 : ℝ) 1)
    (hbound :
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖g t - (inner ℝ p z + t * inner ℝ z (B z))‖ ≤ R) :
    ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤ R := by
  have hunit :=
    norm_unit_interval_remainder_le_of_integral_model_bound
      (f := lineRestriction u x z) (g := g)
      (a := inner ℝ p z) (q := inner ℝ z (B z)) (R := R)
      hrepr hint hbound
  simpa [lineRestriction, affineRemainder, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    using hunit

/-- Right-derivative specialization of
`norm_affineRemainder_sub_quadratic_le_of_line_integral_model_bound`.

This is the form closest to the source proof's notation
`φ'_+(t) = sup {p · z : p ∈ ∂u(x + t z)}`. The hypotheses deliberately keep the
one-dimensional FTC representation and integrability explicit; later convex-analysis lemmas
should supply them for sufficiently short segments. -/
theorem norm_affineRemainder_sub_quadratic_le_of_line_rightDeriv_model_bound
    {u : E → ℝ} {x p z : E} {B : E →L[ℝ] E} {R : ℝ}
    (hrepr :
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hbound :
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖rightDeriv (lineRestriction u x z) t -
          (inner ℝ p z + t * inner ℝ z (B z))‖ ≤ R) :
    ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤ R :=
  norm_affineRemainder_sub_quadratic_le_of_line_integral_model_bound
    (u := u) (x := x) (p := p) (z := z) (B := B)
    (g := rightDeriv (lineRestriction u x z)) (R := R)
    hrepr hint hbound

/-- Convert subgradient linearization along a segment into the right-derivative endpoint
quadratic estimate, assuming the source proof's support-function identity is available along the
line.

The hypothesis `hrightSubgradient` is the remaining convex-analysis bridge in this local form:
for each parameter `t ∈ (0,1]`, the right derivative of the line restriction is realized by
pairing the segment direction with some ambient subgradient at `x + t • z`. -/
theorem HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineRightDeriv
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach)
    (hrepr : ∀ᶠ z in 𝓝 (0 : E),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : E),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hrightSubgradient : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : E,
          SubgradientOn domain u (x + t • z) p ∧
            rightDeriv (lineRestriction u x z) t = inner ℝ p z) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : E),
      ‖affineRemainder u x p₀ (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
        ε * ‖z‖ ^ 2 := by
  intro ε hε
  filter_upwards [
    HasSubgradientLinearizationOnAt.eventually_segment_inner_estimates hlin hsegment ε hε,
    hrepr,
    hint,
    hrightSubgradient] with z hzseg hzrepr hzint hzright
  refine norm_affineRemainder_sub_quadratic_le_of_line_rightDeriv_model_bound
    (u := u) (x := x) (p := p₀) (z := z) (B := B)
    (R := ε * ‖z‖ ^ 2) hzrepr hzint ?_
  intro t ht
  rcases hzright t ht with ⟨p, hp, hright⟩
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa using ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
  have hbound := hzseg t htIcc p hp
  simpa [hright, Real.norm_eq_abs] using hbound

/-- Version of `HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineRightDeriv`
whose remaining support-function input is stated as a lift of arbitrary line subgradients to
ambient subgradients. Convexity supplies the fact that the right derivative is a line
subgradient. -/
theorem HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineSubgradientLift
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hu : ConvexOn ℝ domain u)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach)
    (hsegmentInterior : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior domain)
    (hrepr : ∀ᶠ z in 𝓝 (0 : E),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : E),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hlift : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain domain x z) (lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient domain u x z t q) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : E),
      ‖affineRemainder u x p₀ (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
        ε * ‖z‖ ^ 2 :=
  HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineRightDeriv
    hlin hsegment hrepr hint
    (ConvexOn.eventually_lineRightDeriv_realized_by_subgradient_of_lineSubgradientLift
      (s := domain) (u := u) (x := x) hu hsegmentInterior hlift)

/-- Functional-lift version of
`HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineSubgradientLift`.

This is the form intended for the eventual separation proof: the ambient lift of each line
subgradient may be supplied by a supporting continuous linear functional, and Fréchet-Riesz
converts it to the vector-valued subgradient used by `SubgradientOn`. -/
theorem HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineSubgradientFunctional
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    [CompleteSpace E]
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hu : ConvexOn ℝ domain u)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach)
    (hsegmentInterior : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior domain)
    (hrepr : ∀ᶠ z in 𝓝 (0 : E),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : E),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hlift : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain domain x z) (lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional domain u x z t q) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : E),
      ‖affineRemainder u x p₀ (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
        ε * ‖z‖ ^ 2 := by
  have hsegmentDomain : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ domain := by
    filter_upwards [hsegmentInterior] with z hz t ht
    exact interior_subset (hz t ht)
  exact
    HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineSubgradientLift
      hlin hu hsegment hsegmentInterior hrepr hint
      (eventually_lineSubgradientLiftsToAmbient_of_functional hsegmentDomain hlift)

/-- Expansion form of
`HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineRightDeriv`.

This is the local Taylor conclusion before the separate symmetry requirement needed by
`SecondOrderDifferentiableAt`. -/
theorem HasSubgradientLinearizationOnAt.hasSecondOrderExpansionAt_of_lineRightDeriv
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach)
    (hrepr : ∀ᶠ z in 𝓝 (0 : E),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : E),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hrightSubgradient : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : E,
          SubgradientOn domain u (x + t • z) p ∧
            rightDeriv (lineRestriction u x z) t = inner ℝ p z) :
    HasSecondOrderExpansionAt u x p₀ B :=
by
  refine hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul ?_
  intro ε hε
  exact
    HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineRightDeriv
      hlin hsegment hrepr hint hrightSubgradient ε hε

/-- Expansion form using the line-subgradient lift interface. -/
theorem HasSubgradientLinearizationOnAt.hasSecondOrderExpansionAt_of_lineSubgradientLift
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hu : ConvexOn ℝ domain u)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach)
    (hsegmentInterior : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior domain)
    (hrepr : ∀ᶠ z in 𝓝 (0 : E),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : E),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hlift : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain domain x z) (lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient domain u x z t q) :
    HasSecondOrderExpansionAt u x p₀ B :=
by
  refine hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul ?_
  intro ε hε
  exact
    HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineSubgradientLift
      hlin hu hsegment hsegmentInterior hrepr hint hlift ε hε

/-- Expansion form using the functional line-subgradient lift interface. -/
theorem HasSubgradientLinearizationOnAt.hasSecondOrderExpansionAt_of_lineSubgradientFunctional
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    [CompleteSpace E]
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hu : ConvexOn ℝ domain u)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach)
    (hsegmentInterior : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior domain)
    (hrepr : ∀ᶠ z in 𝓝 (0 : E),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : E),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hlift : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain domain x z) (lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional domain u x z t q) :
    HasSecondOrderExpansionAt u x p₀ B :=
by
  refine hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul ?_
  intro ε hε
  exact
    HasSubgradientLinearizationOnAt.eventually_quadraticBound_of_lineSubgradientFunctional
      hlin hu hsegment hsegmentInterior hrepr hint hlift ε hε

/-- Second-order differentiability form of
`HasSubgradientLinearizationOnAt.hasSecondOrderExpansionAt_of_lineRightDeriv`.

The operator produced by gradient linearization need not be separately shown symmetric here:
`SecondOrderDifferentiableAt` is obtained using its symmetric part, which has the same quadratic
form. -/
theorem HasSubgradientLinearizationOnAt.secondOrderDifferentiableAt_of_lineRightDeriv
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    [CompleteSpace E]
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach)
    (hrepr : ∀ᶠ z in 𝓝 (0 : E),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : E),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hrightSubgradient : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : E,
          SubgradientOn domain u (x + t • z) p ∧
            rightDeriv (lineRestriction u x z) t = inner ℝ p z) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt_symmetricPart
    (HasSubgradientLinearizationOnAt.hasSecondOrderExpansionAt_of_lineRightDeriv
      hlin hsegment hrepr hint hrightSubgradient)

/-- Second-order differentiability form using the line-subgradient lift interface.

As in the right-derivative version, the symmetric part of the linearized operator is used for the
final Hessian witness. -/
theorem HasSubgradientLinearizationOnAt.secondOrderDifferentiableAt_of_lineSubgradientLift
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    [CompleteSpace E]
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hu : ConvexOn ℝ domain u)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach)
    (hsegmentInterior : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior domain)
    (hrepr : ∀ᶠ z in 𝓝 (0 : E),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : E),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hlift : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain domain x z) (lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient domain u x z t q) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt_symmetricPart
    (HasSubgradientLinearizationOnAt.hasSecondOrderExpansionAt_of_lineSubgradientLift
      hlin hu hsegment hsegmentInterior hrepr hint hlift)

/-- Second-order differentiability form using the functional line-subgradient lift interface. -/
theorem HasSubgradientLinearizationOnAt.secondOrderDifferentiableAt_of_lineSubgradientFunctional
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    [CompleteSpace E]
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hu : ConvexOn ℝ domain u)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach)
    (hsegmentInterior : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior domain)
    (hrepr : ∀ᶠ z in 𝓝 (0 : E),
      lineRestriction u x z 1 - lineRestriction u x z 0 =
        ∫ t in (0 : ℝ)..1, rightDeriv (lineRestriction u x z) t)
    (hint : ∀ᶠ z in 𝓝 (0 : E),
      IntervalIntegrable (rightDeriv (lineRestriction u x z)) volume (0 : ℝ) 1)
    (hlift : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain domain x z) (lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional domain u x z t q) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt_symmetricPart
    (HasSubgradientLinearizationOnAt.hasSecondOrderExpansionAt_of_lineSubgradientFunctional
      hlin hu hsegment hsegmentInterior hrepr hint hlift)

end AleksandrovDifferentiability
