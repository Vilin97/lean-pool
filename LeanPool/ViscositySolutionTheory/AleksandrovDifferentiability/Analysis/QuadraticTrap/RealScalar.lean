/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.QuadraticTrap.AmbientEstimate

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Real scalar quadratic estimates

One-dimensional scalar quadratic estimate predicates and transport lemmas.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Real-line scalar form of the local quadratic estimate-to-expansion constructor. This is the
shape expected from one-dimensional estimates: the Hessian candidate is the scalar `q`, encoded as
`q` times the identity operator on `ℝ`. -/
theorem hasSecondOrderExpansionAt_real_of_eventually_norm_sub_quadratic_le_mul
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤ ε * ‖z‖ ^ 2) :
    HasSecondOrderExpansionAt f x p (q • (1 : ℝ →L[ℝ] ℝ)) := by
  refine hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul ?_
  intro ε hε
  filter_upwards [h ε hε] with z hz
  have hnorm :
      ‖affineRemainder f x p (x + z) -
          (1 / 2 : ℝ) * inner ℝ z ((q • (1 : ℝ →L[ℝ] ℝ)) z)‖ =
        ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ := by
    congr 1
    simp [affineRemainder, mul_assoc, mul_left_comm, mul_comm, pow_two]
    ring
  rw [hnorm]
  exact hz

/-- Real-line scalar form of the punctured normalized quadratic estimate-to-expansion
constructor. -/
theorem hasSecondOrderExpansionAt_real_of_eventually_norm_sub_quadratic_div_norm_sq_le
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
        ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ / ‖z‖ ^ 2 ≤ ε) :
    HasSecondOrderExpansionAt f x p (q • (1 : ℝ →L[ℝ] ℝ)) := by
  refine hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
    ?_
  intro ε hε
  filter_upwards [h ε hε] with z hz
  have hnorm :
      ‖affineRemainder f x p (x + z) -
          (1 / 2 : ℝ) * inner ℝ z ((q • (1 : ℝ →L[ℝ] ℝ)) z)‖ =
        ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ := by
    congr 1
    simp [affineRemainder, mul_assoc, mul_left_comm, mul_comm, pow_two]
    ring
  rw [hnorm]
  exact hz

/-- Real-line scalar form of the local quadratic estimate-to-second-order-differentiability
constructor. -/
theorem secondOrderDifferentiableAt_real_of_eventually_norm_sub_quadratic_le_mul
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤ ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAt f x := by
  refine ⟨p, q • (1 : ℝ →L[ℝ] ℝ), ?_,
    hasSecondOrderExpansionAt_real_of_eventually_norm_sub_quadratic_le_mul h⟩
  rw [IsSymmetricOperator]
  exact LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one

/-- Real-line scalar form of the punctured normalized quadratic
estimate-to-second-order-differentiability constructor. -/
theorem secondOrderDifferentiableAt_real_of_eventually_norm_sub_quadratic_div_norm_sq_le
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
        ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ / ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAt f x := by
  refine ⟨p, q • (1 : ℝ →L[ℝ] ℝ), ?_,
    hasSecondOrderExpansionAt_real_of_eventually_norm_sub_quadratic_div_norm_sq_le h⟩
  rw [IsSymmetricOperator]
  exact LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one

/-- Pointwise real-line scalar quadratic estimate data. This names the usual one-dimensional
target estimate before it is converted into the project second-order expansion predicate. -/
def RealScalarQuadraticEstimateAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ p : ℝ, ∃ q : ℝ,
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤ ε * ‖z‖ ^ 2

/-- Real-line scalar quadratic estimate data with the first-order and quadratic coefficients
specified explicitly. This is useful when several line estimates must share coefficients coming
from one ambient affine slope. -/
def RealScalarQuadraticEstimateWithDataAt (f : ℝ → ℝ) (x p q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z in nhds 0,
      ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤ ε * ‖z‖ ^ 2

/-- Punctured normalized quotient version of `RealScalarQuadraticEstimateAt`. -/
def RealScalarQuadraticQuotientEstimateAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ p : ℝ, ∃ q : ℝ,
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
        ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ / ‖z‖ ^ 2 ≤ ε

/-- Punctured normalized scalar quadratic quotient estimate with explicit coefficients. -/
def RealScalarQuadraticQuotientEstimateWithDataAt (f : ℝ → ℝ) (x p q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
      ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ / ‖z‖ ^ 2 ≤ ε

/-- Explicit scalar estimate data implies the existential scalar estimate predicate. -/
theorem RealScalarQuadraticEstimateWithDataAt.realScalarQuadraticEstimateAt
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : RealScalarQuadraticEstimateWithDataAt f x p q) :
    RealScalarQuadraticEstimateAt f x :=
  ⟨p, q, h⟩

/-- Explicit scalar quotient-estimate data implies the existential scalar quotient predicate. -/
theorem RealScalarQuadraticQuotientEstimateWithDataAt.realScalarQuadraticQuotientEstimateAt
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : RealScalarQuadraticQuotientEstimateWithDataAt f x p q) :
    RealScalarQuadraticQuotientEstimateAt f x :=
  ⟨p, q, h⟩

/-- Explicit scalar estimate data gives the explicit punctured normalized quotient estimate with
the same coefficients. -/
theorem RealScalarQuadraticEstimateWithDataAt.quadraticQuotientEstimateWithDataAt
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : RealScalarQuadraticEstimateWithDataAt f x p q) :
    RealScalarQuadraticQuotientEstimateWithDataAt f x p q := by
  intro ε hε
  filter_upwards [(h ε hε).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hz_ne
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz_ne)
  exact (div_le_iff₀ hden).mpr hz

/-- Two scalar quadratic estimates with the same base point and first-order coefficient can be
averaged in their quadratic coefficient. -/
theorem RealScalarQuadraticEstimateWithDataAt.average
    {f : ℝ → ℝ} {x p q q' : ℝ}
    (hq : RealScalarQuadraticEstimateWithDataAt f x p q)
    (hq' : RealScalarQuadraticEstimateWithDataAt f x p q') :
    RealScalarQuadraticEstimateWithDataAt f x p ((q + q') / 2) := by
  intro ε hε
  have hεpos : 0 < ε / 2 := by positivity
  filter_upwards [hq (ε / 2) hεpos, hq' (ε / 2) hεpos] with z hz hz'
  let A : ℝ := f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2
  let B : ℝ := f (x + z) - f x - p * z - (1 / 2 : ℝ) * q' * z ^ 2
  have hsplit :
      f (x + z) - f x - p * z - (1 / 2 : ℝ) * ((q + q') / 2) * z ^ 2 =
        (1 / 2 : ℝ) * A + (1 / 2 : ℝ) * B := by
    simp [A, B]
    ring
  calc
    ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * ((q + q') / 2) * z ^ 2‖ =
        ‖(1 / 2 : ℝ) * A + (1 / 2 : ℝ) * B‖ := by rw [hsplit]
    _ ≤ ‖(1 / 2 : ℝ) * A‖ + ‖(1 / 2 : ℝ) * B‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) * ‖A‖ + (1 / 2 : ℝ) * ‖B‖ := by
      simp [norm_mul]
    _ ≤ (1 / 2 : ℝ) * ((ε / 2) * ‖z‖ ^ 2) +
        (1 / 2 : ℝ) * ((ε / 2) * ‖z‖ ^ 2) := by
      gcongr
    _ = (ε / 2) * ‖z‖ ^ 2 := by ring
    _ ≤ ε * ‖z‖ ^ 2 := by
      gcongr
      linarith

/-- Quotient-form scalar estimates with the same base point and first-order coefficient can be
averaged in their quadratic coefficient. -/
theorem RealScalarQuadraticQuotientEstimateWithDataAt.average
    {f : ℝ → ℝ} {x p q q' : ℝ}
    (hq : RealScalarQuadraticQuotientEstimateWithDataAt f x p q)
    (hq' : RealScalarQuadraticQuotientEstimateWithDataAt f x p q') :
    RealScalarQuadraticQuotientEstimateWithDataAt f x p ((q + q') / 2) := by
  intro ε hε
  have hεpos : 0 < ε / 2 := by positivity
  filter_upwards [hq (ε / 2) hεpos, hq' (ε / 2) hεpos,
    self_mem_nhdsWithin] with z hz hz' hz_ne
  let A : ℝ := f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2
  let B : ℝ := f (x + z) - f x - p * z - (1 / 2 : ℝ) * q' * z ^ 2
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz_ne)
  have hsplit :
      f (x + z) - f x - p * z - (1 / 2 : ℝ) * ((q + q') / 2) * z ^ 2 =
        (1 / 2 : ℝ) * A + (1 / 2 : ℝ) * B := by
    simp [A, B]
    ring
  have hnorm :
      ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * ((q + q') / 2) * z ^ 2‖ ≤
        (ε / 2) * ‖z‖ ^ 2 := by
    calc
      ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * ((q + q') / 2) * z ^ 2‖ =
          ‖(1 / 2 : ℝ) * A + (1 / 2 : ℝ) * B‖ := by rw [hsplit]
      _ ≤ ‖(1 / 2 : ℝ) * A‖ + ‖(1 / 2 : ℝ) * B‖ := norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖A‖ + (1 / 2 : ℝ) * ‖B‖ := by
        simp [norm_mul]
      _ ≤ (1 / 2 : ℝ) * ((ε / 2) * ‖z‖ ^ 2) +
          (1 / 2 : ℝ) * ((ε / 2) * ‖z‖ ^ 2) := by
        have hA : ‖A‖ ≤ (ε / 2) * ‖z‖ ^ 2 := (div_le_iff₀ hden).mp hz
        have hB : ‖B‖ ≤ (ε / 2) * ‖z‖ ^ 2 := (div_le_iff₀ hden).mp hz'
        gcongr
      _ = (ε / 2) * ‖z‖ ^ 2 := by ring
  have hnorm' : ‖f (x + z) - f x - p * z -
        (1 / 2 : ℝ) * ((q + q') / 2) * z ^ 2‖ ≤ ε * ‖z‖ ^ 2 := by
    exact hnorm.trans (by
      gcongr
      linarith)
  exact (div_le_iff₀ hden).mpr hnorm'

/-- Scalar quadratic estimates are stable under rescaling the line parameter. This is the
coefficient bookkeeping behind replacing a line direction `v` by `c • v`. -/
theorem RealScalarQuadraticEstimateWithDataAt.comp_mul
    {f : ℝ → ℝ} {p q c : ℝ}
    (h : RealScalarQuadraticEstimateWithDataAt f 0 p q) :
    RealScalarQuadraticEstimateWithDataAt (fun t : ℝ => f (c * t)) 0 (c * p) (c ^ 2 * q) := by
  intro ε hε
  let δ : ℝ := ε / (‖c‖ ^ 2 + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hc_le : δ * ‖c‖ ^ 2 ≤ ε := by
    have hnonneg : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hden_pos : 0 < ‖c‖ ^ 2 + 1 := by positivity
    calc
      δ * ‖c‖ ^ 2 = ε * (‖c‖ ^ 2 / (‖c‖ ^ 2 + 1)) := by
        rw [show δ = ε / (‖c‖ ^ 2 + 1) by rfl]
        field_simp [ne_of_gt hden_pos]
      _ ≤ ε * 1 := by
        gcongr
        exact div_le_one_of_le₀ (by linarith) (by positivity)
      _ = ε := by ring
  have htend : Filter.Tendsto (fun t : ℝ => c * t) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun t : ℝ => c * t) 0 := by fun_prop
    simpa using hc.tendsto
  filter_upwards [htend.eventually (h δ hδ)] with t ht
  have hnorm :
      ‖f (c * t) - f 0 - (c * p) * t - (1 / 2 : ℝ) * (c ^ 2 * q) * t ^ 2‖ =
        ‖f (c * t) - f 0 - p * (c * t) - (1 / 2 : ℝ) * q * (c * t) ^ 2‖ := by
    congr 1
    ring
  have hbound :
      ‖f (c * t) - f 0 - (c * p) * t - (1 / 2 : ℝ) * (c ^ 2 * q) * t ^ 2‖ ≤
        ε * ‖t‖ ^ 2 := by
    rw [hnorm]
    calc
      ‖f (c * t) - f 0 - p * (c * t) - (1 / 2 : ℝ) * q * (c * t) ^ 2‖
          ≤ δ * ‖c * t‖ ^ 2 := by
            simpa [zero_add] using ht
      _ = (δ * ‖c‖ ^ 2) * ‖t‖ ^ 2 := by
        simp [norm_mul, mul_assoc, mul_left_comm, mul_comm, pow_two]
      _ ≤ ε * ‖t‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hc_le (sq_nonneg _)
  simpa [zero_add, mul_zero] using hbound

/-- Quotient-form scalar estimates are stable under rescaling the line parameter. -/
theorem RealScalarQuadraticQuotientEstimateWithDataAt.comp_mul
    {f : ℝ → ℝ} {p q c : ℝ}
    (h : RealScalarQuadraticQuotientEstimateWithDataAt f 0 p q) :
    RealScalarQuadraticQuotientEstimateWithDataAt
      (fun t : ℝ => f (c * t)) 0 (c * p) (c ^ 2 * q) := by
  intro ε hε
  by_cases hc : c = 0
  · filter_upwards [self_mem_nhdsWithin] with t ht_ne
    subst c
    simp [hε.le]
  · let δ : ℝ := ε / (‖c‖ ^ 2 + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hc_le : δ * ‖c‖ ^ 2 ≤ ε := by
      have hnonneg : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
      have hden_pos : 0 < ‖c‖ ^ 2 + 1 := by positivity
      calc
        δ * ‖c‖ ^ 2 = ε * (‖c‖ ^ 2 / (‖c‖ ^ 2 + 1)) := by
          rw [show δ = ε / (‖c‖ ^ 2 + 1) by rfl]
          field_simp [ne_of_gt hden_pos]
        _ ≤ ε * 1 := by
          gcongr
          exact div_le_one_of_le₀ (by linarith) (by positivity)
        _ = ε := by ring
    have htend :
        Filter.Tendsto (fun t : ℝ => c * t)
          (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0})
          (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0}) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun t : ℝ => c * t) 0 := by fun_prop
        have hbase : Filter.Tendsto (fun t : ℝ => c * t) (nhds 0) (nhds 0) := by
          simpa using hc.tendsto
        exact hbase.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht_ne
        exact mul_ne_zero hc ht_ne
    filter_upwards [htend.eventually (h δ hδ), self_mem_nhdsWithin] with t ht ht_ne
    have hden_t : 0 < ‖t‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ht_ne)
    have hden_ct : 0 < ‖c * t‖ ^ 2 := by
      exact sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hc ht_ne))
    have hnorm :
        ‖f (c * t) - f 0 - (c * p) * t - (1 / 2 : ℝ) * (c ^ 2 * q) * t ^ 2‖ =
          ‖f (c * t) - f 0 - p * (c * t) - (1 / 2 : ℝ) * q * (c * t) ^ 2‖ := by
      congr 1
      ring
    have hbound :
        ‖f (c * t) - f 0 - (c * p) * t - (1 / 2 : ℝ) * (c ^ 2 * q) * t ^ 2‖ ≤
          ε * ‖t‖ ^ 2 := by
      rw [hnorm]
      calc
        ‖f (c * t) - f 0 - p * (c * t) - (1 / 2 : ℝ) * q * (c * t) ^ 2‖
            ≤ δ * ‖c * t‖ ^ 2 := by
              exact (div_le_iff₀ hden_ct).mp (by simpa [zero_add] using ht)
        _ = (δ * ‖c‖ ^ 2) * ‖t‖ ^ 2 := by
          simp [norm_mul, mul_assoc, mul_left_comm, mul_comm, pow_two]
        _ ≤ ε * ‖t‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right hc_le (sq_nonneg _)
    exact (div_le_iff₀ hden_t).mpr (by simpa [zero_add, mul_zero] using hbound)

/-- Recenter scalar quadratic estimate data at `x` as estimate data at `0` for the translated
function `z ↦ f (x + z)`. -/
theorem RealScalarQuadraticEstimateWithDataAt.recenter_zero
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : RealScalarQuadraticEstimateWithDataAt f x p q) :
    RealScalarQuadraticEstimateWithDataAt (fun z : ℝ => f (x + z)) 0 p q := by
  intro ε hε
  simpa using h ε hε

/-- Quotient-estimate version of `RealScalarQuadraticEstimateWithDataAt.recenter_zero`. -/
theorem RealScalarQuadraticQuotientEstimateWithDataAt.recenter_zero
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : RealScalarQuadraticQuotientEstimateWithDataAt f x p q) :
    RealScalarQuadraticQuotientEstimateWithDataAt (fun z : ℝ => f (x + z)) 0 p q := by
  intro ε hε
  simpa using h ε hε

/-- On the real line, scalar quadratic estimate data at `x` transfers to the restriction of `f`
to the affine line through `x` with real direction `ξ`. -/
theorem RealScalarQuadraticEstimateWithDataAt.real_lineRestriction
    {f : ℝ → ℝ} {x ξ p q : ℝ}
    (h : RealScalarQuadraticEstimateWithDataAt f x p q) :
    RealScalarQuadraticEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction f x ξ) 0 (ξ * p) (ξ ^ 2 * q) := by
  have hcomp := h.recenter_zero.comp_mul (c := ξ)
  have hfun :
      AleksandrovDifferentiability.lineRestriction f x ξ =
        fun t : ℝ => f (x + ξ * t) := by
    funext t
    simp [AleksandrovDifferentiability.lineRestriction, mul_comm]
  simpa [hfun] using hcomp

/-- Quotient-estimate version of
`RealScalarQuadraticEstimateWithDataAt.real_lineRestriction`. -/
theorem RealScalarQuadraticQuotientEstimateWithDataAt.real_lineRestriction
    {f : ℝ → ℝ} {x ξ p q : ℝ}
    (h : RealScalarQuadraticQuotientEstimateWithDataAt f x p q) :
    RealScalarQuadraticQuotientEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction f x ξ) 0 (ξ * p) (ξ ^ 2 * q) := by
  have hcomp := h.recenter_zero.comp_mul (c := ξ)
  have hfun :
      AleksandrovDifferentiability.lineRestriction f x ξ =
        fun t : ℝ => f (x + ξ * t) := by
    funext t
    simp [AleksandrovDifferentiability.lineRestriction, mul_comm]
  simpa [hfun] using hcomp

/-- Line-restriction version of `RealScalarQuadraticEstimateWithDataAt.comp_mul`: replacing the
direction `v` by `c • v` scales the first coefficient by `c` and the quadratic coefficient by
`c ^ 2`. -/
theorem RealScalarQuadraticEstimateWithDataAt.lineRestriction_smul
    {u : E → ℝ} {x v : E} {p q c : ℝ}
    (h : RealScalarQuadraticEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0 p q) :
    RealScalarQuadraticEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x (c • v)) 0 (c * p) (c ^ 2 * q) := by
  have hfun :
      AleksandrovDifferentiability.lineRestriction u x (c • v) =
        fun t : ℝ => AleksandrovDifferentiability.lineRestriction u x v (c * t) := by
    funext t
    simp [AleksandrovDifferentiability.lineRestriction, smul_smul, mul_comm]
  simpa [hfun] using h.comp_mul (c := c)

/-- Quotient-estimate version of
`RealScalarQuadraticEstimateWithDataAt.lineRestriction_smul`. -/
theorem RealScalarQuadraticQuotientEstimateWithDataAt.lineRestriction_smul
    {u : E → ℝ} {x v : E} {p q c : ℝ}
    (h : RealScalarQuadraticQuotientEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0 p q) :
    RealScalarQuadraticQuotientEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x (c • v)) 0 (c * p) (c ^ 2 * q) := by
  have hfun :
      AleksandrovDifferentiability.lineRestriction u x (c • v) =
        fun t : ℝ => AleksandrovDifferentiability.lineRestriction u x v (c * t) := by
    funext t
    simp [AleksandrovDifferentiability.lineRestriction, smul_smul, mul_comm]
  simpa [hfun] using h.comp_mul (c := c)

/-- Diagonal pair-direction version of line-restriction rescaling: the direction `v + v` carries
the first-order coefficient from the ambient slope and the quadratic coefficient `4 * q`. -/
theorem RealScalarQuadraticEstimateWithDataAt.lineRestriction_add_self
    {u : E → ℝ} {x p v : E} {q : ℝ}
    (h : RealScalarQuadraticEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0 (inner ℝ p v) q) :
    RealScalarQuadraticEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x (v + v)) 0
        (inner ℝ p (v + v)) (4 * q) := by
  have hs := h.lineRestriction_smul (c := (2 : ℝ))
  simpa [two_smul, inner_add_right, two_mul, pow_two, mul_assoc,
    show (2 + 2 : ℝ) = 4 by norm_num] using hs

/-- Quotient-estimate version of
`RealScalarQuadraticEstimateWithDataAt.lineRestriction_add_self`. -/
theorem RealScalarQuadraticQuotientEstimateWithDataAt.lineRestriction_add_self
    {u : E → ℝ} {x p v : E} {q : ℝ}
    (h : RealScalarQuadraticQuotientEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0 (inner ℝ p v) q) :
    RealScalarQuadraticQuotientEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x (v + v)) 0
        (inner ℝ p (v + v)) (4 * q) := by
  have hs := h.lineRestriction_smul (c := (2 : ℝ))
  simpa [two_smul, inner_add_right, two_mul, pow_two, mul_assoc,
    show (2 + 2 : ℝ) = 4 by norm_num] using hs

/-- Existential scalar estimate version of line-restriction rescaling. -/
theorem RealScalarQuadraticEstimateAt.lineRestriction_smul
    {u : E → ℝ} {x v : E} {c : ℝ}
    (h : RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0) :
    RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x (c • v)) 0 := by
  rcases h with ⟨p, q, hest⟩
  have hwith :
      RealScalarQuadraticEstimateWithDataAt
        (AleksandrovDifferentiability.lineRestriction u x v) 0 p q := hest
  exact
    RealScalarQuadraticEstimateWithDataAt.realScalarQuadraticEstimateAt
      (hwith.lineRestriction_smul (u := u) (x := x) (v := v) (c := c))

/-- Existential scalar quotient-estimate version of line-restriction rescaling. -/
theorem RealScalarQuadraticQuotientEstimateAt.lineRestriction_smul
    {u : E → ℝ} {x v : E} {c : ℝ}
    (h : RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0) :
    RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x (c • v)) 0 := by
  rcases h with ⟨p, q, hest⟩
  have hwith :
      RealScalarQuadraticQuotientEstimateWithDataAt
        (AleksandrovDifferentiability.lineRestriction u x v) 0 p q := hest
  exact
    RealScalarQuadraticQuotientEstimateWithDataAt.realScalarQuadraticQuotientEstimateAt
      (hwith.lineRestriction_smul (u := u) (x := x) (v := v) (c := c))

/-- Nonzero rescaling of a line direction preserves the existential scalar estimate predicate. -/
theorem RealScalarQuadraticEstimateAt.lineRestriction_smul_iff
    {u : E → ℝ} {x v : E} {c : ℝ} (hc : c ≠ 0) :
    RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x (c • v)) 0 ↔
    RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0 := by
  constructor
  · intro h
    have h' := h.lineRestriction_smul (u := u) (x := x) (v := c • v) (c := c⁻¹)
    simpa [smul_smul, inv_mul_cancel₀ hc] using h'
  · intro h
    exact h.lineRestriction_smul (u := u) (x := x) (v := v) (c := c)

/-- Quotient-estimate version of `RealScalarQuadraticEstimateAt.lineRestriction_smul_iff`. -/
theorem RealScalarQuadraticQuotientEstimateAt.lineRestriction_smul_iff
    {u : E → ℝ} {x v : E} {c : ℝ} (hc : c ≠ 0) :
    RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x (c • v)) 0 ↔
    RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0 := by
  constructor
  · intro h
    have h' := h.lineRestriction_smul (u := u) (x := x) (v := c • v) (c := c⁻¹)
    simpa [smul_smul, inv_mul_cancel₀ hc] using h'
  · intro h
    exact h.lineRestriction_smul (u := u) (x := x) (v := v) (c := c)

/-- Existential scalar estimate version for the diagonal pair direction `v + v`. -/
theorem RealScalarQuadraticEstimateAt.lineRestriction_add_self
    {u : E → ℝ} {x v : E}
    (h : RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0) :
    RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x (v + v)) 0 := by
  simpa [two_smul] using h.lineRestriction_smul (u := u) (x := x) (v := v) (c := (2 : ℝ))

/-- Existential scalar quotient-estimate version for the diagonal pair direction `v + v`. -/
theorem RealScalarQuadraticQuotientEstimateAt.lineRestriction_add_self
    {u : E → ℝ} {x v : E}
    (h : RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x v) 0) :
    RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x (v + v)) 0 := by
  simpa [two_smul] using h.lineRestriction_smul (u := u) (x := x) (v := v) (c := (2 : ℝ))

/-- Constant real-line functions have scalar quadratic estimate data with zero coefficients. -/
theorem realScalarQuadraticEstimateWithDataAt_const (c x : ℝ) :
    RealScalarQuadraticEstimateWithDataAt (fun _ : ℝ => c) x 0 0 := by
  intro ε hε
  filter_upwards with z
  simpa using mul_nonneg hε.le (sq_nonneg z)

/-- Constant real-line functions have punctured scalar quotient-estimate data with zero
coefficients. -/
theorem realScalarQuadraticQuotientEstimateWithDataAt_const (c x : ℝ) :
    RealScalarQuadraticQuotientEstimateWithDataAt (fun _ : ℝ => c) x 0 0 := by
  exact (realScalarQuadraticEstimateWithDataAt_const c x).quadraticQuotientEstimateWithDataAt

/-- Existential scalar estimate form for constant real-line functions. -/
theorem realScalarQuadraticEstimateAt_const (c x : ℝ) :
    RealScalarQuadraticEstimateAt (fun _ : ℝ => c) x :=
  (realScalarQuadraticEstimateWithDataAt_const c x).realScalarQuadraticEstimateAt

/-- Existential quotient-estimate form for constant real-line functions. -/
theorem realScalarQuadraticQuotientEstimateAt_const (c x : ℝ) :
    RealScalarQuadraticQuotientEstimateAt (fun _ : ℝ => c) x :=
  (realScalarQuadraticQuotientEstimateWithDataAt_const c x).realScalarQuadraticQuotientEstimateAt

/-- Real affine functions have scalar quadratic estimate data with zero quadratic coefficient. -/
theorem realScalarQuadraticEstimateWithDataAt_affine (a b x : ℝ) :
    RealScalarQuadraticEstimateWithDataAt (fun t : ℝ => a * t + b) x a 0 := by
  intro ε hε
  filter_upwards with z
  have hinside :
      (a * (x + z) + b) - (a * x + b) - a * z -
          (1 / 2 : ℝ) * 0 * z ^ 2 = 0 := by
    ring
  have hzero :
      ‖(a * (x + z) + b) - (a * x + b) - a * z -
          (1 / 2 : ℝ) * 0 * z ^ 2‖ = 0 := by
    rw [hinside, norm_zero]
  rw [hzero]
  exact mul_nonneg hε.le (sq_nonneg ‖z‖)

/-- Punctured normalized quotient-estimate version of
`realScalarQuadraticEstimateWithDataAt_affine`. -/
theorem realScalarQuadraticQuotientEstimateWithDataAt_affine (a b x : ℝ) :
    RealScalarQuadraticQuotientEstimateWithDataAt (fun t : ℝ => a * t + b) x a 0 :=
  (realScalarQuadraticEstimateWithDataAt_affine a b x).quadraticQuotientEstimateWithDataAt

/-- Existential scalar estimate form for real affine functions. -/
theorem realScalarQuadraticEstimateAt_affine (a b x : ℝ) :
    RealScalarQuadraticEstimateAt (fun t : ℝ => a * t + b) x :=
  (realScalarQuadraticEstimateWithDataAt_affine a b x).realScalarQuadraticEstimateAt

/-- Existential quotient-estimate form for real affine functions. -/
theorem realScalarQuadraticQuotientEstimateAt_affine (a b x : ℝ) :
    RealScalarQuadraticQuotientEstimateAt (fun t : ℝ => a * t + b) x :=
  RealScalarQuadraticQuotientEstimateWithDataAt.realScalarQuadraticQuotientEstimateAt
    (realScalarQuadraticQuotientEstimateWithDataAt_affine a b x)

/-- A zero-direction line restriction has scalar quadratic estimate data at the base parameter. -/
theorem realScalarQuadraticEstimateAt_lineRestriction_zero_direction
    (u : E → ℝ) (x : E) :
    RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x (0 : E)) 0 := by
  have hfun :
      AleksandrovDifferentiability.lineRestriction u x (0 : E) = fun _ : ℝ => u x := by
    funext t
    simp [AleksandrovDifferentiability.lineRestriction]
  simpa [hfun] using
    (realScalarQuadraticEstimateAt_const (u x) 0)

/-- Quotient-estimate version of
`realScalarQuadraticEstimateAt_lineRestriction_zero_direction`. -/
theorem realScalarQuadraticQuotientEstimateAt_lineRestriction_zero_direction
    (u : E → ℝ) (x : E) :
    RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x (0 : E)) 0 := by
  have hfun :
      AleksandrovDifferentiability.lineRestriction u x (0 : E) = fun _ : ℝ => u x := by
    funext t
    simp [AleksandrovDifferentiability.lineRestriction]
  simpa [hfun] using
    (realScalarQuadraticQuotientEstimateAt_const (u x) 0)

/-- Rebase scalar estimate data from a parameter `t` on the line through `x` to parameter `0`
on the same geometric line based at `x + t • v`. -/
theorem RealScalarQuadraticEstimateWithDataAt.lineRestriction_rebase
    {u : E → ℝ} {x v : E} {t p q : ℝ}
    (h : RealScalarQuadraticEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x v) t p q) :
    RealScalarQuadraticEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u (x + t • v) v) 0 p q := by
  intro ε hε
  filter_upwards [h ε hε] with z hz
  have harg : x + t • v + z • v = x + (t + z) • v := by
    rw [add_smul]
    abel
  simpa [AleksandrovDifferentiability.lineRestriction, harg, add_assoc] using hz

/-- Quotient-estimate version of
`RealScalarQuadraticEstimateWithDataAt.lineRestriction_rebase`. -/
theorem RealScalarQuadraticQuotientEstimateWithDataAt.lineRestriction_rebase
    {u : E → ℝ} {x v : E} {t p q : ℝ}
    (h : RealScalarQuadraticQuotientEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u x v) t p q) :
    RealScalarQuadraticQuotientEstimateWithDataAt
      (AleksandrovDifferentiability.lineRestriction u (x + t • v) v) 0 p q := by
  intro ε hε
  filter_upwards [h ε hε] with z hz
  have harg : x + t • v + z • v = x + (t + z) • v := by
    rw [add_smul]
    abel
  simpa [AleksandrovDifferentiability.lineRestriction, harg, add_assoc] using hz

/-- Existential scalar estimate rebase from a line parameter to the corresponding ambient base
point on the same line. -/
theorem RealScalarQuadraticEstimateAt.lineRestriction_rebase
    {u : E → ℝ} {x v : E} {t : ℝ}
    (h : RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x v) t) :
    RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction u (x + t • v) v) 0 := by
  rcases h with ⟨p, q, hest⟩
  have hwith :
      RealScalarQuadraticEstimateWithDataAt
        (AleksandrovDifferentiability.lineRestriction u x v) t p q := hest
  exact (hwith.lineRestriction_rebase (u := u) (x := x) (v := v)).realScalarQuadraticEstimateAt

/-- Quotient-estimate existential rebase from a line parameter to the corresponding ambient base
point on the same line. -/
theorem RealScalarQuadraticQuotientEstimateAt.lineRestriction_rebase
    {u : E → ℝ} {x v : E} {t : ℝ}
    (h : RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction u x v) t) :
    RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction u (x + t • v) v) 0 := by
  rcases h with ⟨p, q, hest⟩
  have hwith :
      RealScalarQuadraticQuotientEstimateWithDataAt
        (AleksandrovDifferentiability.lineRestriction u x v) t p q := hest
  exact
    (hwith.lineRestriction_rebase (u := u) (x := x) (v := v)).realScalarQuadraticQuotientEstimateAt

/-- On the real line, a project-level second-order expansion gives the scalar quadratic estimate
shape used by the one-dimensional assembly interface. -/
theorem realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt
    {f : ℝ → ℝ} {x p : ℝ} {B : ℝ →L[ℝ] ℝ}
    (h : HasSecondOrderExpansionAt f x p B) :
    RealScalarQuadraticEstimateWithDataAt f x p (B 1) := by
  intro ε hε
  filter_upwards [h.def hε] with z hz
  have hBz : B z = z * B 1 := by
    calc
      B z = B (z • (1 : ℝ)) := by simp
      _ = z • B 1 := by rw [map_smul]
      _ = z * B 1 := by rfl
  have hnorm :
      ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * B 1 * z ^ 2‖ =
        ‖f (x + z) - f x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z)‖ := by
    congr 1
    simp [hBz, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hsq_norm : ‖(‖z‖ ^ 2 : ℝ)‖ = ‖z‖ ^ 2 :=
    Real.norm_of_nonneg (sq_nonneg _)
  rw [hnorm]
  simpa [hsq_norm] using hz

/-- On the real line, a project-level second-order expansion gives the scalar quadratic estimate
shape used by the one-dimensional assembly interface. -/
theorem realScalarQuadraticEstimateAt_of_hasSecondOrderExpansionAt
    {f : ℝ → ℝ} {x p : ℝ} {B : ℝ →L[ℝ] ℝ}
    (h : HasSecondOrderExpansionAt f x p B) :
    RealScalarQuadraticEstimateAt f x :=
  RealScalarQuadraticEstimateWithDataAt.realScalarQuadraticEstimateAt
    (realScalarQuadraticEstimateWithDataAt_of_hasSecondOrderExpansionAt h)

/-- On the real line, project-level second-order differentiability gives the scalar quadratic
estimate shape used by the one-dimensional assembly interface. -/
theorem realScalarQuadraticEstimateAt_of_secondOrderDifferentiableAt
    {f : ℝ → ℝ} {x : ℝ} (h : SecondOrderDifferentiableAt f x) :
    RealScalarQuadraticEstimateAt f x := by
  rcases h with ⟨p, B, _hB, hExp⟩
  exact realScalarQuadraticEstimateAt_of_hasSecondOrderExpansionAt hExp

/-- The averaged right-derivative remainder estimate, together with differentiability of the
right derivative, gives the project's scalar quadratic estimate.

This theorem isolates the remaining genuinely one-dimensional convex analytic ingredient:
for convex functions, one still has to prove `HasRightDerivAverageRemainderAt` at the
derivative-good points. Once that averaging estimate is available, the passage to the usual
`(1 / 2) * q * z ^ 2` Taylor coefficient is formal. -/
theorem realScalarQuadraticEstimateAt_of_rightDeriv_averageRemainder_of_hasDerivWithinAt
    {S : Set ℝ} {f : ℝ → ℝ} {x q : ℝ}
    (hx : x ∈ interior S) (havg : HasRightDerivAverageRemainderAt f x)
    (hderiv : HasDerivWithinAt (rightDeriv f) q (interior S) x) :
    RealScalarQuadraticEstimateAt f x := by
  refine ⟨rightDeriv f x, q, ?_⟩
  intro ε hε
  have hεhalf : 0 < ε / 2 := by positivity
  have hto_nhds :
      Filter.Tendsto (fun z : ℝ => x + z) (nhds 0) (nhds x) := by
    simpa using (tendsto_const_nhds.add Filter.tendsto_id :
      Filter.Tendsto (fun z : ℝ => x + z) (nhds 0) (nhds (x + 0)))
  have hmem :
      ∀ᶠ z in nhds 0, x + z ∈ interior S :=
    hto_nhds (isOpen_interior.mem_nhds hx)
  have hto_within :
      Filter.Tendsto (fun z : ℝ => x + z) (nhds 0) (nhdsWithin x (interior S)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hto_nhds, hmem⟩
  have hderiv_comp :
      (fun z : ℝ => rightDeriv f (x + z) - rightDeriv f x - q * z)
        =o[nhds 0] fun z : ℝ => z := by
    have hcomp := hderiv.isLittleO.comp_tendsto hto_within
    simpa [Function.comp_def, mul_comm] using hcomp
  have hderiv_bound :
      ∀ᶠ z in nhds 0,
        ‖rightDeriv f (x + z) - rightDeriv f x - q * z‖ ≤ ε * ‖z‖ := by
    simpa using hderiv_comp.def hε
  filter_upwards [havg (ε / 2) hεhalf, hderiv_bound] with z havg_z hderiv_z
  let A : ℝ :=
    f (x + z) - f x - rightDeriv f x * z -
      (1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x) * z
  let D : ℝ :=
    (1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x - q * z) * z
  have hD : ‖D‖ ≤ (ε / 2) * ‖z‖ ^ 2 := by
    calc
      ‖D‖ =
          ‖(1 / 2 : ℝ)‖ *
            ‖rightDeriv f (x + z) - rightDeriv f x - q * z‖ * ‖z‖ := by
        simp [D, norm_mul, mul_assoc]
      _ ≤ ‖(1 / 2 : ℝ)‖ * (ε * ‖z‖) * ‖z‖ := by
        gcongr
      _ = (ε / 2) * ‖z‖ ^ 2 := by
        simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
        nlinarith [sq_abs z]
  have hsplit :
      f (x + z) - f x - rightDeriv f x * z - (1 / 2 : ℝ) * q * z ^ 2 =
        A + D := by
    simp [A, D, pow_two]
    ring
  calc
    ‖f (x + z) - f x - rightDeriv f x * z - (1 / 2 : ℝ) * q * z ^ 2‖ =
        ‖A + D‖ := by rw [hsplit]
    _ ≤ ‖A‖ + ‖D‖ := norm_add_le A D
    _ ≤ (ε / 2) * ‖z‖ ^ 2 + (ε / 2) * ‖z‖ ^ 2 :=
      add_le_add havg_z hD
    _ = ε * ‖z‖ ^ 2 := by ring

/-- Derivative-good points satisfy the scalar quadratic estimate once the averaged
right-derivative remainder estimate is known there. -/
theorem realScalarQuadraticEstimateAt_of_mem_oneSidedDerivDifferentiabilitySet_of_averageRemainder
    {S : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ interior S) (hgood : x ∈ oneSidedDerivDifferentiabilitySet S f)
    (havg : HasRightDerivAverageRemainderAt f x) :
    RealScalarQuadraticEstimateAt f x := by
  exact realScalarQuadraticEstimateAt_of_rightDeriv_averageRemainder_of_hasDerivWithinAt
    (S := S) (f := f) (x := x)
    (q := derivWithin (rightDeriv f) (interior S) x) hx havg hgood.1.hasDerivWithinAt

/-- A usual scalar Taylor little-o expansion gives the project-local scalar quadratic estimate
at the base point. -/
theorem realScalarQuadraticEstimateAt_of_taylor_isLittleO
    {f : ℝ → ℝ} {x p q : ℝ}
    (h : (fun y : ℝ => f y - (f x + p * (y - x) + (1 / 2 : ℝ) * q * (y - x) ^ 2))
      =o[nhds x] fun y : ℝ => (y - x) ^ 2) :
    RealScalarQuadraticEstimateAt f x := by
  refine ⟨p, q, ?_⟩
  intro ε hε
  have hcomp :
      (fun z : ℝ =>
        f (x + z) - (f x + p * ((x + z) - x) + (1 / 2 : ℝ) * q * ((x + z) - x) ^ 2))
        =o[nhds 0] fun z : ℝ => ((x + z) - x) ^ 2 := by
    refine h.comp_tendsto ?_
    simpa using (tendsto_const_nhds.add Filter.tendsto_id :
      Filter.Tendsto (fun z : ℝ => x + z) (nhds 0) (nhds (x + 0)))
  filter_upwards [hcomp.def hε] with z hz
  have hleft :
      ‖f (x + z) -
          (f x + p * ((x + z) - x) + (1 / 2 : ℝ) * q * ((x + z) - x) ^ 2)‖ =
        ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ := by
    congr 1
    ring
  have hright : ‖((x + z) - x) ^ 2‖ = ‖z‖ ^ 2 := by
    simp [norm_pow]
  rw [← hleft, ← hright]
  exact hz

/-- A `C^2` real function on a convex neighborhood of `x` satisfies the project-local scalar
quadratic estimate at `x`. This is a direct wrapper around Mathlib's Taylor theorem, with the
Taylor polynomial coefficients exposed in the project's scalar-estimate format. -/
theorem realScalarQuadraticEstimateAt_of_contDiffOn_two_of_mem_interior
    {s : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hs : Convex ℝ s) (hx : x ∈ interior s) (hf : ContDiffOn ℝ 2 f s) :
    RealScalarQuadraticEstimateAt f x := by
  let p : ℝ := iteratedDerivWithin 1 f s x
  let q : ℝ := iteratedDerivWithin 2 f s x
  refine realScalarQuadraticEstimateAt_of_taylor_isLittleO (p := p) (q := q) ?_
  have htaylor :
      (fun y : ℝ => f y - taylorWithinEval f 2 s x y)
        =o[nhds x] fun y : ℝ => (y - x) ^ 2 := by
    have hwithin :=
      taylor_isLittleO (f := f) (x₀ := x) (n := 2) (s := s)
        hs (interior_subset hx) hf
    simpa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hx)] using hwithin
  have htwo : ((1 + 1 : ℝ)⁻¹) = (2 : ℝ)⁻¹ := by norm_num
  simpa [p, q, taylor_within_apply, Nat.factorial, pow_succ, mul_assoc, mul_comm,
    mul_left_comm, htwo] using htaylor

/-- Points carrying real-line scalar quadratic estimate data. -/
def realScalarQuadraticEstimateSet (f : ℝ → ℝ) : Set ℝ :=
  {x | RealScalarQuadraticEstimateAt f x}

/-- Points carrying punctured normalized real-line scalar quadratic estimate data. -/
def realScalarQuadraticQuotientEstimateSet (f : ℝ → ℝ) : Set ℝ :=
  {x | RealScalarQuadraticQuotientEstimateAt f x}

@[simp]
theorem mem_realScalarQuadraticEstimateSet {f : ℝ → ℝ} {x : ℝ} :
    x ∈ realScalarQuadraticEstimateSet f ↔ RealScalarQuadraticEstimateAt f x :=
  Iff.rfl

@[simp]
theorem mem_realScalarQuadraticQuotientEstimateSet {f : ℝ → ℝ} {x : ℝ} :
    x ∈ realScalarQuadraticQuotientEstimateSet f ↔
      RealScalarQuadraticQuotientEstimateAt f x :=
  Iff.rfl

/-- Scalar quadratic estimate data implies project second-order differentiability on `ℝ`. -/
theorem RealScalarQuadraticEstimateAt.secondOrderDifferentiableAt
    {f : ℝ → ℝ} {x : ℝ} (h : RealScalarQuadraticEstimateAt f x) :
    SecondOrderDifferentiableAt f x := by
  rcases h with ⟨p, q, hest⟩
  exact secondOrderDifferentiableAt_real_of_eventually_norm_sub_quadratic_le_mul hest

/-- Scalar quotient-estimate data implies project second-order differentiability on `ℝ`. -/
theorem RealScalarQuadraticQuotientEstimateAt.secondOrderDifferentiableAt
    {f : ℝ → ℝ} {x : ℝ} (h : RealScalarQuadraticQuotientEstimateAt f x) :
    SecondOrderDifferentiableAt f x := by
  rcases h with ⟨p, q, hest⟩
  exact secondOrderDifferentiableAt_real_of_eventually_norm_sub_quadratic_div_norm_sq_le hest

/-- A local real-line scalar quadratic estimate implies the punctured normalized quotient
estimate. -/
theorem RealScalarQuadraticEstimateAt.quadraticQuotientEstimateAt
    {f : ℝ → ℝ} {x : ℝ} (h : RealScalarQuadraticEstimateAt f x) :
    RealScalarQuadraticQuotientEstimateAt f x := by
  rcases h with ⟨p, q, hest⟩
  refine ⟨p, q, ?_⟩
  intro ε hε
  filter_upwards [(hest ε hε).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hz_ne
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz_ne)
  exact (div_le_iff₀ hden).mpr hz

/-- The scalar estimate good set is contained in the second-order differentiability locus. -/
theorem realScalarQuadraticEstimateSet_subset_secondOrderDifferentiabilitySet
    {f : ℝ → ℝ} :
    realScalarQuadraticEstimateSet f ⊆ secondOrderDifferentiabilitySet f := by
  intro x hx
  exact hx.secondOrderDifferentiableAt

/-- The scalar quotient-estimate good set is contained in the second-order differentiability
locus. -/
theorem realScalarQuadraticQuotientEstimateSet_subset_secondOrderDifferentiabilitySet
    {f : ℝ → ℝ} :
    realScalarQuadraticQuotientEstimateSet f ⊆ secondOrderDifferentiabilitySet f := by
  intro x hx
  exact hx.secondOrderDifferentiableAt

/-- The local scalar estimate set is contained in the scalar quotient-estimate set. -/
theorem realScalarQuadraticEstimateSet_subset_realScalarQuadraticQuotientEstimateSet
    {f : ℝ → ℝ} :
    realScalarQuadraticEstimateSet f ⊆ realScalarQuadraticQuotientEstimateSet f := by
  intro x hx
  exact hx.quadraticQuotientEstimateAt

end AleksandrovDifferentiability
