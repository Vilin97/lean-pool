/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.KyFan
public import LeanPool.DavisKahan.ForTauCeti.Topology.ENNRealLiminf

/-!
# The trace-class ideal

The **nuclear norm** of a bounded operator is the sum of all its approximation numbers,

```
T.nuclearENorm = ∑' n, ENNReal.ofReal (T.approximationNumber n),
```

and `T` is **trace class** when that is finite.  Like the Hilbert--Schmidt norm it is valued
in `ℝ≥0∞`, so it is defined for every bounded operator and is `∞` exactly off the ideal.

## Why this is now possible

The nuclear norm is the supremum of the Ky Fan gauges, so its triangle inequality *is* the
Ky Fan triangle inequality, taken to the limit.  That inequality is the one whose only
proof in this repository used to run through `vendor/Spectra`'s projection-valued measures;
since 2026-07-28 it is `ContinuousLinearMap.kyFanGauge_add_le_complex`, proved from Mathlib's
continuous functional calculus, and the trace-class ideal follows immediately.

**Everything is stated over `RCLike 𝕜`.**  The Ky Fan triangle inequality is what the scalar
field is needed for, and it now holds over any field satisfying
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere` — a class with two instances, `ℂ` from
the continuous functional calculus and `ℝ` by complexification.  So the family is built once
and `traceClassIdealFamily ℝ` and `traceClassIdealFamily ℂ` are both instances of it, with no
second copy of any argument.

## Main results

* `ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge`: the nuclear norm is the supremum of
  the Ky Fan gauges;
* `ContinuousLinearMap.nuclearENorm_add_le`, `_smul`, `_adjoint`, `_comp_le`: the ideal laws;
* `ContinuousLinearMap.IsTraceClass` and
  `ContinuousLinearMap.isTraceClass_iff_summable`: the membership predicate and its concrete
  form;
* `TauCeti.traceClassIdealFamily`: the resulting symmetric operator ideal family.

Unlike the Ky Fan families, whose carriers are provably `⊤`, this one need not be all of
`E →L[𝕜] F`, so it is the first family here whose `ℝ≥0∞` gauge is expected to take the value
`∞`.  That it actually does — that some bounded operator is not trace class — is not proved
here; it needs an infinite orthonormal family to exhibit one.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: none.
-/

open scoped ENNReal NNReal InnerProductSpace

public section

namespace ContinuousLinearMap

universe u v w

section Basic

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The **nuclear norm**: the sum of all approximation numbers, valued in `ℝ≥0∞` and so
defined for every bounded operator. -/
@[expose]
noncomputable def nuclearENorm (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n)

/-- The nuclear norm is the supremum of the Ky Fan gauges.  Every property of it below is
read off this identity. -/
theorem nuclearENorm_eq_iSup_kyFanGauge (T : E →L[𝕜] F) :
    T.nuclearENorm = ⨆ k : ℕ, ENNReal.ofReal (T.kyFanGauge k) := by
  rw [nuclearENorm, ENNReal.tsum_eq_iSup_nat]
  refine iSup_congr fun k => ?_
  rw [kyFanGauge, ENNReal.ofReal_sum_of_nonneg]
  exact fun n _ => T.approximationNumber_nonneg n

/-- Every finite Ky Fan gauge is dominated by the nuclear norm, of which it is a
partial sum.  This is the inequality that makes the nuclear norm the supremum of
the Ky Fan family rather than merely an upper bound for it. -/
theorem ofReal_kyFanGauge_le_nuclearENorm (T : E →L[𝕜] F) (k : ℕ) :
    ENNReal.ofReal (T.kyFanGauge k) ≤ T.nuclearENorm := by
  rw [nuclearENorm_eq_iSup_kyFanGauge]
  exact le_iSup (fun j : ℕ => ENNReal.ofReal (T.kyFanGauge j)) k

/-- The nuclear norm vanishes on the zero operator: all of its approximation
numbers are `0`. -/
@[simp] theorem nuclearENorm_zero : (0 : E →L[𝕜] F).nuclearENorm = 0 := by
  simp [nuclearENorm]

end Basic

section Complete

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The triangle inequality**: the Ky Fan inequality in the limit. -/
theorem nuclearENorm_add_le [HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (S T : E →L[𝕜] F) :
    (S + T).nuclearENorm ≤ S.nuclearENorm + T.nuclearENorm := by
  rw [nuclearENorm_eq_iSup_kyFanGauge]
  refine iSup_le fun k => ?_
  calc ENNReal.ofReal ((S + T).kyFanGauge k)
      ≤ ENNReal.ofReal (S.kyFanGauge k + T.kyFanGauge k) :=
        ENNReal.ofReal_le_ofReal
          (kyFanGauge_add_le_of_hasMinMaxLowerBound HasMinMaxLowerBoundEverywhere.out S T k)
    _ = ENNReal.ofReal (S.kyFanGauge k) + ENNReal.ofReal (T.kyFanGauge k) :=
        ENNReal.ofReal_add (S.kyFanGauge_nonneg k) (T.kyFanGauge_nonneg k)
    _ ≤ S.nuclearENorm + T.nuclearENorm :=
        add_le_add (S.ofReal_kyFanGauge_le_nuclearENorm k)
          (T.ofReal_kyFanGauge_le_nuclearENorm k)

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Absolute homogeneity.**  Scaling an operator scales every approximation
number, hence the whole sum. -/
theorem nuclearENorm_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).nuclearENorm = ‖c‖ₑ * T.nuclearENorm := by
  simp only [nuclearENorm, approximationNumber_smul,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm]
  exact ENNReal.tsum_mul_left

omit [CompleteSpace E] [CompleteSpace F] in
/-- The nuclear norm is unchanged by negation, term by term. -/
@[simp] theorem nuclearENorm_neg (T : E →L[𝕜] F) : (-T).nuclearENorm = T.nuclearENorm := by
  simp only [nuclearENorm, approximationNumber_neg]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The nuclear norm dominates the operator norm**, being its zeroth term. -/
theorem enorm_le_nuclearENorm (T : E →L[𝕜] F) : ‖T‖ₑ ≤ T.nuclearENorm := by
  rw [← ofReal_norm, ← T.approximationNumber_index_zero]
  exact ENNReal.le_tsum (f := fun n => ENNReal.ofReal (T.approximationNumber n)) 0

/-- **Adjoint invariance**, immediate from invariance of the approximation
numbers.  This is the field that makes the trace-class family *symmetric*. -/
theorem nuclearENorm_adjoint (T : E →L[𝕜] F) : T.adjoint.nuclearENorm = T.nuclearENorm := by
  simp only [nuclearENorm, approximationNumber_adjoint]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The two-sided ideal bound.** -/
theorem nuclearENorm_comp_le {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) :
    (L ∘L T ∘L R).nuclearENorm ≤ ‖L‖ₑ * T.nuclearENorm * ‖R‖ₑ := by
  calc (L ∘L T ∘L R).nuclearENorm
      ≤ ∑' n : ℕ, ENNReal.ofReal (‖L‖ * T.approximationNumber n * ‖R‖) :=
        ENNReal.tsum_le_tsum fun n =>
          ENNReal.ofReal_le_ofReal (approximationNumber_comp_comp_le L T R n)
    _ = ‖L‖ₑ * T.nuclearENorm * ‖R‖ₑ := by
        simp only [ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (T.approximationNumber_nonneg _)),
          ENNReal.ofReal_mul (norm_nonneg L), ofReal_norm]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
        rfl

-- Lower semicontinuity is a statement about the sequence of approximation numbers, and
-- those need no completeness.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **The nuclear norm is lower semicontinuous along operator-norm convergence.**

Each approximation number is `1`-Lipschitz in the operator norm
(`abs_approximationNumber_sub_approximationNumber_le`), so an operator-norm limit converges
termwise; `ENNReal.tsum_le_liminf_tsum` then passes that to the sum.  This is the step the
Ky Fan families get for free, because their gauge is a finite sum and therefore continuous. -/
theorem nuclearENorm_le_liminf {u : Filter ℕ} [u.NeBot]
    {T : ℕ → E →L[𝕜] F} {L : E →L[𝕜] F}
    (hop : Filter.Tendsto (fun n => ‖T n - L‖) u (nhds 0)) :
    L.nuclearENorm ≤ Filter.liminf (fun n => (T n).nuclearENorm) u := by
  refine ENNReal.tsum_le_liminf_tsum fun i => ?_
  refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hop
  rw [Real.dist_eq]
  exact abs_approximationNumber_sub_approximationNumber_le (T n) L i

omit [CompleteSpace E] [CompleteSpace F] in
/-- `T` is **trace class** when its nuclear norm is finite. -/
def IsTraceClass (T : E →L[𝕜] F) : Prop := T.nuclearENorm ≠ ∞

omit [CompleteSpace E] [CompleteSpace F] in
/-- Concretely, `T` is trace class exactly when its approximation numbers are summable. -/
theorem isTraceClass_iff_summable (T : E →L[𝕜] F) :
    T.IsTraceClass ↔ Summable fun n => T.approximationNumber n := by
  rw [IsTraceClass, nuclearENorm]
  have hcoe : (fun n : ℕ => ENNReal.ofReal (T.approximationNumber n))
      = fun n : ℕ => ((T.approximationNumber n).toNNReal : ℝ≥0∞) := (rfl)
  rw [hcoe, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  refine summable_congr fun n => ?_
  exact Real.coe_toNNReal _ (T.approximationNumber_nonneg n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- On a trace-class operator every Ky Fan gauge is bounded by the nuclear norm read as a
real number. -/
theorem kyFanGauge_le_toReal_nuclearENorm (T : E →L[𝕜] F) (hT : T.IsTraceClass) (k : ℕ) :
    T.kyFanGauge k ≤ T.nuclearENorm.toReal := by
  have h := T.ofReal_kyFanGauge_le_nuclearENorm k
  rw [← ENNReal.ofReal_toReal hT] at h
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h

end Complete

end ContinuousLinearMap

namespace TauCeti

universe u v

open ContinuousLinearMap

/-- **The trace-class operator ideal.**

Its carrier is `ContinuousLinearMap.IsTraceClass` definitionally, which unlike the Ky Fan
carriers is not provably `⊤`. -/
@[expose]
noncomputable def traceClassIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge A := A.nuclearENorm
  gauge_add_le A B := A.nuclearENorm_add_le B
  gauge_smul c A := nuclearENorm_smul c A
  enorm_le_gauge A := A.enorm_le_nuclearENorm
  gauge_comp_le L A R := nuclearENorm_comp_le L A R
  gauge_adjoint A := A.nuclearENorm_adjoint

/-- **The trace-class ideal is complete.**

The argument is the Hilbert--Schmidt one with the energy replaced by the nuclear norm, and
it is worth saying which part is shared and which is not.  Shared: the gauge dominates the
operator norm, so a gauge-Cauchy sequence has an operator-norm limit `L`; then lower
semicontinuity of the gauge puts `L` in the ideal and gives convergence *in the gauge*.  Not
shared: the semicontinuity itself.  Hilbert--Schmidt gets it from pointwise convergence on a
basis; here it comes from `abs_approximationNumber_sub_approximationNumber_le`, the
perturbation bound on the whole `s`-sequence, which needs no basis at all.

Unlike the Ky Fan families the gauge is *not* equivalent to the operator norm, so the
operator-norm limit is only the start of the argument rather than the whole of it. -/
instance isComplete_traceClassIdealFamily {𝕜 : Type u} [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] :
    (traceClassIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    -- the gauge dominates the operator norm, so the sequence is Cauchy there too
    have hop : CauchySeq fun n => (a n).val :=
      TauCeti.OperatorIdealFamily.Elem.cauchySeq_val ha
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hop
    -- the tail of the Cauchy estimate, transported from the ideal norm to the gauge
    have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        (L - (a n).val).nuclearENorm ≤ ENNReal.ofReal ε := by
      intro ε hε
      rw [Metric.cauchySeq_iff] at ha
      obtain ⟨N, hN⟩ := ha ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hfatou : (L - (a n).val).nuclearENorm ≤
          Filter.liminf (fun m => ((a m).val - (a n).val).nuclearENorm) Filter.atTop := by
        refine ContinuousLinearMap.nuclearENorm_le_liminf ?_
        have hd : Filter.Tendsto (fun m => dist ((a m).val) L) Filter.atTop (nhds 0) :=
          tendsto_iff_dist_tendsto_zero.mp hL
        simpa [dist_eq_norm] using hd
      refine hfatou.trans ?_
      have hev : ∀ᶠ m in Filter.atTop,
          ((a m).val - (a n).val).nuclearENorm ≤ ENNReal.ofReal ε := by
        filter_upwards [Filter.eventually_ge_atTop N] with m hm
        have hd : ‖a m - a n‖ < ε := by simpa [dist_eq_norm] using hN m hm n hn
        have heq : (traceClassIdealFamily.{u, v} 𝕜).gauge (a m - a n).val
            = ((a m).val - (a n).val).nuclearENorm := rfl
        rw [← heq, ← TauCeti.OperatorIdealFamily.Elem.enorm_eq_gauge, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hd.le
      calc Filter.liminf (fun m => ((a m).val - (a n).val).nuclearENorm) Filter.atTop
          ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal ε) Filter.atTop :=
            Filter.liminf_le_liminf hev
        _ = ENNReal.ofReal ε := Filter.liminf_const _
    -- the limit lies in the ideal: it differs from a member by something of finite gauge
    obtain ⟨N₁, hN₁⟩ := hcauchy 1 one_pos
    have hmemL : L ∈ (traceClassIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.carrier := by
      have hsplit : L = (L - (a N₁).val) + (a N₁).val := by abel
      rw [TauCeti.OperatorIdealFamily.mem_carrier_iff, hsplit]
      refine ne_top_of_le_ne_top ?_
        ((traceClassIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.gauge_add_le _ _)
      refine ENNReal.add_ne_top.mpr ⟨?_, (a N₁).gauge_val_ne_top⟩
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hN₁ N₁ le_rfl)
    refine ⟨TauCeti.OperatorIdealFamily.Elem.mk hmemL, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hgauge : ((a n).val - L).nuclearENorm ≤ ENNReal.ofReal (ε / 2) := by
      have hneg : ((a n).val - L) = -(L - (a n).val) := by abel
      rw [hneg, ContinuousLinearMap.nuclearENorm_neg]
      exact hN n hn
    have hle : ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ ≤ ε / 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgauge
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    calc dist (a n) (TauCeti.OperatorIdealFamily.Elem.mk hmemL)
        = ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ := dist_eq_norm _ _
      _ ≤ ε / 2 := hle
      _ < ε := by linarith

variable {𝕜 : Type u} [RCLike 𝕜]
  [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The gauge of the trace-class family *is* the nuclear norm, definitionally. -/
@[simp] theorem gauge_traceClassIdealFamily (A : E →L[𝕜] F) :
    ((traceClassIdealFamily.{u, v} 𝕜)).gauge A = A.nuclearENorm := (rfl)
/-- Membership in the trace-class ideal is exactly `IsTraceClass`, so the generic
carrier and the named predicate never diverge. -/
theorem mem_traceClassIdealFamily_carrier_iff (A : E →L[𝕜] F) :
    A ∈ ((traceClassIdealFamily.{u, v} 𝕜)).toOperatorIdealFamily.carrier ↔
      A.IsTraceClass := (Iff.rfl)
end TauCeti
