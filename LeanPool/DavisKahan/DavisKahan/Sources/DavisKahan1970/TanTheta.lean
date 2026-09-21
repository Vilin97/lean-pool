/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.TanTheta.RitzResidual
import LeanPool.DavisKahan.DavisKahan.TanTheta.All

/-!
# Literal Davis--Kahan 1970 Theorem 6.3 surface

Source anchor: Theorem 6.3, the generalized `tan Θ` theorem, together with the
Section 2 `tan Θ` statement and equation (6.6).

## Audited source scope

The source theorem takes a Rayleigh--Ritz trial pair whose compression
spectrum lies in a finite interval, an unwanted exact spectral block lying
one-sidedly beyond the interval by the gap `δ`, and a trial space of rank not
exceeding the wanted exact block; the conclusion bounds every source
unitary-invariant norm of a `tan Θ₀` representative by the residual over `δ`.
Transversality (no `π/2` angle) is a conclusion of the spectral placement,
not a hypothesis.

## What is compiled, at which scope

* `theorem6_3` — the finite-dimensional theorem in the source's literal
  orientation (Ritz spectrum in `[β, α]`, unwanted exact spectrum in
  `[α + δ, ∞)`, strict-lower-rank trial space), for **every rectangular
  unitarily invariant norm**, with the paper's freedom in the choice of the
  `tan Θ₀` representative (any operator with the principal-tangent
  singular values).
* `Theorem6_3_unbounded_graphAngle_opNorm` — the general separable-Hilbert
  space, unbounded self-adjoint theorem in **bounded graph-angle operator
  form** at operator-norm scope.  The tangent operator is the graph
  coordinate of the trial subspace over the exact spectral subspace — the
  source's tangent direction — and the spectral placement is the
  interval/exterior dual (unwanted spectral interval, Ritz spectrum exterior
  by `δ`), which contains the source's one-sided placement.
* per-vector Hilbert-space forms (`Theorem6_3_unbounded_vector`,
  `Theorem6_3_bounded_vector`) feeding the graph-angle form.  The bounded
  per-vector form is also available in the source's literal one-sided
  orientation (`Theorem6_3_bounded_vector_oneSided`): test compression
  spectrum below `α₀`, unwanted compression spectrum in `[α₀ + δ, ∞)`,
  with the interval cap recovered from boundedness of the compression.

## The ideal-gauge Hilbert-space form (closed)

This section previously recorded the exact general-Hilbert-space
**unitary-invariant-ideal** conclusion of Theorem 6.3 as uncompiled, with two
obligations: a Ky Fan transport of the finite root
`kyFan_tanTheta0_ritzResidual_le`, and construction of the transverse
coordinate datum from the spectral placement alone. Both were discharged and
the note went stale; it is corrected here, 2026-08-09, after re-elaborating the
endpoints.

* `TauCeti.DavisKahan.TanTheta.theorem6_3_generalizedTanTheta_ideal`
  — arbitrary complete complex Hilbert space, arbitrary `KyFanDominantIdealFamily`,
  the source's one-sided spectral placement, with ideal membership of the tangent
  *concluded* rather than assumed.
* `…TanTheta.theorem6_3_infiniteTrial_of_formBounds` and
  `…theorem6_3_infiniteTrial_spectral_exists` — the same conclusion at arbitrary
  trial dimension, needing only `[CompleteSpace ↥Z]`, and dropping the printed
  rank comparison entirely.

What genuinely remains on the Section 6 tangent side is the *unbounded Ritz
compression* of the Appendix: the trial-block records carry the compression as a
bounded field, so the source's `Ω(τ) A₀ Ω(τ)` truncation is not reproduced. That
obligation is tracked on census row `DK-6-appendix`, not here.
-/

namespace TauCeti
namespace DavisKahan1970

/-! ## The finite source theorem, literal orientation, every UI norm -/

/-- The source's one-sided interval hypothesis: Ritz spectrum in `[β, α]`,
unwanted exact spectrum at least `α + δ`. -/
alias Theorem6_3_intervalGap := DavisKahan.FiniteDimensional.TanThetaIntervalGap

/-- Transversality is a conclusion of the source placement, not a
hypothesis. -/
alias Theorem6_3_transversality :=
  DavisKahan.FiniteDimensional.isTransverse_of_tanThetaIntervalGap

/-- **Davis--Kahan 1970, Theorem 6.3, finite form.**  Strict-lower-rank trial
space, Rayleigh--Ritz residual, one-sided spectral gap; the bound holds for
every rectangular unitarily invariant norm and any `tan Θ₀` representative
with the principal-tangent singular values. -/
alias theorem6_3 :=
  DavisKahan.FiniteDimensional.davisKahan1970_generalizedTanTheta0_ritzResidual_le

/-- Equal-rank companion of `theorem6_3`; this is the Section 2 `tan Θ`
statement in Ritz-residual form. -/
alias Theorem6_3_equalRank :=
  DavisKahan.FiniteDimensional.davisKahan1970_tanTheta0_ritzResidual_le

/-- Ky Fan root of the finite theorem, equation (6.6): the prefix sums of the
tangent singular values are controlled by those of the residual. -/
alias Theorem6_3_kyFan := DavisKahan.FiniteDimensional.kyFan_tanTheta0_ritzResidual_le

/-! ## The general Hilbert-space theorem, graph-angle operator form

`A` is an unbounded self-adjoint closed operator on a complex Hilbert space.
The trial block packages a subspace of the operator domain together with its
Ritz compression and bounded residual; the transverse coordinates select the
graph branch of the trial space over the exact spectral subspace.  These are
the paper's objects with the domain bookkeeping made explicit. -/

/-- Bundled Rayleigh--Ritz trial block for an unbounded operator: domain
inclusion, self-adjoint compression, and bounded residual. -/
alias TanThetaTrialBlock :=
  DavisKahan.TanTheta.BoundedCompressionTrialBlock

/-- Proof-carrying transversality: the orthogonal projection restricts to a
bounded linear equivalence from the trial subspace onto the exact subspace. -/
alias TanThetaTransverseCoordinates :=
  DavisKahan.TanTheta.TrialExactCoordinates

/-- The bounded tangent operator of the trial graph over the exact
subspace: the source's `tan Θ` direction. -/
alias tanThetaGraphOperator :=
  DavisKahan.TanTheta.TrialExactCoordinates.angularMap

/-- The graph of the tangent operator is exactly the trial subspace. -/
alias tanThetaGraphOperator_range :=
  DavisKahan.TanTheta.TrialExactCoordinates.range_graphEmbedding

/-- **Davis--Kahan 1970, Theorem 6.3, general Hilbert-space graph-angle
form at operator norm.**  For an unbounded self-adjoint `A`, a genuine
exterior Ritz spectrum, and transverse coordinates over the complement of the
interval spectral subspace, `δ · ‖tan Θ‖ ≤ ‖R‖`. -/
alias Theorem6_3_unbounded_graphAngle_opNorm :=
  DavisKahan.TanTheta.tanTheta_unbounded_graphAngle_trialBlock

/-- Per-vector unbounded form with a genuine Ritz-spectrum hypothesis. -/
alias Theorem6_3_unbounded_vector :=
  DavisKahan.TanTheta.tanTheta_unbounded_exactSpectralIcc_trialBlock

/-- Per-vector unbounded form with an explicit coercivity hypothesis on the
compressed shifted operator. -/
alias Theorem6_3_unbounded_vector_of_coercivity :=
  DavisKahan.TanTheta.tanTheta_unbounded_exactSpectralIcc

/-- Per-vector bounded form with genuine compression spectra. -/
alias Theorem6_3_bounded_vector := DavisKahanExt.tanTheta_spectrum

/-- Per-vector bounded form in the source's literal **one-sided**
orientation: test compression spectrum below `α₀`, unwanted compression
spectrum in `[α₀ + δ, ∞)`.  The interval cap of the interval/exterior form
is recovered from boundedness of the compression, so no upper bound is
assumed. -/
alias Theorem6_3_bounded_vector_oneSided :=
  DavisKahanExt.tanTheta_spectrum_oneSided

/-- Per-vector bounded form from quadratic-form bounds alone; the
low-dependency Hilbert-space companion. -/
alias Theorem6_3_bounded_vector_formBounds := DavisKahanExt.tan_theta_le'

end DavisKahan1970
end TauCeti
