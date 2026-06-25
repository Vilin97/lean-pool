/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.TraceExp

/-!
# Matrix Laplace statement vocabulary

Verified Wikipedia references:
* Matrix exponential: https://en.wikipedia.org/wiki/Matrix_exponential
* Trace: https://en.wikipedia.org/wiki/Trace_(linear_algebra)
* Chernoff bound: https://en.wikipedia.org/wiki/Chernoff_bound
* Matrix Chernoff bound: https://en.wikipedia.org/wiki/Matrix_Chernoff_bound

Note: despite the file name, the comments here cite the trace-exponential
Laplace method used in matrix concentration, not the classical integral
Laplace transform page.

This module records honest typed targets for the future matrix Laplace method.
It does not prove a matrix Laplace theorem, matrix Chernoff theorem, trace-mgf
bound, or matrix Bernstein theorem.
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/-- Right-hand side of the trace-exponential Laplace bound for an upper
quadratic-form tail event. -/
def matrixLaplaceRHS {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (Y : RandomMatrix Omega n n) (theta t : Real) :
    ENNReal :=
  ENNReal.ofReal (Real.exp (-(theta * t)) * traceExpMoment P Y theta)

/-- LIntegral right-hand side for the matrix Laplace upper-tail reduction. -/
def matrixLaplaceRHSLIntegral {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (Y : RandomMatrix Omega n n) (theta t : Real) :
    ENNReal :=
  ENNReal.ofReal (Real.exp (-(theta * t))) * traceExpMomentLIntegral P Y theta

/-- Trace-exponential threshold event used by the conditional matrix Laplace
Markov bridge.

This event is deliberately separate from `quadraticFormUpperTailEvent`: the
missing spectral/trace comparison must be supplied as an explicit subset
hypothesis by any theorem that starts from quadratic-form tails. -/
def traceExpThresholdEvent {Omega : Type*} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real) : Set Omega :=
  {omega | ENNReal.ofReal (Real.exp (theta * t)) <=
    ENNReal.ofReal (traceExpIntegrand Y theta omega)}

/-- Semantic trace-exponential dominance for a deterministic scalar upper
bound `L`.

This does not assert that any particular spectral provider, such as
`lambdaMaxOrdered`, supplies such a bound.  It only packages the deterministic
trace-exponential inequality needed by the event-level Laplace bridge. -/
def TraceExpDominatesUpperBound {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (L theta : Real) : Prop :=
  Real.exp (theta * L) <= traceMatrixExp (theta • A)

/-- The ordered largest-eigenvalue endpoint provides trace-exponential
dominance for nonnegative Laplace parameters.

The proof composes the MB-S7B helper split: nonnegative scalar endpoint
scaling, matrix-exponential spectral mapping, and trace domination of the
largest endpoint for positive semidefinite matrices. -/
theorem lambdaMaxOrdered_traceExpDominatesUpperBound
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) (theta : Real) (hTheta : 0 <= theta) :
    TraceExpDominatesUpperBound A (lambdaMaxOrdered A hA) theta := by
  let hThetaA : IsSelfAdjointMatrix (theta • A) :=
    isSelfAdjointMatrix_smul theta hA
  let hExpThetaA : IsSelfAdjointMatrix (matrixExp (theta • A)) :=
    isSelfAdjointMatrix_matrixExp hThetaA
  have hPSD : Matrix.PosSemidef (matrixExp (theta • A)) :=
    matrixExp_posSemidef_of_selfAdjoint hThetaA
  have hTrace :
      lambdaMaxOrdered (matrixExp (theta • A)) hExpThetaA <=
        Matrix.trace (matrixExp (theta • A)) :=
    lambdaMaxOrdered_le_trace_of_posSemidef hExpThetaA hPSD
  have hExpMap :
      lambdaMaxOrdered (matrixExp (theta • A)) hExpThetaA =
        Real.exp (lambdaMaxOrdered (theta • A) hThetaA) :=
    lambdaMaxOrdered_matrixExp hThetaA
  have hSmul :
      lambdaMaxOrdered (theta • A) hThetaA =
        theta * lambdaMaxOrdered A hA :=
    lambdaMaxOrdered_smul_of_nonneg theta hTheta hA
  have hProvider :
      Real.exp (theta * lambdaMaxOrdered A hA) <=
        Matrix.trace (matrixExp (theta • A)) := by
    calc
      Real.exp (theta * lambdaMaxOrdered A hA)
          = Real.exp (lambdaMaxOrdered (theta • A) hThetaA) := by
              rw [hSmul]
      _ = lambdaMaxOrdered (matrixExp (theta • A)) hExpThetaA := by
              rw [hExpMap]
      _ <= Matrix.trace (matrixExp (theta • A)) := hTrace
  simpa [TraceExpDominatesUpperBound, traceMatrixExp, matrixTrace] using hProvider

/-- Pointwise trace-exponential dominance turns the semantic matrix upper-bound
tail event into the trace-exponential threshold event. -/
theorem matrixUpperBoundTailEvent_subset_traceExpThresholdEvent_of_traceExpDominatesUpperBound
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (Y : RandomMatrix Omega n n) (L : Omega -> Real) (theta t : Real)
    (hTheta : 0 <= theta)
    (hDom : forall omega,
      TraceExpDominatesUpperBound (Y omega) (L omega) theta) :
    matrixUpperBoundTailEvent Y L t ⊆ traceExpThresholdEvent Y theta t := by
  intro omega hTail
  have htL : t <= L omega := by
    simpa [matrixUpperBoundTailEvent, scalarUpperTailEvent] using hTail
  have hMul : theta * t <= theta * L omega :=
    mul_le_mul_of_nonneg_left htL hTheta
  have hExp : Real.exp (theta * t) <= Real.exp (theta * L omega) :=
    Real.exp_le_exp.mpr hMul
  have hDomOmega :
      Real.exp (theta * L omega) <= traceExpIntegrand Y theta omega := by
    change Real.exp (theta * L omega) <= traceMatrixExp (theta • Y omega)
    exact hDom omega
  exact ENNReal.ofReal_le_ofReal (hExp.trans hDomOmega)

/-- Division-normal form of the lintegral matrix Laplace right-hand side.

This is the direct normal form produced by Mathlib's lintegral Markov theorem.
It is definitionally separate from `matrixLaplaceRHSLIntegral` only to keep the
Markov proof simple and auditable. -/
def matrixLaplaceRHSLIntegralDiv {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (Y : RandomMatrix Omega n n)
    (theta t : Real) : ENNReal :=
  traceExpMomentLIntegral P Y theta /
    ENNReal.ofReal (Real.exp (theta * t))

/-- The division-normal lintegral RHS agrees with the existing product RHS. -/
theorem matrixLaplaceRHSLIntegralDiv_eq_matrixLaplaceRHSLIntegral
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real) :
    matrixLaplaceRHSLIntegralDiv P Y theta t =
      matrixLaplaceRHSLIntegral P Y theta t := by
  rw [matrixLaplaceRHSLIntegralDiv, matrixLaplaceRHSLIntegral]
  rw [div_eq_mul_inv]
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos (theta * t))]
  rw [← Real.exp_neg]
  rw [mul_comm]

/-- LIntegral Markov bound for the trace-exponential threshold event. -/
theorem traceExpThresholdEvent_lintegral_bound {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real)
    (hMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P) :
    P (traceExpThresholdEvent Y theta t) <=
      matrixLaplaceRHSLIntegral P Y theta t := by
  calc
    P (traceExpThresholdEvent Y theta t)
        <= matrixLaplaceRHSLIntegralDiv P Y theta t :=
          MeasureTheory.meas_ge_le_lintegral_div hMeas
            (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos (theta * t)))
            ENNReal.ofReal_ne_top
    _ = matrixLaplaceRHSLIntegral P Y theta t :=
          matrixLaplaceRHSLIntegralDiv_eq_matrixLaplaceRHSLIntegral Y theta t

/-- Conditional quadratic-form matrix Laplace bridge in division-normal form.

The subset hypothesis is the currently missing spectral/trace bridge. -/
theorem matrixLaplaceTransformLIntegralDiv_of_traceExpThreshold_subset
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real)
    (hMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P)
    (hSubset :
      quadraticFormUpperTailEvent Y t ⊆ traceExpThresholdEvent Y theta t) :
    P (quadraticFormUpperTailEvent Y t) <=
      matrixLaplaceRHSLIntegralDiv P Y theta t := by
  calc
    P (quadraticFormUpperTailEvent Y t)
        <= P (traceExpThresholdEvent Y theta t) :=
          measure_mono hSubset
    _ <= matrixLaplaceRHSLIntegralDiv P Y theta t := by
          rw [matrixLaplaceRHSLIntegralDiv_eq_matrixLaplaceRHSLIntegral]
          exact traceExpThresholdEvent_lintegral_bound Y theta t hMeas

/-- Conditional quadratic-form matrix Laplace bridge.

This does not prove `matrixLaplaceTransformLIntegralStatement`; it assumes the
missing event-subset bridge explicitly. -/
theorem matrixLaplaceTransformLIntegral_of_traceExpThreshold_subset
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real)
    (hMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P)
    (hSubset :
      quadraticFormUpperTailEvent Y t ⊆ traceExpThresholdEvent Y theta t) :
    P (quadraticFormUpperTailEvent Y t) <=
      matrixLaplaceRHSLIntegral P Y theta t := by
  exact
    (matrixLaplaceTransformLIntegralDiv_of_traceExpThreshold_subset
      Y theta t hMeas hSubset).trans_eq
      (matrixLaplaceRHSLIntegralDiv_eq_matrixLaplaceRHSLIntegral Y theta t)

/-- Explicit dominance hypothesis for the source-backed spectral step.

The book proof routes largest-eigenvalue tails through a trace-exponential
threshold.  The current HighDimProb API uses the proof-friendly
`quadraticFormUpperTailEvent`; the spectral/Rayleigh bridge from that event to
this threshold is not proved yet, so MB-S6 exposes it as a named hypothesis. -/
def TraceExpDominatesQuadraticFormUpperTail {Omega : Type*}
    {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real) : Prop :=
  quadraticFormUpperTailEvent Y t ⊆ traceExpThresholdEvent Y theta t

/-- Typed target for the future source-backed spectral dominance bridge.

This is not a theorem.  It records the intended shape of the missing step from
the book-level largest-eigenvalue/trace-exponential argument to the current
HighDimProb quadratic-form event API. -/
abbrev traceExpDominatesQuadraticFormUpperTailStatement {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 <= theta ->
      TraceExpDominatesQuadraticFormUpperTail Y theta t

/-- Unpack the explicit trace-exponential dominance hypothesis as the event
subset needed by the MB-S5 conditional Laplace bridge. -/
theorem quadraticFormUpperTailEvent_subset_traceExpThresholdEvent_of_traceExpDominates
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real)
    (hDom : TraceExpDominatesQuadraticFormUpperTail Y theta t) :
    quadraticFormUpperTailEvent Y t ⊆ traceExpThresholdEvent Y theta t :=
  hDom

/-- Rayleigh upper bounds plus pointwise trace-exponential dominance imply the
trace-exponential threshold event subset needed by the conditional Laplace
bridge. -/
theorem quadraticFormTailEvent_subset_traceExpThresholdEvent_of_rayleighBound_and_traceExpDomination
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (Y : RandomMatrix Omega n n) (L : Omega -> Real) (theta t : Real)
    (hTheta : 0 <= theta)
    (hRayleigh : forall omega, RayleighUpperBound (Y omega) (L omega))
    (hDom : forall omega,
      TraceExpDominatesUpperBound (Y omega) (L omega) theta) :
    quadraticFormUpperTailEvent Y t ⊆ traceExpThresholdEvent Y theta t :=
  Set.Subset.trans
    (quadraticFormUpperTailEvent_subset_matrixUpperBoundTailEvent_of_rayleighUpperBound
      Y L t hRayleigh)
    (matrixUpperBoundTailEvent_subset_traceExpThresholdEvent_of_traceExpDominatesUpperBound
      Y L theta t hTheta hDom)

/-- Spectral upper bounds plus pointwise trace-exponential dominance imply the
trace-exponential threshold event subset needed by the conditional Laplace
bridge. -/
theorem quadraticFormTailEvent_subset_traceExpThresholdEvent_of_spectralBound_and_traceExpDomination
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (Y : RandomMatrix Omega n n) (L : Omega -> Real) (theta t : Real)
    (hTheta : 0 <= theta)
    (hUpper : forall omega, SpectralUpperBound (Y omega) (L omega))
    (hDom : forall omega,
      TraceExpDominatesUpperBound (Y omega) (L omega) theta) :
    quadraticFormUpperTailEvent Y t ⊆ traceExpThresholdEvent Y theta t :=
  Set.Subset.trans
    (quadraticFormUpperTailEvent_subset_matrixUpperBoundTailEvent_of_spectralUpperBound
      Y L t hUpper)
    (matrixUpperBoundTailEvent_subset_traceExpThresholdEvent_of_traceExpDominatesUpperBound
      Y L theta t hTheta hDom)

/-- Package the Rayleigh semantic route as the existing MB-S6 dominance
hypothesis. -/
theorem traceExpDominatesQuadraticFormUpperTail_of_rayleighUpperBound_of_traceExpDominatesUpperBound
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (Y : RandomMatrix Omega n n) (L : Omega -> Real) (theta t : Real)
    (hTheta : 0 <= theta)
    (hRayleigh : forall omega, RayleighUpperBound (Y omega) (L omega))
    (hDom : forall omega,
      TraceExpDominatesUpperBound (Y omega) (L omega) theta) :
    TraceExpDominatesQuadraticFormUpperTail Y theta t :=
  quadraticFormTailEvent_subset_traceExpThresholdEvent_of_rayleighBound_and_traceExpDomination
    Y L theta t hTheta hRayleigh hDom

/-- Package the spectral semantic route as the existing MB-S6 dominance
hypothesis. -/
theorem traceExpDominatesQuadraticFormUpperTail_of_spectralUpperBound_of_traceExpDominatesUpperBound
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (Y : RandomMatrix Omega n n) (L : Omega -> Real) (theta t : Real)
    (hTheta : 0 <= theta)
    (hUpper : forall omega, SpectralUpperBound (Y omega) (L omega))
    (hDom : forall omega,
      TraceExpDominatesUpperBound (Y omega) (L omega) theta) :
    TraceExpDominatesQuadraticFormUpperTail Y theta t :=
  quadraticFormTailEvent_subset_traceExpThresholdEvent_of_spectralBound_and_traceExpDomination
    Y L theta t hTheta hUpper hDom

/-- Concrete trace-exponential dominance for random self-adjoint matrices via
the canonical ordered endpoint provider.

This only assembles existing MB-S7A/MB-S7B providers and the generic semantic
bridge.  It does not prove full matrix Laplace or any trace-mgf inequality. -/
theorem traceExpDominatesQuadraticFormUpperTail_of_randomSelfAdjoint
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega (n + 1) (n + 1)) (theta t : Real)
    (hY : RandomSelfAdjointMatrix P Y) (hTheta : 0 <= theta) :
    TraceExpDominatesQuadraticFormUpperTail Y theta t := by
  let L : Omega -> Real := fun omega =>
    lambdaMaxOrdered (Y omega) (hY omega)
  exact
    traceExpDominatesQuadraticFormUpperTail_of_rayleighUpperBound_of_traceExpDominatesUpperBound
      Y L theta t hTheta
      (by
        intro omega
        exact lambdaMaxOrdered_rayleighUpperBound (hY omega))
      (by
        intro omega
        exact lambdaMaxOrdered_traceExpDominatesUpperBound (hY omega) theta hTheta)

/-- Conditional quadratic-form matrix Laplace bridge using the named MB-S6
dominance hypothesis, in division-normal form. -/
theorem matrixLaplaceTransformLIntegralDiv_of_traceExpDominatesQuadraticFormUpperTail
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real)
    (hMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P)
    (hDom : TraceExpDominatesQuadraticFormUpperTail Y theta t) :
    P (quadraticFormUpperTailEvent Y t) <=
      matrixLaplaceRHSLIntegralDiv P Y theta t :=
  matrixLaplaceTransformLIntegralDiv_of_traceExpThreshold_subset
    Y theta t hMeas
    (quadraticFormUpperTailEvent_subset_traceExpThresholdEvent_of_traceExpDominates
      Y theta t hDom)

/-- Conditional quadratic-form matrix Laplace bridge using the named MB-S6
dominance hypothesis. -/
theorem matrixLaplaceTransformLIntegral_of_traceExpDominatesQuadraticFormUpperTail
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta t : Real)
    (hMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P)
    (hDom : TraceExpDominatesQuadraticFormUpperTail Y theta t) :
    P (quadraticFormUpperTailEvent Y t) <=
      matrixLaplaceRHSLIntegral P Y theta t :=
  matrixLaplaceTransformLIntegral_of_traceExpThreshold_subset
    Y theta t hMeas
    (quadraticFormUpperTailEvent_subset_traceExpThresholdEvent_of_traceExpDominates
      Y theta t hDom)

/-- Concrete lintegral matrix Laplace bridge for random self-adjoint matrices,
in division-normal form.

This only assembles the concrete MB-S7C dominance theorem with the existing
conditional Laplace wrapper. It keeps the trace-exp integrand measurability
hypothesis explicit and does not prove any trace-mgf bound. -/
theorem matrixLaplaceTransformLIntegralDiv_of_randomSelfAdjoint
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega (n + 1) (n + 1)) (theta t : Real)
    (hMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P)
    (hY : RandomSelfAdjointMatrix P Y) (hTheta : 0 <= theta) :
    P (quadraticFormUpperTailEvent Y t) <=
      matrixLaplaceRHSLIntegralDiv P Y theta t :=
  matrixLaplaceTransformLIntegralDiv_of_traceExpDominatesQuadraticFormUpperTail
    Y theta t hMeas
    (traceExpDominatesQuadraticFormUpperTail_of_randomSelfAdjoint
      Y theta t hY hTheta)

/-- Concrete lintegral matrix Laplace bridge for random self-adjoint matrices.

This is the product-RHS version obtained from the concrete MB-S7C dominance
theorem and the existing conditional Laplace wrapper. It does not prove the
real-valued RHS bridge, trace-mgf bounds, or Matrix Bernstein. -/
theorem matrixLaplaceTransformLIntegral_of_randomSelfAdjoint
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega (n + 1) (n + 1)) (theta t : Real)
    (hMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P)
    (hY : RandomSelfAdjointMatrix P Y) (hTheta : 0 <= theta) :
    P (quadraticFormUpperTailEvent Y t) <=
      matrixLaplaceRHSLIntegral P Y theta t :=
  matrixLaplaceTransformLIntegral_of_traceExpDominatesQuadraticFormUpperTail
    Y theta t hMeas
    (traceExpDominatesQuadraticFormUpperTail_of_randomSelfAdjoint
      Y theta t hY hTheta)

/-- Substitute a bounded-Bernstein lintegral trace-MGF bound into the product
form of the matrix Laplace RHS.

This is a reusable lintegral-level bridge. It does not need real integrability
or nonnegativity hypotheses because those belong to whatever theorem produces
the lintegral trace-MGF bound. -/
theorem matrixLaplaceRHSLIntegral_le_of_traceMGFBernsteinVarianceProxyBoundLIntegral
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta t R : Real)
    (hBound : TraceMGFBernsteinVarianceProxyBoundLIntegral P Y V theta R) :
    matrixLaplaceRHSLIntegral P Y theta t <=
      ENNReal.ofReal (Real.exp (-(theta * t))) *
        ENNReal.ofReal
          (traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V)) := by
  unfold matrixLaplaceRHSLIntegral
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_left hBound (ENNReal.ofReal (Real.exp (-(theta * t))))

/-- Conditional quadratic-form upper-tail bound from an explicit event-subset
bridge and a bounded-Bernstein lintegral trace-MGF bound.

This packages the reusable PR-style contract without hiding the two required
inputs: the event subset and the lintegral trace-MGF provider. -/
theorem quadraticFormUpperTail_laplace_bound_of_traceMGFBernsteinVarianceProxyBoundLIntegral
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta t R : Real)
    (hMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P)
    (hSubset :
      quadraticFormUpperTailEvent Y t ⊆ traceExpThresholdEvent Y theta t)
    (hBound : TraceMGFBernsteinVarianceProxyBoundLIntegral P Y V theta R) :
    P (quadraticFormUpperTailEvent Y t) <=
      ENNReal.ofReal (Real.exp (-(theta * t))) *
        ENNReal.ofReal
          (traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V)) :=
  calc
    P (quadraticFormUpperTailEvent Y t)
        <= matrixLaplaceRHSLIntegral P Y theta t :=
          matrixLaplaceTransformLIntegral_of_traceExpThreshold_subset
            Y theta t hMeas hSubset
    _ <= ENNReal.ofReal (Real.exp (-(theta * t))) *
          ENNReal.ofReal
            (traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V)) :=
          matrixLaplaceRHSLIntegral_le_of_traceMGFBernsteinVarianceProxyBoundLIntegral
            Y V theta t R hBound

/-- Typed target for the reusable bounded-Bernstein lintegral trace-MGF to
quadratic-form Laplace contract. -/
abbrev quadraticFormTailLaplaceTraceMGFVarianceProxyBoundLIntegralStatement
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta t R : Real) : Prop :=
  AEMeasurable (fun omega => ENNReal.ofReal (traceExpIntegrand Y theta omega)) P ->
    (quadraticFormUpperTailEvent Y t ⊆ traceExpThresholdEvent Y theta t) ->
      TraceMGFBernsteinVarianceProxyBoundLIntegral P Y V theta R ->
        P (quadraticFormUpperTailEvent Y t) <=
          ENNReal.ofReal (Real.exp (-(theta * t))) *
            ENNReal.ofReal
              (traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V))

/-- Typed target for the matrix Laplace transform upper-tail reduction.

The event is the proof-friendly quadratic-form upper-tail event from
`HighDimProb.RandomMatrix.Spectral`, standing in for a future lambda-max event
until the Rayleigh quotient bridge is proved. -/
abbrev matrixLaplaceTransformStatement {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (Y : RandomMatrix Omega n n)
    (theta t : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 < theta ->
      0 <= traceExpMoment P Y theta ->
        P (quadraticFormUpperTailEvent Y t) <= matrixLaplaceRHS P Y theta t

/-- LIntegral-form typed target for the matrix Laplace upper-tail reduction. -/
abbrev matrixLaplaceTransformLIntegralStatement {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (theta t : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 < theta ->
      P (quadraticFormUpperTailEvent Y t) <=
        matrixLaplaceRHSLIntegral P Y theta t

/-- Typed target for the scalar Chernoff step once a trace-exponential moment
bound has been supplied. -/
abbrev matrixChernoffFromTraceExpStatement {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (theta t rhs : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 < theta ->
      0 <= rhs ->
        traceExpMoment P Y theta <= rhs ->
          P (quadraticFormUpperTailEvent Y t) <=
            ENNReal.ofReal (Real.exp (-(theta * t)) * rhs)

/-- LIntegral-form typed target for the scalar Chernoff step once a
trace-exponential lintegral bound has been supplied. -/
abbrev matrixChernoffFromTraceExpLIntegralStatement {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (theta t : Real) (rhs : ENNReal) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 < theta ->
      traceExpMomentLIntegral P Y theta <= rhs ->
        P (quadraticFormUpperTailEvent Y t) <=
          ENNReal.ofReal (Real.exp (-(theta * t))) * rhs

/-- LIntegral right-hand side for the two-sided self-adjoint operator-norm
Laplace route. -/
def selfAdjointOperatorNormLaplaceRHSLIntegral {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (theta t : Real) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(theta * t))) *
    (traceExpMomentLIntegral P Y theta +
      traceExpMomentLIntegral P (fun omega => -Y omega) theta)

/-- Typed target for the two-sided self-adjoint operator-norm Laplace route.

The right side uses the usual trace-exponential moments of `Y` and `-Y`. This
remains a statement target because the operator-norm/lambda-max reduction and
matrix Laplace theorem are not proved here. -/
abbrev selfAdjointOperatorNormLaplaceStatement {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (theta t : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 < theta ->
      0 <= traceExpMoment P Y theta ->
        0 <= traceExpMoment P (fun omega => -Y omega) theta ->
          P (SelfAdjointOperatorNormTailEvent Y t) <=
            ENNReal.ofReal
              (Real.exp (-(theta * t)) *
                (traceExpMoment P Y theta +
                  traceExpMoment P (fun omega => -Y omega) theta))

/-- LIntegral-form typed target for the two-sided self-adjoint operator-norm
Laplace route. -/
abbrev selfAdjointOperatorNormLaplaceLIntegralStatement {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (theta t : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 < theta ->
      P (SelfAdjointOperatorNormTailEvent Y t) <=
        selfAdjointOperatorNormLaplaceRHSLIntegral P Y theta t

end

end HighDimProb
