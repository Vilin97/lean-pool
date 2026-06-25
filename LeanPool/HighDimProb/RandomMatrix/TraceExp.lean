/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import LeanPool.HighDimProb.RandomMatrix.Spectral
import LeanPool.HighDimProb.RandomMatrix.VarianceProxy
import LeanPool.HighDimProb.Analysis.RealInequalities

/-!
# Matrix exponential and trace-exponential vocabulary

Verified Wikipedia references:
* Matrix exponential: https://en.wikipedia.org/wiki/Matrix_exponential
* Trace: https://en.wikipedia.org/wiki/Trace_(linear_algebra)
* Self-adjoint operator: https://en.wikipedia.org/wiki/Self-adjoint_operator
* Loewner order: https://en.wikipedia.org/wiki/Loewner_order

Note: Golden-Thompson-type trace-exponential inequalities are background for
this area, but this file's current comments only cite concepts directly present
in the definitions and theorem statements.

Mathlib provides matrix exponential facts through `NormedSpace.exp` and
`Mathlib.Analysis.Normed.Algebra.MatrixExponential`. This module wraps those
objects with HighDimProb-facing names for future matrix Laplace and trace-mgf
arguments.

No Golden-Thompson, Lieb, trace-mgf, or matrix Bernstein theorem is proved
here.
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/-- Matrix exponential wrapper using Mathlib's `NormedSpace.exp`. -/
def matrixExp {n : Nat} (A : Matrix (Fin n) (Fin n) Real) :
    Matrix (Fin n) (Fin n) Real :=
  NormedSpace.exp A

@[simp]
theorem matrixExp_apply {n : Nat} (A : Matrix (Fin n) (Fin n) Real) :
    matrixExp A = NormedSpace.exp A :=
  rfl

/-- Matrix trace wrapper. -/
def matrixTrace {n : Nat} (A : Matrix (Fin n) (Fin n) Real) : Real :=
  Matrix.trace A

@[simp]
theorem matrixTrace_apply {n : Nat} (A : Matrix (Fin n) (Fin n) Real) :
    matrixTrace A = Matrix.trace A :=
  rfl

/-- Trace/rank certificate for star-projection matrices.

This deterministic bridge only identifies the trace of an explicit star projection
with its matrix rank. It does not construct support domination, support
projections for another matrix, or a true effective-rank certificate. -/
theorem matrixTrace_eq_rank_of_isStarProjection {n : Nat}
    {support : Matrix (Fin n) (Fin n) Real}
    (hSupport : IsStarProjection support) :
    matrixTrace support = (Matrix.rank support : Real) := by
  classical
  let f : (Fin n → Real) →ₗ[Real] (Fin n → Real) := Matrix.toLin' support
  have hIdemMatrix : support * support = support :=
    hSupport.isIdempotentElem.eq
  have hfIdem : IsIdempotentElem f := by
    change f * f = f
    dsimp [f]
    rw [Module.End.mul_eq_comp]
    rw [← Matrix.toLin'_mul]
    simp [hIdemMatrix]
  have hProj : LinearMap.IsProj (LinearMap.range f) f :=
    (LinearMap.isProj_range_iff_isIdempotentElem f).2 hfIdem
  have hTraceLin :
      LinearMap.trace Real (Fin n → Real) f =
        (Module.finrank Real (LinearMap.range f) : Real) :=
    LinearMap.IsProj.trace hProj
  have hTraceMatrix :
      LinearMap.trace Real (Fin n → Real) f = Matrix.trace support := by
    simp [f]
  have hRank :
      Matrix.rank support = Module.finrank Real (LinearMap.range f) := by
    have hr := Matrix.rank_eq_finrank_range_toLin support
      (Pi.basisFun Real (Fin n)) (Pi.basisFun Real (Fin n))
    exact hr
  calc
    matrixTrace support = Matrix.trace support := rfl
    _ = LinearMap.trace Real (Fin n → Real) f := hTraceMatrix.symm
    _ = (Module.finrank Real (LinearMap.range f) : Real) := hTraceLin
    _ = (Matrix.rank support : Real) := by rw [hRank]

section StarProjectionPSD

open scoped MatrixOrder

/-- Star projections are PSD in HighDimProb's explicit quadratic-form order.

This deterministic conversion bridge reuses Mathlib's ordered star-projection
fact `IsStarProjection.nonneg` and the matrix-order equivalence
`Matrix.nonneg_iff_posSemidef`. It does not construct a support projection or
prove any support-domination certificate for another matrix. -/
theorem isPSDMatrix_of_isStarProjection {n : Nat}
    {support : Matrix (Fin n) (Fin n) Real}
    (hSupport : IsStarProjection support) :
    IsPSDMatrix support := by
  have hNonneg : 0 <= support := hSupport.nonneg
  have hPSD : Matrix.PosSemidef support :=
    Matrix.nonneg_iff_posSemidef.mp hNonneg
  constructor
  · apply Matrix.IsSymm.ext
    intro i j
    have h := Matrix.IsHermitian.apply hPSD.isHermitian i j
    simpa using h
  · intro x
    exact matrixQuadraticForm_nonneg_of_posSemidef hPSD x

end StarProjectionPSD

/-- Trace of the matrix exponential. -/
def traceMatrixExp {n : Nat} (A : Matrix (Fin n) (Fin n) Real) : Real :=
  matrixTrace (matrixExp A)

@[simp]
theorem traceMatrixExp_apply {n : Nat} (A : Matrix (Fin n) (Fin n) Real) :
    traceMatrixExp A = Matrix.trace (NormedSpace.exp A) :=
  rfl

/-- Matrix exponentials preserve real self-adjointness. -/
theorem isSelfAdjointMatrix_matrixExp {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    IsSelfAdjointMatrix (matrixExp A) := by
  simpa [matrixExp] using Matrix.IsHermitian.exp hA

/-- A Mathlib-positive-semidefinite matrix has nonnegative trace. -/
theorem matrixTrace_nonneg_of_posSemidef {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : Matrix.PosSemidef A) :
    0 <= matrixTrace A := by
  simpa [matrixTrace] using hA.trace_nonneg

/-- Trace commutes with scalar multiplication through the HighDimProb wrapper. -/
theorem matrixTrace_smul {n : Nat} (c : Real)
    (A : Matrix (Fin n) (Fin n) Real) :
    matrixTrace (c • A) = c * matrixTrace A := by
  simp [matrixTrace]

/-- The explicit HighDimProb Loewner comparison is monotone for trace. -/
theorem matrixTrace_le_of_matrixLE {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Real} (hAB : MatrixLE A B) :
    matrixTrace A <= matrixTrace B := by
  have hPSD : Matrix.PosSemidef (B - A) := posSemidef_of_isPSDMatrix hAB
  have hnonneg : 0 <= matrixTrace (B - A) :=
    matrixTrace_nonneg_of_posSemidef hPSD
  rw [matrixTrace, Matrix.trace_sub] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Ambient trace certificate from PSD and an ordered lambda-max bound.

This gives the trace certificate needed by effective-rank consumers only with
the ambient dimension as the rank parameter. It does not define effective rank
or prove a support/rank projection theorem. -/
theorem matrixTrace_le_card_mul_of_isPSD_lambdaMaxOrdered_le
    {n : Nat} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    {sigmaSq : Real}
    (hPSD : IsPSDMatrix V)
    (hV : IsSelfAdjointMatrix V)
    (hSpec : lambdaMaxOrdered V hV <= sigmaSq) :
    matrixTrace V <= ((n + 1 : Nat) : Real) * sigmaSq := by
  classical
  let e : Equiv (Fin (Fintype.card (Fin (n + 1)))) (Fin (n + 1)) :=
    Fintype.equivOfCardEq (by simp)
  have _hPSD' : Matrix.PosSemidef V := posSemidef_of_isPSDMatrix hPSD
  have htrace :
      matrixTrace V = Finset.univ.sum (fun i : Fin (n + 1) => hV.eigenvalues i) := by
    simpa [matrixTrace] using hV.trace_eq_sum_eigenvalues
  have hterm : forall i : Fin (n + 1), hV.eigenvalues i <= sigmaSq := by
    intro i
    have hgreat :=
      lambdaMaxOrdered_is_greatest_eigenvalue V hV (e.symm i)
    have hi : hV.eigenvalues i <= lambdaMaxOrdered V hV := by
      simpa [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues, e] using hgreat
    exact hi.trans hSpec
  calc
    matrixTrace V
        = Finset.univ.sum (fun i : Fin (n + 1) => hV.eigenvalues i) := htrace
    _ <= Finset.univ.sum (fun _i : Fin (n + 1) => sigmaSq) := by
          exact Finset.sum_le_sum (by
            intro i _hi
            exact hterm i)
    _ = ((n + 1 : Nat) : Real) * sigmaSq := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- If the matrix exponential is known to be Mathlib-positive-semidefinite,
then its trace is nonnegative.  The remaining self-adjoint-to-PSD bridge is
recorded by `matrixExpPosSemidefOfSelfAdjointStatement`. -/
theorem traceMatrixExp_nonneg_of_matrixExp_posSemidef {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real}
    (hA : Matrix.PosSemidef (matrixExp A)) :
    0 <= traceMatrixExp A := by
  simpa [traceMatrixExp] using
    (matrixTrace_nonneg_of_posSemidef (A := matrixExp A) hA)

/-- Compatibility target: the matrix exponential of a real self-adjoint matrix
is Mathlib-positive-semidefinite. -/
abbrev matrixExpPosSemidefOfSelfAdjointStatement {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) : Prop :=
  IsSelfAdjointMatrix A -> Matrix.PosSemidef (matrixExp A)

section MatrixExpPosSemidef

open scoped MatrixOrder Matrix.Norms.Operator Matrix.Norms.L2Operator

/-- The matrix exponential of a real self-adjoint matrix is
Mathlib-positive-semidefinite.

The proof uses Mathlib's scoped matrix Loewner order and the CFC theorem
`IsSelfAdjoint.exp_nonneg`, then converts `0 <= exp A` back to
`Matrix.PosSemidef`. -/
theorem matrixExp_posSemidef_of_selfAdjoint {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    Matrix.PosSemidef (matrixExp A) := by
  exact Matrix.nonneg_iff_posSemidef.mp (by
    simpa [matrixExp] using IsSelfAdjoint.exp_nonneg hA.isSelfAdjoint)

/-- Matrix exponential dominates its affine first-order lower bound in the
explicit HighDimProb Loewner-style order.

This is the CFC lift of the scalar inequality `x + 1 <= exp x`, converted from
Mathlib's matrix order to `MatrixLE`. -/
theorem matrixLE_one_add_self_le_matrixExp_of_selfAdjoint {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    MatrixLE ((1 : Matrix (Fin n) (Fin n) Real) + A) (matrixExp A) := by
  unfold MatrixLE
  have hle :
      (1 : Matrix (Fin n) (Fin n) Real) + A <= matrixExp A := by
    have hmono :
        cfc (fun x : Real => x + 1) A <= cfc Real.exp A := by
      exact cfc_mono (a := A)
        (f := fun x : Real => x + 1)
        (g := Real.exp)
        (by
          intro x _hx
          exact Real.add_one_le_exp x)
    have hlin :
        cfc (fun x : Real => x + 1) A =
          A + (1 : Matrix (Fin n) (Fin n) Real) := by
      calc
        cfc (fun x : Real => x + 1) A =
            cfc (fun x : Real => id x + (1 : Real)) A := rfl
        _ = cfc id A + cfc (1 : Real -> Real) A := by
            exact cfc_add A id (1 : Real -> Real)
        _ = A + (1 : Matrix (Fin n) (Fin n) Real) := by
            rw [cfc_id Real A hA.isSelfAdjoint, cfc_one Real A hA.isSelfAdjoint]
    have hexp : cfc Real.exp A = matrixExp A := by
      simpa [matrixExp] using
        (CFC.real_exp_eq_normedSpace_exp (a := A) hA.isSelfAdjoint)
    calc
      (1 : Matrix (Fin n) (Fin n) Real) + A =
          A + (1 : Matrix (Fin n) (Fin n) Real) := by
            rw [add_comm]
      _ = cfc (fun x : Real => x + 1) A := hlin.symm
      _ <= cfc Real.exp A := hmono
      _ = matrixExp A := hexp
  have hPSD :
      (matrixExp A - ((1 : Matrix (Fin n) (Fin n) Real) + A)).PosSemidef :=
    Matrix.le_iff.mp hle
  constructor
  · apply Matrix.IsSymm.ext
    intro i j
    have h := Matrix.IsHermitian.apply hPSD.isHermitian i j
    simpa using h
  · intro x
    exact matrixQuadraticForm_nonneg_of_posSemidef hPSD x

/-- Scalar-multiple wrapper for the matrix exponential affine lower bound. -/
theorem matrixLE_one_add_smul_le_matrixExp_smul_of_selfAdjoint {n : Nat}
    {V : Matrix (Fin n) (Fin n) Real} (c : Real)
    (hV : IsSelfAdjointMatrix V) :
    MatrixLE ((1 : Matrix (Fin n) (Fin n) Real) + SMul.smul c V)
      (matrixExp (SMul.smul c V)) := by
  exact matrixLE_one_add_self_le_matrixExp_of_selfAdjoint
    (isSelfAdjointMatrix_smul c hV)

end MatrixExpPosSemidef

/-- Square-factor proof of PSD for the matrix exponential of a real
self-adjoint matrix.

This factors `exp A` as `exp (A/2) * exp (A/2)`, rewrites the first factor as
the conjugate transpose of the second using Hermitian preservation, and then
applies Mathlib's PSD theorem for `Bᴴ * B`. -/
private theorem matrixExp_posSemidef_of_selfAdjoint_square {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    Matrix.PosSemidef (matrixExp A) := by
  let H : Matrix (Fin n) (Fin n) Real :=
    SMul.smul (((1 : Real) / (2 : Real))) A
  let E : Matrix (Fin n) (Fin n) Real := matrixExp H
  have hH : IsSelfAdjointMatrix H := by
    have hHalf : IsSelfAdjoint (((1 : Real) / (2 : Real))) := by
      simp [IsSelfAdjoint]
    change (SMul.smul (((1 : Real) / (2 : Real))) A).IsHermitian
    exact hA.smul hHalf
  have hE : IsSelfAdjointMatrix E := by
    simpa [E] using isSelfAdjointMatrix_matrixExp hH
  have hPSD : Matrix.PosSemidef (E * E) := by
    have hSquare : Matrix.PosSemidef (star E * E) := by
      change Matrix.PosSemidef (E.transpose * E)
      exact Matrix.posSemidef_conjTranspose_mul_self E
    have hStarE : star E = E := hE.eq
    simpa [hStarE] using hSquare
  have hsplit : A = H + H := by
    ext i j
    change A i j =
      (((1 : Real) / (2 : Real)) * A i j) +
        (((1 : Real) / (2 : Real)) * A i j)
    ring
  have hExpSplit : matrixExp A = E * E := by
    rw [matrixExp, hsplit]
    simpa [E, matrixExp] using Matrix.exp_add_of_commute H H (Commute.refl H)
  rw [hExpSplit]
  exact hPSD

/-- Trace-exponential moment of a random square matrix at scalar parameter
`theta`.

This is the scalar integrand shared by the raw expectation and lintegral
versions below. -/
def traceExpIntegrand {Omega : Type*} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta : Real) : RealRandomVariable Omega :=
  fun omega => traceMatrixExp (SMul.smul theta (Y omega))

/-- Trace-exponential moment of a random square matrix at scalar parameter
`theta`.

This is a raw expectation wrapper. Integrability and finiteness hypotheses
belong in theorem statements using it. -/
def traceExpMoment {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (Y : RandomMatrix Omega n n) (theta : Real) : Real :=
  expect P (traceExpIntegrand Y theta)

/-- LIntegral version of the trace-exponential moment.

This is the nonnegative-integral object needed by Markov/Laplace arguments.
The bridge to the raw real expectation is kept as a statement target below
because it requires nonnegativity and integrability of the trace-exponential
random variable. -/
def traceExpMomentLIntegral {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (Y : RandomMatrix Omega n n) (theta : Real) : ENNReal :=
  ∫⁻ omega, ENNReal.ofReal (traceExpIntegrand Y theta omega) ∂P

/-! ## Semantic trace-mgf bounds -/

/-- Semantic real trace-mgf upper bound.

`TraceMGFBound P Y theta rhs` means the raw trace-exponential moment of `Y`
at `theta` is bounded by the deterministic real value `rhs`. Integrability and
provider assumptions are deliberately external. -/
def TraceMGFBound {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (Y : RandomMatrix Omega n n) (theta rhs : Real) : Prop :=
  traceExpMoment P Y theta <= rhs

/-- Semantic lintegral trace-mgf upper bound.

This is the nonnegative-integral counterpart of `TraceMGFBound`, used by the
already proved lintegral Laplace wrappers. -/
def TraceMGFBoundLIntegral {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (P : Measure Omega) (Y : RandomMatrix Omega n n) (theta : Real)
    (rhs : ENNReal) : Prop :=
  traceExpMomentLIntegral P Y theta <= rhs

/-- Semantic trace-mgf bound supplied by a deterministic variance-proxy matrix.

This records the usual future matrix-mgf target without proving the
Golden-Thompson/Lieb or independence machinery needed to establish it. -/
def TraceMGFVarianceProxyBound {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (Y : RandomMatrix Omega n n)
    (V : Matrix (Fin n) (Fin n) Real) (theta : Real) : Prop :=
  TraceMGFBound P Y theta (traceMatrixExp ((theta ^ 2 / 2) • V))

/-- LIntegral-form trace-mgf bound supplied by a deterministic variance-proxy
matrix. -/
def TraceMGFVarianceProxyBoundLIntegral {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (Y : RandomMatrix Omega n n)
    (V : Matrix (Fin n) (Fin n) Real) (theta : Real) : Prop :=
  TraceMGFBoundLIntegral P Y theta
    (ENNReal.ofReal (traceMatrixExp ((theta ^ 2 / 2) • V)))

/-! ## Typed Tropp/Lieb trace-mgf primitive -/

section TroppMasterTraceMGFStep

open scoped BigOperators MatrixOrder Matrix.Norms.Operator Matrix.Norms.L2Operator

/-- Typed Tropp master trace-mgf step.

This is the source-backed primitive
`E tr exp(H + Z) <= tr exp(H + log E exp Z)` from the Lieb/Tropp matrix-mgf
route. It is only a `Prop`-valued typed statement: the hard Lieb concavity and
Jensen/conditional-expectation proof is not supplied here.

All currently visible infrastructure assumptions are explicit. The matrix
exponential moment uses HighDimProb's entrywise `matrixExpect`, and the
self-adjointness and strict positivity needed to form the matrix logarithm are
assumptions rather than hidden providers. -/
abbrev troppMasterTraceMGFStepStatement {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (H : Matrix (Fin n) (Fin n) Real)
    (Z : RandomMatrix Omega n n) : Prop :=
  IsSelfAdjointMatrix H ->
    RandomSelfAdjointMatrix P Z ->
      IntegrableRealRandomVariable P
        (fun omega => traceMatrixExp (H + Z omega)) ->
        IntegrableRandomMatrix P (fun omega => matrixExp (Z omega)) ->
          IsSelfAdjointMatrix
            (matrixExpect P (fun omega => matrixExp (Z omega))) ->
            IsStrictlyPositive
              (matrixExpect P (fun omega => matrixExp (Z omega))) ->
              expect P (fun omega => traceMatrixExp (H + Z omega)) <=
                traceMatrixExp
                  (H + CFC.log
                    (matrixExpect P (fun omega => matrixExp (Z omega))))

/-- Typed log/order-to-`K` bridge for the Tropp one-step RHS.

This is the deterministic bridge needed after a one-summand matrix-MGF
comparison has produced `M <= exp K`. It records the combined analytic
consequence that the logarithmic RHS from the Tropp step can be replaced by the
deterministic comparison matrix `K` inside the trace exponential.

The statement is intentionally a typed primitive. It does not prove operator
monotonicity of matrix logarithm or monotonicity of the trace exponential. -/
abbrev troppLogExpComparisonToKStatement {n : Nat}
    (H M K : Matrix (Fin n) (Fin n) Real) : Prop :=
  IsSelfAdjointMatrix H ->
    IsSelfAdjointMatrix M ->
      IsStrictlyPositive M ->
        IsSelfAdjointMatrix K ->
          MatrixLE M (matrixExp K) ->
            traceMatrixExp (H + CFC.log M) <= traceMatrixExp (H + K)

/-- Apply the typed log/order-to-`K` bridge to the Tropp one-step statement. -/
theorem troppMasterTraceMGFStep_trace_bound_of_logExpComparisonToK
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (H K : Matrix (Fin n) (Fin n) Real)
    (Z : RandomMatrix Omega n n)
    (hStep : troppMasterTraceMGFStepStatement (P := P) H Z)
    (hBridge :
      troppLogExpComparisonToKStatement H
        (matrixExpect P (fun omega => matrixExp (Z omega))) K)
    (hH : IsSelfAdjointMatrix H)
    (hZ : RandomSelfAdjointMatrix P Z)
    (hTraceInt :
      IntegrableRealRandomVariable P
        (fun omega => traceMatrixExp (H + Z omega)))
    (hExpInt : IntegrableRandomMatrix P (fun omega => matrixExp (Z omega)))
    (hExpMeanSA :
      IsSelfAdjointMatrix
        (matrixExpect P (fun omega => matrixExp (Z omega))))
    (hExpMeanPos :
      IsStrictlyPositive
        (matrixExpect P (fun omega => matrixExp (Z omega))))
    (hKSA : IsSelfAdjointMatrix K)
    (hMGF :
      MatrixLE
        (matrixExpect P (fun omega => matrixExp (Z omega)))
        (matrixExp K)) :
    expect P (fun omega => traceMatrixExp (H + Z omega)) <=
      traceMatrixExp (H + K) :=
  (hStep hH hZ hTraceInt hExpInt hExpMeanSA hExpMeanPos).trans
    (hBridge hH hExpMeanSA hExpMeanPos hKSA hMGF)

/-- Typed conditional/history one-step primitive for the Tropp trace-MGF
iteration.

This is intentionally weaker than the finite-family theorem: it handles one
random history matrix `H`, one increment `Z`, and one deterministic comparison
matrix `K`. The conclusion is a conditional trace-exponential bound relative
to a history sigma-algebra, so later finite-family work can iterate it without
using the deterministic-`H` one-step primitive for a random history. -/
abbrev troppMasterTraceMGFConditionalStepStatement {Omega : Type*}
    [mOmega : MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (mHist : MeasurableSpace Omega)
    (H Z : RandomMatrix Omega n n)
    (K : Matrix (Fin n) (Fin n) Real) : Prop :=
  mHist ≤ mOmega ->
    @IsRandomMatrix Omega mOmega n n P H ->
      @IsRandomMatrix Omega mOmega n n P Z ->
        (forall i j,
          @Measurable Omega Real mHist inferInstance
            (fun omega => H omega i j)) ->
          (forall omega, IsSelfAdjointMatrix (H omega)) ->
            @RandomSelfAdjointMatrix Omega mOmega n P Z ->
              @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _ H Z P ->
                @IntegrableRealRandomVariable Omega mOmega P
                  (fun omega => traceMatrixExp (H omega + Z omega)) ->
                  @IntegrableRandomMatrix Omega mOmega n n P
                    (fun omega => matrixExp (Z omega)) ->
                    IsSelfAdjointMatrix
                      (@matrixExpect Omega mOmega n n P
                        (fun omega => matrixExp (Z omega))) ->
                      IsStrictlyPositive
                        (@matrixExpect Omega mOmega n n P
                          (fun omega => matrixExp (Z omega))) ->
                        IsSelfAdjointMatrix K ->
                          MatrixLE
                            (@matrixExpect Omega mOmega n n P
                              (fun omega => matrixExp (Z omega)))
                            (matrixExp K) ->
                            ∀ᵐ omega ∂P,
                              MeasureTheory.condExp (m := mHist) P
                                (fun omega' =>
                                  traceMatrixExp (H omega' + Z omega')) omega <=
                                traceMatrixExp (H omega + K)

/-- Apply the conditional-step primitive using history-entry measurability to
derive the ambient random-matrix measurability of the history matrix. -/
theorem troppMasterTraceMGFConditionalStep_apply_of_histEntryMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {n : Nat} (mHist : MeasurableSpace Omega)
    (H Z : RandomMatrix Omega n n)
    (K : Matrix (Fin n) (Fin n) Real)
    (hCond :
      @troppMasterTraceMGFConditionalStepStatement
        Omega mOmega P n mHist H Z K)
    (hHistSub : mHist ≤ mOmega)
    (hZRand : @IsRandomMatrix Omega mOmega n n P Z)
    (hHistMeas :
      forall i j,
        @Measurable Omega Real mHist inferInstance
          (fun omega => H omega i j))
    (hHistSA : forall omega, IsSelfAdjointMatrix (H omega))
    (hZSA : @RandomSelfAdjointMatrix Omega mOmega n P Z)
    (hIndep :
      @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _ H Z P)
    (hCondTraceInt :
      @IntegrableRealRandomVariable Omega mOmega P
        (fun omega => traceMatrixExp (H omega + Z omega)))
    (hExpInt :
      @IntegrableRandomMatrix Omega mOmega n n P
        (fun omega => matrixExp (Z omega)))
    (hExpMeanSA :
      IsSelfAdjointMatrix
        (@matrixExpect Omega mOmega n n P
          (fun omega => matrixExp (Z omega))))
    (hExpMeanPos :
      IsStrictlyPositive
        (@matrixExpect Omega mOmega n n P
          (fun omega => matrixExp (Z omega))))
    (hKSA : IsSelfAdjointMatrix K)
    (hMGFToK :
      MatrixLE
        (@matrixExpect Omega mOmega n n P
          (fun omega => matrixExp (Z omega)))
        (matrixExp K)) :
    Filter.EventuallyLE (MeasureTheory.ae P)
      (fun omega =>
        MeasureTheory.condExp (m := mHist) P
          (fun omega' => traceMatrixExp (H omega' + Z omega')) omega)
      (fun omega => traceMatrixExp (H omega + K)) := by
  exact hCond hHistSub
    (@isRandomMatrix_of_sub_measurable_entries Omega mOmega P n n H
      mHist hHistSub hHistMeas)
    hZRand hHistMeas hHistSA hZSA hIndep hCondTraceInt hExpInt
    hExpMeanSA hExpMeanPos hKSA hMGFToK

/-- Integrate one typed conditional/history Tropp step.

This theorem only turns the conditional one-step primitive into an
unconditional expected trace-exponential comparison. It keeps the
sigma-finiteness and right-hand integrability assumptions explicit. -/
theorem troppMasterTraceMGFConditionalStep_expect_bound {Omega : Type*}
    [mOmega : MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (mHist : MeasurableSpace Omega)
    (H Z : RandomMatrix Omega n n)
    (K : Matrix (Fin n) (Fin n) Real)
    (hCond :
      @troppMasterTraceMGFConditionalStepStatement
        Omega mOmega P n mHist H Z K)
    (hHistSub : mHist ≤ mOmega)
    (hHistRand : @IsRandomMatrix Omega mOmega n n P H)
    (hZRand : @IsRandomMatrix Omega mOmega n n P Z)
    (hHistMeas :
      forall i j,
        @Measurable Omega Real mHist inferInstance
          (fun omega => H omega i j))
    (hHistSA : forall omega, IsSelfAdjointMatrix (H omega))
    (hZSA : @RandomSelfAdjointMatrix Omega mOmega n P Z)
    (hIndep :
      @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _ H Z P)
    (hCondTraceInt :
      @IntegrableRealRandomVariable Omega mOmega P
        (fun omega => traceMatrixExp (H omega + Z omega)))
    (hExpInt :
      @IntegrableRandomMatrix Omega mOmega n n P
        (fun omega => matrixExp (Z omega)))
    (hExpMeanSA :
      IsSelfAdjointMatrix
        (@matrixExpect Omega mOmega n n P
          (fun omega => matrixExp (Z omega))))
    (hExpMeanPos :
      IsStrictlyPositive
        (@matrixExpect Omega mOmega n n P
          (fun omega => matrixExp (Z omega))))
    (hKSA : IsSelfAdjointMatrix K)
    (hMGFToK :
      MatrixLE
        (@matrixExpect Omega mOmega n n P
          (fun omega => matrixExp (Z omega)))
        (matrixExp K))
    (hSigma : SigmaFinite (P.trim hHistSub))
    (hRhsInt :
      @IntegrableRealRandomVariable Omega mOmega P
        (fun omega => traceMatrixExp (H omega + K))) :
    @expect Omega mOmega P
        (fun omega => traceMatrixExp (H omega + Z omega)) <=
      @expect Omega mOmega P
        (fun omega => traceMatrixExp (H omega + K)) := by
  letI := hSigma
  have hCondAE :
      (fun omega =>
        MeasureTheory.condExp (m := mHist) P
          (fun omega' => traceMatrixExp (H omega' + Z omega')) omega) ≤ᵐ[P]
        (fun omega => traceMatrixExp (H omega + K)) :=
    hCond hHistSub hHistRand hZRand hHistMeas hHistSA hZSA hIndep
      hCondTraceInt hExpInt hExpMeanSA hExpMeanPos hKSA hMGFToK
  have hCondInt :
      Integrable
        (MeasureTheory.condExp (m := mHist) P
          (fun omega => traceMatrixExp (H omega + Z omega))) P :=
    MeasureTheory.integrable_condExp (μ := P) (m := mHist)
      (f := fun omega => traceMatrixExp (H omega + Z omega))
  have hIntegralCond :
      (∫ omega,
        MeasureTheory.condExp (m := mHist) P
          (fun omega' => traceMatrixExp (H omega' + Z omega')) omega ∂P) =
        ∫ omega, traceMatrixExp (H omega + Z omega) ∂P :=
    MeasureTheory.integral_condExp (μ := P) (m := mHist)
      (f := fun omega => traceMatrixExp (H omega + Z omega)) hHistSub
  calc
    @expect Omega mOmega P
        (fun omega => traceMatrixExp (H omega + Z omega))
        = ∫ omega, traceMatrixExp (H omega + Z omega) ∂P := rfl
    _ = ∫ omega,
          MeasureTheory.condExp (m := mHist) P
            (fun omega' => traceMatrixExp (H omega' + Z omega')) omega ∂P :=
          hIntegralCond.symm
    _ <= ∫ omega, traceMatrixExp (H omega + K) ∂P :=
          integral_mono_ae hCondInt hRhsInt hCondAE
    _ = @expect Omega mOmega P
          (fun omega => traceMatrixExp (H omega + K)) := rfl

private theorem fin_expect_chain_le {m : Nat} (a : Fin (m + 1) -> Real)
    (hStep : forall i : Fin m, a i.castSucc <= a i.succ) :
    a ⟨0, Nat.succ_pos m⟩ <= a ⟨m, Nat.lt_succ_self m⟩ := by
  have hPrefix :
      forall k, (hk : k <= m) ->
        a ⟨0, Nat.succ_pos m⟩ <= a ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
        intro _hk
        rfl
    | succ k ih =>
        intro hk
        have hkLe : k <= m := Nat.le_trans (Nat.le_succ k) hk
        have hkLt : k < m := hk
        exact (ih hkLe).trans (by
          have h := hStep ⟨k, hkLt⟩
          simpa [Fin.castSucc, Fin.succ] using h)
  exact hPrefix m le_rfl

/-- Finite induction skeleton from conditional/history Tropp steps.

The theorem proves only the finite chain once every adjacent state has already
been identified with a one-step conditional/history Tropp comparison. It does
not derive the history sigma-algebras from `iIndepFun`, does not prove the
state-identification algebra, and does not prove the full finite-family Tropp
primitive. -/
theorem troppTraceExpFiniteFamilyIterationSkeleton_of_conditionalSteps
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (state : Fin (m + 1) -> RealRandomVariable Omega)
    (mHist : Fin m -> MeasurableSpace Omega)
    (H Z : Fin m -> RandomMatrix Omega n n)
    (hCond :
      forall i,
        troppMasterTraceMGFConditionalStepStatement (P := P)
          (mHist i) (H i) (Z i) (K i))
    (hHistSub : forall i, mHist i ≤ mOmega)
    (hHistRand : forall i, @IsRandomMatrix Omega mOmega n n P (H i))
    (hZRand : forall i, @IsRandomMatrix Omega mOmega n n P (Z i))
    (hHistMeas :
      forall i r c,
        @Measurable Omega Real (mHist i) inferInstance
          (fun omega => H i omega r c))
    (hHistSA : forall i omega, IsSelfAdjointMatrix (H i omega))
    (hZSA : forall i, @RandomSelfAdjointMatrix Omega mOmega n P (Z i))
    (hIndep :
      forall i,
        @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _ (H i) (Z i) P)
    (hCondTraceInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega => traceMatrixExp (H i omega + Z i omega)))
    (hExpInt :
      forall i,
        @IntegrableRandomMatrix Omega mOmega n n P
          (fun omega => matrixExp (Z i omega)))
    (hExpMeanSA :
      forall i,
        IsSelfAdjointMatrix
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (Z i omega))))
    (hExpMeanPos :
      forall i,
        IsStrictlyPositive
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (Z i omega))))
    (hKSA : forall i, IsSelfAdjointMatrix (K i))
    (hMGFToK :
      forall i,
        MatrixLE
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (Z i omega)))
          (matrixExp (K i)))
    (hSigma : forall i, SigmaFinite (P.trim (hHistSub i)))
    (hRhsInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega => traceMatrixExp (H i omega + K i)))
    (hStateZero :
      state ⟨0, Nat.succ_pos m⟩ =
        fun omega => traceMatrixExp (randomMatrixSum X omega))
    (hStateLast :
      state ⟨m, Nat.lt_succ_self m⟩ =
        fun _omega =>
          traceMatrixExp (Finset.univ.sum fun i : Fin m => K i))
    (hStateLeft :
      forall i,
        state i.castSucc =
          fun omega => traceMatrixExp (H i omega + Z i omega))
    (hStateRight :
      forall i,
        state i.succ =
          fun omega => traceMatrixExp (H i omega + K i)) :
    expect P (fun omega => traceMatrixExp (randomMatrixSum X omega)) <=
      traceMatrixExp (Finset.univ.sum fun i : Fin m => K i) := by
  have hStep :
      forall i : Fin m, expect P (state i.castSucc) <= expect P (state i.succ) := by
    intro i
    have h :=
      troppMasterTraceMGFConditionalStep_expect_bound
        (P := P) (mHist i) (H i) (Z i) (K i) (hCond i)
        (hHistSub i) (hHistRand i) (hZRand i) (hHistMeas i)
        (hHistSA i) (hZSA i) (hIndep i) (hCondTraceInt i)
        (hExpInt i) (hExpMeanSA i) (hExpMeanPos i) (hKSA i)
        (hMGFToK i) (hSigma i) (hRhsInt i)
    simpa [hStateLeft i, hStateRight i] using h
  have hChain :=
    fin_expect_chain_le (m := m) (fun i => expect P (state i)) hStep
  calc
    expect P (fun omega => traceMatrixExp (randomMatrixSum X omega))
        = expect P (state ⟨0, Nat.succ_pos m⟩) := by
          rw [hStateZero]
    _ <= expect P (state ⟨m, Nat.lt_succ_self m⟩) := hChain
    _ = traceMatrixExp (Finset.univ.sum fun i : Fin m => K i) := by
          rw [hStateLast]
          simp [expect, measureReal_def]

/-- Trace-exponential endpoint for a state written with the final random prefix.

This is a bookkeeping wrapper over `randomMatrixPrefixSum_last`, matching the
function-equality shape used by Tropp finite-state endpoint hypotheses. -/
theorem traceMatrixExp_randomMatrixPrefixSum_last {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat}
    (A : Fin m -> RandomMatrix Omega n n) :
    (fun omega => traceMatrixExp (randomMatrixPrefixSum A (Fin.last m) omega)) =
      fun omega => traceMatrixExp (randomMatrixSum A omega) := by
  rw [randomMatrixPrefixSum_last A]

/-- Trace-exponential endpoint for a constant state written with the final
comparison-matrix prefix.

This is a bookkeeping wrapper over `comparisonMatrixPrefixSum_last`, matching
the constant-function shape used by Tropp finite-state endpoint hypotheses. -/
theorem traceMatrixExp_comparisonMatrixPrefixSum_last {Omega : Type*}
    {m n : Nat} (K : Fin m -> Matrix (Fin n) (Fin n) Real) :
    (fun _omega : Omega =>
      traceMatrixExp (comparisonMatrixPrefixSum K (Fin.last m))) =
      fun _omega : Omega =>
        traceMatrixExp (Finset.univ.sum fun i : Fin m => K i) := by
  rw [comparisonMatrixPrefixSum_last K]

/-- Natural random-history suffix for the `Fin m` conditional Tropp route.

At step `i`, this is the scaled random suffix after the current summand. -/
def troppRandomHistory {Omega : Type*}
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n) (i : Fin m) :
    RandomMatrix Omega n n :=
  randomMatrixSuffixSum (scaledRandomMatrixFamily theta X) i.succ

/-- Natural deterministic comparison-history prefix before step `i`. -/
def troppComparisonHistory {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    Matrix (Fin n) (Fin n) Real :=
  comparisonMatrixPrefixSum K i.castSucc

/-- Natural current scaled random step for the `Fin m` Tropp route. -/
def troppCurrentRandomStep {Omega : Type*}
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n) (i : Fin m) :
    RandomMatrix Omega n n :=
  scaledRandomMatrixFamily theta X i

/-- Natural current deterministic comparison step for the `Fin m` Tropp route. -/
abbrev troppCurrentComparisonStep {m n : Nat}
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    Matrix (Fin n) (Fin n) Real :=
  K i

/-- Natural matrix history at step `i`: comparison prefix plus random suffix. -/
def troppStateHistory {Omega : Type*}
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    RandomMatrix Omega n n :=
  fun omega => troppComparisonHistory K i + troppRandomHistory theta X i omega

/-- Natural trace-exponential state for the `Fin m` Tropp route. -/
def troppTraceState {Omega : Type*}
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (k : Fin (m + 1)) : RealRandomVariable Omega :=
  fun omega =>
    traceMatrixExp
      (comparisonMatrixPrefixSum K k +
        randomMatrixSuffixSum (scaledRandomMatrixFamily theta X) k omega)

/-- Natural left state before replacing the current random step. -/
def troppStateLeft {Omega : Type*}
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    RealRandomVariable Omega :=
  troppTraceState theta X K i.castSucc

/-- Natural right state after replacing the current random step by `K i`. -/
def troppStateRight {Omega : Type*}
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    RealRandomVariable Omega :=
  troppTraceState theta X K i.succ

/-- Zero endpoint for the natural Tropp trace state. -/
theorem troppNaturalState_zero {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) :
    troppTraceState theta X K 0 =
      fun omega =>
        traceMatrixExp
          (randomMatrixSum (scaledRandomMatrixFamily theta X) omega) := by
  funext omega
  simp [troppTraceState]

/-- Last endpoint for the natural Tropp trace state. -/
theorem troppNaturalState_last {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) :
    troppTraceState theta X K (Fin.last m) =
      fun _omega : Omega =>
        traceMatrixExp (Finset.univ.sum fun i : Fin m => K i) := by
  funext omega
  simp [troppTraceState]

/-- Left adjacent-state identity for the natural Tropp trace state. -/
theorem troppNaturalState_left {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    troppStateLeft theta X K i =
      fun omega =>
        traceMatrixExp
          (troppStateHistory theta X K i omega +
            troppCurrentRandomStep theta X i omega) := by
  funext omega
  simp only [troppStateLeft, troppTraceState, troppStateHistory,
    troppComparisonHistory, troppRandomHistory, troppCurrentRandomStep,
    randomMatrixSuffixSum_apply]
  rw [comparisonMatrixSuffixSum_succ]
  ac_rfl

/-- Right adjacent-state identity for the natural Tropp trace state. -/
theorem troppNaturalState_right {Omega : Type*} [MeasurableSpace Omega]
    {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    troppStateRight theta X K i =
      fun omega =>
        traceMatrixExp
          (troppStateHistory theta X K i omega +
            troppCurrentComparisonStep K i) := by
  funext omega
  simp only [troppStateRight, troppTraceState, troppStateHistory,
    troppComparisonHistory, troppRandomHistory, troppCurrentComparisonStep,
    randomMatrixSuffixSum_apply]
  rw [comparisonMatrixPrefixSum_succ]
  ac_rfl

/-- Conditional-step finite iteration with the canonical natural trace state.

Compared with `troppTraceExpFiniteFamilyIterationSkeleton_of_conditionalSteps`,
this wrapper fixes `state`, `H`, and `Z` to the Fin-prefix/suffix natural
construction and discharges the four raw endpoint assumptions by bookkeeping.
The analytic, measurability, independence, and integrability hypotheses remain
explicit. -/
theorem troppTraceExpFiniteFamilyIterationSkeleton_of_naturalStateConditionalSteps
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (theta : Real)
    (mHist : Fin m -> MeasurableSpace Omega)
    (hCond :
      forall i,
        @troppMasterTraceMGFConditionalStepStatement Omega mOmega P n
          (mHist i) (@troppStateHistory Omega m n theta X K i)
          (@troppCurrentRandomStep Omega m n theta X i) (K i))
    (hHistSub : forall i, mHist i ≤ mOmega)
    (hHistRand :
      forall i,
        @IsRandomMatrix Omega mOmega n n P
          (troppStateHistory theta X K i))
    (hZRand :
      forall i,
        @IsRandomMatrix Omega mOmega n n P
          (troppCurrentRandomStep theta X i))
    (hHistMeas :
      forall i r c,
        @Measurable Omega Real (mHist i) inferInstance
          (fun omega => troppStateHistory theta X K i omega r c))
    (hHistSA :
      forall i omega, IsSelfAdjointMatrix (troppStateHistory theta X K i omega))
    (hZSA :
      forall i,
        @RandomSelfAdjointMatrix Omega mOmega n P
          (troppCurrentRandomStep theta X i))
    (hIndep :
      forall i,
        @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _
          (troppStateHistory theta X K i)
          (troppCurrentRandomStep theta X i) P)
    (hCondTraceInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega =>
            traceMatrixExp
              (troppStateHistory theta X K i omega +
                troppCurrentRandomStep theta X i omega)))
    (hExpInt :
      forall i,
        @IntegrableRandomMatrix Omega mOmega n n P
          (fun omega => matrixExp (troppCurrentRandomStep theta X i omega)))
    (hExpMeanSA :
      forall i,
        IsSelfAdjointMatrix
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (troppCurrentRandomStep theta X i omega))))
    (hExpMeanPos :
      forall i,
        IsStrictlyPositive
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (troppCurrentRandomStep theta X i omega))))
    (hKSA : forall i, IsSelfAdjointMatrix (K i))
    (hMGFToK :
      forall i,
        MatrixLE
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (troppCurrentRandomStep theta X i omega)))
          (matrixExp (K i)))
    (hSigma : forall i, SigmaFinite (P.trim (hHistSub i)))
    (hRhsInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega =>
            traceMatrixExp (troppStateHistory theta X K i omega + K i))) :
    expect P
        (fun omega =>
          traceMatrixExp
            (randomMatrixSum (scaledRandomMatrixFamily theta X) omega)) <=
      traceMatrixExp (Finset.univ.sum fun i : Fin m => K i) :=
  troppTraceExpFiniteFamilyIterationSkeleton_of_conditionalSteps
    (P := P)
    (scaledRandomMatrixFamily theta X) K
    (troppTraceState theta X K) mHist
    (troppStateHistory theta X K) (troppCurrentRandomStep theta X)
    hCond hHistSub hHistRand hZRand hHistMeas hHistSA hZSA hIndep
    hCondTraceInt hExpInt hExpMeanSA hExpMeanPos hKSA hMGFToK hSigma
    hRhsInt
    (troppNaturalState_zero theta X K)
    (troppNaturalState_last theta X K)
    (troppNaturalState_left theta X K)
    (troppNaturalState_right theta X K)

end TroppMasterTraceMGFStep

/-! ## Typed Bernstein functional-calculus primitive -/

section BernsteinFunctionalCalculus

open scoped MatrixOrder Matrix.Norms.Operator Matrix.Norms.L2Operator

/-- Canonical bounded-Bernstein matrix-MGF coefficient. -/
def bernsteinMGFCoeff (theta R : Real) : Real :=
  (theta ^ 2 / 2) / (1 - abs theta * R / 3)

@[simp]
theorem bernsteinMGFCoeff_neg (theta R : Real) :
    bernsteinMGFCoeff (-theta) R = bernsteinMGFCoeff theta R := by
  simp [bernsteinMGFCoeff]

/-- Canonical scalar Bernstein optimizing choice for the bounded-MGF
coefficient.

For positive variance proxy `sigmaSq`, nonnegative radius `R`, and positive
deviation `t`, this is the usual conservative choice
`theta = t / (sigmaSq + R * t / 3)`. -/
def bernsteinThetaChoice (t sigmaSq R : Real) : Real :=
  t / (sigmaSq + R * t / 3)

/-- Positivity of the Bernstein theta-choice denominator under the standard
nonnegative parameter assumptions. -/
lemma bernsteinThetaChoice_den_pos {t sigmaSq R : Real}
    (hSigma : 0 < sigmaSq) (hR : 0 <= R) (ht : 0 <= t) :
    0 < sigmaSq + R * t / 3 := by
  have hnonneg : 0 <= R * t / 3 := by positivity
  linarith

/-- Nonnegativity of the Bernstein theta choice when its denominator is
positive. -/
lemma bernsteinThetaChoice_nonneg {t sigmaSq R : Real} (ht : 0 <= t)
    (hden : 0 < sigmaSq + R * t / 3) :
    0 <= bernsteinThetaChoice t sigmaSq R := by
  exact div_nonneg ht hden.le

/-- Positivity of the Bernstein theta choice when `t` and its denominator are
positive. -/
lemma bernsteinThetaChoice_pos {t sigmaSq R : Real} (ht : 0 < t)
    (hden : 0 < sigmaSq + R * t / 3) :
    0 < bernsteinThetaChoice t sigmaSq R := by
  exact div_pos ht hden

/-- The Bernstein theta choice lies in the standard bounded-MGF range
`|theta| * R < 3`. -/
lemma bernsteinThetaChoice_range {t sigmaSq R : Real}
    (hSigma : 0 < sigmaSq) (hR : 0 <= R) (ht : 0 <= t) :
    abs (bernsteinThetaChoice t sigmaSq R) * R < 3 := by
  have hdenpos : 0 < sigmaSq + R * t / 3 :=
    bernsteinThetaChoice_den_pos hSigma hR ht
  have htheta_nonneg : 0 <= bernsteinThetaChoice t sigmaSq R :=
    bernsteinThetaChoice_nonneg ht hdenpos
  rw [abs_of_nonneg htheta_nonneg]
  by_cases hRt : R * t = 0
  · have : bernsteinThetaChoice t sigmaSq R * R = 0 := by
      unfold bernsteinThetaChoice
      rw [div_mul_eq_mul_div, mul_comm t R, hRt]
      simp
    rw [this]
    norm_num
  · have hmain : (R * t) / (sigmaSq + R * t / 3) < 3 := by
      rw [div_lt_iff₀ hdenpos]
      nlinarith
    calc
      bernsteinThetaChoice t sigmaSq R * R =
          (R * t) / (sigmaSq + R * t / 3) := by
        unfold bernsteinThetaChoice
        field_simp [hdenpos.ne']
      _ < 3 := hmain

/-- Scalar exponent simplification produced by the Bernstein theta choice. -/
lemma bernsteinThetaChoice_exponent_eq {t sigmaSq R : Real}
    (hSigma : 0 < sigmaSq) (hR : 0 <= R) (ht : 0 <= t) :
    -(bernsteinThetaChoice t sigmaSq R * t) +
        bernsteinMGFCoeff (bernsteinThetaChoice t sigmaSq R) R * sigmaSq =
      -(t ^ 2 / (2 * sigmaSq + (2 / 3) * R * t)) := by
  have hdenpos : 0 < sigmaSq + R * t / 3 :=
    bernsteinThetaChoice_den_pos hSigma hR ht
  have htheta_nonneg : 0 <= bernsteinThetaChoice t sigmaSq R :=
    bernsteinThetaChoice_nonneg ht hdenpos
  have hsig_ne : sigmaSq ≠ 0 := ne_of_gt hSigma
  have hden_ne : sigmaSq + R * t / 3 ≠ 0 := ne_of_gt hdenpos
  have htarget_ne : 2 * sigmaSq + (2 / 3) * R * t ≠ 0 := by
    nlinarith
  rw [bernsteinMGFCoeff, abs_of_nonneg htheta_nonneg]
  unfold bernsteinThetaChoice
  field_simp [hsig_ne, hden_ne, htarget_ne]
  ring

/-- Nonnegativity of the Bernstein quadratic coefficient under the standard
theta-range hypothesis. -/
theorem bernsteinCoefficient_nonneg {theta R : Real}
    (hRange : abs theta * R < 3) :
    0 <= (theta ^ 2 / 2) / (1 - abs theta * R / 3) := by
  have hNum : 0 <= theta ^ 2 / 2 := by
    exact div_nonneg (sq_nonneg theta) (by norm_num : (0 : Real) <= 2)
  have hDenPos : 0 < 1 - abs theta * R / 3 := by
    nlinarith [hRange]
  exact div_nonneg hNum (le_of_lt hDenPos)

/-- Named-coefficient wrapper for `bernsteinCoefficient_nonneg`. -/
theorem bernsteinMGFCoeff_nonneg {theta R : Real}
    (hRange : abs theta * R < 3) :
    0 <= bernsteinMGFCoeff theta R := by
  simpa [bernsteinMGFCoeff] using bernsteinCoefficient_nonneg hRange

/-- Semantic trace-mgf bound using the bounded-Bernstein coefficient.

This is the RHS normal form produced by the bounded single-summand Bernstein
MGF route. The older `TraceMGFVarianceProxyBound` remains available for the
subGaussian-style coefficient `theta ^ 2 / 2`. -/
def TraceMGFBernsteinVarianceProxyBound {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta R : Real) : Prop :=
  TraceMGFBound P Y theta
    (traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V))

/-- LIntegral-form trace-mgf bound using the bounded-Bernstein coefficient. -/
def TraceMGFBernsteinVarianceProxyBoundLIntegral {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta R : Real) : Prop :=
  TraceMGFBoundLIntegral P Y theta
    (ENNReal.ofReal
      (traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V)))

/-- Typed finite-family Tropp/Lieb trace-mgf comparison primitive.

This is the iteration-shaped interface needed by the Matrix Bernstein
trace-mgf route after the one-summand matrix-MGF comparison has been proved.
It is only a `Prop`-valued typed statement. It does not prove Lieb concavity,
Golden-Thompson, conditional expectation, independence iteration, or the
trace-mgf provider.

The primitive consumes explicit per-summand matrix-MGF comparisons
`E exp(theta X_i) <= exp(K_i)`, an independence assumption, full-sum
trace-exp integrability, and an explicit RHS normalization from
`sum_i K_i` to the bounded Bernstein coefficient normal form. Its conclusion
is the bounded semantic trace-mgf target for the random finite sum. The older
one-step log-form primitive `troppMasterTraceMGFStepStatement` remains
available for source-level Lieb/Tropp work. -/
abbrev troppMasterTraceMGFFiniteFamilyStatement {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {I : Type*}
    [Fintype I] {n : Nat}
    (X : I -> RandomMatrix Omega n n)
    (K : I -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real)
    (theta R : Real) : Prop :=
  (forall i, IsRandomMatrix P (X i)) ->
    (forall i, RandomSelfAdjointMatrix P (X i)) ->
      ProbabilityTheory.iIndepFun X P ->
        (forall i,
          IntegrableRandomMatrix P
            (fun omega => matrixExp (SMul.smul theta (X i omega)))) ->
          IntegrableRealRandomVariable P
            (traceExpIntegrand (randomMatrixSum X) theta) ->
            (forall i, IsSelfAdjointMatrix (K i)) ->
              IsSelfAdjointMatrix V ->
                0 <= R ->
                  abs theta * R < 3 ->
                    (forall i,
                      MatrixLE
                        (matrixExpect P
                          (fun omega =>
                            matrixExp (SMul.smul theta (X i omega))))
                        (matrixExp (K i))) ->
                      Finset.univ.sum (fun i : I => K i) =
                        SMul.smul (bernsteinMGFCoeff theta R) V ->
                        TraceMGFBernsteinVarianceProxyBound P (randomMatrixSum X)
                          V theta R

/-- Transport the finite-family Tropp primitive from a canonical `Fin` reindex.

This is a bookkeeping bridge only. It uses `Fintype.equivFin` to transfer a
provider for the `Fin (Fintype.card I)` family back to the original arbitrary
finite index type `I`; it does not prove the Tropp/Lieb primitive itself. -/
theorem troppMasterTraceMGFFiniteFamily_statement_of_reindexedFin
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} [Fintype I] {n : Nat}
    (X : I -> RandomMatrix Omega n n)
    (K : I -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement (P := P)
        (fun j : Fin (Fintype.card I) =>
          X ((Fintype.equivFin I).symm j))
        (fun j : Fin (Fintype.card I) =>
          K ((Fintype.equivFin I).symm j))
        V theta R) :
    troppMasterTraceMGFFiniteFamilyStatement (P := P) X K V theta R := by
  classical
  intro hRand hSA hIndep hExpInt hTraceInt hKSA hVSA hR hRange hMGF hNorm
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hSumX :
      randomMatrixSum (fun j : Fin (Fintype.card I) => X (e j)) =
        randomMatrixSum X := by
    funext omega
    unfold randomMatrixSum
    ext r c
    rw [Matrix.sum_apply, Matrix.sum_apply]
    simpa [e] using (e.sum_comp (fun i : I => X i omega r c))
  have hSumK :
      Finset.univ.sum (fun j : Fin (Fintype.card I) => K (e j)) =
        Finset.univ.sum (fun i : I => K i) := by
    simpa [e] using (e.sum_comp K)
  have hRandFin :
      forall j : Fin (Fintype.card I), IsRandomMatrix P (X (e j)) := by
    intro j
    exact hRand (e j)
  have hSAFin :
      forall j : Fin (Fintype.card I), RandomSelfAdjointMatrix P (X (e j)) := by
    intro j
    exact hSA (e j)
  have hIndepFin :
      ProbabilityTheory.iIndepFun
        (fun j : Fin (Fintype.card I) => X (e j)) P := by
    simpa [e] using hIndep.precomp e.injective
  have hExpIntFin :
      forall j : Fin (Fintype.card I),
        IntegrableRandomMatrix P
          (fun omega => matrixExp (SMul.smul theta (X (e j) omega))) := by
    intro j
    exact hExpInt (e j)
  have hTraceIntFin :
      IntegrableRealRandomVariable P
        (traceExpIntegrand
          (randomMatrixSum (fun j : Fin (Fintype.card I) => X (e j)))
          theta) := by
    rw [hSumX]
    exact hTraceInt
  have hKSAFin :
      forall j : Fin (Fintype.card I), IsSelfAdjointMatrix (K (e j)) := by
    intro j
    exact hKSA (e j)
  have hMGFFin :
      forall j : Fin (Fintype.card I),
        MatrixLE
          (matrixExpect P
            (fun omega => matrixExp (SMul.smul theta (X (e j) omega))))
          (matrixExp (K (e j))) := by
    intro j
    exact hMGF (e j)
  have hNormFin :
      Finset.univ.sum (fun j : Fin (Fintype.card I) => K (e j)) =
        SMul.smul (bernsteinMGFCoeff theta R) V := by
    rw [hSumK]
    exact hNorm
  have hFin :=
    hTropp hRandFin hSAFin hIndepFin hExpIntFin hTraceIntFin hKSAFin hVSA hR
      hRange hMGFFin hNormFin
  simpa [e, hSumX] using hFin

private theorem traceMGFBernsteinVarianceProxyBound_of_conditionalSteps_core
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (state : Fin (m + 1) -> RealRandomVariable Omega)
    (mHist : Fin m -> MeasurableSpace Omega)
    (H Z : Fin m -> RandomMatrix Omega n n)
    (hCond :
      forall i,
        troppMasterTraceMGFConditionalStepStatement (P := P)
          (mHist i) (H i) (Z i) (K i))
    (hHistSub : forall i, mHist i ≤ mOmega)
    (hHistRand : forall i, @IsRandomMatrix Omega mOmega n n P (H i))
    (hZRand : forall i, @IsRandomMatrix Omega mOmega n n P (Z i))
    (hHistMeas :
      forall i r c,
        @Measurable Omega Real (mHist i) inferInstance
          (fun omega => H i omega r c))
    (hHistSA : forall i omega, IsSelfAdjointMatrix (H i omega))
    (hZSA : forall i, @RandomSelfAdjointMatrix Omega mOmega n P (Z i))
    (hZScaled : Z = scaledRandomMatrixFamily theta X)
    (hStepIndep :
      forall i,
        @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _ (H i) (Z i) P)
    (hCondTraceInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega => traceMatrixExp (H i omega + Z i omega)))
    (hExpIntStep :
      forall i,
        @IntegrableRandomMatrix Omega mOmega n n P
          (fun omega => matrixExp (Z i omega)))
    (hExpMeanSA :
      forall i,
        IsSelfAdjointMatrix
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (Z i omega))))
    (hExpMeanPos :
      forall i,
        IsStrictlyPositive
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (Z i omega))))
    (hKSA : forall i, IsSelfAdjointMatrix (K i))
    (hSigma : forall i, SigmaFinite (P.trim (hHistSub i)))
    (hRhsInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega => traceMatrixExp (H i omega + K i)))
    (hStateZero :
      state ⟨0, Nat.succ_pos m⟩ =
        fun omega =>
          traceMatrixExp
            (randomMatrixSum
              (scaledRandomMatrixFamily theta X) omega))
    (hStateLast :
      state ⟨m, Nat.lt_succ_self m⟩ =
        fun _omega =>
          traceMatrixExp (Finset.univ.sum fun i : Fin m => K i))
    (hStateLeft :
      forall i,
        state i.castSucc =
          fun omega => traceMatrixExp (H i omega + Z i omega))
    (hStateRight :
      forall i,
        state i.succ =
          fun omega => traceMatrixExp (H i omega + K i))
    (hMGF :
      forall i,
        MatrixLE
          (matrixExpect P
            (fun omega => matrixExp (SMul.smul theta (X i omega))))
          (matrixExp (K i)))
    (hNorm :
      Finset.univ.sum (fun i : Fin m => K i) =
        SMul.smul (bernsteinMGFCoeff theta R) V) :
    TraceMGFBernsteinVarianceProxyBound P (randomMatrixSum X) V theta R := by
  have hSkel :
      expect P
          (fun omega =>
            traceMatrixExp
              (randomMatrixSum
                (scaledRandomMatrixFamily theta X) omega)) <=
        traceMatrixExp (Finset.univ.sum fun i : Fin m => K i) :=
    have hStepMGFToK :
        forall i,
          MatrixLE
            (@matrixExpect Omega mOmega n n P
              (fun omega => matrixExp (Z i omega)))
            (matrixExp (K i)) := by
      intro i
      simpa [hZScaled, scaledRandomMatrixFamily, scaledRandomMatrix] using
        hMGF i
    troppTraceExpFiniteFamilyIterationSkeleton_of_conditionalSteps
      (P := P)
      (scaledRandomMatrixFamily theta X) K
      state mHist H Z hCond hHistSub hHistRand hZRand hHistMeas hHistSA
      hZSA hStepIndep hCondTraceInt hExpIntStep hExpMeanSA hExpMeanPos hKSA
      hStepMGFToK hSigma hRhsInt hStateZero hStateLast hStateLeft hStateRight
  have hScaledIntegrand :
      (fun omega =>
        traceMatrixExp
          (randomMatrixSum
            (scaledRandomMatrixFamily theta X) omega)) =
        traceExpIntegrand (randomMatrixSum X) theta := by
    funext omega
    unfold traceExpIntegrand randomMatrixSum scaledRandomMatrixFamily
      scaledRandomMatrix
    congr 1
    ext r c
    rw [Matrix.sum_apply]
    change
      (Finset.univ.sum fun i : Fin m => (theta • X i omega) r c) =
        (theta • (Finset.univ.sum fun i : Fin m => X i omega)) r c
    rw [Matrix.smul_apply]
    rw [Matrix.sum_apply]
    simp_rw [Matrix.smul_apply]
    simp only [smul_eq_mul]
    change (Finset.univ.sum fun i : Fin m => theta * X i omega r c) =
      theta * (Finset.univ.sum fun i : Fin m => X i omega r c)
    rw [Finset.mul_sum]
  unfold TraceMGFBernsteinVarianceProxyBound TraceMGFBound traceExpMoment
  calc
    expect P (traceExpIntegrand (randomMatrixSum X) theta)
        = expect P
            (fun omega =>
              traceMatrixExp
                (randomMatrixSum
                  (scaledRandomMatrixFamily theta X) omega)) := by
          rw [hScaledIntegrand]
    _ <= traceMatrixExp (Finset.univ.sum fun i : Fin m => K i) := hSkel
    _ = traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V) := by
          rw [hNorm]

/-- Finite-family Tropp provider from explicit conditional-step state data.

This theorem is deliberately narrower than the typed finite-family primitive:
it specializes the existing finite-family interface to `Fin m` and uses the S4
finite-chain skeleton for the named scaled family
`scaledRandomMatrixFamily theta X`. The history
sigma-algebras, adjacent state identifications, conditional step assumptions,
and right-hand integrability hypotheses are still explicit; the theorem does
not derive them from `iIndepFun`. -/
theorem troppMasterTraceMGFFiniteFamily_of_conditionalSteps
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (state : Fin (m + 1) -> RealRandomVariable Omega)
    (mHist : Fin m -> MeasurableSpace Omega)
    (H Z : Fin m -> RandomMatrix Omega n n)
    (hCond :
      forall i,
        troppMasterTraceMGFConditionalStepStatement (P := P)
          (mHist i) (H i) (Z i) (K i))
    (hHistSub : forall i, mHist i ≤ mOmega)
    (hHistRand : forall i, @IsRandomMatrix Omega mOmega n n P (H i))
    (hZRand : forall i, @IsRandomMatrix Omega mOmega n n P (Z i))
    (hHistMeas :
      forall i r c,
        @Measurable Omega Real (mHist i) inferInstance
          (fun omega => H i omega r c))
    (hHistSA : forall i omega, IsSelfAdjointMatrix (H i omega))
    (hZSA : forall i, @RandomSelfAdjointMatrix Omega mOmega n P (Z i))
    (hZScaled : Z = scaledRandomMatrixFamily theta X)
    (hStepIndep :
      forall i,
        @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _ (H i) (Z i) P)
    (hCondTraceInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega => traceMatrixExp (H i omega + Z i omega)))
    (hExpIntStep :
      forall i,
        @IntegrableRandomMatrix Omega mOmega n n P
          (fun omega => matrixExp (Z i omega)))
    (hExpMeanSA :
      forall i,
        IsSelfAdjointMatrix
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (Z i omega))))
    (hExpMeanPos :
      forall i,
        IsStrictlyPositive
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (Z i omega))))
    (hSigma : forall i, SigmaFinite (P.trim (hHistSub i)))
    (hRhsInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega => traceMatrixExp (H i omega + K i)))
    (hStateZero :
      state ⟨0, Nat.succ_pos m⟩ =
        fun omega =>
          traceMatrixExp
            (randomMatrixSum
              (scaledRandomMatrixFamily theta X) omega))
    (hStateLast :
      state ⟨m, Nat.lt_succ_self m⟩ =
        fun _omega =>
          traceMatrixExp (Finset.univ.sum fun i : Fin m => K i))
    (hStateLeft :
      forall i,
        state i.castSucc =
          fun omega => traceMatrixExp (H i omega + Z i omega))
    (hStateRight :
      forall i,
        state i.succ =
          fun omega => traceMatrixExp (H i omega + K i)) :
    troppMasterTraceMGFFiniteFamilyStatement (P := P) X K V theta R := by
  intro _hRand _hSA _hIndep _hExpInt _hTraceInt hKSA _hVSA _hR _hRange hMGF hNorm
  exact traceMGFBernsteinVarianceProxyBound_of_conditionalSteps_core
    X K V theta R state mHist H Z hCond hHistSub hHistRand hZRand hHistMeas
    hHistSA hZSA hZScaled hStepIndep hCondTraceInt hExpIntStep hExpMeanSA
    hExpMeanPos hKSA hSigma hRhsInt hStateZero hStateLast hStateLeft
    hStateRight hMGF hNorm

/-- Finite-family Tropp provider from natural-state conditional-step data.

This is the natural-state version of
`troppMasterTraceMGFFiniteFamily_of_conditionalSteps`: it fixes the state,
history matrix, and current random step to the canonical Fin-prefix/suffix
construction and discharges the raw endpoint equalities. The conditional-step
analytic hypotheses remain explicit. -/
theorem troppMasterTraceMGFFiniteFamily_of_naturalStateConditionalSteps
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (mHist : Fin m -> MeasurableSpace Omega)
    (hCond :
      forall i,
        @troppMasterTraceMGFConditionalStepStatement Omega mOmega P n
          (mHist i) (@troppStateHistory Omega m n theta X K i)
          (@troppCurrentRandomStep Omega m n theta X i) (K i))
    (hHistSub : forall i, mHist i ≤ mOmega)
    (hHistRand :
      forall i,
        @IsRandomMatrix Omega mOmega n n P
          (troppStateHistory theta X K i))
    (hZRand :
      forall i,
        @IsRandomMatrix Omega mOmega n n P
          (troppCurrentRandomStep theta X i))
    (hHistMeas :
      forall i r c,
        @Measurable Omega Real (mHist i) inferInstance
          (fun omega => troppStateHistory theta X K i omega r c))
    (hHistSA :
      forall i omega, IsSelfAdjointMatrix (troppStateHistory theta X K i omega))
    (hZSA :
      forall i,
        @RandomSelfAdjointMatrix Omega mOmega n P
          (troppCurrentRandomStep theta X i))
    (hStepIndep :
      forall i,
        @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _
          (troppStateHistory theta X K i)
          (troppCurrentRandomStep theta X i) P)
    (hCondTraceInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega =>
            traceMatrixExp
              (troppStateHistory theta X K i omega +
                troppCurrentRandomStep theta X i omega)))
    (hExpIntStep :
      forall i,
        @IntegrableRandomMatrix Omega mOmega n n P
          (fun omega => matrixExp (troppCurrentRandomStep theta X i omega)))
    (hExpMeanSA :
      forall i,
        IsSelfAdjointMatrix
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (troppCurrentRandomStep theta X i omega))))
    (hExpMeanPos :
      forall i,
        IsStrictlyPositive
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (troppCurrentRandomStep theta X i omega))))
    (hSigma : forall i, SigmaFinite (P.trim (hHistSub i)))
    (hRhsInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega =>
            traceMatrixExp (troppStateHistory theta X K i omega + K i))) :
    troppMasterTraceMGFFiniteFamilyStatement (P := P) X K V theta R := by
  have hZScaled :
      troppCurrentRandomStep theta X = scaledRandomMatrixFamily theta X := by
    funext i
    rfl
  exact
    troppMasterTraceMGFFiniteFamily_of_conditionalSteps
      X K V theta R
      (troppTraceState theta X K) mHist
      (troppStateHistory theta X K) (troppCurrentRandomStep theta X)
      hCond hHistSub hHistRand hZRand hHistMeas hHistSA hZSA hZScaled
      hStepIndep hCondTraceInt hExpIntStep hExpMeanSA hExpMeanPos hSigma
      hRhsInt
      (troppNaturalState_zero theta X K)
      (troppNaturalState_last theta X K)
      (troppNaturalState_left theta X K)
      (troppNaturalState_right theta X K)

/-- Thin semantic trace-mgf provider from the finite-family Tropp typed
primitive.

This theorem does not prove the finite-family Tropp/Lieb primitive. It takes
that primitive as an explicit assumption and applies it to its fully exposed
hypotheses. -/
theorem traceMGFBernsteinVarianceProxyBound_of_troppMasterTraceMGFFiniteFamily
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {I : Type*} [Fintype I] {n : Nat}
    (X : I -> RandomMatrix Omega n n)
    (K : I -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (hTropp :
      troppMasterTraceMGFFiniteFamilyStatement (P := P) X K V theta R)
    (hRand : forall i, IsRandomMatrix P (X i))
    (hSA : forall i, RandomSelfAdjointMatrix P (X i))
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P
          (fun omega => matrixExp (SMul.smul theta (X i omega))))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum X) theta))
    (hKSA : forall i, IsSelfAdjointMatrix (K i))
    (hVSA : IsSelfAdjointMatrix V)
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hMGF :
      forall i,
        MatrixLE
          (matrixExpect P
            (fun omega => matrixExp (SMul.smul theta (X i omega))))
          (matrixExp (K i)))
    (hNorm :
      Finset.univ.sum (fun i : I => K i) =
        SMul.smul (bernsteinMGFCoeff theta R) V) :
    TraceMGFBernsteinVarianceProxyBound P (randomMatrixSum X) V theta R :=
  hTropp hRand hSA hIndep hExpInt hTraceInt hKSA hVSA hR hRange hMGF hNorm

/-- Thin trace-MGF provider from explicit conditional-step Tropp data.

This wrapper keeps the public signature aligned with the ordinary
finite-family trace-MGF wrapper. It first derives the finite-family Tropp
primitive from the conditional-step/state package, then applies the existing
trace-MGF wrapper. The shared private core avoids duplicating the finite-chain
proof inside the finite-family provider. -/
theorem traceMGFBernsteinVarianceProxyBound_of_troppConditionalSteps
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (state : Fin (m + 1) -> RealRandomVariable Omega)
    (mHist : Fin m -> MeasurableSpace Omega)
    (H Z : Fin m -> RandomMatrix Omega n n)
    (hCond :
      forall i,
        troppMasterTraceMGFConditionalStepStatement (P := P)
          (mHist i) (H i) (Z i) (K i))
    (hHistSub : forall i, mHist i ≤ mOmega)
    (hHistRand : forall i, @IsRandomMatrix Omega mOmega n n P (H i))
    (hZRand : forall i, @IsRandomMatrix Omega mOmega n n P (Z i))
    (hHistMeas :
      forall i r c,
        @Measurable Omega Real (mHist i) inferInstance
          (fun omega => H i omega r c))
    (hHistSA : forall i omega, IsSelfAdjointMatrix (H i omega))
    (hZSA : forall i, @RandomSelfAdjointMatrix Omega mOmega n P (Z i))
    (hZScaled : Z = scaledRandomMatrixFamily theta X)
    (hStepIndep :
      forall i,
        @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _ (H i) (Z i) P)
    (hCondTraceInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega => traceMatrixExp (H i omega + Z i omega)))
    (hExpIntStep :
      forall i,
        @IntegrableRandomMatrix Omega mOmega n n P
          (fun omega => matrixExp (Z i omega)))
    (hExpMeanSA :
      forall i,
        IsSelfAdjointMatrix
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (Z i omega))))
    (hExpMeanPos :
      forall i,
        IsStrictlyPositive
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (Z i omega))))
    (hSigma : forall i, SigmaFinite (P.trim (hHistSub i)))
    (hRhsInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega => traceMatrixExp (H i omega + K i)))
    (hStateZero :
      state ⟨0, Nat.succ_pos m⟩ =
        fun omega =>
          traceMatrixExp
            (randomMatrixSum
              (scaledRandomMatrixFamily theta X) omega))
    (hStateLast :
      state ⟨m, Nat.lt_succ_self m⟩ =
        fun _omega =>
          traceMatrixExp (Finset.univ.sum fun i : Fin m => K i))
    (hStateLeft :
      forall i,
        state i.castSucc =
          fun omega => traceMatrixExp (H i omega + Z i omega))
    (hStateRight :
      forall i,
        state i.succ =
          fun omega => traceMatrixExp (H i omega + K i))
    (hRand : forall i, IsRandomMatrix P (X i))
    (hSA : forall i, RandomSelfAdjointMatrix P (X i))
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P
          (fun omega => matrixExp (SMul.smul theta (X i omega))))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum X) theta))
    (hKSA : forall i, IsSelfAdjointMatrix (K i))
    (hVSA : IsSelfAdjointMatrix V)
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hMGF :
      forall i,
        MatrixLE
          (matrixExpect P
            (fun omega => matrixExp (SMul.smul theta (X i omega))))
          (matrixExp (K i)))
    (hNorm :
      Finset.univ.sum (fun i : Fin m => K i) =
        SMul.smul (bernsteinMGFCoeff theta R) V) :
    TraceMGFBernsteinVarianceProxyBound P (randomMatrixSum X) V theta R :=
  traceMGFBernsteinVarianceProxyBound_of_troppMasterTraceMGFFiniteFamily
    X K V theta R
    (troppMasterTraceMGFFiniteFamily_of_conditionalSteps
      X K V theta R state mHist H Z hCond hHistSub hHistRand hZRand
      hHistMeas hHistSA hZSA hZScaled hStepIndep hCondTraceInt hExpIntStep
      hExpMeanSA hExpMeanPos hSigma hRhsInt hStateZero hStateLast hStateLeft
      hStateRight)
    hRand hSA hIndep hExpInt hTraceInt hKSA hVSA hR hRange hMGF hNorm

/-- Trace-MGF provider from natural-state conditional-step data.

This wrapper composes the natural-state finite-family Tropp provider with the
existing semantic trace-MGF provider. It removes the raw state, `H`, `Z`,
scaled-step equality, and endpoint assumptions from the public conditional-step
route while keeping all analytic assumptions explicit. -/
theorem traceMGFBernsteinVarianceProxyBound_of_naturalStateConditionalSteps
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real)
    (V : Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (mHist : Fin m -> MeasurableSpace Omega)
    (hCond :
      forall i,
        @troppMasterTraceMGFConditionalStepStatement Omega mOmega P n
          (mHist i) (@troppStateHistory Omega m n theta X K i)
          (@troppCurrentRandomStep Omega m n theta X i) (K i))
    (hHistSub : forall i, mHist i ≤ mOmega)
    (hHistRand :
      forall i,
        @IsRandomMatrix Omega mOmega n n P
          (troppStateHistory theta X K i))
    (hZRand :
      forall i,
        @IsRandomMatrix Omega mOmega n n P
          (troppCurrentRandomStep theta X i))
    (hHistMeas :
      forall i r c,
        @Measurable Omega Real (mHist i) inferInstance
          (fun omega => troppStateHistory theta X K i omega r c))
    (hHistSA :
      forall i omega, IsSelfAdjointMatrix (troppStateHistory theta X K i omega))
    (hZSA :
      forall i,
        @RandomSelfAdjointMatrix Omega mOmega n P
          (troppCurrentRandomStep theta X i))
    (hStepIndep :
      forall i,
        @ProbabilityTheory.IndepFun Omega _ _ mOmega _ _
          (troppStateHistory theta X K i)
          (troppCurrentRandomStep theta X i) P)
    (hCondTraceInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega =>
            traceMatrixExp
              (troppStateHistory theta X K i omega +
                troppCurrentRandomStep theta X i omega)))
    (hExpIntStep :
      forall i,
        @IntegrableRandomMatrix Omega mOmega n n P
          (fun omega => matrixExp (troppCurrentRandomStep theta X i omega)))
    (hExpMeanSA :
      forall i,
        IsSelfAdjointMatrix
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (troppCurrentRandomStep theta X i omega))))
    (hExpMeanPos :
      forall i,
        IsStrictlyPositive
          (@matrixExpect Omega mOmega n n P
            (fun omega => matrixExp (troppCurrentRandomStep theta X i omega))))
    (hSigma : forall i, SigmaFinite (P.trim (hHistSub i)))
    (hRhsInt :
      forall i,
        @IntegrableRealRandomVariable Omega mOmega P
          (fun omega =>
            traceMatrixExp (troppStateHistory theta X K i omega + K i)))
    (hRand : forall i, IsRandomMatrix P (X i))
    (hSA : forall i, RandomSelfAdjointMatrix P (X i))
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hExpInt :
      forall i,
        IntegrableRandomMatrix P
          (fun omega => matrixExp (SMul.smul theta (X i omega))))
    (hTraceInt :
      IntegrableRealRandomVariable P
        (traceExpIntegrand (randomMatrixSum X) theta))
    (hKSA : forall i, IsSelfAdjointMatrix (K i))
    (hVSA : IsSelfAdjointMatrix V)
    (hR : 0 <= R)
    (hRange : abs theta * R < 3)
    (hMGF :
      forall i,
        MatrixLE
          (matrixExpect P
            (fun omega => matrixExp (SMul.smul theta (X i omega))))
          (matrixExp (K i)))
    (hNorm :
      Finset.univ.sum (fun i : Fin m => K i) =
        SMul.smul (bernsteinMGFCoeff theta R) V) :
    TraceMGFBernsteinVarianceProxyBound P (randomMatrixSum X) V theta R :=
  traceMGFBernsteinVarianceProxyBound_of_troppMasterTraceMGFFiniteFamily
    X K V theta R
    (troppMasterTraceMGFFiniteFamily_of_naturalStateConditionalSteps
      X K V theta R mHist hCond hHistSub hHistRand hZRand hHistMeas hHistSA
      hZSA hStepIndep hCondTraceInt hExpIntStep hExpMeanSA hExpMeanPos
      hSigma hRhsInt)
    hRand hSA hIndep hExpInt hTraceInt hKSA hVSA hR hRange hMGF hNorm

/-- Typed Bernstein-specific scalar-to-matrix functional-calculus primitive.

This records the source-backed lift of the scalar Bernstein exponential
inequality to the explicit HighDimProb Loewner-style order:
`exp(theta A) <= I + theta A + g(theta, R) A^2`.

It is only a `Prop`-valued typed statement. The scalar Bernstein inequality,
CFC expression rewrites, conversion to `MatrixLE`, and
operator-norm-to-spectral-interval bridge are not proved here. -/
abbrev bernsteinMatrixExpLeQuadraticStatement {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (theta R : Real) : Prop :=
  IsSelfAdjointMatrix A ->
    deterministicOperatorNorm A <= R ->
      0 <= R ->
        abs theta * R < 3 ->
          MatrixLE
            (matrixExp (SMul.smul theta A))
            ((1 : Matrix (Fin n) (Fin n) Real) +
              SMul.smul theta A +
                SMul.smul (bernsteinMGFCoeff theta R) (matrixSquare A))

/-- Sign-normalization for the Bernstein functional-calculus primitive.

This theorem does not prove the CFC primitive. It only says that a supplied
primitive for `A` at parameter `-theta` can be reused for `-A` at parameter
`theta`, using coefficient parity and `(-A)^2 = A^2`. -/
theorem bernsteinMatrixExp_le_quadratic_neg_of_neg_theta {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (hA : bernsteinMatrixExpLeQuadraticStatement A (-theta) R) :
    bernsteinMatrixExpLeQuadraticStatement (-A) theta R := by
  intro hSA hBound hR hRange
  have hSApos : IsSelfAdjointMatrix A := by
    simpa using isSelfAdjointMatrix_neg hSA
  have hBoundPos : deterministicOperatorNorm A <= R := by
    have hnorm :
        deterministicOperatorNorm A = deterministicOperatorNorm (-A) := by
      unfold deterministicOperatorNorm
      rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def]
      simp
    exact hnorm.trans_le hBound
  have hRangePos : abs (-theta) * R < 3 := by
    simpa using hRange
  have h := hA hSApos hBoundPos hR hRangePos
  have harg : SMul.smul theta (-A) = SMul.smul (-theta) A := by
    ext r c
    simp [SMul.smul]
  have hrhs :
      (1 : Matrix (Fin n) (Fin n) Real) + SMul.smul theta (-A) +
          SMul.smul (bernsteinMGFCoeff theta R) (matrixSquare (-A)) =
        (1 : Matrix (Fin n) (Fin n) Real) + SMul.smul (-theta) A +
          SMul.smul (bernsteinMGFCoeff (-theta) R) (matrixSquare A) := by
    ext r c
    simp [SMul.smul, matrixSquare_neg]
  rw [← bernsteinMGFCoeff_neg theta R]
  simpa [harg, hrhs] using h

end BernsteinFunctionalCalculus

/-! ## Typed single-summand matrix-mgf primitive -/

section SingleSummandMatrixMGF

open scoped MatrixOrder Matrix.Norms.Operator Matrix.Norms.L2Operator

/-- Typed single-summand matrix MGF variance-proxy primitive.

This records the source-backed Bernstein single-summand step
`E exp(theta X) <= exp(g(theta, R) V)` in the explicit HighDimProb
Loewner-style order. It is only a `Prop`-valued typed statement. The scalar
functional-calculus lift, matrix-valued expectation monotonicity, and
boundedness-to-spectrum bridge are not proved here.

All assumptions currently needed by the future proof route are explicit:
measurability, pointwise self-adjointness, integrability of `X`, `X^2`, and
`exp(theta X)`, entrywise zero mean, pointwise operator-norm boundedness,
theta-range, self-adjoint/PSD structure of the deterministic comparison
matrix, and the square/variance-proxy comparison. -/
abbrev singleSummandMatrixMGFVarianceProxyStatement {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (X : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta R : Real) : Prop :=
  IsRandomMatrix P X ->
    RandomSelfAdjointMatrix P X ->
      IntegrableRandomMatrix P X ->
        IntegrableRandomMatrix P (randomMatrixSquare X) ->
          IntegrableRandomMatrix P
            (fun omega => matrixExp (SMul.smul theta (X omega))) ->
            matrixExpect P X = 0 ->
              (forall omega, operatorNorm X omega <= R) ->
                0 <= R ->
                  abs theta * R < 3 ->
                    IsSelfAdjointMatrix V ->
                      IsPSDMatrix V ->
                        MatrixLE (matrixSecondMoment P X) V ->
                          MatrixLE
                            (matrixExpect P
                              (fun omega =>
                                matrixExp (SMul.smul theta (X omega))))
                            (matrixExp
                              (SMul.smul (bernsteinMGFCoeff theta R) V))

/-- Single-summand matrix MGF variance-proxy provider assuming the pointwise
Bernstein functional-calculus primitive.

This theorem does not prove the CFC primitive
`bernsteinMatrixExpLeQuadraticStatement`; it takes that primitive as an
explicit pointwise assumption and assembles the expectation monotonicity,
linearity, variance-proxy comparison, coefficient nonnegativity, and
exponential lower-bound infrastructure. -/
theorem singleSummandMatrixMGFVarianceProxy_of_bernsteinMatrixExp_le_quadratic
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {n : Nat}
    (X : RandomMatrix Omega n n)
    (V : Matrix (Fin n) (Fin n) Real) (theta R : Real)
    (hCFC :
      forall omega,
        bernsteinMatrixExpLeQuadraticStatement (X omega) theta R) :
  singleSummandMatrixMGFVarianceProxyStatement (P := P) X V theta R := by
  intro hRand hSA hIntX hIntSq hIntExp hMeanZero hBound hR hRange hVSA hVPSD hSecond
  let c : Real := bernsteinMGFCoeff theta R
  let rhsRandom : RandomMatrix Omega n n :=
    fun omega =>
      (1 : Matrix (Fin n) (Fin n) Real) + SMul.smul theta (X omega) +
        SMul.smul c (matrixSquare (X omega))
  have hConstInt :
      IntegrableRandomMatrix P
        (fun _omega => (1 : Matrix (Fin n) (Fin n) Real)) :=
    integrableRandomMatrix_const (P := P) (1 : Matrix (Fin n) (Fin n) Real)
  have hThetaInt :
      IntegrableRandomMatrix P (fun omega => SMul.smul theta (X omega)) :=
    integrableRandomMatrix_smul theta hIntX
  have hCoeffInt :
      IntegrableRandomMatrix P
        (fun omega => SMul.smul c (matrixSquare (X omega))) := by
    exact integrableRandomMatrix_smul c hIntSq
  have hRhsInt : IntegrableRandomMatrix P rhsRandom := by
    exact integrableRandomMatrix_add
      (integrableRandomMatrix_add hConstInt hThetaInt) hCoeffInt
  have hPointwise :
      forall omega,
        MatrixLE
          (matrixExp (SMul.smul theta (X omega)))
          (rhsRandom omega) := by
    intro omega
    dsimp [rhsRandom, c]
    exact hCFC omega (hSA omega) (by simpa [operatorNorm] using hBound omega)
      hR hRange
  have hExpectToRhs :
      MatrixLE
        (matrixExpect P
          (fun omega => matrixExp (SMul.smul theta (X omega))))
        (matrixExpect P rhsRandom) :=
    matrixExpect_matrixLE_of_pointwise_matrixLE hIntExp hRhsInt hPointwise
  have hRhsExpect :
      matrixExpect P rhsRandom =
        (1 : Matrix (Fin n) (Fin n) Real) +
          SMul.smul theta (matrixExpect P X) +
            SMul.smul c (matrixSecondMoment P X) := by
    have hThetaExp :
        matrixExpect P (fun omega => SMul.smul theta (X omega)) =
          SMul.smul theta (matrixExpect P X) :=
      matrixExpect_smul theta
    have hCoeffExp :
        matrixExpect P (fun omega => SMul.smul c (matrixSquare (X omega))) =
          SMul.smul c (matrixExpect P (randomMatrixSquare X)) := by
      exact matrixExpect_smul (P := P) (A := randomMatrixSquare X) c
    calc
      matrixExpect P rhsRandom =
          matrixExpect P
              (fun omega =>
                (1 : Matrix (Fin n) (Fin n) Real) +
                  SMul.smul theta (X omega)) +
            matrixExpect P
              (fun omega => SMul.smul c (matrixSquare (X omega))) := by
            rw [matrixExpect_add
              (integrableRandomMatrix_add hConstInt hThetaInt) hCoeffInt]
      _ =
          (matrixExpect P
              (fun _omega => (1 : Matrix (Fin n) (Fin n) Real)) +
            matrixExpect P (fun omega => SMul.smul theta (X omega))) +
            matrixExpect P
              (fun omega => SMul.smul c (matrixSquare (X omega))) := by
            rw [matrixExpect_add hConstInt hThetaInt]
      _ =
        (1 : Matrix (Fin n) (Fin n) Real) +
          SMul.smul theta (matrixExpect P X) +
            SMul.smul c (matrixSecondMoment P X) := by
            simp [matrixExpect_const_of_isProbabilityMeasure, hThetaExp, hCoeffExp,
              matrixSecondMoment, add_assoc]
  have hRhsCentered :
      matrixExpect P rhsRandom =
        (1 : Matrix (Fin n) (Fin n) Real) +
          SMul.smul c (matrixSecondMoment P X) := by
    calc
      matrixExpect P rhsRandom =
          (1 : Matrix (Fin n) (Fin n) Real) +
            SMul.smul theta (matrixExpect P X) +
              SMul.smul c (matrixSecondMoment P X) := hRhsExpect
      _ =
          (1 : Matrix (Fin n) (Fin n) Real) +
            SMul.smul theta (0 : Matrix (Fin n) (Fin n) Real) +
              SMul.smul c (matrixSecondMoment P X) := by
            rw [hMeanZero]
      _ =
          (1 : Matrix (Fin n) (Fin n) Real) +
            SMul.smul c (matrixSecondMoment P X) := by
            have hThetaZero :
                SMul.smul theta (0 : Matrix (Fin n) (Fin n) Real) =
                  (0 : Matrix (Fin n) (Fin n) Real) := by
              exact smul_zero theta
            rw [hThetaZero, add_zero]
  have hRhsToSecond :
      MatrixLE
        (matrixExpect P rhsRandom)
        ((1 : Matrix (Fin n) (Fin n) Real) +
          SMul.smul c (matrixSecondMoment P X)) :=
    matrixLE_of_eq hRhsCentered
  have hCoeffNonneg : 0 <= c := by
    dsimp [c]
    exact bernsteinMGFCoeff_nonneg hRange
  have hSecondToV :
      MatrixLE
        ((1 : Matrix (Fin n) (Fin n) Real) +
          SMul.smul c (matrixSecondMoment P X))
        ((1 : Matrix (Fin n) (Fin n) Real) + SMul.smul c V) :=
    matrixLE_add_left (1 : Matrix (Fin n) (Fin n) Real)
      (matrixLE_smul_of_nonneg hCoeffNonneg hSecond)
  have hVToExp :
      MatrixLE
        ((1 : Matrix (Fin n) (Fin n) Real) + SMul.smul c V)
        (matrixExp (SMul.smul c V)) :=
    matrixLE_one_add_smul_le_matrixExp_smul_of_selfAdjoint c hVSA
  have hFinal :
      MatrixLE
        (matrixExpect P
          (fun omega => matrixExp (SMul.smul theta (X omega))))
        (matrixExp (SMul.smul c V)) :=
    matrixLE_trans hExpectToRhs
      (matrixLE_trans hRhsToSecond (matrixLE_trans hSecondToV hVToExp))
  simpa [c] using hFinal

end SingleSummandMatrixMGF

/-- Typed target: trace of the exponential of a real self-adjoint matrix is
nonnegative.

The theorem below now proves this target via
`matrixExp_posSemidef_of_selfAdjoint` and
`traceMatrixExp_nonneg_of_matrixExp_posSemidef`. -/
abbrev traceMatrixExpNonnegOfSelfAdjointStatement {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) : Prop :=
  IsSelfAdjointMatrix A -> 0 <= traceMatrixExp A

/-- Trace of the exponential of a real self-adjoint matrix is nonnegative. -/
theorem traceMatrixExp_nonneg_of_selfAdjoint {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    0 <= traceMatrixExp A :=
  traceMatrixExp_nonneg_of_matrixExp_posSemidef
    (matrixExp_posSemidef_of_selfAdjoint hA)

section LambdaMaxOrderedMatrixExp

open scoped MatrixOrder Matrix.Norms.Operator Matrix.Norms.L2Operator

/-- Trace-exp as the sum of exponentials of Hermitian eigenvalues.

This is the eigenvalue-sum bridge for the repository's `traceMatrixExp`
wrapper. It uses Mathlib's Hermitian continuous functional calculus
diagonalization; it does not prove any trace-mgf or Bernstein inequality. -/
theorem traceMatrixExp_eq_sum_exp_eigenvalues {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) :
    traceMatrixExp A =
      Finset.univ.sum fun i => Real.exp (hA.eigenvalues i) := by
  rw [traceMatrixExp, matrixTrace, matrixExp]
  rw [show NormedSpace.exp A = cfc Real.exp A from
    (CFC.real_exp_eq_normedSpace_exp (a := A)
      (ha := hA.isSelfAdjoint)).symm]
  rw [Matrix.IsHermitian.cfc_eq hA Real.exp]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp

/-- The real spectrum of the matrix exponential of a self-adjoint real matrix
is the pointwise real exponential image of the original real spectrum. -/
private theorem matrixExp_spectrum_real_eq_exp_image {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) :
    spectrum Real (matrixExp A) = Real.exp '' spectrum Real A := by
  rw [matrixExp]
  rw [← CFC.real_exp_eq_normedSpace_exp (a := A) hA.isSelfAdjoint]
  exact cfc_map_spectrum Real.exp A hA.isSelfAdjoint

/-- The ordered lambda-max endpoint is a real spectral value. -/
private theorem lambdaMaxOrdered_mem_spectrum_real_for_traceExp {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) :
    lambdaMaxOrdered A hA ∈ spectrum Real A := by
  classical
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (by simp)
  have hmem := hA.eigenvalues_mem_spectrum_real (e 0)
  simpa [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues, e] using hmem

/-- Every real spectral value of a self-adjoint matrix is bounded by the
ordered endpoint. -/
private theorem spectrum_real_le_lambdaMaxOrdered_for_traceExp {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) {x : Real}
    (hx : x ∈ spectrum Real A) :
    x <= lambdaMaxOrdered A hA := by
  classical
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  rcases hx with ⟨i, rfl⟩
  dsimp [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues]
  exact hA.eigenvalues₀_antitone (Fin.zero_le _)

/-- The ordered largest eigenvalue of the matrix exponential is the real
exponential of the ordered largest eigenvalue. -/
theorem lambdaMaxOrdered_matrixExp
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) :
    lambdaMaxOrdered (matrixExp A) (isSelfAdjointMatrix_matrixExp hA)
      = Real.exp (lambdaMaxOrdered A hA) := by
  classical
  let hExpA : IsSelfAdjointMatrix (matrixExp A) :=
    isSelfAdjointMatrix_matrixExp hA
  change lambdaMaxOrdered (matrixExp A) hExpA
      = Real.exp (lambdaMaxOrdered A hA)
  apply le_antisymm
  · have hmemExp :
        lambdaMaxOrdered (matrixExp A) hExpA ∈ spectrum Real (matrixExp A) :=
      lambdaMaxOrdered_mem_spectrum_real_for_traceExp (matrixExp A) hExpA
    have hspectrum :
        spectrum Real (matrixExp A) = Real.exp '' spectrum Real A :=
      matrixExp_spectrum_real_eq_exp_image hA
    rw [hspectrum] at hmemExp
    rcases hmemExp with ⟨mu, hmu, hmul⟩
    rw [← hmul]
    exact Real.exp_le_exp.mpr
      (spectrum_real_le_lambdaMaxOrdered_for_traceExp hA hmu)
  · have hmemTop :
        Real.exp (lambdaMaxOrdered A hA) ∈ spectrum Real (matrixExp A) := by
      rw [matrixExp_spectrum_real_eq_exp_image hA]
      exact ⟨lambdaMaxOrdered A hA,
        lambdaMaxOrdered_mem_spectrum_real_for_traceExp A hA, rfl⟩
    exact spectrum_real_le_lambdaMaxOrdered_for_traceExp hExpA hmemTop

/-- Trace-exp is bounded by dimension times the largest exponential eigenvalue.

This is the deterministic eigenvalue-count step used before applying a
separate spectral/norm bound to the input matrix. -/
private theorem traceMatrixExp_le_card_mul_exp_lambdaMaxOrdered
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) :
    traceMatrixExp A <=
      (n + 1 : Real) * Real.exp (lambdaMaxOrdered A hA) := by
  classical
  let hExpA : IsSelfAdjointMatrix (matrixExp A) :=
    isSelfAdjointMatrix_matrixExp hA
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (by simp)
  have htrace :
      Matrix.trace (matrixExp A) = ∑ i, hExpA.eigenvalues i :=
    hExpA.trace_eq_sum_eigenvalues
  have hterm :
      ∀ i : Fin (n + 1),
        hExpA.eigenvalues i <=
          lambdaMaxOrdered (matrixExp A) hExpA := by
    intro i
    have hgreat :=
      lambdaMaxOrdered_is_greatest_eigenvalue (matrixExp A) hExpA (e.symm i)
    simpa [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues, e] using hgreat
  calc
    traceMatrixExp A
        = ∑ i : Fin (n + 1), hExpA.eigenvalues i := by
          simpa [traceMatrixExp, matrixTrace] using htrace
    _ <= ∑ _i : Fin (n + 1), lambdaMaxOrdered (matrixExp A) hExpA := by
          exact Finset.sum_le_sum (by
            intro i _hi
            exact hterm i)
    _ = (n + 1 : Real) * lambdaMaxOrdered (matrixExp A) hExpA := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (n + 1 : Real) * Real.exp (lambdaMaxOrdered A hA) := by
          rw [lambdaMaxOrdered_matrixExp hA]

/-- Explicit support-domination certificate for the matrix exponential.

This names the deterministic certificate used by rank/support trace-exp
consumers. It is only a vocabulary wrapper around the existing Loewner-order
comparison; it does not construct a support matrix or prove the certificate for
any application. -/
abbrev MatrixExpSupportDomination {n : Nat}
    (A support : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  MatrixLE (matrixExp A) (Real.exp (lambdaMaxOrdered A hA) • support)

/-- Explicit support-domination certificate for the excess matrix exponential.

This is the corrected low-rank support shape for trace-exponential dimension
work: zero directions of `A` contribute the identity term to `matrixExp A`, so a
proper support certificate should often control `matrixExp A - 1`, not
`matrixExp A` itself. This is only vocabulary; it does not construct the
support or prove the certificate. -/
abbrev MatrixExpExcessSupportDomination {n : Nat}
    (A support : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  MatrixLE (matrixExp A - 1)
    ((Real.exp (lambdaMaxOrdered A hA) - 1) • support)

/-- Trace-exp bound from an explicit support domination certificate.

This bridge only consumes a provided Loewner comparison against a support
matrix. It does not construct support projections or prove any rank theorem. -/
theorem traceMatrixExp_le_trace_support_exp_lambdaMax_of_matrixExp_le_smul_support
    {n : Nat} {A support : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A)
    (hDom : MatrixExpSupportDomination A support hA) :
    traceMatrixExp A <=
      matrixTrace support * Real.exp (lambdaMaxOrdered A hA) := by
  have hTrace := matrixTrace_le_of_matrixLE hDom
  simpa [traceMatrixExp, matrixTrace_smul, mul_comm] using hTrace

/-- Trace-exp bound from the named matrix-exponential support-domination
certificate.

This is the preferred reader-facing spelling of
`traceMatrixExp_le_trace_support_exp_lambdaMax_of_matrixExp_le_smul_support`.
The older name is kept as a compatibility alias for code that still talks
directly about the underlying Loewner comparison. -/
theorem traceMatrixExp_le_trace_support_exp_lambdaMax_of_supportDomination
    {n : Nat} {A support : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A)
    (hDom : MatrixExpSupportDomination A support hA) :
    traceMatrixExp A <=
      matrixTrace support * Real.exp (lambdaMaxOrdered A hA) :=
  traceMatrixExp_le_trace_support_exp_lambdaMax_of_matrixExp_le_smul_support
    hA hDom

/-- Trace-exp excess bound from an explicit excess support-domination
certificate.

This deterministic bridge consumes a certificate for `matrixExp A - 1`, so the
ambient identity contribution remains visible as `(n + 1)`. It does not prove
the excess support certificate or construct a support matrix. -/
theorem traceMatrixExp_le_card_add_trace_support_mul_exp_sub_one_of_excessSupportDomination
    {n : Nat} {A support : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A)
    (hDom : MatrixExpExcessSupportDomination A support hA) :
    traceMatrixExp A <=
      ((n + 1 : Nat) : Real) +
        matrixTrace support * (Real.exp (lambdaMaxOrdered A hA) - 1) := by
  have hTrace := matrixTrace_le_of_matrixLE hDom
  have hTrace' :
      matrixTrace (matrixExp A - 1) <=
        matrixTrace support * (Real.exp (lambdaMaxOrdered A hA) - 1) := by
    simpa [matrixTrace_smul, mul_comm] using hTrace
  have hSplit :
      traceMatrixExp A =
        ((n + 1 : Nat) : Real) + matrixTrace (matrixExp A - 1) := by
    simp [traceMatrixExp, matrixTrace, Matrix.trace_sub]
  calc
    traceMatrixExp A =
        ((n + 1 : Nat) : Real) + matrixTrace (matrixExp A - 1) := hSplit
    _ <= ((n + 1 : Nat) : Real) +
          matrixTrace support * (Real.exp (lambdaMaxOrdered A hA) - 1) := by
        simpa [add_comm] using
          add_le_add_left hTrace' ((n + 1 : Nat) : Real)

/-- Deterministic trace-exponential dimension bound under a direct ordered
lambda-max upper bound.

This is generic deterministic spectral infrastructure.  It does not mention
random matrices, variance proxies, Bernstein coefficients, or tail bounds. -/
theorem traceMatrixExp_smul_le_card_exp_of_lambdaMaxOrdered_le
    {n : Nat} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (c sigmaSq : Real)
    (hc : 0 <= c)
    (hV : IsSelfAdjointMatrix V)
    (hSpec : lambdaMaxOrdered V hV <= sigmaSq) :
    traceMatrixExp (c • V) <=
      (n + 1 : Real) * Real.exp (c * sigmaSq) := by
  let hCV : IsSelfAdjointMatrix (c • V) :=
    isSelfAdjointMatrix_smul c hV
  have hTrace :
      traceMatrixExp (c • V) <=
        (n + 1 : Real) *
          Real.exp (lambdaMaxOrdered (c • V) hCV) :=
    traceMatrixExp_le_card_mul_exp_lambdaMaxOrdered hCV
  have hLambda :
      lambdaMaxOrdered (c • V) hCV <= c * sigmaSq := by
    change
      lambdaMaxOrdered (c • V) (isSelfAdjointMatrix_smul c hV) <=
        c * sigmaSq
    rw [lambdaMaxOrdered_smul_of_nonneg c hc hV]
    exact mul_le_mul_of_nonneg_left hSpec hc
  have hExp :
      Real.exp (lambdaMaxOrdered (c • V) hCV) <=
        Real.exp (c * sigmaSq) :=
    Real.exp_le_exp.mpr hLambda
  have hCardNonneg : 0 <= (n + 1 : Real) := by
    positivity
  exact le_trans hTrace (mul_le_mul_of_nonneg_left hExp hCardNonneg)

/-- PSD trace-exp minus-identity bridge under a lambda-max variance proxy bound.

This deterministic spectral bridge is the intrinsic-dimension step before any
effective-rank consumer. It uses the eigenvalue-sum formula for
`traceMatrixExp`, the scalar exponential chord inequality, PSD eigenvalue
nonnegativity, and trace/eigenvalue normalization. It does not prove a trace-MGF
provider, variance-proxy control, or Matrix Bernstein. -/
theorem traceMatrixExp_smul_le_card_add_trace_div_mul_exp_sub_one_of_psd_lambdaMax_le
    {n : Nat} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    {c sigmaSq : Real}
    (hc : 0 <= c) (hsigma : 0 < sigmaSq)
    (hPSD : IsPSDMatrix V)
    (hV : IsSelfAdjointMatrix V)
    (hSpec : lambdaMaxOrdered V hV <= sigmaSq) :
    traceMatrixExp (c • V) <=
      (n + 1 : Real) +
        (matrixTrace V / sigmaSq) * (Real.exp (c * sigmaSq) - 1) := by
  by_cases hc_zero : c = 0
  case pos =>
    subst c
    have hBase :=
      traceMatrixExp_smul_le_card_exp_of_lambdaMaxOrdered_le
        (V := V) (c := 0) (sigmaSq := sigmaSq) (by norm_num) hV hSpec
    have hRhs : (n + 1 : Real) * Real.exp (0 * sigmaSq) =
        (n + 1 : Real) + (matrixTrace V / sigmaSq) * (Real.exp (0 * sigmaSq) - 1) := by
      simp [Real.exp_zero]
    exact hBase.trans_eq hRhs
  case neg =>
    have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc_zero)
    let hCV : IsSelfAdjointMatrix (c • V) := isSelfAdjointMatrix_smul c hV
    have hCVPSD_explicit : IsPSDMatrix (c • V) :=
      isPSDMatrix_smul_of_nonneg hc hPSD
    have hCVPSD : Matrix.PosSemidef (c • V) :=
      posSemidef_of_isPSDMatrix hCVPSD_explicit
    let e : Equiv (Fin (Fintype.card (Fin (n + 1)))) (Fin (n + 1)) :=
      Fintype.equivOfCardEq (by simp)
    have hLambda : lambdaMaxOrdered (c • V) hCV <= c * sigmaSq := by
      change lambdaMaxOrdered (c • V) (isSelfAdjointMatrix_smul c hV) <=
        c * sigmaSq
      rw [lambdaMaxOrdered_smul_of_nonneg c hc hV]
      exact mul_le_mul_of_nonneg_left hSpec hc
    have hsigmaC : 0 < c * sigmaSq := mul_pos hc_pos hsigma
    have hterm : forall i : Fin (n + 1),
        Real.exp (hCV.eigenvalues i) <=
          1 + (hCV.eigenvalues i / (c * sigmaSq)) *
            (Real.exp (c * sigmaSq) - 1) := by
      intro i
      have hx0 : 0 <= hCV.eigenvalues i := hCVPSD.eigenvalues_nonneg i
      have hx_le_lmax : hCV.eigenvalues i <= lambdaMaxOrdered (c • V) hCV := by
        have hgreat :=
          lambdaMaxOrdered_is_greatest_eigenvalue (c • V) hCV (e.symm i)
        simpa [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues, e] using hgreat
      have hxle : hCV.eigenvalues i <= c * sigmaSq := hx_le_lmax.trans hLambda
      simpa [one_mul] using
        exp_mul_le_chord_exp_of_nonneg_of_le
          (c := (1 : Real)) (x := hCV.eigenvalues i) (sigma := c * sigmaSq)
          (by norm_num) hx0 hxle hsigmaC
    have hsum_le :
        Finset.univ.sum (fun i : Fin (n + 1) => Real.exp (hCV.eigenvalues i)) <=
          Finset.univ.sum (fun i : Fin (n + 1) =>
            1 + (hCV.eigenvalues i / (c * sigmaSq)) *
              (Real.exp (c * sigmaSq) - 1)) := by
      exact Finset.sum_le_sum (by intro i _hi; exact hterm i)
    have htrace_eigs :
        matrixTrace (c • V) =
          Finset.univ.sum fun i : Fin (n + 1) => hCV.eigenvalues i := by
      simpa [matrixTrace] using hCV.trace_eq_sum_eigenvalues
    have hsum_eigs :
        Finset.univ.sum (fun i : Fin (n + 1) => hCV.eigenvalues i) =
          c * matrixTrace V := by
      rw [<- htrace_eigs, matrixTrace_smul]
    have hsum_rhs :
        Finset.univ.sum (fun i : Fin (n + 1) =>
            1 + (hCV.eigenvalues i / (c * sigmaSq)) *
              (Real.exp (c * sigmaSq) - 1)) =
          (n + 1 : Real) +
            (matrixTrace V / sigmaSq) * (Real.exp (c * sigmaSq) - 1) := by
      rw [Finset.sum_add_distrib]
      have hones : Finset.univ.sum (fun _i : Fin (n + 1) => (1 : Real)) =
          (n + 1 : Real) := by
        simp
      rw [hones]
      have hfactor :
          Finset.univ.sum (fun i : Fin (n + 1) =>
              (hCV.eigenvalues i / (c * sigmaSq)) *
                (Real.exp (c * sigmaSq) - 1)) =
            (matrixTrace V / sigmaSq) * (Real.exp (c * sigmaSq) - 1) := by
        rw [<- Finset.sum_mul]
        have hdivsum :
            Finset.univ.sum (fun i : Fin (n + 1) =>
              hCV.eigenvalues i / (c * sigmaSq)) = matrixTrace V / sigmaSq := by
          rw [<- Finset.sum_div, hsum_eigs]
          field_simp [hc_pos.ne', hsigma.ne']
        rw [hdivsum]
      rw [hfactor]
    calc
      traceMatrixExp (c • V)
          = Finset.univ.sum (fun i : Fin (n + 1) => Real.exp (hCV.eigenvalues i)) := by
              exact traceMatrixExp_eq_sum_exp_eigenvalues hCV
      _ <= Finset.univ.sum (fun i : Fin (n + 1) =>
            1 + (hCV.eigenvalues i / (c * sigmaSq)) *
              (Real.exp (c * sigmaSq) - 1)) := hsum_le
      _ = (n + 1 : Real) +
            (matrixTrace V / sigmaSq) * (Real.exp (c * sigmaSq) - 1) := hsum_rhs

end LambdaMaxOrderedMatrixExp

/-- Typed target for nonnegativity of the real trace-exponential moment. -/
abbrev traceExpMomentNonnegStatement {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (Y : RandomMatrix Omega n n)
    (theta : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 <= theta ->
      0 <= traceExpMoment P Y theta

/-- The real trace-exponential moment is nonnegative whenever its scalar
integrand is pointwise nonnegative. -/
theorem traceExpMoment_nonneg_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} (Y : RandomMatrix Omega n n)
    (theta : Real)
    (hNonneg : forall omega, 0 <= traceExpIntegrand Y theta omega) :
    0 <= traceExpMoment P Y theta := by
  simpa [traceExpMoment] using
    integral_nonneg_of_ae (ae_of_all P hNonneg)

/-- The trace-exponential integrand is pointwise nonnegative for a random
self-adjoint matrix, for every real scalar parameter. -/
theorem traceExpIntegrand_nonneg_of_randomSelfAdjoint {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {Y : RandomMatrix Omega n n} (theta : Real)
    (hY : RandomSelfAdjointMatrix P Y) :
    forall omega, 0 <= traceExpIntegrand Y theta omega := by
  intro omega
  exact traceMatrixExp_nonneg_of_selfAdjoint
    (isSelfAdjointMatrix_smul theta (hY omega))

/-- The real trace-exponential moment is nonnegative for a random
self-adjoint matrix, for every real scalar parameter. -/
theorem traceExpMoment_nonneg_of_randomSelfAdjoint {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta : Real)
    (hY : RandomSelfAdjointMatrix P Y) :
    0 <= traceExpMoment P Y theta := by
  exact traceExpMoment_nonneg_of_nonneg Y theta
    (traceExpIntegrand_nonneg_of_randomSelfAdjoint theta hY)

/-- The lintegral trace-exponential moment is always nonnegative as an
`ENNReal` value. -/
theorem traceExpMomentLIntegral_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {n : Nat} (Y : RandomMatrix Omega n n)
    (theta : Real) :
    0 <= traceExpMomentLIntegral P Y theta := by
  exact bot_le

/-- Typed target connecting the lintegral and real-expectation trace-exp
moments under the hypotheses future Laplace proofs should make explicit. -/
abbrev traceExpMomentLIntegralEqOfRealStatement {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (theta : Real) : Prop :=
  IntegrableRealRandomVariable P (traceExpIntegrand Y theta) ->
    (forall omega, 0 <= traceExpIntegrand Y theta omega) ->
      traceExpMomentLIntegral P Y theta =
        ENNReal.ofReal (traceExpMoment P Y theta)

/-- For a nonnegative integrable trace-exponential integrand, the lintegral
through `ENNReal.ofReal` is the `ENNReal.ofReal` of the raw real expectation. -/
theorem traceExpMomentLIntegral_eq_ofReal_traceExpMoment {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (theta : Real)
    (hInt : IntegrableRealRandomVariable P (traceExpIntegrand Y theta))
    (hNonneg : forall omega, 0 <= traceExpIntegrand Y theta omega) :
    traceExpMomentLIntegral P Y theta =
      ENNReal.ofReal (traceExpMoment P Y theta) := by
  rw [traceExpMomentLIntegral, traceExpMoment]
  exact (ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all P hNonneg)).symm

/-- Convert a bounded-Bernstein real trace-MGF semantic bound into its
lintegral semantic form.

This is only the real-to-lintegral bridge. It does not prove a trace-MGF
provider, a Laplace event theorem, dimension/norm reduction, theta
optimization, or Matrix Bernstein. -/
theorem traceMGFBernsteinVarianceProxyBoundLIntegral_of_traceMGFBernsteinVarianceProxyBound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (Y : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta R : Real)
    (hY : RandomSelfAdjointMatrix P Y)
    (hInt : IntegrableRealRandomVariable P (traceExpIntegrand Y theta))
    (hReal : TraceMGFBernsteinVarianceProxyBound P Y V theta R) :
    TraceMGFBernsteinVarianceProxyBoundLIntegral P Y V theta R := by
  have hRaw :
      traceExpMoment P Y theta <=
        traceMatrixExp (SMul.smul (bernsteinMGFCoeff theta R) V) := by
    simpa [TraceMGFBernsteinVarianceProxyBound, TraceMGFBound] using hReal
  unfold TraceMGFBernsteinVarianceProxyBoundLIntegral TraceMGFBoundLIntegral
  rw [traceExpMomentLIntegral_eq_ofReal_traceExpMoment
    Y theta hInt (traceExpIntegrand_nonneg_of_randomSelfAdjoint theta hY)]
  exact ENNReal.ofReal_le_ofReal hRaw

/-- Typed target for future trace-exponential moment bounds.

The right side is supplied as a scalar bound so different future trace-mgf
theorems can choose their own constants and variance proxies. -/
abbrev traceExpMomentBoundStatement {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (Y : RandomMatrix Omega n n)
    (theta rhs : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 <= theta ->
      traceExpMoment P Y theta <= rhs

/-- Typed target for the matrix-Bernstein-style trace-mgf bound using a
deterministic variance proxy matrix. -/
abbrev traceExpVarianceProxyBoundStatement {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (Y : RandomMatrix Omega n n)
    (V : Matrix (Fin n) (Fin n) Real) (theta : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    IsPSDMatrix V ->
      0 <= theta ->
        traceExpMoment P Y theta <= traceMatrixExp ((theta ^ 2 / 2) • V)

/-! ## Typed trace-mgf targets over the semantic layer -/

/-- Typed target for future real trace-mgf bounds, stated through the semantic
predicate rather than directly through `traceExpMoment`. -/
abbrev traceMGFBoundStatement {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (Y : RandomMatrix Omega n n)
    (theta rhs : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 <= theta ->
      TraceMGFBound P Y theta rhs

/-- Typed target for future lintegral trace-mgf bounds. -/
abbrev traceMGFBoundLIntegralStatement {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} (P : Measure Omega) (Y : RandomMatrix Omega n n)
    (theta : Real) (rhs : ENNReal) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    0 <= theta ->
      TraceMGFBoundLIntegral P Y theta rhs

/-- Typed target for future variance-proxy trace-mgf bounds. This is the
semantic form of `traceExpVarianceProxyBoundStatement`; the hard provider proof
is intentionally deferred. -/
abbrev traceMGFVarianceProxyBoundStatement {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    IsPSDMatrix V ->
      0 <= theta ->
        TraceMGFVarianceProxyBound P Y V theta

/-- Typed target for future bounded-Bernstein variance-proxy trace-mgf bounds.

This variant records the denominator coefficient used by the bounded Matrix
Bernstein single-summand route. The hard trace-mgf provider remains deferred. -/
abbrev traceMGFBernsteinVarianceProxyBoundStatement {Omega : Type*}
    [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta R : Real) : Prop :=
  RandomSelfAdjointMatrix P Y ->
    IsPSDMatrix V ->
      0 <= theta ->
        abs theta * R < 3 ->
          TraceMGFBernsteinVarianceProxyBound P Y V theta R

/-- Typed target: real `TraceMGFBernsteinVarianceProxyBound` plus integrability and
nonnegativity imply the lintegral `TraceMGFBernsteinVarianceProxyBoundLIntegral`.

This is the bridge from the proved real-valued MB-S9 trace-MGF entry point to the
lintegral form consumed by the Laplace/tail layer.  The integrability and
nonnegativity of `traceExpIntegrand` are required because the `LIntegral` route
works through `ENNReal.ofReal`. -/
abbrev traceMGFBernsteinVarianceProxyBoundLIntegralOfRealStatement
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat} (P : Measure Omega)
    (Y : RandomMatrix Omega n n) (V : Matrix (Fin n) (Fin n) Real)
    (theta R : Real) : Prop :=
  IntegrableRealRandomVariable P (traceExpIntegrand Y theta) ->
    (forall omega, 0 <= traceExpIntegrand Y theta omega) ->
      TraceMGFBernsteinVarianceProxyBound P Y V theta R ->
        TraceMGFBernsteinVarianceProxyBoundLIntegral P Y V theta R

end

end HighDimProb
