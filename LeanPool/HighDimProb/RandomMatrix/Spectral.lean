/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import LeanPool.HighDimProb.RandomMatrix.MatrixOrder
import LeanPool.HighDimProb.RandomMatrix.OperatorNorm

/-!
# Spectral and quadratic-form event vocabulary

Verified Wikipedia references:
* Eigenvalues and eigenvectors: https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors
* Spectral theorem: https://en.wikipedia.org/wiki/Spectral_theorem
* Operator norm: https://en.wikipedia.org/wiki/Operator_norm
* Loewner order: https://en.wikipedia.org/wiki/Loewner_order

This module starts the matrix Bernstein spectral layer. Mathlib provides
Hermitian eigenvalues, but HighDimProb does not yet have a proved lambda-max
Rayleigh quotient bridge. We therefore expose two honest layers:

* narrow `lambdaMax` / `lambdaMin` wrappers for visibly nonempty finite real
  self-adjoint matrices;
* dimension-agnostic quadratic-form bound and tail-event predicates that can
  be used before the full spectral theorem interface is connected.
-/

namespace HighDimProb

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder Pointwise

noncomputable section

/-! ## Semantic spectral upper-bound layer -/

/-- Semantic Loewner-style upper spectral bound.

`SpectralUpperBound A L` means that `L * I - A` is positive semidefinite in
Mathlib's matrix order. Concrete endpoint providers such as `lambdaMax` and
`lambdaMaxOrdered` should specialize to this predicate rather than duplicating
its matrix expression downstream. -/
abbrev SpectralUpperBound {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (L : Real) : Prop :=
  (((L • (1 : Matrix (Fin n) (Fin n) Real)) - A).PosSemidef)

/-- Semantic Rayleigh upper bound over HighDimProb's explicit unit sphere. -/
def RayleighUpperBound {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (L : Real) : Prop :=
  forall x : Fin n -> Real, IsUnitVector x -> matrixQuadraticForm A x <= L

/-- Generic scalar upper-tail event for a real-valued process. -/
def scalarUpperTailEvent {Omega : Type*}
    (Z : Omega -> Real) (t : Real) : Set Omega :=
  {omega | t <= Z omega}

/-- Upper-tail event for a scalar semantic upper-bound provider attached to a
random matrix.

The matrix argument records the semantic owner of the bound; the proof that
`L omega` actually bounds `A omega` remains a separate hypothesis. -/
def matrixUpperBoundTailEvent {Omega : Type*}
    {n : Nat} (A : RandomMatrix Omega n n) (L : Omega -> Real)
    (t : Real) : Set Omega :=
  let _ := A
  scalarUpperTailEvent L t

/-! ## Lambda endpoint wrappers -/

/-- Largest-eigenvalue wrapper for a real self-adjoint matrix indexed by a
nonempty `Fin (n + 1)` type.

This uses Mathlib's ordered Hermitian eigenvalue list. The bridge from this
wrapper to HighDimProb's explicit quadratic-form order is intentionally kept as
a statement target below. -/
def lambdaMax {n : Nat} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Real :=
  hA.eigenvalues 0

/-- Canonical largest-eigenvalue endpoint using Mathlib's ordered Hermitian
eigenvalue API directly.

This is intentionally separate from `lambdaMax`, whose public meaning remains
the existing `eigenvalues 0` wrapper. -/
def lambdaMaxOrdered {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Real :=
  hA.eigenvalues₀ 0

/-- The ordered lambda-max wrapper is definitionally Mathlib's ordered
Hermitian endpoint. -/
theorem lambdaMaxOrdered_eq_eigenvalues₀_zero {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) :
    lambdaMaxOrdered A hA = hA.eigenvalues₀ 0 :=
  rfl

/-- Smallest-eigenvalue wrapper for a real self-adjoint matrix indexed by a
nonempty `Fin (n + 1)` type. -/
def lambdaMin {n : Nat} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Real :=
  hA.eigenvalues (Fin.last n)

/-! ## Explicit quadratic-form bound predicates -/

/-- Quadratic-form upper bound over the explicit unit sphere.

This is the proof-ready surrogate for a future `lambdaMax A <= t` event when
the lambda-max/Rayleigh bridge is not yet available. -/
def QuadraticFormUpperBound {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (t : Real) : Prop :=
  RayleighUpperBound A t

/-- Quadratic-form lower bound over the explicit unit sphere. -/
def QuadraticFormLowerBound {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (t : Real) : Prop :=
  forall x : Fin n -> Real, IsUnitVector x -> t <= matrixQuadraticForm A x

/-- Monotonicity of quadratic-form upper bounds in the scalar threshold. -/
theorem quadraticFormUpperBound_mono {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} {s t : Real}
    (hst : s <= t) (hA : QuadraticFormUpperBound A s) :
    QuadraticFormUpperBound A t := by
  intro x hx
  exact le_trans (hA x hx) hst

/-- Monotonicity of quadratic-form lower bounds in the scalar threshold. -/
theorem quadraticFormLowerBound_mono {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} {s t : Real}
    (hst : s <= t) (hA : QuadraticFormLowerBound A t) :
    QuadraticFormLowerBound A s := by
  intro x hx
  exact le_trans hst (hA x hx)

/-- Proof-friendly lambda-max upper-bound predicate.

This is definitionally the quadratic-form upper bound. It is not a proved
eigenvalue characterization; that bridge is recorded by
`lambdaMaxLeIffQuadraticFormLeStatement`. -/
abbrev LambdaMaxBound {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (t : Real) : Prop :=
  QuadraticFormUpperBound A t

/-! ## Spectral bridge typed targets -/

/-- Typed target recording that the `lambdaMax` wrapper is the greatest
Hermitian eigenvalue.

Mathlib exposes decreasing Hermitian eigenvalue order through the underlying
`eigenvalues₀` / symmetric-operator APIs. The remaining work is the clean
bridge through HighDimProb's `Fin (n + 1)` wrapper and explicit naming. -/
abbrev lambdaMaxIsGreatestEigenvalueStatement {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  forall i : Fin (n + 1), hA.eigenvalues i <= lambdaMax A hA

/-- Typed target recording that the legacy `lambdaMax` wrapper agrees with the
canonical ordered endpoint wrapper.

This remains a statement target because Mathlib's `eigenvalues` API reindexes
`eigenvalues₀` through `Fintype.equivOfCardEq`. -/
abbrev lambdaMaxEqLambdaMaxOrderedStatement {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  lambdaMax A hA = lambdaMaxOrdered A hA

/-- Typed target recording that the ordered endpoint wrapper is the greatest
ordered Hermitian eigenvalue. -/
abbrev lambdaMaxOrderedIsGreatestEigenvalueStatement {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  forall i : Fin (Fintype.card (Fin (n + 1))),
    hA.eigenvalues₀ i <= lambdaMaxOrdered A hA

/-- Mathlib's ordered Hermitian endpoint is greatest in the ordered list. -/
theorem lambdaMaxOrdered_is_greatest_eigenvalue {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) :
    lambdaMaxOrderedIsGreatestEigenvalueStatement A hA := by
  intro i
  simpa [lambdaMaxOrdered,
    lambdaMaxOrderedIsGreatestEigenvalueStatement] using
    hA.eigenvalues₀_antitone (Fin.zero_le i)

/-- The ordered lambda-max endpoint is a real spectral value. -/
private theorem lambdaMaxOrdered_mem_spectrum_real {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) :
    lambdaMaxOrdered A hA ∈ spectrum Real A := by
  classical
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (by simp)
  have hmem := hA.eigenvalues_mem_spectrum_real (e 0)
  simpa [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues, e] using hmem

/-- The ordered lambda-max endpoint is bounded by the deterministic L2
operator norm. -/
theorem lambdaMaxOrdered_le_deterministicOperatorNorm
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) :
    lambdaMaxOrdered A hA <= deterministicOperatorNorm A := by
  have hmem : lambdaMaxOrdered A hA ∈ spectrum Real A :=
    lambdaMaxOrdered_mem_spectrum_real A hA
  have hnorm : ‖lambdaMaxOrdered A hA‖ <= ‖A‖ :=
    spectrum.norm_le_norm_of_mem hmem
  exact (le_abs_self (lambdaMaxOrdered A hA)).trans (by
    simpa [Real.norm_eq_abs, deterministicOperatorNorm] using hnorm)

/-- Every real spectral value of a self-adjoint matrix is bounded by the
ordered endpoint. -/
private theorem spectrum_real_le_lambdaMaxOrdered {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) {x : Real}
    (hx : x ∈ spectrum Real A) :
    x <= lambdaMaxOrdered A hA := by
  classical
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  rcases hx with ⟨i, rfl⟩
  dsimp [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues]
  exact hA.eigenvalues₀_antitone (Fin.zero_le _)

/-- The ordered lambda-max endpoint commutes with nonnegative scalar
multiplication. -/
theorem lambdaMaxOrdered_smul_of_nonneg
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (theta : Real) (hTheta : 0 <= theta)
    (hA : IsSelfAdjointMatrix A) :
    lambdaMaxOrdered (theta • A) (isSelfAdjointMatrix_smul theta hA)
      = theta * lambdaMaxOrdered A hA := by
  classical
  let hThetaA : IsSelfAdjointMatrix (theta • A) :=
    isSelfAdjointMatrix_smul theta hA
  apply le_antisymm
  · have hmemTheta :
        lambdaMaxOrdered (theta • A) hThetaA ∈ spectrum Real (theta • A) :=
      lambdaMaxOrdered_mem_spectrum_real (theta • A) hThetaA
    have hspectrum :
        spectrum Real (theta • A) = theta • spectrum Real A :=
      spectrum.smul_eq_smul theta A
        (Set.nonempty_of_mem (lambdaMaxOrdered_mem_spectrum_real A hA))
    rw [hspectrum] at hmemTheta
    rcases hmemTheta with ⟨mu, hmu, hmul⟩
    rw [← hmul]
    exact mul_le_mul_of_nonneg_left
      (spectrum_real_le_lambdaMaxOrdered hA hmu) hTheta
  · have hmem :
        theta * lambdaMaxOrdered A hA ∈ spectrum Real (theta • A) := by
      have hspectrum :
          spectrum Real (theta • A) = theta • spectrum Real A :=
        spectrum.smul_eq_smul theta A
          (Set.nonempty_of_mem (lambdaMaxOrdered_mem_spectrum_real A hA))
      rw [hspectrum]
      simpa [smul_eq_mul] using
        (Set.smul_mem_smul_set
          (a := theta)
          (lambdaMaxOrdered_mem_spectrum_real A hA))
    exact spectrum_real_le_lambdaMaxOrdered hThetaA hmem

/-- For a positive semidefinite self-adjoint matrix, the ordered largest
eigenvalue is bounded by the matrix trace.

This is stated with `Matrix.trace` so it can live in `Spectral.lean` without
importing the downstream `matrixTrace` wrapper from `TraceExp.lean`. -/
theorem lambdaMaxOrdered_le_trace_of_posSemidef
    {n : Nat} {B : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hB : IsSelfAdjointMatrix B)
    (hPSD : Matrix.PosSemidef B) :
    lambdaMaxOrdered B hB <= Matrix.trace B := by
  classical
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (by simp)
  have htrace : Matrix.trace B = ∑ i, (hB.eigenvalues i : Real) :=
    hB.trace_eq_sum_eigenvalues
  have hnonneg : ∀ i : Fin (n + 1), 0 <= hB.eigenvalues i := by
    intro i
    exact hPSD.eigenvalues_nonneg i
  have hterm :
      hB.eigenvalues (e 0) <= ∑ i, hB.eigenvalues i := by
    exact Finset.single_le_sum (by
      intro j _hj
      exact hnonneg j) (Finset.mem_univ (e 0))
  simpa [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues, e, htrace] using hterm

/-- Typed target recording that the `lambdaMin` wrapper is the least
Hermitian eigenvalue. -/
abbrev lambdaMinIsLeastEigenvalueStatement {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  forall i : Fin (n + 1), lambdaMin A hA <= hA.eigenvalues i

/-- Typed target for the Rayleigh bridge from HighDimProb's explicit
unit-vector quadratic form to the `lambdaMax` wrapper.

This statement is restricted to the nonempty `Fin (n + 1)` route used by
`lambdaMax`.  The actual proof still requires connecting
`matrixQuadraticForm`/`IsUnitVector` to Mathlib's Rayleigh quotient or
Hermitian eigenvalue API. -/
abbrev matrixQuadraticFormLeLambdaMaxStatement {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  RayleighUpperBound A (lambdaMax A hA)

/-- Typed target for the Rayleigh bridge to the canonical ordered endpoint
wrapper. -/
abbrev matrixQuadraticFormLeLambdaMaxOrderedStatement {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  RayleighUpperBound A (lambdaMaxOrdered A hA)

/-! ## Endpoint-PSD helper bridge -/

/-- Named endpoint PSD premise for the lambda-max Rayleigh bridge.

This is a premise, not a theorem. The next spectral proof task is to prove
this predicate from Mathlib Hermitian eigenvalue endpoint ordering or an
equivalent Loewner/CFC route. -/
abbrev LambdaMaxPSDUpperBound {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  SpectralUpperBound A (lambdaMax A hA)

/-- Named endpoint PSD premise for the ordered lambda-max Rayleigh bridge. -/
abbrev LambdaMaxOrderedPSDUpperBound {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  SpectralUpperBound A (lambdaMaxOrdered A hA)

/-- The canonical ordered lambda-max endpoint provides the semantic spectral
upper-bound predicate. -/
theorem lambdaMaxOrdered_spectralUpperBound
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) :
    SpectralUpperBound A (lambdaMaxOrdered A hA) := by
  classical
  have hle :
      A ≤ algebraMap Real (Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
        (lambdaMaxOrdered A hA) := by
    apply le_algebraMap_of_spectrum_le
    · intro x hx
      rw [hA.spectrum_real_eq_range_eigenvalues] at hx
      rcases hx with ⟨i, rfl⟩
      dsimp [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues]
      exact hA.eigenvalues₀_antitone (Fin.zero_le _)
    · exact hA.isSelfAdjoint
  simpa [SpectralUpperBound, Algebra.algebraMap_eq_smul_one] using
    (Matrix.le_iff.mp hle)

/-- The ordered lambda-max endpoint satisfies the named provider predicate. -/
theorem lambdaMaxOrderedPSDUpperBound
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) :
    LambdaMaxOrderedPSDUpperBound A hA :=
  lambdaMaxOrdered_spectralUpperBound hA

/-- Compatibility projection from the legacy lambda-max PSD premise to the
semantic spectral upper-bound predicate. -/
theorem spectralUpperBound_of_lambdaMaxPSDUpperBound
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    {hA : IsSelfAdjointMatrix A}
    (hPSD : LambdaMaxPSDUpperBound A hA) :
    SpectralUpperBound A (lambdaMax A hA) :=
  hPSD

/-- Compatibility projection from the ordered lambda-max PSD premise to the
semantic spectral upper-bound predicate. -/
theorem spectralUpperBound_of_lambdaMaxOrderedPSDUpperBound
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    {hA : IsSelfAdjointMatrix A}
    (hPSD : LambdaMaxOrderedPSDUpperBound A hA) :
    SpectralUpperBound A (lambdaMaxOrdered A hA) :=
  hPSD

/-- Mathlib positive semidefiniteness implies nonnegativity of the
HighDimProb explicit double-sum quadratic form.

This is only a conversion lemma. It does not identify HighDimProb's
`IsPSDMatrix` with Mathlib's `Matrix.PosSemidef`. -/
theorem matrixQuadraticForm_nonneg_of_posSemidef {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : A.PosSemidef)
    (x : Fin n -> Real) :
    0 <= matrixQuadraticForm A x := by
  have h := hA.dotProduct_mulVec_nonneg x
  simpa [matrixQuadraticForm, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul, mul_assoc] using h

/-- Mathlib positive semidefiniteness gives HighDimProb's explicit PSD predicate.

This is the converse representation bridge to `posSemidef_of_isPSDMatrix`.
It does not install a global matrix order instance. -/
theorem isPSDMatrix_of_posSemidef {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : A.PosSemidef) :
    IsPSDMatrix A := by
  constructor
  · apply Matrix.IsSymm.ext
    intro i j
    have h := Matrix.IsHermitian.apply hA.isHermitian i j
    simpa using h
  · intro x
    exact matrixQuadraticForm_nonneg_of_posSemidef hA x

/-- Convert Mathlib matrix order into HighDimProb's explicit `MatrixLE`. -/
theorem matrixLE_of_mathlib_le {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Real} (hAB : A <= B) :
    MatrixLE A B := by
  exact isPSDMatrix_of_posSemidef (Matrix.le_iff.mp hAB)

/-- Convert HighDimProb's explicit `MatrixLE` into Mathlib matrix order. -/
theorem mathlib_le_of_matrixLE {n : Nat}
    {A B : Matrix (Fin n) (Fin n) Real} (hAB : MatrixLE A B) :
    A <= B :=
  Matrix.le_iff.mpr (posSemidef_of_isPSDMatrix hAB)
/-- PSD nullspace converse in HighDimProb's explicit quadratic-form vocabulary.

Formula reference: for a positive semidefinite matrix, a zero quadratic form
forces the vector into the kernel; one proof uses the PSD square root, see
https://en.wikipedia.org/wiki/Definite_matrix#Square_root .  This theorem is a
thin wrapper over Mathlib's `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`. -/
theorem matrixQuadraticForm_eq_zero_iff_mulVec_eq_zero_of_posSemidef {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : A.PosSemidef)
    (x : Fin n -> Real) :
    matrixQuadraticForm A x = 0 <-> Matrix.mulVec A x = 0 := by
  have h := hA.dotProduct_mulVec_zero_iff x
  simpa [matrixQuadraticForm, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul, mul_assoc] using h

/-- One-way PSD nullspace converse from a zero HighDimProb quadratic form. -/
theorem matrix_mulVec_eq_zero_of_posSemidef_quadraticForm_eq_zero {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : A.PosSemidef)
    {x : Fin n -> Real} (hx : matrixQuadraticForm A x = 0) :
    Matrix.mulVec A x = 0 :=
  (matrixQuadraticForm_eq_zero_iff_mulVec_eq_zero_of_posSemidef hA x).mp hx

/-- Explicit-PSD version of the PSD nullspace iff.

Formula reference: the statement is the usual PSD nullspace converse for
symmetric positive semidefinite real matrices; see
https://math.stackexchange.com/questions/3918031/prove-that-if-xtax-0-rightarrow-ax-0 .
-/
theorem matrixQuadraticForm_eq_zero_iff_mulVec_eq_zero_of_isPSDMatrix {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsPSDMatrix A)
    (x : Fin n -> Real) :
    matrixQuadraticForm A x = 0 <-> Matrix.mulVec A x = 0 :=
  matrixQuadraticForm_eq_zero_iff_mulVec_eq_zero_of_posSemidef
    (posSemidef_of_isPSDMatrix hA) x

/-- One-way explicit-PSD nullspace converse from a zero HighDimProb quadratic
form. -/
theorem matrix_mulVec_eq_zero_of_isPSDMatrix_quadraticForm_eq_zero {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsPSDMatrix A)
    {x : Fin n -> Real} (hx : matrixQuadraticForm A x = 0) :
    Matrix.mulVec A x = 0 :=
  (matrixQuadraticForm_eq_zero_iff_mulVec_eq_zero_of_isPSDMatrix hA x).mp hx

/-! ## Rank-one kernel/nullspace bridges -/

/-- Finite sum of deterministic rank-one outer-product matrices. -/
def rankOneMatrixSum {I : Type*} [Fintype I] {n : Nat}
    (v : I -> Fin n -> Real) : Matrix (Fin n) (Fin n) Real :=
  Finset.univ.sum fun a : I => rankOneMatrix (v a)

/-- The quadratic form of a rank-one outer product is the squared feature
inner product. -/
theorem rankOneMatrix_quadraticForm_eq_inner_sq {n : Nat}
    (v x : Fin n -> Real) :
    matrixQuadraticForm (rankOneMatrix v) x =
      (Finset.univ.sum fun i : Fin n => v i * x i) ^ 2 := by
  have hquad :
      matrixQuadraticForm (rankOneMatrix v) x =
        (Finset.univ.sum fun i : Fin n => x i * v i) ^ 2 := by
    simp only [matrixQuadraticForm_apply, rankOneMatrix_apply]
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hquad]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A direction is in the kernel of a rank-one matrix exactly when it is
orthogonal to the generating vector. -/
theorem rankOneMatrix_mulVec_eq_zero_iff_inner_eq_zero {n : Nat}
    (v x : Fin n -> Real) :
    Matrix.mulVec (rankOneMatrix v) x = 0 <->
      (Finset.univ.sum fun i : Fin n => v i * x i) = 0 := by
  constructor
  · intro h
    have hquad :
        matrixQuadraticForm (rankOneMatrix v) x = 0 :=
      (matrixQuadraticForm_eq_zero_iff_mulVec_eq_zero_of_isPSDMatrix
        (isPSDMatrix_rankOneMatrix v) x).mpr h
    rw [rankOneMatrix_quadraticForm_eq_inner_sq] at hquad
    exact sq_eq_zero_iff.mp hquad
  · intro h
    ext i
    calc
      Matrix.mulVec (rankOneMatrix v) x i
          = v i * (Finset.univ.sum fun j : Fin n => v j * x j) := by
            simp [Matrix.mulVec, dotProduct, rankOneMatrix, Finset.mul_sum,
              mul_assoc]
      _ = 0 := by
            rw [h, mul_zero]

/-- A vector killed by every rank-one summand is killed by their finite sum. -/
theorem rankOneSum_mulVec_eq_zero_of_forall_inner_eq_zero {I : Type*} [Fintype I]
    {n : Nat} (v : I -> Fin n -> Real) (x : Fin n -> Real)
    (h : forall a : I,
      (Finset.univ.sum fun j : Fin n => v a j * x j) = 0) :
    Matrix.mulVec (rankOneMatrixSum v) x = 0 := by
  ext i
  calc
    Matrix.mulVec (rankOneMatrixSum v) x i
        = Finset.univ.sum fun j : Fin n =>
            (Finset.univ.sum fun a : I => v a i * v a j) * x j := by
          simp [rankOneMatrixSum, Matrix.mulVec, Matrix.sum_apply,
            dotProduct, rankOneMatrix]
    _ = Finset.univ.sum fun j : Fin n =>
          Finset.univ.sum fun a : I => (v a i * v a j) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = Finset.univ.sum fun a : I =>
          Finset.univ.sum fun j : Fin n => (v a i * v a j) * x j := by
          rw [Finset.sum_comm]
    _ = Finset.univ.sum fun a : I =>
          Matrix.mulVec (rankOneMatrix (v a)) x i := by
          apply Finset.sum_congr rfl
          intro a _
          simp [Matrix.mulVec, dotProduct, rankOneMatrix, mul_assoc]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          have ha :
              Matrix.mulVec (rankOneMatrix (v a)) x = 0 :=
            (rankOneMatrix_mulVec_eq_zero_iff_inner_eq_zero (v a) x).mpr (h a)
          simp [ha]

/-- Scalar-matrix quadratic form over an explicit unit vector.

This is the small algebraic bridge needed to turn a Loewner-order upper bound
`A <= lambdaMax A * I` into HighDimProb's explicit Rayleigh bound. -/
theorem matrixQuadraticForm_smul_one_of_isUnitVector {n : Nat}
    (c : Real) {x : Fin n -> Real} (hx : IsUnitVector x) :
    matrixQuadraticForm (c • (1 : Matrix (Fin n) (Fin n) Real)) x = c := by
  calc
    matrixQuadraticForm (c • (1 : Matrix (Fin n) (Fin n) Real)) x
        = Finset.univ.sum fun i : Fin n => x i * (c * x i) := by
          simp only [matrixQuadraticForm_apply, Matrix.smul_apply, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_eq_single i]
          · simp [mul_assoc]
          · intro j _ hji
            simp [hji.symm]
          · intro hi
            simp at hi
    _ = c * Finset.univ.sum fun i : Fin n => x i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = c := by
          rw [show (Finset.univ.sum fun i : Fin n => x i ^ 2) = 1 by
            simpa [IsUnitVector, vectorSqNorm] using hx]
          ring

/-- A semantic spectral upper bound implies the corresponding explicit
HighDimProb Rayleigh upper bound. -/
theorem rayleighUpperBound_of_spectralUpperBound
    {n : Nat} {A : Matrix (Fin n) (Fin n) Real} {L : Real}
    (hUpper : SpectralUpperBound A L) :
    RayleighUpperBound A L := by
  intro x hx
  have hnonneg := matrixQuadraticForm_nonneg_of_posSemidef hUpper x
  rw [matrixQuadraticForm_sub] at hnonneg
  rw [matrixQuadraticForm_smul_one_of_isUnitVector L hx] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Direct Rayleigh bridge supplied by the ordered lambda-max provider theorem. -/
theorem lambdaMaxOrdered_rayleighUpperBound
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) :
    matrixQuadraticFormLeLambdaMaxOrderedStatement A hA :=
  rayleighUpperBound_of_spectralUpperBound
    (lambdaMaxOrdered_spectralUpperBound hA)

/-- The absolute explicit quadratic form of a unit vector is bounded by the
deterministic L2 operator norm. -/
theorem abs_matrixQuadraticForm_le_deterministicOperatorNorm {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) {x : Fin n -> Real}
    (hx : IsUnitVector x) :
    abs (matrixQuadraticForm A x) <= deterministicOperatorNorm A := by
  have hxnorm :
      norm (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) = 1 :=
    norm_toLp_eq_one_of_isUnitVector hx
  have hmul :=
    Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x : EuclideanSpace Real (Fin n))
  have hmul' :
      norm ((EuclideanSpace.equiv (Fin n) Real).symm (Matrix.mulVec A x) :
        EuclideanSpace Real (Fin n)) <= norm A := by
    simpa [hxnorm] using hmul
  have hinner :
      matrixQuadraticForm A x =
        inner Real
          ((EuclideanSpace.equiv (Fin n) Real).symm (Matrix.mulVec A x) :
            EuclideanSpace Real (Fin n))
          (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) := by
    simp only [matrixQuadraticForm_apply, PiLp.continuousLinearEquiv_symm_apply,
      Matrix.mulVec, dotProduct, inner, mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    rw [<- Finset.mul_sum]
    simp only [RCLike.re_to_real, TrivialStar.star_trivial]
  calc
    abs (matrixQuadraticForm A x)
        = abs (inner Real
          ((EuclideanSpace.equiv (Fin n) Real).symm (Matrix.mulVec A x) :
            EuclideanSpace Real (Fin n))
          (WithLp.toLp 2 x : EuclideanSpace Real (Fin n))) := by rw [hinner]
    _ <= norm ((EuclideanSpace.equiv (Fin n) Real).symm (Matrix.mulVec A x) :
          EuclideanSpace Real (Fin n)) *
        norm (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) :=
      abs_real_inner_le_norm _ _
    _ = norm ((EuclideanSpace.equiv (Fin n) Real).symm (Matrix.mulVec A x) :
          EuclideanSpace Real (Fin n)) * 1 := by rw [hxnorm]
    _ <= norm A * 1 := by
      exact mul_le_mul_of_nonneg_right hmul' zero_le_one
    _ = deterministicOperatorNorm A := by
      simp [deterministicOperatorNorm]

/-- The explicit quadratic form of a unit vector is bounded above by the
deterministic L2 operator norm. -/
theorem matrixQuadraticForm_le_deterministicOperatorNorm {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) {x : Fin n -> Real}
    (hx : IsUnitVector x) :
    matrixQuadraticForm A x <= deterministicOperatorNorm A :=
  (le_abs_self (matrixQuadraticForm A x)).trans
    (abs_matrixQuadraticForm_le_deterministicOperatorNorm A hx)

/-- The ordered lambda-max endpoint is attained by an explicit unit
eigenvector in HighDimProb's quadratic-form convention. -/
private theorem exists_unitVector_matrixQuadraticForm_eq_lambdaMaxOrdered
    {n : Nat} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) :
    exists x : Fin (n + 1) -> Real,
      IsUnitVector x /\ matrixQuadraticForm A x = lambdaMaxOrdered A hA := by
  classical
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (by simp)
  let idx : Fin (n + 1) := e 0
  let x : Fin (n + 1) -> Real := fun i => hA.eigenvectorBasis idx i
  refine ⟨x, ?_, ?_⟩
  · apply isUnitVector_of_norm_toLp_eq_one
    simp [x, hA.eigenvectorBasis.norm_eq_one idx]
  · have hquad :
        matrixQuadraticForm A x = hA.eigenvalues idx := by
      simpa [x, matrixQuadraticForm, dotProduct, Matrix.mulVec,
        Finset.mul_sum, Finset.sum_mul, mul_assoc] using
        (hA.eigenvalues_eq idx).symm
    have hidx : hA.eigenvalues idx = lambdaMaxOrdered A hA := by
      simp [lambdaMaxOrdered, Matrix.IsHermitian.eigenvalues, idx, e]
    exact hquad.trans hidx

/-- A real self-adjoint nonempty matrix has a unit vector whose absolute
quadratic form attains the deterministic L2 operator norm. -/
theorem exists_unitVector_abs_matrixQuadraticForm_eq_deterministicOperatorNorm
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    (hA : IsSelfAdjointMatrix A) :
    exists x : Fin (n + 1) -> Real,
      IsUnitVector x /\
        abs (matrixQuadraticForm A x) = deterministicOperatorNorm A := by
  classical
  have hconj_norm
      (U : Matrix.unitaryGroup (Fin (n + 1)) Real)
      (B : Matrix (Fin (n + 1)) (Fin (n + 1)) Real) :
      norm (Unitary.conjStarAlgAut Real _ U B) = norm B := by
    rw [Unitary.conjStarAlgAut_apply]
    calc
      norm ((U : Matrix (Fin (n + 1)) (Fin (n + 1)) Real) * B *
          star (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)) =
          norm ((U : Matrix (Fin (n + 1)) (Fin (n + 1)) Real) * B) := by
        exact CStarRing.norm_mul_coe_unitary
          ((U : Matrix (Fin (n + 1)) (Fin (n + 1)) Real) * B) (star U)
      _ = norm B := by
        exact CStarRing.norm_coe_unitary_mul U B
  have hnormA : norm A = norm (hA.eigenvalues : Fin (n + 1) -> Real) := by
    calc
      norm A =
          norm (Unitary.conjStarAlgAut Real _ hA.eigenvectorUnitary
            (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))) := by
        exact congrArg norm hA.spectral_theorem
      _ = norm (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Real) := hconj_norm _ _
      _ = norm (Matrix.diagonal hA.eigenvalues :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Real) := by
          simp
      _ = norm (hA.eigenvalues : Fin (n + 1) -> Real) := by
          exact
            Matrix.l2_opNorm_diagonal
              (n := Fin (n + 1)) (𝕜 := Real) hA.eigenvalues
  obtain ⟨idx, _, hidx_max⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin (n + 1)))
      (fun i => norm (hA.eigenvalues i))
      Finset.univ_nonempty
  have hidx_norm :
      norm (hA.eigenvalues idx) =
        norm (hA.eigenvalues : Fin (n + 1) -> Real) := by
    refine le_antisymm (norm_le_pi_norm _ idx) ?_
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg (hA.eigenvalues idx))).2
      (fun i => hidx_max i (Finset.mem_univ i))
  let x : Fin (n + 1) -> Real := fun i => hA.eigenvectorBasis idx i
  refine ⟨x, ?_, ?_⟩
  · apply isUnitVector_of_norm_toLp_eq_one
    simp [x, hA.eigenvectorBasis.norm_eq_one idx]
  · have hquad :
        matrixQuadraticForm A x = hA.eigenvalues idx := by
      simpa [x, matrixQuadraticForm, dotProduct, Matrix.mulVec,
        Finset.mul_sum, Finset.sum_mul, mul_assoc] using
        (hA.eigenvalues_eq idx).symm
    calc
      abs (matrixQuadraticForm A x) =
          norm (hA.eigenvalues idx) := by
        rw [hquad, Real.norm_eq_abs]
      _ = norm (hA.eigenvalues : Fin (n + 1) -> Real) := hidx_norm
      _ = deterministicOperatorNorm A := by
        simpa [deterministicOperatorNorm] using hnormA.symm

/-- Conditional Rayleigh conversion from a Mathlib Loewner-style premise.

The hard spectral fact is the premise
`((lambdaMax A hA) • 1 - A).PosSemidef`; proving that premise from the
Hermitian eigenvalue order remains a separate bridge target. -/
theorem matrixQuadraticForm_le_lambdaMax_of_lambdaMax_sub_posSemidef
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    {hA : IsSelfAdjointMatrix A}
    (hPSD :
      (((lambdaMax A hA) •
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)) - A).PosSemidef) :
    matrixQuadraticFormLeLambdaMaxStatement A hA := by
  exact rayleighUpperBound_of_spectralUpperBound hPSD

/-- Conditional Rayleigh conversion from the named endpoint PSD premise. -/
theorem matrixQuadraticForm_le_lambdaMax_of_lambdaMaxPSDUpperBound
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    {hA : IsSelfAdjointMatrix A}
    (hPSD : LambdaMaxPSDUpperBound A hA) :
    matrixQuadraticFormLeLambdaMaxStatement A hA := by
  exact matrixQuadraticForm_le_lambdaMax_of_lambdaMax_sub_posSemidef hPSD

/-- Conditional Rayleigh conversion from the named ordered endpoint PSD
premise. -/
theorem matrixQuadraticForm_le_lambdaMaxOrdered_of_lambdaMaxOrderedPSDUpperBound
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    {hA : IsSelfAdjointMatrix A}
    (hPSD : LambdaMaxOrderedPSDUpperBound A hA) :
    matrixQuadraticFormLeLambdaMaxOrderedStatement A hA := by
  exact rayleighUpperBound_of_spectralUpperBound hPSD

/-- Conditional conversion from a proved Rayleigh bridge and a lambda-max
threshold into the explicit quadratic-form upper-bound predicate. -/
theorem quadraticFormUpperBound_of_lambdaMax_le_of_matrixQuadraticForm_le_lambdaMax
    {n : Nat} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real}
    {hA : IsSelfAdjointMatrix A} {t : Real}
    (hRayleigh : matrixQuadraticFormLeLambdaMaxStatement A hA)
    (ht : lambdaMax A hA <= t) :
    QuadraticFormUpperBound A t := by
  intro x hx
  exact le_trans (hRayleigh x hx) ht

/-! ## Tail event vocabulary -/

/-- Largest-eigenvalue upper-tail event for the nonempty `Fin (n + 1)`
lambda-max wrapper.

The self-adjointness proof is an explicit parameter so the event does not hide
the dependence of `lambdaMax` on a Hermitian witness. -/
def lambdaMaxUpperTailEvent {Omega : Type*} {n : Nat}
    (A : RandomMatrix Omega (n + 1) (n + 1))
    (hA : forall omega, IsSelfAdjointMatrix (A omega)) (t : Real) :
    Set Omega :=
  matrixUpperBoundTailEvent A (fun omega => lambdaMax (A omega) (hA omega)) t

/-- Largest-eigenvalue upper-tail event for the canonical ordered endpoint
wrapper. -/
def lambdaMaxOrderedUpperTailEvent {Omega : Type*}
    {n : Nat} (A : RandomMatrix Omega (n + 1) (n + 1))
    (hA : forall omega, IsSelfAdjointMatrix (A omega)) (t : Real) :
    Set Omega :=
  matrixUpperBoundTailEvent A
    (fun omega => lambdaMaxOrdered (A omega) (hA omega)) t

/-- The legacy lambda-max upper-tail event is a concrete provider instance of
the generic matrix upper-bound tail event. -/
theorem lambdaMaxUpperTailEvent_eq_matrixUpperBoundTailEvent
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega (n + 1) (n + 1))
    (hA : forall omega, IsSelfAdjointMatrix (A omega)) (t : Real) :
    lambdaMaxUpperTailEvent A hA t =
      matrixUpperBoundTailEvent A
        (fun omega => lambdaMax (A omega) (hA omega)) t :=
  rfl

/-- The ordered lambda-max upper-tail event is a concrete provider instance of
the generic matrix upper-bound tail event. -/
theorem lambdaMaxOrderedUpperTailEvent_eq_matrixUpperBoundTailEvent
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega (n + 1) (n + 1))
    (hA : forall omega, IsSelfAdjointMatrix (A omega)) (t : Real) :
    lambdaMaxOrderedUpperTailEvent A hA t =
      matrixUpperBoundTailEvent A
        (fun omega => lambdaMaxOrdered (A omega) (hA omega)) t :=
  rfl

/-! ## Zero-dimensional cleanup for explicit unit-sphere events -/

/-- There are no explicit HighDimProb unit vectors in dimension zero. -/
theorem not_isUnitVector_fin_zero (x : Fin 0 -> Real) :
    ¬ IsUnitVector x := by
  intro hx
  have hzero : vectorSqNorm x = 0 := by
    simp [vectorSqNorm]
  rw [IsUnitVector, hzero] at hx
  norm_num at hx

/-- The explicit unit sphere is empty in dimension zero. -/
theorem unitSphere_empty_of_zero_dim :
    unitSphere 0 = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim ((not_isUnitVector_fin_zero x) hx)
  · intro hEmpty
    cases hEmpty

/-- Event that some unit vector has quadratic form at least `t`. -/
def quadraticFormUpperTailEvent {Omega : Type*}
    {n : Nat} (A : RandomMatrix Omega n n) (t : Real) : Set Omega :=
  {omega | exists x : Fin n -> Real,
    IsUnitVector x /\ t <= matrixQuadraticForm (A omega) x}

/-- Generic event-level bridge from pointwise Rayleigh upper bounds to a scalar
upper-tail provider event. -/
theorem quadraticFormUpperTailEvent_subset_scalarUpperTailEvent_of_rayleighUpperBound
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega n n) (L : Omega -> Real) (t : Real)
    (hRayleigh : forall omega, RayleighUpperBound (A omega) (L omega)) :
    quadraticFormUpperTailEvent A t <= scalarUpperTailEvent L t := by
  intro omega hTail
  rcases hTail with ⟨x, hx, ht⟩
  exact le_trans ht (hRayleigh omega x hx)

/-- Generic event-level bridge from pointwise Rayleigh upper bounds to a matrix
upper-bound provider event. -/
theorem quadraticFormUpperTailEvent_subset_matrixUpperBoundTailEvent_of_rayleighUpperBound
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega n n) (L : Omega -> Real) (t : Real)
    (hRayleigh : forall omega, RayleighUpperBound (A omega) (L omega)) :
    quadraticFormUpperTailEvent A t <= matrixUpperBoundTailEvent A L t := by
  exact
    quadraticFormUpperTailEvent_subset_scalarUpperTailEvent_of_rayleighUpperBound
      A L t hRayleigh

/-- Generic event-level bridge from pointwise semantic spectral upper bounds to
a matrix upper-bound provider event. -/
theorem quadraticFormUpperTailEvent_subset_matrixUpperBoundTailEvent_of_spectralUpperBound
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega n n) (L : Omega -> Real) (t : Real)
    (hUpper : forall omega, SpectralUpperBound (A omega) (L omega)) :
    quadraticFormUpperTailEvent A t <= matrixUpperBoundTailEvent A L t := by
  exact
    quadraticFormUpperTailEvent_subset_matrixUpperBoundTailEvent_of_rayleighUpperBound
      A L t (fun omega => rayleighUpperBound_of_spectralUpperBound (hUpper omega))

/-- Ordered lambda-max upper-tail events reduce to the existing explicit
quadratic-form upper-tail event by taking an eigenvector attaining the ordered
endpoint. -/
theorem lambdaMaxOrderedUpperTailEvent_subset_quadraticFormUpperTailEvent
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega (n + 1) (n + 1))
    (hA : forall omega, IsSelfAdjointMatrix (A omega)) (t : Real) :
    lambdaMaxOrderedUpperTailEvent A hA t <=
      quadraticFormUpperTailEvent A t := by
  intro omega hTail
  change t <= lambdaMaxOrdered (A omega) (hA omega) at hTail
  rcases exists_unitVector_matrixQuadraticForm_eq_lambdaMaxOrdered
      (A omega) (hA omega) with ⟨x, hx, hquad⟩
  exact ⟨x, hx, hquad.symm ▸ hTail⟩

/-- Conditional event-level Rayleigh bridge from the explicit unit-sphere
quadratic-form upper tail to the lambda-max upper tail. -/
theorem quadraticFormTailEvent_subset_lambdaMaxTailEvent_of_quadraticForm_le_lambdaMax
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega (n + 1) (n + 1)) (t : Real)
    (hA : forall omega, IsSelfAdjointMatrix (A omega))
    (hRayleigh :
      forall omega, matrixQuadraticFormLeLambdaMaxStatement (A omega) (hA omega)) :
    quadraticFormUpperTailEvent A t <= lambdaMaxUpperTailEvent A hA t := by
  exact
    quadraticFormUpperTailEvent_subset_matrixUpperBoundTailEvent_of_rayleighUpperBound
      A (fun omega => lambdaMax (A omega) (hA omega)) t hRayleigh

/-- Conditional event-level Rayleigh bridge to the ordered lambda-max upper
tail. -/
theorem quadraticFormTailEvent_subset_lambdaMaxOrderedTailEvent_of_quadraticForm_le_lambdaMaxOrdered
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega (n + 1) (n + 1)) (t : Real)
    (hA : forall omega, IsSelfAdjointMatrix (A omega))
    (hRayleigh :
      forall omega,
        matrixQuadraticFormLeLambdaMaxOrderedStatement (A omega) (hA omega)) :
    quadraticFormUpperTailEvent A t <= lambdaMaxOrderedUpperTailEvent A hA t := by
  exact
    quadraticFormUpperTailEvent_subset_matrixUpperBoundTailEvent_of_rayleighUpperBound
      A (fun omega => lambdaMaxOrdered (A omega) (hA omega)) t hRayleigh

/-- The quadratic-form upper-tail event is empty in dimension zero because the
explicit unit sphere is empty. -/
theorem quadraticFormUpperTailEvent_empty_of_zero_dim {Omega : Type*}
    [MeasurableSpace Omega] (A : RandomMatrix Omega 0 0) (t : Real) :
    quadraticFormUpperTailEvent A t = ∅ := by
  ext omega
  constructor
  · intro hTail
    rcases hTail with ⟨x, hx, _⟩
    exact False.elim ((not_isUnitVector_fin_zero x) hx)
  · intro hEmpty
    cases hEmpty

/-- Event that some unit vector has quadratic form at most `t`. -/
def quadraticFormLowerTailEvent {Omega : Type*}
    {n : Nat} (A : RandomMatrix Omega n n) (t : Real) : Set Omega :=
  {omega | exists x : Fin n -> Real,
    IsUnitVector x /\ matrixQuadraticForm (A omega) x <= t}

/-- A reflected lower quadratic-form tail is an upper tail for the pointwise
negated matrix. -/
theorem quadraticFormLowerTailEvent_subset_quadraticFormUpperTailEvent_neg
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega n n) (t : Real) :
    quadraticFormLowerTailEvent A (-t) ⊆
      quadraticFormUpperTailEvent (fun omega => -(A omega)) t := by
  intro omega hTail
  rcases hTail with ⟨x, hx, hquad⟩
  refine ⟨x, hx, ?_⟩
  have hneg :
      matrixQuadraticForm (-(A omega)) x =
        -matrixQuadraticForm (A omega) x := by
    rw [show -(A omega) = (-1 : Real) • A omega by simp,
      matrixQuadraticForm_smul]
    ring
  change t <= matrixQuadraticForm (-(A omega)) x
  rw [hneg]
  simpa using neg_le_neg hquad

/-- Operator-norm tail event for square random matrices.

Future self-adjoint concentration statements should pair this event with a
self-adjointness assumption on `A`; the event itself is just the operator-norm
tail set. -/
def SelfAdjointOperatorNormTailEvent {Omega : Type*}
    {n : Nat} (A : RandomMatrix Omega n n) (t : Real) : Set Omega :=
  {omega | t <= operatorNorm A omega}

/-- In dimension zero, a positive-threshold self-adjoint operator-norm tail is
empty.

The positivity assumption is essential: at threshold `0`, the operator-norm
tail is nonempty on any nonempty sample space because matrix norms are
nonnegative, while the explicit unit-sphere quadratic-form events are empty. -/
theorem selfAdjointOperatorNormTailEvent_empty_of_zero_dim_of_pos
    {Omega : Type*} [MeasurableSpace Omega]
    (A : RandomMatrix Omega 0 0) {t : Real} (ht : 0 < t) :
    SelfAdjointOperatorNormTailEvent A t = ∅ := by
  ext omega
  constructor
  · intro hTail
    have hA_zero : A omega = 0 := by
      ext i j
      exact Fin.elim0 i
    have hnorm : norm (A omega) = 0 := by
      simp [hA_zero]
    have ht_zero : t <= 0 := by
      simpa [SelfAdjointOperatorNormTailEvent, operatorNorm, hnorm] using hTail
    linarith
  · intro hEmpty
    cases hEmpty

/-- Lowercase compatibility alias for the self-adjoint operator-norm tail
event vocabulary. -/
abbrev selfAdjointOperatorNormTailEvent {Omega : Type*}
    {n : Nat} (A : RandomMatrix Omega n n) (t : Real) : Set Omega :=
  SelfAdjointOperatorNormTailEvent A t

/-- Two-sided quadratic-form tail event over the explicit unit sphere.

This is the proof-ready event that should receive a future self-adjoint
operator-norm tail by the Rayleigh/eigenvalue bridge. -/
def twoSidedQuadraticFormTailEvent {Omega : Type*}
    {n : Nat} (A : RandomMatrix Omega n n) (t : Real) : Set Omega :=
  quadraticFormUpperTailEvent A t ∪ quadraticFormLowerTailEvent A (-t)

/-- The upper quadratic-form tail is one side of the two-sided event. -/
theorem quadraticFormUpperTailEvent_subset_twoSidedQuadraticFormTailEvent
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega n n) (t : Real) :
    quadraticFormUpperTailEvent A t ⊆ twoSidedQuadraticFormTailEvent A t := by
  intro omega h
  exact Or.inl h

/-- The reflected lower quadratic-form tail is one side of the two-sided
event. -/
theorem quadraticFormLowerTailEvent_subset_twoSidedQuadraticFormTailEvent
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega n n) (t : Real) :
    quadraticFormLowerTailEvent A (-t) ⊆ twoSidedQuadraticFormTailEvent A t := by
  intro omega h
  exact Or.inr h

/-- Typed target for the future self-adjoint operator-norm tail reduction.

The proof is blocked until HighDimProb connects Mathlib's self-adjoint
spectral/Rayleigh theorem to the explicit finite-dimensional quadratic form
used by `IsUnitVector`. -/
abbrev selfAdjointOperatorNormTailViaQuadraticFormStatement
    {Omega : Type*} {n : Nat}
    (A : RandomMatrix Omega n n) (t : Real) : Prop :=
  (forall omega, IsSelfAdjointMatrix (A omega)) ->
    0 <= t ->
      SelfAdjointOperatorNormTailEvent A t ⊆ twoSidedQuadraticFormTailEvent A t

/-- Nonempty self-adjoint operator-norm tail events reduce to the explicit
two-sided quadratic-form tail event.

The proof uses the deterministic nonempty witness lemma: at every sample, a
unit vector attains the L2 operator norm as the absolute value of the
quadratic form. Splitting on the sign of that quadratic form puts the sample
in the upper or lower quadratic-form tail. -/
theorem selfAdjointOperatorNormTailViaQuadraticFormStatement_nonempty
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega (n + 1) (n + 1)) (t : Real) :
    selfAdjointOperatorNormTailViaQuadraticFormStatement A t := by
  intro hA _ht omega hTail
  rcases exists_unitVector_abs_matrixQuadraticForm_eq_deterministicOperatorNorm
      (hA omega) with ⟨x, hx, hnorm⟩
  have htNorm : t <= deterministicOperatorNorm (A omega) := by
    simpa [SelfAdjointOperatorNormTailEvent, operatorNorm,
      deterministicOperatorNorm] using hTail
  by_cases hq_nonneg : 0 <= matrixQuadraticForm (A omega) x
  · exact Or.inl ⟨x, hx, by
      calc
        t <= deterministicOperatorNorm (A omega) := htNorm
        _ = abs (matrixQuadraticForm (A omega) x) := hnorm.symm
        _ = matrixQuadraticForm (A omega) x := abs_of_nonneg hq_nonneg⟩
  · have hq_nonpos : matrixQuadraticForm (A omega) x <= 0 :=
      le_of_not_ge hq_nonneg
    exact Or.inr ⟨x, hx, by
      have ht_abs :
          t <= abs (matrixQuadraticForm (A omega) x) := by
        exact htNorm.trans_eq hnorm.symm
      have ht_neg :
          t <= -matrixQuadraticForm (A omega) x := by
        calc
          t <= abs (matrixQuadraticForm (A omega) x) := ht_abs
          _ = -matrixQuadraticForm (A omega) x := abs_of_nonpos hq_nonpos
      linarith⟩

/-- Positive-threshold arbitrary-dimensional self-adjoint operator-norm tail
events reduce to the explicit two-sided quadratic-form tail event.

The proof keeps the zero-dimensional endpoint explicit: positive thresholds make
the operator-norm tail empty in dimension zero, while successor dimensions reuse
the nonempty spectral bridge. -/
theorem selfAdjointOperatorNormTailViaQuadraticFormStatement_of_pos
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (A : RandomMatrix Omega n n) {t : Real} (ht : 0 < t) :
    selfAdjointOperatorNormTailViaQuadraticFormStatement A t := by
  cases n with
  | zero =>
      intro _hA _ht omega hTail
      have hEmpty :
          SelfAdjointOperatorNormTailEvent A t = ∅ :=
        selfAdjointOperatorNormTailEvent_empty_of_zero_dim_of_pos A ht
      rw [hEmpty] at hTail
      cases hTail
  | succ n =>
      exact selfAdjointOperatorNormTailViaQuadraticFormStatement_nonempty A t

/-- Typed target for the future Rayleigh quotient bridge between Mathlib
Hermitian eigenvalues and HighDimProb's explicit unit-sphere quadratic form. -/
abbrev lambdaMaxLeIffQuadraticFormLeStatement {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) (t : Real) : Prop :=
  lambdaMax A hA <= t <-> QuadraticFormUpperBound A t

/-- Typed target for relating the self-adjoint operator norm to the largest
absolute endpoint eigenvalue. -/
abbrev operatorNormEqMaxAbsLambdaStatement {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hA : IsSelfAdjointMatrix A) : Prop :=
  deterministicOperatorNorm A = max (abs (lambdaMax A hA)) (abs (lambdaMin A hA))

end

end HighDimProb
