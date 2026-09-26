/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.ConcreteLocalizedTwoBlockSpecialFibre
public import LeanPool.Stafford38.Stafford38.Characteristic.ArtinianAdaptedBasisExistence
public import LeanPool.Stafford38.Stafford38.Characteristic.ArtinianEquation33TraceProducer


/-!
# Source matrices for the concrete equation-(3.3) bridge

This file carries out the source-level matrix algebra that precedes the trace
argument in Singh--Kumar, Proposition 3.2.  It deliberately keeps the
deformation ring noncommutative and preserves the written left-factor
orientation of the central parameter.

For strict lifted zeroth-order matrices `A` and `B`, it constructs the three
strict parameter cofactors `X`, `Y`, and `Omega` in

`[x,B] = cX`, `[y,A] = cY`, and `[B,A] = cOmega`.

For arbitrary first-order matrices `Gamma` and `Theta`, it also constructs
literal cofactors for the traces of `[Theta,A]` and `[B,Gamma]`.  Hence the
matrix represented by equation (3.3) has zero trace after parameter and
coefficient-field reduction.  The concrete localized two-block
specialization is packaged as the required principal parameter reduction.

The file does not identify this reduced matrix with the operator induced by
the bracket cofactor `z` on the concrete localized module.  That is the first
remaining source-specific action identity; its exact signature is recorded at
the end, without claiming the final operator trace.
-/

@[expose] public section

namespace Stafford38.Characteristic.ConcreteEquation33SourceMatrices

open Matrix
open Stafford38.Characteristic
open Stafford38.Characteristic.ArtinianAdaptedBasisExistence
open Stafford38.Characteristic.ArtinianAdaptedBasisTraceAdapter
open Stafford38.Characteristic.ArtinianEquation33TraceProducer
open Stafford38.Characteristic.ConcreteLocalizedTwoBlockSpecialFibre
open Stafford38.Characteristic.LocalizedHighPowerTwoBlockVanishing
open Stafford38.Characteristic.LocalizedTwoBlockQuotient
open Stafford38.Characteristic.RightReesArtinianAdapter
open Stafford38.Characteristic.SquareZeroLocalizedExactness
open Stafford38.Characteristic.SquareZeroLocalizedRing
open Stafford38.CharacteristicConcreteSquareZeroTraceData
open Stafford38.CharacteristicOrderReesTwoJet
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

section PrincipalReduction

variable {B Abar : Type u} [Ring B] [CommRing Abar]

/-- A surjective reduction with an exact written-order left-principal kernel.
This is the elementwise form supplied by the concrete localized Rees
specialization. -/
structure LeftPrincipalParameterReduction where
  /-- The central parameter whose multiples form the kernel of reduction. -/
  parameter : B
  /-- The surjective ring map reducing the source algebra modulo the central parameter. -/
  modParameter : B →+* Abar
  surjective : Function.Surjective modParameter
  parameter_comm : ∀ z : B, parameter * z = z * parameter
  kernel_left : ∀ z : B,
    modParameter z = 0 ↔ ∃ w : B, parameter * w = z

/-- The source's ideal-valued reduction follows from the stronger explicit
left-principal kernel, using centrality only to match Mathlib's left-ideal
generator convention. -/
def LeftPrincipalParameterReduction.toParameterIdealReduction
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar)) :
    ParameterIdealReduction B Abar where
  parameter := S.parameter
  modParameter := S.modParameter
  ker_modParameter := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw⟩ := (S.kernel_left z).1 hz
      rw [Ideal.mem_span_singleton']
      exact ⟨w, (S.parameter_comm w).symm.trans hw⟩
    · intro hz
      rw [Ideal.mem_span_singleton'] at hz
      obtain ⟨w, rfl⟩ := hz
      rw [← S.parameter_comm w]
      exact (S.kernel_left (S.parameter * w)).2 ⟨w, rfl⟩

/-- A zero-preserving choice of a lift through a surjective reduction. -/
def zeroPreservingLift
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (z : Abar) : B := by
  classical
  exact if hz : z = 0 then 0 else Classical.choose (S.surjective z)

@[simp]
theorem modParameter_zeroPreservingLift
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (z : Abar) :
    S.modParameter (zeroPreservingLift S z) = z := by
  classical
  by_cases hz : z = 0
  · simp [zeroPreservingLift, hz]
  · simpa [zeroPreservingLift, hz] using Classical.choose_spec (S.surjective z)

@[simp]
theorem zeroPreservingLift_zero
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar)) :
    zeroPreservingLift S 0 = 0 := by
  classical
  simp [zeroPreservingLift]

/-- A zero-preserving written-order parameter cofactor. -/
def principalCofactor
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (z : B) : B := by
  classical
  exact if hz : z = 0 then 0
    else if hker : S.modParameter z = 0 then
      Classical.choose ((S.kernel_left z).1 hker)
    else 0

theorem parameter_mul_principalCofactor
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    {z : B} (hz : S.modParameter z = 0) :
    S.parameter * principalCofactor S z = z := by
  classical
  by_cases hzero : z = 0
  · simp [principalCofactor, hzero]
  · simp only [principalCofactor, hzero, hz, ↓reduceDIte]
    exact Classical.choose_spec ((S.kernel_left z).1 hz)

@[simp]
theorem principalCofactor_zero
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar)) :
    principalCofactor S 0 = 0 := by
  classical
  simp [principalCofactor]

end PrincipalReduction

section MatrixAlgebra

variable {B Abar K : Type u}
variable [Ring B] [CommRing Abar] [Field K]
variable {n : ℕ}

/-- Entrywise scalar commutator, in the order used in equation (3.3). -/
def scalarMatrixCommutator
    (x : B) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) B) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) B :=
  fun i j => x * M i j - M i j * x

/-- Written-order matrix commutator over the deformation ring. -/
def sourceMatrixCommutator
    (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) B) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) B :=
  M * N - N * M

/-- Coefficientwise zero-preserving lift of a matrix. -/
def liftMatrix
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Abar) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) B :=
  fun i j => zeroPreservingLift S (M i j)

@[simp]
theorem liftMatrix_map
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Abar) :
    (liftMatrix S M).map S.modParameter = M := by
  ext i j
  simp [liftMatrix, Matrix.map_apply]

theorem liftMatrix_isStrictUpperTriangular
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Abar)
    (hM : IsStrictUpperTriangularOver M) :
    IsStrictUpperTriangularOver (liftMatrix S M) := by
  intro i j hji
  simp [liftMatrix, hM i j hji]

/-- Entrywise parameter cofactor of a matrix whose reduction vanishes. -/
def factorMatrix
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) B) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) B :=
  fun i j => principalCofactor S (M i j)

theorem parameter_mul_factorMatrix
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hM : M.map S.modParameter = 0) :
    ∀ i j, S.parameter * factorMatrix S M i j = M i j := by
  intro i j
  apply parameter_mul_principalCofactor S
  have hij := congrArg (fun Q => Q i j) hM
  simpa [Matrix.map_apply] using hij

theorem factorMatrix_isStrictUpperTriangular
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hM : IsStrictUpperTriangularOver M) :
    IsStrictUpperTriangularOver (factorMatrix S M) := by
  intro i j hji
  simp [factorMatrix, hM i j hji]

theorem scalarMatrixCommutator_map_eq_zero
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (x : B) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) B) :
    (scalarMatrixCommutator x M).map S.modParameter = 0 := by
  ext i j
  simp [scalarMatrixCommutator, Matrix.map_apply, mul_comm]

theorem scalarMatrixCommutator_isStrictUpperTriangular
    (x : B) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hM : IsStrictUpperTriangularOver M) :
    IsStrictUpperTriangularOver (scalarMatrixCommutator x M) := by
  intro i j hji
  simp [scalarMatrixCommutator, hM i j hji]

theorem mul_isStrictUpperTriangular
    (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hM : IsStrictUpperTriangularOver M)
    (hN : IsStrictUpperTriangularOver N) :
    IsStrictUpperTriangularOver (M * N) := by
  intro i j hji
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro a _ha
  rcases le_total a i with hai | hia
  · rw [hM i a hai, zero_mul]
  · rw [hN a j (hji.trans hia), mul_zero]

theorem sourceMatrixCommutator_isStrictUpperTriangular
    (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hM : IsStrictUpperTriangularOver M)
    (hN : IsStrictUpperTriangularOver N) :
    IsStrictUpperTriangularOver (sourceMatrixCommutator M N) := by
  intro i j hji
  simp [sourceMatrixCommutator,
    mul_isStrictUpperTriangular M N hM hN i j hji,
    mul_isStrictUpperTriangular N M hN hM i j hji]

theorem sourceMatrixCommutator_map_eq_zero
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hcomm : M.map S.modParameter * N.map S.modParameter =
      N.map S.modParameter * M.map S.modParameter) :
    (sourceMatrixCommutator M N).map S.modParameter = 0 := by
  ext i j
  have hij := congrArg (fun Q => Q i j) hcomm
  change S.modParameter ((M * N) i j - (N * M) i j) = 0
  rw [S.modParameter.map_sub, Matrix.mul_apply, Matrix.mul_apply]
  simp only [map_sum, S.modParameter.map_mul]
  simpa [Matrix.mul_apply, Matrix.map_apply] using sub_eq_zero.mpr hij

/-- Although matrix multiplication need not commute after reduction, the
trace of a reduced matrix commutator vanishes over the commutative special
fibre. -/
theorem sourceMatrixCommutator_map_trace_eq_zero
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) B) :
    Matrix.trace ((sourceMatrixCommutator M N).map S.modParameter) = 0 := by
  have hmap : (sourceMatrixCommutator M N).map S.modParameter =
      M.map S.modParameter * N.map S.modParameter -
        N.map S.modParameter * M.map S.modParameter := by
    ext i j
    simp [sourceMatrixCommutator, Matrix.map_apply, Matrix.mul_apply]
  rw [hmap, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- The five cofactors retained from the primary-source calculation: three
strict matrix cofactors and two scalar trace cofactors. -/
structure Equation33Cofactors
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (x y : B)
    (A Bm Gamma Theta : Matrix (Fin (n + 1)) (Fin (n + 1)) B) where
  /-- The strictly upper triangular cofactor of the scalar commutator of `x` with `Bm`. -/
  X : Matrix (Fin (n + 1)) (Fin (n + 1)) B
  /-- The strictly upper triangular cofactor of the scalar commutator of `y` with `A`. -/
  Y : Matrix (Fin (n + 1)) (Fin (n + 1)) B
  /-- The strictly upper triangular cofactor of the matrix commutator of `Bm` with `A`. -/
  Omega : Matrix (Fin (n + 1)) (Fin (n + 1)) B
  /-- The parameter cofactor of the trace of the commutator of `Theta` with `A`. -/
  tauThetaA : B
  /-- The parameter cofactor of the trace of the commutator of `Bm` with `Gamma`. -/
  tauBGamma : B
  xB_eq : ∀ i j, S.parameter * X i j = scalarMatrixCommutator x Bm i j
  yA_eq : ∀ i j, S.parameter * Y i j = scalarMatrixCommutator y A i j
  BA_eq : ∀ i j,
    S.parameter * Omega i j = sourceMatrixCommutator Bm A i j
  X_strict : IsStrictUpperTriangularOver X
  Y_strict : IsStrictUpperTriangularOver Y
  Omega_strict : IsStrictUpperTriangularOver Omega
  trace_ThetaA_eq :
    S.parameter * tauThetaA = Matrix.trace (sourceMatrixCommutator Theta A)
  trace_BGamma_eq :
    S.parameter * tauBGamma = Matrix.trace (sourceMatrixCommutator Bm Gamma)

/-- The source cofactors are constructed, not assumed. -/
def equation33Cofactors
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (x y : B)
    (A Bm Gamma Theta : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hA : IsStrictUpperTriangularOver A)
    (hB : IsStrictUpperTriangularOver Bm)
    (hBAcomm : Bm.map S.modParameter * A.map S.modParameter =
      A.map S.modParameter * Bm.map S.modParameter) :
    Equation33Cofactors S x y A Bm Gamma Theta := by
  let X := factorMatrix S (scalarMatrixCommutator x Bm)
  let Y := factorMatrix S (scalarMatrixCommutator y A)
  let Omega := factorMatrix S (sourceMatrixCommutator Bm A)
  let tauThetaA := principalCofactor S
    (Matrix.trace (sourceMatrixCommutator Theta A))
  let tauBGamma := principalCofactor S
    (Matrix.trace (sourceMatrixCommutator Bm Gamma))
  refine
    { X := X
      Y := Y
      Omega := Omega
      tauThetaA := tauThetaA
      tauBGamma := tauBGamma
      xB_eq := parameter_mul_factorMatrix S _
        (scalarMatrixCommutator_map_eq_zero S x Bm)
      yA_eq := parameter_mul_factorMatrix S _
        (scalarMatrixCommutator_map_eq_zero S y A)
      BA_eq := parameter_mul_factorMatrix S _
        (sourceMatrixCommutator_map_eq_zero S Bm A hBAcomm)
      X_strict := factorMatrix_isStrictUpperTriangular S _
        (scalarMatrixCommutator_isStrictUpperTriangular x Bm hB)
      Y_strict := factorMatrix_isStrictUpperTriangular S _
        (scalarMatrixCommutator_isStrictUpperTriangular y A hA)
      Omega_strict := factorMatrix_isStrictUpperTriangular S _
        (sourceMatrixCommutator_isStrictUpperTriangular Bm A hB hA)
      trace_ThetaA_eq := ?_
      trace_BGamma_eq := ?_ }
  · apply parameter_mul_principalCofactor S
    calc
      S.modParameter (Matrix.trace (sourceMatrixCommutator Theta A)) =
          Matrix.trace ((sourceMatrixCommutator Theta A).map S.modParameter) := by
            simpa using
              (AddMonoidHom.map_trace S.modParameter.toAddMonoidHom
                (sourceMatrixCommutator Theta A))
      _ = 0 := sourceMatrixCommutator_map_trace_eq_zero S Theta A
  · apply parameter_mul_principalCofactor S
    calc
      S.modParameter (Matrix.trace (sourceMatrixCommutator Bm Gamma)) =
          Matrix.trace ((sourceMatrixCommutator Bm Gamma).map S.modParameter) := by
            simpa using
              (AddMonoidHom.map_trace S.modParameter.toAddMonoidHom
                (sourceMatrixCommutator Bm Gamma))
      _ = 0 := sourceMatrixCommutator_map_trace_eq_zero S Bm Gamma

/-- The strict remainder `R = X - Y + Omega` from equation (3.3). -/
def sourceStrictRemainder
    {S : LeftPrincipalParameterReduction (B := B) (Abar := Abar)}
    {x y : B} {A Bm Gamma Theta : Matrix (Fin (n + 1)) (Fin (n + 1)) B}
    (C : Equation33Cofactors S x y A Bm Gamma Theta) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) B :=
  C.X - C.Y + C.Omega

theorem sourceStrictRemainder_isStrictUpperTriangular
    {S : LeftPrincipalParameterReduction (B := B) (Abar := Abar)}
    {x y : B} {A Bm Gamma Theta : Matrix (Fin (n + 1)) (Fin (n + 1)) B}
    (C : Equation33Cofactors S x y A Bm Gamma Theta) :
    IsStrictUpperTriangularOver (sourceStrictRemainder C) := by
  intro i j hji
  simp [sourceStrictRemainder, C.X_strict i j hji,
    C.Y_strict i j hji, C.Omega_strict i j hji]

/-- The two correction matrices `Q1=[Theta,A]` and `Q2=[B,Gamma]`. -/
def sourceCorrectionThetaA
    (Theta A : Matrix (Fin (n + 1)) (Fin (n + 1)) B) :=
  sourceMatrixCommutator Theta A

/-- The matrix commutator correction involving `Bm` and `Gamma`. -/
def sourceCorrectionBGamma
    (Bm Gamma : Matrix (Fin (n + 1)) (Fin (n + 1)) B) :=
  sourceMatrixCommutator Bm Gamma

theorem correctionThetaA_traceInParameter
    {S : LeftPrincipalParameterReduction (B := B) (Abar := Abar)}
    {x y : B} {A Bm Gamma Theta : Matrix (Fin (n + 1)) (Fin (n + 1)) B}
    (C : Equation33Cofactors S x y A Bm Gamma Theta) :
    CorrectionTraceInParameter S.toParameterIdealReduction
      (sourceCorrectionThetaA Theta A) := by
  rw [CorrectionTraceInParameter, Ideal.mem_span_singleton']
  exact ⟨C.tauThetaA,
    (S.parameter_comm C.tauThetaA).symm.trans C.trace_ThetaA_eq⟩

theorem correctionBGamma_traceInParameter
    {S : LeftPrincipalParameterReduction (B := B) (Abar := Abar)}
    {x y : B} {A Bm Gamma Theta : Matrix (Fin (n + 1)) (Fin (n + 1)) B}
    (C : Equation33Cofactors S x y A Bm Gamma Theta) :
    CorrectionTraceInParameter S.toParameterIdealReduction
      (sourceCorrectionBGamma Bm Gamma) := by
  rw [CorrectionTraceInParameter, Ideal.mem_span_singleton']
  exact ⟨C.tauBGamma,
    (S.parameter_comm C.tauBGamma).symm.trans C.trace_BGamma_eq⟩

/-- Literal trace-zero conclusion for the matrix produced by the source
cofactors.  This consumes the faithful equation-(3.3) trace reducer, not the
stronger same-size coefficient-field commutator surrogate. -/
theorem sourceReducedEquation33Matrix_trace_eq_zero
    (S : LeftPrincipalParameterReduction (B := B) (Abar := Abar))
    (residue : Abar →+* K)
    (x y : B)
    (A Bm Gamma Theta : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hA : IsStrictUpperTriangularOver A)
    (hB : IsStrictUpperTriangularOver Bm)
    (hBAcomm : Bm.map S.modParameter * A.map S.modParameter =
      A.map S.modParameter * Bm.map S.modParameter) :
    Matrix.trace
      (reducedEquation33Matrix S.toParameterIdealReduction residue
        (sourceStrictRemainder
          (equation33Cofactors S x y A Bm Gamma Theta hA hB hBAcomm))
        (sourceCorrectionThetaA Theta A)
        (sourceCorrectionBGamma Bm Gamma)) = 0 := by
  let C := equation33Cofactors S x y A Bm Gamma Theta hA hB hBAcomm
  exact reducedEquation33Matrix_trace_eq_zero
    S.toParameterIdealReduction residue
      (sourceStrictRemainder C)
      (sourceCorrectionThetaA Theta A)
      (sourceCorrectionBGamma Bm Gamma)
      (sourceStrictRemainder_isStrictUpperTriangular C)
      (correctionThetaA_traceInParameter C)
      (correctionBGamma_traceInParameter C)

end MatrixAlgebra

section AdaptedActionMatrices

variable {K R V B : Type u}
variable [Field K] [CommRing R] [Algebra K R] [IsLocalRing R]
variable [IsArtinianRing R]
variable [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower K R V]
variable [FiniteDimensional K V]
variable [Ring B]
variable {n : ℕ}

local notation "m" => IsLocalRing.maximalIdeal R

/-- The literal matrix of multiplication by a special-fibre element.  This is
the operator that equation (3.3) must identify when the element is the
bracket cofactor `z`. -/
def inducedSpecialFibreActionMatrix
    (b : Module.Basis (Fin (n + 1)) K V) (zbar : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  LinearMap.toMatrix b b
    (leftMultiplicationEnd (K := K) (V := V) zbar)

/-- The source uses row vectors, whereas `LinearMap.toMatrix` uses the usual
column convention.  Transposition is therefore part of the literal
source-to-Lean adapter. -/
def inducedSpecialFibreSourceMatrix
    (b : Module.Basis (Fin (n + 1)) K V) (zbar : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  (inducedSpecialFibreActionMatrix b zbar)ᵀ

/-- Actual zeroth-order adapted-basis action matrices in Lean's column
convention, with strict zero-preserving lifts to the deformation ring.  The
returned lifts `x` and `y` specialize to the requested elements.  Passing to
the source's row convention requires the explicit transpose adapter above. -/
theorem exists_lifted_adapted_actionMatrices
    (S : LeftPrincipalParameterReduction (B := B) (Abar := R))
    (hdim : Module.finrank K V = n + 1)
    (xbar ybar : R) (hx : xbar ∈ m) (hy : ybar ∈ m) :
    ∃ (b : Module.Basis (Fin (n + 1)) K V)
      (level : Fin (n + 1) → ℕ)
      (x y : B)
      (A Bm : Matrix (Fin (n + 1)) (Fin (n + 1)) B),
      IsMaximalIdealFiltrationAdapted m b level ∧
      S.modParameter x = xbar ∧
      S.modParameter y = ybar ∧
      A.map S.modParameter =
        (LinearMap.toMatrix b b
          (leftMultiplicationEnd (K := K) (V := V) xbar)).map
            (algebraMap K R) ∧
      Bm.map S.modParameter =
        (LinearMap.toMatrix b b
          (leftMultiplicationEnd (K := K) (V := V) ybar)).map
            (algebraMap K R) ∧
      IsStrictUpperTriangularOver A ∧
      IsStrictUpperTriangularOver Bm ∧
      Bm.map S.modParameter * A.map S.modParameter =
        A.map S.modParameter * Bm.map S.modParameter := by
  obtain ⟨b, level, hadapted⟩ :=
    exists_maximalIdealFiltrationAdaptedBasis (K := K) (R := R) (V := V) hdim
  let Ax := leftMultiplicationEnd (K := K) (V := V) xbar
  let By := leftMultiplicationEnd (K := K) (V := V) ybar
  let A0K := LinearMap.toMatrix b b Ax
  let B0K := LinearMap.toMatrix b b By
  let A0 := A0K.map (algebraMap K R)
  let B0 := B0K.map (algebraMap K R)
  let A := liftMatrix S A0
  let Bm := liftMatrix S B0
  let x := zeroPreservingLift S xbar
  let y := zeroPreservingLift S ybar
  have hA0K : IsStrictUpperTriangularOver A0K :=
    leftMultiplicationMatrix_isStrictUpperTriangular b level hadapted hx
  have hB0K : IsStrictUpperTriangularOver B0K :=
    leftMultiplicationMatrix_isStrictUpperTriangular b level hadapted hy
  have hA0 : IsStrictUpperTriangularOver A0 :=
    fun i j hji => by simp [A0, Matrix.map_apply, hA0K i j hji]
  have hB0 : IsStrictUpperTriangularOver B0 :=
    fun i j hji => by simp [B0, Matrix.map_apply, hB0K i j hji]
  have hEnd : By * Ax = Ax * By := by
    ext v
    change ybar • xbar • v = xbar • ybar • v
    rw [← mul_smul, ← mul_smul, mul_comm]
  have hK : B0K * A0K = A0K * B0K := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, hEnd]
  have hcomm : B0 * A0 = A0 * B0 := by
    change B0K.map (algebraMap K R) * A0K.map (algebraMap K R) =
      A0K.map (algebraMap K R) * B0K.map (algebraMap K R)
    rw [← Matrix.map_mul, ← Matrix.map_mul, hK]
  exact ⟨b, level, x, y, A, Bm, hadapted,
    modParameter_zeroPreservingLift S xbar,
    modParameter_zeroPreservingLift S ybar,
    liftMatrix_map S A0,
    liftMatrix_map S B0,
    liftMatrix_isStrictUpperTriangular S A0 hA0,
    liftMatrix_isStrictUpperTriangular S B0 hB0, by
      rw [liftMatrix_map, liftMatrix_map]
      exact hcomm⟩

end AdaptedActionMatrices

section ConcreteReduction

variable (k : Type u) [Field k]
variable {n : ℕ}
variable (I : RightIdeal (PresentedWeyl k n))
variable (S : Submonoid (SymbolRing k n))
variable [OreLocalization.OreSet
  (OppositeDenominators (filteredQuotientTwoJetTraceData k I) S)]
variable [IsLocalRing (Localization S)]

local notation "D" =>
  Stafford38.Characteristic.ConcreteLocalizedTwoBlockSpecialFibre.concreteData k I

/-- The concrete localized two-block quotient has exactly the principal
parameter reduction required by the source matrix construction. -/
def concreteLeftPrincipalParameterReduction (q : ℕ) :
    LeftPrincipalParameterReduction
      (B := LocalizedTwoBlockRing D S q)
      (Abar := (Localization S) ⧸ localizedDoubledPower S q) where
  parameter := concreteLocalizedTwoBlockParameter k I S q
  modParameter := localizedTwoBlockSpecialization D S q
  surjective := localizedTwoBlockSpecialization_surjective D S q
  parameter_comm := by
    intro z
    induction z using Quotient.inductionOn' with
    | _ a =>
      change
        (localizedTwoBlockIdeal D S q).ringCon.mk'
            (OreLocalization.numeratorRingHom
              (MulOpposite.op (orderReesTwoJetParameter (n := n) k))) *
          (localizedTwoBlockIdeal D S q).ringCon.mk' a = _
      calc
        (localizedTwoBlockIdeal D S q).ringCon.mk'
              (OreLocalization.numeratorRingHom
                (MulOpposite.op (orderReesTwoJetParameter (n := n) k))) *
            (localizedTwoBlockIdeal D S q).ringCon.mk' a =
          (localizedTwoBlockIdeal D S q).ringCon.mk'
            (OreLocalization.numeratorRingHom
              (MulOpposite.op (orderReesTwoJetParameter (n := n) k)) * a) := by
                exact ((localizedTwoBlockIdeal D S q).ringCon.mk').map_mul _ _ |>.symm
        _ = (localizedTwoBlockIdeal D S q).ringCon.mk'
            (a * OreLocalization.numeratorRingHom
              (MulOpposite.op (orderReesTwoJetParameter (n := n) k))) := by
                exact congrArg ((localizedTwoBlockIdeal D S q).ringCon.mk')
                  (localizedParameter_comm D S a)
        _ = (localizedTwoBlockIdeal D S q).ringCon.mk' a *
            (localizedTwoBlockIdeal D S q).ringCon.mk'
              (OreLocalization.numeratorRingHom
                (MulOpposite.op (orderReesTwoJetParameter (n := n) k))) := by
                exact ((localizedTwoBlockIdeal D S q).ringCon.mk').map_mul _ _
  kernel_left :=
    concreteLocalizedTwoBlockSpecialization_eq_zero_iff_exists_parameter_mul
      k I S q

/-- The exact remaining source-specific bridge.  The left side is the actual
matrix of the operator induced by the bracket cofactor `z` on the coefficient
field special fibre.  The right side is the matrix already constructed from
the lifted adapted basis and all five explicit equation-(3.3) cofactors.

No inhabitant is constructed here: proving this equality requires the lifted
basis-vector action equations in the concrete localized module.  In
particular, this definition is not a trace-zero theorem. -/
def ConcreteInducedZActionIdentity
    {K V : Type u} [Field K]
    [AddCommGroup V]
    {q r : ℕ}
    (parameterReduction : LeftPrincipalParameterReduction
      (B := LocalizedTwoBlockRing D S q)
      (Abar := (Localization S) ⧸ localizedDoubledPower S q))
    (residue : ((Localization S) ⧸ localizedDoubledPower S q) →+* K)
    [Algebra K ((Localization S) ⧸ localizedDoubledPower S q)]
    [Module K V]
    [Module ((Localization S) ⧸ localizedDoubledPower S q) V]
    [IsScalarTower K ((Localization S) ⧸ localizedDoubledPower S q) V]
    (b : Module.Basis (Fin (r + 1)) K V)
    (zbar : (Localization S) ⧸ localizedDoubledPower S q)
    (x y : LocalizedTwoBlockRing D S q)
    (A Bm Gamma Theta :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (LocalizedTwoBlockRing D S q))
    (hA : IsStrictUpperTriangularOver A)
    (hB : IsStrictUpperTriangularOver Bm)
    (hBAcomm : Bm.map parameterReduction.modParameter *
        A.map parameterReduction.modParameter =
      A.map parameterReduction.modParameter *
        Bm.map parameterReduction.modParameter) : Prop :=
  let C := equation33Cofactors parameterReduction x y A Bm Gamma Theta
    hA hB hBAcomm
  inducedSpecialFibreSourceMatrix b zbar =
    reducedEquation33Matrix parameterReduction.toParameterIdealReduction residue
      (sourceStrictRemainder C)
      (sourceCorrectionThetaA Theta A)
      (sourceCorrectionBGamma Bm Gamma)


end ConcreteReduction

end

end Stafford38.Characteristic.ConcreteEquation33SourceMatrices
