/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.MultiscalePoincare
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoli
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS

/-! # Setup -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Coarse Caccioppoli with RHS Setup

This file is split mechanically out of `CoarseCaccioppoliRHS.lean`.

## Audit tag

Claim: define the public forced-boundary Caccioppoli decomposition data and
transport the zero-trace corrector into the open-cube public domain.

Downstream target: `CoarseCaccioppoliRHS/EnergySplit.lean`.  This file should
remain setup infrastructure, not a public theorem-package surface.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- The public/open-cube form of the zero-trace corrector attached to the
forced boundary Caccioppoli decomposition. -/
noncomputable def boundaryForcedCaccioppoliCorrectorOpenH10
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    H10Function (Ch02.cubeDomain Q : Set (Vec d)) :=
  castH10Domain (Ch02.cubeDomain_coe Q).symm ρ.toH10.toOpenCubeSet

@[simp] theorem boundaryForcedCaccioppoliCorrectorOpenH10_grad
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ).toH1Function.grad =
      ρ.toH10.toH1Function.grad := by
  simp only [boundaryForcedCaccioppoliCorrectorOpenH10]
  rw [castH10Domain_toH1Function_grad]
  rw [H10Function.toOpenCubeSet_toH1Function_grad]

@[simp] theorem boundaryForcedCaccioppoliCorrectorOpenH10_toFun
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ).toH1Function.toFun =
      ρ.toH10.toH1Function.toFun := by
  simp only [boundaryForcedCaccioppoliCorrectorOpenH10]
  rw [castH10Domain_toH1Function_toFun]
  rw [H10Function.toOpenCubeSet_toH1Function_toFun]

/-- Half-open zero-trace RHS weak solutions transport to the open cube because
the boundary has zero volume. -/
theorem isZeroTraceDirichletRhsWeakSolution_openCubeSet_of_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d}
    {A : CoeffField d} {u : H10Function (cubeSet Q)}
    {g : Vec d → Vec d}
    (h : IsZeroTraceDirichletRhsWeakSolution A (cubeSet Q) u g) :
    IsZeroTraceDirichletRhsWeakSolution A (openCubeSet Q) u.toOpenCubeSet g := by
  intro φ
  have hcube := h φ.toCubeSet
  have hleft :
      ∫ x in cubeSet Q,
          vecDot (matVecMul (A x) (u.toH1Function.grad x))
            (φ.toCubeSet.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (matVecMul (A x) (u.toOpenCubeSet.toH1Function.grad x))
            (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q)
        (f := fun x =>
          vecDot (matVecMul (A x) (u.toH1Function.grad x))
            (φ.toCubeSet.toH1Function.grad x)))
  have hright :
      ∫ x in cubeSet Q,
          vecDot (g x) (φ.toCubeSet.toH1Function.grad x)
            ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q)
        (f := fun x => vecDot (g x) (φ.toCubeSet.toH1Function.grad x)))
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (A x) (u.toOpenCubeSet.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in cubeSet Q,
        vecDot (matVecMul (A x) (u.toH1Function.grad x))
          (φ.toCubeSet.toH1Function.grad x) ∂MeasureTheory.volume := hleft.symm
    _ =
      ∫ x in cubeSet Q,
        vecDot (g x) (φ.toCubeSet.toH1Function.grad x)
          ∂MeasureTheory.volume := hcube
    _ =
      ∫ x in openCubeSet Q,
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := hright

/-- On the public open cube, replacing `publicCoeffField` by the deterministic
`coeffOn` representative preserves zero-trace RHS weak solutions. -/
theorem isZeroTraceDirichletRhsWeakSolution_coeffOn_openCubeSet_of_publicCoeffField
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {u : H10Function (openCubeSet Q)} {g : Vec d → Vec d}
    (h : IsZeroTraceDirichletRhsWeakSolution (publicCoeffField Q a)
      (openCubeSet Q) u g) :
    IsZeroTraceDirichletRhsWeakSolution (a.coeffOn Q).toCoeffField
      (openCubeSet Q) u g := by
  intro φ
  have hcoeff := publicCoeffField_ae_eq_openCubeSet Q a
  have hintegrand :
      (fun x =>
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
          (u.toH1Function.grad x)) (φ.toH1Function.grad x))
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x =>
        vecDot (matVecMul (publicCoeffField Q a x)
          (u.toH1Function.grad x)) (φ.toH1Function.grad x) := by
    filter_upwards [hcoeff] with x hx
    simp [hx]
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
          (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        vecDot (matVecMul (publicCoeffField Q a x)
          (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := MeasureTheory.integral_congr_ae hintegrand
    _ =
      ∫ x in openCubeSet Q,
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := h φ

/-- Public zero-trace forced-solution wrapper for the auxiliary corrector in
the forced boundary Caccioppoli decomposition. -/
noncomputable def boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    ZeroTraceForcedCubeSolution Q a g where
  toH10 := boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ
  weakSolution := by
    have hopen_public :
        IsZeroTraceDirichletRhsWeakSolution (publicCoeffField Q a)
          (openCubeSet Q) ρ.toH10.toOpenCubeSet g :=
      isZeroTraceDirichletRhsWeakSolution_openCubeSet_of_cubeSet
        (Q := Q) (A := publicCoeffField Q a) ρ.weakSolution
    have hopen_coeff :
        IsZeroTraceDirichletRhsWeakSolution (a.coeffOn Q).toCoeffField
          (openCubeSet Q) ρ.toH10.toOpenCubeSet g :=
      isZeroTraceDirichletRhsWeakSolution_coeffOn_openCubeSet_of_publicCoeffField
        (Q := Q) (a := a) hopen_public
    intro φ
    let φOpen : H10Function (openCubeSet Q) :=
      castH10Domain (Ch02.cubeDomain_coe Q) φ
    have h := hopen_coeff φOpen
    have hgrad : φOpen.toH1Function.grad = φ.toH1Function.grad := by
      simp only [φOpen]
      rw [castH10Domain_toH1Function_grad]
    have hρgrad :
        (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ).toH1Function.grad =
          ρ.toH10.toH1Function.grad :=
      boundaryForcedCaccioppoliCorrectorOpenH10_grad (Q := Q) (a := a) ρ
    have hρgrad' :
        ρ.toH10.toOpenCubeSet.toH1Function.grad = ρ.toH10.toH1Function.grad := by
      simp only [H10Function.toOpenCubeSet_toH1Function_grad]
    simpa only [hgrad, hρgrad, hρgrad', Ch02.cubeDomain_coe] using h

/-- Public forced-solution wrapper for the zero-trace corrector, used when the
RHS Poincare gradient estimate is applied to the corrector itself. -/
noncomputable def boundaryForcedCaccioppoliCorrectorForcedCubeSolution
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    ForcedCubeSolution Q a g where
  toH1 :=
    (boundaryForcedCaccioppoliCorrectorOpenH10
      (Q := Q) (a := a) ρ).toH1Function
  weakSolution :=
    (boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution
      (Q := Q) (a := a) ρ).weakSolution

@[simp] theorem boundaryForcedCaccioppoliCorrectorForcedCubeSolution_grad
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    (boundaryForcedCaccioppoliCorrectorForcedCubeSolution
      (Q := Q) (a := a) ρ).toH1.grad =
      ρ.toH10.toH1Function.grad := by
  simp [boundaryForcedCaccioppoliCorrectorForcedCubeSolution]

@[simp] theorem boundaryForcedCaccioppoliCorrectorForcedCubeSolution_energyNorm_eq
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    forcedSolutionEnergyNorm Q a
        (boundaryForcedCaccioppoliCorrectorForcedCubeSolution
          (Q := Q) (a := a) ρ) =
      zeroTraceForcedSolutionEnergyNorm Q a
        (boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution
          (Q := Q) (a := a) ρ) := by
  simp only [boundaryForcedCaccioppoliCorrectorForcedCubeSolution,
    boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution,
    forcedSolutionEnergyNorm, zeroTraceForcedSolutionEnergyNorm]

/-- Value-level homogeneous remainder `w = u - ρ` on the public open cube. -/
noncomputable def boundaryForcedCaccioppoliRemainderOpenH1
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    H1Function (Ch02.cubeDomain Q : Set (Vec d)) :=
  u.toH1 - (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ).toH1Function

@[simp] theorem boundaryForcedCaccioppoliRemainderOpenH1_grad
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    (boundaryForcedCaccioppoliRemainderOpenH1 u ρ).grad =
      fun y => u.toH1.grad y - ρ.toH10.toH1Function.grad y := by
  funext y
  simp only [boundaryForcedCaccioppoliRemainderOpenH1, H1Function.sub_grad,
    boundaryForcedCaccioppoliCorrectorOpenH10_grad]

@[simp] theorem boundaryForcedCaccioppoliRemainderOpenH1_toFun
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    (boundaryForcedCaccioppoliRemainderOpenH1 u ρ).toFun =
      fun y => u.toH1.toFun y - ρ.toH10.toH1Function.toFun y := by
  funext y
  simp only [boundaryForcedCaccioppoliRemainderOpenH1, H1Function.sub_toFun,
    boundaryForcedCaccioppoliCorrectorOpenH10_toFun]

/-- Deterministic half-open-cube realization of the homogeneous remainder. -/
noncomputable def boundaryForcedCaccioppoliRemainderCubeH1
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    H1Function (cubeSet Q) :=
  publicH1ToCubeSet (boundaryForcedCaccioppoliRemainderOpenH1 u ρ)

@[simp] theorem boundaryForcedCaccioppoliRemainderCubeH1_grad
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    (boundaryForcedCaccioppoliRemainderCubeH1 u ρ).grad =
      fun y => u.toH1.grad y - ρ.toH10.toH1Function.grad y := by
  funext y
  simp [boundaryForcedCaccioppoliRemainderCubeH1]

@[simp] theorem boundaryForcedCaccioppoliRemainderCubeH1_toFun
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g) :
    (boundaryForcedCaccioppoliRemainderCubeH1 u ρ).toFun =
      fun y => u.toH1.toFun y - ρ.toH10.toH1Function.toFun y := by
  funext y
  simp [boundaryForcedCaccioppoliRemainderCubeH1]

/-- The value-level remainder is `a`-harmonic on the deterministic cube. -/
theorem boundaryForcedCaccioppoliRemainderCube_isAHarmonicGradient_publicCoeffField
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g) :
    IsAHarmonicGradient (publicCoeffField Q a) (cubeSet Q)
      (boundaryForcedCaccioppoliRemainderCubeH1 u ρ).grad := by
  let U : H1Function (cubeSet Q) := publicH1ToCubeSet u.toH1
  let W : H1Function (cubeSet Q) :=
    boundaryForcedCaccioppoliRemainderCubeH1 u ρ
  have hweak :
      IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (cubeSet Q) U g := by
    simpa [U] using
      isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
        (Q := Q) (a := a) (u := u.toH1) (g := g) u.weakSolution
  have hres_u :
      IsSolenoidalOn (cubeSet Q)
        (fun y => matVecMul (publicCoeffField Q a y) (U.grad y) - g y) :=
    hweak.residual_solenoidal
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) hg_mem
  have hres_ρ :
      IsSolenoidalOn (cubeSet Q)
        (fun y =>
          matVecMul (publicCoeffField Q a y) (ρ.toH10.toH1Function.grad y) - g y) :=
    ρ.residualFlux_solenoidal
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) hg_mem
  have hU_mem : MemVectorL2 (cubeSet Q) U.grad := U.grad_memVectorL2
  have hflux_u_mem :
      MemVectorL2 (cubeSet Q)
        (fun y => matVecMul (publicCoeffField Q a y) (U.grad y)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) hU_mem
  have hres_u_mem :
      MemVectorL2 (cubeSet Q)
        (fun y => matVecMul (publicCoeffField Q a y) (U.grad y) - g y) :=
    hflux_u_mem.sub hg_mem
  have hflux_ρ_mem :
      MemVectorL2 (cubeSet Q)
        (fun y => matVecMul (publicCoeffField Q a y)
          (ρ.toH10.toH1Function.grad y)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      ρ.toH10.toH1Function.grad_memVectorL2
  have hres_ρ_mem :
      MemVectorL2 (cubeSet Q)
        (fun y =>
          matVecMul (publicCoeffField Q a y) (ρ.toH10.toH1Function.grad y) - g y) :=
    hflux_ρ_mem.sub hg_mem
  have hsol_sum :
      IsSolenoidalOn (cubeSet Q)
        ((fun y => matVecMul (publicCoeffField Q a y) (U.grad y) - g y) +
          (-1 : ℝ) •
            (fun y =>
              matVecMul (publicCoeffField Q a y)
                (ρ.toH10.toH1Function.grad y) - g y)) :=
    isSolenoidalOn_add_of_memVectorL2 hres_u_mem (hres_ρ_mem.const_smul (-1))
      hres_u (isSolenoidalOn_smul hres_ρ (-1))
  have hsol :
      IsSolenoidalOn (cubeSet Q)
        (fun y => matVecMul (publicCoeffField Q a y) (W.grad y)) := by
    convert hsol_sum using 1
    funext y
    ext i
    simp [W, U, boundaryForcedCaccioppoliRemainderCubeH1,
      sub_eq_add_neg, matVecMul_add, matVecMul_neg, Pi.add_apply]
  exact ⟨W.isPotentialOn, hsol⟩

/-- The value-level remainder is harmonic for the public coefficient field on
the open cube. -/
theorem boundaryForcedCaccioppoliRemainderOpen_isAHarmonicGradient_publicCoeffField
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g) :
    IsAHarmonicGradient (publicCoeffField Q a) (openCubeSet Q)
      (boundaryForcedCaccioppoliRemainderOpenH1 u ρ).grad := by
  have hcube :=
    boundaryForcedCaccioppoliRemainderCube_isAHarmonicGradient_publicCoeffField
      (Q := Q) (a := a) u ρ hg_mem
  constructor
  · simpa [boundaryForcedCaccioppoliRemainderCubeH1] using
      isPotentialOn_openCubeSet_triadicCube_of_cubeSet hcube.1
  · simpa [boundaryForcedCaccioppoliRemainderCubeH1] using
      isSolenoidalOn_openCubeSet_triadicCube_of_cubeSet hcube.2

/-- The value-level remainder is harmonic for the note-facing coefficient
representative on the public cube domain. -/
theorem boundaryForcedCaccioppoliRemainderOpen_isAHarmonicGradient_coeffOn
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g) :
    IsAHarmonicGradient (a.coeffOn Q).toCoeffField
      (Ch02.cubeDomain Q : Set (Vec d))
      (boundaryForcedCaccioppoliRemainderOpenH1 u ρ).grad := by
  have hpublic :
      IsAHarmonicGradient (publicCoeffField Q a) (openCubeSet Q)
        (boundaryForcedCaccioppoliRemainderOpenH1 u ρ).grad :=
    boundaryForcedCaccioppoliRemainderOpen_isAHarmonicGradient_publicCoeffField
      (Q := Q) (a := a) u ρ hg_mem
  have hcoeff :
      IsAHarmonicGradient (a.coeffOn Q).toCoeffField (openCubeSet Q)
        (boundaryForcedCaccioppoliRemainderOpenH1 u ρ).grad :=
    IsAHarmonicGradient.of_ae_eq_coeff
      (publicCoeffField_ae_eq_openCubeSet Q a) hpublic
  simpa [Ch02.cubeDomain_coe] using hcoeff

/-- Homogeneous boundary datum obtained by subtracting the zero-trace
Dirichlet corrector from a forced boundary datum. -/
noncomputable def boundaryForcedCaccioppoliRemainderDatum
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g) :
    BoundaryCaccioppoliDatum Q a x where
  toH1 := boundaryForcedCaccioppoliRemainderOpenH1 u ρ
  isHarmonic :=
    boundaryForcedCaccioppoliRemainderOpen_isAHarmonicGradient_coeffOn
      (Q := Q) (a := a) u ρ hg_mem
  zeroTraceOnBoundaryPatch := by
    have hρ :
        LocalizedZeroTraceFunctionOn
          (Ch02.cubeDomain Q : Set (Vec d))
          (openCubeAtScale x (Q.scale - 1))
          (boundaryForcedCaccioppoliCorrectorOpenH10
            (Q := Q) (a := a) ρ).toH1Function.toFun :=
      localizedZeroTraceFunctionOn_of_h10_any
        (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) ρ)
    have hsub :=
      localizedZeroTraceFunctionOn_sub u.zeroTraceOnBoundaryPatch hρ
    have hfun :
        (boundaryForcedCaccioppoliRemainderOpenH1 u ρ).toFun =
          fun y => u.toH1.toFun y -
            (boundaryForcedCaccioppoliCorrectorOpenH10
              (Q := Q) (a := a) ρ).toH1Function.toFun y := by
      funext y
      simp only [boundaryForcedCaccioppoliRemainderOpenH1, H1Function.sub_toFun]
    rw [hfun]
    exact hsub

@[simp] theorem boundaryForcedCaccioppoliRemainderDatum_toH1
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hg_mem : MemVectorL2 (cubeSet Q) g) :
    (boundaryForcedCaccioppoliRemainderDatum u ρ hg_mem).toH1 =
      boundaryForcedCaccioppoliRemainderOpenH1 u ρ :=
  rfl


end

end Ch03
end Book
end Homogenization
