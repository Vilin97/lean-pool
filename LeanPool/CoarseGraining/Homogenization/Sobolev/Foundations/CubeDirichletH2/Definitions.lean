/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

/-! # Definitions -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# Cube Dirichlet `H²` regularity interfaces

This file freezes the theorem surface for the cube Dirichlet `H²` endpoint
needed by the Chapter 1 Hodge projection argument.  The analytic proof is
planned as an odd-reflection sibling of the existing Neumann/CZ reflection
endpoint; this file contains only the stable problem and regularity contracts.
-/

/-- Scalar weak Dirichlet Poisson problem on a cube.

The sign convention is `-Delta u = f`, encoded by
`int_Q grad u . grad phi = int_Q f phi` for all zero-trace tests. -/
def CubeDirichletWeakPoissonProblem {d : ℕ} (Q : TriadicCube d)
    (u : H10Function (openCubeSet Q)) (f : Vec d → ℝ) : Prop :=
  ∀ φ : H10Function (openCubeSet Q),
    ∫ x in openCubeSet Q,
        vecDot (u.toH1Function.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, f x * φ.toH1Function x
          ∂MeasureTheory.volume

/-- Cube Dirichlet `H²` regularity in the repository's weak-Hessian form.

The Hessian size is measured by `HasWeakHessianOn.hessianCoordL2NormSum`, the
same quantity used by the existing Neumann/CZ endpoint.  The forcing norm is
the normalized cube `L²` norm, matching the positive Besov/CZ layer. -/
def CubeDirichletH2Regularity {d : ℕ} (Q : TriadicCube d) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (u : H10Function (openCubeSet Q)) (f : Vec d → ℝ),
      MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
      CubeDirichletWeakPoissonProblem Q u f →
      ∃ H : HasWeakHessianOn (openCubeSet Q) u.toH1Function,
        H.hessianCoordL2NormSum ≤ C * cubeLpNorm Q (2 : ℝ≥0∞) f

/-- Dimension-uniform cube Dirichlet `H²` regularity. -/
def CubeDirichletH2RegularityInDimension (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ Q : TriadicCube d, CubeDirichletH2Regularity Q C

/-- Cube Dirichlet `H²` regularity with the unnormalized open-cube `L²`
forcing norm on the right-hand side.  The input integrability is still phrased
for the normalized cube measure so this contract can be consumed by the same
Besov/CZ callers as `CubeDirichletH2Regularity`. -/
def CubeDirichletH2RegularityVolumeL2 {d : ℕ} (Q : TriadicCube d) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (u : H10Function (openCubeSet Q)) (f : Vec d → ℝ)
      (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)),
      CubeDirichletWeakPoissonProblem Q u f →
      ∃ H : HasWeakHessianOn (openCubeSet Q) u.toH1Function,
        H.hessianCoordL2NormSum ≤
          C * ‖toScalarL2 (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf)‖

/-- Dimension-uniform cube Dirichlet `H²` regularity with the unnormalized
open-cube `L²` forcing norm. -/
def CubeDirichletH2RegularityVolumeL2InDimension (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ Q : TriadicCube d, CubeDirichletH2RegularityVolumeL2 Q C

theorem CubeDirichletH2Regularity.constant_nonneg
    {d : ℕ} {Q : TriadicCube d} {C : ℝ}
    (h : CubeDirichletH2Regularity Q C) :
    0 ≤ C :=
  h.1

theorem CubeDirichletH2RegularityInDimension.constant_nonneg
    {d : ℕ} {C : ℝ}
    (h : CubeDirichletH2RegularityInDimension d C) :
    0 ≤ C :=
  h.1

theorem CubeDirichletH2RegularityVolumeL2.constant_nonneg
    {d : ℕ} {Q : TriadicCube d} {C : ℝ}
    (h : CubeDirichletH2RegularityVolumeL2 Q C) :
    0 ≤ C :=
  h.1

theorem CubeDirichletH2RegularityVolumeL2InDimension.constant_nonneg
    {d : ℕ} {C : ℝ}
    (h : CubeDirichletH2RegularityVolumeL2InDimension d C) :
    0 ≤ C :=
  h.1

/-- The local Dirichlet `H²` regularity estimate may be enlarged to any larger
constant. -/
theorem CubeDirichletH2Regularity.mono
    {d : ℕ} {Q : TriadicCube d} {C D : ℝ}
    (h : CubeDirichletH2Regularity Q C)
    (hCD : C ≤ D) :
    CubeDirichletH2Regularity Q D := by
  refine ⟨h.1.trans hCD, ?_⟩
  intro u f hf hweak
  rcases h.2 u f hf hweak with ⟨H, hH⟩
  refine ⟨H, ?_⟩
  exact hH.trans
    (mul_le_mul_of_nonneg_right hCD
      (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) f))

/-- The dimension-uniform Dirichlet `H²` regularity estimate may be enlarged to
any larger constant. -/
theorem CubeDirichletH2RegularityInDimension.mono
    {d : ℕ} {C D : ℝ}
    (h : CubeDirichletH2RegularityInDimension d C)
    (hCD : C ≤ D) :
    CubeDirichletH2RegularityInDimension d D := by
  refine ⟨h.1.trans hCD, ?_⟩
  intro Q
  exact (h.2 Q).mono hCD

/-- The unnormalized local Dirichlet `H²` regularity estimate may be enlarged
to any larger constant. -/
theorem CubeDirichletH2RegularityVolumeL2.mono
    {d : ℕ} {Q : TriadicCube d} {C D : ℝ}
    (h : CubeDirichletH2RegularityVolumeL2 Q C)
    (hCD : C ≤ D) :
    CubeDirichletH2RegularityVolumeL2 Q D := by
  refine ⟨h.1.trans hCD, ?_⟩
  intro u f hf hweak
  rcases h.2 u f hf hweak with ⟨H, hH⟩
  refine ⟨H, ?_⟩
  exact hH.trans
    (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))

/-- The dimension-uniform unnormalized Dirichlet `H²` regularity estimate may
be enlarged to any larger constant. -/
theorem CubeDirichletH2RegularityVolumeL2InDimension.mono
    {d : ℕ} {C D : ℝ}
    (h : CubeDirichletH2RegularityVolumeL2InDimension d C)
    (hCD : C ≤ D) :
    CubeDirichletH2RegularityVolumeL2InDimension d D := by
  refine ⟨h.1.trans hCD, ?_⟩
  intro Q
  exact (h.2 Q).mono hCD

end

end Homogenization
