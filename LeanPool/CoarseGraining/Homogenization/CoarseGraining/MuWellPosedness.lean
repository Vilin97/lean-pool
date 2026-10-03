/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientField
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.HilbertMinimization
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! # Mu Well Posedness -/

@[expose] public section

namespace Homogenization

/-!
This file records the Hilbert-space well-posedness package behind the doubled
`\mu` problem.

The notes minimize a uniformly convex quadratic energy over the affine space
`P + \Lpoto(U) × \Lsolo(U)` inside the Hilbert space `L²(U; \R^{2d})`. At the
current stage of the formalization, we package that setup abstractly: an
ambient real Hilbert space, a closed subspace modeling `\mathcal{H}(U)`, a
linear embedding of the parameter `P ∈ \R^{2d}`, and a coercive symmetric
bilinear form.

This does not replace the note's definition of `\mu(U,P;\a)`. It isolates the
analytic theorem surface needed to turn the doubled minimization problem into a
canonical linear minimizer map `P ↦ X_P`.
-/

noncomputable section

section OperatorEnergy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The bilinear form induced by a continuous operator on a real Hilbert
space. -/
noncomputable def energyBilinOfOperator (T : H →L[ℝ] H) :
    H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ).comp T

@[simp] theorem energyBilinOfOperator_apply (T : H →L[ℝ] H) (X Y : H) :
    energyBilinOfOperator T X Y = inner ℝ (T X) Y := by
  simp [energyBilinOfOperator, innerSL_apply_apply]

theorem energyBilinOfOperator_symm (T : H →L[ℝ] H)
    (hT : LinearMap.IsSymmetric (T : H →ₗ[ℝ] H)) :
    ∀ X Y : H, energyBilinOfOperator T X Y = energyBilinOfOperator T Y X := by
  intro X Y
  calc
    energyBilinOfOperator T X Y = inner ℝ (T X) Y := by
      simp
    _ = inner ℝ X (T Y) := by
      simpa using hT.apply_clm X Y
    _ = inner ℝ (T Y) X := by
      rw [real_inner_comm]
    _ = energyBilinOfOperator T Y X := by
      simp

end OperatorEnergy

/--
Black-box Hilbert-space data for the doubled `\mu` problem on `U`.

The intended future instantiation is:
- `ambient = L²(U; \R^{2d})` or an equivalent Hilbert realization;
- `hilbertSubspace = \Lpoto(U) × \Lsolo(U)`;
- `constantField P =` the constant field with value `P`;
- `energyBilin X Y = \fint_U X \cdot \mathbf{A}(\a) Y`.
-/
structure MuHilbertProblem {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  /-- The ambient Hilbert space modeling `L²(U; \R^{2d})`. -/
  ambient : Type*
  instNormedAddCommGroup : NormedAddCommGroup ambient
  instInnerProductSpace : InnerProductSpace ℝ ambient
  instCompleteSpace : CompleteSpace ambient
  /-- The closed subspace modeling `\mathcal{H}(U) = \Lpoto(U) × \Lsolo(U)`. -/
  hilbertSubspace : ClosedSubmodule ℝ ambient
  /-- The embedding of the parameter `P ∈ \R^{2d}` as a constant ambient field. -/
  constantField : BlockVec d →L[ℝ] ambient
  /-- The averaged doubled energy bilinear form. -/
  energyBilin : ambient →L[ℝ] ambient →L[ℝ] ℝ
  /-- Symmetry of the energy bilinear form. -/
  energySymm : ∀ X Y : ambient, energyBilin X Y = energyBilin Y X
  /-- Coercivity of the energy bilinear form. -/
  energyCoercive : IsCoercive energyBilin

attribute [instance] MuHilbertProblem.instNormedAddCommGroup
attribute [instance] MuHilbertProblem.instInnerProductSpace
attribute [instance] MuHilbertProblem.instCompleteSpace

namespace MuHilbertProblem

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- The canonical minimizer in the affine space `P + \mathcal{H}(U)`. -/
noncomputable def minimizerMap (M : MuHilbertProblem U a) :
    BlockVec d →L[ℝ] M.ambient :=
  parameterAffineMinimizerMap
    (K := M.hilbertSubspace)
    (B := M.energyBilin)
    (hB := M.energyCoercive)
    (ι := M.constantField)

@[simp] theorem minimizerMap_apply (M : MuHilbertProblem U a) (P : BlockVec d) :
    M.minimizerMap P =
      affineMinimizerMap M.hilbertSubspace M.energyBilin M.energyCoercive (M.constantField P) :=
  rfl

/-- The correction from `P` to the minimizer lies in `\mathcal{H}(U)`. -/
theorem sub_minimizerMap_apply_mem (M : MuHilbertProblem U a) (P : BlockVec d) :
    M.minimizerMap P - M.constantField P ∈ M.hilbertSubspace := by
  change affineMinimizerMap M.hilbertSubspace M.energyBilin M.energyCoercive (M.constantField P) -
      M.constantField P ∈ M.hilbertSubspace
  exact
    sub_affineMinimizerMap_apply_mem M.hilbertSubspace M.energyBilin M.energyCoercive
      (M.constantField P)

/-- First variation of the minimized energy against all directions in
`\mathcal{H}(U)`. -/
theorem minimizerMap_firstVariation (M : MuHilbertProblem U a) (P : BlockVec d)
    (Y : M.hilbertSubspace.toSubmodule) :
    M.energyBilin (M.minimizerMap P) Y = 0 := by
  simpa [minimizerMap] using
    parameterAffineMinimizerMap_firstVariation
      (K := M.hilbertSubspace)
      (B := M.energyBilin)
      (hB := M.energyCoercive)
      (ι := M.constantField)
      (p := P)
      (w := Y)

/-- The minimized quadratic energy attached to the Hilbert-space package. -/
noncomputable def muCandidate (M : MuHilbertProblem U a) (P : BlockVec d) : ℝ :=
  quadraticEnergy M.energyBilin (M.minimizerMap P)

/-- The canonical minimizer minimizes the quadratic energy over the whole affine
space `P + \mathcal{H}(U)`. -/
theorem muCandidate_le_quadraticEnergy (M : MuHilbertProblem U a) (P : BlockVec d)
    (X : M.ambient) (hX : X - M.constantField P ∈ M.hilbertSubspace) :
    M.muCandidate P ≤ quadraticEnergy M.energyBilin X := by
  simpa [muCandidate, minimizerMap] using
    parameterAffineMinimizerMap_minimizes_quadraticEnergy
      (K := M.hilbertSubspace)
      (hB := M.energyCoercive)
      (h_symm := M.energySymm)
      (ι := M.constantField)
      (p := P)
      (y := X)
      hX

/-- Uniqueness of the Hilbert minimizer in the affine correction space. -/
theorem eq_minimizerMap_of_quadraticEnergy_le_muCandidate
    (M : MuHilbertProblem U a) (P : BlockVec d)
    (X : M.ambient) (hX : X - M.constantField P ∈ M.hilbertSubspace)
    (hle : quadraticEnergy M.energyBilin X ≤ M.muCandidate P) :
    X = M.minimizerMap P := by
  simpa [muCandidate, minimizerMap] using
    eq_affineMinimizerMap_of_quadraticEnergy_le
      (K := M.hilbertSubspace)
      (hB := M.energyCoercive)
      (h_symm := M.energySymm)
      (x := M.constantField P)
      (y := X)
      hX
      hle

end MuHilbertProblem

/--
A realization of the doubled `\mu` problem in the actual ambient Hilbert space
`L²(U; \R^{2d})`.

This keeps the abstract minimization engine of `MuHilbertProblem`, but now the
ambient type is fixed to the concrete Hilbert-valued `L²` space built in the
Sobolev layer.
-/
structure MuHilbertRealization {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  /-- The closed correction space `\Lpoto(U) × \Lsolo(U)` inside the concrete
  Hilbert ambient space. -/
  correctionSpace : MuCorrectionSpaceData U
  /-- The constant field embedding of `P ∈ \R^{2d}` into `L²(U; \R^{2d})`. -/
  constantField : BlockVec d →L[ℝ] HilbertBlockL2 U
  /-- The averaged doubled energy bilinear form on the concrete ambient space. -/
  energyBilin : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ
  /-- Symmetry of the energy bilinear form. -/
  energySymm : ∀ X Y : HilbertBlockL2 U, energyBilin X Y = energyBilin Y X
  /-- Coercivity of the energy bilinear form. -/
  energyCoercive : IsCoercive energyBilin

namespace MuHilbertRealization

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- Package the doubled `\mu` problem from a symmetric coercive operator on
the concrete Hilbert ambient space `L²(U; \R^{2d})`. -/
noncomputable def ofOperator
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (correctionSpace : MuCorrectionSpaceData U)
    (operator : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U)
    (operatorSymm : LinearMap.IsSymmetric (operator : HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U))
    (operatorCoercive : IsCoercive (energyBilinOfOperator operator)) :
    MuHilbertRealization U a where
  correctionSpace := correctionSpace
  constantField := blockVecToHilbertBlockL2Const (U := U)
  energyBilin := energyBilinOfOperator operator
  energySymm := energyBilinOfOperator_symm operator operatorSymm
  energyCoercive := operatorCoercive

/-- Forget the concrete ambient realization and view it as an abstract
`MuHilbertProblem`. -/
noncomputable def toProblem (M : MuHilbertRealization U a) : MuHilbertProblem U a where
  ambient := HilbertBlockL2 U
  instNormedAddCommGroup := inferInstance
  instInnerProductSpace := inferInstance
  instCompleteSpace := inferInstance
  hilbertSubspace := M.correctionSpace.correctionSpace
  constantField := M.constantField
  energyBilin := M.energyBilin
  energySymm := M.energySymm
  energyCoercive := M.energyCoercive

/-- The canonical minimizer map in the actual ambient Hilbert space
`L²(U; \R^{2d})`. -/
noncomputable def minimizerMap (M : MuHilbertRealization U a) :
    BlockVec d →L[ℝ] HilbertBlockL2 U :=
  MuHilbertProblem.minimizerMap M.toProblem

@[simp] theorem minimizerMap_apply (M : MuHilbertRealization U a) (P : BlockVec d) :
    M.minimizerMap P = MuHilbertProblem.minimizerMap M.toProblem P :=
  rfl

/-- The minimizer correction lies in the concrete correction space
`\Lpoto(U) × \Lsolo(U)`. -/
theorem sub_minimizerMap_apply_mem (M : MuHilbertRealization U a) (P : BlockVec d) :
    M.minimizerMap P - M.constantField P ∈ M.correctionSpace.correctionSpace := by
  exact MuHilbertProblem.sub_minimizerMap_apply_mem M.toProblem P

/-- First variation of the minimized energy against all concrete correction
directions. -/
theorem minimizerMap_firstVariation (M : MuHilbertRealization U a) (P : BlockVec d)
    (Y : M.correctionSpace.correctionSpace.toSubmodule) :
    M.energyBilin (M.minimizerMap P) Y = 0 := by
  change M.toProblem.energyBilin (MuHilbertProblem.minimizerMap M.toProblem P)
      (Y : HilbertBlockL2 U) = 0
  exact MuHilbertProblem.minimizerMap_firstVariation M.toProblem P Y

/-- The minimized quadratic energy attached to the concrete Hilbert
realization. -/
noncomputable def muCandidate (M : MuHilbertRealization U a) (P : BlockVec d) : ℝ :=
  MuHilbertProblem.muCandidate M.toProblem P

/-- The canonical minimizer minimizes the quadratic energy over the concrete
affine space `P + \Lpoto(U) × \Lsolo(U)`. -/
theorem muCandidate_le_quadraticEnergy (M : MuHilbertRealization U a) (P : BlockVec d)
    (X : HilbertBlockL2 U)
    (hX : X - M.constantField P ∈ M.correctionSpace.correctionSpace) :
    M.muCandidate P ≤ quadraticEnergy M.energyBilin X := by
  exact MuHilbertProblem.muCandidate_le_quadraticEnergy M.toProblem P X hX

/-- Uniqueness of the concrete Hilbert minimizer in the affine correction
space. -/
theorem eq_minimizerMap_of_quadraticEnergy_le_muCandidate
    (M : MuHilbertRealization U a) (P : BlockVec d)
    (X : HilbertBlockL2 U)
    (hX : X - M.constantField P ∈ M.correctionSpace.correctionSpace)
    (hle : quadraticEnergy M.energyBilin X ≤ M.muCandidate P) :
    X = M.minimizerMap P := by
  change X = M.toProblem.minimizerMap P
  exact
    MuHilbertProblem.eq_minimizerMap_of_quadraticEnergy_le_muCandidate
      M.toProblem P X hX hle

end MuHilbertRealization

end

end Homogenization
