/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.EuclideanNormalized
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.EuclideanNormalized

/-!
# The common centered-cube Calderón--Zygmund `q = 2` constant

This is the additive source-facing endpoint surface for the two Chapter 1
classical inputs.  It deliberately concerns only centered triadic cubes and
the presently formalized `q = 2` case.  The same dimension-only constant is
used for its Dirichlet and mean-zero Neumann branches.
-/

@[expose] public section

namespace Homogenization

noncomputable section

/-- The two exact centered-cube `q = 2` Calderón--Zygmund branches share the
same nonnegative dimension-only constant.  In particular, the constant is
outside every cube-scale, forcing, and supplied-solution binder. -/
def CenteredCubeCalderonZygmundQTwo (d : ℕ) (C : ℝ) : Prop :=
  CubeDirichletWeakPoissonProblem.OriginCubeDirichletCalderonZygmundQTwo d C ∧
    OriginCubeNeumannW22CalderonZygmundQTwo (d := d) C

theorem CenteredCubeCalderonZygmundQTwo.constant_nonneg
    {d : ℕ} {C : ℝ} (h : CenteredCubeCalderonZygmundQTwo d C) :
    0 ≤ C :=
  h.1.constant_nonneg

/-- Extract the exact centered-cube Dirichlet `q = 2` branch. -/
theorem CenteredCubeCalderonZygmundQTwo.dirichlet
    {d : ℕ} {C : ℝ} (h : CenteredCubeCalderonZygmundQTwo d C) :
    CubeDirichletWeakPoissonProblem.OriginCubeDirichletCalderonZygmundQTwo d C :=
  h.1

/-- Extract the exact centered-cube Neumann `q = 2` branch.  Its forcing is
centered internally and its estimate applies to every supplied mean-zero
Neumann solution. -/
theorem CenteredCubeCalderonZygmundQTwo.neumann
    {d : ℕ} {C : ℝ} (h : CenteredCubeCalderonZygmundQTwo d C) :
    OriginCubeNeumannW22CalderonZygmundQTwo (d := d) C :=
  h.2

private theorem originCube_dirichlet_calderon_zygmund_q_two_mono
    {d : ℕ} {C D : ℝ}
    (h : CubeDirichletWeakPoissonProblem.OriginCubeDirichletCalderonZygmundQTwo d C)
    (hCD : C ≤ D) :
    CubeDirichletWeakPoissonProblem.OriginCubeDirichletCalderonZygmundQTwo d D := by
  refine ⟨h.constant_nonneg.trans hCD, ?_⟩
  intro m u F hF hweak H
  refine (h.apply m u F hF hweak H).trans ?_
  exact mul_le_mul_of_nonneg_right hCD ENNReal.toReal_nonneg

private theorem originCube_neumann_calderon_zygmund_q_two_mono
    {d : ℕ} {C D : ℝ}
    (h : OriginCubeNeumannW22CalderonZygmundQTwo (d := d) C)
    (hCD : C ≤ D) :
    OriginCubeNeumannW22CalderonZygmundQTwo (d := d) D := by
  refine ⟨h.constant_nonneg.trans hCD, ?_⟩
  intro m F hF W H
  refine (h.apply m F hF W H).trans ?_
  exact mul_le_mul_of_nonneg_right hCD ENNReal.toReal_nonneg

/-- The explicit common dimension-only constant for the exact centered-cube
`q = 2` Dirichlet and Neumann branches. -/
noncomputable def centeredCubeCalderonZygmundQTwoConstant (d : ℕ) [NeZero d] : ℝ :=
  max (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact d)
    (originCubeNeumannW22CalderonZygmundConstant d)

theorem centeredCubeCalderonZygmundQTwoConstant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ centeredCubeCalderonZygmundQTwoConstant d := by
  unfold centeredCubeCalderonZygmundQTwoConstant
  exact le_max_of_le_left
    (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d)

/-- The explicit common constant simultaneously proves the exact normalized
Frobenius Dirichlet branch and the internally centered all-solutions Neumann
branch. -/
theorem centeredCubeCalderonZygmundQTwo_exact
    (d : ℕ) [NeZero d] :
    CenteredCubeCalderonZygmundQTwo d (centeredCubeCalderonZygmundQTwoConstant d) := by
  constructor
  · exact originCube_dirichlet_calderon_zygmund_q_two_mono
      (CubeDirichletWeakPoissonProblem.originCubeDirichletCalderonZygmundQTwo_exact d)
      (by
        unfold centeredCubeCalderonZygmundQTwoConstant
        exact le_max_left _ _)
  · exact originCube_neumann_calderon_zygmund_q_two_mono
      (originCubeNeumannW22CalderonZygmund_qTwo d)
      (by
        unfold centeredCubeCalderonZygmundQTwoConstant
        exact le_max_right _ _)

/-- There is one dimension-only constant for both exact centered-cube
Calderón--Zygmund `q = 2` branches. -/
theorem exists_centeredCubeCalderonZygmundQTwo
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, CenteredCubeCalderonZygmundQTwo d C :=
  ⟨centeredCubeCalderonZygmundQTwoConstant d,
    centeredCubeCalderonZygmundQTwo_exact d⟩

end

end Homogenization
