/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.BanachSpace

/-!
# Two-sided parabolic parametrices

This file isolates the functional-analytic step in the manifold Schauder
construction.  If `P : U → F` has an approximate inverse `Q : F → U`, and
both defects

`1 - P Q : F → F` and `1 - Q P : U → U`

have norm strictly below one, their Neumann series correct `Q` to the unique
bounded inverse of `P`.  The resulting solution operator carries an explicit
Schauder bound.

The statement is deliberately between two different Banach spaces: in the
geometric application `U` is the higher parabolic tensor space (including the
initial trace) and `F` is the forcing/initial-data space.  No assumptions are
not hidden here: the two small-error inequalities are precisely what the
finite atlas, cutoffs, frozen Euclidean heat operators, and commutator bounds
must establish.
-/

@[expose] public noncomputable section
namespace RicciFlow
namespace AnalyticPDE
namespace LinearParabolicParametrix

variable {U F : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The forcing-space defect of an approximate inverse. -/
def rightError (P : U →L[ℝ] F) (Q : F →L[ℝ] U) : F →L[ℝ] F :=
  1 - P.comp Q

/-- The solution-space defect of an approximate inverse. -/
def leftError (P : U →L[ℝ] F) (Q : F →L[ℝ] U) : U →L[ℝ] U :=
  1 - Q.comp P

/-- A two-sided approximate inverse whose two defects are contractions. -/
structure Data (P : U →L[ℝ] F) where
  /-- The uncorrected local-to-global parametrix. -/
  approxInverse : F →L[ℝ] U
  /-- Smallness of `1 - P Q` on the forcing space. -/
  rightError_lt_one : ‖rightError P approxInverse‖ < 1
  /-- Smallness of `1 - Q P` on the solution space. -/
  leftError_lt_one : ‖leftError P approxInverse‖ < 1

/-- A one-sided approximate inverse.  This is the exact datum needed for
existence: injectivity may be proved independently, for example by an energy
estimate for the geometric heat operator. -/
structure RightData (P : U →L[ℝ] F) where
  /-- The uncorrected local-to-global right parametrix. -/
  approxRightInverse : F →L[ℝ] U
  /-- Smallness of the forcing-space defect `1 - P Q`. -/
  rightError_lt_one : ‖rightError P approxRightInverse‖ < 1

/-- The Neumann inverse of `1 - A` for a strict contraction `A`. -/
def neumannInverse (A : U →L[ℝ] U) (hA : ‖A‖ < 1) : U →L[ℝ] U :=
  ↑(Units.oneSub A hA)⁻¹

/-- The Neumann inverse is a right inverse of `1 - A`. -/
theorem oneSub_comp_neumannInverse
    (A : U →L[ℝ] U) (hA : ‖A‖ < 1) :
    (1 - A) * neumannInverse A hA = 1 := by
  show (1 - A) * (↑(Units.oneSub A hA)⁻¹) = 1
  rw [← Units.val_oneSub A hA]
  exact (Units.oneSub A hA).mul_inv

/-- The Neumann inverse is a left inverse of `1 - A`. -/
theorem neumannInverse_comp_oneSub
    (A : U →L[ℝ] U) (hA : ‖A‖ < 1) :
    neumannInverse A hA * (1 - A) = 1 := by
  show (↑(Units.oneSub A hA)⁻¹) * (1 - A) = 1
  rw [← Units.val_oneSub A hA]
  exact (Units.oneSub A hA).inv_mul

/-- Quantitative geometric-series bound for the Neumann inverse. -/
theorem norm_neumannInverse_le
    (A : U →L[ℝ] U) (hA : ‖A‖ < 1) :
    ‖neumannInverse A hA‖ ≤ (1 - ‖A‖)⁻¹ := by
  have hsum : neumannInverse A hA = ∑' n : ℕ, A ^ n := rfl
  rw [hsum]
  have hb := tsum_geometric_le_of_norm_lt_one A hA
  have h1 : ‖(1 : U →L[ℝ] U)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le
  linarith

/-- Neumann correction of a one-sided right parametrix. -/
def rightSolutionOperator (P : U →L[ℝ] F) (D : RightData P) : F →L[ℝ] U :=
  D.approxRightInverse.comp
    (neumannInverse (rightError P D.approxRightInverse)
      D.rightError_lt_one)

/-- The corrected one-sided parametrix is an exact right inverse. -/
theorem comp_rightSolutionOperator (P : U →L[ℝ] F) (D : RightData P) :
    P.comp (rightSolutionOperator P D) = ContinuousLinearMap.id ℝ F := by
  have hInv := oneSub_comp_neumannInverse
    (rightError P D.approxRightInverse) D.rightError_lt_one
  have hPQ : 1 - rightError P D.approxRightInverse =
      P.comp D.approxRightInverse := by
    simp [rightError]
  rw [hPQ] at hInv
  ext f
  have hf := congrArg (fun L : F →L[ℝ] F => L f) hInv
  simpa [rightSolutionOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply] using hf

/-- The one-sided correction constructs a solution for every forcing datum. -/
theorem rightSolutionOperator_solves
    (P : U →L[ℝ] F) (D : RightData P) (f : F) :
    P (rightSolutionOperator P D f) = f := by
  have h := congrArg (fun L : F →L[ℝ] F => L f)
    (comp_rightSolutionOperator P D)
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Surjectivity supplied by a small right parametrix defect. -/
theorem surjective_of_rightData (P : U →L[ℝ] F) (D : RightData P) :
    Function.Surjective P := by
  intro f
  exact ⟨rightSolutionOperator P D f, rightSolutionOperator_solves P D f⟩

/-- Operator-norm estimate for the one-sided corrected solution map. -/
theorem norm_rightSolutionOperator_le
    (P : U →L[ℝ] F) (D : RightData P) :
    ‖rightSolutionOperator P D‖ ≤
      ‖D.approxRightInverse‖ *
        (1 - ‖rightError P D.approxRightInverse‖)⁻¹ := by
  calc
    ‖rightSolutionOperator P D‖
        ≤ ‖D.approxRightInverse‖ *
            ‖neumannInverse (rightError P D.approxRightInverse)
              D.rightError_lt_one‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖D.approxRightInverse‖ *
          (1 - ‖rightError P D.approxRightInverse‖)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (norm_neumannInverse_le
          (rightError P D.approxRightInverse) D.rightError_lt_one)
        (norm_nonneg D.approxRightInverse)

/-- Pointwise Schauder estimate furnished by a one-sided parametrix. -/
theorem norm_rightSolutionOperator_apply_le
    (P : U →L[ℝ] F) (D : RightData P) (f : F) :
    ‖rightSolutionOperator P D f‖ ≤
      ‖D.approxRightInverse‖ *
        (1 - ‖rightError P D.approxRightInverse‖)⁻¹ * ‖f‖ := by
  exact (rightSolutionOperator P D).le_opNorm f |>.trans
    (mul_le_mul_of_nonneg_right
      (norm_rightSolutionOperator_le P D) (norm_nonneg f))

/-- Right-corrected solution operator `Q (1 - (1 - P Q))⁻¹`. -/
def solutionOperator (P : U →L[ℝ] F) (D : Data P) : F →L[ℝ] U :=
  D.approxInverse.comp
    (neumannInverse (rightError P D.approxInverse) D.rightError_lt_one)

/-- The corrected parametrix is a right inverse of the parabolic operator. -/
theorem comp_solutionOperator (P : U →L[ℝ] F) (D : Data P) :
    P.comp (solutionOperator P D) = ContinuousLinearMap.id ℝ F := by
  have hInv := oneSub_comp_neumannInverse
    (rightError P D.approxInverse) D.rightError_lt_one
  have hPQ : 1 - rightError P D.approxInverse = P.comp D.approxInverse := by
    simp [rightError]
  rw [hPQ] at hInv
  ext f
  have hf := congrArg (fun L : F →L[ℝ] F => L f) hInv
  simpa [solutionOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply] using hf

/-- Left-corrected solution operator `(1 - (1 - Q P))⁻¹ Q`. -/
def leftSolutionOperator (P : U →L[ℝ] F) (D : Data P) : F →L[ℝ] U :=
  (neumannInverse (leftError P D.approxInverse) D.leftError_lt_one).comp
    D.approxInverse

/-- The left-corrected parametrix is a left inverse of the parabolic operator. -/
theorem leftSolutionOperator_comp (P : U →L[ℝ] F) (D : Data P) :
    (leftSolutionOperator P D).comp P = ContinuousLinearMap.id ℝ U := by
  have hInv := neumannInverse_comp_oneSub
    (leftError P D.approxInverse) D.leftError_lt_one
  have hQP : 1 - leftError P D.approxInverse = D.approxInverse.comp P := by
    simp [leftError]
  rw [hQP] at hInv
  ext u
  have hu := congrArg (fun L : U →L[ℝ] U => L u) hInv
  simpa [leftSolutionOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply] using hu

/-- The right- and left-corrected parametrices coincide. -/
theorem solutionOperator_eq_leftSolutionOperator
    (P : U →L[ℝ] F) (D : Data P) :
    solutionOperator P D = leftSolutionOperator P D := by
  ext f
  have hr := congrArg (fun L : F →L[ℝ] F => L f)
    (comp_solutionOperator P D)
  have hl := congrArg (fun L : U →L[ℝ] U => L (solutionOperator P D f))
    (leftSolutionOperator_comp P D)
  have hr' : P (solutionOperator P D f) = f := by
    simpa [ContinuousLinearMap.comp_apply] using hr
  have hl' : leftSolutionOperator P D (P (solutionOperator P D f)) =
      solutionOperator P D f := by
    simpa [ContinuousLinearMap.comp_apply] using hl
  exact hl'.symm.trans (congrArg (fun u => leftSolutionOperator P D u) hr')

/-- The corrected solution operator is also a left inverse. -/
theorem solutionOperator_comp (P : U →L[ℝ] F) (D : Data P) :
    (solutionOperator P D).comp P = ContinuousLinearMap.id ℝ U := by
  rw [solutionOperator_eq_leftSolutionOperator P D]
  exact leftSolutionOperator_comp P D

/-- The parametrix constructs a solution of `P u = f` for every datum. -/
theorem solutionOperator_solves
    (P : U →L[ℝ] F) (D : Data P) (f : F) :
    P (solutionOperator P D f) = f := by
  have h := congrArg (fun L : F →L[ℝ] F => L f)
    (comp_solutionOperator P D)
  simpa [ContinuousLinearMap.comp_apply] using h

/-- A solution of `P u = f` is uniquely determined. -/
theorem eq_solutionOperator_of_apply_eq
    (P : U →L[ℝ] F) (D : Data P) {u : U} {f : F}
    (hu : P u = f) :
    u = solutionOperator P D f := by
  have hleft := congrArg (fun L : U →L[ℝ] U => L u)
    (solutionOperator_comp P D)
  simpa [ContinuousLinearMap.comp_apply, hu] using hleft.symm

/-- Existence and uniqueness for the operator equation supplied by a
two-sided small-error parametrix. -/
theorem existsUnique_apply_eq
    (P : U →L[ℝ] F) (D : Data P) (f : F) :
    ∃! u : U, P u = f := by
  refine ⟨solutionOperator P D f, solutionOperator_solves P D f, ?_⟩
  intro u hu
  exact eq_solutionOperator_of_apply_eq P D hu

/-- Operator-norm Schauder estimate for the corrected parametrix. -/
theorem norm_solutionOperator_le
    (P : U →L[ℝ] F) (D : Data P) :
    ‖solutionOperator P D‖ ≤
      ‖D.approxInverse‖ * (1 - ‖rightError P D.approxInverse‖)⁻¹ := by
  calc
    ‖solutionOperator P D‖
        ≤ ‖D.approxInverse‖ *
            ‖neumannInverse (rightError P D.approxInverse) D.rightError_lt_one‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖D.approxInverse‖ * (1 - ‖rightError P D.approxInverse‖)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (norm_neumannInverse_le
          (rightError P D.approxInverse) D.rightError_lt_one)
        (norm_nonneg D.approxInverse)

/-- Pointwise Schauder estimate for the unique solution. -/
theorem norm_solutionOperator_apply_le
    (P : U →L[ℝ] F) (D : Data P) (f : F) :
    ‖solutionOperator P D f‖ ≤
      ‖D.approxInverse‖ * (1 - ‖rightError P D.approxInverse‖)⁻¹ * ‖f‖ := by
  exact (solutionOperator P D).le_opNorm f |>.trans
    (mul_le_mul_of_nonneg_right (norm_solutionOperator_le P D) (norm_nonneg f))

/-- The parabolic operator is a continuous linear equivalence whenever it has
a two-sided small-error parametrix. -/
def continuousLinearEquiv (P : U →L[ℝ] F) (D : Data P) : U ≃L[ℝ] F where
  toFun := P
  invFun := solutionOperator P D
  map_add' := P.map_add
  map_smul' := P.map_smul
  left_inv u := by
    have h := congrArg (fun L : U →L[ℝ] U => L u)
      (solutionOperator_comp P D)
    simpa [ContinuousLinearMap.comp_apply] using h
  right_inv f := solutionOperator_solves P D f
  continuous_toFun := P.continuous
  continuous_invFun := (solutionOperator P D).continuous

end LinearParabolicParametrix
end AnalyticPDE
end RicciFlow
