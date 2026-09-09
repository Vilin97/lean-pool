/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMatrixCoefficientAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientBounds
public import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets

@[expose] public section

/-! Bounds for the actual composition, scalar multiple and spatial derivative
of packet matrix-coefficient witnesses.  The derivative radius enlargement
occurs only in this fixed coefficient budget. -/

noncomputable section

namespace EulerPacketCylinderField.MatrixCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerBoundedFieldCalculus
  EulerPacketPointJets EulerGevrey EulerOperatorGevreyCalculus
open scoped ContDiff BoundedContinuousFunction

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

variable {T : ℝ} {a b : Domain → Space →L[ℝ] Space}

theorem comp_bound (A : MatrixCoefficient T a) (B : MatrixCoefficient T b)
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbA : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A.path) x‖ ≤ C*majorant R 0 n)
    (hbB : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath B.path) x‖ ≤ D*majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (A.comp B).path) x‖ ≤
      (3*C*D)*majorant R 0 n := by
  have he : translateCoefficientPath (A.comp B).path =
      fun v => pathCompositionMap (translateCoefficientPath A.path v) (translateCoefficientPath
        B.path v) := by
    funext v
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro y
    rfl
  rw [he]
  exact pathComposition_bound (α := Space) (K := Icc (0 : ℝ) T)
    (U := Space) (E := Space) (F := Space)
    (translateCoefficientPath A.path) (translateCoefficientPath B.path)
    A.orbit B.orbit R C D hR hC hD 0 0 hbA hbB n x

theorem smul_bound (A : MatrixCoefficient T a) (c R C : ℝ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A.path) x‖ ≤ C*majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (A.smul c).path) x‖ ≤
      (|c| * C)*majorant R 0 n := by
  have he : translateCoefficientPath (A.smul c).path = c • translateCoefficientPath A.path := by
    funext v
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro y
    rfl
  rw [he,iteratedFDeriv_const_smul_apply (A.orbit.of_le (by
    simp)).contDiffAt,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hb n x) (abs_nonneg c)).trans_eq (by ring)

theorem spatialDerivative_norm_le (A : MatrixCoefficient T a) (v : Space)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (A.spatialDerivative v).path) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (n+1) (translateCoefficientPath A.path) x‖ := by
  have he : translateCoefficientPath (A.spatialDerivative v).path =
      fun y => fderiv ℝ (translateCoefficientPath A.path) y v :=
    funext (orbitDerivativePath_translation A.path A.orbit v)
  rw [he]
  have h := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ (translateCoefficientPath A.path)) (c := v) (n := n) (x := x)
    (A.orbit.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)
  simpa only [norm_iteratedFDeriv_fderiv] using h

theorem spatialDerivative_bound (A : MatrixCoefficient T a) (v : Space) (hv : ‖v‖ ≤ 1)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A.path) x‖ ≤ C*majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (A.spatialDerivative v).path) x‖ ≤
      (C*R)*majorant (4*R) 0 n := by
  have h1 := (spatialDerivative_norm_le A v n x).trans
    (mul_le_mul_of_nonneg_left (hb (n+1) x) (norm_nonneg v))
  have h2 : ‖v‖*(C*majorant R 0 (n+1)) ≤ C*majorant R 1 n := by
    simpa only [one_mul,majorant,Nat.add_zero,Nat.zero_add] using
      mul_le_mul_of_nonneg_right hv (mul_nonneg hC (majorant_nonneg R hR 0 (n+1)))
  exact (h1.trans h2).trans ((mul_le_mul_of_nonneg_left
    (majorant_one_le_radius_four R hR n) hC).trans_eq (by ring))

theorem bound_mono_radius (A : MatrixCoefficient T a) (R S C : ℝ)
    (hR : 0 ≤ R) (hRS : R ≤ S) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A.path) x‖ ≤ C*majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath A.path) x‖ ≤ C*majorant S 0 n :=
  (hb n x).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono R S hR hRS 0 n) hC)

end EulerPacketCylinderField.MatrixCoefficient
