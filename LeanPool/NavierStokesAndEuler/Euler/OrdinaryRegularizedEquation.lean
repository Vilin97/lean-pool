/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySmoothingOperator
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.HilbertQuadraticFlow
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryAdvectionLimit
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryTransportCancellation

/-! A genuine global L² solution of the symmetric regularized Euler
equation. The vector field is a bounded bilinear map and its actual
L² energy vanishes by noncompact transport cancellation. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanClassical Finset
open scoped ContDiff Topology

theorem advection_add_left (A B C : SmoothL2Field Space) :
    advectionField (addField A B) C=addField (advectionField A C) (advectionField B C) := by
  apply field_ext
  exact funext (fun x => by simp only [advectionField_field,addField_field,map_add])

theorem advection_add_right (A B C : SmoothL2Field Space) :
    advectionField A (addField B C)=addField (advectionField A B) (advectionField A C) := by
  apply field_ext
  funext x
  have he : (addField B C).field=B.field+C.field := rfl
  simp only [advectionField_field,addField_field,he,
    fderiv_add (B.smooth.differentiable (by
        simp) x) (C.smooth.differentiable (by simp) x),add_apply]

theorem advection_smul_left (c : ℝ) (A B : SmoothL2Field Space) :
    advectionField (scaleField c A) B=scaleField c (advectionField A B) := by
  apply field_ext
  exact funext (fun x => by simp only [advectionField_field,scaleField_field,map_smul])

theorem advection_smul_right (c : ℝ) (A B : SmoothL2Field Space) :
    advectionField A (scaleField c B)=scaleField c (advectionField A B) := by
  apply field_ext
  exact funext (fun x => by
    simp only [advectionField_field,scaleField_field,scaleField_fderiv,smul_apply])

namespace SmoothingOperator

variable (S : SmoothingOperator)

/-- Advection linear, bundling `toFun`, `map_add`, `map_smul`, `map_add` and the required
compatibility proofs. -/
def advectionLinear : L2 →ₗ[ℝ] L2 →ₗ[ℝ] L2 where
  toFun u :=
    { toFun v := (advectionField (S.field u) (S.field v)).toLp
      map_add' v w := by rw [S.field_add,advection_add_right,toLp_addField]
      map_smul' c v := by rw [S.field_smul,advection_smul_right,scaleField_toLp]; rfl }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change (advectionField (S.field (u+v)) (S.field w)).toLp =
      (advectionField (S.field u) (S.field w)).toLp +
        (advectionField (S.field v) (S.field w)).toLp
    rw [S.field_add,advection_add_left,toLp_addField]
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    change (advectionField (S.field (c • u)) (S.field v)).toLp =
      c • (advectionField (S.field u) (S.field v)).toLp
    rw [S.field_smul,advection_smul_left,scaleField_toLp]

/-- Advection cost, given by `S.pointwiseCost*‖S.jetMap 1‖`. -/
def advectionCost : ℝ := S.pointwiseCost*‖S.jetMap 1‖

theorem advectionLinear_bound (u v : L2) :
    ‖S.advectionLinear u v‖ ≤ S.advectionCost*‖u‖*‖v‖ := by
  change ‖(advectionField (S.field u) (S.field v)).toLp‖ ≤ _
  apply (advection_norm_velocity (S.field u) (S.field v) _ (S.field_pointwise u)).trans
  rw [← (S.field v).derivative.norm_jetLp_zero,(S.field v).norm_derivative_jetLp]
  apply (mul_le_mul_of_nonneg_left (S.field_jet_norm v 1)
    (mul_nonneg S.pointwiseCost_nonneg (norm_nonneg u))).trans_eq
  dsimp [advectionCost]
  ring

/-- Advection, given by `S.advectionLinear.mkContinuous₂ S.advectionCost
S.advectionLinear_bound`. -/
def advection : L2 →L[ℝ] L2 →L[ℝ] L2 :=
  S.advectionLinear.mkContinuous₂ S.advectionCost S.advectionLinear_bound

@[simp] theorem advection_apply (u v : L2) :
    S.advection u v=(advectionField (S.field u) (S.field v)).toLp := rfl

/-- Quadratic, given by `(ContinuousLinearMap.compL ℝ L2 L2 L2 (-S.op)).comp S.advection`. -/
def quadratic : L2 →L[ℝ] L2 →L[ℝ] L2 :=
  (ContinuousLinearMap.compL ℝ L2 L2 L2 (-S.op)).comp S.advection

@[simp] theorem quadratic_apply (u v : L2) :
    S.quadratic u v= -S.op (advectionField (S.field u) (S.field v)).toLp := rfl

theorem field_divergence (u : L2) (x : Space) : divergence (S.field u).field x=0 :=
  solenoidal_representative_divergence _ (S.solenoidal u) _ (S.field u).smooth
    (by simpa only [field_toLp] using (S.field u).toLp_ae) x

theorem quadratic_energy (u : L2) : ⟪u,S.quadratic u u⟫_ℝ=0 := by
  rw [quadratic_apply,inner_neg_right,← S.symmetric,← field_toLp]
  rw [real_inner_comm,advection_inner_zero (S.field u) (S.field u) (S.field_divergence u),neg_zero]

theorem exists_global (u₀ : L2) :
    ∃ u : ℝ → L2, u 0=u₀ ∧ (∀ t, HasDerivAt u (S.quadratic (u t) (u t)) t) ∧
      ∀ t, ‖u t‖=‖u₀‖ :=
  EulerHilbertQuadraticFlow.exists_global_quadratic S.quadratic S.quadratic_energy u₀

end SmoothingOperator
end EulerOrdinarySobolev
