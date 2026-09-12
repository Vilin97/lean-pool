/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySmoothLimit
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! Passing the actual nonlinear advection and Helmholtz pressure to a
strong ordinary Sobolev limit. Only a uniform H³ bound is used in the
product estimate; pressure convergence is a consequence. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerSmoothSobolev EulerVolterraConvolution
open scoped ContDiff Topology

theorem jetLp_fieldSub (A B : SmoothL2Field Space) (n : ℕ) :
    (fieldSub A B).jetLp n=A.jetLp n-B.jetLp n := by
  have he : (fieldSub A B).field=A.field-B.field := funext (fieldSub_field A B)
  apply Lp.ext
  filter_upwards [(fieldSub A B).jetLp_ae n,A.jetLp_ae n,B.jetLp_ae n,
    Lp.coeFn_sub (A.jetLp n) (B.jetLp n)] with x ha hb hc hd
  rw [ha,he]
  have hh := iteratedFDeriv_sub_apply (i := n) (x := x)
    (A.smooth.contDiffAt.of_le (by simp)) (B.smooth.contDiffAt.of_le (by simp))
  exact hh.trans ((congrArg₂ (fun u v : Space [×n]→L[ℝ] Space => u-v) hb hc).symm.trans hd.symm)

theorem advection_difference (A B : SmoothL2Field Space) :
    fieldSub (advectionField A A) (advectionField B B) =
      addField (advectionField (fieldSub A B) A) (advectionField B (fieldSub A B)) := by
  apply field_ext
  funext x
  have he : (fieldSub A B).field=A.field-B.field := funext (fieldSub_field A B)
  simp only [fieldSub_field,addField_field,advectionField_field]
  rw [he,fderiv_sub (A.smooth.differentiable (by simp) x) (B.smooth.differentiable (by simp) x)]
  simp only [map_sub,sub_apply]
  abel

theorem advection_norm_velocity (U W : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖U.field x‖ ≤ K) :
    ‖(advectionField U W).toLp‖ ≤ K*‖W.derivative.toLp‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(advectionField U W).toLp_ae,W.derivative.toLp_ae] with x ha hw
  rw [ha,hw,advectionField_field]
  exact ((fderiv ℝ W.field x).le_opNorm (U.field x)).trans
    ((mul_le_mul_of_nonneg_left (hK x) (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem advection_sub_norm (A B : SmoothL2Field Space) (G K : ℝ)
    (hG : ∀ x, ‖fderiv ℝ A.field x‖ ≤ G) (hK : ∀ x, ‖B.field x‖ ≤ K) :
    ‖(advectionField A A).toLp-(advectionField B B).toLp‖ ≤
      G*‖A.toLp-B.toLp‖+K*‖A.jetLp 1-B.jetLp 1‖ := by
  rw [← toLp_fieldSub,advection_difference,toLp_addField]
  apply (norm_add_le _ _).trans
  have h := add_le_add (advection_norm_gradient (fieldSub A B) A G hG)
    (advection_norm_velocity B (fieldSub A B) K hK)
  simpa only [toLp_fieldSub,← norm_jetLp_zero (fieldSub A B).derivative,
    norm_derivative_jetLp,jetLp_fieldSub] using h

variable {T : ℝ}

/-- Advection path, given by `fieldPath (fun t => advectionField (A t) (A t))
(advectionField_continuous A hA)`. -/
def advectionPath (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : C(Icc (0 : ℝ) T,L2) :=
  fieldPath (fun t => advectionField (A t) (A t)) (advectionField_continuous A hA)

/-- Projected rhs path, given by `fieldPath (fun t => projectedRhs (A t))
(projectedRhs_continuous A hA)`. -/
def projectedRhsPath (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : C(Icc (0 : ℝ) T,L2) :=
  fieldPath (fun t => projectedRhs (A t)) (projectedRhs_continuous A hA)

/-- Pressure path, given by `fieldPath (fun t => pressureField (A t)) (pressureField_continuous
A hA)`. -/
def pressurePath (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : C(Icc (0 : ℝ) T,L2) :=
  fieldPath (fun t => pressureField (A t)) (pressureField_continuous A hA)

theorem projectedRhsPath_eq (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    projectedRhsPath A hA=(-solenoidalProjection).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (advectionPath A hA) := by
  apply ContinuousMap.ext
  intro t
  exact projectedRhs_toLp (A t)

theorem pressurePath_eq (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    pressurePath A hA=(solenoidalProjection-ContinuousLinearMap.id ℝ L2).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (advectionPath A hA) := by
  apply ContinuousMap.ext
  intro t
  exact pressureField_toLp (A t)

theorem advectionPath_sub_norm (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) (G K : ℝ) (hG0 : 0 ≤ G) (hK0 : 0 ≤ K)
    (hG : ∀ t x, ‖fderiv ℝ (A t).field x‖ ≤ G) (hK : ∀ t x, ‖(B t).field x‖ ≤ K) :
    ‖advectionPath A hA-advectionPath B hB‖ ≤
      G*‖fieldPath A hA-fieldPath B hB‖+K*‖jetPath A hA 1-jetPath B hB 1‖ := by
  apply (ContinuousMap.norm_le _ (add_nonneg (mul_nonneg hG0 (norm_nonneg _))
    (mul_nonneg hK0 (norm_nonneg _)))).mpr
  intro t
  apply (advection_sub_norm (A t) (B t) G K (hG t) (hK t)).trans
  exact add_le_add (mul_le_mul_of_nonneg_left
    ((fieldPath A hA-fieldPath B hB).norm_coe_le_norm t) hG0)
    (mul_le_mul_of_nonneg_left ((jetPath A hA 1-jetPath B hB 1).norm_coe_le_norm t) hK0)

namespace SmoothLimitData

variable {A : ℕ → Icc (0 : ℝ) T → SmoothL2Field Space}
  {hA : ∀ k n, Continuous (fun t => (A k t).jetLp n)} (L : SmoothLimitData A hA)

theorem advectionPath_convergence (hT : 0 ≤ T) (M : ℝ)
    (hb : ∀ k t, tensorNorm 3 (A k t) ≤ M) :
    Tendsto (fun k => advectionPath (A k) (hA k)) atTop (𝓝 (advectionPath L.field
        L.field_continuous)) := by
  have hM : 0 ≤ M := (tensorNorm_nonneg 3 (A 0 ⟨0,le_rfl,hT⟩)).trans (hb 0 _)
  let G := (9*smoothEmbeddingConstant)*M
  let K := (13*smoothEmbeddingConstant)*M
  have hG0 : 0 ≤ G := mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) hM
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) hM
  have hG (k : ℕ) (t : Icc (0 : ℝ) T) (x : Space) : ‖fderiv ℝ (A k t).field x‖ ≤ G := by
    have h := real_smooth_fderiv_le_H3 3 (A k t).field (A k t).smooth
      (fun j _ => (A k t).integrable j) x
    rw [← tensorNorm_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hb k t)
      (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg))
  have hK (t : Icc (0 : ℝ) T) (x : Space) : ‖(L.field t).field x‖ ≤ K := by
    apply wordBound_pointwise
    intro n hn w
    exact (wordBound_tensorNorm 3 (L.field t) n (by omega) w).trans (L.tensorNorm_bound 3 M hb t)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h0 : Tendsto (fun k => ‖fieldPath (A k) (hA k)-fieldPath L.field L.field_continuous‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp L.fieldPath_convergence
  have h1 : Tendsto (fun k => ‖jetPath (A k) (hA k) 1-jetPath L.field L.field_continuous 1‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp (L.jetPath_convergence 1)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => advectionPath_sub_norm (A k) L.field (hA k) L.field_continuous G K hG0 hK0 (hG k) hK)
  simpa only [mul_zero,add_zero] using (h0.const_mul G).add (h1.const_mul K)

theorem projectedRhsPath_convergence (hT : 0 ≤ T) (M : ℝ)
    (hb : ∀ k t, tensorNorm 3 (A k t) ≤ M) :
    Tendsto (fun k => projectedRhsPath (A k) (hA k)) atTop (𝓝 (projectedRhsPath L.field
        L.field_continuous)) := by
  simp only [projectedRhsPath_eq]
  exact ((-solenoidalProjection).compLeftContinuous ℝ (Icc (0 : ℝ) T)).continuous.tendsto _
    |>.comp (L.advectionPath_convergence hT M hb)

theorem pressurePath_convergence (hT : 0 ≤ T) (M : ℝ)
    (hb : ∀ k t, tensorNorm 3 (A k t) ≤ M) :
    Tendsto (fun k => pressurePath (A k) (hA k)) atTop (𝓝 (pressurePath L.field
        L.field_continuous)) := by
  simp only [pressurePath_eq]
  exact ((solenoidalProjection-ContinuousLinearMap.id ℝ L2).compLeftContinuous ℝ
    (Icc (0 : ℝ) T)).continuous.tendsto _ |>.comp (L.advectionPath_convergence hT M hb)

end SmoothLimitData
end EulerOrdinarySobolev
