/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionDifferencePDE
public import LeanPool.NavierStokesAndEuler.Euler.SobolevDifferenceEnergy

@[expose] public section

/-! The actual nonlinear viscosity-difference PDE implies a fixed squared metric energy inequality.
  -/

noncomputable section

namespace EulerCorrectionDifferenceMetric

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerSpatialSobolevInverse EulerCylinderSobolevSpace EulerCorrectionOperators
    EulerCorrectionDifference
  EulerCorrectionDifferencePDE EulerCorrectionStabilityConstants EulerSobolevTransport
  EulerSobolevMetricTransport EulerSobolevHeatGenerator EulerMetricHeatEnergy EulerSobolevL2Product
  EulerSquaredMetricStability EulerSobolevDifferenceEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The existing Sobolev normed-group instance for the literal metric difference equation. -/
local instance metricSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
/-- The existing real Sobolev module instance for the literal metric difference equation. -/
local instance metricSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual correction-difference PDE gives the quantitative squared L² metric bound, with no assumed energy inequality. -/
theorem difference_metric_deriv_bound {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (τ : T)
    (u v : SobolevSpace period (q+1)) (A : SmoothCoefficient period)
    (K : ℝ → LiftL2 period →L[ℝ] LiftL2 period) (e : ℝ → LiftL2 period)
    (t ν μ c Kb Kx Kt A0 A2 Z R : ℝ) (K' : LiftL2 period →L[ℝ] LiftL2 period)
    (hc : 0 < c) (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hKv : K t=A.operator) (hev : e t=value period (u-v))
    (hK : HasDerivAt K K' t) (he : HasDerivAt e (differenceRhs period D hq ν μ τ u v) t)
    (hKb : ‖A.operator‖ ≤ Kb) (hKx : (A.firstBound : ℝ) ≤ Kx) (hKt : ‖K'‖ ≤ Kt)
    (hA0 : ((D.linear.coefficient τ).bound : ℝ) ≤ A0)
    (hA2 : (∑ i : Fin 3, (((D.quadratic i).coefficient τ).bound : ℝ)) ≤ A2)
    (hZ : ‖D.approximation τ‖ ≤ Z) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    (hsym : ∀ x a b, ⟪A.coefficient x a,b⟫_ℝ=⟪a,A.coefficient x b⟫_ℝ)
    (hpos : ∀ x a, c^2*‖a‖^2 ≤ ⟪A.coefficient x a,a⟫_ℝ)
    (hinv : ∀ x a, A.coefficient x ((D.metric.coefficient τ).coefficient x a)=a)
    (hz : value period (D.approximation τ) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : value period u ∈ divergenceFreeSpace period D.κ D.direction)
    (hvd : value period v ∈ divergenceFreeSpace period D.κ D.direction) :
    deriv (fun s => ⟪K s (e s),e s⟫_ℝ) t ≤
      growthConstant c Kb Kx Kt (velocityBound period q Z R) (lowerConstant period q A0 A2 Z R)*
        ⟪K t (e t),e t⟫_ℝ+defectConstant Kb R*|ν-μ|^2 := by
  let d := u-v
  let top := value period (transportBilinear period hq (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation τ+u)
      d)
  let p := value period (D.pressure period hq τ u)-value period (D.pressure period hq τ v)
  let F := -value period (differenceRemainder period D hq τ u v)+
    (ν-μ) • laplacianEvaluation period (q+1) (by omega) v
  let L := lowerConstant period q A0 A2 Z R
  let V := velocityBound period q Z R
  have hr0 := (norm_nonneg u).trans hu
  have hz0 := (norm_nonneg (D.approximation τ)).trans hZ
  have ha00 := (D.linear.coefficient τ).bound.coe_nonneg.trans hA0
  have ha20 := (Finset.sum_nonneg (fun i _ => ((D.quadratic i).coefficient
    τ).bound.coe_nonneg)).trans hA2
  have hL : 0 ≤ L := lowerConstant_nonneg period q A0 A2 Z R ha00 ha20 hz0 hr0
  have hV : 0 ≤ V := velocityBound_nonneg period q Z R hz0 hr0
  have hkx0 := A.firstBound.coe_nonneg.trans hKx
  have hkb0 := (norm_nonneg A.operator).trans hKb
  have hkt0 := (norm_nonneg K').trans hKt
  have heq : differenceRhs period D hq ν μ τ u v+top+(D.metric.coefficient τ).operator p =
      F+ν • laplacianEvaluation period (q+1) (by omega) d := by
    dsimp only [differenceRhs,top,p,F,d]
    abel
  have hdiv : value period d ∈ divergenceFreeSpace period D.κ D.direction :=
    (divergenceFreeSpace period D.κ D.direction).sub_mem hud hvd
  have hpgrad : p ∈ gradientSpace period D.κ D.direction :=
    (gradientSpace period D.κ D.direction).sub_mem (D.pressure_mem_gradient period hq τ u)
      (D.pressure_mem_gradient period hq τ v)
  have hp : ⟪K t (e t),(D.metric.coefficient τ).operator p⟫_ℝ=0 := by
    rw [hKv,hev]
    exact metric_pressure_cancellation period D.κ D.direction A.coefficient (D.metric.coefficient
      τ).coefficient
      A.measurable (D.metric.coefficient τ).measurable A.bound (D.metric.coefficient τ).bound
      A.norm_bound (D.metric.coefficient τ).norm_bound hsym hinv hdiv hpgrad
  have ht : |⟪K t (e t),top⟫_ℝ| ≤ (Kx*V)*‖e t‖^2 := by
    rw [hKv,hev]
    exact difference_transport_bound period D hq τ A u v Kx Z R hKx hZ hu hsym hz hud
  have hheat : ⟪K t (e t),laplacianEvaluation period (q+1) (by omega) d⟫_ℝ ≤
      (2*Kx^2/c^2)*‖e t‖^2 := by
    rw [hKv,hev]
    exact difference_heat_bound period (by omega : 2 ≤ q+1) A d c Kx hc hKx hpos
  have hforce : ‖F‖ ≤ L*‖e t‖+|ν-μ| *(4*R) := by
    rw [hev]
    have hrem := differenceRemainder_uniform period D hq τ u v A0 A2 Z R hA0 hA2 hZ hu hv
    have hlap := (laplacianEvaluation_bound period (by omega : 2 ≤ q+1) v).trans
      (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 4))
    have hh := norm_add_le (-value period (differenceRemainder period D hq τ u v))
      ((ν-μ) • laplacianEvaluation period (q+1) (by omega) v)
    rw [norm_neg,norm_smul,Real.norm_eq_abs] at hh
    exact hh.trans (add_le_add hrem (mul_le_mul_of_nonneg_left hlap (abs_nonneg _)))
  have hcoer : c^2*‖e t‖^2 ≤ ⟪K t (e t),e t⟫_ℝ := by
    rw [hKv]
    exact coefficientOperator_coercive A.coefficient A.measurable A.bound A.norm_bound (c^2) hpos
      (e t)
  have hsymL : ∀ a b, ⟪K t a,b⟫_ℝ=⟪a,K t b⟫_ℝ := by
    rw [hKv]
    exact coefficientOperator_inner_swap A.coefficient A.measurable A.bound A.norm_bound hsym
  have hgen := metric_derivative_bound K e t ν c (Kx*V) (2*Kx^2/c^2) L |ν-μ| (4*R) K'
    (differenceRhs period D hq ν μ τ u v) top ((D.metric.coefficient τ).operator p) F
    (laplacianEvaluation period (q+1) (by omega) d) hc hν (mul_nonneg hkx0 hV) (by positivity) hL
    hK he hsymL hcoer heq hp ht hheat hforce
  have he0 : 0 ≤ ⟪K t (e t),e t⟫_ℝ := (mul_nonneg (sq_nonneg c) (sq_nonneg ‖e t‖)).trans hcoer
  have hkn : ‖K t‖ ≤ Kb := by rw [hKv]; exact hKb
  have hg : (‖K'‖+2*(Kx*V)+2*ν*(2*Kx^2/c^2)+2*‖K t‖*L+1)/c^2 ≤
      growthConstant c Kb Kx Kt V L := by
    unfold growthConstant
    apply div_le_div_of_nonneg_right _ (sq_nonneg c)
    have hh : 2*ν*(2*Kx^2/c^2) ≤ 4*Kx^2/c^2 := by
      calc
        _ = ν*(4*Kx^2/c^2) := by ring
        _ ≤ 1*(4*Kx^2/c^2) := mul_le_mul_of_nonneg_right hν1 (by positivity)
        _ = _ := one_mul _
    have hk : 2*‖K t‖*L ≤ 2*Kb*L := by
      have h := mul_le_mul_of_nonneg_right hkn (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)
      nlinarith only [h]
    have hsum := add_le_add (add_le_add (add_le_add hKt (le_refl (2*(Kx*V)))) hh) hk
    exact (add_le_add hsum (le_refl 1)).trans_eq (by ring)
  have hd : (‖K t‖*(4*R))^2 ≤ defectConstant Kb R := by
    have h := mul_le_mul_of_nonneg_right hkn (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hr0)
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg (K t))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hr0)) h 2
  exact hgen.trans (add_le_add (mul_le_mul_of_nonneg_right hg he0)
    (mul_le_mul_of_nonneg_right hd (sq_nonneg _)))

end EulerCorrectionDifferenceMetric
