/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerDatum
public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.CompactSmoothL2Bounds
import LeanPool.NavierStokesAndEuler.Euler.GevreyCompactProduct
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! The actual compact base datum has factorial bounds uniform in the
small transverse parameter. All constants use the fixed cutoff only. -/

@[expose] public section


noncomputable section

namespace EulerBaseDatum

open Set Filter ContinuousLinearMap MeasureTheory EulerSmoothLimit EulerVectorCalculus
  EulerSpatialCutoffs EulerGevrey EulerGevreyFunctions EulerLpTranslation
      EulerOperatorGevreyCalculus
  EulerMeanBoundary EulerMeanCutoffCurl EulerPacketPiola
open scoped ContDiff Topology

theorem coordinate_norm_le (i : Fin 3) : ‖(EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  change ‖x i‖ ≤ 1*‖x‖
  simpa only [one_mul] using PiLp.norm_apply_le x i

theorem coordinate_bound_on_ball (i : Fin 3) (x : Space) (hx : ‖x‖ ≤ 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y : Space => y i) x‖ ≤ 2*majorant 256 0 n := by
  apply (linear_bound_on_ball (EuclideanSpace.proj i) 2 256 (by
      norm_num) (by norm_num) x hx n).trans
  exact mul_le_mul_of_nonneg_right (by nlinarith [coordinate_norm_le i])
    (majorant_nonneg 256 (by norm_num) 0 n)

theorem linear_coordinate_bound_on_ball (L : Space →L[ℝ] Space) (i : Fin 3)
    (x : Space) (hx : ‖x‖ ≤ 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => L y i) x‖ ≤ (2*‖L‖)*majorant 256 0 n := by
  have hL : ‖(EuclideanSpace.proj i).comp L‖ ≤ ‖L‖ := by
    apply (opNorm_comp_le _ _).trans
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right (coordinate_norm_le i) (norm_nonneg L))
  apply (linear_bound_on_ball ((EuclideanSpace.proj i).comp L) 2 256
    (by norm_num) (by norm_num) x hx n).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (majorant_nonneg 256 (by norm_num) 0 n)

theorem linearPotential_bound (L : Space →L[ℝ] Space) (i : Fin 3)
    (x : Space) (hx : ‖x‖ ≤ 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (linearPotential L i) x‖ ≤ (24*‖L‖)*majorant 256 0 n := by
  let f : Space → ℝ := fun y => y (i+1)*L y (i+2)
  let g : Space → ℝ := fun y => y (i+2)*L y (i+1)
  have hs (a b : Fin 3) : ContDiff ℝ ∞ (fun y : Space => y a*L y b) :=
    (EuclideanSpace.proj a : Space →L[ℝ] ℝ).contDiff.mul
      ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp L.contDiff)
  have hp (a b : Fin 3) :
      ‖iteratedFDeriv ℝ n (fun y : Space => y a*L y b) x‖ ≤ (12*‖L‖)*majorant 256 0 n := by
    have h := product_bound_at (fun y : Space => y a) (fun y => L y b)
      (EuclideanSpace.proj a : Space →L[ℝ] ℝ).contDiff
      ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp L.contDiff)
      256 2 (2*‖L‖) (by norm_num) (by norm_num) (by positivity) x
      (coordinate_bound_on_ball a x hx) (linear_coordinate_bound_on_ball L b x hx) n
    convert h using 1
    ring
  have hfg : ‖iteratedFDeriv ℝ n (f-g) x‖ ≤ (24*‖L‖)*majorant 256 0 n := by
    rw [iteratedFDeriv_sub_apply ((hs (i+1) (i+2)).contDiffAt.of_le (by simp))
      ((hs (i+2) (i+1)).contDiffAt.of_le (by simp))]
    exact (norm_sub_le _ _).trans ((add_le_add (hp (i+1) (i+2)) (hp (i+2) (i+1))).trans_eq (by
        ring))
  change ‖iteratedFDeriv ℝ n ((-1/3 : ℝ) • (f-g)) x‖ ≤ _
  have hfgsm : ContDiff ℝ ∞ (f-g) := (hs (i+1) (i+2)).sub (hs (i+2) (i+1))
  rw [iteratedFDeriv_const_smul_apply (a := (-1/3 : ℝ)) (f := f-g)
    (hfgsm.contDiffAt.of_le (by simp)),norm_smul]
  exact (mul_le_mul_of_nonneg_right (by norm_num : ‖(-1/3 : ℝ)‖ ≤ 1)
    (norm_nonneg _)).trans (by simpa only [one_mul] using hfg)

/-- Cutoff amplitude, given by `(9*(1+3/EulerGevreyCutoff.bumpMass)^2)^3`. -/
def cutoffAmplitude : ℝ := (9*(1+3/EulerGevreyCutoff.bumpMass)^2)^3

theorem cutoffAmplitude_nonneg : 0 ≤ cutoffAmplitude := by unfold cutoffAmplitude; positivity

/-- Potential amplitude, given by `3*cutoffAmplitude*(24*‖L‖)`. -/
def potentialAmplitude (L : Space →L[ℝ] Space) : ℝ := 3*cutoffAmplitude*(24*‖L‖)

theorem potentialAmplitude_nonneg (L : Space →L[ℝ] Space) : 0 ≤ potentialAmplitude L := by
  unfold potentialAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) cutoffAmplitude_nonneg) (by positivity)

theorem potential_bound (L : Space →L[ℝ] Space) (i : Fin 3) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (potential L i) x‖ ≤ potentialAmplitude L*majorant 256 0 n := by
  exact compact_product_bound outerCutoff (linearPotential L i) outerCutoff_contDiff
    (contDiff_linearPotential L i) (Metric.closedBall 0 2) outerCutoff_support
    256 cutoffAmplitude (24*‖L‖) (by norm_num) cutoffAmplitude_nonneg (by positivity)
    outerCutoff_gevrey (fun y hy => linearPotential_bound L i y
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)) n x

/-- Vector potential, given by `∑ i : Fin 3, potential L i x • EuclideanSpace.single i 1`. -/
def vectorPotential (L : Space →L[ℝ] Space) (x : Space) : Space :=
  ∑ i : Fin 3, potential L i x • EuclideanSpace.single i 1

@[simp] theorem vectorPotential_apply (L : Space →L[ℝ] Space) (x : Space) (i : Fin 3) :
    vectorPotential L x i=potential L i x := by
  fin_cases i <;> simp [vectorPotential,Fin.sum_univ_three]

theorem vectorPotential_smooth (L : Space →L[ℝ] Space) : ContDiff ℝ ∞ (vectorPotential L) :=
  ContDiff.sum (fun i _ => (potential_smooth L i).smul contDiff_const)

/-- Coordinate embedding, given by `(ContinuousLinearMap.id ℝ ℝ).smulRight
(EuclideanSpace.single i 1)`. -/
def coordinateEmbedding (i : Fin 3) : ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)

theorem coordinateEmbedding_norm (i : Fin 3) : ‖coordinateEmbedding i‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  change ‖x • (EuclideanSpace.single i 1 : Space)‖ ≤ 1*‖x‖
  simp [norm_smul]

theorem vectorPotential_bound (L : Space →L[ℝ] Space) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (vectorPotential L) x‖ ≤ (3*potentialAmplitude L)*majorant 256 0 n := by
  unfold vectorPotential
  have hs (i : Fin 3) : ContDiff ℝ ∞ (fun y => potential L i y • (EuclideanSpace.single i 1 :
      Space)) :=
    (potential_smooth L i).smul contDiff_const
  rw [iteratedFDeriv_fun_sum_apply
    (f := fun i y => potential L i y • (EuclideanSpace.single i 1 : Space))
    (u := Finset.univ) (fun i _ => (hs i).contDiffAt.of_le (by simp))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, potentialAmplitude L*majorant 256 0 n := by
      apply Finset.sum_le_sum
      intro i _
      exact contraction_bound (coordinateEmbedding i) (coordinateEmbedding_norm i)
        (potential L i) (potential_smooth L i) 256 (potentialAmplitude L)
        (by norm_num) (potentialAmplitude_nonneg L) 0 (potential_bound L i) n x
    _ = _ := by simp; ring

theorem velocity_eq_curlOperator (L : Space →L[ℝ] Space) :
    velocity L = fun x => curlOperator (fderiv ℝ (vectorPotential L) x) := by
  funext x
  rw [curlOperator_apply,← vectorCurl_eq_matrix _ x
    ((vectorPotential_smooth L).differentiable (by simp) x)]
  have he : (fun i x => vectorPotential L x i)=potential L := by
    funext i y
    exact vectorPotential_apply L y i
  exact congrArg (fun f => curl f x) he.symm

/-- Velocity amplitude, given by `‖curlOperator‖*(3*potentialAmplitude L*256)`. -/
def velocityAmplitude (L : Space →L[ℝ] Space) : ℝ :=
  ‖curlOperator‖*(3*potentialAmplitude L*256)

theorem velocityAmplitude_nonneg (L : Space →L[ℝ] Space) : 0 ≤ velocityAmplitude L := by
  unfold velocityAmplitude
  apply mul_nonneg
  · exact norm_nonneg curlOperator
  · exact mul_nonneg (mul_nonneg (by norm_num) (potentialAmplitude_nonneg L)) (by norm_num)

theorem velocity_sup_bound (L : Space →L[ℝ] Space) : HasSupBound (velocity L) (velocityAmplitude L)
    1024 := by
  have hp : HasSupBound (vectorPotential L) (3*potentialAmplitude L) 256 := by
    intro n x
    simpa only [majorant,Nat.add_zero,mul_assoc] using vectorPotential_bound L n x
  have hd := hp.derivative (mul_nonneg (by norm_num) (potentialAmplitude_nonneg L))
    (by norm_num : (0 : ℝ) ≤ 256)
  rw [velocity_eq_curlOperator]
  intro n x
  have h := linear_bound curlOperator (fderiv ℝ (vectorPotential L))
    ((vectorPotential_smooth L).fderiv_right (m := ∞) (by simp))
    1024 (3*potentialAmplitude L*256) 0 (fun j y => by
      simpa only [majorant,Nat.add_zero,mul_assoc,show 4*(256 : ℝ)=1024 by
          norm_num] using hd j y) n x
  simpa only [velocityAmplitude,majorant,Nat.add_zero,mul_assoc] using h

/-- Volume factor, given by `(volume (Metric.closedBall (0 : Space) 2)).toReal^(1/2 : ℝ)`. -/
def volumeFactor : ℝ := (volume (Metric.closedBall (0 : Space) 2)).toReal^(1/2 : ℝ)

theorem volumeFactor_nonneg : 0 ≤ volumeFactor := Real.rpow_nonneg (ENNReal.toReal_nonneg) _

theorem field_jet_bound (L : Space →L[ℝ] Space) :
    (field L).HasJetBound (velocityAmplitude L*volumeFactor) 1024 :=
  SmoothL2Field.hasJetBound_of_support_sup (field L) (Metric.closedBall 0 2)
    (isCompact_closedBall (0 : Space) 2).measure_lt_top.ne (velocity_support L)
    (velocityAmplitude L) 1024 (velocityAmplitude_nonneg L) (by norm_num) (velocity_sup_bound L)

end EulerBaseDatum
