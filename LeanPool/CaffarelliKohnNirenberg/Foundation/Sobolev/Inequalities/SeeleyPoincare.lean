/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyGradient
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Lp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import Mathlib.Analysis.Convex.Measure

/-!
# Seeley Poincare

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

noncomputable section

def seeleyUnitEuclideanBall : Set (Vec 3) :=
  euclideanBall (0 : Vec 3) 1

private theorem seeleyVecEuclideanNorm_eq_l2 (x : Vec 3) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [vecEuclideanNorm, vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem seeleyVecEuclideanNorm_add_le (x y : Vec 3) :
    vecEuclideanNorm (x + y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  rw [seeleyVecEuclideanNorm_eq_l2, seeleyVecEuclideanNorm_eq_l2,
    seeleyVecEuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem seeleyUnitEuclideanBall_open :
    IsOpen seeleyUnitEuclideanBall := by
  change IsOpen {x : Vec 3 | euclideanSqDist x 0 < (1 : ℝ) ^ 2}
  exact isOpen_lt (contDiff_euclideanSqDist_left (0 : Vec 3)).continuous
    continuous_const

private theorem seeleyUnitEuclideanBall_bounded :
    IsBoundedDomain seeleyUnitEuclideanBall := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx i
  have hx' : vecEuclideanNorm x < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  exact (abs_apply_le_vecEuclideanNorm x i).trans hx'.le

private theorem seeleyUnitEuclideanBall_convex :
    Convex ℝ seeleyUnitEuclideanBall := by
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  rcases hz with ⟨a, b, ha, hb, hab, habz⟩
  have hx' : vecEuclideanNorm x < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  have hy' : vecEuclideanNorm y < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
  simp only [sub_zero]
  rw [← habz]
  calc
    vecEuclideanNorm (a • x + b • y) ≤
        vecEuclideanNorm (a • x) + vecEuclideanNorm (b • y) :=
      seeleyVecEuclideanNorm_add_le _ _
    _ = a * vecEuclideanNorm x + b * vecEuclideanNorm y := by
      rw [vecEuclideanNorm_smul, vecEuclideanNorm_smul,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ < a * 1 + b * 1 := by
      by_cases hapos : 0 < a
      · exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx' hapos)
          (mul_le_mul_of_nonneg_left hy'.le hb)
      · have ha0 : a = 0 := le_antisymm (not_lt.mp hapos) ha
        have hbpos : 0 < b := by linarith only [hab, ha0]
        exact add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_left hx'.le ha)
          (mul_lt_mul_of_pos_left hy' hbpos)
    _ = 1 := by simp [hab]

theorem seeleyUnitEuclideanBall_domain :
    IsOpenBoundedConvexDomain seeleyUnitEuclideanBall :=
  ⟨seeleyUnitEuclideanBall_open, seeleyUnitEuclideanBall_bounded,
    seeleyUnitEuclideanBall_convex⟩

private theorem seeleyNorm_le_vecEuclideanNorm (x : Vec 3) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

private theorem seeleyUnitSphere_subset_frontier {x : Vec 3}
    (hx : vecEuclideanNorm x = 1) :
    x ∈ frontier seeleyUnitEuclideanBall := by
  have hnorm : ‖x‖ ≤ 1 := by
    simpa [hx] using (seeleyNorm_le_vecEuclideanNorm x)
  have hcl : x ∈ closure seeleyUnitEuclideanBall := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (1 / 2) (ε / 2)
    have hδ : 0 < δ := lt_min (by norm_num) (by linarith only [hε])
    have hδle : δ ≤ 1 / 2 := min_le_left _ _
    have hδeps : δ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith only [hε])
    refine ⟨(1 - δ) • x, ?_, ?_⟩
    · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
      simp only [sub_zero]
      rw [vecEuclideanNorm_smul, hx, abs_of_nonneg]
      · linarith only [hδ]
      · linarith only [hδle]
    · rw [dist_eq_norm]
      have heq : x - (1 - δ) • x = δ • x := by
        calc
          x - (1 - δ) • x = (1 : ℝ) • x - (1 - δ) • x := by simp
          _ = (1 - (1 - δ)) • x := by
            rw [← one_smul ℝ x, ← sub_smul]
          _ = δ • x := by ring_nf
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      have hδeps' : δ * 1 < ε := by simpa using hδeps
      exact (mul_le_mul_of_nonneg_left hnorm hδ.le).trans_lt hδeps'
  have hint : x ∉ interior seeleyUnitEuclideanBall := by
    rw [seeleyUnitEuclideanBall_open.interior_eq]
    intro h
    have h' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp h
    have h'' : vecEuclideanNorm x < 1 := by
      simpa only [sub_zero] using h'
    exact (ne_of_lt h'') hx
  exact ⟨hcl, hint⟩

private theorem seeleyUnitSphere_null :
    volume {x : Vec 3 | vecEuclideanNorm x = 1} = 0 := by
  apply measure_mono_null (fun x hx => seeleyUnitSphere_subset_frontier hx)
  exact seeleyUnitEuclideanBall_convex.addHaar_frontier volume

theorem euclideanClosedBall_one_ae_eq_euclideanBall :
    euclideanClosedBall (0 : Vec 3) 1 =ᵐ[volume] euclideanBall (0 : Vec 3) 1 := by
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null
      (fun x hx => by
        have hle := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
          (by norm_num)).mp hx.1
        have hnotlt : ¬vecEuclideanNorm x < 1 := by
          intro hlt
          exact hx.2 ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
            (by simpa only [sub_zero] using hlt))
        exact le_antisymm (by simpa only [sub_zero] using hle) (le_of_not_gt hnotlt))
    exact seeleyUnitSphere_null
  · have hsub : euclideanBall (0 : Vec 3) 1 \
        euclideanClosedBall (0 : Vec 3) 1 ⊆ (∅ : Set (Vec 3)) := by
      intro x hx
      have hxnot : x ∉ euclideanClosedBall (0 : Vec 3) 1 := hx.2
      have hxle : x ∈ euclideanClosedBall (0 : Vec 3) 1 :=
        (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2
          (((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx.1).le)
      exact (hxnot hxle).elim
    exact measure_mono_null hsub measure_empty

noncomputable def euclideanBallPoincareConstant : ℝ≥0∞ :=
  let A : ℝ :=
    (MeasureTheory.volume seeleyUnitEuclideanBall).toReal⁻¹ *
      (((2 * Classical.choose
        seeleyUnitEuclideanBall_domain.isBoundedDomain) ^ 3) / (3 : ℝ))
  let B : ℝ :=
    (3 : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec 3) 1)).toReal *
      (4 * Classical.choose seeleyUnitEuclideanBall_domain.isBoundedDomain)
  ENNReal.ofReal (9 * A ^ 2 * B ^ 2)

theorem euclideanBall_value_energy_poincare
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) :
    ∫⁻ x in euclideanBall (0 : Vec 3) 1,
        ENNReal.ofReal |v x - MeasureTheory.average
          (MeasureTheory.volume.restrict (euclideanBall (0 : Vec 3) 1)) v| ^ 2 ∂volume ≤
      euclideanBallPoincareConstant *
        ∫⁻ y in euclideanBall (0 : Vec 3) 1,
          ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
  let U : Set (Vec 3) := seeleyUnitEuclideanBall
  let hU := seeleyUnitEuclideanBall_domain
  let _ : IsFiniteMeasure (volumeOn U) := hU.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume U).toReal := by
    have hpos : 0 < volume U := hU.isOpen.measure_pos volume ⟨0, by
      change (0 : Vec 3) ∈ euclideanBall (0 : Vec 3) 1
      exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2 (by
        norm_num [vecEuclideanNorm, vecNormSq, vecDot])⟩
    exact ENNReal.toReal_pos hpos.ne' hU.isBoundedDomain.volume_lt_top.ne
  have hcompact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  have hvint : IntegrableOn v U := by
    exact (hv.continuous.continuousOn.integrableOn_compact hcompact).mono_set
      subset_closure
  have hfdcont : Continuous (fderiv ℝ v) :=
    hv.continuous_fderiv (by norm_num)
  have hfdint : IntegrableOn (fun x => ‖fderiv ℝ v x‖ ^ 2) U := by
    exact (hfdcont.norm.pow 2).continuousOn.integrableOn_compact hcompact |>.mono_set
      subset_closure
  have hgradint : IntegrableOn
      (fun x => ‖classicalGradient v x‖ ^ 2) U := by
    have hc : Continuous (classicalGradient v) := by
      apply continuous_pi
      intro i
      simpa only [classicalGradient_apply] using
        (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact (hc.norm.pow 2).continuousOn.integrableOn_compact hcompact |>.mono_set
      subset_closure
  have hfdle :
      ∫ x in U, ‖fderiv ℝ v x‖ ^ 2 ∂volume ≤
        9 * ∫ x in U, ‖classicalGradient v x‖ ^ 2 ∂volume := by
    have hmono :
        (fun x => ‖fderiv ℝ v x‖ ^ 2) ≤ᵐ[volume.restrict U]
          (fun x => 9 * ‖classicalGradient v x‖ ^ 2) :=
      Filter.Eventually.of_forall (fun x => by
        have h := seeley_fderiv_norm_le_three_classicalGradient v x
        have hs := (sq_le_sq₀ (norm_nonneg (fderiv ℝ v x)) (by positivity)).2 h
        nlinarith only [hs])
    calc
      _ ≤ ∫ x in U, 9 * ‖classicalGradient v x‖ ^ 2 ∂volume :=
        MeasureTheory.integral_mono_ae hfdint
          ((hgradint.const_mul 9).congr (Filter.Eventually.of_forall
            (fun x => by ring))) hmono
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  have hP := integral_rpow_norm_sub_integralAverage_le_bound_of_isOpenBoundedConvexDomain
    hU hvint hv (by norm_num : (1 : ℝ) < 2) hvol
  let A : ℝ :=
    (volume U).toReal⁻¹ *
      (((2 * Classical.choose hU.isBoundedDomain) ^ 3) / (3 : ℝ))
  let B : ℝ :=
    (3 : ℝ) * (volume (Metric.ball (0 : Vec 3) 1)).toReal *
      (4 * Classical.choose hU.isBoundedDomain)
  have hP' :
      ∫ x in U, |v x - integralAverage U v| ^ (2 : ℝ) ∂volume ≤
        A ^ 2 * (B ^ 2 *
          ∫ x in U, ‖fderiv ℝ v x‖ ^ (2 : ℝ) ∂volume) := by
    convert hP using 1
    simp [A, B, U, mul_assoc]
  have hreal :
      ∫ x in U, |v x - integralAverage U v| ^ 2 ∂volume ≤
        9 * A ^ 2 * B ^ 2 *
          ∫ x in U, ‖classicalGradient v x‖ ^ 2 ∂volume := by
    calc
      _ = ∫ x in U, |v x - integralAverage U v| ^ (2 : ℝ) ∂volume := by
        congr 1
        funext x
        simp only [Real.rpow_two]
      _ ≤ A ^ 2 * (B ^ 2 *
          ∫ x in U, ‖fderiv ℝ v x‖ ^ 2 ∂volume) := hP'
      _ ≤ A ^ 2 * (B ^ 2 *
          (9 * ∫ x in U, ‖classicalGradient v x‖ ^ 2 ∂volume)) := by
        have hfdle' :
            ∫ x in U, ‖fderiv ℝ v x‖ ^ (2 : ℝ) ∂volume ≤
              9 * ∫ x in U, ‖classicalGradient v x‖ ^ 2 ∂volume := by
          simpa only [Real.rpow_two] using hfdle
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfdle' (by positivity)) (by positivity)
      _ = _ := by ring
  have hleftint : IntegrableOn
      (fun x => |v x - integralAverage U v| ^ 2) U := by
    have hc : Continuous (fun x => |v x - integralAverage U v| ^ 2) :=
      (hv.continuous.sub continuous_const).abs.pow 2
    exact (hc.continuousOn.integrableOn_compact hcompact).mono_set subset_closure
  have hleft_eq :
      ∫⁻ x in U, ENNReal.ofReal |v x - integralAverage U v| ^ 2 ∂volume =
        ENNReal.ofReal (∫ x in U, |v x - integralAverage U v| ^ 2 ∂volume) := by
    calc
      _ = ∫⁻ x in U, ENNReal.ofReal (|v x - integralAverage U v| ^ 2) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [] with x
        rw [ENNReal.ofReal_pow (abs_nonneg _)]
      _ = _ := (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hleftint
        (ae_restrict_of_ae (Filter.Eventually.of_forall
          (fun x => sq_nonneg (|v x - integralAverage U v|))))).symm
  have hgrad_eq :
      ∫⁻ x in U, ENNReal.ofReal (‖classicalGradient v x‖ ^ 2) ∂volume =
        ENNReal.ofReal (∫ x in U, ‖classicalGradient v x‖ ^ 2 ∂volume) := by
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgradint
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun x => sq_nonneg (‖classicalGradient v x‖))))).symm
  calc
    ∫⁻ x in U, ENNReal.ofReal |v x - integralAverage U v| ^ 2 ∂volume =
        ENNReal.ofReal (∫ x in U, |v x - integralAverage U v| ^ 2 ∂volume) := hleft_eq
    _ ≤ ENNReal.ofReal (9 * A ^ 2 * B ^ 2 *
          ∫ x in U, ‖classicalGradient v x‖ ^ 2 ∂volume) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = euclideanBallPoincareConstant *
        ∫⁻ x in U, ENNReal.ofReal (‖classicalGradient v x‖ ^ 2) ∂volume := by
      rw [hgrad_eq, euclideanBallPoincareConstant]
      dsimp [A, B]
      rw [ENNReal.ofReal_mul (by positivity)]

end
end CKN
