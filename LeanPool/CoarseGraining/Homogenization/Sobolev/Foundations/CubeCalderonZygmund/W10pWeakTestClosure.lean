/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit
public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Definitions

/-! # W10p Weak Test Closure -/

@[expose] public section

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

private theorem tendsto_eLpNorm_two_of_tendsto_eLpNorm_finiteMeasure
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (p : FiniteLpExponent) (hp : 2 ≤ p.exponent)
    {F : ℕ → Vec d → ℝ} {G : Vec d → ℝ}
    (hF : ∀ n, MemLp (F n) p.exponent (volume.restrict U))
    (hG : MemLp G p.exponent (volume.restrict U))
    (hTendsto : Tendsto
      (fun n => eLpNorm (fun x => F n x - G x) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    Tendsto
      (fun n => eLpNorm (fun x => F n x - G x) 2 (volume.restrict U))
      atTop (nhds 0) := by
  let μ : Measure (Vec d) := volume.restrict U
  have hdiff_meas : ∀ n, AEStronglyMeasurable (fun x => F n x - G x) μ := by
    intro n
    exact (hF n).aestronglyMeasurable.sub hG.aestronglyMeasurable
  have hp_real : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / p.exponent.toReal := by
    have hp_two : (2 : ℝ≥0∞).toReal ≤ p.exponent.toReal :=
      (ENNReal.toReal_le_toReal (by norm_num) p.lt_top.ne).mpr hp
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by norm_num) hp_two
  have hbound : ∀ n,
      eLpNorm (fun x => F n x - G x) 2 μ ≤
        eLpNorm (fun x => F n x - G x) p.exponent μ *
          μ Set.univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / p.exponent.toReal) := by
    intro n
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hdiff_meas n)
  have hfactor_ne_top :
      μ Set.univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / p.exponent.toReal) ≠ ∞ := by
    refine (ENNReal.rpow_lt_top_of_nonneg hp_real ?_).ne
    exact (measure_lt_top μ Set.univ).ne
  have hscaled : Tendsto
      (fun n => eLpNorm (fun x => F n x - G x) p.exponent μ *
        μ Set.univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / p.exponent.toReal))
      atTop (nhds 0) := by
    change Tendsto
      (fun n => eLpNorm (fun x => F n x - G x) p.exponent (volume.restrict U) *
        (volume.restrict U) Set.univ ^
          (1 / (2 : ℝ≥0∞).toReal - 1 / p.exponent.toReal))
      atTop (nhds 0)
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const hTendsto (Or.inr hfactor_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hscaled (fun _ => zero_le) hbound

private theorem integral_vecDot_eq_sum_integral_coord
    {d : ℕ} {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : ∀ i : Fin d, MemScalarL2 U (fun x => F x i))
    (hG : ∀ i : Fin d, MemScalarL2 U (fun x => G x i)) :
    ∫ x in U, vecDot (F x) (G x) ∂volume =
      ∑ i : Fin d, ∫ x in U, F x i * G x i ∂volume := by
  calc
    ∫ x in U, vecDot (F x) (G x) ∂volume =
        ∫ x in U, ∑ i : Fin d, F x i * G x i ∂volume := by
          simp only [vecDot]
    _ = ∑ i : Fin d, ∫ x in U, F x i * G x i ∂volume := by
      rw [integral_finsetSum]
      intro i _
      exact (hF i).integrable_mul (hG i)

/-- Extend a smooth compactly supported weak-divergence identity to every
zero-trace `W^{1,p}` test on a finite-measure domain when `p ≥ 2`. -/
theorem weak_divergence_identity_of_w10p
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (p : FiniteLpExponent) (hp : 2 ≤ p.exponent)
    (w : H1Function U) (h : Vec d → Vec d) (hh : MemVectorL2 U h)
    (sigma0 : ℝ)
    (hweak : ∀ phi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) phi →
      HasCompactSupport phi → tsupport phi ⊆ U →
      sigma0 * ∫ x in U, vecDot (w.grad x) (euclideanGradient phi x) ∂volume =
        -∫ x in U, vecDot (h x) (euclideanGradient phi x) ∂volume)
    (v : W10pFunction U p.exponent) :
    sigma0 * ∫ x in U, vecDot (w.grad x) (v.grad x) ∂volume =
      -∫ x in U, vecDot (h x) (v.grad x) ∂volume := by
  let Dv : Vec d → Vec d := v.grad
  let Dvn : ℕ → Vec d → Vec d := fun n => euclideanGradient (v.approx n)
  have hDvn_mem_p : ∀ n i, MemLp (fun x => Dvn n x i) p.exponent
      (volume.restrict U) := by
    intro n i
    have hcont : Continuous (fun x => (fderiv ℝ (v.approx n) x) (basisVec i)) := by
      simpa using
        (v.approx_smooth n).continuous_fderiv (by simp) |>.clm_apply continuous_const
    have hsupp : HasCompactSupport
        (fun x => (fderiv ℝ (v.approx n) x) (basisVec i)) := by
      simpa using (v.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i)
    simpa [Dvn, euclideanGradient, euclideanCoordDeriv] using
      (hcont.memLp_of_hasCompactSupport hsupp).restrict U
  have hDv_mem_p : ∀ i, MemLp (fun x => Dv x i) p.exponent (volume.restrict U) := by
    intro i
    simpa [Dv] using v.gradMemLp i
  have hDvn_mem_two : ∀ n i, MemScalarL2 U (fun x => Dvn n x i) := by
    intro n i
    exact (hDvn_mem_p n i).mono_exponent hp
  have hDv_mem_two : ∀ i, MemScalarL2 U (fun x => Dv x i) := by
    intro i
    exact (hDv_mem_p i).mono_exponent hp
  have hDvn_to_Dv_two : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => Dvn n x i - Dv x i) 2 (volume.restrict U))
      atTop (nhds 0) := by
    intro i
    apply tendsto_eLpNorm_two_of_tendsto_eLpNorm_finiteMeasure p hp
      (fun n => hDvn_mem_p n i) (hDv_mem_p i)
    simpa [Dvn, Dv, euclideanGradient, euclideanCoordDeriv] using
      v.tendsto_approx_grad i
  have hDvn_to_Dv_l2 : ∀ i, Tendsto
      (fun n => toScalarL2 (hDvn_mem_two n i)) atTop
        (nhds (toScalarL2 (hDv_mem_two i))) := by
    intro i
    exact tendsto_toScalarL2_of_tendsto_eLpNorm
      (fun n => hDvn_mem_two n i) (hDv_mem_two i) (hDvn_to_Dv_two i)
  have hw_pair : ∀ i, Tendsto
      (fun n => ∫ x in U, w.grad x i * Dvn n x i ∂volume)
      atTop (nhds (∫ x in U, w.grad x i * Dv x i ∂volume)) := by
    intro i
    exact tendsto_integral_mul_of_tendsto_toScalarL2
      (w.gradMemL2 i) (fun n => hDvn_mem_two n i) (hDv_mem_two i)
      (hDvn_to_Dv_l2 i)
  have hh_coord : ∀ i, MemScalarL2 U (fun x => h x i) := by
    intro i
    exact memScalarL2_coord_of_memVectorL2 hh i
  have hh_pair : ∀ i, Tendsto
      (fun n => ∫ x in U, h x i * Dvn n x i ∂volume)
      atTop (nhds (∫ x in U, h x i * Dv x i ∂volume)) := by
    intro i
    exact tendsto_integral_mul_of_tendsto_toScalarL2
      (hh_coord i) (fun n => hDvn_mem_two n i) (hDv_mem_two i)
      (hDvn_to_Dv_l2 i)
  have hw_pair_vec : Tendsto
      (fun n => ∫ x in U, vecDot (w.grad x) (Dvn n x) ∂volume)
      atTop (nhds (∫ x in U, vecDot (w.grad x) (Dv x) ∂volume)) := by
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => hw_pair i)
    rw [show
      (fun n => ∫ x in U, vecDot (w.grad x) (Dvn n x) ∂volume) =
        fun n => ∑ i : Fin d, ∫ x in U, w.grad x i * Dvn n x i ∂volume by
      funext n
      exact integral_vecDot_eq_sum_integral_coord (fun i => w.gradMemL2 i)
        (fun i => hDvn_mem_two n i)]
    rw [show
      ∫ x in U, vecDot (w.grad x) (Dv x) ∂volume =
        ∑ i : Fin d, ∫ x in U, w.grad x i * Dv x i ∂volume by
      exact integral_vecDot_eq_sum_integral_coord (fun i => w.gradMemL2 i) hDv_mem_two]
    exact hsum
  have hh_pair_vec : Tendsto
      (fun n => ∫ x in U, vecDot (h x) (Dvn n x) ∂volume)
      atTop (nhds (∫ x in U, vecDot (h x) (Dv x) ∂volume)) := by
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => hh_pair i)
    rw [show
      (fun n => ∫ x in U, vecDot (h x) (Dvn n x) ∂volume) =
        fun n => ∑ i : Fin d, ∫ x in U, h x i * Dvn n x i ∂volume by
      funext n
      exact integral_vecDot_eq_sum_integral_coord hh_coord
        (fun i => hDvn_mem_two n i)]
    rw [show
      ∫ x in U, vecDot (h x) (Dv x) ∂volume =
        ∑ i : Fin d, ∫ x in U, h x i * Dv x i ∂volume by
      exact integral_vecDot_eq_sum_integral_coord hh_coord hDv_mem_two]
    exact hsum
  have hleft : Tendsto
      (fun n => sigma0 * ∫ x in U, vecDot (w.grad x) (Dvn n x) ∂volume)
      atTop (nhds (sigma0 * ∫ x in U, vecDot (w.grad x) (Dv x) ∂volume)) :=
    hw_pair_vec.const_mul sigma0
  have hright : Tendsto
      (fun n => -∫ x in U, vecDot (h x) (Dvn n x) ∂volume)
      atTop (nhds (-∫ x in U, vecDot (h x) (Dv x) ∂volume)) :=
    hh_pair_vec.neg
  have hseq :
      (fun n => sigma0 * ∫ x in U, vecDot (w.grad x) (Dvn n x) ∂volume) =
        fun n => -∫ x in U, vecDot (h x) (Dvn n x) ∂volume := by
    funext n
    exact hweak (v.approx n) (v.approx_smooth n) (v.approx_hasCompactSupport n)
      (v.approx_support_subset n)
  exact tendsto_nhds_unique (hleft.congr' (EventuallyEq.of_eq hseq)) hright

end CubeCalderonZygmund

end

end Homogenization
