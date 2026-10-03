/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.HeatKernelIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.IntegralBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Product integrability for heat subordination

The heat subordination representation of the Newtonian kernel and of its first
spatial derivative integrates a Gaussian family over positive times.  The two
lemmas here supply the product integrability on `(0, ∞) × ℝ³` that licenses the
Fubini exchange, for data that is smooth with compact support.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-- A compactly supported bounded factor preserves integrability of the heat
kernel on the positive-time half-space. -/
theorem heat_kernel_mul_compact_integrable {g : Vec3 → ℝ} {y : Vec3}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ × Vec3 =>
      heatKernel (p.2-y) p.1 * g p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  let K : Set Vec3 := tsupport g
  let F : ℝ × Vec3 → ℝ := fun p => heatKernel (p.2-y) p.1 * g p.2
  have hK : IsCompact K := hgc.isCompact
  have hKmeas : MeasurableSet K := hK.measurableSet
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
  have hFmeas : AEStronglyMeasurable F
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    have hheat : Measurable (fun p : ℝ × Vec3 =>
        heatKernel (p.2-y) p.1) := by
      unfold heatKernel
      apply Measurable.ite (measurableSet_Ioi.preimage measurable_fst)
      · fun_prop
      · exact measurable_const
    have hgmeas : Measurable (fun p : ℝ × Vec3 => g p.2) :=
      hg.continuous.measurable.comp measurable_snd
    exact (hheat.mul hgmeas).aestronglyMeasurable
  have hnearBase : Integrable (fun p : ℝ × Vec3 =>
      heatKernel (p.2-y) p.1)
      ((volume.restrict (Ioc 0 1)).prod volume) := by
    have hheat := (heatKernelPlus_integrable_prod (T := 1)).swap
    have hheat' : Integrable (fun p : ℝ × Vec3 => heatKernel p.2 p.1)
        ((volume.restrict (Ioc 0 1)).prod volume) := by
      convert hheat using 1
      funext p
      symm
      exact heatKernelPlus_eq_heatKernel (show ParabolicPoint from p.swap)
    let S : ℝ × Vec3 → ℝ × Vec3 := Prod.map id (fun x : Vec3 => x-y)
    have hS : MeasurePreserving S
        ((volume.restrict (Ioc 0 1)).prod (volume : Measure Vec3))
        ((volume.restrict (Ioc 0 1)).prod volume) := by
      exact MeasurePreserving.prod
        (MeasurePreserving.id (volume.restrict (Ioc 0 1)))
        (measurePreserving_sub_right volume y)
    have hshift := (hS.integrable_comp hheat'.aestronglyMeasurable).2 hheat'
    change Integrable (fun p : ℝ × Vec3 => heatKernel (p.2-y) p.1)
      ((volume.restrict (Ioc 0 1)).prod volume) at hshift
    exact hshift
  have hnearMajor : Integrable (fun p : ℝ × Vec3 => C *
      heatKernel (p.2-y) p.1)
      ((volume.restrict (Ioc 0 1)).prod volume) := hnearBase.const_mul C
  have hnear : IntegrableOn F (Ioc 0 1 ×ˢ (Set.univ : Set Vec3))
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    change Integrable F ((volume.prod volume).restrict
      (Ioc 0 1 ×ˢ (Set.univ : Set Vec3)))
    rw [← Measure.prod_restrict]
    have hm := hFmeas.restrict (s := Ioc 0 1 ×ˢ (Set.univ : Set Vec3))
    rw [← Measure.prod_restrict] at hm
    have hm' : AEStronglyMeasurable F
        ((volume.restrict (Ioc 0 1)).prod volume) := by
      simpa only [Measure.restrict_univ] using hm
    have hi : Integrable F ((volume.restrict (Ioc 0 1)).prod volume) := by
      apply hnearMajor.mono' hm'
      filter_upwards [] with p
      by_cases hp : p.2 ∈ K
      · have hg' : ‖g p.2‖ ≤ C := hC p.2
        dsimp [F]
        change |heatKernel (p.2-y) p.1 * g p.2| ≤
          C * heatKernel (p.2-y) p.1
        rw [abs_mul]
        have hk : 0 ≤ heatKernel (p.2-y) p.1 := heatKernel_nonneg _ _
        calc
          |heatKernel (p.2-y) p.1| * |g p.2| ≤
              C * heatKernel (p.2-y) p.1 := by
            rw [abs_of_nonneg hk]
            calc
              heatKernel (p.2-y) p.1 * |g p.2| ≤
                  heatKernel (p.2-y) p.1 * C := by
                simpa only [Real.norm_eq_abs] using
                  mul_le_mul_of_nonneg_left hg' hk
              _ = C * heatKernel (p.2-y) p.1 := by ring
          _ = _ := by ring
      · have hz : g p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
        simp only [hz, mul_zero, norm_zero, ge_iff_le, F]
        exact mul_nonneg hC0 (heatKernel_nonneg _ _)
    simpa only [Measure.restrict_univ] using hi
  have ht2 : Integrable (fun t : ℝ => t ^ (-(3 : ℝ) / 2))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).integrable
  have hKone : Integrable (K.indicator (fun _ : Vec3 => (1 : ℝ))) volume := by
    apply (integrable_indicator_iff hKmeas).2
    exact integrableOn_const hK.measure_lt_top.ne
  have htailBase : Integrable (fun p : ℝ × Vec3 =>
      p.1 ^ (-(3 : ℝ) / 2) * K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2)
      ((volume.restrict (Ioi 1)).prod volume) := by
    simpa only using ht2.mul_prod hKone
  have htailMajor : Integrable (fun p : ℝ × Vec3 => C *
      (p.1 ^ (-(3 : ℝ) / 2) * K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2))
      ((volume.restrict (Ioi 1)).prod volume) := htailBase.const_mul C
  have htail : IntegrableOn F (Ioi 1 ×ˢ (Set.univ : Set Vec3))
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    change Integrable F ((volume.prod volume).restrict
      (Ioi 1 ×ˢ (Set.univ : Set Vec3)))
    have hm := hFmeas.restrict (s := Ioi 1 ×ˢ (Set.univ : Set Vec3))
    have hm' : AEStronglyMeasurable F
        ((volume.prod volume).restrict (Ioi 1 ×ˢ (Set.univ : Set Vec3))) := hm
    have hmajor' : Integrable (fun p : ℝ × Vec3 => C *
        (p.1 ^ (-(3 : ℝ) / 2) *
          K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2))
        ((volume.prod volume).restrict (Ioi 1 ×ˢ (Set.univ : Set Vec3))) := by
      rw [← Measure.prod_restrict]
      simpa only [Measure.restrict_univ] using htailMajor
    apply hmajor'.mono' hm'
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp_time
    by_cases hp : p.2 ∈ K
    · have ht : 1 < p.1 := hp_time.1
      have ht0 : 0 < p.1 := lt_trans zero_lt_one ht
      have hkernel : heatKernel (p.2-y) p.1 ≤ p.1 ^ (-(3 : ℝ) / 2) := by
        have hpref := heatKernel_le_prefactor (y := p.2-y) ht0
        rw [show 4 * Real.pi * p.1 = (4 * Real.pi) * p.1 by ring,
          Real.mul_rpow (by positivity) ht0.le] at hpref
        have hconst : (4 * Real.pi : ℝ) ^ (-(3 : ℝ) / 2) ≤ 1 := by
          have hbase : 1 ≤ (4 * Real.pi : ℝ) := by
            nlinarith only [Real.pi_gt_three]
          rw [show -(3 : ℝ) / 2 = -(3 / 2 : ℝ) by ring,
            Real.rpow_neg (by positivity)]
          exact (inv_le_one₀ (by positivity)).2
            (Real.one_le_rpow hbase (by positivity))
        calc
          heatKernel (p.2-y) p.1 ≤
              (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
                p.1 ^ (-(3 : ℝ) / 2) := hpref
          _ ≤ p.1 ^ (-(3 : ℝ) / 2) := by
            exact mul_le_of_le_one_left (by positivity) hconst
      have hg' : |g p.2| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC p.2
      rw [Real.norm_eq_abs, abs_mul, Set.indicator_of_mem hp]
      calc
        |heatKernel (p.2-y) p.1| * |g p.2| ≤
            C * p.1 ^ (-(3 : ℝ) / 2) := by
          rw [abs_of_nonneg (heatKernel_nonneg _ _)]
          calc
            heatKernel (p.2-y) p.1 * |g p.2| ≤
                p.1 ^ (-(3 : ℝ) / 2) * C :=
              mul_le_mul hkernel hg' (abs_nonneg _) (by positivity)
            _ = C * p.1 ^ (-(3 : ℝ) / 2) := by ring
        _ = C * (p.1 ^ (-(3 : ℝ) / 2) * 1) := by ring
    · have hz : g p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
      simp [F, hz, Set.indicator_of_notMem hp]
  have hall : IntegrableOn F (Ioi 0 ×ˢ (Set.univ : Set Vec3))
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
      Set.union_prod, integrableOn_union]
    exact ⟨hnear, htail⟩
  have hall' : Integrable F ((volume.prod volume).restrict
      (Ioi 0 ×ˢ (Set.univ : Set Vec3))) := hall
  rw [← Measure.prod_restrict] at hall'
  simpa only [F, Measure.restrict_univ] using hall'

/-- The spatial derivative of the heat kernel has the same compact-support
product integrability, with the sharp large-time majorant used by the heat
subordination formula. -/
theorem heat_derivative_mul_compact_integrable {g : Vec3 → ℝ} {y : Vec3}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (i : Fin 3) :
    Integrable (fun p : ℝ × Vec3 =>
      heatKernelSpaceDerivative (p.2-y) p.1 i * g p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  let K : Set Vec3 := tsupport g
  let F : ℝ × Vec3 → ℝ := fun p =>
    heatKernelSpaceDerivative (p.2-y) p.1 i * g p.2
  have hK : IsCompact K := hgc.isCompact
  have hKmeas : MeasurableSet K := hK.measurableSet
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
  have hFmeas : AEStronglyMeasurable F
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    have hheat : Measurable (fun p : ℝ × Vec3 =>
        heatKernel (p.2-y) p.1) := by
      unfold heatKernel
      apply Measurable.ite (measurableSet_Ioi.preimage measurable_fst)
      · fun_prop
      · exact measurable_const
    have hderiv : Measurable (fun p : ℝ × Vec3 =>
        heatKernelSpaceDerivative (p.2-y) p.1 i) := by
      unfold heatKernelSpaceDerivative
      apply Measurable.ite (measurableSet_Ioi.preimage measurable_fst)
      · have hcoord : Measurable (fun p : ℝ × Vec3 => (p.2-y) i) :=
          (measurable_pi_apply i).comp (measurable_snd.sub measurable_const)
        have hden : Measurable (fun p : ℝ × Vec3 => (2 : ℝ) * p.1) :=
          measurable_const.mul measurable_fst
        have hm := hcoord.div hden |>.neg.mul hheat
        convert hm using 1
        funext p
        dsimp
        ring
      · exact measurable_const
    have hgmeas : Measurable (fun p : ℝ × Vec3 => g p.2) :=
      hg.continuous.measurable.comp measurable_snd
    exact (hderiv.mul hgmeas).aestronglyMeasurable
  have hnearBase : Integrable (fun p : ℝ × Vec3 =>
      heatKernelGradientNorm (p.2-y) p.1)
      ((volume.restrict (Ioc 0 1)).prod volume) := by
    have hgrad := (heatKernelGradientNorm_integrable_prod (T := 1)
      (by norm_num : (0 : ℝ) < 1)).swap
    have hgrad' : Integrable (fun p : ℝ × Vec3 =>
        heatKernelGradientNorm p.2 p.1)
        ((volume.restrict (Ioc 0 1)).prod volume) := by
      convert hgrad using 1
      funext p
      rfl
    let S : ℝ × Vec3 → ℝ × Vec3 := Prod.map id (fun x : Vec3 => x-y)
    have hS : MeasurePreserving S
        ((volume.restrict (Ioc 0 1)).prod (volume : Measure Vec3))
        ((volume.restrict (Ioc 0 1)).prod volume) := by
      exact MeasurePreserving.prod
        (MeasurePreserving.id (volume.restrict (Ioc 0 1)))
        (measurePreserving_sub_right volume y)
    have hshift := (hS.integrable_comp hgrad'.aestronglyMeasurable).2 hgrad'
    change Integrable (fun p : ℝ × Vec3 =>
      heatKernelGradientNorm (p.2-y) p.1)
      ((volume.restrict (Ioc 0 1)).prod volume) at hshift
    exact hshift
  have hnearMajor : Integrable (fun p : ℝ × Vec3 => C *
      heatKernelGradientNorm (p.2-y) p.1)
      ((volume.restrict (Ioc 0 1)).prod volume) := hnearBase.const_mul C
  have hnear : IntegrableOn F (Ioc 0 1 ×ˢ (Set.univ : Set Vec3))
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    change Integrable F ((volume.prod volume).restrict
      (Ioc 0 1 ×ˢ (Set.univ : Set Vec3)))
    rw [← Measure.prod_restrict]
    have hm := hFmeas.restrict (s := Ioc 0 1 ×ˢ (Set.univ : Set Vec3))
    rw [← Measure.prod_restrict] at hm
    have hm' : AEStronglyMeasurable F
        ((volume.restrict (Ioc 0 1)).prod volume) := by
      simpa only [Measure.restrict_univ] using hm
    have hi : Integrable F ((volume.restrict (Ioc 0 1)).prod volume) := by
      apply hnearMajor.mono' hm'
      filter_upwards [] with p
      by_cases hp : p.2 ∈ K
      · have hderiv : |heatKernelSpaceDerivative (p.2-y) p.1 i| ≤
            heatKernelGradientNorm (p.2-y) p.1 := by
          unfold heatKernelGradientNorm
          exact Finset.single_le_sum
            (fun j _hj => abs_nonneg (heatKernelSpaceDerivative (p.2-y) p.1 j))
            (Finset.mem_univ i)
        have hg' : ‖g p.2‖ ≤ C := hC p.2
        dsimp [F]
        rw [abs_mul]
        calc
          |heatKernelSpaceDerivative (p.2-y) p.1 i| * |g p.2| ≤
              heatKernelGradientNorm (p.2-y) p.1 * C :=
            mul_le_mul hderiv hg' (abs_nonneg _)
              (by unfold heatKernelGradientNorm; positivity)
          _ = C * heatKernelGradientNorm (p.2-y) p.1 := by ring
      · have hz : g p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
        simp only [hz, mul_zero, norm_zero, ge_iff_le, F]
        exact mul_nonneg hC0 (by unfold heatKernelGradientNorm; positivity)
    simpa only [Measure.restrict_univ] using hi
  have ht2 : Integrable (fun t : ℝ => t ^ (-2 : ℝ))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).integrable
  have hKone : Integrable (K.indicator (fun _ : Vec3 => (1 : ℝ))) volume := by
    apply (integrable_indicator_iff hKmeas).2
    exact integrableOn_const hK.measure_lt_top.ne
  have htailBase : Integrable (fun p : ℝ × Vec3 =>
      p.1 ^ (-2 : ℝ) * K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2)
      ((volume.restrict (Ioi 1)).prod volume) := by
    simpa only using ht2.mul_prod hKone
  have htailMajor : Integrable (fun p : ℝ × Vec3 =>
      300000 * C * (p.1 ^ (-2 : ℝ) *
        K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2))
      ((volume.restrict (Ioi 1)).prod volume) :=
    htailBase.const_mul (300000 * C)
  have htail : IntegrableOn F (Ioi 1 ×ˢ (Set.univ : Set Vec3))
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    change Integrable F ((volume.prod volume).restrict
      (Ioi 1 ×ˢ (Set.univ : Set Vec3)))
    have htailMajor' : Integrable (fun p : ℝ × Vec3 =>
        300000 * C * (p.1 ^ (-2 : ℝ) *
          K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2))
        ((volume.prod volume).restrict (Ioi 1 ×ˢ (Set.univ : Set Vec3))) := by
      rw [← Measure.prod_restrict]
      simpa only [Measure.restrict_univ] using htailMajor
    apply htailMajor'.mono' hFmeas.restrict
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp_time
    by_cases hp : p.2 ∈ K
    · have ht : 1 < p.1 := hp_time.1
      have ht0 : 0 < p.1 := lt_trans zero_lt_one ht
      have hrho : Real.sqrt p.1 ≤ rhoTwo (p.2-y) p.1 := by
        unfold rhoTwo
        exact le_add_of_nonneg_left (vec3EuclideanNorm_nonneg (p.2-y))
      have hpow : p.1 ^ (2 : ℕ) ≤ rhoTwo (p.2-y) p.1 ^ 4 := by
        have hs : (Real.sqrt p.1) ^ 4 ≤ rhoTwo (p.2-y) p.1 ^ 4 := by
          gcongr
        have hsquare : p.1 ^ (2 : ℕ) = (Real.sqrt p.1) ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
            Real.sq_sqrt ht0.le]
        rw [hsquare]
        exact hs
      have hrhopos : 0 < rhoTwo (p.2-y) p.1 ^ 4 := by
        have hpos : 0 < rhoTwo (p.2-y) p.1 := lt_of_lt_of_le
          (Real.sqrt_pos.2 ht0) hrho
        positivity
      have htpowpos : 0 < p.1 ^ (2 : ℕ) := by positivity
      have hinv : (rhoTwo (p.2-y) p.1 ^ 4)⁻¹ ≤
          (p.1 ^ (2 : ℕ))⁻¹ := (inv_le_inv₀ hrhopos htpowpos).2 hpow
      have hkernel : |heatKernelSpaceDerivative (p.2-y) p.1 i| ≤
          300000 * p.1 ^ (-2 : ℝ) := by
        have hraw := heatKernelSpaceDerivative_abs_le_rho_inv_four
          (x := p.2-y) (t := p.1) ht0 i
        calc
          |heatKernelSpaceDerivative (p.2-y) p.1 i| ≤
              300000 / rhoTwo (p.2-y) p.1 ^ 4 := hraw
          _ = 300000 * (rhoTwo (p.2-y) p.1 ^ 4)⁻¹ := by ring
          _ ≤ 300000 * (p.1 ^ (2 : ℕ))⁻¹ := by gcongr
          _ = 300000 * p.1 ^ (-2 : ℝ) := by
            rw [Real.rpow_neg ht0.le, ← Real.rpow_natCast,
              Real.rpow_natCast]
            exact congrArg (fun q : ℝ => 300000 * q⁻¹)
              (Real.rpow_natCast p.1 2).symm
      have hg' : |g p.2| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC p.2
      rw [Real.norm_eq_abs, abs_mul, Set.indicator_of_mem hp]
      calc
        |heatKernelSpaceDerivative (p.2-y) p.1 i| * |g p.2| ≤
            (300000 * p.1 ^ (-2 : ℝ)) * C :=
          mul_le_mul hkernel hg' (abs_nonneg _) (by positivity)
        _ = 300000 * C * (p.1 ^ (-2 : ℝ) * 1) := by ring
    · have hz : g p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
      simp [F, hz, Set.indicator_of_notMem hp]
  have hall : IntegrableOn F (Ioi 0 ×ˢ (Set.univ : Set Vec3))
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
      Set.union_prod, integrableOn_union]
    exact ⟨hnear, htail⟩
  have hall' : Integrable F ((volume.prod volume).restrict
      (Ioi 0 ×ˢ (Set.univ : Set Vec3))) := hall
  rw [← Measure.prod_restrict] at hall'
  simpa only [F, Measure.restrict_univ] using hall'

end CKN
