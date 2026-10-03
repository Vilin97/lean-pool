/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.GlobalAffineLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.GlobalMollifierLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.InwardMollificationGeometry

/-!
# Global `L^p` convergence of inward mollification

This file combines the global approximate-identity theorem with strong
continuity under the outward affine expansion.  The result is independent of
domain geometry and boundary conditions.
-/

@[expose] public section

namespace Homogenization

open Function MeasureTheory Topology
open _root_.Filter
open scoped Convolution ENNReal Pointwise

noncomputable section

private theorem memLp_inwardMollification
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hg : MemLp g p volume) (x0 : Vec d)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    MemLp (inwardMollification ρ g x0 r ε) p volume := by
  have hscale : 0 < ε * r := mul_pos hε hr
  have hk_compact : HasCompactSupport (scaledConvexApproxKernel ρ (ε * r)) :=
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport hscale
  have hk_cont : Continuous (scaledConvexApproxKernel ρ (ε * r)) :=
    (contDiff_scaledConvexApproxKernel hρ (ε * r)).continuous
  have hg_loc : LocallyIntegrable g volume := hg.locallyIntegrable hp1
  let mollified : Vec d → ℝ :=
    scaledConvexApproxKernel ρ (ε * r) ⋆[
      ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hmollified_cont : Continuous mollified := by
    exact hk_compact.continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hg_loc
  have hmollified_norm : eLpNorm mollified p volume ≤ eLpNorm g p volume := by
    exact young_convolution_nonneg_integral_one_of_aemeasurable hp1 hp
      (scaledConvexApproxKernel_nonneg hρ hscale)
      (integrable_scaledConvexApproxKernel hρ hscale)
      (integral_scaledConvexApproxKernel hρ hscale)
      (measurable_scaledConvexApproxKernel hρ.continuous (ε * r))
      hg.aemeasurable
  have hmollified_mem : MemLp mollified p volume :=
    hmollified_norm.trans_lt hg.eLpNorm_lt_top
  have hcomp := MemLp.comp_globalAffineExpansion hmollified_mem x0 hε.le
  simpa only [inwardMollification, mollified, globalAffineExpansion] using! hcomp

/-- Inward mollification converges strongly to its input in every finite
`L^p`, `1 ≤ p < ∞`, on the whole Euclidean space. -/
theorem tendsto_eLpNorm_inwardMollification_sub_zero
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hg : MemLp g p volume) (x0 : Vec d)
    {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ n, 0 ≤ ε n)
    (hε_pos : ∀ᶠ n in Filter.atTop, 0 < ε n) :
    Filter.Tendsto
      (fun n => eLpNorm
        (inwardMollification ρ g x0 r (ε n) - g) p volume)
      Filter.atTop (nhds 0) := by
  let mollified : ℕ → Vec d → ℝ := fun n =>
    scaledConvexApproxKernel ρ (ε n * r) ⋆[
      ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hmollifier : Filter.Tendsto
      (fun n => eLpNorm (mollified n - g) p volume) Filter.atTop (nhds 0) := by
    simpa only [mollified, Pi.sub_apply] using!
      tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel
        hρ hp1 hp hg hr hε hε_pos
  have haffine : Filter.Tendsto
      (fun n => eLpNorm
        (g ∘ globalAffineExpansion x0 (ε n) - g) p volume)
      Filter.atTop (nhds 0) :=
    tendsto_eLpNorm_comp_globalAffineExpansion_sub_zero
      hp1 hp hg x0 hε hε_nonneg
  have hsum : Filter.Tendsto
      (fun n => eLpNorm (mollified n - g) p volume +
        eLpNorm (g ∘ globalAffineExpansion x0 (ε n) - g) p volume)
      Filter.atTop (nhds 0) := by
    simpa using hmollifier.add haffine
  have hupper : ∀ᶠ n in Filter.atTop,
      eLpNorm (inwardMollification ρ g x0 r (ε n) - g) p volume ≤
        eLpNorm (mollified n - g) p volume +
          eLpNorm (g ∘ globalAffineExpansion x0 (ε n) - g) p volume := by
    filter_upwards [hε_pos] with n hn_pos
    have hscale : 0 < ε n * r := mul_pos hn_pos hr
    have hk_compact : HasCompactSupport (scaledConvexApproxKernel ρ (ε n * r)) :=
      hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport hscale
    have hk_cont : Continuous (scaledConvexApproxKernel ρ (ε n * r)) :=
      (contDiff_scaledConvexApproxKernel hρ (ε n * r)).continuous
    have hg_loc : LocallyIntegrable g volume := hg.locallyIntegrable hp1
    have hmollified_cont : Continuous (mollified n) := by
      exact hk_compact.continuous_convolution_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hg_loc
    have hmollified_norm : eLpNorm (mollified n) p volume ≤ eLpNorm g p volume := by
      exact young_convolution_nonneg_integral_one_of_aemeasurable hp1 hp
        (scaledConvexApproxKernel_nonneg hρ hscale)
        (integrable_scaledConvexApproxKernel hρ hscale)
        (integral_scaledConvexApproxKernel hρ hscale)
        (measurable_scaledConvexApproxKernel hρ.continuous (ε n * r))
        hg.aemeasurable
    have hmollified_mem : MemLp (mollified n) p volume :=
      hmollified_norm.trans_lt hg.eLpNorm_lt_top
    have hdiff_mem : MemLp (mollified n - g) p volume :=
      hmollified_mem.sub hg
    have hdiff_comp_mem :
        MemLp ((mollified n - g) ∘ globalAffineExpansion x0 (ε n)) p volume :=
      MemLp.comp_globalAffineExpansion hdiff_mem x0 (hε_nonneg n)
    have hg_comp_mem : MemLp (g ∘ globalAffineExpansion x0 (ε n)) p volume :=
      MemLp.comp_globalAffineExpansion hg x0 (hε_nonneg n)
    have hfactor_le :
        ENNReal.ofReal (((1 + ε n) ^ d)⁻¹) ^ (1 / p).toReal ≤ 1 := by
      have hpow : 1 ≤ (1 + ε n) ^ d := one_le_pow₀ (by linarith [hε_nonneg n])
      have hbase : ENNReal.ofReal (((1 + ε n) ^ d)⁻¹) ≤ 1 :=
        ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ hpow)
      exact ENNReal.rpow_le_one hbase (by positivity)
    have hcomp_le :
        eLpNorm ((mollified n - g) ∘ globalAffineExpansion x0 (ε n)) p volume ≤
          eLpNorm (mollified n - g) p volume := by
      rw [eLpNorm_comp_globalAffineExpansion hp hdiff_mem x0 (hε_nonneg n)]
      simpa only [one_mul] using
        mul_le_mul_left hfactor_le (eLpNorm (mollified n - g) p volume)
    have hdecomp :
        inwardMollification ρ g x0 r (ε n) - g =
          (mollified n - g) ∘ globalAffineExpansion x0 (ε n) +
            (g ∘ globalAffineExpansion x0 (ε n) - g) := by
      funext x
      simp only [inwardMollification, mollified, globalAffineExpansion,
        Function.comp_apply, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hdecomp]
    calc
      eLpNorm
          ((mollified n - g) ∘ globalAffineExpansion x0 (ε n) +
            (g ∘ globalAffineExpansion x0 (ε n) - g)) p volume ≤
          eLpNorm ((mollified n - g) ∘ globalAffineExpansion x0 (ε n)) p volume +
            eLpNorm (g ∘ globalAffineExpansion x0 (ε n) - g) p volume :=
        eLpNorm_add_le hp1
      _ ≤ eLpNorm (mollified n - g) p volume +
            eLpNorm (g ∘ globalAffineExpansion x0 (ε n) - g) p volume :=
        add_le_add hcomp_le (le_refl _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum (Filter.Eventually.of_forall fun _ => zero_le) hupper

/-- The scalar factor produced by differentiating the affine pullback does not
alter strong finite-`L^p` convergence of inward mollification. -/
theorem tendsto_eLpNorm_one_add_mul_inwardMollification_sub_zero
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hg : MemLp g p volume) (x0 : Vec d)
    {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ n, 0 ≤ ε n)
    (hε_pos : ∀ᶠ n in Filter.atTop, 0 < ε n) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x => (1 + ε n) * inwardMollification ρ g x0 r (ε n) x - g x)
        p volume)
      Filter.atTop (nhds 0) := by
  let c : ℕ → ℝ := fun n => 1 + ε n
  have hbase := tendsto_eLpNorm_inwardMollification_sub_zero
    hρ hp1 hp hg x0 hr hε hε_nonneg hε_pos
  have hc : Filter.Tendsto c Filter.atTop (nhds 1) := by
    simpa [c] using (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)).add hε
  have hcnorm : Filter.Tendsto (fun n => ‖c n‖ₑ) Filter.atTop (nhds 1) := by
    simpa using! (continuous_enorm.tendsto (1 : ℝ)).comp hc
  have hdiffnorm : Filter.Tendsto (fun n => ‖c n - 1‖ₑ)
      Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto (fun n => c n - 1) Filter.atTop (nhds 0) := by
      simpa using hc.sub (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1))
    simpa using! (continuous_enorm.tendsto (0 : ℝ)).comp hreal
  have hfirst : Filter.Tendsto
      (fun n => eLpNorm
        (c n • (inwardMollification ρ g x0 r (ε n) - g)) p volume)
      Filter.atTop (nhds 0) := by
    simpa only [eLpNorm_const_smul, one_mul] using
      ENNReal.Tendsto.mul hcnorm (Or.inl one_ne_zero) hbase
        (Or.inr ENNReal.one_ne_top)
  have hg_norm_ne_top : eLpNorm g p volume ≠ ⊤ := hg.eLpNorm_ne_top
  have hsecond : Filter.Tendsto
      (fun n => eLpNorm ((c n - 1) • g) p volume)
      Filter.atTop (nhds 0) := by
    simpa only [eLpNorm_const_smul, zero_mul] using
      ENNReal.Tendsto.mul_const hdiffnorm (Or.inr hg_norm_ne_top)
  have hsum : Filter.Tendsto
      (fun n =>
        eLpNorm (c n • (inwardMollification ρ g x0 r (ε n) - g)) p volume +
          eLpNorm ((c n - 1) • g) p volume)
      Filter.atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  have hupper : ∀ᶠ n in Filter.atTop,
      eLpNorm
          (fun x => (1 + ε n) * inwardMollification ρ g x0 r (ε n) x - g x)
          p volume ≤
        eLpNorm (c n • (inwardMollification ρ g x0 r (ε n) - g)) p volume +
          eLpNorm ((c n - 1) • g) p volume := by
    filter_upwards [hε_pos] with n hn_pos
    have hinward_mem : MemLp (inwardMollification ρ g x0 r (ε n)) p volume :=
      memLp_inwardMollification hρ hp1 hp hg x0 hr hn_pos
    have hfirst_meas : AEStronglyMeasurable
        (c n • (inwardMollification ρ g x0 r (ε n) - g)) volume :=
      (hinward_mem.sub hg).aestronglyMeasurable.const_smul (c n)
    have hsecond_meas : AEStronglyMeasurable ((c n - 1) • g) volume :=
      hg.aestronglyMeasurable.const_smul (c n - 1)
    have hdecomp :
        (fun x => (1 + ε n) * inwardMollification ρ g x0 r (ε n) x - g x) =
          c n • (inwardMollification ρ g x0 r (ε n) - g) +
            (c n - 1) • g := by
      funext x
      simp only [c, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hdecomp]
    exact eLpNorm_add_le hp1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum (Filter.Eventually.of_forall fun _ => zero_le) hupper

end

end Homogenization
