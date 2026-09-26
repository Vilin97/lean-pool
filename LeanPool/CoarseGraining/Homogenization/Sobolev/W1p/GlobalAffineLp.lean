/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Global affine expansion in finite `Lᵖ`

This file isolates the volume transport and strong finite-`Lᵖ` continuity of
the outward affine map used by inward mollification.
-/

@[expose] public section

namespace Homogenization

open Function MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

noncomputable section

/-- The outward affine map based at `x0` with expansion parameter `ε`. -/
def globalAffineExpansion {d : ℕ} (x0 : Vec d) (ε : ℝ) : Vec d → Vec d :=
  fun x => (1 + ε) • x - ε • x0

@[simp] theorem globalAffineExpansion_apply {d : ℕ} (x0 x : Vec d) (ε : ℝ) :
    globalAffineExpansion x0 ε x = (1 + ε) • x - ε • x0 :=
  rfl

private theorem globalAffineExpansion_eq_add_comp_smul {d : ℕ} (x0 : Vec d) (ε : ℝ) :
    globalAffineExpansion x0 ε =
      (fun y : Vec d => y + (-ε • x0)) ∘ fun x : Vec d => (1 + ε) • x := by
  funext x
  simp [globalAffineExpansion_apply, sub_eq_add_neg, neg_smul]

/-- The outward affine expansion pushes Lebesgue measure forward by the
Jacobian factor of its scalar linear part. -/
theorem map_globalAffineExpansion_volume {d : ℕ} (x0 : Vec d) {ε : ℝ}
    (hε : 0 ≤ ε) :
    Measure.map (globalAffineExpansion x0 ε) volume =
      ENNReal.ofReal (((1 + ε) ^ d)⁻¹) • volume := by
  have ha : 0 < 1 + ε := by linarith
  rw [globalAffineExpansion_eq_add_comp_smul]
  change Measure.map ((fun y : Vec d => y + (-ε • x0)) ∘
      fun x : Vec d => (1 + ε) • x) volume = _
  rw [← Measure.map_map (g := fun y : Vec d => y + (-ε • x0))
    (f := fun x : Vec d => (1 + ε) • x) (measurable_id.add measurable_const)
      (measurable_const_smul (1 + ε))]
  · have hmap := map_smul_volume_restrict (d := d) ha Set.univ
    have hsmul_univ : (1 + ε) • (Set.univ : Set (Vec d)) = Set.univ :=
      Set.smul_set_univ₀ ha.ne'
    rw [hsmul_univ, Measure.restrict_univ] at hmap
    rw [hmap, Measure.map_smul _ (f := fun y : Vec d => y + (-ε • x0))
      (measurable_id.add measurable_const).aemeasurable,
      map_add_right_eq_self]

/-- The outward affine expansion is quasi-measure-preserving for Lebesgue
measure whenever its scalar factor is positive. -/
theorem quasiMeasurePreserving_globalAffineExpansion {d : ℕ} (x0 : Vec d) {ε : ℝ}
    (hε : 0 ≤ ε) :
    Measure.QuasiMeasurePreserving (globalAffineExpansion x0 ε) volume volume := by
  refine ⟨(measurable_const_smul (1 + ε)).sub measurable_const, ?_⟩
  rw [map_globalAffineExpansion_volume x0 hε]
  exact Measure.smul_absolutelyContinuous

/-- Almost-everywhere equal fields remain almost-everywhere equal after an
outward affine expansion. -/
theorem Filter.EventuallyEq.comp_globalAffineExpansion {d : ℕ} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volume] g) (x0 : Vec d) {ε : ℝ} (hε : 0 ≤ ε) :
    f ∘ globalAffineExpansion x0 ε =ᵐ[volume] g ∘ globalAffineExpansion x0 ε :=
  (quasiMeasurePreserving_globalAffineExpansion x0 hε).ae_eq hfg

/-- Finite `Lᵖ` functions remain in `Lᵖ` after an outward affine expansion. -/
theorem MemLp.comp_globalAffineExpansion {d : ℕ} {g : Vec d → ℝ} {p : ℝ≥0∞}
    (hg : MemLp g p volume) (x0 : Vec d) {ε : ℝ} (hε : 0 ≤ ε) :
    MemLp (g ∘ globalAffineExpansion x0 ε) p volume := by
  have hmap : Measure.map (globalAffineExpansion x0 ε) volume =
      ENNReal.ofReal (((1 + ε) ^ d)⁻¹) • volume :=
    map_globalAffineExpansion_volume x0 hε
  have hg_map : MemLp g p (Measure.map (globalAffineExpansion x0 ε) volume) := by
    rw [hmap]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  have hmeas : AEMeasurable (globalAffineExpansion x0 ε) volume :=
    ((measurable_const_smul (1 + ε)).sub measurable_const).aemeasurable
  exact hg_map.comp_of_map hmeas

/-- Exact finite-`Lᵖ` norm transport under an outward affine expansion. -/
theorem eLpNorm_comp_globalAffineExpansion {d : ℕ} {g : Vec d → ℝ} {p : ℝ≥0∞}
    (hp : p ≠ ∞) (hg : MemLp g p volume) (x0 : Vec d) {ε : ℝ} (hε : 0 ≤ ε) :
    eLpNorm (g ∘ globalAffineExpansion x0 ε) p volume =
      ENNReal.ofReal (((1 + ε) ^ d)⁻¹) ^ (1 / p).toReal * eLpNorm g p volume := by
  have hmap : Measure.map (globalAffineExpansion x0 ε) volume =
      ENNReal.ofReal (((1 + ε) ^ d)⁻¹) • volume :=
    map_globalAffineExpansion_volume x0 hε
  have hmeas : AEMeasurable (globalAffineExpansion x0 ε) volume :=
    ((measurable_const_smul (1 + ε)).sub measurable_const).aemeasurable
  have hg_map : AEStronglyMeasurable g
      (Measure.map (globalAffineExpansion x0 ε) volume) := by
    rw [hmap]
    exact (hg.smul_measure ENNReal.ofReal_ne_top).aestronglyMeasurable
  rw [← MeasureTheory.eLpNorm_map_measure hg_map hmeas, hmap,
    MeasureTheory.eLpNorm_smul_measure_of_ne_top hp g _ hg.aestronglyMeasurable]
  simp only [smul_eq_mul]

private theorem eLpNorm_comp_globalAffineExpansion_le {d : ℕ} {g : Vec d → ℝ}
    {p : ℝ≥0∞} (hp : p ≠ ∞) (hg : MemLp g p volume) (x0 : Vec d) {ε : ℝ}
    (hε : 0 ≤ ε) :
    eLpNorm (g ∘ globalAffineExpansion x0 ε) p volume ≤ eLpNorm g p volume := by
  rw [eLpNorm_comp_globalAffineExpansion hp hg x0 hε]
  have hpow : 1 ≤ (1 + ε) ^ d := one_le_pow₀ (by linarith)
  have hbase : ENNReal.ofReal (((1 + ε) ^ d)⁻¹) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ hpow)
  have hfactor : ENNReal.ofReal (((1 + ε) ^ d)⁻¹) ^ (1 / p).toReal ≤ 1 :=
    ENNReal.rpow_le_one hbase (by positivity)
  simpa only [one_mul] using mul_le_mul_left hfactor (eLpNorm g p volume)

private theorem globalAffineExpansion_inv_apply {d : ℕ} (x x0 : Vec d) {ε : ℝ}
    (hε : 0 ≤ ε) :
    x = (1 + ε)⁻¹ • globalAffineExpansion x0 ε x +
      (ε * (1 + ε)⁻¹) • x0 := by
  have ha : 0 < 1 + ε := by linarith
  ext i
  simp only [globalAffineExpansion_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [ha.ne']
  ring

private theorem norm_globalAffineExpansion_inv_le {d : ℕ} (x x0 : Vec d) {ε R : ℝ}
    (hε : 0 ≤ ε) (hR : ‖globalAffineExpansion x0 ε x‖ ≤ R) :
    ‖x‖ ≤ R + ‖x0‖ := by
  have ha : 0 < 1 + ε := by linarith
  have hinv_nonneg : 0 ≤ (1 + ε)⁻¹ := inv_nonneg.mpr ha.le
  have hcoeff_nonneg : 0 ≤ ε * (1 + ε)⁻¹ := mul_nonneg hε hinv_nonneg
  have hinv_le_one : (1 + ε)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ ha]
    linarith
  have hcoeff_le_one : ε * (1 + ε)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one₀ ha).mpr (by linarith)
  have hR_nonneg : 0 ≤ R := (norm_nonneg _).trans hR
  rw [globalAffineExpansion_inv_apply x x0 hε]
  calc
    ‖(1 + ε)⁻¹ • globalAffineExpansion x0 ε x +
        (ε * (1 + ε)⁻¹) • x0‖ ≤
      ‖(1 + ε)⁻¹ • globalAffineExpansion x0 ε x‖ +
        ‖(ε * (1 + ε)⁻¹) • x0‖ := norm_add_le _ _
    _ = (1 + ε)⁻¹ * ‖globalAffineExpansion x0 ε x‖ +
        (ε * (1 + ε)⁻¹) * ‖x0‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hinv_nonneg, abs_of_nonneg hcoeff_nonneg]
    _ ≤ R + ‖x0‖ := by
      exact add_le_add
        (calc
          (1 + ε)⁻¹ * ‖globalAffineExpansion x0 ε x‖ ≤
              1 * ‖globalAffineExpansion x0 ε x‖ :=
            mul_le_mul_of_nonneg_right hinv_le_one (norm_nonneg _)
          _ ≤ 1 * R := mul_le_mul_of_nonneg_left hR zero_le_one
          _ = R := one_mul _)
        (calc
          (ε * (1 + ε)⁻¹) * ‖x0‖ ≤ 1 * ‖x0‖ :=
            mul_le_mul_of_nonneg_right hcoeff_le_one (norm_nonneg _)
          _ = ‖x0‖ := one_mul _)

private theorem tendsto_globalAffineExpansion_apply {d : ℕ} (x x0 : Vec d)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => globalAffineExpansion x0 (ε n) x) Filter.atTop (nhds x) := by
  have hscale : Filter.Tendsto (fun n => 1 + ε n) Filter.atTop (nhds 1) :=
    by simpa using (tendsto_const_nhds.add hε)
  have hfirst : Filter.Tendsto (fun n => (1 + ε n) • x) Filter.atTop (nhds x) := by
    simpa using hscale.smul (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x))
  have hsecond : Filter.Tendsto (fun n => ε n • x0) Filter.atTop (nhds 0) := by
    simpa using hε.smul (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => x0) Filter.atTop (nhds x0))
  simpa [globalAffineExpansion_apply] using hfirst.sub hsecond

private theorem tendsto_eLpNorm_comp_globalAffineExpansion_sub_zero_of_continuous_compactSupport
    {d : ℕ} {h : Vec d → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hcont : Continuous h) (hcompact : HasCompactSupport h) (x0 : Vec d)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ n, 0 ≤ ε n) :
    Filter.Tendsto
      (fun n => eLpNorm (h ∘ globalAffineExpansion x0 (ε n) - h) p volume)
      Filter.atTop (nhds 0) := by
  obtain ⟨R, hR⟩ := hcompact.isCompact.isBounded.subset_closedBall (0 : Vec d)
  let B : Set (Vec d) := Metric.closedBall 0 (R + ‖x0‖)
  have hB_meas : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  let : IsFiniteMeasure (volume.restrict B) :=
    ⟨by
      simpa [B] using (measure_closedBall_lt_top (μ := volume) (x := (0 : Vec d))
        (r := R + ‖x0‖))⟩
  have hcomp_support : ∀ n, Function.support (h ∘ globalAffineExpansion x0 (ε n)) ⊆ B := by
    intro n x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply norm_globalAffineExpansion_inv_le x x0 (hε_nonneg n)
    have hy : globalAffineExpansion x0 (ε n) x ∈ Metric.closedBall 0 R :=
      hR (subset_tsupport h (by simpa only [Function.mem_support, Function.comp_apply] using hx))
    rwa [Metric.mem_closedBall, dist_zero_right] at hy
  have hh_support : Function.support h ⊆ B := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hx' : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hR (subset_tsupport h hx)
    exact hx'.trans (le_add_of_nonneg_right (norm_nonneg _))
  have hdiff_support : ∀ n,
      Function.support (h ∘ globalAffineExpansion x0 (ε n) - h) ⊆ B := by
    intro n
    exact (Function.support_sub _ _).trans (Set.union_subset (hcomp_support n) hh_support)
  have hmem : MemLp h p volume := hcont.memLp_of_hasCompactSupport hcompact
  have hmem_comp : ∀ n, MemLp (h ∘ globalAffineExpansion x0 (ε n)) p volume :=
    fun n => MemLp.comp_globalAffineExpansion hmem x0 (hε_nonneg n)
  have hpoint : ∀ x : Vec d,
      Filter.Tendsto (fun n => (h ∘ globalAffineExpansion x0 (ε n)) x)
        Filter.atTop (nhds (h x)) := by
    intro x
    exact hcont.continuousAt.tendsto.comp (tendsto_globalAffineExpansion_apply x x0 hε)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcompact
  have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hUI : UnifIntegrable (fun n => h ∘ globalAffineExpansion x0 (ε n)) p
      (volume.restrict B) := by
    apply unifIntegrable_of hp hp_top
    · intro n
      exact (hmem_comp n).restrict B |>.aestronglyMeasurable
    · intro δ hδ
      let C' : NNReal := ⟨C + 1, by linarith⟩
      refine ⟨C', fun n => ?_⟩
      have hzero : {x | C' ≤
          ‖(h ∘ globalAffineExpansion x0 (ε n)) x‖₊}.indicator
          (h ∘ globalAffineExpansion x0 (ε n)) = 0 := by
        funext x
        by_cases hx : C' ≤
            ‖(h ∘ globalAffineExpansion x0 (ε n)) x‖₊
        · exfalso
          have hle : C + 1 ≤ ‖h (globalAffineExpansion x0 (ε n) x)‖ := by
            exact_mod_cast hx
          linarith [hC (globalAffineExpansion x0 (ε n) x)]
        · change Set.indicator {x | C' ≤
              ‖(h ∘ globalAffineExpansion x0 (ε n)) x‖₊}
              (h ∘ globalAffineExpansion x0 (ε n)) x = (0 : ℝ)
          have hx' : x ∉ {x | C' ≤
              ‖(h ∘ globalAffineExpansion x0 (ε n)) x‖₊} := hx
          simp only [Set.indicator_apply, hx', ↓reduceIte]
      rw [hzero, eLpNorm_zero]
      exact bot_le
  have hlocal := tendsto_Lp_finite_of_tendsto_ae hp hp_top
    (fun n => (hmem_comp n).restrict B |>.aestronglyMeasurable)
    (hmem.restrict B) hUI (ae_of_all _ hpoint)
  have hEq : (fun n => eLpNorm (h ∘ globalAffineExpansion x0 (ε n) - h) p volume) =
      fun n => eLpNorm (h ∘ globalAffineExpansion x0 (ε n) - h) p (volume.restrict B) := by
    funext n
    exact (eLpNorm_restrict_eq_of_support_subset
      ((hmem_comp n).aestronglyMeasurable.sub hmem.aestronglyMeasurable) (hdiff_support n)).symm
  rw [hEq]
  exact hlocal

/-- Outward affine expansions are strongly continuous on global finite `Lᵖ`.
The conclusion is stated for scalar fields; downstream weak-gradient arguments
apply it coordinatewise. -/
theorem tendsto_eLpNorm_comp_globalAffineExpansion_sub_zero {d : ℕ}
    {g : Vec d → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hg : MemLp g p volume) (x0 : Vec d) {ε : ℕ → ℝ}
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ n, 0 ≤ ε n) :
    Filter.Tendsto
      (fun n => eLpNorm (g ∘ globalAffineExpansion x0 (ε n) - g) p volume)
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hthree_ne_top : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨h, hcompact, hgh, hcont, hh⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le hp_top
      (ENNReal.div_ne_zero.mpr ⟨hδ.ne', hthree_ne_top⟩)
  have hmiddle :=
    tendsto_eLpNorm_comp_globalAffineExpansion_sub_zero_of_continuous_compactSupport
      hp hp_top hcont hcompact x0 hε hε_nonneg
  rw [ENNReal.tendsto_atTop_zero] at hmiddle
  obtain ⟨N, hN⟩ := hmiddle (δ / (3 : ℝ≥0∞)) (by
    exact (pos_iff_ne_zero.mpr (ENNReal.div_ne_zero.mpr ⟨hδ.ne', hthree_ne_top⟩)))
  refine ⟨N, fun n hn => ?_⟩
  have hgh_comp : MemLp ((g - h) ∘ globalAffineExpansion x0 (ε n)) p volume :=
    MemLp.comp_globalAffineExpansion (hg.sub hh) x0 (hε_nonneg n)
  have hh_comp : MemLp (h ∘ globalAffineExpansion x0 (ε n)) p volume :=
    MemLp.comp_globalAffineExpansion hh x0 (hε_nonneg n)
  have hsplit : g ∘ globalAffineExpansion x0 (ε n) - g =
      (g - h) ∘ globalAffineExpansion x0 (ε n) +
        ((h ∘ globalAffineExpansion x0 (ε n) - h) + (h - g)) := by
    funext x
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit]
  calc
    eLpNorm ((g - h) ∘ globalAffineExpansion x0 (ε n) +
        ((h ∘ globalAffineExpansion x0 (ε n) - h) + (h - g))) p volume ≤
      eLpNorm ((g - h) ∘ globalAffineExpansion x0 (ε n)) p volume +
        eLpNorm ((h ∘ globalAffineExpansion x0 (ε n) - h) + (h - g)) p volume :=
      eLpNorm_add_le hp
    _ ≤ eLpNorm ((g - h) ∘ globalAffineExpansion x0 (ε n)) p volume +
        (eLpNorm (h ∘ globalAffineExpansion x0 (ε n) - h) p volume +
          eLpNorm (h - g) p volume) := by
      gcongr
      exact eLpNorm_add_le hp
    _ ≤ δ / 3 + (δ / 3 + δ / 3) := by
      gcongr
      · exact eLpNorm_comp_globalAffineExpansion_le hp_top (hg.sub hh) x0 (hε_nonneg n)
          |>.trans hgh
      · exact hN n hn
      · rw [show h - g = -(g - h) by
          funext x
          simp only [Pi.neg_apply, Pi.sub_apply]
          ring, eLpNorm_neg]
        exact hgh
    _ = δ := by rw [← add_assoc, ENNReal.add_thirds]

end

end Homogenization
