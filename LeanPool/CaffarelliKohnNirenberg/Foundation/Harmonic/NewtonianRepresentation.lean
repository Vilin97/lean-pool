/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Newtonian
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Newtonian Representation

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Interval
open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-! The Newtonian kernel representation obtained from the heat semigroup. -/

/-- The positive three-dimensional Newtonian kernel. -/
def newtonianKernel (z : Vec3) : ℝ :=
  1 / (4 * Real.pi * vec3EuclideanNorm z)

lemma newtonianKernel_locallyIntegrable :
    LocallyIntegrable newtonianKernel volume := by
  have hnorm : Continuous (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hmeas : AEStronglyMeasurable newtonianKernel volume := by
    exact (measurable_const.div (measurable_const.mul hnorm.measurable)).aestronglyMeasurable
  refine locallyIntegrable_of_norm_le_rpow (E := Vec3) (F := ℝ)
    (C := (4 * Real.pi)⁻¹) (α := (1 : ℝ)) ?_ (by norm_num) ?_ hmeas
  · change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ)
    rw [Module.finrank_fin_fun]
    norm_num
  · filter_upwards [] with z
    by_cases hz : z = 0
    · subst z
      simp [newtonianKernel, vec3EuclideanNorm]
    · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hrn : 0 < vec3EuclideanNorm z :=
        lt_of_lt_of_le hzn (CKN.space_norm_le_euclideanNorm z)
      have hinv : (vec3EuclideanNorm z)⁻¹ ≤ ‖z‖⁻¹ := by
        exact (inv_le_inv₀ hrn hzn).2 (CKN.space_norm_le_euclideanNorm z)
      rw [newtonianKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [show 1 / (4 * Real.pi * vec3EuclideanNorm z) =
          (4 * Real.pi)⁻¹ * (vec3EuclideanNorm z)⁻¹ by field_simp]
      have hrpow : ‖z‖ ^ (-1 : ℝ) = ‖z‖⁻¹ := by
        rw [Real.rpow_neg (norm_nonneg z), Real.rpow_one]
      rw [hrpow]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)

private lemma newtonianKernel_shift_locallyIntegrable (x : Vec3) :
    LocallyIntegrable (fun y : Vec3 => newtonianKernel (x - y)) volume := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Vec3) x
  have hmap : Measure.map (fun y : Vec3 => x - y) volume = volume := hmp.map_eq
  have hmap' : LocallyIntegrable newtonianKernel
      (Measure.map (Homeomorph.subLeft x) volume) := by
    change LocallyIntegrable newtonianKernel
      (Measure.map (fun y : Vec3 => x - y) volume)
    rw [hmap]
    exact newtonianKernel_locallyIntegrable
  have hcomp := (locallyIntegrable_map_homeomorph (Homeomorph.subLeft x)
    (f := newtonianKernel)).1 hmap'
  change LocallyIntegrable (fun y : Vec3 => newtonianKernel (x - y)) volume at hcomp
  exact hcomp

private lemma newtonianKernel_mul_spatialLaplacian_norm_integrable_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u) (x : Vec3) :
    Integrable (fun y : Vec3 => newtonianKernel (x - y) *
      ‖CKN.spatialLaplacian u y‖) volume := by
  have hgi (i : Fin 3) : HasCompactSupport
      (CKN.spatialDeriv (CKN.spatialDeriv u i) i) :=
    (huSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)).fderiv_apply
      (𝕜 := ℝ) (CKN.basisVec i)
  have hDelta : HasCompactSupport (CKN.spatialLaplacian u) := by
    have h01 : HasCompactSupport (fun y : Vec3 =>
        CKN.spatialDeriv (CKN.spatialDeriv u (0 : Fin 3)) 0 y +
          CKN.spatialDeriv (CKN.spatialDeriv u (1 : Fin 3)) 1 y) := by
      convert (hgi (0 : Fin 3)).add (hgi (1 : Fin 3)) using 1
    have hsum : HasCompactSupport (fun y : Vec3 =>
        CKN.spatialDeriv (CKN.spatialDeriv u (0 : Fin 3)) 0 y +
          CKN.spatialDeriv (CKN.spatialDeriv u (1 : Fin 3)) 1 y +
            CKN.spatialDeriv (CKN.spatialDeriv u (2 : Fin 3)) 2 y) := by
      convert h01.add (hgi (2 : Fin 3)) using 1
    change HasCompactSupport (fun y : Vec3 =>
      ∑ i : Fin 3, CKN.spatialDeriv (CKN.spatialDeriv u i) i y)
    simpa only [Fin.sum_univ_three] using hsum
  have hcont : Continuous (fun y : Vec3 => ‖CKN.spatialLaplacian u y‖) :=
    (CKN.contDiff_spatialLaplacian_smooth hu).continuous.norm
  simpa only [smul_eq_mul] using
    (newtonianKernel_shift_locallyIntegrable x).integrable_smul_right_of_hasCompactSupport
      hcont hDelta.norm

private lemma heatKernel_laplacian_prod_integrable_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u) (x : Vec3) :
    Integrable
      (fun p : ℝ × Vec3 => heatKernel (x - p.2) p.1 * CKN.spatialLaplacian u p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × Vec3 → ℝ := fun p =>
    heatKernel (x - p.2) p.1 * CKN.spatialLaplacian u p.2
  have hheat : Measurable (fun p : ℝ × Vec3 => heatKernel (x - p.2) p.1) := by
    unfold heatKernel
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_fst)
    · fun_prop
    · exact measurable_const
  have hspace : Measurable (fun p : ℝ × Vec3 => CKN.spatialLaplacian u p.2) :=
    (CKN.contDiff_spatialLaplacian_smooth hu).continuous.measurable.comp measurable_snd
  have hFmeas : AEStronglyMeasurable F (μ.prod volume) := by
    exact (hheat.mul hspace).aestronglyMeasurable
  change Integrable F (μ.prod volume)
  apply (integrable_prod_iff' hFmeas).2
  constructor
  · filter_upwards [Measure.ae_ne volume x] with y hy
    have hxy : x - y ≠ 0 := sub_ne_zero.mpr hy.symm
    have hk : Integrable (fun t : ℝ => heatKernel (x - y) t) μ := by
      change Integrable (fun t : ℝ => heatKernel (x - y) t)
        (volume.restrict (Ioi 0))
      apply Integrable.of_integral_ne_zero
      rw [heatKernel_integral_Ioi hxy]
      have hnorm : 0 < vec3EuclideanNorm (x - y) := by
        rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
        intro hz
        apply hxy
        exact (WithLp.toLp_eq_zero 2).mp hz
      exact ne_of_gt (by positivity)
    change Integrable (fun t : ℝ => heatKernel (x - y) t *
      CKN.spatialLaplacian u y) μ
    exact hk.mul_const _
  · have hnormeq : (fun y : Vec3 => ∫ t, ‖F (t, y)‖ ∂μ) =ᵐ[volume]
        (fun y => newtonianKernel (x - y) *
          ‖CKN.spatialLaplacian u y‖) := by
      filter_upwards [Measure.ae_ne volume x] with y hy
      have hxy : x - y ≠ 0 := sub_ne_zero.mpr hy.symm
      have hnorm : (fun t : ℝ => ‖F (t, y)‖) =ᵐ[μ]
          (fun t : ℝ => heatKernel (x - y) t *
            ‖CKN.spatialLaplacian u y‖) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        dsimp [F]
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg _ _)]
      rw [integral_congr_ae hnorm, integral_mul_const,
        heatKernel_integral_Ioi hxy]
      rfl
    exact (newtonianKernel_mul_spatialLaplacian_norm_integrable_smooth hu huSupport x).congr
      hnormeq.symm

private lemma heatConv_abs_le_sup_smooth {v : Vec3 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvSupport : HasCompactSupport v) {t : ℝ}
    (ht : 0 < t) (x : Vec3) :
    |heatConv t v x| ≤ ⨆ z : Vec3, ‖v z‖ := by
  let g : Vec3 → ℝ := fun y => v (x - y)
  have hgc : Continuous g := by
    dsimp [g]
    fun_prop
  have hgs : HasCompactSupport g := by
    dsimp [g]
    exact hvSupport.comp_homeomorph (Homeomorph.subLeft x)
  have hgi : Integrable g volume :=
    hgc.integrable_of_hasCompactSupport hgs
  have hbound : BddAbove (Set.range (fun z : Vec3 => ‖v z‖)) :=
    hv.continuous.norm.bddAbove_range_of_hasCompactSupport hvSupport.norm
  have hcomp : Integrable (fun y : Vec3 => heatKernel y t * g y) volume := by
    exact (heatKernel_integrable ht).mul_bdd hgi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => le_ciSup hbound (x - y))
  have hprod : Integrable (fun y : Vec3 => heatKernel y t *
      (⨆ z : Vec3, ‖v z‖)) volume := by
    simpa only [mul_comm] using
      (heatKernel_integrable ht).mul_const (⨆ z : Vec3, ‖v z‖)
  have hpoint : ∀ y : Vec3,
      ‖heatKernel y t * g y‖ ≤ heatKernel y t * (⨆ z : Vec3, ‖v z‖) := by
    intro y
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (le_ciSup hbound (x - y))
      (heatKernel_nonneg _ _)
  rw [heatConv_eq_integral]
  calc
    |∫ y : Vec3, heatKernel y t * g y| ≤
        ∫ y : Vec3, ‖heatKernel y t * g y‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun y : Vec3 => heatKernel y t * g y))
    _ ≤ ∫ y : Vec3, heatKernel y t * (⨆ z : Vec3, ‖v z‖) :=
      integral_mono_ae hcomp.norm hprod (Filter.Eventually.of_forall hpoint)
    _ = ⨆ z : Vec3, ‖v z‖ := by
      rw [integral_mul_const]
      simp only [heatKernel_integral t ht, one_mul]

private lemma heatConv_laplacian_integrableOn_Ioi_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u) (x : Vec3) :
    IntegrableOn (fun t : ℝ => heatConv t (CKN.spatialLaplacian u) x) (Ioi 0) := by
  let v : Vec3 → ℝ := CKN.spatialLaplacian u
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := CKN.contDiff_spatialLaplacian_smooth hu
  have hvs : HasCompactSupport v := by
    have hgi (i : Fin 3) : HasCompactSupport
        (CKN.spatialDeriv (CKN.spatialDeriv u i) i) :=
      (huSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)).fderiv_apply
        (𝕜 := ℝ) (CKN.basisVec i)
    have h01 : HasCompactSupport (fun y : Vec3 =>
        CKN.spatialDeriv (CKN.spatialDeriv u (0 : Fin 3)) 0 y +
          CKN.spatialDeriv (CKN.spatialDeriv u (1 : Fin 3)) 1 y) := by
      convert (hgi (0 : Fin 3)).add (hgi (1 : Fin 3)) using 1
    have hsum : HasCompactSupport (fun y : Vec3 =>
        CKN.spatialDeriv (CKN.spatialDeriv u (0 : Fin 3)) 0 y +
          CKN.spatialDeriv (CKN.spatialDeriv u (1 : Fin 3)) 1 y +
            CKN.spatialDeriv (CKN.spatialDeriv u (2 : Fin 3)) 2 y) := by
      convert h01.add (hgi (2 : Fin 3)) using 1
    change HasCompactSupport (fun y : Vec3 =>
      ∑ i : Fin 3, CKN.spatialDeriv (CKN.spatialDeriv u i) i y)
    simpa only [Fin.sum_univ_three] using hsum
  have hC : 0 ≤ ⨆ z : Vec3, ‖v z‖ := by
    exact le_ciSup_of_le (hv.continuous.norm.bddAbove_range_of_hasCompactSupport hvs.norm)
      (0 : Vec3) (norm_nonneg _)
  have hqcont : ContinuousOn (fun t : ℝ => heatConv t v x) (Ioi 0) := by
    intro t ht
    exact (heatConv_hasDerivAt_laplacianIntegral_smooth hv hvs ht x).continuousAt.continuousWithinAt
  have hnear : IntegrableOn (fun t : ℝ => heatConv t v x) (Ioc 0 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => (⨆ z : Vec3, ‖v z‖)) (Ioc 0 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine Integrable.mono' hconst
      ((hqcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using
      heatConv_abs_le_sup_smooth hv hvs ht.1 x
  have hinf : IntegrableOn (fun t : ℝ => heatConv t v x) (Ioi 1) := by
    have hpow : IntegrableOn (fun t : ℝ =>
        (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
          (t ^ (-(3 : ℝ) / 2) * ∫ y : Vec3, ‖v y‖)) (Ioi 1) := by
      have hpow' : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
      have hpow'' := hpow'.const_mul ((4 * Real.pi) ^ (-(3 : ℝ) / 2))
      change Integrable (fun t : ℝ =>
          (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
            (t ^ (-(3 : ℝ) / 2) * ∫ y : Vec3, ‖v y‖))
        (volume.restrict (Ioi 1))
      simpa only [mul_assoc] using hpow''.mul_const (∫ y : Vec3, ‖v y‖)
    have hmeas : AEStronglyMeasurable (fun t : ℝ => heatConv t v x)
        (volume.restrict (Ioi 1)) := by
      exact (hqcont.mono (Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable
        measurableSet_Ioi
    refine Integrable.mono' hpow hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 ≤ t := zero_le_one.trans (mem_Ioi.mp ht).le
    have hrewrite : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) =
        (4 * Real.pi) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) := by
      rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring,
        Real.mul_rpow (by positivity) htpos]
    have hb := heatConv_abs_le_prefactor_mul_integral_smooth hv hvs
      (lt_of_lt_of_le zero_lt_one (mem_Ioi.mp ht).le) x
    rw [hrewrite] at hb
    simpa only [Real.norm_eq_abs, mul_assoc] using hb
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1), integrableOn_union]
  exact ⟨hnear, hinf⟩

private lemma endpoint_interval_limit {q : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hq : IntegrableOn q (Ioc 0 b)) (C : ℝ)
    (hC : ∀ t ∈ Ioc 0 b, ‖q t‖ ≤ C) :
    Tendsto (fun a : ℝ => ∫ t in Ioc a b, q t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioc 0 b, q t)) := by
  have hC0 : 0 ≤ C := by
    have hmem : (b / 2) ∈ Ioc 0 b := by
      constructor <;> linarith only [hb]
    exact (norm_nonneg (q (b / 2))).trans (hC (b / 2) hmem)
  have hsmall (a : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      ‖∫ t in Ioc 0 a, q t‖ ≤ C * a := by
    have hbound := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (f := q) (s := Ioc 0 a) measure_Ioc_lt_top
      (fun t ht => hC t ⟨ht.1, le_trans ht.2 hab⟩)
    have hmeasure : volume.real (Ioc 0 a) = a := by
      rw [Measure.real, Real.volume_Ioc]
      rw [ENNReal.toReal_ofReal (sub_nonneg.mpr ha.le)]
      simp only [sub_zero]
    rw [hmeasure] at hbound
    exact hbound
  have hdiff (a : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      (∫ t in Ioc a b, q t) - ∫ t in Ioc 0 b, q t =
        -∫ t in Ioc 0 a, q t := by
    have hdisj : Disjoint (Ioc 0 a) (Ioc a b) := Ioc_disjoint_Ioc_of_le le_rfl
    have hunion : Ioc 0 a ∪ Ioc a b = Ioc 0 b := Ioc_union_Ioc_eq_Ioc ha.le hab
    have hq0 : IntegrableOn q (Ioc 0 a) := hq.mono_set (by
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hab⟩)
    have hqab : IntegrableOn q (Ioc a b) := hq.mono_set (by
      intro t ht
      exact ⟨lt_trans ha ht.1, ht.2⟩)
    have hsum := setIntegral_union hdisj measurableSet_Ioc hq0 hqab
    rw [hunion] at hsum
    linarith only [hsum]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hupper : Tendsto (fun a : ℝ => C * a) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (show Tendsto (fun _ : ℝ => C) (𝓝[>] 0) (𝓝 C) from tendsto_const_nhds).mul
        (tendsto_id.mono_left nhdsWithin_le_nhds)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0)) hupper
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with a ha hlt
    have ha' : 0 < a := ha
    have hab : a ≤ b := hlt.le
    have hrewrite := hdiff a ha' hab
    rw [hrewrite]
    simpa only [norm_neg] using hsmall a ha' hab

private lemma heatConv_integral_laplacian_eq_neg_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u) (x : Vec3) :
    ∫ t : ℝ in Ioi 0, heatConv t (CKN.spatialLaplacian u) x = -u x := by
  let f : ℝ → ℝ := fun t => heatConv t u x
  let q : ℝ → ℝ := fun t => heatConv t (CKN.spatialLaplacian u) x
  have hderiv : ∀ t ∈ Ioi 0, HasDerivAt f (q t) t := by
    intro t ht
    dsimp [f, q]
    convert heatConv_hasDerivAt_laplacianIntegral_smooth hu huSupport ht x using 1
    exact (heatKernel_laplacian_integral_eq_smooth hu huSupport ht x).symm
  have hqint : IntegrableOn q (Ioi 0) := by
    exact heatConv_laplacian_integrableOn_Ioi_smooth hu huSupport x
  have htail : ∫ t : ℝ in Ioi 1, q t = -f 1 := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto
      (a := (1 : ℝ)) (f := f) (f' := q) (m := 0)
      (hderiv 1 (by norm_num)).continuousAt.continuousWithinAt
      (fun t ht => hderiv t (lt_trans zero_lt_one (mem_Ioi.mp ht)))
      (hqint.mono_set (Ioi_subset_Ioi (by norm_num)))
      (heatConv_tendsto_zero_atTop_smooth hu huSupport x)
    simpa only [zero_sub] using h
  let v : Vec3 → ℝ := CKN.spatialLaplacian u
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := CKN.contDiff_spatialLaplacian_smooth hu
  have hvs : HasCompactSupport v := by
    have hgi (i : Fin 3) : HasCompactSupport
        (CKN.spatialDeriv (CKN.spatialDeriv u i) i) :=
      (huSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)).fderiv_apply
        (𝕜 := ℝ) (CKN.basisVec i)
    have h01 : HasCompactSupport (fun y : Vec3 =>
        CKN.spatialDeriv (CKN.spatialDeriv u (0 : Fin 3)) 0 y +
          CKN.spatialDeriv (CKN.spatialDeriv u (1 : Fin 3)) 1 y) := by
      convert (hgi (0 : Fin 3)).add (hgi (1 : Fin 3)) using 1
    have hsum : HasCompactSupport (fun y : Vec3 =>
        CKN.spatialDeriv (CKN.spatialDeriv u (0 : Fin 3)) 0 y +
          CKN.spatialDeriv (CKN.spatialDeriv u (1 : Fin 3)) 1 y +
            CKN.spatialDeriv (CKN.spatialDeriv u (2 : Fin 3)) 2 y) := by
      convert h01.add (hgi (2 : Fin 3)) using 1
    change HasCompactSupport (fun y : Vec3 =>
      ∑ i : Fin 3, CKN.spatialDeriv (CKN.spatialDeriv u i) i y)
    simpa only [Fin.sum_univ_three] using hsum
  have hC : 0 ≤ ⨆ z : Vec3, ‖v z‖ := by
    exact le_ciSup_of_le (hv.continuous.norm.bddAbove_range_of_hasCompactSupport hvs.norm)
      (0 : Vec3) (norm_nonneg _)
  have hnear_limit : ∫ t : ℝ in Ioc 0 1, q t = f 1 - u x := by
    have hqnear : IntegrableOn q (Ioc 0 1) :=
      hqint.mono_set Ioc_subset_Ioi_self
    have hqbound : ∀ t ∈ Ioc 0 1, ‖q t‖ ≤ ⨆ z : Vec3, ‖v z‖ := by
      intro t ht
      simpa only [q, Real.norm_eq_abs] using heatConv_abs_le_sup_smooth hv hvs ht.1 x
    have hlimit := endpoint_interval_limit zero_lt_one hqnear
      (⨆ z : Vec3, ‖v z‖) hqbound
    have hzero : Tendsto (fun a : ℝ => f 1 - f a) (𝓝[>] 0) (𝓝 (f 1 - u x)) := by
      simpa only [sub_eq_add_neg, add_zero] using
        (tendsto_const_nhds.sub
          (heatConv_tendsto_self_nhdsWithin_zero_smooth hu huSupport x))
    have hinterval (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
        ∫ t in Ioc a 1, q t = f 1 - f a := by
      rw [← intervalIntegral.integral_of_le ha1]
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        exact hderiv t (by
          rw [uIcc_of_le ha1] at ht
          exact lt_of_lt_of_le ha ht.1)
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
        exact hqint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le))
    have hright := hzero.congr' (by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with a ha0 ha1
      exact (hinterval a ha0 ha1.le).symm)
    exact tendsto_nhds_unique hlimit hright
  have htotal := intervalIntegral.integral_interval_add_Ioi hqint
    (hqint.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
  have htotal' : (∫ t : ℝ in Ioc 0 1, q t) + ∫ t : ℝ in Ioi 1, q t =
      ∫ t : ℝ in Ioi 0, q t := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact htotal
  rw [← htotal', hnear_limit, htail]
  dsimp [f]
  ring

/-- For a compactly supported smooth function, the heat representation gives the
    Newtonian potential of its Laplacian, with the displayed sign convention. -/
theorem newtonian_representation_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u) (x : Vec3) :
    u x = -∫ y : Vec3, newtonianKernel (x - y) * CKN.spatialLaplacian u y := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × Vec3 → ℝ := fun p =>
    heatKernel (x - p.2) p.1 * CKN.spatialLaplacian u p.2
  have hprod : Integrable F (μ.prod volume) := by
    exact heatKernel_laplacian_prod_integrable_smooth hu huSupport x
  have hscalar : ∫ t : ℝ, ∫ y : Vec3, F (t, y) ∂volume ∂μ = -u x := by
    calc
      ∫ t : ℝ, ∫ y : Vec3, F (t, y) ∂volume ∂μ =
          ∫ t : ℝ in Ioi 0, heatConv t (CKN.spatialLaplacian u) x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [show heatConv t (CKN.spatialLaplacian u) x = ∫ y : Vec3, F (t, y) ∂volume by
          rw [heatConv, MeasureTheory.convolution_eq_swap]
          rfl]
      _ = -u x := heatConv_integral_laplacian_eq_neg_smooth hu huSupport x
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun t y => F (t, y))
    (by
      change Integrable (fun p : ℝ × Vec3 => F p) (μ.prod volume)
      exact hprod)
  have hinner : (fun y : Vec3 => ∫ t : ℝ, F (t, y) ∂μ) =ᵐ[volume]
      (fun y => newtonianKernel (x - y) * CKN.spatialLaplacian u y) := by
    filter_upwards [Measure.ae_ne volume x] with y hy
    have hxy : x - y ≠ 0 := sub_ne_zero.mpr hy.symm
    have hk : Integrable (fun t : ℝ => heatKernel (x - y) t) μ := by
      change Integrable (fun t : ℝ => heatKernel (x - y) t)
        (volume.restrict (Ioi 0))
      apply Integrable.of_integral_ne_zero
      rw [heatKernel_integral_Ioi hxy]
      have hnorm : 0 < vec3EuclideanNorm (x - y) := by
        rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
        intro hz
        apply hxy
        exact (WithLp.toLp_eq_zero 2).mp hz
      exact ne_of_gt (by positivity)
    rw [show (fun t : ℝ => F (t, y)) =
        (fun t : ℝ => heatKernel (x - y) t * CKN.spatialLaplacian u y) by rfl]
    rw [integral_mul_const, heatKernel_integral_Ioi hxy]
    rfl
  have hright : ∫ y : Vec3, ∫ t : ℝ, F (t, y) ∂μ ∂volume =
      ∫ y : Vec3, newtonianKernel (x - y) * CKN.spatialLaplacian u y := by
    rw [integral_congr_ae hinner]
  have hC : (∫ y : Vec3, newtonianKernel (x - y) *
      CKN.spatialLaplacian u y) = -u x :=
    hright.symm.trans (hswap.symm.trans hscalar)
  linarith only [hC]

end CKN.Foundation.Heat
