/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Mean
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence

/-!
# Interior Display Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat


/-- Common coefficient for the displayed harmonic value, gradient and integral estimates. -/
noncomputable def harmonicInteriorDisplayConstant : ℝ :=
  max (max weakHarmonicInteriorSupConstant
    (576 * weakHarmonicInteriorSupConstant))
    (max (1728 * harmonicInteriorGradientSupConstant)
      (max ((Real.pi * 4 / 3) * weakHarmonicInteriorSupConstant ^ (3 / 2 : ℝ))
        ((Real.pi * 4 / 3) *
          (6 * (1728 * harmonicInteriorGradientSupConstant)) ^ (3 / 2 : ℝ))))

lemma harmonicInteriorDisplayConstant_nonneg :
    0 ≤ harmonicInteriorDisplayConstant := by
  dsimp [harmonicInteriorDisplayConstant]
  have hS := weakHarmonicInteriorSupConstant_nonneg
  have hG := harmonicInteriorGradientSupConstant_nonneg
  positivity

lemma convex_euclideanBall {x₀ : Vec3} {R : ℝ} (hR : 0 < R) :
    Convex ℝ (euclideanBall x₀ R) := by
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  rw [segment_eq_image] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  have hx' : vec3EuclideanNorm (x - x₀) < R := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hx
  have hy' : vec3EuclideanNorm (y - x₀) < R := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
  rw [show ((1 - θ) • x + θ • y) - x₀ =
      (1 - θ) • (x - x₀) + θ • (y - x₀) by
        simp only [smul_sub]
        module]
  have hcalc : vec3EuclideanNorm ((1 - θ) • (x - x₀) + θ • (y - x₀)) < R := by
    rw [vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 ((1 - θ) • (x - x₀) + θ • (y - x₀))‖ ≤
          ‖WithLp.toLp 2 ((1 - θ) • (x - x₀))‖ +
            ‖WithLp.toLp 2 (θ • (y - x₀))‖ := norm_add_le _ _
      _ = |1 - θ| * vec3EuclideanNorm (x - x₀) +
            |θ| * vec3EuclideanNorm (y - x₀) := by
        simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_smul, norm_smul,
          Real.norm_eq_abs]
      _ < (1 - θ) * R + θ * R := by
        have hθ0 : 0 ≤ θ := hθ.1
        have hθ1 : θ ≤ 1 := hθ.2
        rw [abs_of_nonneg hθ0, abs_of_nonneg (sub_nonneg.mpr hθ1)]
        by_cases hθz : θ = 0
        · simp only [hθz, sub_zero, one_mul, zero_mul, add_zero, gt_iff_lt]
          exact hx'
        by_cases hθo : θ = 1
        · simp only [hθo, sub_self, zero_mul, one_mul, zero_add, gt_iff_lt]
          exact hy'
        have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθz)
        have hθlt : θ < 1 := lt_of_le_of_ne hθ1 hθo
        gcongr
      _ = R := by ring
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hcalc

lemma fderiv_norm_le_three_classicalGradient
    {f : Vec3 → ℝ} (x : Vec3) :
    ‖fderiv ℝ f x‖ ≤ 3 * vec3EuclideanNorm (classicalGradient f x) := by
  have hbase : ‖fderiv ℝ f x‖ ≤ 3 * ‖classicalGradient f x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    calc
      ‖(fderiv ℝ f x) z‖ =
          ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
        have hz : (fderiv ℝ f x) z =
            ∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i) := by
          conv_lhs => rw [← sum_smul_basisVec z]
          rw [_root_.map_sum]
          simp only [map_smul]
        exact congrArg norm hz
      _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ f x) (basisVec i)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ‖z‖ * ‖classicalGradient f x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs]
        have hz : |z i| ≤ ‖z‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
        have hg : |(fderiv ℝ f x) (basisVec i)| ≤
            ‖classicalGradient f x‖ := by
          simpa only [classicalGradient_apply, Real.norm_eq_abs] using
            norm_le_pi_norm (classicalGradient f x) i
        exact mul_le_mul hz hg (abs_nonneg _) (norm_nonneg _)
      _ = 3 * ‖classicalGradient f x‖ * ‖z‖ := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (CKN.space_norm_le_euclideanNorm (classicalGradient f x)) (by positivity))

lemma euclideanBall_subset_closedBall {x : Vec3} {ε : ℝ} (hε : 0 < ε) :
    euclideanBall x ε ⊆ Metric.closedBall x ε := by
  intro y hy
  apply Metric.mem_closedBall.mpr
  rw [dist_eq_norm]
  have hy' : vec3EuclideanNorm (y - x) < ε := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hε).1 hy
  exact (CKN.space_norm_le_euclideanNorm (y - x)).trans hy'.le

lemma tsupport_spatialDeriv_subset {ψ : Vec3 → ℝ} (i : Fin 3) :
    tsupport (spatialDeriv ψ i) ⊆ tsupport ψ := by
  apply closure_minimal
  · intro x hx
    by_contra hxt
    exact hx (by simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt])
  · exact isClosed_tsupport ψ

lemma spatialLaplacian_zero_off
    {ψ : Vec3 → ℝ} {U : Set Vec3} (hψU : tsupport ψ ⊆ U)
    {x : Vec3} (hx : x ∉ U) : spatialLaplacian ψ x = 0 := by
  have hxψ : x ∉ tsupport ψ := fun h => hx (hψU h)
  unfold spatialLaplacian
  apply Finset.sum_eq_zero
  intro i hi
  have hxi : x ∉ tsupport (spatialDeriv ψ i) :=
    fun h => hxψ (tsupport_spatialDeriv_subset i h)
  simp only [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxi,
    zero_apply]

lemma local_weak_harmonic
    {h : Vec3 → ℝ} {U V : Set Vec3} (hVU : V ⊆ U)
    (hweak : WeaklyHarmonicOn U h) : WeaklyHarmonicOn V h := by
  intro ψ hψ hψc hψV
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [spatialLaplacian_zero_off hψV hx, mul_zero])]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [spatialLaplacian_zero_off (hψV.trans hVU) hx, mul_zero])]
  exact hweak ψ hψ hψc (hψV.trans hVU)

lemma local_value_bound
    {h : Vec3 → ℝ} {x₀ x : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (3 * ρ / 4))
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h) :
    ∃ v : ℝ, |v| ≤ 576 * weakHarmonicInteriorSupConstant *
      (ρ ^ 2)⁻¹ * lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) := by
  let ε : ℝ := ρ / 24
  let V : Set Vec3 := euclideanBall x ε
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hVsub : V ⊆ euclideanBall x₀ ρ := by
    exact (euclideanBall_subset_closedBall hε).trans
      (closedBall_subset_euclideanBall hρ hε hx (by
      dsimp [ε]
      nlinarith only [hρ]))
  have hVmeas : MeasurableSet V := by
    dsimp [V]
    exact (isOpen_lt (contDiff_euclideanSqDist_left x).continuous continuous_const).measurableSet
  have hmemV := hmem.mono_measure (Measure.restrict_mono_set volume hVsub)
  have hweakV : WeaklyHarmonicOn V h :=
    local_weak_harmonic hVsub hweak
  obtain ⟨H, hHdiff, hHae, hHbound, hHgrad⟩ :=
    weakly_harmonic_interior_smooth hε hmemV hweakV
  refine ⟨H x, ?_⟩
  have hxcenter : x ∈ euclideanBall x (ε / 2) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    simpa [sub_self, vecEuclideanNorm, vecNormSq, vecDot] using (half_pos hε)
  have hbound := hHbound x hxcenter
  have hmono : lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict V) ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) := by
    rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
    exact ENNReal.toReal_mono hmem.eLpNorm_lt_top.ne
      (eLpNorm_mono_measure h (Measure.restrict_mono_set volume hVsub))
  have hscale : (ε ^ 2)⁻¹ = 576 * (ρ ^ 2)⁻¹ := by
    dsimp [ε]
    field_simp [hρ.ne']
    ring
  rw [hscale] at hbound
  have hK := weakHarmonicInteriorSupConstant_nonneg
  have hcoef : 0 ≤ 576 * weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ := by
    positivity
  calc
    |H x| ≤ weakHarmonicInteriorSupConstant *
        (576 * (ρ ^ 2)⁻¹) *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict V) := hbound
    _ = 576 * weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict V) := by ring
    _ ≤ 576 * weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) :=
      mul_le_mul_of_nonneg_left hmono hcoef

lemma norm_sub_le_gradient_on_euclideanBall
    {H : Vec3 → ℝ} {x₀ : Vec3} {R G : ℝ} (hR : 0 < R)
    (hH : ContDiffOn ℝ (1 : ℕ∞) H (euclideanBall x₀ R))
    (hgrad : ∀ x ∈ euclideanBall x₀ R,
      vec3EuclideanNorm (classicalGradient H x) ≤ G)
    {x y : Vec3} (hx : x ∈ euclideanBall x₀ R)
    (hy : y ∈ euclideanBall x₀ R) :
    |H y - H x| ≤ 3 * G * vec3EuclideanNorm (y - x) := by
  have hopen : IsOpen (euclideanBall x₀ R) := by
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hconv := convex_euclideanBall (x₀ := x₀) hR
  have hfderiv : ∀ z ∈ euclideanBall x₀ R,
      HasFDerivWithinAt H (fderiv ℝ H z) (euclideanBall x₀ R) z := by
    intro z hz
    exact ((hH.contDiffAt (hopen.mem_nhds hz)).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have hbound : ∀ z ∈ euclideanBall x₀ R,
      ‖fderiv ℝ H z‖ ≤ 3 * G := by
    intro z hz
    exact (fderiv_norm_le_three_classicalGradient z).trans
      (mul_le_mul_of_nonneg_left (hgrad z hz) (by positivity))
  have hmean := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    hfderiv hbound hx hy
  have hGnonneg : 0 ≤ G :=
    (vec3EuclideanNorm_nonneg (classicalGradient H x)).trans (hgrad x hx)
  calc
    |H y - H x| = ‖H y - H x‖ := by rw [Real.norm_eq_abs]
    _ ≤ 3 * G * ‖y - x‖ := hmean
    _ ≤ 3 * G * vec3EuclideanNorm (y - x) := by
      gcongr
      exact CKN.space_norm_le_euclideanNorm (y - x)

lemma euclideanBall_eq_vec3Ball_display {x₀ : Vec3} {R : ℝ} (hR : 0 < R) :
    euclideanBall x₀ R = vec3Ball x₀ R := by
  ext x
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hR)

lemma set_integral_rpow_bound
    {f : Vec3 → ℝ} {s : Set Vec3} {S : ℝ}
    (hf : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict s))
    (hsvol : volume s ≠ ∞)
    (hbound : ∀ᵐ x ∂volume.restrict s, |f x| ≤ S) :
    (∫ x in s, |f x| ^ (3 / 2 : ℝ)) ≤
      (volume s).toReal * S ^ (3 / 2 : ℝ) := by
  have hfint := hf.integrable_norm_rpow (by norm_num) (by norm_num)
  have hp : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
    norm_num
  have hfint' : Integrable (fun x => |f x| ^ (3 / 2 : ℝ))
      (volume.restrict s) := by
    simpa only [Real.norm_eq_abs, hp] using hfint
  have hcint : Integrable (fun _ : Vec3 => S ^ (3 / 2 : ℝ))
      (volume.restrict s) := by
    exact integrableOn_const (μ := volume) (s := s) hsvol (by finiteness)
  have hpow : ∀ᵐ x ∂volume.restrict s,
      |f x| ^ (3 / 2 : ℝ) ≤ S ^ (3 / 2 : ℝ) := by
    filter_upwards [hbound] with x hx
    exact Real.rpow_le_rpow (abs_nonneg _) hx (by norm_num)
  calc
    (∫ x in s, |f x| ^ (3 / 2 : ℝ)) ≤
        ∫ x in s, S ^ (3 / 2 : ℝ) := integral_mono_ae hfint' hcint hpow
    _ = (volume s).toReal * S ^ (3 / 2 : ℝ) := by
      rw [MeasureTheory.setIntegral_const]
      simp [MeasureTheory.measureReal_def, smul_eq_mul]

lemma plain_display_scaling
    {r ρ K L A : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hL : 0 ≤ L) :
    (r ^ 2)⁻¹ * (A * r ^ 3 * (K * (ρ ^ 2)⁻¹ * L) ^ (3 / 2 : ℝ)) =
      (A * K ^ (3 / 2 : ℝ)) * (r / ρ) * (ρ ^ 2)⁻¹ *
        L ^ (3 / 2 : ℝ) := by
  rw [Real.mul_rpow (mul_nonneg hK (by positivity)) hL]
  rw [Real.mul_rpow hK (by positivity : 0 ≤ (ρ ^ 2)⁻¹)]
  have hρpow : ((ρ ^ 2)⁻¹) ^ (3 / 2 : ℝ) = ρ ^ (-3 : ℝ) := by
    rw [Real.inv_rpow (by positivity)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ ρ)]
    norm_num
  rw [hρpow]
  norm_num
  field_simp [hr.ne', hρ.ne']

lemma oscillation_display_scaling
    {r ρ G L A : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hG : 0 ≤ G)
    (hL : 0 ≤ L) :
    (r ^ 2)⁻¹ * (A * r ^ 3 * (6 * G * (ρ ^ 3)⁻¹ * L * r) ^ (3 / 2 : ℝ)) =
      (A * (6 * G) ^ (3 / 2 : ℝ)) * (r / ρ) ^ (5 / 2 : ℝ) *
        (ρ ^ 2)⁻¹ * L ^ (3 / 2 : ℝ) := by
  rw [show 6 * G * (ρ ^ 3)⁻¹ * L * r =
      (6 * G) * ((ρ ^ 3)⁻¹ * (L * r)) by ring]
  rw [Real.mul_rpow (by positivity : 0 ≤ 6 * G)
    (by positivity : 0 ≤ (ρ ^ 3)⁻¹ * (L * r))]
  rw [Real.mul_rpow (by positivity : 0 ≤ (ρ ^ 3)⁻¹)
    (by positivity : 0 ≤ L * r)]
  rw [Real.mul_rpow (by positivity : 0 ≤ L) (by positivity : 0 ≤ r)]
  have hρpow : ((ρ ^ 3)⁻¹) ^ (3 / 2 : ℝ) = ρ ^ (-9 / 2 : ℝ) := by
    rw [Real.inv_rpow (by positivity)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ ρ)]
    norm_num
    rw [← Real.inv_rpow (by positivity : 0 ≤ ρ)]
    rw [Real.rpow_neg_eq_inv_rpow]
  rw [hρpow]
  rw [Real.div_rpow (by positivity : 0 ≤ r) (by positivity : 0 ≤ ρ)]
  rw [show (ρ ^ 2)⁻¹ = ρ ^ (-2 : ℝ) by
    rw [← Real.rpow_natCast, Real.rpow_neg (by positivity)]; norm_num]
  rw [show (r ^ 2)⁻¹ = r ^ (-2 : ℝ) by
    rw [← Real.rpow_natCast, Real.rpow_neg (by positivity)]; norm_num]
  have hrpow : r ^ (-2 : ℝ) * r ^ (3 : ℕ) * r ^ (3 / 2 : ℝ) =
      r ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr, ← Real.rpow_add hr]
    norm_num
  have hρcombine : ρ ^ (-(9 / 2 : ℝ)) * ρ ^ (5 / 2 : ℝ) =
      ρ ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hρ]
    norm_num
  field_simp [hr.ne', hρ.ne']
  calc
    r ^ (-2 : ℝ) * A * r ^ (3 : ℕ) * (6 * G) ^ (3 / 2 : ℝ) *
          ρ ^ (-(9 / 2 : ℝ)) * L ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) *
          ρ ^ (5 / 2 : ℝ) =
        A * (6 * G) ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) *
          (r ^ (-2 : ℝ) * r ^ (3 : ℕ) * r ^ (3 / 2 : ℝ)) *
          (ρ ^ (-(9 / 2 : ℝ)) * ρ ^ (5 / 2 : ℝ)) := by ring
    _ = A * (6 * G) ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) *
          r ^ (5 / 2 : ℝ) * ρ ^ (-2 : ℝ) := by
      rw [hrpow, hρcombine]

lemma euclideanBall_pair_distance_le
    {x₀ x y : Vec3} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ euclideanBall x₀ r) (hy : y ∈ euclideanBall x₀ r) :
    vec3EuclideanNorm (y - x) ≤ 2 * r := by
  have hx' : vec3EuclideanNorm (x - x₀) < r := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
  have hy' : vec3EuclideanNorm (y - x₀) < r := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
  have htri : vec3EuclideanNorm (y - x) ≤
      vec3EuclideanNorm (y - x₀) + vec3EuclideanNorm (x - x₀) := by
    rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
      vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 (y - x)‖ =
          ‖WithLp.toLp 2 ((y - x₀) + (x₀ - x))‖ := by
            congr 1
            ext i
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
      _ ≤ ‖WithLp.toLp 2 (y - x₀)‖ +
          ‖WithLp.toLp 2 (x₀ - x)‖ := norm_add_le _ _
      _ = ‖WithLp.toLp 2 (y - x₀)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := by
        rw [show x₀ - x = -(x - x₀) by module]
        simp only [WithLp.toLp_sub, neg_sub, _root_.add_right_inj]
        rw [norm_sub_rev]
  nlinarith only [htri, hx', hy']

end CKN.Foundation.Heat
