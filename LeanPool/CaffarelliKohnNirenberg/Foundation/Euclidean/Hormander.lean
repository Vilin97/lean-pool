/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Hörmander condition for the Newtonian second-derivative kernel

The Calderón--Zygmund treatment of the second Newtonian derivative
`∂ᵢ∂ⱼN` on `ℝ³` (see `paper/ckn.tex`, §1, where the ambient space is `ℝ³`
with the Euclidean norm and the ball volume is `(4/3)πr³`; the classical
route chosen for the `L^{3/2}` bound on the pressure is recorded in the design
notes, `docs/DESIGN_NOTES.md`) needs the classical Hörmander kernel
condition: a kernel `K` whose gradient decays like `|x|⁻⁴` satisfies

  `∫_{|x| > 2|y|} |K(x - y) - K(x)| dx ≤ C`

with a constant `C` independent of `y` (Stein, *Singular Integrals and
Differentiability Properties of Functions*, Ch. II, §2).  The main result
of this file, `hormander_integral_bound`, is the explicit form of that
bound: if `‖∇K‖ ≤ C₂ |x|⁻⁴` off the origin then the integral above is at
most `64 π C₂`.

The proof has two elementary halves.  The mean value inequality on the
segment `[x - y, x]` gives the pointwise bound
`|K (x - y) - K x| ≤ 16 C₂ |y| |x|⁻⁴`, because every point of the segment
stays at distance at least `|x| / 2` from the origin; then the integral is
estimated on the geometric shells of ratio `4/3` around the origin, using
the exact annulus volumes.

Two modelling remarks.  `Vec3` carries the supremum norm by default, while
the decay hypothesis `hgrad` is stated with the operator norm on `Vec3` and
the Euclidean radius `vec3EuclideanNorm`.  No factor `√3` appears: the
operator norm is only ever applied to `‖x - (x - y)‖`, and since the
supremum norm is dominated by the Euclidean norm (`space_norm_le_euclideanNorm`)
the displacement contributes exactly `vec3EuclideanNorm y`.  All balls and
shells are Euclidean (`vec3Ball`), and the volume normalization
`volume_vec3Ball_eq` is the one of the paper.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open Filter MeasureTheory MeasureTheory.Measure Set Metric
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Foundation.Euclidean

private lemma norm_le_vec3EuclideanNorm (v : Vec3) : ‖v‖ ≤ vec3EuclideanNorm v := by
  simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using CKN.space_norm_le_euclideanNorm v

private lemma vec3EuclideanNorm_add_le (u v : Vec3) :
    vec3EuclideanNorm (u + v) ≤ vec3EuclideanNorm u + vec3EuclideanNorm v := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

private lemma le_vec3EuclideanNorm_sub_add (x z : Vec3) :
    vec3EuclideanNorm x ≤ vec3EuclideanNorm (x - z) + vec3EuclideanNorm z := by
  calc vec3EuclideanNorm x = vec3EuclideanNorm ((x - z) + z) := by rw [sub_add_cancel]
    _ ≤ vec3EuclideanNorm (x - z) + vec3EuclideanNorm z := vec3EuclideanNorm_add_le _ _

private lemma vec3EuclideanNorm_pos {v : Vec3} (hv : v ≠ 0) : 0 < vec3EuclideanNorm v := by
  rw [vec3EuclideanNorm_eq_l2]
  exact norm_pos_iff.mpr fun h => hv (WithLp.toLp_injective 2 (by simpa using h))

private lemma rpow_neg_four {r : ℝ} (hr : 0 < r) : r ^ (-(4:ℝ)) = (r ^ 4)⁻¹ := by
  rw [Real.rpow_neg (le_of_lt hr)]
  norm_num

private lemma div_two_rpow_neg_four {r : ℝ} (hr : 0 < r) :
    (r / 2) ^ (-(4:ℝ)) = 16 * r ^ (-(4:ℝ)) := by
  rw [rpow_neg_four (by positivity), rpow_neg_four hr]
  field_simp
  ring

/-- Pointwise Hörmander bound at a fixed pair `(x - y, x)`: on the segment the
Euclidean norm stays above `‖x‖ / 2`, so the gradient hypothesis and the mean
value inequality give `|K (x - y) - K x| ≤ 16 C₂ ‖y‖ ‖x‖⁻⁴`. -/
private lemma hormander_pointwise {K : Vec3 → ℝ} {C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hdiff : ∀ x, x ≠ 0 → DifferentiableAt ℝ K x)
    (hgrad : ∀ x, x ≠ 0 → ‖fderiv ℝ K x‖ ≤ C₂ * (vec3EuclideanNorm x) ^ (-(4 : ℝ)))
    {y x : Vec3} (hy : y ≠ 0) (hx : 2 * vec3EuclideanNorm y < vec3EuclideanNorm x) :
    |K (x - y) - K x| ≤ 16 * C₂ * vec3EuclideanNorm y * (vec3EuclideanNorm x) ^ (-(4:ℝ)) := by
  have ha : 0 < vec3EuclideanNorm y := vec3EuclideanNorm_pos hy
  have hr : 0 < vec3EuclideanNorm x := by linarith only [ha, hx]
  have hseg : ∀ z ∈ segment ℝ (x - y) x, vec3EuclideanNorm x / 2 ≤ vec3EuclideanNorm z := by
    intro z hz
    rw [segment_eq_image' ℝ (x - y) x] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have hdecomp : (x - y) + θ • (x - (x - y)) = x - (1 - θ) • y := by
      rw [sub_sub_cancel x y, sub_smul, one_smul]
      abel
    dsimp only
    rw [hdecomp]
    have habs : |1 - θ| ≤ 1 := by
      rw [abs_of_nonneg (by linarith only [hθ.2])]
      linarith only [hθ.1]
    have hsplit := le_vec3EuclideanNorm_sub_add x ((1 - θ) • y)
    rw [vec3EuclideanNorm_smul] at hsplit
    nlinarith only [hsplit, habs, abs_nonneg (1 - θ), ha, hr, hx]
  have hseg0 : ∀ z ∈ segment ℝ (x - y) x, z ≠ 0 := by
    intro z hz hz0
    have h := hseg z hz
    rw [hz0, vec3EuclideanNorm_zero] at h
    linarith only [h, hr]
  have hf : ∀ z ∈ segment ℝ (x - y) x, DifferentiableAt ℝ K z :=
    fun z hz => hdiff z (hseg0 z hz)
  have hbound : ∀ z ∈ segment ℝ (x - y) x,
      ‖fderiv ℝ K z‖ ≤ 16 * C₂ * (vec3EuclideanNorm x) ^ (-(4:ℝ)) := by
    intro z hz
    calc ‖fderiv ℝ K z‖ ≤ C₂ * (vec3EuclideanNorm z) ^ (-(4:ℝ)) := hgrad z (hseg0 z hz)
      _ ≤ C₂ * (vec3EuclideanNorm x / 2) ^ (-(4:ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (by linarith only [hr]) (hseg z hz) (by norm_num)) hC₂
      _ = 16 * C₂ * (vec3EuclideanNorm x) ^ (-(4:ℝ)) := by
          rw [div_two_rpow_neg_four hr]
          ring
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := K) (C := 16 * C₂ * (vec3EuclideanNorm x) ^ (-(4:ℝ))) hf hbound
      (convex_segment (x - y) x) (left_mem_segment ℝ (x - y) x)
      (right_mem_segment ℝ (x - y) x)
  have hCnn : 0 ≤ 16 * C₂ * (vec3EuclideanNorm x) ^ (-(4:ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hC₂) (Real.rpow_nonneg (vec3EuclideanNorm_nonneg x) _)
  have hnormy : ‖x - (x - y)‖ ≤ vec3EuclideanNorm y := by
    rw [sub_sub_cancel]
    exact norm_le_vec3EuclideanNorm y
  calc |K (x - y) - K x| = ‖K x - K (x - y)‖ := by
        rw [Real.norm_eq_abs, abs_sub_comm]
    _ ≤ (16 * C₂ * (vec3EuclideanNorm x) ^ (-(4:ℝ))) * vec3EuclideanNorm y :=
        le_trans hmvt (mul_le_mul_of_nonneg_left hnormy hCnn)
    _ = 16 * C₂ * vec3EuclideanNorm y * (vec3EuclideanNorm x) ^ (-(4:ℝ)) := by ring

/-- Integral of the model kernel `‖x‖⁻⁴` over the exterior of the ball of radius
`2 ‖y‖`: the geometric shells of ratio `4/3` give `≤ 4π / ‖y‖`. -/
private lemma lintegral_rpow_neg_four {y : Vec3} (hy : y ≠ 0) :
    ∫⁻ x in {x : Vec3 | 2 * vec3EuclideanNorm y < vec3EuclideanNorm x},
        ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ)))
      ≤ ENNReal.ofReal (4 * Real.pi / vec3EuclideanNorm y) := by
  set a : ℝ := vec3EuclideanNorm y with ha_def
  have ha : 0 < a := by rw [ha_def]; exact vec3EuclideanNorm_pos hy
  set R : ℝ := 2 * a with hR_def
  have hR : 0 < R := by rw [hR_def]; linarith only [ha]
  have hregion : {x : Vec3 | 2 * vec3EuclideanNorm y < vec3EuclideanNorm x}
      = {x : Vec3 | R < vec3EuclideanNorm x} := by
    rw [hR_def, ha_def]
  rw [hregion]
  have hcover : {x : Vec3 | R < vec3EuclideanNorm x} ⊆
      ⋃ m : ℕ, (vec3Ball (0 : Vec3) ((4/3:ℝ)^(m+1) * R) \ vec3Ball (0 : Vec3) ((4/3:ℝ)^m * R)) := by
    intro x hx
    change R < vec3EuclideanNorm x at hx
    simp only [mem_iUnion]
    have hex : ∃ n : ℕ, vec3EuclideanNorm x < (4/3:ℝ)^n * R := by
      have h1 : Tendsto (fun n : ℕ => (4/3:ℝ)^n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      have h2 : Tendsto (fun n : ℕ => (4/3:ℝ)^n * R) atTop atTop := h1.atTop_mul_const hR
      exact (h2.eventually (eventually_gt_atTop (vec3EuclideanNorm x))).exists
    have hk := Nat.find_spec hex
    have hk0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h, pow_zero, one_mul] at hk
      linarith only [hk, hx]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    refine ⟨m, ?_⟩
    simp only [Set.mem_sdiff, mem_vec3Ball, sub_zero]
    rw [hm] at hk
    exact ⟨hk, Nat.find_min hex (by rw [hm]; exact Nat.lt_succ_self m)⟩
  have hstep1 : ∫⁻ x in {x : Vec3 | R < vec3EuclideanNorm x},
        ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ)))
      ≤ ∫⁻ x in ⋃ m : ℕ, (vec3Ball (0 : Vec3) ((4/3:ℝ)^(m+1) * R) \ vec3Ball (0 : Vec3) ((4/3:ℝ)^m
        * R)),
          ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ))) := lintegral_mono_set hcover
  have hstep2 : ∫⁻ x in {x : Vec3 | R < vec3EuclideanNorm x},
        ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ)))
      ≤ ∑' m : ℕ, ∫⁻ x in (vec3Ball (0 : Vec3) ((4/3:ℝ)^(m+1) * R) \ vec3Ball (0 : Vec3)
        ((4/3:ℝ)^m * R)),
          ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ))) :=
    hstep1.trans (lintegral_iUnion_le _ _)
  refine hstep2.trans ?_
  set c : ℝ := (4 * Real.pi / 3) * ((4/3:ℝ)^3 - 1) * R⁻¹ with hc_def
  have hc : 0 ≤ c := by rw [hc_def]; positivity
  have hsub34 : 1 - ENNReal.ofReal (3/4:ℝ) = ENNReal.ofReal (1/4:ℝ) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1:ℝ) (by norm_num : (0:ℝ) ≤ 3/4)]
    norm_num
  have hgeom : (1 - ENNReal.ofReal (3/4:ℝ))⁻¹ = ENNReal.ofReal 4 := by
    rw [hsub34, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1/4)]
    norm_num
  have hterm : ∀ m : ℕ,
      ∫⁻ x in (vec3Ball (0 : Vec3) ((4/3:ℝ)^(m+1) * R) \ vec3Ball (0 : Vec3) ((4/3:ℝ)^m * R)),
          ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ)))
        ≤ ENNReal.ofReal c * (ENNReal.ofReal (3/4:ℝ))^m := by
    intro m
    set qi : ℝ := (4/3:ℝ)^m * R with hqi_def
    set qo : ℝ := (4/3:ℝ)^(m+1) * R with hqo_def
    have hqi_pos : 0 < qi := by rw [hqi_def]; positivity
    have hqo_pos : 0 < qo := by rw [hqo_def]; positivity
    have hqo_eq : qo = (4/3:ℝ) * qi := by
      rw [hqi_def, hqo_def, pow_succ]
      ring
    have hle_qi_qo : qi ≤ qo := by rw [hqo_eq]; nlinarith only [hqi_pos]
    have hsub : vec3Ball (0 : Vec3) qi ⊆ vec3Ball (0 : Vec3) qo := vec3Ball_mono hle_qi_qo
    have hfin : volume (vec3Ball (0 : Vec3) qi) ≠ ∞ := by
      rw [volume_vec3Ball_eq]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    have hvol : volume (vec3Ball (0 : Vec3) qo \ vec3Ball (0 : Vec3) qi)
        = ENNReal.ofReal ((Real.pi * 4 / 3) * (qo^3 - qi^3)) := by
      rw [measure_sdiff hsub (vec3Ball_measurable _ _).nullMeasurableSet hfin,
          volume_vec3Ball_eq (0 : Vec3) qo, volume_vec3Ball_eq (0 : Vec3) qi,
          ← ENNReal.ofReal_pow hqo_pos.le, ← ENNReal.ofReal_pow hqi_pos.le,
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ qo^3 by positivity),
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ qi^3 by positivity),
          ← ENNReal.ofReal_sub (qo^3 * (Real.pi * 4 / 3))
            (show (0:ℝ) ≤ qi^3 * (Real.pi * 4 / 3) by positivity)]
      congr 1
      ring
    have hmem : ∀ x ∈ vec3Ball (0 : Vec3) qo \ vec3Ball (0 : Vec3) qi,
        qi ≤ vec3EuclideanNorm x := by
      intro x hx
      simp only [Set.mem_sdiff, mem_vec3Ball, sub_zero] at hx
      exact le_of_not_gt hx.2
    have hpoint : ∀ x ∈ vec3Ball (0 : Vec3) qo \ vec3Ball (0 : Vec3) qi,
        ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ))) ≤ ENNReal.ofReal (qi ^ (-(4:ℝ))) := by
      intro x hx
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos hqi_pos (hmem x hx) (by norm_num))
    have h34 : (3/4:ℝ)^m = ((4/3:ℝ)^m)⁻¹ := by
      rw [← inv_pow (4/3:ℝ) m]
      norm_num
    have halg : qi ^ (-(4:ℝ)) * ((Real.pi * 4 / 3) * (qo^3 - qi^3))
        = ((4 * Real.pi / 3) * ((4/3:ℝ)^3 - 1) * R⁻¹) * (3/4:ℝ)^m := by
      rw [rpow_neg_four hqi_pos, hqo_eq, hqi_def, h34]
      field_simp
    calc ∫⁻ x in (vec3Ball (0 : Vec3) qo \ vec3Ball (0 : Vec3) qi),
            ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ)))
        ≤ ∫⁻ x in (vec3Ball (0 : Vec3) qo \ vec3Ball (0 : Vec3) qi),
            ENNReal.ofReal (qi ^ (-(4:ℝ))) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem
            (vec3Ball_measurable (0 : Vec3) qo |>.diff (vec3Ball_measurable (0 : Vec3) qi))]
            with x hx
          exact hpoint x hx
      _ = ENNReal.ofReal (qi ^ (-(4:ℝ))) * volume (vec3Ball (0 : Vec3) qo \ vec3Ball (0 : Vec3)
        qi) := by
          rw [lintegral_const, restrict_apply_univ]
      _ = ENNReal.ofReal (qi ^ (-(4:ℝ))) * ENNReal.ofReal ((Real.pi * 4 / 3) * (qo^3 - qi^3)) := by
          rw [hvol]
      _ = ENNReal.ofReal (qi ^ (-(4:ℝ)) * ((Real.pi * 4 / 3) * (qo^3 - qi^3))) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hqi_pos.le _)]
      _ = ENNReal.ofReal (c * (3/4:ℝ)^m) := by
          rw [halg, hc_def]
      _ = ENNReal.ofReal c * (ENNReal.ofReal (3/4:ℝ))^m := by
          rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 3/4)]
  calc ∑' m : ℕ, ∫⁻ x in (vec3Ball (0 : Vec3) ((4/3:ℝ)^(m+1) * R) \ vec3Ball (0 : Vec3) ((4/3:ℝ)^m
    * R)),
            ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ)))
      ≤ ∑' m : ℕ, ENNReal.ofReal c * (ENNReal.ofReal (3/4:ℝ))^m := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal c * ∑' m : ℕ, (ENNReal.ofReal (3/4:ℝ))^m := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal c * ENNReal.ofReal 4 := by
        rw [ENNReal.tsum_geometric, hgeom]
    _ = ENNReal.ofReal (c * 4) := by rw [ENNReal.ofReal_mul hc]
    _ ≤ ENNReal.ofReal (4 * Real.pi / a) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hc_def, hR_def, show ((4/3:ℝ)^3 - 1) = 37/27 by norm_num, mul_inv]
        field_simp
        nlinarith only [Real.pi_pos, ha]

/-- **Hörmander condition.**  If `K` is differentiable off the origin with
`|∇K| ≤ C₂ |x|⁻⁴`, then for every `y ≠ 0` the integral of `|K (x - y) - K x|`
over the region `|x| > 2 |y|` is at most `64 π C₂`, uniformly in `y`. -/
theorem hormander_integral_bound {K : Vec3 → ℝ} {C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hdiff : ∀ x, x ≠ 0 → DifferentiableAt ℝ K x)
    (hgrad : ∀ x, x ≠ 0 → ‖fderiv ℝ K x‖ ≤ C₂ * (vec3EuclideanNorm x) ^ (-(4 : ℝ)))
    {y : Vec3} (hy : y ≠ 0) :
    ∫⁻ x in {x | 2 * vec3EuclideanNorm y < vec3EuclideanNorm x},
        ENNReal.ofReal |K (x - y) - K x| ≤ ENNReal.ofReal (64 * Real.pi * C₂) := by
  have hfac : 0 ≤ 16 * C₂ * vec3EuclideanNorm y :=
    mul_nonneg (mul_nonneg (by norm_num) hC₂) (vec3EuclideanNorm_nonneg y)
  have hmeas : MeasurableSet {x : Vec3 | 2 * vec3EuclideanNorm y < vec3EuclideanNorm x} := by
    refine measurableSet_lt measurable_const ?_
    unfold vec3EuclideanNorm
    fun_prop
  calc ∫⁻ x in {x | 2 * vec3EuclideanNorm y < vec3EuclideanNorm x},
          ENNReal.ofReal |K (x - y) - K x|
      ≤ ∫⁻ x in {x | 2 * vec3EuclideanNorm y < vec3EuclideanNorm x},
          ENNReal.ofReal (16 * C₂ * vec3EuclideanNorm y * (vec3EuclideanNorm x) ^ (-(4:ℝ))) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hmeas] with x hx
        exact ENNReal.ofReal_le_ofReal (hormander_pointwise hC₂ hdiff hgrad hy hx)
    _ = ENNReal.ofReal (16 * C₂ * vec3EuclideanNorm y) *
          ∫⁻ x in {x | 2 * vec3EuclideanNorm y < vec3EuclideanNorm x},
            ENNReal.ofReal ((vec3EuclideanNorm x) ^ (-(4:ℝ))) := by
        rw [← lintegral_const_mul' (ENNReal.ofReal (16 * C₂ * vec3EuclideanNorm y)) _
          ENNReal.ofReal_ne_top]
        apply lintegral_congr_ae
        filter_upwards with x
        rw [ENNReal.ofReal_mul hfac]
    _ ≤ ENNReal.ofReal (16 * C₂ * vec3EuclideanNorm y) *
          ENNReal.ofReal (4 * Real.pi / vec3EuclideanNorm y) :=
        mul_le_mul_right (lintegral_rpow_neg_four hy)
          (ENNReal.ofReal (16 * C₂ * vec3EuclideanNorm y))
    _ = ENNReal.ofReal (64 * Real.pi * C₂) := by
        rw [← ENNReal.ofReal_mul hfac]
        congr 1
        have hy' : vec3EuclideanNorm y ≠ 0 := ne_of_gt (vec3EuclideanNorm_pos hy)
        field_simp
        ring

end CKN.Foundation.Euclidean
