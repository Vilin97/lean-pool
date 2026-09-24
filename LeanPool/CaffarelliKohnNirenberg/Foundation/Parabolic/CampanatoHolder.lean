/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Campanato
public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecOn

/-!
# Campanato Holder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Foundation.Parabolic
def ParabolicBallLpOscillation (f : ParabolicPoint → ℝ) (z : ParabolicPoint)
    (r p : ℝ) : ℝ :=
  (⨍ y in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
    |f y - ⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r, f x| ^ p) ^
      (1 / p)
def ParabolicBallCampanatoBoundOn (f : ParabolicPoint → ℝ) (U : Set ParabolicPoint)
    (R α K p : ℝ) : Prop :=
  ∀ z ∈ U, ∀ {r : ℝ}, 0 < r → r ≤ R →
    ParabolicBallLpOscillation f z r p ≤ K * r ^ α
def GlobalParabolicBallCampanatoBound (f : ParabolicPoint → ℝ) (α K p : ℝ) : Prop :=
  ∀ z : ParabolicPoint, ∀ {r : ℝ}, 0 < r →
    ParabolicBallLpOscillation f z r p ≤ K * r ^ α
def ParabolicBallLpDataOn (f : ParabolicPoint → ℝ) (U : Set ParabolicPoint)
    (R p : ℝ) : Prop :=
  ∀ z ∈ U, ∀ {r : ℝ}, 0 < r → r ≤ R →
    IntegrableOn f (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume ∧
    IntegrableOn (fun q => |f q - ⨍ x in
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r, f x| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume
def ParabolicBallMeanSeq (f : ParabolicPoint → ℝ) (R : ℝ) (z : ParabolicPoint)
    (n : ℕ) : ℝ :=
  ⨍ y in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (R / (2 : ℝ) ^ n), f y
def parabolicBallRepresentative (f : ParabolicPoint → ℝ) (R : ℝ) (z : ParabolicPoint) : ℝ :=
  limUnder atTop (ParabolicBallMeanSeq f R z)
private lemma ball_dyadic_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < R / (2 : ℝ) ^ n := by positivity
private lemma ball_dyadic_antitone {R : ℝ} (hR : 0 < R) {m n : ℕ} (hmn : m ≤ n) :
    R / (2 : ℝ) ^ n ≤ R / (2 : ℝ) ^ m := by
  exact div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ (by norm_num) hmn)
private lemma ball_dyadic_le {R : ℝ} (hR : 0 < R) (n : ℕ) : R / (2 : ℝ) ^ n ≤ R := by
  simpa using ball_dyadic_antitone hR (Nat.zero_le n)
private lemma ball_dyadic_rpow {R : ℝ} (hR : 0 ≤ R) (α : ℝ) : ∀ n : ℕ,
      (R / (2 : ℝ) ^ n) ^ α = R ^ α * ((2 : ℝ) ^ (-α)) ^ n
  | 0 => by simp
  | n + 1 => by
      have hsplit :
          R / (2 : ℝ) ^ (n + 1) = (R / (2 : ℝ) ^ n) / 2 := by
        rw [pow_succ]
        ring
      have hrn : 0 ≤ R / (2 : ℝ) ^ n := div_nonneg hR (by positivity)
      rw [hsplit, Real.div_rpow hrn (by norm_num), ball_dyadic_rpow hR α n,
        pow_succ, Real.rpow_neg (by norm_num)]
      field_simp
private lemma closedBall_pos {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) : 0 < volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) := by
  exact (volume_parabolicBall_pos hr).trans_le (measure_mono Metric.ball_subset_closedBall)
private lemma closedBall_top {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) : volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) < ∞ := by
  exact (measure_mono (Metric.closedBall_subset_ball (x := z) (ε₁ := r) (ε₂ := 2 * r) (by linarith only [hr]))).trans_lt (volume_parabolicBall_lt_top (by positivity))
def vec3ClosedBall (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) ≤ r}
private lemma vec3ClosedBall_measurable (x : Vec3) (r : ℝ) :
    MeasurableSet (vec3ClosedBall x r) := by
  have hmeas : Measurable (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
    unfold vec3EuclideanNorm
    fun_prop
  exact hmeas measurableSet_Iic
private lemma volume_vec3ClosedBall (x : Vec3) (r : ℝ) :
    volume (vec3ClosedBall x r) = volume (vec3ClosedBall 0 r) := by
  have hpre : (fun y : Vec3 => x + y) ⁻¹' vec3ClosedBall x r =
      vec3ClosedBall 0 r := by
    ext y
    simp only [mem_preimage, vec3ClosedBall]
    change vec3EuclideanNorm ((x + y) - x) ≤ r ↔
      vec3EuclideanNorm (y - 0) ≤ r
    have hdiff : (x + y) - x = y := by abel
    simp only [sub_zero, hdiff]
  have h := (measurePreserving_add_left (volume : Measure Vec3) x).measure_preimage
    (vec3ClosedBall_measurable x r).nullMeasurableSet
  rw [hpre] at h
  exact h.symm
def campanatoHolderVec3ScaleLinear (a : ℝ) : Vec3 →ₗ[ℝ] Vec3 :=
  a • LinearMap.id
private lemma vec3ScaleLinear_apply (a : ℝ) (v : Vec3) :
    campanatoHolderVec3ScaleLinear a v = a • v := by
  rfl
private lemma vec3ScaleLinear_det (a : ℝ) :
    LinearMap.det (campanatoHolderVec3ScaleLinear a) = a ^ 3 := by
  simp [campanatoHolderVec3ScaleLinear, LinearMap.det_smul, LinearMap.det_id]
private lemma volume_vec3ClosedBall_scale {a r : ℝ} (ha : 0 < a) :
    volume (vec3ClosedBall 0 (a * r)) =
      ENNReal.ofReal (a ^ 3) * volume (vec3ClosedBall 0 r) := by
  let f := campanatoHolderVec3ScaleLinear a⁻¹
  have hdet : LinearMap.det f ≠ 0 := by
    rw [show f = campanatoHolderVec3ScaleLinear a⁻¹ by rfl, vec3ScaleLinear_det]
    exact pow_ne_zero 3 (inv_ne_zero ha.ne')
  have hpre : (f : Vec3 → Vec3) ⁻¹' vec3ClosedBall 0 r =
      vec3ClosedBall 0 (a * r) := by
    ext y
    change vec3EuclideanNorm (f y - 0) ≤ r ↔
      vec3EuclideanNorm (y - 0) ≤ a * r
    rw [sub_zero, sub_zero, vec3ScaleLinear_apply, vec3EuclideanNorm_smul,
      abs_of_pos (inv_pos.mpr ha)]
    constructor
    · intro h
      have h' := mul_le_mul_of_nonneg_left h (le_of_lt ha)
      simpa [ha.ne'] using h'
    · intro h
      have h' := mul_le_mul_of_nonneg_left h (inv_pos.mpr ha).le
      simpa [ha.ne'] using h'
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := f) hdet
  have hmeasure := congrArg (fun μ : Measure Vec3 => μ (vec3ClosedBall 0 r)) hmap
  rw [Measure.map_apply (f.continuous_of_finiteDimensional.measurable)
    (vec3ClosedBall_measurable 0 r), hpre, Measure.smul_apply] at hmeasure
  rw [vec3ScaleLinear_det] at hmeasure
  have ha3 : 0 < a ^ 3 := pow_pos ha 3
  simpa [f, abs_of_pos (inv_pos.mpr ha), abs_of_pos ha, inv_pow, ha.ne',
    ENNReal.ofReal_inv_of_pos ha3, ENNReal.ofReal_pow ha.le] using hmeasure
private lemma parabolicMetricClosedBall_eq_product {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) :
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r =
      vec3ClosedBall z.1 r ×ˢ Icc (z.2 - r ^ 2) (z.2 + r ^ 2) := by
  ext p
  rcases z with ⟨x, t⟩
  rcases p with ⟨y, s⟩
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      (y, s) ((x, t) : ParabolicPoint) ≤ r ↔ _
  have hdist : @dist ParabolicPoint
      (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      (y, s) ((x, t) : ParabolicPoint) = parabolicDist (y, s) (x, t) := by
    exact dist_eq_parabolicDist (y, s) (x, t)
  rw [hdist]
  change max (vec3EuclideanNorm (y - x)) (Real.sqrt |s - t|) ≤ r ↔
    vec3EuclideanNorm (y - x) ≤ r ∧
      (t - r ^ 2 ≤ s ∧ s ≤ t + r ^ 2)
  rw [max_le_iff]
  constructor
  · rintro ⟨hspace, htime⟩
    have habs : |s - t| ≤ r ^ 2 := (Real.sqrt_le_iff.mp htime).2
    refine ⟨hspace, ?_, ?_⟩
    · linarith only [abs_le.mp habs |>.1]
    · linarith only [abs_le.mp habs |>.2]
  · rintro ⟨hspace, hlo, hupp⟩
    refine ⟨hspace, ?_⟩
    apply Real.sqrt_le_iff.mpr
    refine ⟨hr.le, ?_⟩
    exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hupp, sq_pos_of_pos hr]
      ⟩
private lemma volume_parabolicMetricClosedBall {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) :
    volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) =
      volume (vec3ClosedBall z.1 r) * ENNReal.ofReal (2 * r ^ 2) := by
  rw [parabolicMetricClosedBall_eq_product hr]
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      (vec3ClosedBall z.1 r ×ˢ Icc (z.2 - r ^ 2) (z.2 + r ^ 2)) = _
  rw [Measure.prod_prod, Real.volume_Icc]
  congr 2
  ring
private lemma volume_parabolicMetricClosedBall_radius_scale
    {z : ParabolicPoint} {r a : ℝ} (ha : 0 < a) (hr : 0 < r) :
    volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (a * r)) =
      ENNReal.ofReal (a ^ 5) *
        volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) := by
  rw [volume_parabolicMetricClosedBall (mul_pos ha hr),
    volume_parabolicMetricClosedBall hr]
  simp only [volume_vec3ClosedBall]
  rw [volume_vec3ClosedBall_scale ha]
  rw [show 2 * (a * r) ^ 2 = a ^ 2 * (2 * r ^ 2) by ring,
    ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ 2)]
  calc
    (ENNReal.ofReal (a ^ 3) * volume (vec3ClosedBall 0 r)) *
          (ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (2 * r ^ 2)) =
        (ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (a ^ 2)) *
          (volume (vec3ClosedBall 0 r) * ENNReal.ofReal (2 * r ^ 2) : ℝ≥0∞) := by
            ring
    _ = ENNReal.ofReal (a ^ 5) *
          (volume (vec3ClosedBall 0 r) * ENNReal.ofReal (2 * r ^ 2)) := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ 3)]
            congr 2
            ring
private lemma volume_parabolicMetricClosedBall_center
    {z w : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) =
      volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace w r) := by
  rw [volume_parabolicMetricClosedBall hr, volume_parabolicMetricClosedBall hr]
  simp only [volume_vec3ClosedBall]
private lemma closedBall_volume_ratio_two {z w : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r))).toReal /
        (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace w r)).toReal =
      (2 : ℝ) ^ 5 := by
  have hcenter := volume_parabolicMetricClosedBall_center (z := z) (w := w)
    (r := 2 * r) (mul_pos (by norm_num) hr)
  have hscale := volume_parabolicMetricClosedBall_radius_scale (z := w) (a := 2)
    (r := r) (by norm_num) hr
  calc
    (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r))).toReal /
          (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace w r)).toReal =
        (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace w (2 * r))).toReal /
          (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace w r)).toReal := by
            rw [hcenter]
    _ = (ENNReal.ofReal (2 ^ 5) *
          volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace w r)).toReal /
          (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace w r)).toReal := by
            rw [hscale]
    _ = (2 : ℝ) ^ 5 := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 ^ 5)]
      have hne : (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace w r)).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt (closedBall_pos (z := w) hr),
          ne_of_lt (closedBall_top (z := w) hr)⟩
      field_simp [hne]
private lemma closedBall_volume_ratio_le_two
    {z : ParabolicPoint} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hsr : s ≤ 2 * r) :
    (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z s)).toReal /
        (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)).toReal ≤
      (2 : ℝ) ^ 5 := by
  let a : ℝ := s / r
  have ha : 0 < a := div_pos hs hr
  have ha2 : a ≤ 2 := by
    dsimp [a]
    exact (div_le_iff₀ hr).2 hsr
  have har : a * r = s := by
    dsimp [a]
    field_simp
  have hscale := volume_parabolicMetricClosedBall_radius_scale (z := z) ha hr
  calc
    (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z s)).toReal /
          (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)).toReal =
        (ENNReal.ofReal (a ^ 5) *
          volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)).toReal /
          (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)).toReal := by
            rw [← har, hscale, ENNReal.toReal_mul,
              ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ a ^ 5)]
    _ = a ^ 5 := by
      have hne : (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt (closedBall_pos (z := z) hr),
          ne_of_lt (closedBall_top (z := z) hr)⟩
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ a ^ 5)]
      field_simp [hne]
    _ ≤ (2 : ℝ) ^ 5 := by gcongr
theorem parabolicBall_volume_ratio_two {z w : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r))).toReal /
        (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace w r)).toReal =
      (2 : ℝ) ^ 5 :=
  closedBall_volume_ratio_two hr
theorem parabolicBall_volume_ratio_le_two
    {z : ParabolicPoint} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hsr : s ≤ 2 * r) :
    (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z s)).toReal /
        (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)).toReal ≤
      (2 : ℝ) ^ 5 :=
  closedBall_volume_ratio_le_two hr hs hsr
theorem parabolicBall_closedBall_pos {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    0 < volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :=
  closedBall_pos hr
theorem parabolicBall_closedBall_top {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) < ∞ :=
  closedBall_top hr
theorem parabolicBall_dyadic_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < R / (2 : ℝ) ^ n :=
  ball_dyadic_pos hR n
theorem parabolicBall_dyadic_le {R : ℝ} (hR : 0 < R) (n : ℕ) :
    R / (2 : ℝ) ^ n ≤ R :=
  ball_dyadic_le hR n
theorem parabolicBall_dyadic_rpow {R : ℝ} (hR : 0 ≤ R) (α : ℝ) (n : ℕ) :
    (R / (2 : ℝ) ^ n) ^ α = R ^ α * ((2 : ℝ) ^ (-α)) ^ n :=
  ball_dyadic_rpow hR α n
private theorem average_sub_const_le_rpow_outer
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {A B : Set α} {c p D : ℝ} (hBA : B ⊆ A)
    (hApos : 0 < μ A) (hAtop : μ A < ∞)
    (hBpos : 0 < μ B) (hBtop : μ B < ∞)
    (hfA : IntegrableOn f A μ)
    (hfpA : IntegrableOn (fun x => |f x - c| ^ p) A μ)
    (hp : 1 ≤ p) (hD : (μ A).toReal / (μ B).toReal ≤ D) :
    |(⨍ x in B, f x ∂μ) - c| ≤
      D ^ (1 / p) * (⨍ x in A, |f x - c| ^ p ∂μ) ^ (1 / p) := by
  have hfB : IntegrableOn f B μ := hfA.mono_set hBA
  have hconstA : IntegrableOn (fun _ : α => c) A μ := integrableOn_const hAtop.ne
  have hconstB : IntegrableOn (fun _ : α => c) B μ := integrableOn_const hBtop.ne
  have hdiff :
      (⨍ x in B, (f - fun _ : α => c) x ∂μ) =
        (⨍ x in B, f x ∂μ) - c := by
    rw [MeasureTheory.setAverage_sub hfB hconstB,
      MeasureTheory.setAverage_const hBpos.ne' hBtop.ne]
  have hpowB : IntegrableOn (fun x => |f x - c| ^ p) B μ := hfpA.mono_set hBA
  have hfirst :
      |(⨍ x in B, f x ∂μ) - c| ≤
        (⨍ x in B, |f x - c| ^ p ∂μ) ^ (1 / p) := by
    rw [← hdiff]
    simpa only [Real.norm_eq_abs, Pi.sub_apply, one_div, one_mul] using
      (Integration.setAverage_abs_le_rpow_mean hp hBpos hBtop
        (hfB.sub hconstB) hpowB)
  have houter := average_abs_le_outer_average_abs hBA hApos hAtop hBpos hBtop
    hfpA
  have houter' :
      (⨍ x in B, |f x - c| ^ p ∂μ) ≤
        (μ A).toReal / (μ B).toReal *
          (⨍ x in A, |f x - c| ^ p ∂μ) := by
    simpa only [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using houter
  have hroot : 0 ≤ (1 / p : ℝ) := by positivity
  have hnonnegB : 0 ≤ ⨍ x in B, |f x - c| ^ p ∂μ :=
    Integration.setAverage_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (abs_nonneg _) _)
  have hnonnegA : 0 ≤ ⨍ x in A, |f x - c| ^ p ∂μ :=
    Integration.setAverage_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (abs_nonneg _) _)
  have hD0 : 0 ≤ D := by
    exact le_trans (div_nonneg (ENNReal.toReal_nonneg) (by positivity)) hD
  have hroot' := Real.rpow_le_rpow hnonnegB houter' hroot
  calc
    _ ≤ (⨍ x in B, |f x - c| ^ p ∂μ) ^ (1 / p) := hfirst
    _ ≤ ((μ A).toReal / (μ B).toReal *
        (⨍ x in A, |f x - c| ^ p ∂μ)) ^ (1 / p) := hroot'
    _ ≤ (D * (⨍ x in A, |f x - c| ^ p ∂μ)) ^ (1 / p) := by
      gcongr
    _ = D ^ (1 / p) * (⨍ x in A, |f x - c| ^ p ∂μ) ^ (1 / p) := by
      rw [Real.mul_rpow hD0 hnonnegA]
theorem abs_setAverage_sub_setAverage_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {A B : Set α} {p D : ℝ} (hBA : B ⊆ A)
    (hApos : 0 < μ A) (hAtop : μ A < ∞)
    (hBpos : 0 < μ B) (hBtop : μ B < ∞)
    (hfA : IntegrableOn f A μ)
    (hfpA : IntegrableOn
      (fun x => |f x - ⨍ y in A, f y ∂μ| ^ p) A μ)
    (hp : 1 ≤ p) (hD : (μ A).toReal / (μ B).toReal ≤ D) :
    |(⨍ x in B, f x ∂μ) - ⨍ x in A, f x ∂μ| ≤
      D ^ (1 / p) *
        (⨍ x in A, |f x - ⨍ y in A, f y ∂μ| ^ p ∂μ) ^ (1 / p) := by
  simpa only using
    (average_sub_const_le_rpow_outer hBA hApos hAtop hBpos hBtop hfA hfpA hp hD)
theorem abs_parabolicBallMean_sub_le_of_subset
    {f : ParabolicPoint → ℝ} {z z' : ParabolicPoint} {r p : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p)
    (hsubset : @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z' r ⊆
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r))
    (hf : IntegrableOn f
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r)) volume)
    (hfp : IntegrableOn
      (fun q => |f q - ⨍ x in
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r), f x| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r)) volume) :
    |(⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z' r, f x) -
        ⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r), f x| ≤
    (2 : ℝ) ^ (5 / p) *
        (⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r),
          |f x - ⨍ y in
            @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r), f y| ^ p) ^
          (1 / p) := by
  have hratio := closedBall_volume_ratio_two (z := z) (w := z') hr
  have hbase := abs_setAverage_sub_setAverage_le hsubset
      (closedBall_pos (z := z) (mul_pos (by norm_num) hr))
      (closedBall_top (z := z) (mul_pos (by norm_num) hr))
      (closedBall_pos (z := z') hr) (closedBall_top (z := z') hr)
      hf hfp hp (le_of_eq hratio)
  have hpow : ((2 : ℝ) ^ 5) ^ p⁻¹ = (2 : ℝ) ^ (5 / p) := by
    rw [show (2 : ℝ) ^ 5 = (2 : ℝ) ^ (5 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
  simpa only [one_mul, one_div, hpow] using hbase
theorem abs_parabolicBallMeanSeq_succ_le
    {f : ParabolicPoint → ℝ} {U : Set ParabolicPoint}
    {R α K p D : ℝ} {z : ParabolicPoint}
    (hR : 0 < R) (hp : 1 ≤ p) (hD : 0 ≤ D)
    (hcamp : ParabolicBallCampanatoBoundOn f U R α K p)
    (hz : z ∈ U) (n : ℕ)
    (hratio :
      (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
        (R / (2 : ℝ) ^ n))).toReal /
          (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
            (R / (2 : ℝ) ^ (n + 1)))).toReal ≤ D)
    (hf : IntegrableOn f
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
        (R / (2 : ℝ) ^ n)) volume)
    (hfp : IntegrableOn
      (fun q => |f q - ⨍ x in
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
          (R / (2 : ℝ) ^ n), f x| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
        (R / (2 : ℝ) ^ n)) volume) :
    |ParabolicBallMeanSeq f R z n - ParabolicBallMeanSeq f R z (n + 1)| ≤
      D ^ (1 / p) * (K * (R / (2 : ℝ) ^ n) ^ α) := by
  have hrn : 0 < R / (2 : ℝ) ^ n := ball_dyadic_pos hR n
  have hrn1 : 0 < R / (2 : ℝ) ^ (n + 1) := ball_dyadic_pos hR (n + 1)
  have hscale : R / (2 : ℝ) ^ (n + 1) ≤ R / (2 : ℝ) ^ n :=
    ball_dyadic_antitone hR (Nat.le_succ n)
  have hsub :
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
        (R / (2 : ℝ) ^ (n + 1)) ⊆
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
        (R / (2 : ℝ) ^ n) := Metric.closedBall_subset_closedBall hscale
  have hcomp := average_sub_const_le_rpow_outer hsub
    (closedBall_pos hrn) (closedBall_top hrn)
    (closedBall_pos hrn1) (closedBall_top hrn1) hf hfp hp hratio
  have hcamp' := hcamp z hz hrn (ball_dyadic_le hR n)
  have hrootnonneg : 0 ≤ D ^ (1 / p : ℝ) := Real.rpow_nonneg hD _
  change |(⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
      (R / (2 : ℝ) ^ n), f x) -
    (⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
      (R / (2 : ℝ) ^ (n + 1)), f x)| ≤ _
  calc
    _ ≤ D ^ (1 / p) *
        (⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
          (R / (2 : ℝ) ^ n),
          |f x - ⨍ y in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
            (R / (2 : ℝ) ^ n), f y| ^ p) ^ (1 / p) := by
      rw [abs_sub_comm]
      exact hcomp
    _ ≤ D ^ (1 / p) * (K * (R / (2 : ℝ) ^ n) ^ α) :=
      mul_le_mul_of_nonneg_left hcamp' hrootnonneg
theorem abs_parabolicBallRepresentative_sub_meanSeq_le
    {f : ParabolicPoint → ℝ} {R α C : ℝ} {z : ParabolicPoint}
    (hα : 0 < α) (hstep : ∀ n : ℕ,
      dist (ParabolicBallMeanSeq f R z n)
          (ParabolicBallMeanSeq f R z (n + 1)) ≤
        C * ((2 : ℝ) ^ (-α)) ^ n) (n : ℕ) :
    |parabolicBallRepresentative f R z - ParabolicBallMeanSeq f R z n| ≤
      parabolicCampanatoTailConstant α * C * ((2 : ℝ) ^ (-α)) ^ n := by
  have hq : (2 : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hα])
  have htendsto : Tendsto (ParabolicBallMeanSeq f R z) atTop
      (𝓝 (parabolicBallRepresentative f R z)) :=
    (cauchySeq_of_le_geometric ((2 : ℝ) ^ (-α)) C hq hstep).tendsto_limUnder
  have hbase := dist_le_of_le_geometric_of_tendsto
    ((2 : ℝ) ^ (-α)) C hq hstep
    htendsto n
  rw [Real.dist_eq, abs_sub_comm] at hbase
  refine hbase.trans_eq ?_
  unfold parabolicCampanatoTailConstant
  field_simp
def GlobalParabolicBallLpData
    (f : ParabolicPoint → ℝ) (p : ℝ) : Prop :=
  ∀ z : ParabolicPoint, ∀ {r : ℝ}, 0 < r →
    IntegrableOn f
        (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume ∧
    IntegrableOn
      (fun q => |f q - ⨍ x in
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r, f x| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume
def parabolicCampanatoHolderConstant (α p : ℝ) : ℝ :=
  (2 * parabolicCampanatoTailConstant α + 1) *
    (2 : ℝ) ^ (5 / p) * (8 : ℝ) ^ α
private lemma parabolicBallMeanSeq_step_of_campanato
    {f : ParabolicPoint → ℝ} {U : Set ParabolicPoint}
    {R α K p : ℝ} {z : ParabolicPoint}
    (hR : 0 < R) (hp : 1 ≤ p)
    (hcamp : ParabolicBallCampanatoBoundOn f U R α K p)
    (hz : z ∈ U) (hdata : ParabolicBallLpDataOn f U R p) :
    ∀ n : ℕ,
      dist (ParabolicBallMeanSeq f R z n)
          (ParabolicBallMeanSeq f R z (n + 1)) ≤
        ((2 : ℝ) ^ (5 / p) * (K * R ^ α)) *
          ((2 : ℝ) ^ (-α)) ^ n := by
  intro n
  have hrn : 0 < R / (2 : ℝ) ^ n := ball_dyadic_pos hR n
  have hrn1 : 0 < R / (2 : ℝ) ^ (n + 1) := ball_dyadic_pos hR (n + 1)
  have hratio :
      (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
        (R / (2 : ℝ) ^ n))).toReal /
          (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
            (R / (2 : ℝ) ^ (n + 1)))).toReal ≤ (2 : ℝ) ^ 5 := by
    have heq : 2 * (R / (2 : ℝ) ^ (n + 1)) = R / (2 : ℝ) ^ n := by
      rw [pow_succ]
      ring
    rw [← heq]
    exact le_of_eq (closedBall_volume_ratio_two (z := z) (w := z) hrn1)
  have hdata' := hdata z hz hrn (ball_dyadic_le hR n)
  have h := abs_parabolicBallMeanSeq_succ_le hR hp (by positivity)
    hcamp hz n hratio hdata'.1 hdata'.2
  rw [Real.dist_eq]
  calc
    _ ≤ (2 : ℝ) ^ (5 / p) * (K * (R / (2 : ℝ) ^ n) ^ α) := by
      have hpow : ((2 : ℝ) ^ 5) ^ p⁻¹ = (2 : ℝ) ^ (5 / p) := by
        rw [show (2 : ℝ) ^ 5 = (2 : ℝ) ^ (5 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
      simpa only [one_mul, one_div, hpow] using h
    _ = ((2 : ℝ) ^ (5 / p) * (K * R ^ α)) *
          ((2 : ℝ) ^ (-α)) ^ n := by
      rw [ball_dyadic_rpow hR.le α n]
      ring
theorem parabolicBallRepresentative_holder_at_scale
    {f : ParabolicPoint → ℝ} {U : Set ParabolicPoint}
    {R α K p : ℝ} (hα : 0 < α) (hR : 0 < R) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hcamp : ParabolicBallCampanatoBoundOn f U R α K p)
    (hdata : ParabolicBallLpDataOn f U R p) :
    ∀ z ∈ U, ∀ z' ∈ U, dist z z' < R / 4 →
      |parabolicBallRepresentative f R z - parabolicBallRepresentative f R z'| ≤
        parabolicCampanatoHolderConstant α p * K * parabolicDist z z' ^ α := by
  have hstep : ∀ z ∈ U, ∀ n : ℕ,
      dist (ParabolicBallMeanSeq f R z n)
          (ParabolicBallMeanSeq f R z (n + 1)) ≤
        ((2 : ℝ) ^ (5 / p) * (K * R ^ α)) *
          ((2 : ℝ) ^ (-α)) ^ n := by
    intro z hz n
    exact parabolicBallMeanSeq_step_of_campanato hR hp hcamp hz hdata n
  have htail : ∀ z ∈ U, ∀ n : ℕ,
      |parabolicBallRepresentative f R z - ParabolicBallMeanSeq f R z n| ≤
        parabolicCampanatoTailConstant α *
          ((2 : ℝ) ^ (5 / p) * (K * R ^ α)) *
            ((2 : ℝ) ^ (-α)) ^ n := by
    intro z hz n
    exact abs_parabolicBallRepresentative_sub_meanSeq_le hα (hstep z hz) n
  intro z hz z' hz' hdist
  by_cases hzz' : z = z'
  · subst z'
    simp [parabolicDist, vec3EuclideanNorm_zero, hα.ne']
  ·
    let ρ : ℝ := dist z z'
    have hρpos : 0 < ρ := dist_pos.mpr hzz'
    have hρsmall : ρ < R / 4 := hdist
    have hqone : 1 < R / (2 * ρ) := by
      apply (lt_div_iff₀ (mul_pos (by norm_num) hρpos)).2
      have hRrho : 4 * ρ < R := by
        calc
          4 * ρ < 4 * (R / 4) := mul_lt_mul_of_pos_left hρsmall (by norm_num)
          _ = R := by ring
      linarith only [hRrho, hρpos]
    have hqtwo : 2 < R / (2 * ρ) := by
      apply (lt_div_iff₀ (mul_pos (by norm_num) hρpos)).2
      have hRrho : 4 * ρ < R := by linarith only [hρsmall]
      convert hRrho using 1
      ring
    have hex : ∃ n : ℕ, R / (2 * ρ) ≤ (2 : ℝ) ^ (n + 1) := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / (2 * ρ)) one_lt_two
      exact ⟨n, le_trans (le_of_lt hn) (by
        rw [pow_succ]
        have hpw : 0 ≤ (2 : ℝ) ^ n := by positivity
        nlinarith only [hpw])⟩
    let j : ℕ := Nat.find hex
    have hjhi : R / (2 * ρ) ≤ (2 : ℝ) ^ (j + 1) := Nat.find_spec hex
    have hjlo : (2 : ℝ) ^ j < R / (2 * ρ) := by
      have hjne : j ≠ 0 := by
        intro hj0
        have := hjhi
        simp [hj0] at this
        linarith only [hqtwo, this]
      cases hj : j with
      | zero => contradiction
      | succ k =>
        have hnot : ¬ R / (2 * ρ) ≤ (2 : ℝ) ^ (k + 1) := by
          intro h
          have hmin := Nat.find_min' hex h
          have hmin' : j ≤ k := by simpa [j] using hmin
          exact (Nat.not_succ_le_self k) (by omega)
        simpa [hj] using (lt_of_not_ge hnot)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, j = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by
        intro hj0
        have := hjhi
        simp [hj0] at this
        linarith only [hqtwo, this])
    have hjlo' : (2 : ℝ) ^ (k + 1) < R / (2 * ρ) := by simpa [hk] using hjlo
    have hjhi' : R / (2 * ρ) ≤ (2 : ℝ) ^ (k + 2) := by
      simpa [hk, pow_succ, Nat.add_assoc] using hjhi
    let r : ℝ := R / (2 : ℝ) ^ (k + 1)
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hρle : ρ ≤ r := by
      have hsmall : 2 * ρ < r := by
        dsimp [r]
        apply (lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (k + 1))).2
        have := (lt_div_iff₀ (mul_pos (by norm_num) hρpos)).mp hjlo'
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      have hrho_lt : ρ < 2 * ρ := by linarith only [hρpos]
      exact (hrho_lt.trans hsmall).le
    have hsubset :
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z' r ⊆
          @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r) := by
      intro w hw
      rw [Metric.mem_closedBall] at hw ⊢
      calc
        dist w z ≤ dist w z' + dist z' z := dist_triangle w z' z
        _ ≤ r + r := by
          have hdist' : dist z' z = ρ := by simp [ρ, dist_comm]
          rw [hdist']
          exact add_le_add hw hρle
        _ = 2 * r := by ring
    have heq : 2 * r = R / (2 : ℝ) ^ k := by
      dsimp [r]
      rw [pow_succ]
      ring
    have houter : 2 * r ≤ R := by
      rw [heq]
      exact ball_dyadic_le hR k
    have hdata_outer := hdata z hz (mul_pos (by norm_num) hr) houter
    have hcamp_outer := hcamp z hz (mul_pos (by norm_num) hr) houter
    have hcomp := abs_parabolicBallMean_sub_le_of_subset hr hp hsubset
      hdata_outer.1 hdata_outer.2
    have hcomp' :
        |ParabolicBallMeanSeq f R z' (k + 1) -
            ParabolicBallMeanSeq f R z k| ≤
          (2 : ℝ) ^ (5 / p) * (K * (2 * r) ^ α) := by
      calc
        _ ≤ (2 : ℝ) ^ (5 / p) *
            (⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r),
              |f x - ⨍ y in
                @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r), f y| ^ p) ^
              (1 / p) := by simpa [ParabolicBallMeanSeq, heq, one_div] using hcomp
        _ ≤ (2 : ℝ) ^ (5 / p) * (K * (2 * r) ^ α) := by
          exact mul_le_mul_of_nonneg_left hcamp_outer (by positivity)
    have htail_z := htail z hz k
    have htail_z' := htail z' hz' (k + 1)
    have htail_z'' :
        |parabolicBallRepresentative f R z - ParabolicBallMeanSeq f R z k| ≤
          parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
            (K * (R / (2 : ℝ) ^ k) ^ α) := by
      calc
        _ ≤ parabolicCampanatoTailConstant α *
            ((2 : ℝ) ^ (5 / p) * (K * R ^ α)) *
              ((2 : ℝ) ^ (-α)) ^ k := htail_z
        _ = _ := by rw [ball_dyadic_rpow hR.le α k]; ring
    have htail_z''' :
        |parabolicBallRepresentative f R z' - ParabolicBallMeanSeq f R z' (k + 1)| ≤
          parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
            (K * r ^ α) := by
      calc
        _ ≤ parabolicCampanatoTailConstant α *
            ((2 : ℝ) ^ (5 / p) * (K * R ^ α)) *
              ((2 : ℝ) ^ (-α)) ^ (k + 1) := htail_z'
        _ = _ := by rw [ball_dyadic_rpow hR.le α (k + 1)]; ring
    have hinnerρ : r ≤ 4 * ρ := by
      dsimp [r]
      apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (k + 1))).2
      have h := (div_le_iff₀ (mul_pos (by norm_num) hρpos)).mp hjhi'
      convert h using 1
      all_goals rw [pow_succ]
      all_goals ring
    have houterρ : 2 * r ≤ 8 * ρ := by linarith only [hinnerρ]
    have hpow_outer : (2 * r) ^ α ≤ (8 * ρ) ^ α := by
      exact Real.rpow_le_rpow (by positivity) houterρ (le_of_lt hα)
    have hpow_inner : r ^ α ≤ (8 * ρ) ^ α := by
      exact Real.rpow_le_rpow (by positivity)
        (hinnerρ.trans (by linarith only [hρpos])) (le_of_lt hα)
    have hT : 0 ≤ parabolicCampanatoTailConstant α := by
      unfold parabolicCampanatoTailConstant
      exact one_div_nonneg.mpr (sub_nonneg.mpr
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hα])).le)
    have hD : 0 ≤ (2 : ℝ) ^ (5 / p) := Real.rpow_nonneg (by norm_num) _
    have htail_z_le :
        |parabolicBallRepresentative f R z - ParabolicBallMeanSeq f R z k| ≤
            parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
            (K * (8 * ρ) ^ α) := by
      have htail_z4 := htail_z''
      rw [← heq] at htail_z4
      exact htail_z4.trans (by gcongr)
    have htail_z'_le :
        |parabolicBallRepresentative f R z' - ParabolicBallMeanSeq f R z' (k + 1)| ≤
          parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
            (K * (8 * ρ) ^ α) := by
      exact htail_z'''.trans (by gcongr)
    have hcomp_le :
        |ParabolicBallMeanSeq f R z' (k + 1) -
            ParabolicBallMeanSeq f R z k| ≤
          (2 : ℝ) ^ (5 / p) * (K * (8 * ρ) ^ α) := by
      exact hcomp'.trans (by gcongr)
    have hcomp_le' :
        |ParabolicBallMeanSeq f R z k -
            ParabolicBallMeanSeq f R z' (k + 1)| ≤
          (2 : ℝ) ^ (5 / p) * (K * (8 * ρ) ^ α) := by
      simpa only [abs_sub_comm] using hcomp_le
    have htail_z'_le' :
        |ParabolicBallMeanSeq f R z' (k + 1) -
            parabolicBallRepresentative f R z'| ≤
          parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
            (K * (8 * ρ) ^ α) := by
      simpa only [abs_sub_comm] using htail_z'_le
    have hsum :
        |parabolicBallRepresentative f R z - parabolicBallRepresentative f R z'| ≤
          (2 * parabolicCampanatoTailConstant α + 1) *
            (2 : ℝ) ^ (5 / p) * (K * (8 * ρ) ^ α) := by
      calc
        _ ≤ |parabolicBallRepresentative f R z - ParabolicBallMeanSeq f R z k| +
            |ParabolicBallMeanSeq f R z k -
              parabolicBallRepresentative f R z'| :=
          abs_sub_le _ _ _
        _ ≤ |parabolicBallRepresentative f R z - ParabolicBallMeanSeq f R z k| +
            (|ParabolicBallMeanSeq f R z k - ParabolicBallMeanSeq f R z' (k + 1)| +
              |ParabolicBallMeanSeq f R z' (k + 1) -
                parabolicBallRepresentative f R z'|) := by
          have hmid := abs_sub_le
            (ParabolicBallMeanSeq f R z k)
            (ParabolicBallMeanSeq f R z' (k + 1))
            (parabolicBallRepresentative f R z')
          exact add_le_add_right hmid _
        _ = |parabolicBallRepresentative f R z - ParabolicBallMeanSeq f R z k| +
            |ParabolicBallMeanSeq f R z k - ParabolicBallMeanSeq f R z' (k + 1)| +
            |ParabolicBallMeanSeq f R z' (k + 1) -
              parabolicBallRepresentative f R z'| := by ring
        _ ≤ (2 * parabolicCampanatoTailConstant α + 1) *
            (2 : ℝ) ^ (5 / p) * (K * (8 * ρ) ^ α) := by
          calc
            _ ≤ parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
                (K * (8 * ρ) ^ α) +
                ((2 : ℝ) ^ (5 / p) * (K * (8 * ρ) ^ α)) +
                parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
                  (K * (8 * ρ) ^ α) :=
              add_le_add (add_le_add htail_z_le hcomp_le') htail_z'_le'
            _ = _ := by ring_nf
    rw [show (8 * ρ) ^ α = (8 : ℝ) ^ α * ρ ^ α by
      rw [Real.mul_rpow (by positivity) hρpos.le]] at hsum
    simpa [parabolicCampanatoHolderConstant, ρ, mul_assoc, mul_left_comm, mul_comm,
      dist_eq_parabolicDist] using hsum
theorem ae_tendsto_parabolicBallMeanSeq
    {f : ParabolicPoint → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      Tendsto (ParabolicBallMeanSeq f R z) atTop (𝓝 (f z)) := by
  have hδ : Tendsto (fun n : ℕ => R / (2 : ℝ) ^ n) atTop (𝓝[>] 0) := by
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · convert h0.const_mul R using 1 <;> simp [div_eq_mul_inv]
    · filter_upwards [] with n
      exact ball_dyadic_pos hR n
  have hnorm := IsUnifLocDoublingMeasure.ae_tendsto_average
    (volume : Measure ParabolicPoint) hf 1
  filter_upwards [hnorm] with z hz
  have hz' := hz (w := fun _ : ℕ => z)
    (δ := fun n : ℕ => R / (2 : ℝ) ^ n) hδ ?_
  · change Tendsto (fun n : ℕ => ⨍ y in
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
          (R / (2 : ℝ) ^ n), f y) atTop (𝓝 (f z))
    exact hz'
  · filter_upwards [] with n
    rw [Metric.mem_closedBall]
    simpa only [dist_self, one_mul] using (ball_dyadic_pos hR n).le
theorem parabolicBallRepresentative_ae_eq
    {f : ParabolicPoint → ℝ} {R : ℝ}
    (hlim : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      Tendsto (ParabolicBallMeanSeq f R z) atTop (𝓝 (f z))) :
    parabolicBallRepresentative f R =ᵐ[volume] f := by
  filter_upwards [hlim] with z hz
  exact hz.limUnder_eq
theorem parabolicBallRepresentative_ae_eq_of_locallyIntegrable
    {f : ParabolicPoint → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : LocallyIntegrable f volume) :
    parabolicBallRepresentative f R =ᵐ[volume] f := by
  exact parabolicBallRepresentative_ae_eq (ae_tendsto_parabolicBallMeanSeq hR hf)
end CKN.Foundation.Parabolic
