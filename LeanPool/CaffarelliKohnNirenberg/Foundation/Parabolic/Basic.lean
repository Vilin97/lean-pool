/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Snowflaking

/-!
# Parabolic space-time geometry

The spatial geometry uses the Euclidean norm on `Fin 3 → ℝ`, defined from the
finite sum of squares.  This is deliberate: the ambient function space's
default norm can be the sup norm, whereas the cylinders here are Euclidean.
-/

public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric


noncomputable section

namespace CKN.Foundation.Parabolic

/-- Native three-dimensional coordinate vectors. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Three-dimensional coordinate vectors equipped with their Euclidean L² norm. -/
abbrev L2Vec3 := PiLp 2 (fun _ : Fin 3 => ℝ)

/-- Space-time points, given the parabolic metric below rather than the product metric. -/
@[expose]
def ParabolicPoint := Vec3 × ℝ

theorem half_pos : 0 < (1 / 2 : ℝ) := by norm_num

theorem half_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num

/-- Time equipped with the square-root snowflake metric. -/
abbrev SnowTime := Metric.Snowflaking ℝ (1 / 2 : ℝ) half_pos half_le_one

/-- Euclidean length of a native three-dimensional coordinate vector. -/
@[expose]
def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)

instance : MeasurableSpace ParabolicPoint := inferInstanceAs (MeasurableSpace (Vec3 × ℝ))

instance : MeasurableSpace SnowTime := borel SnowTime

instance : BorelSpace SnowTime := ⟨rfl⟩

/-- Measurable equivalence to Euclidean space times snowflaked time. -/
@[expose]
def parabolicMeasurableEquiv : ParabolicPoint ≃ᵐ L2Vec3 × SnowTime :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 Vec3) {
    toEquiv := Metric.Snowflaking.toSnowflaking
    measurable_toFun := Metric.Snowflaking.continuous_toSnowflaking.measurable
    measurable_invFun := Metric.Snowflaking.homeomorph.continuous.measurable }

/-- Coordinate map into the product carrying the parabolic metric. -/
@[expose]
def parabolicMap (p : ParabolicPoint) :
    L2Vec3 × SnowTime := parabolicMeasurableEquiv p

lemma parabolicMap_injective : Function.Injective parabolicMap := by
  intro p q h
  exact parabolicMeasurableEquiv.injective h

noncomputable instance parabolicMetricSpace : MetricSpace ParabolicPoint :=
  MetricSpace.induced parabolicMap parabolicMap_injective inferInstance

/-- Pseudometric presentation of the parabolic metric for explicit metric-space arguments. -/
abbrev parabolicPseudoMetricSpace : PseudoMetricSpace ParabolicPoint :=
  MetricSpace.toPseudoMetricSpace (self := parabolicMetricSpace)

instance : SecondCountableTopology ParabolicPoint :=
  Topology.IsInducing.secondCountableTopology (Topology.IsInducing.induced parabolicMap)

instance : BorelSpace ParabolicPoint :=
  MeasurableEmbedding.borelSpace parabolicMeasurableEquiv.measurableEmbedding
    (Topology.IsInducing.induced parabolicMap)

lemma vec3EuclideanNorm_eq_l2 (v : Vec3) :
    vec3EuclideanNorm v = ‖WithLp.toLp 2 v‖ := by
  rw [vec3EuclideanNorm, PiLp.norm_eq_of_L2]
  simp only [Real.norm_eq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [sq_abs]

lemma vec3EuclideanNorm_nonneg (v : Vec3) : 0 ≤ vec3EuclideanNorm v := by
  exact Real.sqrt_nonneg _

lemma vec3EuclideanNorm_zero : vec3EuclideanNorm (0 : Vec3) = 0 := by
  simp [vec3EuclideanNorm]

lemma vec3EuclideanNorm_smul (a : ℝ) (v : Vec3) :
    vec3EuclideanNorm (a • v) = |a| * vec3EuclideanNorm v := by
  rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
    ← vec3EuclideanNorm_eq_l2]

/-- Maximum of spatial Euclidean distance and square-root time separation. -/
@[expose]
def parabolicDist (p q : ParabolicPoint) : ℝ :=
  max (vec3EuclideanNorm (p.1 - q.1)) (Real.sqrt |p.2 - q.2|)

lemma dist_eq_parabolicDist (p q : ParabolicPoint) :
    dist p q = parabolicDist p q := by
  simp only [parabolicDist, vec3EuclideanNorm_eq_l2, Real.sqrt_eq_rpow]
  rfl

/-- Open Euclidean ball in native spatial coordinates. -/
@[expose]
def vec3Ball (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) < r}

/-- Backward parabolic cylinder with spatial radius `r` and time depth `r ^ 2`. -/
@[expose]
def parabolicCylinder (x : Vec3) (t r : ℝ) : Set ParabolicPoint :=
  vec3Ball x r ×ˢ Ioc (t - r ^ 2) t

@[simp] lemma mem_vec3Ball {x y : Vec3} {r : ℝ} :
    y ∈ vec3Ball x r ↔ vec3EuclideanNorm (y - x) < r := Iff.rfl

@[simp] lemma mem_parabolicCylinder {x y : Vec3} {t s r : ℝ} :
    (y, s) ∈ parabolicCylinder x t r ↔
      vec3EuclideanNorm (y - x) < r ∧ t - r ^ 2 < s ∧ s ≤ t := by
  rfl

lemma vec3Ball_mono {x : Vec3} {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    vec3Ball x r₁ ⊆ vec3Ball x r₂ := by
  intro y hy
  exact hy.trans_le hr

lemma parabolicCylinder_mono {x : Vec3} {t r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₁ ≤ r₂) :
    parabolicCylinder x t r₁ ⊆ parabolicCylinder x t r₂ := by
  intro p hp
  rcases hp with ⟨hp₁, hp₂, hp₃⟩
  refine ⟨vec3Ball_mono hr hp₁, ?_, hp₃⟩
  have hr₂ : 0 ≤ r₂ := hr₁.trans hr
  have hrsq : r₁ ^ 2 ≤ r₂ ^ 2 := (sq_le_sq₀ hr₁ hr₂).2 hr
  exact (sub_le_sub_left hrsq t).trans_lt hp₂

/-- Space-time translation by a spatial vector and time offset. -/
@[expose]
def parabolicTranslate (a : Vec3) (τ : ℝ) (p : ParabolicPoint) : ParabolicPoint :=
  (a + p.1, τ + p.2)

/-- Parabolic scaling, linear in space and quadratic in time. -/
@[expose]
def parabolicScale (a : ℝ) (p : ParabolicPoint) : ParabolicPoint :=
  (a • p.1, a ^ 2 * p.2)

lemma parabolicCylinder_translate (a x : Vec3) (τ t r : ℝ) :
    parabolicTranslate a τ '' parabolicCylinder x t r =
      parabolicCylinder (a + x) (τ + t) r := by
  ext p
  constructor
  · rintro ⟨⟨z, u⟩, hz, rfl⟩
    rcases hz with ⟨hz₁, hz₂, hz₃⟩
    change vec3EuclideanNorm ((a + z) - (a + x)) < r ∧
      τ + t - r ^ 2 < τ + u ∧ τ + u ≤ τ + t
    refine ⟨?_, ?_, ?_⟩
    · have hdiff : (a + z) - (a + x) = z - x := by abel
      rw [hdiff]
      exact hz₁
    · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz₂
    · simpa [add_assoc, add_left_comm, add_comm] using hz₃
  · intro hp
    rcases p with ⟨y, s⟩
    rcases hp with ⟨hp₁, hp₂, hp₃⟩
    refine ⟨(y - a, s - τ), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [vec3Ball, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp₁
      · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp₂
      · simpa [add_assoc, add_left_comm, add_comm] using hp₃
    · apply Prod.ext <;> simp [parabolicTranslate, sub_eq_add_neg]

lemma parabolicCylinder_scale {x : Vec3} {t r a : ℝ} (ha : 0 < a) :
    parabolicScale a '' parabolicCylinder x t r =
      parabolicCylinder (a • x) (a ^ 2 * t) (a * r) := by
  ext p
  rcases p with ⟨y, s⟩
  constructor
  · rintro ⟨⟨z, u⟩, hz, hzy⟩
    change (a • z, a ^ 2 * u) = (y, s) at hzy
    have hy : y = a • z := by
      exact (congrArg Prod.fst hzy).symm
    have hs : s = a ^ 2 * u := by
      exact (congrArg Prod.snd hzy).symm
    rw [hy, hs]
    rcases hz with ⟨hz₁, hz₂, hz₃⟩
    change vec3EuclideanNorm (a • z - a • x) < a * r ∧
      a ^ 2 * t - (a * r) ^ 2 < a ^ 2 * u ∧ a ^ 2 * u ≤ a ^ 2 * t
    refine ⟨?_, ?_, ?_⟩
    · rw [← smul_sub, vec3EuclideanNorm_smul, abs_of_pos ha]
      exact mul_lt_mul_of_pos_left hz₁ ha
    · have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
      have h := mul_lt_mul_of_pos_left hz₂ ha2
      calc
        a ^ 2 * t - (a * r) ^ 2 = a ^ 2 * (t - r ^ 2) := by ring
        _ < a ^ 2 * u := h
    · exact mul_le_mul_of_nonneg_left hz₃ (le_of_lt (sq_pos_of_pos ha))
  · intro hp
    rcases hp with ⟨hp₁, hp₂, hp₃⟩
    refine ⟨(a⁻¹ • y, a⁻¹ ^ 2 * s), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · change vec3EuclideanNorm (a⁻¹ • y - x) < r
        have hdiff : a⁻¹ • y - x = a⁻¹ • (y - a • x) := by
          rw [smul_sub, smul_smul]
          simp [ha.ne']
        rw [hdiff, vec3EuclideanNorm_smul, abs_inv, abs_of_pos ha]
        have h := mul_lt_mul_of_pos_left hp₁ (inv_pos.mpr ha)
        simpa [ha.ne'] using h
      · have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
        have hmul : a ^ 2 * (t - r ^ 2) < a ^ 2 * (a⁻¹ ^ 2 * s) := by
          calc
            a ^ 2 * (t - r ^ 2) = a ^ 2 * t - (a * r) ^ 2 := by ring
            _ < s := hp₂
            _ = a ^ 2 * (a⁻¹ ^ 2 * s) := by field_simp [ha.ne']
        have h := lt_of_mul_lt_mul_left hmul (le_of_lt ha2)
        exact h
      · apply le_of_mul_le_mul_left _ (sq_pos_of_pos ha)
        simpa [ha.ne'] using hp₃
    · apply Prod.ext
      · simp [parabolicScale, smul_smul, ha.ne']
      · change a ^ 2 * (a⁻¹ ^ 2 * s) = s
        field_simp [ha.ne']

instance : MeasureSpace ParabolicPoint := inferInstanceAs (MeasureSpace (Vec3 × ℝ))

lemma vec3Ball_measurable (x : Vec3) (r : ℝ) : MeasurableSet (vec3Ball x r) := by
  have hmeas : Measurable (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
    unfold vec3EuclideanNorm
    fun_prop
  exact hmeas measurableSet_Iio

lemma volume_vec3Ball (x : Vec3) (r : ℝ) :
    volume (vec3Ball x r) = volume (vec3Ball 0 r) := by
  have hpre : (fun y : Vec3 => x + y) ⁻¹' vec3Ball x r = vec3Ball 0 r := by
    ext y
    simp only [mem_preimage, mem_vec3Ball, sub_zero]
    abel_nf
  have h := (measurePreserving_add_left (volume : Measure Vec3) x).measure_preimage
    (vec3Ball_measurable x r).nullMeasurableSet
  rw [hpre] at h
  exact h.symm

lemma volume_parabolicCylinder (x : Vec3) (t r : ℝ) :
    volume (parabolicCylinder x t r) =
      volume (vec3Ball x r) * ENNReal.ofReal (r ^ 2) := by
  rw [parabolicCylinder]
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t) =
    volume (vec3Ball x r) * ENNReal.ofReal (r ^ 2)
  rw [Measure.prod_prod]
  rw [Real.volume_Ioc]
  congr 2
  ring

lemma volume_parabolicCylinder_zero (x : Vec3) (t r : ℝ) :
    volume (parabolicCylinder x t r) =
      volume (vec3Ball 0 r) * ENNReal.ofReal (r ^ 2) := by
  rw [volume_parabolicCylinder, volume_vec3Ball]

/-- Hausdorff measure computed using the parabolic metric and the real value of the exponent. -/
@[expose]
def parabolicHausdorffMeasure (d : ℝ≥0∞) : Measure ParabolicPoint :=
  MeasureTheory.Measure.hausdorffMeasure d.toReal

lemma metricBall_subset_parabolicCylinder {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    @Metric.ball ParabolicPoint parabolicPseudoMetricSpace
      (x, t - r ^ 2 / 2) (r / 2) ⊆
      parabolicCylinder x t r := by
  rintro (p : ParabolicPoint) hp
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      p ((x, t - r ^ 2 / 2) : ParabolicPoint) < r / 2 at hp
  have hdist : @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      p ((x, t - r ^ 2 / 2) : ParabolicPoint) =
      parabolicDist p (x, t - r ^ 2 / 2) := by
    exact dist_eq_parabolicDist p (x, t - r ^ 2 / 2)
  rw [hdist] at hp
  have hp' := hp
  rcases p with ⟨y, s⟩
  rcases (max_lt_iff.mp hp') with ⟨hspace, htime⟩
  have hspace' : vec3EuclideanNorm (y - x) < r := by
    exact hspace.trans (half_lt_self hr)
  have habs : |s - (t - r ^ 2 / 2)| < (r / 2) ^ 2 :=
    (Real.sqrt_lt' (div_pos hr (by norm_num))).mp htime
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  have hrq : (r / 2) ^ 2 < r ^ 2 / 2 := by
    calc
      (r / 2) ^ 2 = (1 / 4 : ℝ) * r ^ 2 := by ring
      _ < (1 / 2 : ℝ) * r ^ 2 :=
        mul_lt_mul_of_pos_right (by norm_num) (sq_pos_of_pos hr)
      _ = r ^ 2 / 2 := by ring
  have hsum : r ^ 2 / 2 + (r / 2) ^ 2 < r ^ 2 := by
    calc
      r ^ 2 / 2 + (r / 2) ^ 2 < r ^ 2 / 2 + r ^ 2 / 2 :=
        add_lt_add_right hrq (r ^ 2 / 2)
      _ = r ^ 2 := by ring
  have hlow : t - r ^ 2 < s := by
    calc
      t - r ^ 2 < (t - r ^ 2 / 2) - (r / 2) ^ 2 := by
        calc
          t - r ^ 2 < t - (r ^ 2 / 2 + (r / 2) ^ 2) :=
            sub_lt_sub_left hsum t
          _ = (t - r ^ 2 / 2) - (r / 2) ^ 2 := by ring
      _ < s := by
        calc
          (t - r ^ 2 / 2) - (r / 2) ^ 2 <
              (t - r ^ 2 / 2) + (s - (t - r ^ 2 / 2)) :=
            by
              convert add_lt_add_left hlo (t - r ^ 2 / 2) using 1 <;> ring
          _ = s := by ring
  have hupp : s ≤ t := by
    have hslt : s < (t - r ^ 2 / 2) + (r / 2) ^ 2 := by
      exact (sub_lt_iff_lt_add.mp hhi) |>.trans_eq (add_comm _ _)
    exact le_of_lt (by
      calc
        s < (t - r ^ 2 / 2) + (r / 2) ^ 2 := hslt
        _ < t := by
          have h := add_lt_add_left hrq (t - r ^ 2 / 2)
          convert h using 1 <;> ring)
  exact ⟨hspace', hlow, hupp⟩

lemma parabolicCylinder_subset_metricBall {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    parabolicCylinder x t r ⊆
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace
        (x, t - r ^ 2 / 2) r := by
  rintro p hp
  change @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      p ((x, t - r ^ 2 / 2) : ParabolicPoint) < r
  have hdist : @dist ParabolicPoint (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
      p ((x, t - r ^ 2 / 2) : ParabolicPoint) =
      parabolicDist p (x, t - r ^ 2 / 2) := by
    exact dist_eq_parabolicDist p (x, t - r ^ 2 / 2)
  rw [hdist]
  rcases p with ⟨y, s⟩
  rcases hp with ⟨hspace, hlow, hupp⟩
  change vec3EuclideanNorm (y - x) < r at hspace
  change t - r ^ 2 < s at hlow
  change s ≤ t at hupp
  refine max_lt hspace ?_
  apply (Real.sqrt_lt' hr).mpr
  apply abs_lt.mpr
  constructor
  · calc
      -(r ^ 2) < -r ^ 2 / 2 := by
        have h : r ^ 2 / 2 < r ^ 2 := by
          have h' : 0 < r ^ 2 / 2 := by positivity
          calc
            r ^ 2 / 2 < r ^ 2 / 2 + r ^ 2 / 2 := by
              calc
                r ^ 2 / 2 = 0 + r ^ 2 / 2 := (zero_add _).symm
                _ < r ^ 2 / 2 + r ^ 2 / 2 := add_lt_add_left h' _
            _ = r ^ 2 := by ring
        have h' := neg_lt_neg h
        calc
          -(r ^ 2) < -(r ^ 2 / 2) := h'
          _ = -r ^ 2 / 2 := by ring
      _ < s - (t - r ^ 2 / 2) := by
        have h := sub_lt_sub_right hlow (t - r ^ 2 / 2)
        calc
          -r ^ 2 / 2 = (t - r ^ 2) - (t - r ^ 2 / 2) := by ring
          _ < s - (t - r ^ 2 / 2) := h
  · calc
      s - (t - r ^ 2 / 2) ≤ r ^ 2 / 2 := by
        apply (sub_le_iff_le_add).2
        calc
          s ≤ t := hupp
          _ = r ^ 2 / 2 + (t - r ^ 2 / 2) := by ring
      _ < r ^ 2 := by
        have h : 0 < r ^ 2 / 2 := by positivity
        calc
          r ^ 2 / 2 < r ^ 2 / 2 + r ^ 2 / 2 := by
            calc
              r ^ 2 / 2 = 0 + r ^ 2 / 2 := (zero_add _).symm
              _ < r ^ 2 / 2 + r ^ 2 / 2 := add_lt_add_left h _
          _ = r ^ 2 := by ring

end CKN.Foundation.Parabolic
