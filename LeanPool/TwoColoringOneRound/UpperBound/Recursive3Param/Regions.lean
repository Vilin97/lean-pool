/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.UpperBound.Recursive3Param.Bound

/-!
## Remaining region computations for the 3-parameter recursive algorithm

This file computes the contributions to `ClassicalAlgorithm.p recursive3ParamAlg` coming from the
`b < t1` and `t1 ≤ b < t2` regions.
-/

namespace Distributed2Coloring

open MeasureTheory
open scoped unitInterval ENNReal

namespace UpperBound
namespace Recursive3Param


/-- Turn an affine `(2T-1)·x + (1-T)` `ofReal` formula into the evaluated-coefficient form. -/
private lemma g_eq_affine_aux {x : Rand} {slope const : ℝ} {g : ℝ≥0∞} (hslope : 0 ≤ slope)
    (hg : g = ENNReal.ofReal (slope * (x : ℝ)) + ENNReal.ofReal const) :
    g = ENNReal.ofReal slope * ENNReal.ofReal (x : ℝ) + ENNReal.ofReal const := by
  rw [hg, ENNReal.ofReal_mul hslope]

lemma gCt_eq_affine (c : Rand) :
    gCt c =
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (c : ℝ) + ENNReal.ofReal (3 / 8 : ℝ) :=
  g_eq_affine_aux (by norm_num) (by
    have ht : (2 * (t : ℝ) - 1) = (1 / 4 : ℝ) := by norm_num [t]
    have hconst : (1 - (t : ℝ)) = (3 / 8 : ℝ) := by norm_num [t]
    simpa [ht, hconst] using gCt_eq_linear c)

lemma gTB_eq_affine (b : Rand) :
    gTB b =
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (b : ℝ) + ENNReal.ofReal (3 / 8 : ℝ) :=
  g_eq_affine_aux (by norm_num) (by
    have ht : (2 * (t : ℝ) - 1) = (1 / 4 : ℝ) := by norm_num [t]
    have hconst : (1 - (t : ℝ)) = (3 / 8 : ℝ) := by norm_num [t]
    simpa [ht, hconst] using gTB_eq_linear b)

lemma gCt2_eq_affine (c : Rand) :
    gCt2 c =
      ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (c : ℝ) + ENNReal.ofReal (15 / 32 : ℝ) :=
  g_eq_affine_aux (by norm_num) (by
    have ht : (2 * (t2 : ℝ) - 1) = (1 / 16 : ℝ) := by norm_num [t2]
    have hconst : (1 - (t2 : ℝ)) = (15 / 32 : ℝ) := by norm_num [t2]
    simpa [ht, hconst] using gCt2_eq_linear c)

lemma gT2B_eq_affine (b : Rand) :
    gT2B b =
      ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (b : ℝ) + ENNReal.ofReal (15 / 32 : ℝ) :=
  g_eq_affine_aux (by norm_num) (by
    have ht : (2 * (t2 : ℝ) - 1) = (1 / 16 : ℝ) := by norm_num [t2]
    have hconst : (1 - (t2 : ℝ)) = (15 / 32 : ℝ) := by norm_num [t2]
    simpa [ht, hconst] using gT2B_eq_linear b)

/-- Measurability of an affine `slope · ofReal(coe ·) + ofReal const` function. -/
private lemma measurable_affine_ofReal (slope const : ℝ) :
    Measurable fun x : Rand =>
      ENNReal.ofReal slope * ENNReal.ofReal (x : ℝ) + ENNReal.ofReal const :=
  (measurable_const.mul (ENNReal.measurable_ofReal.comp measurable_subtype_coe)).add
    measurable_const

private lemma measurable_gCt : Measurable gCt := by
  simpa only [funext gCt_eq_affine] using measurable_affine_ofReal (1 / 4) (3 / 8)

private lemma measurable_gTB : Measurable gTB := by
  simpa only [funext gTB_eq_affine] using measurable_affine_ofReal (1 / 4) (3 / 8)

private lemma measurable_gCt2 : Measurable gCt2 := by
  simpa only [funext gCt2_eq_affine] using measurable_affine_ofReal (1 / 16) (15 / 32)

private lemma measurable_gT2B : Measurable gT2B := by
  simpa only [funext gT2B_eq_affine] using measurable_affine_ofReal (1 / 16) (15 / 32)

private lemma mu_Ico_eq (a r : Rand) : μ (Set.Ico a r) = ENNReal.ofReal ((r : ℝ) - (a : ℝ)) := by
  simp [μ]

private lemma Iio_inter_Iio_left {a b : Rand} (hab : a ≤ b) :
    (Set.Iio a ∩ Set.Iio b : Set Rand) = Set.Iio a := by
  rw [Set.inter_eq_left]
  exact Set.Iio_subset_Iio hab

private lemma Iio_diff_Iio {a b : Rand} (_hab : a ≤ b) :
    (Set.Iio b \ Set.Iio a : Set Rand) = Set.Ico a b := by
  ext c
  simp only [Set.mem_sdiff, Set.mem_Iio, Set.mem_Ico, not_lt]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

private lemma Ico_inter_Iio {a b c : Rand} (hcb : c ≤ b) :
    (Set.Ico a b ∩ Set.Iio c : Set Rand) = Set.Ico a c := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Iio]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, lt_of_lt_of_le h.2 hcb⟩, h.2⟩⟩

private lemma Ico_diff_Iio {a b c : Rand} (hac : a ≤ c) :
    (Set.Ico a b \ Set.Iio c : Set Rand) = Set.Ico c b := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_Iio, not_lt]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨le_trans hac h.1, h.2⟩, h.1⟩⟩

private lemma measurable_mul_Ico_measure {g : Rand → ℝ≥0∞} (hg : Measurable g) (r : Rand) :
    Measurable fun b : Rand => g b * μ (Set.Ico b r) := by
  have hmeas : Measurable fun b : Rand => ENNReal.ofReal ((r : ℝ) - (b : ℝ)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_subtype_coe)
  simpa [μ] using hg.mul hmeas

/-- Merge a product of `ofReal`s into a single `ofReal` of the (evaluated) product. -/
private lemma ofReal_mul_eq {p q r : ℝ} (hp : 0 ≤ p) (hpq : p * q = r) :
    ENNReal.ofReal p * ENNReal.ofReal q = ENNReal.ofReal r := by
  rw [← ENNReal.ofReal_mul hp, hpq]

/-- Merge a sum of `ofReal`s into a single `ofReal` of the (evaluated) sum. -/
private lemma ofReal_add_eq {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = r) :
    ENNReal.ofReal p + ENNReal.ofReal q = ENNReal.ofReal r := by
  rw [← ENNReal.ofReal_add hp hq, hpq]

/-- Split `∫ (affine `g`) · (length `R - x`)` over a set `S` into the moment and length integrals.
Used to evaluate each linear "rectangle/triangle" region integral. -/
private lemma lintegral_affine_mul_length {g : Rand → ℝ≥0∞} {slope const R : ℝ}
    (hg : ∀ x : Rand, g x = ENNReal.ofReal slope * ENNReal.ofReal (x : ℝ) + ENNReal.ofReal const)
    (S : Set Rand) :
    (∫⁻ x in S, g x * ENNReal.ofReal (R - (x : ℝ)) ∂μ) =
      ENNReal.ofReal slope * (∫⁻ x in S, ENNReal.ofReal ((x : ℝ) * (R - (x : ℝ))) ∂μ) +
        ENNReal.ofReal const * (∫⁻ x in S, ENNReal.ofReal (R - (x : ℝ)) ∂μ) := by
  have hrewrite :
      (fun x : Rand => g x * ENNReal.ofReal (R - (x : ℝ))) =
        fun x : Rand =>
          ENNReal.ofReal slope * ENNReal.ofReal ((x : ℝ) * (R - (x : ℝ))) +
            ENNReal.ofReal const * ENNReal.ofReal (R - (x : ℝ)) := by
    funext x
    have hprod :
        ENNReal.ofReal (x : ℝ) * ENNReal.ofReal (R - (x : ℝ)) =
          ENNReal.ofReal ((x : ℝ) * (R - (x : ℝ))) :=
      (ENNReal.ofReal_mul x.property.1).symm
    simp [hg, add_mul, mul_assoc, hprod]
  rw [hrewrite]
  have mx : Measurable fun x : Rand => (x : ℝ) := measurable_subtype_coe
  have mMoment : Measurable fun x : Rand => ENNReal.ofReal ((x : ℝ) * (R - (x : ℝ))) :=
    ENNReal.measurable_ofReal.comp (mx.mul (measurable_const.sub mx))
  have mLength : Measurable fun x : Rand => ENNReal.ofReal (R - (x : ℝ)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub mx)
  rw [MeasureTheory.lintegral_add_left (μ := μ.restrict S) (measurable_const.mul mMoment),
    MeasureTheory.lintegral_const_mul (μ := μ.restrict S) _ mMoment,
    MeasureTheory.lintegral_const_mul (μ := μ.restrict S) _ mLength]

lemma lintegral_innerBC_Iio_one_of_b_lt_t1 {b : Rand} (hb : b < t1) :
    (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) =
      (∫⁻ c in Set.Iio b, gCt c ∂μ) + gTB b * μ (Set.Ico b t) := by
  classical
  have htmeas : MeasurableSet (Set.Iio t : Set Rand) := by simp
  have hsplit :=
    (MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio (1 : Rand) : Set Rand)) (B := (Set.Iio t : Set Rand)) htmeas)
  have hAint : ((Set.Iio (1 : Rand) : Set Rand) ∩ Set.Iio t) = Set.Iio t := by
    rw [Set.inter_comm]; exact Iio_inter_Iio_left t_lt_one.le
  have hAdiff : ((Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t) = Set.Ico t (1 : Rand) :=
    Iio_diff_Iio t_lt_one.le
  have hzero :
      (∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ) = 0 := by
    have hs : MeasurableSet (Set.Ico t (1 : Rand) : Set Rand) := by simp
    have hEq : Set.EqOn (fun c : Rand => innerBC b c) 0 (Set.Ico t (1 : Rand) : Set Rand) := by
      intro c hc
      exact innerBC_eq_zero_of_b_lt_t1_of_t_le_c (b := b) (c := c) hb hc.1
    simpa using (MeasureTheory.setLIntegral_eq_zero (μ := μ) hs hEq)
  have hsplit' :
      (∫⁻ c in Set.Iio t, innerBC b c ∂μ) + ∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ =
        ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ := by
    simpa [hAint, hAdiff] using hsplit
  have hA :
      (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) =
        ∫⁻ c in Set.Iio t, innerBC b c ∂μ := by
    have := hsplit'.symm
    simpa [hzero] using this
  -- Now split the `c < t` integral at `b`.
  have hb_lt_t : b < t := lt_trans hb (lt_trans t1_lt_t2 t2_lt_t)
  have hbmeas : MeasurableSet (Set.Iio b : Set Rand) := by simp
  have hsplit2 :=
    (MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio t : Set Rand)) (B := (Set.Iio b : Set Rand)) hbmeas)
  have hBint : (Set.Iio t ∩ Set.Iio b : Set Rand) = Set.Iio b := by
    rw [Set.inter_comm]; exact Iio_inter_Iio_left hb_lt_t.le
  have hBdiff : (Set.Iio t \ Set.Iio b : Set Rand) = Set.Ico b t :=
    Iio_diff_Iio hb_lt_t.le
  have hIo :
      (∫⁻ c in Set.Iio b, innerBC b c ∂μ) = ∫⁻ c in Set.Iio b, gCt c ∂μ := by
    have hs : MeasurableSet (Set.Iio b : Set Rand) := by simp
    have hEq : Set.EqOn (fun c : Rand => innerBC b c) gCt (Set.Iio b : Set Rand) := by
      intro c hc
      exact innerBC_eq_gCt_of_b_lt_t1_of_c_lt_b (b := b) (c := c) hb hc
    exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs hEq
  have hIco :
      (∫⁻ c in Set.Ico b t, innerBC b c ∂μ) = gTB b * μ (Set.Ico b t) := by
    have hs : MeasurableSet (Set.Ico b t : Set Rand) := by simp
    have hEq :
        Set.EqOn (fun c : Rand => innerBC b c) (fun _ => gTB b) (Set.Ico b t : Set Rand) := by
      intro c hc
      exact innerBC_eq_gTB_of_b_lt_t1_of_b_le_c_of_c_lt_t (b := b) (c := c) hb hc.1 hc.2
    calc
      (∫⁻ c in Set.Ico b t, innerBC b c ∂μ) =
          ∫⁻ _c in Set.Ico b t, gTB b ∂μ := MeasureTheory.setLIntegral_congr_fun (μ := μ) hs hEq
      _ = gTB b * μ (Set.Ico b t) := by simp
  have hsplit2' :
      (∫⁻ c in Set.Iio t, innerBC b c ∂μ) =
        (∫⁻ c in Set.Iio b, innerBC b c ∂μ) + ∫⁻ c in Set.Ico b t, innerBC b c ∂μ := by
    have := hsplit2.symm
    simpa [hBint, hBdiff, add_comm] using this
  -- Put everything together.
  calc
    (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) =
        ∫⁻ c in Set.Iio t, innerBC b c ∂μ := hA
    _ = (∫⁻ c in Set.Iio b, innerBC b c ∂μ) + ∫⁻ c in Set.Ico b t, innerBC b c ∂μ := hsplit2'
    _ = (∫⁻ c in Set.Iio b, gCt c ∂μ) + gTB b * μ (Set.Ico b t) := by simp [hIo, hIco]

private lemma lintegral_b_below_t1_triangle_value :
    (∫⁻ b in Set.Iio t1, ∫⁻ c in Set.Iio b, gCt c ∂μ ∂μ) =
      ENNReal.ofReal (117 / 4096 : ℝ) := by
  have htri := lintegral_triangle_Iio (B := t1) (f := gCt) measurable_gCt
  have htri' :
      (∫⁻ b in Set.Iio t1, ∫⁻ c in Set.Iio b, gCt c ∂μ ∂μ) =
        ∫⁻ c in Set.Iio t1, gCt c * ENNReal.ofReal ((t1 : ℝ) - (c : ℝ)) ∂μ := by
    simpa [μ] using htri
  have ha0 : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have hb0 : 0 ≤ (3 / 8 : ℝ) := by norm_num
  have hmul_int :
      (∫⁻ c in Set.Iio t1, ENNReal.ofReal ((c : ℝ) * ((t1 : ℝ) - (c : ℝ))) ∂μ) =
        ENNReal.ofReal (9 / 1024 : ℝ) := by
    have h :=
      (setLIntegral_ofReal_mul_sub_Iio (r := t1) (b := t1)
        (hbr := (le_rfl : (t1 : ℝ) ≤ t1)))
    have hr :
        ((t1 : ℝ) * (t1 : ℝ) ^ 2 / 2 - (t1 : ℝ) ^ 3 / 3) = (9 / 1024 : ℝ) := by
      norm_num [t1]
    simpa [μ, hr] using h
  have hsub_int :
      (∫⁻ c in Set.Iio t1, ENNReal.ofReal ((t1 : ℝ) - (c : ℝ)) ∂μ) =
        ENNReal.ofReal (9 / 128 : ℝ) := by
    have h :=
      (setLIntegral_ofReal_sub_id_Iio (r := t1) (b := t1)
        (hbr := (le_rfl : (t1 : ℝ) ≤ t1)))
    have hr :
        ((t1 : ℝ) * (t1 : ℝ) - (t1 : ℝ) ^ 2 / 2) = (9 / 128 : ℝ) := by
      norm_num [t1]
    simpa [μ, hr] using h
  rw [htri', lintegral_affine_mul_length gCt_eq_affine, hmul_int, hsub_int,
    ofReal_mul_eq ha0 (by norm_num : (1 / 4 : ℝ) * (9 / 1024 : ℝ) = 9 / 4096),
    ofReal_mul_eq hb0 (by norm_num : (3 / 8 : ℝ) * (9 / 128 : ℝ) = 27 / 1024)]
  exact ofReal_add_eq (by norm_num) (by norm_num)
    (by norm_num : (9 / 4096 : ℝ) + (27 / 1024 : ℝ) = 117 / 4096)

private lemma lintegral_b_below_t1_gTB_value :
    (∫⁻ b in Set.Iio t1, gTB b * μ (Set.Ico b t) ∂μ) =
      ENNReal.ofReal (279 / 4096 : ℝ) := by
  have ha0 : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have hb0 : 0 ≤ (3 / 8 : ℝ) := by norm_num
  have ht1 : (t1 : ℝ) ≤ t := le_trans t1_le_t2 t2_le_t
  have hmul_int :
      (∫⁻ b in Set.Iio t1,
            ENNReal.ofReal ((b : ℝ) * ((t : ℝ) - (b : ℝ))) ∂(volume : Measure Rand)) =
          ENNReal.ofReal (27 / 1024 : ℝ) := by
    have h :=
      (setLIntegral_ofReal_mul_sub_Iio (r := t) (b := t1) (hbr := ht1))
    have hr : ((t : ℝ) * (t1 : ℝ) ^ 2 / 2 - (t1 : ℝ) ^ 3 / 3) = (27 / 1024 : ℝ) := by
      norm_num [t1, t]
    simpa [hr] using h
  have hsub_int :
      (∫⁻ b in Set.Iio t1, ENNReal.ofReal ((t : ℝ) - (b : ℝ)) ∂(volume : Measure Rand)) =
          ENNReal.ofReal (21 / 128 : ℝ) := by
    have h :=
      (setLIntegral_ofReal_sub_id_Iio (r := t) (b := t1) (hbr := ht1))
    have hr : ((t : ℝ) * (t1 : ℝ) - (t1 : ℝ) ^ 2 / 2) = (21 / 128 : ℝ) := by norm_num [t1, t]
    simpa [hr] using h
  simp_rw [mu_Ico_eq]
  rw [lintegral_affine_mul_length gTB_eq_affine, hmul_int, hsub_int,
    ofReal_mul_eq ha0 (by norm_num : (1 / 4 : ℝ) * (27 / 1024 : ℝ) = 27 / 4096),
    ofReal_mul_eq hb0 (by norm_num : (3 / 8 : ℝ) * (21 / 128 : ℝ) = 63 / 1024)]
  exact ofReal_add_eq (by norm_num) (by norm_num)
    (by norm_num : (27 / 4096 : ℝ) + (63 / 1024 : ℝ) = 279 / 4096)

lemma lintegral_b_below_t1_value :
    (∫⁻ b in Set.Iio t1, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
      ENNReal.ofReal (99 / 1024 : ℝ)
:= by
  classical
  have hs : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
  have hEq :
      Set.EqOn
        (fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
        (fun b : Rand => (∫⁻ c in Set.Iio b, gCt c ∂μ) + gTB b * μ (Set.Ico b t))
        (Set.Iio t1 : Set Rand) := by
    intro b hb
    simpa using (lintegral_innerBC_Iio_one_of_b_lt_t1 (b := b) hb)
  have hcongr :
      (∫⁻ b in Set.Iio t1, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        ∫⁻ b in Set.Iio t1,
          (∫⁻ c in Set.Iio b, gCt c ∂μ) + gTB b * μ (Set.Ico b t) ∂μ := by
    exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs hEq
  rw [hcongr]
  -- Split into the `gTB` part (measurable) and the triangle part.
  have hmeasTB : Measurable fun b : Rand => gTB b * μ (Set.Ico b t) :=
    measurable_mul_Ico_measure measurable_gTB t
  have hsplit :
      (∫⁻ b in Set.Iio t1,
          (∫⁻ c in Set.Iio b, gCt c ∂μ) + gTB b * μ (Set.Ico b t) ∂μ) =
        (∫⁻ b in Set.Iio t1, gTB b * μ (Set.Ico b t) ∂μ) +
          ∫⁻ b in Set.Iio t1, (∫⁻ c in Set.Iio b, gCt c ∂μ) ∂μ := by
    have :
        (∫⁻ b in Set.Iio t1,
            gTB b * μ (Set.Ico b t) + (∫⁻ c in Set.Iio b, gCt c ∂μ) ∂μ) =
          (∫⁻ b in Set.Iio t1, gTB b * μ (Set.Ico b t) ∂μ) +
            ∫⁻ b in Set.Iio t1, (∫⁻ c in Set.Iio b, gCt c ∂μ) ∂μ := by
      simpa using
        (MeasureTheory.lintegral_add_left (μ := μ.restrict (Set.Iio t1)) hmeasTB
          (fun b : Rand => ∫⁻ c in Set.Iio b, gCt c ∂μ))
    simpa [add_comm, add_left_comm, add_assoc] using this
  rw [hsplit]
  have htri_val :
      (∫⁻ b in Set.Iio t1, ∫⁻ c in Set.Iio b, gCt c ∂μ ∂μ) =
        ENNReal.ofReal (117 / 4096 : ℝ) :=
    lintegral_b_below_t1_triangle_value
  have hTB_val :
      (∫⁻ b in Set.Iio t1, gTB b * μ (Set.Ico b t) ∂μ) =
        ENNReal.ofReal (279 / 4096 : ℝ) :=
    lintegral_b_below_t1_gTB_value
  rw [hTB_val, htri_val]
  exact ofReal_add_eq (by norm_num) (by norm_num)
    (by norm_num : (279 / 4096 : ℝ) + (117 / 4096 : ℝ) = 99 / 1024)

/-!
### `t1 ≤ b < t2` region

For `t1 ≤ b < t2`, the integrand splits into four `c`-regions:
`c < t1`, `t1 ≤ c < b`, `b ≤ c < t2`, and `t2 ≤ c < t` (with zero contribution for `c ≥ t`).
-/

lemma lintegral_innerBC_Iio_one_of_t1_le_b_lt_t2 {b : Rand} (hb1 : t1 ≤ b) (hb2 : b < t2) :
    (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) =
      ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
            constT1T * μ (Set.Ico t2 t)) +
        ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ := by
  classical
  have htmeas : MeasurableSet (Set.Iio t : Set Rand) := by simp
  have hsplit :=
    MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio (1 : Rand) : Set Rand)) (B := (Set.Iio t : Set Rand)) htmeas
  have hAint : ((Set.Iio (1 : Rand) : Set Rand) ∩ Set.Iio t) = Set.Iio t := by
    rw [Set.inter_comm]; exact Iio_inter_Iio_left t_lt_one.le
  have hAdiff : ((Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t) = Set.Ico t (1 : Rand) :=
    Iio_diff_Iio t_lt_one.le
  -- On `t ≤ c < 1`, the contribution is `0` a.e. (we use `Ioc` to get `t < c`).
  have hIco : (Set.Ico t (1 : Rand) : Set Rand) =ᵐ[μ] (Set.Ioc t (1 : Rand) : Set Rand) := by
    simpa using (MeasureTheory.Ico_ae_eq_Ioc (μ := μ) (a := t) (b := (1 : Rand)))
  have hzeroIoc :
      (∫⁻ c in Set.Ioc t (1 : Rand), innerBC b c ∂μ) = 0 := by
    have hs' : MeasurableSet (Set.Ioc t (1 : Rand) : Set Rand) := by simp
    have hEq :
        Set.EqOn (fun c : Rand => innerBC b c) 0 (Set.Ioc t (1 : Rand) : Set Rand) := by
      intro c hc
      exact innerBC_eq_zero_of_t1_le_b_lt_t2_of_t_lt_c (b := b) hb1 hb2 hc.1
    simpa using (MeasureTheory.setLIntegral_eq_zero (μ := μ) hs' hEq)
  have hzero :
      (∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ) = 0 := by
    have := (MeasureTheory.setLIntegral_congr (μ := μ) (f := fun c => innerBC b c) hIco)
    simpa [hzeroIoc] using this
  have hsplit' :
      (∫⁻ c in Set.Iio t, innerBC b c ∂μ) + ∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ =
        ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ := by
    simpa [hAint, hAdiff] using hsplit
  have hA :
      (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) =
        ∫⁻ c in Set.Iio t, innerBC b c ∂μ := by
    have := hsplit'.symm
    simpa [hzero] using this
  -- Split `c < t` at `t2`.
  have ht2meas : MeasurableSet (Set.Iio t2 : Set Rand) := by simp
  have hsplit2 :=
    MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio t : Set Rand)) (B := (Set.Iio t2 : Set Rand)) ht2meas
  have hBint : (Set.Iio t ∩ Set.Iio t2 : Set Rand) = Set.Iio t2 := by
    rw [Set.inter_comm]; exact Iio_inter_Iio_left t2_lt_t.le
  have hBdiff : (Set.Iio t \ Set.Iio t2 : Set Rand) = Set.Ico t2 t :=
    Iio_diff_Iio t2_lt_t.le
  have hconst :
      (∫⁻ c in Set.Ico t2 t, innerBC b c ∂μ) = constT1T * μ (Set.Ico t2 t) := by
    have hs' : MeasurableSet (Set.Ico t2 t : Set Rand) := by simp
    have hEq :
        Set.EqOn (fun c : Rand => innerBC b c) (fun _ => constT1T) (Set.Ico t2 t : Set Rand) := by
      intro c hc
      exact innerBC_eq_constT1T_of_t1_le_b_lt_t2_of_t2_le_c_of_c_lt_t (b := b) hb1 hb2 hc.1 hc.2
    calc
      (∫⁻ c in Set.Ico t2 t, innerBC b c ∂μ) =
          ∫⁻ _c in Set.Ico t2 t, constT1T ∂μ := by
            exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs' hEq
      _ = constT1T * μ (Set.Ico t2 t) := by simp
  have hsplit2' :
      (∫⁻ c in Set.Iio t, innerBC b c ∂μ) =
        (∫⁻ c in Set.Iio t2, innerBC b c ∂μ) + constT1T * μ (Set.Ico t2 t) := by
    have := hsplit2.symm
    simpa [hBint, hBdiff, hconst, add_comm, add_left_comm, add_assoc] using this
  -- Split `c < t2` at `t1`.
  have ht1meas : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
  have hsplit3 :=
    MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio t2 : Set Rand)) (B := (Set.Iio t1 : Set Rand)) ht1meas
  have hCint : (Set.Iio t2 ∩ Set.Iio t1 : Set Rand) = Set.Iio t1 := by
    rw [Set.inter_comm]; exact Iio_inter_Iio_left t1_lt_t2.le
  have hCdiff : (Set.Iio t2 \ Set.Iio t1 : Set Rand) = Set.Ico t1 t2 :=
    Iio_diff_Iio t1_lt_t2.le
  have hPartC :
      (∫⁻ c in Set.Iio t1, innerBC b c ∂μ) = ∫⁻ c in Set.Iio t1, gCt c ∂μ := by
    have hs' : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
    have hEq :
        Set.EqOn (fun c : Rand => innerBC b c) gCt (Set.Iio t1 : Set Rand) := by
      intro c hc
      exact innerBC_eq_gCt_of_t1_le_b_lt_t2_of_c_lt_t1 (b := b) hb1 hb2 hc
    exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs' hEq
  -- Split `c ∈ [t1,t2)` at `b`.
  have hbmeas : MeasurableSet (Set.Iio b : Set Rand) := by simp
  have hsplit4 :=
    MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Ico t1 t2 : Set Rand)) (B := (Set.Iio b : Set Rand)) hbmeas
  have hDint : (Set.Ico t1 t2 ∩ Set.Iio b : Set Rand) = Set.Ico t1 b :=
    Ico_inter_Iio hb2.le
  have hDdiff : (Set.Ico t1 t2 \ Set.Iio b : Set Rand) = Set.Ico b t2 :=
    Ico_diff_Iio hb1
  have hPartD1 :
      (∫⁻ c in Set.Ico t1 b, innerBC b c ∂μ) = ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ := by
    have hs' : MeasurableSet (Set.Ico t1 b : Set Rand) := by simp
    have hEq :
        Set.EqOn (fun c : Rand => innerBC b c) gCt2 (Set.Ico t1 b : Set Rand) := by
      intro c hc
      exact innerBC_eq_gCt2_of_t1_le_b_lt_t2_of_t1_le_c_of_c_lt_b (b := b) hb1 hb2 hc.1 hc.2
    exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs' hEq
  have hPartD2 :
      (∫⁻ c in Set.Ico b t2, innerBC b c ∂μ) = gT2B b * μ (Set.Ico b t2) := by
    have hs' : MeasurableSet (Set.Ico b t2 : Set Rand) := by simp
    have hEq :
        Set.EqOn (fun c : Rand => innerBC b c) (fun _ => gT2B b) (Set.Ico b t2 : Set Rand) := by
      intro c hc
      exact innerBC_eq_gT2B_of_t1_le_b_lt_t2_of_b_le_c_of_c_lt_t2 (b := b) hb1 hb2 hc.1 hc.2
    calc
      (∫⁻ c in Set.Ico b t2, innerBC b c ∂μ) =
          ∫⁻ _c in Set.Ico b t2, gT2B b ∂μ := MeasureTheory.setLIntegral_congr_fun (μ := μ) hs' hEq
      _ = gT2B b * μ (Set.Ico b t2) := by simp
  have hsplit4' :
      (∫⁻ c in Set.Ico t1 t2, innerBC b c ∂μ) =
        (∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ) + gT2B b * μ (Set.Ico b t2) := by
    have := hsplit4.symm
    simpa [hDint, hDdiff, hPartD1, hPartD2, add_comm, add_left_comm, add_assoc] using this
  have hsplit3' :
      (∫⁻ c in Set.Iio t2, innerBC b c ∂μ) =
        (∫⁻ c in Set.Iio t1, gCt c ∂μ) +
          ((∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ) + gT2B b * μ (Set.Ico b t2)) := by
    have := hsplit3.symm
    simpa [hCint, hCdiff, hPartC, hsplit4', add_comm, add_left_comm, add_assoc] using this
  -- Put everything together.
  calc
    (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) =
        ∫⁻ c in Set.Iio t, innerBC b c ∂μ := hA
    _ =
        (∫⁻ c in Set.Iio t2, innerBC b c ∂μ) + constT1T * μ (Set.Ico t2 t) := hsplit2'
    _ =
        (∫⁻ c in Set.Iio t1, gCt c ∂μ) +
            ((∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ) + gT2B b * μ (Set.Ico b t2)) +
          constT1T * μ (Set.Ico t2 t) := by
          simp [hsplit3', add_left_comm, add_comm]
    _ =
        ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
              constT1T * μ (Set.Ico t2 t)) +
          ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ := by
          simp [add_left_comm, add_comm]

private lemma lintegral_gT2B_rect_t1_t2_value :
    (∫⁻ b in Set.Ico t1 t2, gT2B b * μ (Set.Ico b t2) ∂μ) =
      ENNReal.ofReal (19025 / 3145728 : ℝ) := by
  have ha0 : 0 ≤ (1 / 16 : ℝ) := by norm_num
  have hb0 : 0 ≤ (15 / 32 : ℝ) := by norm_num
  have hpoly1 :
      (∫⁻ x in Set.Ico t1 t2, ENNReal.ofReal ((x : ℝ) * ((t2 : ℝ) - x)) ∂μ) =
        ENNReal.ofReal (1025 / 196608 : ℝ) := by
    have h :=
      (setLIntegral_ofReal_mul_sub_Ico (r := t2) (a := t1) (b := t2) t1_le_t2
        (le_rfl : (t2 : ℝ) ≤ t2))
    have hr :
        ((t2 : ℝ) * ((t2 : ℝ) ^ 2 - (t1 : ℝ) ^ 2) / 2 -
            (((t2 : ℝ) ^ 3 - (t1 : ℝ) ^ 3) / 3)) =
          (1025 / 196608 : ℝ) := by
      norm_num [t1, t2]
    simpa [μ, hr] using h
  have hpoly2 :
      (∫⁻ x in Set.Ico t1 t2, ENNReal.ofReal ((t2 : ℝ) - x) ∂μ) =
        ENNReal.ofReal (25 / 2048 : ℝ) := by
    have h :=
      (setLIntegral_ofReal_sub_id_Ico (r := t2) (a := t1) (b := t2) t1_le_t2
        (le_rfl : (t2 : ℝ) ≤ t2))
    have hr :
        ((t2 : ℝ) * ((t2 : ℝ) - (t1 : ℝ)) - (((t2 : ℝ) ^ 2 - (t1 : ℝ) ^ 2) / 2)) =
          (25 / 2048 : ℝ) := by
      norm_num [t1, t2]
    simpa [μ, hr] using h
  simp_rw [mu_Ico_eq]
  rw [lintegral_affine_mul_length gT2B_eq_affine, hpoly1, hpoly2,
    ofReal_mul_eq ha0 (by norm_num : (1 / 16 : ℝ) * (1025 / 196608 : ℝ) = 1025 / 3145728),
    ofReal_mul_eq hb0 (by norm_num : (15 / 32 : ℝ) * (25 / 2048 : ℝ) = 18000 / 3145728)]
  exact ofReal_add_eq (by norm_num) (by norm_num)
    (by norm_num : (1025 / 3145728 : ℝ) + (18000 / 3145728 : ℝ) = 19025 / 3145728)

private lemma lintegral_gCt2_triangle_t1_t2_value :
    (∫⁻ b in Set.Ico t1 t2, ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ ∂μ) =
      ENNReal.ofReal (19025 / 3145728 : ℝ)
:= by
  -- Use the indicator trick and the `Iio` triangle swap.
  let f : Rand → ℝ≥0∞ := (Set.Ici t1).indicator gCt2
  have hf : Measurable f := by simpa [f] using measurable_gCt2.indicator (by simp)
  have htriIio := lintegral_triangle_Iio (B := t2) (f := f) hf
  -- Reduce the `b`-domain from `Iio t2` to `Ico t1 t2` by splitting at `t1`.
  have ht1meas : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
  have hsplitb :=
    MeasureTheory.lintegral_inter_add_sdiff (μ := μ)
      (f := fun b : Rand => ∫⁻ c in Set.Iio b, f c ∂μ)
      (A := (Set.Iio t2 : Set Rand)) (B := (Set.Iio t1 : Set Rand)) ht1meas
  have hBint : (Set.Iio t2 ∩ Set.Iio t1 : Set Rand) = Set.Iio t1 := by
    rw [Set.inter_comm]; exact Iio_inter_Iio_left t1_lt_t2.le
  have hBdiff : (Set.Iio t2 \ Set.Iio t1 : Set Rand) = Set.Ico t1 t2 :=
    Iio_diff_Iio t1_lt_t2.le
  have hzero :
      (∫⁻ b in Set.Iio t1, ∫⁻ c in Set.Iio b, f c ∂μ ∂μ) = 0 := by
    have hs' : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
    have hEq :
        Set.EqOn (fun b : Rand => ∫⁻ c in Set.Iio b, f c ∂μ) 0 (Set.Iio t1 : Set Rand) := by
      intro b hb
      have hsIb : MeasurableSet (Set.Iio b : Set Rand) := by simp
      have hEq0 : Set.EqOn f 0 (Set.Iio b : Set Rand) := by
        intro c hc
        have hct1 : (c : ℝ) < t1 := lt_trans hc hb
        have : c ∉ Set.Ici t1 := by simpa [Set.mem_Ici] using (not_le_of_gt hct1)
        simp [f, this]
      simpa using (MeasureTheory.setLIntegral_eq_zero (μ := μ) hsIb hEq0)
    simpa using (MeasureTheory.setLIntegral_eq_zero (μ := μ) hs' hEq)
  have hsplitb' :
      (∫⁻ b in Set.Iio t2, ∫⁻ c in Set.Iio b, f c ∂μ ∂μ) =
        (∫⁻ b in Set.Ico t1 t2, ∫⁻ c in Set.Iio b, f c ∂μ ∂μ) := by
    have := hsplitb.symm
    -- `A ∩ B = Iio t1`, `A \ B = Ico t1 t2`, and the `Iio t1` part is zero.
    simpa [hBint, hBdiff, hzero, add_zero] using this
  -- Convert the inner integral on `Iio b` to one on `Ico t1 b` (since `f` vanishes below `t1`).
  have hinner :
      (fun b : Rand => ∫⁻ c in Set.Iio b, f c ∂μ) =
        fun b : Rand => ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ := by
    funext b
    have hsIb : MeasurableSet (Set.Iio b : Set Rand) := by simp
    have hsIci : MeasurableSet (Set.Ici t1 : Set Rand) := by simp
    have :
        (∫⁻ c in Set.Iio b, f c ∂μ) =
          ∫⁻ c in Set.Ici t1 ∩ Set.Iio b, gCt2 c ∂μ := by
        simp [f, hsIci]
    have hset : (Set.Ici t1 ∩ Set.Iio b : Set Rand) = Set.Ico t1 b := by
      ext c
      simp [Set.mem_Ici, Set.mem_Iio, Set.mem_Ico]
    simpa [hset] using this
  -- Apply the triangle swap and simplify the RHS to the already computed rectangle integral.
  have hIio_eval :
      (∫⁻ b in Set.Iio t2, ∫⁻ c in Set.Iio b, f c ∂μ ∂μ) =
        ∫⁻ c in Set.Iio t2, f c * μ (Set.Ioo c t2) ∂μ := by
    simpa using htriIio
  -- Use the restriction equality `hsplitb'` and compute using `hRect`.
  have : (∫⁻ b in Set.Ico t1 t2, ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ ∂μ) =
      (∫⁻ b in Set.Iio t2, ∫⁻ c in Set.Iio b, f c ∂μ ∂μ) := by
    -- rewrite both sides by `hinner` and `hsplitb'`
    simpa [hinner] using hsplitb'.symm
  -- Evaluate the swapped integral by restricting to `t1 ≤ c < t2` and comparing with `hRect`.
  have hSwap :
      (∫⁻ c in Set.Iio t2, f c * μ (Set.Ioo c t2) ∂μ) =
        ∫⁻ c in Set.Ico t1 t2, gCt2 c * μ (Set.Ioo c t2) ∂μ := by
    have hsIci : MeasurableSet (Set.Ici t1 : Set Rand) := by simp
    have hind :
        (fun c : Rand => f c * μ (Set.Ioo c t2)) =
          (Set.Ici t1).indicator (fun c : Rand => gCt2 c * μ (Set.Ioo c t2)) := by
      funext c
      by_cases hc : c ∈ (Set.Ici t1 : Set Rand)
      · simp [f, hc, Set.indicator]
      · simp [f, hc, Set.indicator]
    have hInd :=
      (MeasureTheory.setLIntegral_indicator (μ := μ) (s := Set.Ici t1) (t := Set.Iio t2) hsIci
        (fun c : Rand => gCt2 c * μ (Set.Ioo c t2)))
    have hset : (Set.Ici t1 ∩ Set.Iio t2 : Set Rand) = Set.Ico t1 t2 := by
      ext c
      simp [Set.mem_Ici, Set.mem_Iio, Set.mem_Ico]
    have hInd' :
        (∫⁻ c in Set.Iio t2,
              (Set.Ici t1).indicator (fun c : Rand => gCt2 c * μ (Set.Ioo c t2)) c ∂μ) =
            ∫⁻ c in Set.Ico t1 t2, gCt2 c * μ (Set.Ioo c t2) ∂μ := by
      -- rewrite the target set and reuse `hInd`
      rwa [← hset]
    calc
      (∫⁻ c in Set.Iio t2, f c * μ (Set.Ioo c t2) ∂μ) =
          ∫⁻ c in Set.Iio t2,
              (Set.Ici t1).indicator (fun c : Rand => gCt2 c * μ (Set.Ioo c t2)) c ∂μ := by
                simp_rw [hind]
      _ = ∫⁻ c in Set.Ico t1 t2, gCt2 c * μ (Set.Ioo c t2) ∂μ := hInd'
  have hEqIntegrand :
      (fun c : Rand => gCt2 c * μ (Set.Ioo c t2)) =
        fun c : Rand => gT2B c * μ (Set.Ico c t2) := by
    funext c
    simp [gCt2, gT2B, μ, mul_comm]
  have hSwap_to_Rect :
      (∫⁻ c in Set.Ico t1 t2, gCt2 c * μ (Set.Ioo c t2) ∂μ) =
        (∫⁻ b in Set.Ico t1 t2, gT2B b * μ (Set.Ico b t2) ∂μ) := by
    have hsIco : MeasurableSet (Set.Ico t1 t2 : Set Rand) := by simp
    have hEqOn :
        Set.EqOn (fun c : Rand => gCt2 c * μ (Set.Ioo c t2))
          (fun c : Rand => gT2B c * μ (Set.Ico c t2)) (Set.Ico t1 t2 : Set Rand) := by
      intro c _hc
      simpa using congrArg (fun f => f c) hEqIntegrand
    have hcongr :=
      (MeasureTheory.setLIntegral_congr_fun (μ := μ) hsIco hEqOn)
    simpa using hcongr
  calc
    (∫⁻ b in Set.Ico t1 t2, ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ ∂μ) =
        (∫⁻ b in Set.Iio t2, ∫⁻ c in Set.Iio b, f c ∂μ ∂μ) := this
    _ = ∫⁻ c in Set.Iio t2, f c * μ (Set.Ioo c t2) ∂μ := hIio_eval
    _ = ∫⁻ c in Set.Ico t1 t2, gCt2 c * μ (Set.Ioo c t2) ∂μ := hSwap
    _ = ∫⁻ b in Set.Ico t1 t2, gT2B b * μ (Set.Ico b t2) ∂μ := hSwap_to_Rect
    _ = ENNReal.ofReal (19025 / 3145728 : ℝ) := lintegral_gT2B_rect_t1_t2_value

private lemma lintegral_t1_t2_main_value :
    (∫⁻ b in Set.Ico t1 t2,
        (∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
              constT1T * μ (Set.Ico t2 t) ∂μ) =
      ENNReal.ofReal (49680 / 1572864 : ℝ) + ENNReal.ofReal (19025 / 3145728 : ℝ) := by
  have hConstC : (∫⁻ c in Set.Iio t1, gCt c ∂μ) = ENNReal.ofReal (81 / 512 : ℝ) := by
    simpa using lintegral_gCt_Iio_t1
  have hμt1t2 : μ (Set.Ico t1 t2) = ENNReal.ofReal (5 / 32 : ℝ) := by norm_num [μ, t1, t2]
  have hμt2t : μ (Set.Ico t2 t) = ENNReal.ofReal (3 / 32 : ℝ) := by norm_num [μ, t2, t]
  -- Split off the rectangle term; the rest is constant.
  have hconst :
      (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t) =
        ENNReal.ofReal (207 / 1024 : ℝ) := by
    have h45 :
        constT1T * μ (Set.Ico t2 t) = ENNReal.ofReal (45 / 1024 : ℝ) := by
      rw [constT1T_eq, hμt2t]
      exact ofReal_mul_eq (by norm_num) (by norm_num : (15 / 32 : ℝ) * (3 / 32 : ℝ) = 45 / 1024)
    rw [hConstC, h45]
    exact ofReal_add_eq (by norm_num) (by norm_num)
      (by norm_num : (81 / 512 : ℝ) + (45 / 1024 : ℝ) = 207 / 1024)
  -- Integral of the constant part.
  have hconstInt :
      (∫⁻ _b in Set.Ico t1 t2,
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t) ∂μ) =
        ENNReal.ofReal (49680 / 1572864 : ℝ) := by
    calc
      (∫⁻ _b in Set.Ico t1 t2,
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t) ∂μ) =
          ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t)) * μ (Set.Ico t1 t2) := by
            simp
      _ = ENNReal.ofReal (207 / 1024 : ℝ) * ENNReal.ofReal (5 / 32 : ℝ) := by rw [hconst, hμt1t2]
      _ = ENNReal.ofReal (49680 / 1572864 : ℝ) :=
            ofReal_mul_eq (by norm_num)
              (by norm_num : (207 / 1024 : ℝ) * (5 / 32 : ℝ) = 49680 / 1572864)
  -- Combine constant and rectangle.
  have hmeasRect : Measurable fun b : Rand => gT2B b * μ (Set.Ico b t2) :=
    measurable_mul_Ico_measure measurable_gT2B t2
  have hsplitMain :
      (∫⁻ b in Set.Ico t1 t2,
          gT2B b * μ (Set.Ico b t2) +
              ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t)) ∂μ) =
        (∫⁻ b in Set.Ico t1 t2, gT2B b * μ (Set.Ico b t2) ∂μ) +
          ∫⁻ _b in Set.Ico t1 t2,
            (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t) ∂μ := by
    exact
      (MeasureTheory.lintegral_add_left (μ := μ.restrict (Set.Ico t1 t2)) hmeasRect
        (fun _b : Rand =>
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t)))
  -- Finish by rewriting `a + rect(b) + c` as `rect(b) + (a + c)` and applying computed values.
  have hrew :
      (fun b : Rand =>
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
              constT1T * μ (Set.Ico t2 t)) =
        fun b : Rand =>
          gT2B b * μ (Set.Ico b t2) +
            ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t)) := by
    funext b
    simp [add_assoc, add_comm]
  -- Rewrite the LHS integrand, then split and plug in the values.
  simp_rw [hrew]
  rw [hsplitMain, lintegral_gT2B_rect_t1_t2_value, hconstInt]
  simp [add_comm]

lemma lintegral_b_t1_t2_value :
    (∫⁻ b in Set.Ico t1 t2, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
      ENNReal.ofReal (68705 / 1572864 : ℝ)
:= by
  classical
  have hs : MeasurableSet (Set.Ico t1 t2 : Set Rand) := by simp
  have hEq :
      Set.EqOn
        (fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
        (fun b : Rand =>
          ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
                constT1T * μ (Set.Ico t2 t)) +
            ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ)
        (Set.Ico t1 t2 : Set Rand) := by
    intro b hb
    exact lintegral_innerBC_Iio_one_of_t1_le_b_lt_t2 (b := b) hb.1 hb.2
  have hcongr :
      (∫⁻ b in Set.Ico t1 t2, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        ∫⁻ b in Set.Ico t1 t2,
          ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
                constT1T * μ (Set.Ico t2 t)) +
            ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ ∂μ := by
    exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs hEq
  rw [hcongr]
  -- Peel off the measurable part and leave the triangle term as the remainder.
  have hmeasMain :
      Measurable fun b : Rand =>
        (∫⁻ c in Set.Iio t1, gCt c ∂μ) +
          gT2B b * μ (Set.Ico b t2) +
          constT1T * μ (Set.Ico t2 t) := by
    have m_rect : Measurable fun b : Rand => gT2B b * μ (Set.Ico b t2) :=
      measurable_mul_Ico_measure measurable_gT2B t2
    exact ((measurable_const.add m_rect).add measurable_const)
  have hsplit :=
    MeasureTheory.lintegral_add_left (μ := μ.restrict (Set.Ico t1 t2)) hmeasMain
      (fun b : Rand => ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ)
  have hTri :
      (∫⁻ b in Set.Ico t1 t2, ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ ∂μ) =
        ENNReal.ofReal (19025 / 3145728 : ℝ) :=
    lintegral_gCt2_triangle_t1_t2_value
  have hMain :
      (∫⁻ b in Set.Ico t1 t2,
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
                constT1T * μ (Set.Ico t2 t) ∂μ) =
        ENNReal.ofReal (49680 / 1572864 : ℝ) + ENNReal.ofReal (19025 / 3145728 : ℝ) :=
    lintegral_t1_t2_main_value
  -- Combine main + triangle via `hsplit`.
  have htotal :
      (∫⁻ b in Set.Ico t1 t2,
          ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
                constT1T * μ (Set.Ico t2 t)) +
            ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ ∂μ) =
        ENNReal.ofReal (68705 / 1572864 : ℝ) := by
    -- Split by `lintegral_add_left` and use the numeric values.
    have := congrArg (fun z => z) hsplit
    -- `hsplit` is exactly the needed split:
    -- `∫ (main + tri) = ∫ main + ∫ tri`.
    have hsplit' :
        (∫⁻ b in Set.Ico t1 t2,
            ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
                  constT1T * μ (Set.Ico t2 t)) +
              ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ ∂μ) =
          (∫⁻ b in Set.Ico t1 t2,
              (∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
                    constT1T * μ (Set.Ico t2 t) ∂μ) +
            ∫⁻ b in Set.Ico t1 t2, (∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ) ∂μ := by
      simpa using hsplit
    rw [hsplit']
    -- Combine numeric values.
    have hMainVal :
        (∫⁻ b in Set.Ico t1 t2,
            (∫⁻ c in Set.Iio t1, gCt c ∂μ) + gT2B b * μ (Set.Ico b t2) +
                constT1T * μ (Set.Ico t2 t) ∂μ) =
          ENNReal.ofReal (49680 / 1572864 : ℝ) + ENNReal.ofReal (19025 / 3145728 : ℝ) := hMain
    rw [hMainVal, hTri]
    have h2J :
        ENNReal.ofReal (19025 / 3145728 : ℝ) + ENNReal.ofReal (19025 / 3145728 : ℝ) =
          ENNReal.ofReal (19025 / 1572864 : ℝ) :=
      ofReal_add_eq (by norm_num) (by norm_num)
        (by norm_num : (19025 / 3145728 : ℝ) + (19025 / 3145728 : ℝ) = 19025 / 1572864)
    have hsum :
        ENNReal.ofReal (49680 / 1572864 : ℝ) +
            (ENNReal.ofReal (19025 / 3145728 : ℝ) + ENNReal.ofReal (19025 / 3145728 : ℝ)) =
          ENNReal.ofReal (68705 / 1572864 : ℝ) := by
      rw [h2J]
      exact ofReal_add_eq (by norm_num) (by norm_num)
        (by norm_num : (49680 / 1572864 : ℝ) + (19025 / 1572864 : ℝ) = 68705 / 1572864)
    simpa [add_assoc, add_left_comm, add_comm] using hsum
  exact htotal

end Recursive3Param
end UpperBound

end Distributed2Coloring
