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


lemma gCt_eq_affine (c : Rand) :
    gCt c =
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (c : ℝ) + ENNReal.ofReal (3 / 8 : ℝ) := by
  have ha0 : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have ht : (2 * (t : ℝ) - 1) = (1 / 4 : ℝ) := by
    simp [t]
    norm_num
  have hconst : (1 - (t : ℝ)) = (3 / 8 : ℝ) := by
    simp [t]
    norm_num
  have hlin : gCt c = ENNReal.ofReal ((1 / 4 : ℝ) * (c : ℝ)) + ENNReal.ofReal (3 / 8 : ℝ) := by
    simpa [ht, hconst] using (gCt_eq_linear c)
  -- rewrite `ofReal ((1/4) * c)` as `ofReal (1/4) * ofReal c`
  simpa [ENNReal.ofReal_mul ha0, mul_assoc] using hlin

lemma gTB_eq_affine (b : Rand) :
    gTB b =
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (b : ℝ) + ENNReal.ofReal (3 / 8 : ℝ) := by
  have ha0 : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have ht : (2 * (t : ℝ) - 1) = (1 / 4 : ℝ) := by
    simp [t]
    norm_num
  have hconst : (1 - (t : ℝ)) = (3 / 8 : ℝ) := by
    simp [t]
    norm_num
  have hlin : gTB b = ENNReal.ofReal ((1 / 4 : ℝ) * (b : ℝ)) + ENNReal.ofReal (3 / 8 : ℝ) := by
    simpa [ht, hconst] using (gTB_eq_linear b)
  simpa [ENNReal.ofReal_mul ha0, mul_assoc] using hlin

lemma gCt2_eq_affine (c : Rand) :
    gCt2 c =
      ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (c : ℝ) + ENNReal.ofReal (15 / 32 : ℝ) := by
  have ha0 : 0 ≤ (1 / 16 : ℝ) := by norm_num
  have ht : (2 * (t2 : ℝ) - 1) = (1 / 16 : ℝ) := by
    simp [t2]
    norm_num
  have hconst : (1 - (t2 : ℝ)) = (15 / 32 : ℝ) := by
    simp [t2]
    norm_num
  have hlin :
      gCt2 c = ENNReal.ofReal ((1 / 16 : ℝ) * (c : ℝ)) + ENNReal.ofReal (15 / 32 : ℝ) := by
    simpa [ht, hconst] using (gCt2_eq_linear c)
  simpa [ENNReal.ofReal_mul ha0, mul_assoc] using hlin

lemma gT2B_eq_affine (b : Rand) :
    gT2B b =
      ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (b : ℝ) + ENNReal.ofReal (15 / 32 : ℝ) := by
  have ha0 : 0 ≤ (1 / 16 : ℝ) := by norm_num
  have ht : (2 * (t2 : ℝ) - 1) = (1 / 16 : ℝ) := by
    simp [t2]
    norm_num
  have hconst : (1 - (t2 : ℝ)) = (15 / 32 : ℝ) := by
    simp [t2]
    norm_num
  have hlin :
      gT2B b = ENNReal.ofReal ((1 / 16 : ℝ) * (b : ℝ)) + ENNReal.ofReal (15 / 32 : ℝ) := by
    simpa [ht, hconst] using (gT2B_eq_linear b)
  simpa [ENNReal.ofReal_mul ha0, mul_assoc] using hlin

lemma lintegral_innerBC_Iio_one_of_b_lt_t1 {b : Rand} (hb : b < t1) :
    (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) =
      (∫⁻ c in Set.Iio b, gCt c ∂μ) + gTB b * μ (Set.Ico b t) := by
  classical
  have htmeas : MeasurableSet (Set.Iio t : Set Rand) := by simp
  have hsplit :=
    (MeasureTheory.lintegral_inter_add_diff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio (1 : Rand) : Set Rand)) (B := (Set.Iio t : Set Rand)) htmeas)
  have hAint : ((Set.Iio (1 : Rand) : Set Rand) ∩ Set.Iio t) = Set.Iio t := by
    ext c
    constructor
    · intro hc
      exact hc.2
    · intro hc
      have hc1 : (c : ℝ) < 1 := lt_trans (show (c : ℝ) < t from hc) t_lt_one
      exact ⟨by simpa using hc1, hc⟩
  have hAdiff : ((Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t) = Set.Ico t (1 : Rand) := by
    ext c
    constructor
    · rintro ⟨hc1, hct⟩
      exact ⟨le_of_not_gt hct, hc1⟩
    · intro hc
      exact ⟨hc.2, not_lt_of_ge hc.1⟩
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
    (MeasureTheory.lintegral_inter_add_diff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio t : Set Rand)) (B := (Set.Iio b : Set Rand)) hbmeas)
  have hBint : (Set.Iio t ∩ Set.Iio b : Set Rand) = Set.Iio b := by
    ext c
    constructor
    · intro hc
      exact hc.2
    · intro hc
      exact ⟨lt_trans hc hb_lt_t, hc⟩
  have hBdiff : (Set.Iio t \ Set.Iio b : Set Rand) = Set.Ico b t := by
    ext c
    constructor
    · rintro ⟨hct, hcb⟩
      exact ⟨le_of_not_gt hcb, hct⟩
    · intro hc
      exact ⟨hc.2, not_lt_of_ge hc.1⟩
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
          ∫⁻ _c in Set.Ico b t, gTB b ∂μ := by
            exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs hEq
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
  have hgCt : Measurable gCt := by
    have mc : Measurable fun c : Rand => (c : ℝ) := measurable_subtype_coe
    have m_ofReal_c : Measurable fun c : Rand => ENNReal.ofReal (c : ℝ) :=
      ENNReal.measurable_ofReal.comp mc
    have m_gCt_expr :
        Measurable fun c : Rand =>
          ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (c : ℝ) + ENNReal.ofReal (3 / 8 : ℝ) := by
      exact (measurable_const.mul m_ofReal_c).add measurable_const
    have hfun :
        (fun c : Rand => gCt c) =
          fun c : Rand =>
            ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (c : ℝ) + ENNReal.ofReal (3 / 8 : ℝ) := by
      funext c
      simp [gCt_eq_affine]
    simpa [hfun] using m_gCt_expr
  have htri := lintegral_triangle_Iio (B := t1) (f := gCt) hgCt
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
      simp [t1]
      norm_num
    simpa [μ, hr] using h
  have hsub_int :
      (∫⁻ c in Set.Iio t1, ENNReal.ofReal ((t1 : ℝ) - (c : ℝ)) ∂μ) =
        ENNReal.ofReal (9 / 128 : ℝ) := by
    have h :=
      (setLIntegral_ofReal_sub_id_Iio (r := t1) (b := t1)
        (hbr := (le_rfl : (t1 : ℝ) ≤ t1)))
    have hr :
        ((t1 : ℝ) * (t1 : ℝ) - (t1 : ℝ) ^ 2 / 2) = (9 / 128 : ℝ) := by
      simp [t1]
      norm_num
    simpa [μ, hr] using h
  have hrewrite :
      (fun c : Rand => gCt c * ENNReal.ofReal ((t1 : ℝ) - (c : ℝ))) =
        fun c : Rand =>
          ENNReal.ofReal (1 / 4 : ℝ) *
              ENNReal.ofReal ((c : ℝ) * ((t1 : ℝ) - (c : ℝ))) +
            ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal ((t1 : ℝ) - (c : ℝ)) := by
    funext c
    have hc0 : 0 ≤ (c : ℝ) := c.property.1
    have hprod :
        ENNReal.ofReal (c : ℝ) * ENNReal.ofReal ((t1 : ℝ) - (c : ℝ)) =
          ENNReal.ofReal ((c : ℝ) * ((t1 : ℝ) - (c : ℝ))) := by
      simpa using (ENNReal.ofReal_mul hc0).symm
    simp [gCt_eq_affine, add_mul, mul_assoc, hprod]
  rw [htri', hrewrite]
  have hmeas1 :
      Measurable fun c : Rand =>
        ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal ((c : ℝ) * ((t1 : ℝ) - (c : ℝ))) := by
    have mc : Measurable fun c : Rand => (c : ℝ) := measurable_subtype_coe
    have mpoly : Measurable fun c : Rand => (c : ℝ) * ((t1 : ℝ) - (c : ℝ)) :=
      mc.mul (measurable_const.sub mc)
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp mpoly)
  rw [MeasureTheory.lintegral_add_left (μ := μ.restrict (Set.Iio t1)) hmeas1]
  have hA :
      (∫⁻ c in Set.Iio t1,
          ENNReal.ofReal (1 / 4 : ℝ) *
            ENNReal.ofReal ((c : ℝ) * ((t1 : ℝ) - (c : ℝ))) ∂μ) =
        ENNReal.ofReal (1 / 4 : ℝ) *
          (∫⁻ c in Set.Iio t1,
              ENNReal.ofReal ((c : ℝ) * ((t1 : ℝ) - (c : ℝ))) ∂μ) := by
    have mc :
        Measurable fun c : Rand => ENNReal.ofReal ((c : ℝ) * ((t1 : ℝ) - (c : ℝ))) := by
      exact
        ENNReal.measurable_ofReal.comp
          ((measurable_subtype_coe).mul (measurable_const.sub measurable_subtype_coe))
    simpa using
      (MeasureTheory.lintegral_const_mul (μ := μ.restrict (Set.Iio t1))
        (r := ENNReal.ofReal (1 / 4 : ℝ)) mc)
  have hB :
      (∫⁻ c in Set.Iio t1,
          ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal ((t1 : ℝ) - (c : ℝ)) ∂μ) =
        ENNReal.ofReal (3 / 8 : ℝ) *
          (∫⁻ c in Set.Iio t1, ENNReal.ofReal ((t1 : ℝ) - (c : ℝ)) ∂μ) := by
    have mc : Measurable fun c : Rand => ENNReal.ofReal ((t1 : ℝ) - (c : ℝ)) := by
      exact ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_subtype_coe)
    simpa using
      (MeasureTheory.lintegral_const_mul (μ := μ.restrict (Set.Iio t1))
        (r := ENNReal.ofReal (3 / 8 : ℝ)) mc)
  rw [hA, hB, hmul_int, hsub_int]
  have h1 :
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (9 / 1024 : ℝ) =
        ENNReal.ofReal (9 / 4096 : ℝ) := by
    have hmul :
        ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (9 / 1024 : ℝ) =
          ENNReal.ofReal ((1 / 4 : ℝ) * (9 / 1024 : ℝ)) := by
      exact
        (ENNReal.ofReal_mul (p := (1 / 4 : ℝ)) (q := (9 / 1024 : ℝ)) ha0).symm
    have hr : (1 / 4 : ℝ) * (9 / 1024 : ℝ) = (9 / 4096 : ℝ) := by norm_num
    calc
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (9 / 1024 : ℝ) =
          ENNReal.ofReal ((1 / 4 : ℝ) * (9 / 1024 : ℝ)) := hmul
      _ = ENNReal.ofReal (9 / 4096 : ℝ) := by rw [hr]
  have h2 :
      ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal (9 / 128 : ℝ) =
        ENNReal.ofReal (27 / 1024 : ℝ) := by
    have hmul :
        ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal (9 / 128 : ℝ) =
          ENNReal.ofReal ((3 / 8 : ℝ) * (9 / 128 : ℝ)) := by
      exact
        (ENNReal.ofReal_mul (p := (3 / 8 : ℝ)) (q := (9 / 128 : ℝ)) hb0).symm
    have hr : (3 / 8 : ℝ) * (9 / 128 : ℝ) = (27 / 1024 : ℝ) := by norm_num
    calc
      ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal (9 / 128 : ℝ) =
          ENNReal.ofReal ((3 / 8 : ℝ) * (9 / 128 : ℝ)) := hmul
      _ = ENNReal.ofReal (27 / 1024 : ℝ) := by rw [hr]
  have hsum :
      ENNReal.ofReal (9 / 4096 : ℝ) + ENNReal.ofReal (27 / 1024 : ℝ) =
        ENNReal.ofReal (117 / 4096 : ℝ) := by
    have h9 : 0 ≤ (9 / 4096 : ℝ) := by norm_num
    have h27 : 0 ≤ (27 / 1024 : ℝ) := by norm_num
    have : (9 / 4096 : ℝ) + (27 / 1024 : ℝ) = (117 / 4096 : ℝ) := by norm_num
    simpa [this] using (ENNReal.ofReal_add h9 h27).symm
  rw [h1, h2]
  exact hsum

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
      simp [t1, t]
      norm_num
    simpa [hr] using h
  have hsub_int :
      (∫⁻ b in Set.Iio t1, ENNReal.ofReal ((t : ℝ) - (b : ℝ)) ∂(volume : Measure Rand)) =
          ENNReal.ofReal (21 / 128 : ℝ) := by
    have h :=
      (setLIntegral_ofReal_sub_id_Iio (r := t) (b := t1) (hbr := ht1))
    have hr : ((t : ℝ) * (t1 : ℝ) - (t1 : ℝ) ^ 2 / 2) = (21 / 128 : ℝ) := by
      simp [t1, t]
      norm_num
    simpa [hr] using h
  have hrewrite :
      (fun b : Rand => gTB b * μ (Set.Ico b t)) =
        fun b : Rand =>
          ENNReal.ofReal (1 / 4 : ℝ) *
              ENNReal.ofReal ((b : ℝ) * ((t : ℝ) - (b : ℝ))) +
            ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal ((t : ℝ) - (b : ℝ)) := by
    funext b
    have hb0' : 0 ≤ (b : ℝ) := b.property.1
    have hprod :
        ENNReal.ofReal (b : ℝ) * ENNReal.ofReal ((t : ℝ) - (b : ℝ)) =
          ENNReal.ofReal ((b : ℝ) * ((t : ℝ) - (b : ℝ))) := by
      simpa using (ENNReal.ofReal_mul hb0').symm
    simp [μ, gTB_eq_affine, add_mul, mul_assoc, hprod]
  rw [hrewrite]
  have hmeas1 :
      Measurable fun b : Rand =>
        ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal ((b : ℝ) * ((t : ℝ) - (b : ℝ))) := by
    have mb : Measurable fun b : Rand => (b : ℝ) := measurable_subtype_coe
    have mpoly : Measurable fun b : Rand => (b : ℝ) * ((t : ℝ) - (b : ℝ)) :=
      mb.mul (measurable_const.sub mb)
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp mpoly)
  rw [MeasureTheory.lintegral_add_left (μ := μ.restrict (Set.Iio t1)) hmeas1]
  have hA :
      (∫⁻ b in Set.Iio t1,
          ENNReal.ofReal (1 / 4 : ℝ) *
            ENNReal.ofReal ((b : ℝ) * ((t : ℝ) - (b : ℝ))) ∂μ) =
        ENNReal.ofReal (1 / 4 : ℝ) *
          (∫⁻ b in Set.Iio t1,
              ENNReal.ofReal ((b : ℝ) * ((t : ℝ) - (b : ℝ))) ∂μ) := by
    have mb :
        Measurable fun b : Rand => ENNReal.ofReal ((b : ℝ) * ((t : ℝ) - (b : ℝ))) := by
      exact
        ENNReal.measurable_ofReal.comp
          ((measurable_subtype_coe).mul (measurable_const.sub measurable_subtype_coe))
    simpa using
      (MeasureTheory.lintegral_const_mul (μ := μ.restrict (Set.Iio t1))
        (r := ENNReal.ofReal (1 / 4 : ℝ)) mb)
  have hB :
      (∫⁻ b in Set.Iio t1,
          ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal ((t : ℝ) - (b : ℝ)) ∂μ) =
        ENNReal.ofReal (3 / 8 : ℝ) *
          (∫⁻ b in Set.Iio t1, ENNReal.ofReal ((t : ℝ) - (b : ℝ)) ∂μ) := by
    have mb : Measurable fun b : Rand => ENNReal.ofReal ((t : ℝ) - (b : ℝ)) := by
      exact ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_subtype_coe)
    simpa using
      (MeasureTheory.lintegral_const_mul (μ := μ.restrict (Set.Iio t1))
        (r := ENNReal.ofReal (3 / 8 : ℝ)) mb)
  rw [hA, hB, hmul_int, hsub_int]
  have h1 :
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (27 / 1024 : ℝ) =
        ENNReal.ofReal (27 / 4096 : ℝ) := by
    have hmul :
        ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (27 / 1024 : ℝ) =
          ENNReal.ofReal ((1 / 4 : ℝ) * (27 / 1024 : ℝ)) := by
      exact
        (ENNReal.ofReal_mul (p := (1 / 4 : ℝ)) (q := (27 / 1024 : ℝ)) ha0).symm
    have hr : (1 / 4 : ℝ) * (27 / 1024 : ℝ) = (27 / 4096 : ℝ) := by norm_num
    calc
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (27 / 1024 : ℝ) =
          ENNReal.ofReal ((1 / 4 : ℝ) * (27 / 1024 : ℝ)) := hmul
      _ = ENNReal.ofReal (27 / 4096 : ℝ) := by rw [hr]
  have h2 :
      ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal (21 / 128 : ℝ) =
        ENNReal.ofReal (63 / 1024 : ℝ) := by
    have hmul :
        ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal (21 / 128 : ℝ) =
          ENNReal.ofReal ((3 / 8 : ℝ) * (21 / 128 : ℝ)) := by
      exact
        (ENNReal.ofReal_mul (p := (3 / 8 : ℝ)) (q := (21 / 128 : ℝ)) hb0).symm
    have hr : (3 / 8 : ℝ) * (21 / 128 : ℝ) = (63 / 1024 : ℝ) := by norm_num
    calc
      ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal (21 / 128 : ℝ) =
          ENNReal.ofReal ((3 / 8 : ℝ) * (21 / 128 : ℝ)) := hmul
      _ = ENNReal.ofReal (63 / 1024 : ℝ) := by rw [hr]
  have hsum :
      ENNReal.ofReal (27 / 4096 : ℝ) + ENNReal.ofReal (63 / 1024 : ℝ) =
        ENNReal.ofReal (279 / 4096 : ℝ) := by
    have h27 : 0 ≤ (27 / 4096 : ℝ) := by norm_num
    have h63 : 0 ≤ (63 / 1024 : ℝ) := by norm_num
    have : (27 / 4096 : ℝ) + (63 / 1024 : ℝ) = (279 / 4096 : ℝ) := by norm_num
    simpa [this] using (ENNReal.ofReal_add h27 h63).symm
  rw [h1, h2]
  exact hsum

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
  have hmeasTB : Measurable fun b : Rand => gTB b * μ (Set.Ico b t) := by
    have mb : Measurable fun b : Rand => (b : ℝ) := measurable_subtype_coe
    have m_ofReal_b : Measurable fun b : Rand => ENNReal.ofReal (b : ℝ) :=
      ENNReal.measurable_ofReal.comp mb
    have m_ofReal_sub : Measurable fun b : Rand => ENNReal.ofReal ((t : ℝ) - (b : ℝ)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.sub mb)
    have m_gTB_expr :
        Measurable fun b : Rand =>
          ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (b : ℝ) + ENNReal.ofReal (3 / 8 : ℝ) := by
      exact (measurable_const.mul m_ofReal_b).add measurable_const
    have hfun :
        (fun b : Rand => gTB b) =
          fun b : Rand =>
            ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (b : ℝ) + ENNReal.ofReal (3 / 8 : ℝ) := by
      funext b
      simp [gTB_eq_affine]
    -- `μ (Ico b t)` is the interval length `t - b` (as an `ofReal`).
    simpa [μ, hfun] using m_gTB_expr.mul m_ofReal_sub
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
  have hsum :
      ENNReal.ofReal (279 / 4096 : ℝ) + ENNReal.ofReal (117 / 4096 : ℝ) =
        ENNReal.ofReal (99 / 1024 : ℝ) := by
    have h279 : 0 ≤ (279 / 4096 : ℝ) := by norm_num
    have h117 : 0 ≤ (117 / 4096 : ℝ) := by norm_num
    have : (279 / 4096 : ℝ) + (117 / 4096 : ℝ) = (99 / 1024 : ℝ) := by norm_num
    simpa [this] using (ENNReal.ofReal_add h279 h117).symm
  rw [hTB_val, htri_val]
  exact hsum

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
    MeasureTheory.lintegral_inter_add_diff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio (1 : Rand) : Set Rand)) (B := (Set.Iio t : Set Rand)) htmeas
  have hAint : ((Set.Iio (1 : Rand) : Set Rand) ∩ Set.Iio t) = Set.Iio t := by
    ext c
    constructor
    · intro hc
      exact hc.2
    · intro hc
      have hc1 : (c : ℝ) < 1 := lt_trans (show (c : ℝ) < t from hc) t_lt_one
      exact ⟨by simpa using hc1, hc⟩
  have hAdiff : ((Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t) = Set.Ico t (1 : Rand) := by
    ext c
    constructor
    · rintro ⟨hc1, hct⟩
      exact ⟨le_of_not_gt hct, hc1⟩
    · intro hc
      exact ⟨hc.2, not_lt_of_ge hc.1⟩
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
    MeasureTheory.lintegral_inter_add_diff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio t : Set Rand)) (B := (Set.Iio t2 : Set Rand)) ht2meas
  have hBint : (Set.Iio t ∩ Set.Iio t2 : Set Rand) = Set.Iio t2 := by
    ext c
    constructor
    · intro hc
      exact hc.2
    · intro hc
      exact ⟨lt_trans hc t2_lt_t, hc⟩
  have hBdiff : (Set.Iio t \ Set.Iio t2 : Set Rand) = Set.Ico t2 t := by
    ext c
    constructor
    · rintro ⟨hct, hc2⟩
      exact ⟨le_of_not_gt hc2, hct⟩
    · intro hc
      exact ⟨hc.2, not_lt_of_ge hc.1⟩
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
    MeasureTheory.lintegral_inter_add_diff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio t2 : Set Rand)) (B := (Set.Iio t1 : Set Rand)) ht1meas
  have hCint : (Set.Iio t2 ∩ Set.Iio t1 : Set Rand) = Set.Iio t1 := by
    ext c
    constructor
    · intro hc
      exact hc.2
    · intro hc
      exact ⟨lt_trans hc t1_lt_t2, hc⟩
  have hCdiff : (Set.Iio t2 \ Set.Iio t1 : Set Rand) = Set.Ico t1 t2 := by
    ext c
    constructor
    · rintro ⟨hc2, hc1⟩
      exact ⟨le_of_not_gt hc1, hc2⟩
    · intro hc
      exact ⟨hc.2, not_lt_of_ge hc.1⟩
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
    MeasureTheory.lintegral_inter_add_diff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Ico t1 t2 : Set Rand)) (B := (Set.Iio b : Set Rand)) hbmeas
  have hDint : (Set.Ico t1 t2 ∩ Set.Iio b : Set Rand) = Set.Ico t1 b := by
    ext c
    constructor
    · rintro ⟨hcA, hcb⟩
      exact ⟨hcA.1, hcb⟩
    · intro hc
      refine ⟨?_, hc.2⟩
      exact ⟨hc.1, lt_trans hc.2 hb2⟩
  have hDdiff : (Set.Ico t1 t2 \ Set.Iio b : Set Rand) = Set.Ico b t2 := by
    ext c
    constructor
    · rintro ⟨hcA, hcb⟩
      exact ⟨le_of_not_gt hcb, hcA.2⟩
    · intro hc
      refine ⟨?_, not_lt_of_ge hc.1⟩
      exact ⟨le_trans hb1 hc.1, hc.2⟩
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
          ∫⁻ _c in Set.Ico b t2, gT2B b ∂μ := by
            exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs' hEq
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
  have ha0 : 0 ≤ (1 / 16 : ℝ) := by
    norm_num
  have hb0 : 0 ≤ (15 / 32 : ℝ) := by
    norm_num
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
      simp [t1, t2]
      norm_num
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
      simp [t1, t2]
      norm_num
    simpa [μ, hr] using h
  have hrewrite :
      (fun x : Rand => gT2B x * μ (Set.Ico x t2)) =
        fun x : Rand =>
          ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal ((x : ℝ) * ((t2 : ℝ) - x)) +
            ENNReal.ofReal (15 / 32 : ℝ) * ENNReal.ofReal ((t2 : ℝ) - x) := by
    funext x
    have hx0 : 0 ≤ (x : ℝ) := x.property.1
    have hprod :
        ENNReal.ofReal (x : ℝ) * ENNReal.ofReal ((t2 : ℝ) - x) =
          ENNReal.ofReal ((x : ℝ) * ((t2 : ℝ) - x)) := by
      simpa using (ENNReal.ofReal_mul hx0).symm
    simp [μ, gT2B_eq_affine, add_mul, mul_assoc, hprod]
  rw [hrewrite]
  have hmeas1 :
      Measurable fun x : Rand =>
        ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal ((x : ℝ) * ((t2 : ℝ) - x)) := by
    have mx : Measurable fun x : Rand => (x : ℝ) := measurable_subtype_coe
    have mpoly : Measurable fun x : Rand => (x : ℝ) * ((t2 : ℝ) - x) :=
      mx.mul (measurable_const.sub mx)
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp mpoly)
  rw [MeasureTheory.lintegral_add_left (μ := μ.restrict (Set.Ico t1 t2)) hmeas1]
  have hA :
      (∫⁻ x in Set.Ico t1 t2,
          ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal ((x : ℝ) * ((t2 : ℝ) - x)) ∂μ) =
        ENNReal.ofReal (1 / 16 : ℝ) *
          (∫⁻ x in Set.Ico t1 t2,
              ENNReal.ofReal ((x : ℝ) * ((t2 : ℝ) - x)) ∂μ) := by
    have mx :
        Measurable fun x : Rand => ENNReal.ofReal ((x : ℝ) * ((t2 : ℝ) - x)) := by
      exact
        ENNReal.measurable_ofReal.comp
          ((measurable_subtype_coe).mul (measurable_const.sub measurable_subtype_coe))
    simpa using
      (MeasureTheory.lintegral_const_mul (μ := μ.restrict (Set.Ico t1 t2))
        (r := ENNReal.ofReal (1 / 16 : ℝ)) mx)
  have hB :
      (∫⁻ x in Set.Ico t1 t2,
          ENNReal.ofReal (15 / 32 : ℝ) * ENNReal.ofReal ((t2 : ℝ) - x) ∂μ) =
        ENNReal.ofReal (15 / 32 : ℝ) *
          (∫⁻ x in Set.Ico t1 t2, ENNReal.ofReal ((t2 : ℝ) - x) ∂μ) := by
    have mx : Measurable fun x : Rand => ENNReal.ofReal ((t2 : ℝ) - x) := by
      exact ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_subtype_coe)
    simpa using
      (MeasureTheory.lintegral_const_mul (μ := μ.restrict (Set.Ico t1 t2))
        (r := ENNReal.ofReal (15 / 32 : ℝ)) mx)
  rw [hA, hB, hpoly1, hpoly2]
  have h1 :
      ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (1025 / 196608 : ℝ) =
        ENNReal.ofReal (1025 / 3145728 : ℝ) := by
    have hmul :
        ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (1025 / 196608 : ℝ) =
          ENNReal.ofReal ((1 / 16 : ℝ) * (1025 / 196608 : ℝ)) := by
      exact
        (ENNReal.ofReal_mul (p := (1 / 16 : ℝ)) (q := (1025 / 196608 : ℝ)) ha0).symm
    have hr : (1 / 16 : ℝ) * (1025 / 196608 : ℝ) = (1025 / 3145728 : ℝ) := by norm_num
    calc
      ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (1025 / 196608 : ℝ) =
          ENNReal.ofReal ((1 / 16 : ℝ) * (1025 / 196608 : ℝ)) := hmul
      _ = ENNReal.ofReal (1025 / 3145728 : ℝ) := by rw [hr]
  have h2 :
      ENNReal.ofReal (15 / 32 : ℝ) * ENNReal.ofReal (25 / 2048 : ℝ) =
        ENNReal.ofReal (18000 / 3145728 : ℝ) := by
    have hmul :
        ENNReal.ofReal (15 / 32 : ℝ) * ENNReal.ofReal (25 / 2048 : ℝ) =
          ENNReal.ofReal ((15 / 32 : ℝ) * (25 / 2048 : ℝ)) := by
      exact
        (ENNReal.ofReal_mul (p := (15 / 32 : ℝ)) (q := (25 / 2048 : ℝ)) hb0).symm
    have hr : (15 / 32 : ℝ) * (25 / 2048 : ℝ) = (18000 / 3145728 : ℝ) := by norm_num
    calc
      ENNReal.ofReal (15 / 32 : ℝ) * ENNReal.ofReal (25 / 2048 : ℝ) =
          ENNReal.ofReal ((15 / 32 : ℝ) * (25 / 2048 : ℝ)) := hmul
      _ = ENNReal.ofReal (18000 / 3145728 : ℝ) := by rw [hr]
  have hsum :
      ENNReal.ofReal (1025 / 3145728 : ℝ) + ENNReal.ofReal (18000 / 3145728 : ℝ) =
        ENNReal.ofReal (19025 / 3145728 : ℝ) := by
    have h1' : 0 ≤ (1025 / 3145728 : ℝ) := by norm_num
    have h2' : 0 ≤ (18000 / 3145728 : ℝ) := by norm_num
    have : (1025 / 3145728 : ℝ) + (18000 / 3145728 : ℝ) = (19025 / 3145728 : ℝ) := by norm_num
    simpa [this] using (ENNReal.ofReal_add h1' h2').symm
  rw [h1, h2]
  exact hsum

private lemma lintegral_gCt2_triangle_t1_t2_value :
    (∫⁻ b in Set.Ico t1 t2, ∫⁻ c in Set.Ico t1 b, gCt2 c ∂μ ∂μ) =
      ENNReal.ofReal (19025 / 3145728 : ℝ)
:= by
  -- Use the indicator trick and the `Iio` triangle swap.
  let f : Rand → ℝ≥0∞ := (Set.Ici t1).indicator gCt2
  have hf : Measurable f := by
    have hg : Measurable gCt2 := by
      have mc : Measurable fun c : Rand => (c : ℝ) := measurable_subtype_coe
      have m_ofReal_c : Measurable fun c : Rand => ENNReal.ofReal (c : ℝ) :=
        ENNReal.measurable_ofReal.comp mc
      have m_expr :
          Measurable fun c : Rand =>
            ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (c : ℝ) +
              ENNReal.ofReal (15 / 32 : ℝ) := by
        exact (measurable_const.mul m_ofReal_c).add measurable_const
      have hfun :
          (fun c : Rand => gCt2 c) =
            fun c : Rand =>
              ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (c : ℝ) +
                ENNReal.ofReal (15 / 32 : ℝ) := by
        funext c
        simp [gCt2_eq_affine]
      simpa [hfun] using m_expr
    simpa [f] using hg.indicator (by simp)
  have htriIio := lintegral_triangle_Iio (B := t2) (f := f) hf
  -- Reduce the `b`-domain from `Iio t2` to `Ico t1 t2` by splitting at `t1`.
  have ht1meas : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
  have hsplitb :=
    MeasureTheory.lintegral_inter_add_diff (μ := μ)
      (f := fun b : Rand => ∫⁻ c in Set.Iio b, f c ∂μ)
      (A := (Set.Iio t2 : Set Rand)) (B := (Set.Iio t1 : Set Rand)) ht1meas
  have hBint : (Set.Iio t2 ∩ Set.Iio t1 : Set Rand) = Set.Iio t1 := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨lt_trans hx t1_lt_t2, hx⟩
  have hBdiff : (Set.Iio t2 \ Set.Iio t1 : Set Rand) = Set.Ico t1 t2 := by
    ext x
    constructor
    · rintro ⟨hx2, hx1⟩
      exact ⟨le_of_not_gt hx1, hx2⟩
    · intro hx
      exact ⟨hx.2, not_lt_of_ge hx.1⟩
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
        have : c ∉ Set.Ici t1 := by
          simpa [Set.mem_Ici] using (not_le_of_gt hct1)
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
      rw [← hset]
      exact hInd
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
  have hμt1t2 : μ (Set.Ico t1 t2) = ENNReal.ofReal (5 / 32 : ℝ) := by
    simp [μ, t1, t2]
    norm_num
  have hμt2t : μ (Set.Ico t2 t) = ENNReal.ofReal (3 / 32 : ℝ) := by
    simp [μ, t2, t]
    norm_num
  -- Split off the rectangle term; the rest is constant.
  have hconst :
      (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t) =
        ENNReal.ofReal (207 / 1024 : ℝ) := by
    have h45 :
        constT1T * μ (Set.Ico t2 t) = ENNReal.ofReal (45 / 1024 : ℝ) := by
      have h15 : 0 ≤ (15 / 32 : ℝ) := by norm_num
      have hmul :
          ENNReal.ofReal (15 / 32 : ℝ) * ENNReal.ofReal (3 / 32 : ℝ) =
            ENNReal.ofReal ((15 / 32 : ℝ) * (3 / 32 : ℝ)) := by
        exact
          (ENNReal.ofReal_mul (p := (15 / 32 : ℝ)) (q := (3 / 32 : ℝ)) h15).symm
      have hr : (15 / 32 : ℝ) * (3 / 32 : ℝ) = (45 / 1024 : ℝ) := by norm_num
      calc
        constT1T * μ (Set.Ico t2 t) =
            ENNReal.ofReal (15 / 32 : ℝ) * ENNReal.ofReal (3 / 32 : ℝ) := by
              simp [constT1T_eq, hμt2t]
        _ = ENNReal.ofReal ((15 / 32 : ℝ) * (3 / 32 : ℝ)) := hmul
        _ = ENNReal.ofReal (45 / 1024 : ℝ) := by rw [hr]
    have h81 : 0 ≤ (81 / 512 : ℝ) := by norm_num
    have h45' : 0 ≤ (45 / 1024 : ℝ) := by norm_num
    have hsum :
        ENNReal.ofReal (81 / 512 : ℝ) + ENNReal.ofReal (45 / 1024 : ℝ) =
          ENNReal.ofReal (207 / 1024 : ℝ) := by
      have : (81 / 512 : ℝ) + (45 / 1024 : ℝ) = (207 / 1024 : ℝ) := by norm_num
      simpa [this] using (ENNReal.ofReal_add h81 h45').symm
    calc
      (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t) =
          ENNReal.ofReal (81 / 512 : ℝ) + constT1T * μ (Set.Ico t2 t) := by
            rw [hConstC]
      _ = ENNReal.ofReal (81 / 512 : ℝ) + ENNReal.ofReal (45 / 1024 : ℝ) := by
            rw [h45]
      _ = ENNReal.ofReal (207 / 1024 : ℝ) := hsum
  -- Integral of the constant part.
  have hconstInt :
      (∫⁻ _b in Set.Ico t1 t2,
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t) ∂μ) =
        ENNReal.ofReal (49680 / 1572864 : ℝ) := by
    have hμ : μ (Set.Ico t1 t2) = ENNReal.ofReal (5 / 32 : ℝ) := hμt1t2
    have h207 : 0 ≤ (207 / 1024 : ℝ) := by norm_num
    have hmul :
        ENNReal.ofReal (207 / 1024 : ℝ) * ENNReal.ofReal (5 / 32 : ℝ) =
          ENNReal.ofReal ((207 / 1024 : ℝ) * (5 / 32 : ℝ)) := by
      exact
        (ENNReal.ofReal_mul (p := (207 / 1024 : ℝ)) (q := (5 / 32 : ℝ)) h207).symm
    have hr : (207 / 1024 : ℝ) * (5 / 32 : ℝ) = (49680 / 1572864 : ℝ) := by norm_num
    calc
      (∫⁻ _b in Set.Ico t1 t2,
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t) ∂μ) =
          ((∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t)) * μ (Set.Ico t1 t2) := by
            simp
      _ = ENNReal.ofReal (207 / 1024 : ℝ) * ENNReal.ofReal (5 / 32 : ℝ) := by
            have hconst' :
                (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t2 t) =
                  ENNReal.ofReal (207 / 1024 : ℝ) := hconst
            rw [hconst', hμ]
      _ = ENNReal.ofReal ((207 / 1024 : ℝ) * (5 / 32 : ℝ)) := hmul
      _ = ENNReal.ofReal (49680 / 1572864 : ℝ) := by rw [hr]
  -- Combine constant and rectangle.
  have hmeasRect : Measurable fun b : Rand => gT2B b * μ (Set.Ico b t2) := by
    -- same as `m_rect` above
    have mb : Measurable fun b : Rand => (b : ℝ) := measurable_subtype_coe
    have m_ofReal_b : Measurable fun b : Rand => ENNReal.ofReal (b : ℝ) :=
      ENNReal.measurable_ofReal.comp mb
    have m_ofReal_sub :
        Measurable fun b : Rand => ENNReal.ofReal ((t2 : ℝ) - (b : ℝ)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.sub mb)
    have m_expr :
        Measurable fun b : Rand =>
          ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (b : ℝ) +
            ENNReal.ofReal (15 / 32 : ℝ) := by
      exact (measurable_const.mul m_ofReal_b).add measurable_const
    have hfun :
        (fun b : Rand => gT2B b) =
          fun b : Rand =>
            ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (b : ℝ) +
              ENNReal.ofReal (15 / 32 : ℝ) := by
      funext b
      simp [gT2B_eq_affine]
    simpa [μ, hfun] using m_expr.mul m_ofReal_sub
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
    have mb : Measurable fun b : Rand => (b : ℝ) := measurable_subtype_coe
    have m_ofReal_b : Measurable fun b : Rand => ENNReal.ofReal (b : ℝ) :=
      ENNReal.measurable_ofReal.comp mb
    have m_ofReal_sub : Measurable fun b : Rand => ENNReal.ofReal ((t2 : ℝ) - (b : ℝ)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.sub mb)
    have m_gT2B :
        Measurable fun b : Rand =>
          ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (b : ℝ) + ENNReal.ofReal (15 / 32 : ℝ) := by
      exact (measurable_const.mul m_ofReal_b).add measurable_const
    have hfun :
        (fun b : Rand => gT2B b) =
          fun b : Rand =>
            ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (b : ℝ) +
              ENNReal.ofReal (15 / 32 : ℝ) := by
      funext b
      simp [gT2B_eq_affine]
    have m_rect : Measurable fun b : Rand => gT2B b * μ (Set.Ico b t2) := by
      simpa [μ, hfun] using m_gT2B.mul m_ofReal_sub
    -- sum with constants
    have m_const : Measurable fun _b : Rand => (∫⁻ c in Set.Iio t1, gCt c ∂μ) := measurable_const
    have m_const2 : Measurable fun _b : Rand => constT1T * μ (Set.Ico t2 t) := measurable_const
    simpa [add_assoc, add_left_comm, add_comm] using (m_const.add (m_rect.add m_const2))
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
    have h19025 : 0 ≤ (19025 / 3145728 : ℝ) := by norm_num
    have h2J :
        ENNReal.ofReal (19025 / 3145728 : ℝ) + ENNReal.ofReal (19025 / 3145728 : ℝ) =
          ENNReal.ofReal (19025 / 1572864 : ℝ) := by
      have : (19025 / 3145728 : ℝ) + (19025 / 3145728 : ℝ) = (19025 / 1572864 : ℝ) := by norm_num
      simpa [this] using (ENNReal.ofReal_add h19025 h19025).symm
    have hsum :
        ENNReal.ofReal (49680 / 1572864 : ℝ) +
            (ENNReal.ofReal (19025 / 3145728 : ℝ) + ENNReal.ofReal (19025 / 3145728 : ℝ)) =
          ENNReal.ofReal (68705 / 1572864 : ℝ) := by
      have h49680 : 0 ≤ (49680 / 1572864 : ℝ) := by norm_num
      have h19025' : 0 ≤ (19025 / 1572864 : ℝ) := by norm_num
      have : (49680 / 1572864 : ℝ) + (19025 / 1572864 : ℝ) = (68705 / 1572864 : ℝ) := by norm_num
      have :
          ENNReal.ofReal (49680 / 1572864 : ℝ) + ENNReal.ofReal (19025 / 1572864 : ℝ) =
            ENNReal.ofReal (68705 / 1572864 : ℝ) := by
        simpa [this] using (ENNReal.ofReal_add h49680 h19025').symm
      simpa [h2J, add_assoc] using this
    simpa [add_assoc, add_left_comm, add_comm] using hsum
  exact htotal

end Recursive3Param
end UpperBound

end Distributed2Coloring
