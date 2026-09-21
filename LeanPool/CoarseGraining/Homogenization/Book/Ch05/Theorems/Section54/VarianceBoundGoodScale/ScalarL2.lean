/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.QuadraticProbeBounds

/-! # Scalar L2 -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Scalar L2 reduction for good-scale probes

This file contains the probabilistic real-variable step used after the
subadditivity positive-part estimate: if the positive excess over the annealed
base is controlled by a small deterministic error plus a centered partition
average, then the full square fluctuation is controlled by the L1 and L2 sizes
of that partition average.
-/

private theorem real_self_eq_posPart_sub_negPart (x : ℝ) :
    x = max x 0 - max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · have hneg : max (-x) 0 = 0 := max_eq_right (by linarith)
    have hpos : max x 0 = x := max_eq_left hx
    simp [hpos, hneg]
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hpos : max x 0 = 0 := max_eq_right hxle
    have hneg : max (-x) 0 = -x := max_eq_left (by linarith)
    simp [hpos, hneg]

private theorem abs_sub_sq_le_two_pos_neg_sq {x base : ℝ} :
    |x - base| ^ (2 : ℕ) ≤
      2 * (max (x - base) 0) ^ (2 : ℕ) +
        2 * (max (base - x) 0) ^ (2 : ℕ) := by
  let u := max (x - base) 0
  let v := max (base - x) 0
  have habs : |x - base| = u + v := by
    by_cases h : base ≤ x
    · have hx : 0 ≤ x - base := sub_nonneg.mpr h
      have hb : base - x ≤ 0 := sub_nonpos.mpr h
      simp [u, v, max_eq_left hx, max_eq_right hb, abs_of_nonneg hx]
    · have hxb : x ≤ base := le_of_not_ge h
      have hx : x - base ≤ 0 := sub_nonpos.mpr hxb
      have hb : 0 ≤ base - x := sub_nonneg.mpr hxb
      simp [u, v, max_eq_right hx, max_eq_left hb, abs_of_nonpos hx]
  rw [habs]
  nlinarith [sq_nonneg (u - v)]

private theorem add_abs_sq_le_two {err z : ℝ} :
    (err + |z|) ^ (2 : ℕ) ≤
      2 * err ^ (2 : ℕ) + 2 * |z| ^ (2 : ℕ) := by
  nlinarith [sq_nonneg (err - |z|)]

private theorem max_sub_zero_abs_le (x base : ℝ) :
    max (x - base) 0 ≤ |x - base| :=
  max_le (le_abs_self _) (abs_nonneg _)

private theorem max_base_sub_zero_abs_le (x base : ℝ) :
    max (base - x) 0 ≤ |x - base| := by
  have h : |base - x| = |x - base| := by rw [abs_sub_comm]
  rw [← h]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- Real/probability L2 reduction for one scalar probe.

The assumptions are intentionally proof-facing and will be supplied internally
for the coordinate and pair probes; the public Section 5.4 theorem does not
expose these measurability or integrability packages. -/
theorem integral_abs_sub_sq_le_of_positivePart_control
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Z : Ω → ℝ} {base err : ℝ}
    (hbase_nonneg : 0 ≤ base) (_herr_nonneg : 0 ≤ err)
    (hX_nonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hmean_lower : base ≤ ∫ ω, X ω ∂μ)
    (hX_int : Integrable X μ)
    (hpos_int : Integrable (fun ω => (max (X ω - base) 0) ^ (2 : ℕ)) μ)
    (hneg_int : Integrable (fun ω => (max (base - X ω) 0) ^ (2 : ℕ)) μ)
    (hpos_one_int : Integrable (fun ω => max (X ω - base) 0) μ)
    (hneg_one_int : Integrable (fun ω => max (base - X ω) 0) μ)
    (hZ_abs_int : Integrable (fun ω => |Z ω|) μ)
    (hZ_sq_int : Integrable (fun ω => |Z ω| ^ (2 : ℕ)) μ)
    (hpos : (fun ω => max (X ω - base) 0) ≤ᵐ[μ] fun ω => err + |Z ω|) :
    ∫ ω, |X ω - base| ^ (2 : ℕ) ∂μ ≤
      4 * err ^ (2 : ℕ) + 4 * ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ +
        2 * base * (err + ∫ ω, |Z ω| ∂μ) := by
  let U : Ω → ℝ := fun ω => max (X ω - base) 0
  let V : Ω → ℝ := fun ω => max (base - X ω) 0
  have hU_nonneg : ∀ ω, 0 ≤ U ω := fun ω => le_max_right _ _
  have hV_nonneg : ∀ ω, 0 ≤ V ω := fun ω => le_max_right _ _
  have hdiff : (fun ω => X ω - base) = fun ω => U ω - V ω := by
    funext ω
    have h := real_self_eq_posPart_sub_negPart (X ω - base)
    simpa [U, V, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hconst_int : Integrable (fun _ : Ω => base) μ := integrable_const base
  have hmean_diff_nonneg : 0 ≤ ∫ ω, X ω - base ∂μ := by
    rw [integral_sub hX_int hconst_int]
    have hconst : (∫ _ω : Ω, base ∂μ) = base := by
      rw [integral_const]
      simp
    rw [hconst]
    linarith
  have hV_le_U_integral : ∫ ω, V ω ∂μ ≤ ∫ ω, U ω ∂μ := by
    have hdiff_int_eq : ∫ ω, X ω - base ∂μ = ∫ ω, U ω - V ω ∂μ := by
      rw [hdiff]
    rw [integral_sub hpos_one_int hneg_one_int] at hdiff_int_eq
    linarith
  have hU_le_err_abs : ∫ ω, U ω ∂μ ≤ err + ∫ ω, |Z ω| ∂μ := by
    have hR_int : Integrable (fun ω => err + |Z ω|) μ :=
      (integrable_const err).add hZ_abs_int
    have hle := integral_mono_ae hpos_one_int hR_int hpos
    calc
      ∫ ω, U ω ∂μ ≤ ∫ ω, err + |Z ω| ∂μ := hle
      _ = err + ∫ ω, |Z ω| ∂μ := by
        rw [integral_add (integrable_const err) hZ_abs_int, integral_const]
        simp
  have hU_sq_le : ∫ ω, U ω ^ (2 : ℕ) ∂μ ≤
      2 * err ^ (2 : ℕ) + 2 * ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ := by
    have hR_sq_int :
        Integrable (fun ω => 2 * err ^ (2 : ℕ) + 2 * |Z ω| ^ (2 : ℕ)) μ :=
      (integrable_const (2 * err ^ (2 : ℕ))).add (hZ_sq_int.const_mul 2)
    have hpoint : (fun ω => U ω ^ (2 : ℕ)) ≤ᵐ[μ]
        fun ω => 2 * err ^ (2 : ℕ) + 2 * |Z ω| ^ (2 : ℕ) := by
      filter_upwards [hpos] with ω hω
      have hsq1 : U ω ^ (2 : ℕ) ≤ (err + |Z ω|) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (hU_nonneg ω) hω 2
      exact hsq1.trans add_abs_sq_le_two
    have hle := integral_mono_ae hpos_int hR_sq_int hpoint
    calc
      ∫ ω, U ω ^ (2 : ℕ) ∂μ ≤
          ∫ ω, 2 * err ^ (2 : ℕ) + 2 * |Z ω| ^ (2 : ℕ) ∂μ := hle
      _ = 2 * err ^ (2 : ℕ) + 2 * ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ := by
        rw [integral_add (integrable_const (2 * err ^ (2 : ℕ)))
          (hZ_sq_int.const_mul 2), integral_const, integral_const_mul]
        simp
  have hV_sq_le : ∫ ω, V ω ^ (2 : ℕ) ∂μ ≤ base * ∫ ω, U ω ∂μ := by
    have hbaseV_int : Integrable (fun ω => base * V ω) μ :=
      hneg_one_int.const_mul base
    have hpoint : (fun ω => V ω ^ (2 : ℕ)) ≤ᵐ[μ] fun ω => base * V ω := by
      filter_upwards [hX_nonneg] with ω hXω
      have hV_le_base : V ω ≤ base := by
        dsimp [V]
        by_cases h : base - X ω ≤ 0
        · rw [max_eq_right h]
          exact hbase_nonneg
        · have hle : max (base - X ω) 0 = base - X ω :=
            max_eq_left (le_of_not_ge h)
          rw [hle]
          linarith
      have hVn := hV_nonneg ω
      nlinarith
    have hle := integral_mono_ae hneg_int hbaseV_int hpoint
    calc
      ∫ ω, V ω ^ (2 : ℕ) ∂μ ≤ ∫ ω, base * V ω ∂μ := hle
      _ = base * ∫ ω, V ω ∂μ := by rw [integral_const_mul]
      _ ≤ base * ∫ ω, U ω ∂μ :=
        mul_le_mul_of_nonneg_left hV_le_U_integral hbase_nonneg
  have hsquare : ∫ ω, |X ω - base| ^ (2 : ℕ) ∂μ ≤
      2 * ∫ ω, U ω ^ (2 : ℕ) ∂μ + 2 * ∫ ω, V ω ^ (2 : ℕ) ∂μ := by
    have hR_int : Integrable (fun ω => 2 * U ω ^ (2 : ℕ) +
        2 * V ω ^ (2 : ℕ)) μ :=
      (hpos_int.const_mul 2).add (hneg_int.const_mul 2)
    have hleft_int : Integrable (fun ω => |X ω - base| ^ (2 : ℕ)) μ := by
      refine Integrable.mono' hR_int ?_ ?_
      · exact (((hX_int.aemeasurable.sub aemeasurable_const).norm.pow_const
          (2 : ℕ)).aestronglyMeasurable)
      · filter_upwards with ω
        have hle := abs_sub_sq_le_two_pos_neg_sq (x := X ω) (base := base)
        simpa [U, V, Real.norm_eq_abs] using hle
    have hpoint : (fun ω => |X ω - base| ^ (2 : ℕ)) ≤ᵐ[μ]
        fun ω => 2 * U ω ^ (2 : ℕ) + 2 * V ω ^ (2 : ℕ) := by
      filter_upwards with ω
      exact abs_sub_sq_le_two_pos_neg_sq (x := X ω) (base := base)
    have hle := integral_mono_ae hleft_int hR_int hpoint
    calc
      ∫ ω, |X ω - base| ^ (2 : ℕ) ∂μ ≤
          ∫ ω, 2 * U ω ^ (2 : ℕ) + 2 * V ω ^ (2 : ℕ) ∂μ := hle
      _ = 2 * ∫ ω, U ω ^ (2 : ℕ) ∂μ +
          2 * ∫ ω, V ω ^ (2 : ℕ) ∂μ := by
        rw [integral_add (hpos_int.const_mul 2) (hneg_int.const_mul 2),
          integral_const_mul, integral_const_mul]
  calc
    ∫ ω, |X ω - base| ^ (2 : ℕ) ∂μ
        ≤ 2 * ∫ ω, U ω ^ (2 : ℕ) ∂μ +
            2 * ∫ ω, V ω ^ (2 : ℕ) ∂μ := hsquare
    _ ≤ 2 * (2 * err ^ (2 : ℕ) + 2 * ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ) +
          2 * (base * ∫ ω, U ω ∂μ) := by nlinarith [hU_sq_le, hV_sq_le]
    _ ≤ 2 * (2 * err ^ (2 : ℕ) + 2 * ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ) +
          2 * (base * (err + ∫ ω, |Z ω| ∂μ)) := by
            nlinarith [hU_le_err_abs, hbase_nonneg]
    _ = 4 * err ^ (2 : ℕ) + 4 * ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ +
        2 * base * (err + ∫ ω, |Z ω| ∂μ) := by ring

/-- A caller-friendly version of
`integral_abs_sub_sq_le_of_positivePart_control`, deriving the positive and
negative part integrability facts from centered L1/L2 integrability. -/
theorem integral_abs_sub_sq_le_of_positivePart_control_of_centered_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Z : Ω → ℝ} {base err : ℝ}
    (hbase_nonneg : 0 ≤ base) (herr_nonneg : 0 ≤ err)
    (hX_nonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hmean_lower : base ≤ ∫ ω, X ω ∂μ)
    (hX_int : Integrable X μ)
    (hcenter_abs_int : Integrable (fun ω => |X ω - base|) μ)
    (hcenter_sq_int : Integrable (fun ω => |X ω - base| ^ (2 : ℕ)) μ)
    (hZ_abs_int : Integrable (fun ω => |Z ω|) μ)
    (hZ_sq_int : Integrable (fun ω => |Z ω| ^ (2 : ℕ)) μ)
    (hpos : (fun ω => max (X ω - base) 0) ≤ᵐ[μ] fun ω => err + |Z ω|) :
    ∫ ω, |X ω - base| ^ (2 : ℕ) ∂μ ≤
      4 * err ^ (2 : ℕ) + 4 * ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ +
        2 * base * (err + ∫ ω, |Z ω| ∂μ) := by
  have hX_aemeas : AEMeasurable X μ := hX_int.aemeasurable
  have hpos_one_int : Integrable (fun ω => max (X ω - base) 0) μ := by
    refine Integrable.mono' hcenter_abs_int ?_ ?_
    · exact
        ((hX_aemeas.sub aemeasurable_const).max aemeasurable_const).aestronglyMeasurable
    · filter_upwards with ω
      have hle := max_sub_zero_abs_le (X ω) base
      simpa [Real.norm_eq_abs, abs_of_nonneg (le_max_right (X ω - base) 0)] using hle
  have hneg_one_int : Integrable (fun ω => max (base - X ω) 0) μ := by
    refine Integrable.mono' hcenter_abs_int ?_ ?_
    · exact
        ((aemeasurable_const.sub hX_aemeas).max aemeasurable_const).aestronglyMeasurable
    · filter_upwards with ω
      have hle := max_base_sub_zero_abs_le (X ω) base
      simpa [Real.norm_eq_abs, abs_of_nonneg (le_max_right (base - X ω) 0)] using hle
  have hpos_int : Integrable (fun ω => (max (X ω - base) 0) ^ (2 : ℕ)) μ := by
    refine Integrable.mono' hcenter_sq_int ?_ ?_
    · exact
        (((hX_aemeas.sub aemeasurable_const).max aemeasurable_const).pow_const
          (2 : ℕ)).aestronglyMeasurable
    · filter_upwards with ω
      have hle := max_sub_zero_abs_le (X ω) base
      have hsq := pow_le_pow_left₀ (le_max_right (X ω - base) 0) hle 2
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (le_max_right (X ω - base) 0) (2 : ℕ)),
        abs_of_nonneg (pow_nonneg (abs_nonneg (X ω - base)) (2 : ℕ))] using hsq
  have hneg_int : Integrable (fun ω => (max (base - X ω) 0) ^ (2 : ℕ)) μ := by
    refine Integrable.mono' hcenter_sq_int ?_ ?_
    · exact
        (((aemeasurable_const.sub hX_aemeas).max aemeasurable_const).pow_const
          (2 : ℕ)).aestronglyMeasurable
    · filter_upwards with ω
      have hle := max_base_sub_zero_abs_le (X ω) base
      have hsq := pow_le_pow_left₀ (le_max_right (base - X ω) 0) hle 2
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (le_max_right (base - X ω) 0) (2 : ℕ)),
        abs_of_nonneg (pow_nonneg (abs_nonneg (X ω - base)) (2 : ℕ))] using hsq
  exact
    integral_abs_sub_sq_le_of_positivePart_control hbase_nonneg herr_nonneg hX_nonneg
      hmean_lower hX_int hpos_int hneg_int hpos_one_int hneg_one_int
      hZ_abs_int hZ_sq_int hpos

/-- Convert the Rosenthal `L^ξ` root estimate, with `ξ ≥ 2`, into the L1 and
L2 estimates used by `integral_abs_sub_sq_le_of_positivePart_control`. -/
theorem integral_abs_and_sq_le_of_annealedMomentRoot_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : ℕ} {Z : Ω → ℝ} {K : ℝ}
    (hξ : 2 ≤ ξ)
    (hZ_aemeas : AEMeasurable Z μ)
    (hZξ_int : Integrable (fun ω => |Z ω| ^ ξ) μ)
    (hroot : (∫ ω, |Z ω| ^ ξ ∂μ) ^ (1 / (ξ : ℝ)) ≤ K) :
    (∫ ω, |Z ω| ∂μ ≤ K) ∧
      (∫ ω, |Z ω| ^ (2 : ℕ) ∂μ ≤ K ^ (2 : ℕ)) := by
  have hξ_ne_zero : ξ ≠ 0 := by omega
  have hmemξ : MemLp Z (ξ : ENNReal) μ := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hZ_aemeas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hZξ_int
  have hmem2 : MemLp Z (2 : ENNReal) μ :=
    hmemξ.mono_exponent (by exact_mod_cast hξ)
  have hZ2_int : Integrable (fun ω => |Z ω| ^ (2 : ℕ)) μ := by
    simpa [Real.norm_eq_abs] using
      hmem2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hroot2 :
      (∫ ω, |Z ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) ≤ K :=
    (Homogenization.integral_abs_sq_rpow_half_le_integral_abs_pow_rpow_inv_aemeasurable
      (μ := μ) (f := Z) hξ hZ_aemeas hZξ_int).trans hroot
  have hL1 : ∫ ω, |Z ω| ∂μ ≤ K :=
    (Homogenization.integral_abs_le_integral_abs_sq_rpow_half_aemeasurable
      (μ := μ) (f := Z) hZ_aemeas hZ2_int).trans hroot2
  have hI_nonneg : 0 ≤ ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ :=
    integral_nonneg fun ω => pow_nonneg (abs_nonneg (Z ω)) (2 : ℕ)
  have hroot2_nonneg :
      0 ≤ (∫ ω, |Z ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) := by
    positivity
  have hsq := pow_le_pow_left₀ hroot2_nonneg hroot2 2
  have hroot_sq :
      ((∫ ω, |Z ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℕ) =
        ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hI_nonneg]
  have hL2 : ∫ ω, |Z ω| ^ (2 : ℕ) ∂μ ≤ K ^ (2 : ℕ) := by
    rw [hroot_sq] at hsq
    simpa using hsq
  exact ⟨hL1, hL2⟩

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
