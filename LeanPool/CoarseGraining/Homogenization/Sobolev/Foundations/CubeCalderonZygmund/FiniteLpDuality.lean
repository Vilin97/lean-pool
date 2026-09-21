/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.H10Adjoint

/-!
# Finite-exponent duality support for cube Calderón--Zygmund estimates

This file contains the measure-theoretic support for the `1 < q < 2` duality
step.  It deliberately does not state a Calderón--Zygmund estimate: it only
packages the radial truncations, Hölder pairing, and monotone-convergence
facts that will be consumed once the supplied-solution `q > 2` estimate is
available.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund
namespace INTERNAL

/-- If a finite exponent lies strictly between one and two, its finite Hölder
conjugate is strictly bigger than two. -/
theorem conjugate_toReal_gt_two_of_lt_two (q : FiniteLpExponent)
    (hq : q.exponent.toReal < 2) :
    2 < q.conjugate.exponent.toReal := by
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  have hq1 : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hreal : q.exponent.toReal.HolderConjugate q.conjugate.exponent.toReal :=
    ENNReal.HolderConjugate.toReal hq1
  rw [hreal.conjugate_eq]
  apply (lt_div_iff₀ (sub_pos.mpr hq1)).2
  nlinarith

/-- The bounded radial test field used in the `q < 2` duality argument.  The
cutoff is by the Euclidean Hilbert norm, so the field remains a valid datum for
the `H¹₀` adjoint solver. -/
def hilbertRadialTruncation {α : Type*} {d : ℕ} (q : ℝ) (n : ℕ)
    (F : α → HilbertVec d) : α → HilbertVec d :=
  Set.indicator {x | ‖F x‖ ≤ (n : ℝ)} (fun x => ‖F x‖ ^ (q - 2) • F x)

/-- The algebraic-vector spelling of `hilbertRadialTruncation`, suitable for
the divergence solver API. -/
def vectorRadialTruncation {α : Type*} {d : ℕ} (q : ℝ) (n : ℕ)
    (F : α → Vec d) : α → Vec d :=
  fun x => (hilbertRadialTruncation q n (fun y => HilbertVec.ofVec (F y)) x).toVec

private theorem nullMeasurableSet_norm_le {α : Type*} {d : ℕ}
    [MeasurableSpace α] {μ : Measure α} {F : α → HilbertVec d}
    (hF : AEStronglyMeasurable F μ) (n : ℕ) :
    NullMeasurableSet {x | ‖F x‖ ≤ (n : ℝ)} μ := by
  change NullMeasurableSet ((fun x => ‖F x‖) ⁻¹' Set.Iic (n : ℝ)) μ
  exact hF.norm.aemeasurable.nullMeasurableSet_preimage measurableSet_Iic

/-- The radial truncation is a.e. strongly measurable. -/
theorem aestronglyMeasurable_hilbertRadialTruncation {α : Type*} {d : ℕ}
    [MeasurableSpace α] {μ : Measure α} {q : ℝ} {n : ℕ}
    {F : α → HilbertVec d} (hF : AEStronglyMeasurable F μ) :
    AEStronglyMeasurable (hilbertRadialTruncation q n F) μ := by
  apply AEStronglyMeasurable.indicator₀
  · exact (hF.norm.aemeasurable.pow_const (q - 2)).aestronglyMeasurable.smul hF
  · exact nullMeasurableSet_norm_le hF n

/-- Pointwise Euclidean norm identity for the bounded radial test field. -/
theorem norm_hilbertRadialTruncation {α : Type*} {d : ℕ} {q : ℝ}
    (hq : 1 < q) (n : ℕ) (F : α → HilbertVec d) (x : α) :
    ‖hilbertRadialTruncation q n F x‖ =
      if ‖F x‖ ≤ (n : ℝ) then ‖F x‖ ^ (q - 1) else 0 := by
  by_cases hx : ‖F x‖ ≤ (n : ℝ)
  · rw [show hilbertRadialTruncation q n F x =
        ‖F x‖ ^ (q - 2) • F x by
      simp [hilbertRadialTruncation, hx]]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    simp only [if_pos hx]
    calc
      ‖F x‖ ^ (q - 2) * ‖F x‖ =
          ‖F x‖ ^ (q - 2) * ‖F x‖ ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = ‖F x‖ ^ ((q - 2) + 1) :=
        (Real.rpow_add' (norm_nonneg _) (by nlinarith [hq])).symm
      _ = ‖F x‖ ^ (q - 1) := by
        congr 1
        ring
  · rw [show hilbertRadialTruncation q n F x = 0 by
      simp [hilbertRadialTruncation, hx]]
    simp [hx]

/-- Pairing the radial test field with the original field recovers the
truncated `q`-power. -/
theorem inner_hilbertRadialTruncation_self {α : Type*} {d : ℕ} {q : ℝ}
    (hq : 1 < q) (n : ℕ) (F : α → HilbertVec d) (x : α) :
    inner ℝ (hilbertRadialTruncation q n F x) (F x) =
      if ‖F x‖ ≤ (n : ℝ) then ‖F x‖ ^ q else 0 := by
  by_cases hx : ‖F x‖ ≤ (n : ℝ)
  · rw [show hilbertRadialTruncation q n F x =
        ‖F x‖ ^ (q - 2) • F x by
      simp [hilbertRadialTruncation, hx]]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [if_pos hx]
    rw [← Real.rpow_natCast]
    calc
      ‖F x‖ ^ (q - 2) * ‖F x‖ ^ (2 : ℝ) = ‖F x‖ ^ ((q - 2) + 2) :=
        (Real.rpow_add' (norm_nonneg _) (by
          intro h
          norm_num at h
          linarith)).symm
      _ = ‖F x‖ ^ q := by
        congr 1
        ring
  · rw [show hilbertRadialTruncation q n F x = 0 by
      simp [hilbertRadialTruncation, hx]]
    simp [hx]

/-- Raising the radial test field's norm to the Hölder-conjugate exponent
recovers the same truncated `q`-power. -/
theorem norm_hilbertRadialTruncation_rpow_conjugate {α : Type*} {d : ℕ}
    (q : FiniteLpExponent) (n : ℕ)
    (F : α → HilbertVec d) (x : α) :
    ‖hilbertRadialTruncation q.exponent.toReal n F x‖ ^
        q.conjugate.exponent.toReal =
      if ‖F x‖ ≤ (n : ℝ) then ‖F x‖ ^ q.exponent.toReal else 0 := by
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  have hq1 : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hreal : q.exponent.toReal.HolderConjugate q.conjugate.exponent.toReal :=
    ENNReal.HolderConjugate.toReal hq1
  rw [norm_hilbertRadialTruncation hq1]
  by_cases hx : ‖F x‖ ≤ (n : ℝ)
  · simp only [if_pos hx]
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    exact hreal.sub_one_mul_conj
  · simp only [if_neg hx]
    exact Real.zero_rpow hreal.symm.pos.ne'

/-- The algebraic-vector version of the radial pairing identity. -/
theorem vecDot_vectorRadialTruncation_self {α : Type*} {d : ℕ} {q : ℝ}
    (hq : 1 < q) (n : ℕ) (F : α → Vec d) (x : α) :
    vecDot (vectorRadialTruncation q n F x) (F x) =
      if euclideanNorm (F x) ≤ (n : ℝ) then euclideanNorm (F x) ^ q else 0 := by
  simpa [vectorRadialTruncation, euclideanNorm_eq_norm_ofVec, HilbertVec.inner_def] using
    inner_hilbertRadialTruncation_self hq n (fun y => HilbertVec.ofVec (F y)) x

/-- Vector-valued Hölder, in the exact `eLpNorm` form needed to bound the
cross weak pairing in the low-exponent duality argument. -/
theorem eLpNorm_vecDot_le_mul {α : Type*} {d : ℕ} [MeasurableSpace α]
    {μ : Measure α} {p r : ℝ≥0∞} [ENNReal.HolderConjugate p r]
    {F G : α → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p μ)
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) r μ) :
    eLpNorm (fun x => vecDot (F x) (G x)) 1 μ ≤
      eLpNorm (fun x => HilbertVec.ofVec (F x)) p μ *
        eLpNorm (fun x => HilbertVec.ofVec (G x)) r μ := by
  simpa [HilbertVec.inner_def] using
    (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hF.1 hG.1
      (fun x y : HilbertVec d => inner ℝ x y) 1
      (Filter.Eventually.of_forall (fun x => by
        simpa using! norm_inner_le_norm (𝕜 := ℝ)
          (HilbertVec.ofVec (F x)) (HilbertVec.ofVec (G x)))))

/-- The bounded radial test field has the expected uniform pointwise bound. -/
theorem norm_hilbertRadialTruncation_le {α : Type*} {d : ℕ} {q : ℝ}
    (hq : 1 < q) (n : ℕ) (F : α → HilbertVec d) (x : α) :
    ‖hilbertRadialTruncation q n F x‖ ≤ (n : ℝ) ^ (q - 1) := by
  rw [norm_hilbertRadialTruncation hq]
  by_cases hx : ‖F x‖ ≤ (n : ℝ)
  · rw [if_pos hx]
    exact Real.rpow_le_rpow (norm_nonneg _) hx (sub_pos.mpr hq).le
  · rw [if_neg hx]
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- On a finite measure, every radial truncation belongs to every finite
`Lᵖ` space, in particular to `L²` and to the conjugate exponent. -/
theorem memLp_hilbertRadialTruncation {α : Type*} {d : ℕ}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} {q : ℝ} (hq : 1 < q) (n : ℕ)
    {F : α → HilbertVec d} (hF : AEStronglyMeasurable F μ) :
    MemLp (hilbertRadialTruncation q n F) p μ :=
  MemLp.of_bound (aestronglyMeasurable_hilbertRadialTruncation hF)
    ((n : ℝ) ^ (q - 1))
    (Filter.Eventually.of_forall (norm_hilbertRadialTruncation_le hq n F))

/-- The algebraic-vector radial truncation is a.e. strongly measurable. -/
theorem aestronglyMeasurable_vectorRadialTruncation {α : Type*} {d : ℕ}
    [MeasurableSpace α] {μ : Measure α} {q : ℝ} {n : ℕ}
    {F : α → Vec d}
    (hF : AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x)) μ) :
    AEStronglyMeasurable (vectorRadialTruncation q n F) μ := by
  let G : α → HilbertVec d := fun x => HilbertVec.ofVec (F x)
  have hG : AEStronglyMeasurable (hilbertRadialTruncation q n G) μ :=
    aestronglyMeasurable_hilbertRadialTruncation hF
  simpa only [vectorRadialTruncation, G, HilbertVec.continuousLinearEquivVec_apply]
    using! (HilbertVec.continuousLinearEquivVec d).continuous.comp_aestronglyMeasurable hG

/-- The vector radial truncation has a direct `L²` membership form for the
adjoint divergence solver. -/
theorem memVectorL2_vectorRadialTruncation {d : ℕ} (U : Set (Vec d))
    [IsFiniteMeasure (volumeMeasureOn U)] {q : ℝ} (hq : 1 < q) (n : ℕ)
    (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x))
      (volumeMeasureOn U)) :
    MemVectorL2 U (vectorRadialTruncation q n F) := by
  apply MemLp.of_bound (aestronglyMeasurable_vectorRadialTruncation hF)
    ((n : ℝ) ^ (q - 1))
  apply Filter.Eventually.of_forall
  intro x
  calc
    ‖vectorRadialTruncation q n F x‖ ≤
        ‖HilbertVec.ofVec (vectorRadialTruncation q n F x)‖ :=
      HilbertVec.norm_toVec_le_norm _
    _ = ‖hilbertRadialTruncation q n (fun y => HilbertVec.ofVec (F y)) x‖ := by
      simp only [vectorRadialTruncation, HilbertVec.ofVec_toVec]
    _ ≤ _ := norm_hilbertRadialTruncation_le hq n _ x

/-- The truncated `q`-moment integrand used for monotone convergence. -/
def truncatedMoment {α : Type*} {d : ℕ} (q : ℝ) (n : ℕ)
    (F : α → HilbertVec d) : α → ℝ≥0∞ :=
  Set.indicator {x | ‖F x‖ ≤ (n : ℝ)} (fun x => ‖F x‖ₑ ^ q)

/-- The truncated moment integrands are a.e. measurable. -/
theorem aemeasurable_truncatedMoment {α : Type*} {d : ℕ}
    [MeasurableSpace α] {μ : Measure α} {q : ℝ} {n : ℕ}
    {F : α → HilbertVec d} (hF : AEStronglyMeasurable F μ) :
    AEMeasurable (truncatedMoment q n F) μ := by
  apply AEMeasurable.indicator₀
  · exact (hF.enorm.pow_const q)
  · exact nullMeasurableSet_norm_le hF n

/-- At each point, increasing the truncation level increases the truncated
moment, provided the moment exponent is nonnegative. -/
theorem monotone_truncatedMoment {α : Type*} {d : ℕ} {q : ℝ}
    (F : α → HilbertVec d) (x : α) :
    Monotone (fun n : ℕ => truncatedMoment q n F x) := by
  intro m n hmn
  by_cases hn : ‖F x‖ ≤ (n : ℝ)
  · by_cases hm : ‖F x‖ ≤ (m : ℝ)
    · simp [truncatedMoment, hm, hn]
    · have hnm : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hnot : ¬ ‖F x‖ ≤ (m : ℝ) := hm
      simp [truncatedMoment, hnot, hn]
  · have hnot : ¬ ‖F x‖ ≤ (m : ℝ) := by
      intro hm
      apply hn
      exact hm.trans (by exact_mod_cast hmn)
    simp [truncatedMoment, hnot, hn]

/-- The pointwise supremum of all truncated moments is the full moment. -/
theorem iSup_truncatedMoment_eq_enorm_rpow {α : Type*} {d : ℕ} {q : ℝ}
    (F : α → HilbertVec d) (x : α) :
    (⨆ n : ℕ, truncatedMoment q n F x) = ‖F x‖ₑ ^ q := by
  apply le_antisymm
  · apply iSup_le
    intro n
    by_cases hn : ‖F x‖ ≤ (n : ℝ)
    · simp [truncatedMoment, hn]
    · simp [truncatedMoment, hn]
  · obtain ⟨n, hn⟩ := exists_nat_ge ‖F x‖
    exact le_iSup_of_le n (by simp [truncatedMoment, hn])

/-- Monotone convergence in the precise truncated-moment form used by the
low-exponent duality argument. -/
theorem lintegral_enorm_rpow_eq_iSup_lintegral_truncatedMoment
    {α : Type*} {d : ℕ} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {F : α → HilbertVec d}
    (hF : AEStronglyMeasurable F μ) :
    (∫⁻ x, ‖F x‖ₑ ^ q ∂μ) =
      ⨆ n : ℕ, ∫⁻ x, truncatedMoment q n F x ∂μ := by
  rw [← lintegral_iSup'
    (fun n => aemeasurable_truncatedMoment (n := n) hF)
    (Filter.Eventually.of_forall (fun x => monotone_truncatedMoment F x))]
  apply lintegral_congr
  intro x
  exact (iSup_truncatedMoment_eq_enorm_rpow F x).symm

end INTERNAL
end CubeCalderonZygmund

end
end Homogenization
