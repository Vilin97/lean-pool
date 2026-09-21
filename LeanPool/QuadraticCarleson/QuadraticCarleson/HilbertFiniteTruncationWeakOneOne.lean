/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.Definitions
import Mathlib.Analysis.Convolution

/-!
# Weak `(1,1)` for finite annular Hilbert truncations

The zero-modulation contribution of a finite dyadic block is an ordinary
Hilbert kernel restricted to a finite annulus.  Such a kernel is genuinely
`L¹`, so Young's inequality followed by Markov's inequality gives a fully
concrete weak `(1,1)` estimate.  This is the finite-truncation statement; no
maximal-singular-integral hypothesis is introduced.
-/

open Filter MeasureTheory Set
open scoped Convolution ENNReal

namespace QuadraticCarleson
namespace HilbertFiniteTruncationWeakOneOne


noncomputable section

/-- The ordinary Hilbert kernel restricted to `ε < |t| ≤ R`. -/
def annularHilbertKernel (ε R t : ℝ) : ℂ :=
  if ε < |t| ∧ |t| ≤ R then 1 / (t : ℂ) else 0

theorem measurable_annularHilbertKernel (ε R : ℝ) :
    Measurable (annularHilbertKernel ε R) := by
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_le measurable_id.abs measurable_const)
  · exact measurable_const.div (Complex.measurable_ofReal.comp measurable_id)
  · exact measurable_const

theorem annularHilbertKernel_support_subset {ε R : ℝ} :
    Function.support (annularHilbertKernel ε R) ⊆ Icc (-R) R := by
  intro t ht
  change annularHilbertKernel ε R t ≠ 0 at ht
  rw [annularHilbertKernel] at ht
  split_ifs at ht with h
  · exact abs_le.mp h.2
  · exact False.elim (ht rfl)

theorem norm_annularHilbertKernel_le {ε R : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖annularHilbertKernel ε R t‖ ≤ 1 / ε := by
  rw [annularHilbertKernel]
  split_ifs with h
  · have ht0 : t ≠ 0 := by
      intro ht
      subst t
      exact (not_lt_of_ge hε.le) (by simpa only [abs_zero] using h.1)
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, one_div]
    simpa only [one_div] using one_div_le_one_div_of_le hε h.1.le
  · simpa using one_div_nonneg.mpr hε.le

theorem integrable_annularHilbertKernel {ε R : ℝ} (hε : 0 < ε) :
    Integrable (annularHilbertKernel ε R) := by
  apply (integrableOn_iff_integrable_of_support_subset
    annularHilbertKernel_support_subset).mp
  exact IntegrableOn.of_bound isCompact_Icc.measure_lt_top
    (measurable_annularHilbertKernel ε R).aestronglyMeasurable.restrict
    (1 / ε) (Filter.Eventually.of_forall (norm_annularHilbertKernel_le hε))

/-- A convenient explicit upper bound for the `L¹` mass of the annular
Hilbert kernel.  (The exact mass is logarithmic, but this elementary bound
is enough for a fixed finite truncation.) -/
theorem integral_norm_annularHilbertKernel_le {ε R : ℝ} (hε : 0 < ε)
    (hR : 0 ≤ R) :
    (∫ t, ‖annularHilbertKernel ε R t‖) ≤ 2 * R / ε := by
  calc
    (∫ t, ‖annularHilbertKernel ε R t‖) =
        ∫ t in Icc (-R) R, ‖annularHilbertKernel ε R t‖ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      rw [norm_eq_zero]
      by_contra hne
      exact ht (annularHilbertKernel_support_subset hne)
    _ ≤ ∫ _t in Icc (-R) R, (1 / ε : ℝ) := by
      apply integral_mono
      · exact (integrable_annularHilbertKernel hε).norm.integrableOn
      · exact integrableOn_const isCompact_Icc.measure_lt_top.ne
      · exact norm_annularHilbertKernel_le hε
    _ = 2 * R / ε := by
      rw [setIntegral_const, Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
      simp only [smul_eq_mul]
      ring

/-- Finite annular truncation of the ordinary Hilbert transform, written as
a convolution. -/
def annularHilbertTruncation (ε R : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  annularHilbertKernel ε R ⋆[ContinuousLinearMap.mul ℂ ℂ] f

theorem integrable_annularHilbertTruncation {ε R : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (annularHilbertTruncation ε R f) :=
  (integrable_annularHilbertKernel hε).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hf

/-- Young's `L¹ * L¹ → L¹` inequality for the finite annular Hilbert
truncation, with the exact kernel mass on the right. -/
theorem integral_norm_annularHilbertTruncation_le {ε R : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x, ‖annularHilbertTruncation ε R f x‖) ≤
      (∫ t, ‖annularHilbertKernel ε R t‖) * (∫ x, ‖f x‖) := by
  let k : ℝ → ℝ := fun t ↦ ‖annularHilbertKernel ε R t‖
  let g : ℝ → ℝ := fun x ↦ ‖f x‖
  have hk : Integrable k := (integrable_annularHilbertKernel hε).norm
  have hg : Integrable g := hf.norm
  have hconv : Integrable (k ⋆ g) :=
    hk.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg
  have hpoint : ∀ x, ‖annularHilbertTruncation ε R f x‖ ≤ (k ⋆ g) x := by
    intro x
    rw [annularHilbertTruncation, convolution_def, convolution_def]
    calc
      ‖∫ t, annularHilbertKernel ε R t * f (x - t)‖ ≤
          ∫ t, ‖annularHilbertKernel ε R t * f (x - t)‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ t, ‖annularHilbertKernel ε R t‖ * ‖f (x - t)‖ := by
        congr 1
        funext t
        rw [norm_mul]
  calc
    (∫ x, ‖annularHilbertTruncation ε R f x‖) ≤ ∫ x, (k ⋆ g) x := by
      apply integral_mono
      · exact (integrable_annularHilbertTruncation hε hf).norm
      · exact hconv
      · exact hpoint
    _ = (∫ t, k t) * (∫ x, g x) := by
      simpa using integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hk hg
    _ = (∫ t, ‖annularHilbertKernel ε R t‖) * (∫ x, ‖f x‖) := rfl

theorem integrableOn_zeroHilbertTail {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    IntegrableOn (fun t ↦ f (x - t) / (t : ℂ)) {t : ℝ | ε < |t|} := by
  let s : Set ℝ := {t : ℝ | ε < |t|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const measurable_id.abs
  have hg : Integrable (fun t ↦ f (x - t)) := hf.comp_sub_left x
  have hm : Measurable (fun t : ℝ ↦ 1 / (t : ℂ)) :=
    measurable_const.div (Complex.measurable_ofReal.comp measurable_id)
  have hb : ∀ᵐ t : ℝ ∂volume.restrict s, ‖(1 : ℂ) / (t : ℂ)‖ ≤ 1 / ε := by
    filter_upwards [ae_restrict_mem hs] with t ht
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, one_div]
    simpa only [one_div] using one_div_le_one_div_of_le hε ht.le
  have hi := hg.integrableOn.bdd_mul hm.aestronglyMeasurable.restrict hb
  change Integrable (fun t ↦ f (x - t) / (t : ℂ)) (volume.restrict s)
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hi

/-- The annular convolution is exactly the difference of two sharp ordinary
Hilbert truncations.  Thus this module's concrete operator is the `λ = 0`
operator already appearing in `quadraticHilbertTrunc`, not a surrogate. -/
theorem annularHilbertTruncation_eq_zeroTrunc_sub {ε R : ℝ}
    (hε : 0 < ε) (hεR : ε ≤ R) {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    annularHilbertTruncation ε R f x =
      quadraticHilbertTrunc 0 ε f x - quadraticHilbertTrunc 0 R f x := by
  let sε : Set ℝ := {t : ℝ | ε < |t|}
  let sR : Set ℝ := {t : ℝ | R < |t|}
  let A : Set ℝ := {t : ℝ | ε < |t| ∧ |t| ≤ R}
  have hsR : MeasurableSet sR :=
    measurableSet_lt measurable_const measurable_id.abs
  have hsub : sR ⊆ sε := by
    intro t ht
    exact hεR.trans_lt ht
  have hdiff : sε \ sR = A := by
    ext t
    simp only [sε, sR, A, mem_diff, mem_setOf_eq, not_lt]
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_le measurable_id.abs measurable_const)
  have hint : IntegrableOn (fun t ↦ f (x - t) / (t : ℂ)) sε :=
    integrableOn_zeroHilbertTail hε hf x
  calc
    annularHilbertTruncation ε R f x =
        ∫ t in A, f (x - t) / (t : ℂ) := by
      rw [← integral_indicator hA]
      unfold annularHilbertTruncation
      rw [convolution_def]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ A
      · simp only [indicator_of_mem ht, annularHilbertKernel, A, mem_setOf_eq] at ht ⊢
        rw [if_pos ht]
        simp [div_eq_mul_inv, mul_comm]
      · simp only [indicator_of_notMem ht, annularHilbertKernel, A, mem_setOf_eq] at ht ⊢
        rw [if_neg ht]
        change (0 : ℂ) * f (x - t) = 0
        rw [zero_mul]
    _ = ∫ t in sε \ sR, f (x - t) / (t : ℂ) := by rw [hdiff]
    _ = (∫ t in sε, f (x - t) / (t : ℂ)) -
          ∫ t in sR, f (x - t) / (t : ℂ) := integral_diff hsR hint hsub
    _ = quadraticHilbertTrunc 0 ε f x - quadraticHilbertTrunc 0 R f x := by
      unfold quadraticHilbertTrunc
      simp only [zero_mul, phase_zero, mul_one, sε, sR]

/-- Concrete weak `(1,1)` estimate for one finite annular Hilbert
truncation. -/
theorem weak_one_one_annularHilbertTruncation {ε R α : ℝ}
    (hε : 0 < ε) (_hα : 0 ≤ α) {f : ℝ → ℂ} (hf : Integrable f) :
    α * volume.real {x | α ≤ ‖annularHilbertTruncation ε R f x‖} ≤
      (∫ t, ‖annularHilbertKernel ε R t‖) * (∫ x, ‖f x‖) := by
  calc
    α * volume.real {x | α ≤ ‖annularHilbertTruncation ε R f x‖} ≤
        ∫ x, ‖annularHilbertTruncation ε R f x‖ :=
      mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
        (integrable_annularHilbertTruncation hε hf).norm α
    _ ≤ _ := integral_norm_annularHilbertTruncation_le hε hf

/-- Fully explicit finite-truncation weak `(1,1)` estimate. -/
theorem weak_one_one_annularHilbertTruncation_explicit {ε R α : ℝ}
    (hε : 0 < ε) (hR : 0 ≤ R) (hα : 0 ≤ α)
    {f : ℝ → ℂ} (hf : Integrable f) :
    α * volume.real {x | α ≤ ‖annularHilbertTruncation ε R f x‖} ≤
      (2 * R / ε) * (∫ x, ‖f x‖) := by
  calc
    α * volume.real {x | α ≤ ‖annularHilbertTruncation ε R f x‖} ≤
        (∫ t, ‖annularHilbertKernel ε R t‖) * (∫ x, ‖f x‖) :=
      weak_one_one_annularHilbertTruncation hε hα hf
    _ ≤ (2 * R / ε) * (∫ x, ‖f x‖) :=
      mul_le_mul_of_nonneg_right (integral_norm_annularHilbertKernel_le hε hR)
        (integral_nonneg fun _ ↦ norm_nonneg _)

/-- The pointwise maximum of a finite family of annular ordinary Hilbert
truncations.  The empty maximum is zero. -/
noncomputable def finiteAnnularHilbertMax {N : ℕ} (ε R : Fin N → ℝ)
    (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ↑(Finset.univ.sup fun i ↦ ‖annularHilbertTruncation (ε i) (R i) f x‖₊)

/-- The same finite maximum, expressed directly with the project's sharp
zero-modulation truncations. -/
noncomputable def finiteZeroHilbertTruncationDifferenceMax {N : ℕ}
    (ε R : Fin N → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ↑(Finset.univ.sup fun i ↦
    ‖quadraticHilbertTrunc 0 (ε i) f x - quadraticHilbertTrunc 0 (R i) f x‖₊)

theorem finiteAnnularHilbertMax_eq_zeroTruncationDifferenceMax {N : ℕ}
    (ε R : Fin N → ℝ) (hε : ∀ i, 0 < ε i) (hεR : ∀ i, ε i ≤ R i)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    finiteAnnularHilbertMax ε R f x =
      finiteZeroHilbertTruncationDifferenceMax ε R f x := by
  unfold finiteAnnularHilbertMax finiteZeroHilbertTruncationDifferenceMax
  congr 2
  funext i
  rw [annularHilbertTruncation_eq_zeroTrunc_sub (hε i) (hεR i) hf x]

theorem norm_annularHilbertTruncation_le_finiteMax {N : ℕ}
    (ε R : Fin N → ℝ) (f : ℝ → ℂ) (x : ℝ) (i : Fin N) :
    ‖annularHilbertTruncation (ε i) (R i) f x‖ ≤
      finiteAnnularHilbertMax ε R f x := by
  change ↑‖annularHilbertTruncation (ε i) (R i) f x‖₊ ≤
    ↑(Finset.univ.sup fun j ↦ ‖annularHilbertTruncation (ε j) (R j) f x‖₊)
  exact_mod_cast Finset.le_sup (s := Finset.univ)
    (f := fun j ↦ ‖annularHilbertTruncation (ε j) (R j) f x‖₊)
    (Finset.mem_univ i)

theorem finiteAnnularHilbertMax_le_sum {N : ℕ} (ε R : Fin N → ℝ)
    (f : ℝ → ℂ) (x : ℝ) :
    finiteAnnularHilbertMax ε R f x ≤
      ∑ i, ‖annularHilbertTruncation (ε i) (R i) f x‖ := by
  classical
  unfold finiteAnnularHilbertMax
  have hnn : (Finset.univ.sup fun i ↦
      ‖annularHilbertTruncation (ε i) (R i) f x‖₊) ≤
      ∑ i, ‖annularHilbertTruncation (ε i) (R i) f x‖₊ := by
    apply Finset.sup_le
    intro i _hi
    exact Finset.single_le_sum
      (fun j (_hj : j ∈ (Finset.univ : Finset (Fin N))) ↦
        (bot_le : (0 : NNReal) ≤
          ‖annularHilbertTruncation (ε j) (R j) f x‖₊))
      (Finset.mem_univ i)
  calc
    (↑(Finset.univ.sup fun i ↦
        ‖annularHilbertTruncation (ε i) (R i) f x‖₊) : ℝ) ≤
        ↑(∑ i, ‖annularHilbertTruncation (ε i) (R i) f x‖₊) :=
      NNReal.coe_le_coe.mpr hnn
    _ = _ := by simp

theorem integrable_finiteAnnularHilbertMax {N : ℕ} (ε R : Fin N → ℝ)
    (hε : ∀ i, 0 < ε i) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (finiteAnnularHilbertMax ε R f) := by
  classical
  have hs : ∀ s : Finset (Fin N), Integrable (fun x : ℝ ↦
      (↑(s.sup fun i ↦ ‖annularHilbertTruncation (ε i) (R i) f x‖₊) : ℝ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        have hii : Integrable (fun x ↦
            ‖annularHilbertTruncation (ε i) (R i) f x‖) :=
          (integrable_annularHilbertTruncation (hε i) hf).norm
        simp only [Finset.sup_insert, NNReal.coe_max, coe_nnnorm]
        convert hii.sup ih using 1
        · rfl
        · ext x
          rw [Pi.sup_apply]
  exact hs Finset.univ

/-- A concrete weak `(1,1)` estimate for a finite maximum of finite annular
truncations.  Unlike the full maximal Hilbert theorem, this statement follows
only from `L¹` convolution and has the exact sum of the kernel masses. -/
theorem weak_one_one_finiteAnnularHilbertMax {N : ℕ} (ε R : Fin N → ℝ)
    (hε : ∀ i, 0 < ε i) {α : ℝ} (_hα : 0 ≤ α)
    {f : ℝ → ℂ} (hf : Integrable f) :
    α * volume.real {x | α ≤ finiteAnnularHilbertMax ε R f x} ≤
      (∑ i, ∫ t, ‖annularHilbertKernel (ε i) (R i) t‖) *
        (∫ x, ‖f x‖) := by
  classical
  calc
    α * volume.real {x | α ≤ finiteAnnularHilbertMax ε R f x} ≤
        ∫ x, finiteAnnularHilbertMax ε R f x :=
      mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun x ↦ by
          unfold finiteAnnularHilbertMax
          change (0 : ℝ) ≤ ↑(Finset.univ.sup fun i ↦
            ‖annularHilbertTruncation (ε i) (R i) f x‖₊)
          exact NNReal.coe_nonneg _)
        (integrable_finiteAnnularHilbertMax ε R hε hf) α
    _ ≤ ∫ x, ∑ i, ‖annularHilbertTruncation (ε i) (R i) f x‖ := by
      apply integral_mono
      · exact integrable_finiteAnnularHilbertMax ε R hε hf
      · exact integrable_finsetSum Finset.univ (fun i _ ↦
          (integrable_annularHilbertTruncation (hε i) hf).norm)
      · exact finiteAnnularHilbertMax_le_sum ε R f
    _ = ∑ i, ∫ x, ‖annularHilbertTruncation (ε i) (R i) f x‖ := by
      rw [integral_finsetSum]
      intro i _hi
      exact (integrable_annularHilbertTruncation (hε i) hf).norm
    _ ≤ ∑ i, (∫ t, ‖annularHilbertKernel (ε i) (R i) t‖) *
          (∫ x, ‖f x‖) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact integral_norm_annularHilbertTruncation_le (hε i) hf
    _ = _ := by rw [Finset.sum_mul]

/-- Explicit version of the finite-maximal estimate. -/
theorem weak_one_one_finiteAnnularHilbertMax_explicit {N : ℕ}
    (ε R : Fin N → ℝ) (hε : ∀ i, 0 < ε i) (hR : ∀ i, 0 ≤ R i)
    {α : ℝ} (hα : 0 ≤ α) {f : ℝ → ℂ} (hf : Integrable f) :
    α * volume.real {x | α ≤ finiteAnnularHilbertMax ε R f x} ≤
      (∑ i, 2 * R i / ε i) * (∫ x, ‖f x‖) := by
  calc
    _ ≤ (∑ i, ∫ t, ‖annularHilbertKernel (ε i) (R i) t‖) *
          (∫ x, ‖f x‖) :=
      weak_one_one_finiteAnnularHilbertMax ε R hε hα hf
    _ ≤ (∑ i, 2 * R i / ε i) * (∫ x, ‖f x‖) := by
      apply mul_le_mul_of_nonneg_right
      · exact Finset.sum_le_sum fun i _ ↦
          integral_norm_annularHilbertKernel_le (hε i) (hR i)
      · exact integral_nonneg fun _ ↦ norm_nonneg _

/-- Paper-facing finite sharp-truncation consequence at modulation zero.
The constant is explicit, and no Hilbert-transform boundedness premise is
assumed. -/
theorem weak_one_one_finiteZeroHilbertTruncationDifferenceMax_explicit {N : ℕ}
    (ε R : Fin N → ℝ) (hε : ∀ i, 0 < ε i) (hR : ∀ i, 0 ≤ R i)
    (hεR : ∀ i, ε i ≤ R i) {α : ℝ} (hα : 0 ≤ α)
    {f : ℝ → ℂ} (hf : Integrable f) :
    α * volume.real
      {x | α ≤ finiteZeroHilbertTruncationDifferenceMax ε R f x} ≤
      (∑ i, 2 * R i / ε i) * (∫ x, ‖f x‖) := by
  have hfun : finiteZeroHilbertTruncationDifferenceMax ε R f =
      finiteAnnularHilbertMax ε R f := by
    funext x
    exact (finiteAnnularHilbertMax_eq_zeroTruncationDifferenceMax
      ε R hε hεR hf x).symm
  rw [hfun]
  exact weak_one_one_finiteAnnularHilbertMax_explicit ε R hε hR hα hf


end
end HilbertFiniteTruncationWeakOneOne
end QuadraticCarleson
