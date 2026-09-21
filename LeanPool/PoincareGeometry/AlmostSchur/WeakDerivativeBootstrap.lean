/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LocalWeakPoissonGraph
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Differentiating local weak divergence equations

This module proves identities used to bootstrap an interior H² estimate. It
does not assert an elliptic gain of derivatives or a smooth representative.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A local weak directional derivative, tested against genuine smooth compact tests. -/
def HasWeakDirectionalDerivativeOn (K : Set E) (v : E) (u du : E → ℝ) : Prop :=
  ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
    (∫ z in K, u z * fderiv ℝ φ z v) = -(∫ z in K, du z * φ z)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Directional derivatives of smooth tests remain smooth. -/
theorem contDiff_smooth_test_derivative {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : E) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The two classical test derivatives commute. -/
theorem smooth_test_derivatives_commute {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (z v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) z w =
      fderiv ℝ (fun y => fderiv ℝ φ y w) z v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ φ)).differentiable (by simp) z
  rw [fderiv_clm_apply hd (differentiableAt_const v),
    fderiv_clm_apply hd (differentiableAt_const w)]
  have hn : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    decide
  simpa using (hφ.contDiffAt.isSymmSndFDerivAt hn) w v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A locally smooth coefficient times a supported smooth test is globally smooth. -/
theorem contDiff_local_coefficient_mul_test {W : Set E} (hW : IsOpen W)
    {a φ : E → ℝ} (ha : ContDiffOn ℝ ∞ a W) (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ W) : ContDiff ℝ ∞ (fun z => a z * φ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport φ
  · exact (ha.contDiffAt (hW.mem_nhds (hs hz))).mul hφ.contDiffAt
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The coefficient/test product rule holds globally, including outside the
coefficient's smoothness domain, because the test is locally zero there. -/
theorem fderiv_local_coefficient_mul_test {W : Set E} (hW : IsOpen W)
    {a φ : E → ℝ} (ha : ContDiffOn ℝ ∞ a W) (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ W) (z v : E) :
    fderiv ℝ (fun y => a y * φ y) z v =
      fderiv ℝ a z v * φ z + a z * fderiv ℝ φ z v := by
  by_cases hz : z ∈ W
  · have hd := congrArg (fun T : E →L[ℝ] ℝ => T v)
      (fderiv_mul ((ha.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
        (hφ.differentiable (by simp) z))
    change fderiv ℝ (a * φ) z v = _
    simpa [mul_comm, add_comm] using hd
  · have hn : z ∉ tsupport φ := fun h => hz (hs h)
    have hφ0 := image_eq_zero_of_notMem_tsupport hn
    have hdφ : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport ℝ hn
    have hd : fderiv ℝ (fun y => a y * φ y) z = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun h => hn (tsupport_mul_subset_right h))
    simp [hd, hdφ, hφ0]

/-- A smooth local coefficient obeys the genuine weak product rule. The weak
derivative of the coefficient times u is derived by testing, not postulated. -/
theorem HasWeakDirectionalDerivativeOn.mul_coefficient
    {K W : Set E} (hW : IsOpen W) (hKW : K ⊆ W)
    {v : E} {u du a : E → ℝ}
    (hu : MemLp u 2 ((volume : Measure E).restrict K))
    (hdu : MemLp du 2 ((volume : Measure E).restrict K))
    (hd : HasWeakDirectionalDerivativeOn K v u du) (ha : ContDiffOn ℝ ∞ a W) :
    HasWeakDirectionalDerivativeOn K v (fun z => a z * u z)
      (fun z => fderiv ℝ a z v * u z + a z * du z) := by
  intro φ hφ hc hs
  have hsW := hs.trans hKW
  have hdφ := contDiff_smooth_test_derivative hφ v
  have hda : ContDiffOn ℝ ∞ (fun z => fderiv ℝ a z v) W :=
    (ha.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have haφ := contDiff_local_coefficient_mul_test hW ha hφ hsW
  have hadaφ := contDiff_local_coefficient_mul_test hW hda hφ hsW
  have hadφ := contDiff_local_coefficient_mul_test hW ha hdφ
    ((tsupport_fderiv_apply_subset ℝ v).trans hsW)
  have hi₁ : Integrable (fun z => u z * (fderiv ℝ a z v * φ z))
      ((volume : Measure E).restrict K) := hu.integrable_mul
    ((hadaφ.continuous.memLp_of_hasCompactSupport hc.mul_left : MemLp _ 2 volume).restrict K)
  have hi₂ : Integrable (fun z => u z * (a z * fderiv ℝ φ z v))
      ((volume : Measure E).restrict K) := hu.integrable_mul
    ((hadφ.continuous.memLp_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left :
      MemLp _ 2 volume).restrict K)
  have hi₃ : Integrable (fun z => du z * (a z * φ z))
      ((volume : Measure E).restrict K) := hdu.integrable_mul
    ((haφ.continuous.memLp_of_hasCompactSupport hc.mul_left : MemLp _ 2 volume).restrict K)
  have he := hd (fun z => a z * φ z) haφ hc.mul_left (tsupport_mul_subset_right.trans hs)
  have he' : (∫ z in K, u z * (fderiv ℝ a z v * φ z)) +
      (∫ z in K, u z * (a z * fderiv ℝ φ z v)) = -(∫ z in K, du z * (a z * φ z)) := by
    rw [← integral_add hi₁ hi₂]
    convert he using 1
    congr 1
    funext z
    rw [fderiv_local_coefficient_mul_test hW ha hφ hsW]
    ring
  have hl : (∫ z in K, a z * u z * fderiv ℝ φ z v) =
      ∫ z in K, u z * (a z * fderiv ℝ φ z v) := by congr 1; funext z; ring
  have hr : (∫ z in K, (fderiv ℝ a z v * u z + a z * du z) * φ z) =
      (∫ z in K, u z * (fderiv ℝ a z v * φ z)) + (∫ z in K, du z * (a z * φ z)) := by
    rw [← integral_add hi₁ hi₃]
    congr 1
    funext z
    ring
  rw [hl, hr]
  linarith

/-- Differentiating the weak divergence equation differentiates both its flux
and forcing. The proof differentiates only smooth tests and uses the supplied
genuine weak-derivative identities, not classical regularity of the solution. -/
theorem weak_divergence_equation_derivative {ι : Type*} [Fintype ι]
    (b : ι → E) (K : Set E) (v : E) (J dJ : ι → E → ℝ) (f df : E → ℝ)
    (hJ : ∀ j, HasWeakDirectionalDerivativeOn K v (J j) (dJ j))
    (hf : HasWeakDirectionalDerivativeOn K v f df)
    (hPDE : ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, J j z * fderiv ℝ φ z (b j)) = -(∫ z in K, f z * φ z)) :
    ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, dJ j z * fderiv ℝ φ z (b j)) = -(∫ z in K, df z * φ z) := by
  intro φ hφ hc hs
  have he := hPDE (fun z => fderiv ℝ φ z v) (contDiff_smooth_test_derivative hφ v)
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  have hj (j : ι) : (∫ z in K, J j z * fderiv ℝ (fun y => fderiv ℝ φ y v) z (b j)) =
      -(∫ z in K, dJ j z * fderiv ℝ φ z (b j)) := by
    calc
      _ = ∫ z in K, J j z * fderiv ℝ (fun y => fderiv ℝ φ y (b j)) z v := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [smooth_test_derivatives_commute hφ z v (b j)]
      _ = _ := hJ j _ (contDiff_smooth_test_derivative hφ (b j))
        (hc.fderiv_apply ℝ (b j)) ((tsupport_fderiv_apply_subset ℝ (b j)).trans hs)
  simp_rw [hj, Finset.sum_neg_distrib, hf φ hφ hc hs, neg_neg] at he
  linarith

/-- Finite sums preserve genuine L² weak-derivative identities. -/
theorem HasWeakDirectionalDerivativeOn.finset_sum {ι : Type*} (s : Finset ι)
    {K : Set E} {v : E} (u du : ι → E → ℝ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 ((volume : Measure E).restrict K))
    (hdu : ∀ i ∈ s, MemLp (du i) 2 ((volume : Measure E).restrict K))
    (hd : ∀ i ∈ s, HasWeakDirectionalDerivativeOn K v (u i) (du i)) :
    HasWeakDirectionalDerivativeOn K v (fun z => ∑ i ∈ s, u i z)
      (fun z => ∑ i ∈ s, du i z) := by
  intro φ hφ hc hs
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum, integral_finsetSum, ← Finset.sum_neg_distrib]
  · exact Finset.sum_congr rfl (fun i hi => hd i hi φ hφ hc hs)
  · intro i hi
    exact (hdu i hi).integrable_mul
      ((hφ.continuous.memLp_of_hasCompactSupport hc : MemLp _ 2 volume).restrict K)
  · intro i hi
    exact (hu i hi).integrable_mul
      (((contDiff_smooth_test_derivative hφ v).continuous.memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ v) : MemLp _ 2 volume).restrict K)

/-- A coefficient continuous on a compact set preserves local L² membership. -/
theorem memLp_mul_coefficient_on_compact {K : Set E} (hK : IsCompact K)
    {a u : E → ℝ} (ha : ContinuousOn a K)
    (hu : MemLp u 2 ((volume : Measure E).restrict K)) :
    MemLp (fun z => a z * u z) 2 ((volume : Measure E).restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ha
  apply hu.of_le_mul (c := C) ((ha.aestronglyMeasurable hK.measurableSet).mul hu.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  simpa only [Pi.mul_apply, norm_mul] using
    mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg (u z))

/-- The local coefficient-commutator equation derived from weak second
derivative data. Its differentiated flux is proved L² on the compact set.
This supplies an equation for the next elliptic estimate, not that estimate. -/
theorem weak_divergence_coefficient_derivative {ι : Type*} [Fintype ι]
    (b : ι → E) {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (v : E) (A : E → ι → ι → ℝ) (D dD : ι → E → ℝ) (F dF : E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hD : ∀ i, MemLp (D i) 2 ((volume : Measure E).restrict K))
    (hdD : ∀ i, MemLp (dD i) 2 ((volume : Measure E).restrict K))
    (hweak : ∀ i, HasWeakDirectionalDerivativeOn K v (D i) (dD i))
    (hF : HasWeakDirectionalDerivativeOn K v F dF)
    (hPDE : ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * D i z) * fderiv ℝ φ z (b j)) =
        -(∫ z in K, F z * φ z)) :
    (∀ j, MemLp (fun z => ∑ i,
      (fderiv ℝ (fun y => A y i j) z v * D i z + A z i j * dD i z)) 2
      ((volume : Measure E).restrict K)) ∧
    ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i,
        (fderiv ℝ (fun y => A y i j) z v * D i z + A z i j * dD i z)) *
          fderiv ℝ φ z (b j)) = -(∫ z in K, dF z * φ z) := by
  have hDA (i j : ι) : ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun y => A y i j) z v) W :=
    ((hA i j).fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have hm (i j : ι) : MemLp (fun z => A z i j * D i z) 2 ((volume : Measure E).restrict K) :=
    memLp_mul_coefficient_on_compact hK ((hA i j).continuousOn.mono hKW) (hD i)
  have hdm (i j : ι) : MemLp (fun z => fderiv ℝ (fun y => A y i j) z v * D i z +
      A z i j * dD i z) 2 ((volume : Measure E).restrict K) :=
    (memLp_mul_coefficient_on_compact hK ((hDA i j).continuousOn.mono hKW) (hD i)).add
      (memLp_mul_coefficient_on_compact hK ((hA i j).continuousOn.mono hKW) (hdD i))
  refine ⟨fun j => memLp_finsetSum _ (fun i _ => hdm i j), ?_⟩
  apply weak_divergence_equation_derivative b K v
    (fun j z => ∑ i, A z i j * D i z) _ F dF ?_ hF hPDE
  intro j
  exact HasWeakDirectionalDerivativeOn.finset_sum Finset.univ _ _
    (fun i _ => hm i j) (fun i _ => hdm i j)
    (fun i _ => HasWeakDirectionalDerivativeOn.mul_coefficient hW hKW
      (hD i) (hdD i) (hweak i) (hA i j))

end AlmostSchur
