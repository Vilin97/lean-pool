/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBall
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.H1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Sobolev Poincare Ball Weak

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ENNReal Convolution Pointwise

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem native_euclidean_norm_eq_l2 (x : Vec 3) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [vecEuclideanNorm, vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem native_euclidean_norm_add_le (x y : Vec 3) :
    vecEuclideanNorm (x + y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  rw [native_euclidean_norm_eq_l2, native_euclidean_norm_eq_l2,
    native_euclidean_norm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem native_norm_le_euclidean_norm (x : Vec 3) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

private theorem native_euclidean_norm_le_sqrt_three_norm (x : Vec 3) :
    vecEuclideanNorm x ≤ Real.sqrt 3 * ‖x‖ := by
  have hsq : vecEuclideanNorm x ^ 2 ≤ (Real.sqrt 3 * ‖x‖) ^ 2 := by
    rw [vecEuclideanNorm_sq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      vecNormSq x ≤ ∑ _i : Fin 3, ‖x‖ ^ 2 := by
        rw [vecNormSq_eq_sum_sq]
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm x i) 2
      _ = 3 * ‖x‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vecEuclideanNorm x| ≤ |Real.sqrt 3 * ‖x‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vecEuclideanNorm_nonneg x),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg x))] at h2

private theorem eLpNorm_pi_le_sum_weak
    {f : Vec 3 → Vec 3} {μ : Measure (Vec 3)}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ≤ ∑ i : Fin 3, eLpNorm (fun x => f x i) 2 μ := by
  have hpoint : ∀ x, ‖f x‖ ≤ ∑ i : Fin 3, ‖f x i‖ := by
    intro x
    rw [Pi.norm_def]
    have hsup : Finset.univ.sup (fun i => ‖f x i‖₊) ≤
        ∑ i : Fin 3, ‖f x i‖₊ := by
      apply Finset.sup_le
      intro i hi
      have hnonneg : ∀ j : Fin 3, j ∈ Finset.univ → 0 ≤ ‖f x j‖₊ := by
        intro j hj
        exact bot_le
      simpa only [Finset.sum_filter, Finset.mem_univ, ite_true] using
        (Finset.single_le_sum hnonneg (Finset.mem_univ i))
    exact_mod_cast hsup
  calc
    eLpNorm f 2 μ ≤ eLpNorm (fun x => ∑ i : Fin 3, ‖f x i‖) 2 μ := by
      apply eLpNorm_mono_ae hf
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
        (fun i _ => norm_nonneg (f x i)))]
      exact hpoint x
    _ = eLpNorm (∑ i : Fin 3, (fun x => ‖f x i‖)) 2 μ := by rfl
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => ‖f x i‖) 2 μ := by
      simpa using (eLpNorm_sum_le (p := (2 : ENNReal)) (s := Finset.univ)
        (f := fun i : Fin 3 => (fun x => ‖f x i‖)) (by norm_num))
    _ = ∑ i : Fin 3, eLpNorm (fun x => f x i) 2 μ := by
      congr 1
      funext i
      have hfi : AEStronglyMeasurable (fun x => f x i) μ := by
        simpa only [ContinuousLinearMap.proj_apply] using
          (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hf
      rw [eLpNorm_norm _ hfi]

private theorem tendsto_sum_zero_fin_three_weak
    {f : Fin 3 → ℕ → ℝ≥0∞}
    (hf : ∀ i, Tendsto (f i) atTop (nhds 0)) :
    Tendsto (fun n => ∑ i : Fin 3, f i n) atTop (nhds 0) := by
  simpa using tendsto_finsetSum Finset.univ (fun i hi => hf i)

private theorem lpNorm_tendsto_of_diff_weak
    {E : Type*} [NormedAddCommGroup E] {μ : Measure (Vec 3)}
    {f : Vec 3 → E} {g : ℕ → Vec 3 → E}
    (hf : MemLp f 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (fun x => g n x - f x) 2 μ)
      atTop (nhds 0)) :
    Tendsto (fun n => lpNorm (g n) 2 μ) atTop (nhds (lpNorm f 2 μ)) := by
  have hdiff : ∀ n, MemLp (fun x => g n x - f x) 2 μ := fun n => (hg n).sub hf
  have hconv' : Tendsto
      (fun n => lpNorm (fun x => g n x - f x) 2 μ) atTop (nhds 0) := by
    change Tendsto
      (fun n => (eLpNorm (fun x => g n x - f x) 2 μ).toReal)
        atTop (nhds 0)
    exact (ENNReal.tendsto_toReal_zero_iff
      (fun n => (hdiff n).eLpNorm_ne_top)).mpr hconv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv'
    (Eventually.of_forall (fun _ => norm_nonneg _))
  filter_upwards [] with n
  have h₁ := lpNorm_le_lpNorm_add_lpNorm_sub
    (f := f) (g := g n) (hg n) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h₂ := lpNorm_le_lpNorm_add_lpNorm_sub
    (f := g n) (g := f) hf (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcomm := lpNorm_sub_comm (g n) f (2 : ℝ≥0∞) μ
  rw [← hcomm] at h₂
  have h₁' : lpNorm f 2 μ ≤ lpNorm (g n) 2 μ +
      lpNorm (fun x => g n x - f x) 2 μ := by
    change lpNorm f 2 μ ≤ lpNorm (g n) 2 μ +
      lpNorm (fun x => g n x - f x) 2 μ at h₁
    exact h₁
  have h₂' : lpNorm (g n) 2 μ ≤ lpNorm f 2 μ +
      lpNorm (fun x => g n x - f x) 2 μ := by
    change lpNorm (g n) 2 μ ≤ lpNorm f 2 μ +
      lpNorm (fun x => g n x - f x) 2 μ at h₂
    exact h₂
  exact (abs_le).2 ⟨
    (neg_le_sub_iff_le_add).2 (by simpa [add_comm] using h₁'),
    (sub_le_iff_le_add).2 (by simpa [add_comm] using h₂')⟩

private theorem eLpNorm_tendsto_of_diff_weak
    {E : Type*} [NormedAddCommGroup E] {μ : Measure (Vec 3)}
    {f : Vec 3 → E} {g : ℕ → Vec 3 → E}
    (hf : MemLp f 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (fun x => g n x - f x) 2 μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (g n) 2 μ) atTop (nhds (eLpNorm f 2 μ)) := by
  apply (ENNReal.tendsto_toReal_iff (fun n => (hg n).eLpNorm_ne_top)
    hf.eLpNorm_ne_top).mp
  change Tendsto (fun n => lpNorm (g n) 2 μ) atTop (nhds (lpNorm f 2 μ))
  exact lpNorm_tendsto_of_diff_weak hf hg hconv

private theorem integral_sub_tendsto_zero_of_eLpNorm_two
    {μ : Measure (Vec 3)} [IsFiniteMeasure μ]
    {f : Vec 3 → ℝ} {g : ℕ → Vec 3 → ℝ}
    (hf : MemLp f 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (fun x => g n x - f x) 2 μ)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, g n x - f x ∂μ) atTop (nhds 0) := by
  have hdiff : ∀ n, MemLp (fun x => g n x - f x) 2 μ := fun n => (hg n).sub hf
  have hbound : Tendsto
      (fun n => eLpNorm (fun x => g n x - f x) 1 μ) atTop (nhds 0) := by
    let c : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))
    have hc : c ≠ ∞ := by
      dsimp [c]
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
    have hmul : Tendsto
        (fun n => eLpNorm (fun x => g n x - f x) 2 μ * c) atTop (nhds 0) := by
      simpa using (ENNReal.Tendsto.mul_const hconv (Or.inr hc))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hmul (Eventually.of_forall (fun _ => zero_le))
    filter_upwards [] with n
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)
      (hdiff n).aestronglyMeasurable
  have hnorm : Tendsto
      (fun n => ∫ x, ‖g n x - f x‖ ∂μ) atTop (nhds 0) := by
    have h := tendsto_lpNorm_zero_of_tendsto_eLpNorm_zero hbound
    have heq : (fun n => ∫ x, ‖g n x - f x‖ ∂μ) =
        (fun n => lpNorm (fun x => g n x - f x) 1 μ) := by
      funext n
      rw [lpNorm_one_eq_integral_norm]
      exact (hdiff n).aestronglyMeasurable
    rw [heq]
    exact h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hnorm (Eventually.of_forall (fun _ => norm_nonneg _))
  filter_upwards [] with n
  exact norm_integral_le_integral_norm _

private theorem mollify_memLp_two
    {f : Vec 3 → ℝ} (hf : MemLp f 2 (volume : Measure (Vec 3)))
    {ε : ℝ} (hε : 0 < ε) :
    MemLp (mollify f ε hε) 2 (volume : Measure (Vec 3)) := by
  have hconv := young_convolution_nonneg_integral_one_of_aemeasurable
    (p := (2 : ENNReal)) (by norm_num) ENNReal.coe_ne_top
    (mollifier_nonneg hε)
    ((mollifier_contDiff hε (n := 0)).continuous.integrable_of_hasCompactSupport
      (mollifier_hasCompactSupport hε))
    (mollifier_integral_one hε)
    (mollifier_contDiff hε (n := 0)).continuous.measurable
    hf.aestronglyMeasurable.aemeasurable
  rw [memLp_iff]
  simpa [mollify] using hconv.trans_lt hf

theorem sobolevPoincare_L6_ball_weak_inner
    (x₀ : Vec 3) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s < r)
    (u : H1Function (euclideanBall x₀ r)) :
    lpNormOn 6 (euclideanBall x₀ s)
        (fun x => u.toFun x -
          average (volume.restrict (euclideanBall x₀ s)) u.toFun) ≤
      sobolevPoincareL6Constant *
        weakGradientLpNormOn 2 (euclideanBall x₀ s) u.grad := by
  let U : Set (Vec 3) := euclideanBall x₀ r
  let B : Set (Vec 3) := euclideanBall x₀ s
  let K : Set (Vec 3) := euclideanClosedBall x₀ s
  have hUopen : IsOpen U := by
    change IsOpen {x | euclideanSqDist x x₀ < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hBopen : IsOpen B := by
    change IsOpen {x | euclideanSqDist x x₀ < s ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hBsubK : B ⊆ K := by
    intro x hx
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hs.le).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hx).le
  have hKsubU : K ⊆ U := by
    exact euclideanClosedBall_subset_euclideanBall hs.le hsr
  have hKcompact : IsCompact K := by
    simpa [K] using isCompact_euclideanClosedBall x₀ hs.le
  let μB : Measure (Vec 3) := volume.restrict B
  have hBmetric : B ⊆ Metric.ball x₀ s := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    exact (native_norm_le_euclidean_norm (x - x₀)).trans_lt
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hx)
  have hBfinite : volume B < ∞ :=
    (measure_mono hBmetric).trans_lt MeasureTheory.measure_ball_lt_top
  let _ : IsFiniteMeasure μB := by
    refine ⟨?_⟩
    simpa [μB, Measure.restrict_apply_univ, hBmeas] using hBfinite
  let ε₀ : ℝ := (r - s) / (2 * Real.sqrt 3)
  let ε : ℕ → ℝ := fun n => ε₀ / ((n : ℝ) + 1)
  have hsqrt : 0 < Real.sqrt 3 := by positivity
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    exact div_pos hε₀ (by positivity)
  have hε_le : ∀ n, ε n ≤ ε₀ := by
    intro n
    dsimp [ε]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hden).2
    nlinarith only [hε₀.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hε_tendsto : Tendsto ε atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      simpa only [add_comm] using
        (tendsto_atTop_add_const_left atTop (1 : ℝ)
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [ε, div_eq_mul_inv] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ε₀) atTop (nhds ε₀)).mul hinv)
  have hsqrtε : ∀ n, Real.sqrt 3 * ε n ≤ (r - s) / 2 := by
    intro n
    calc
      Real.sqrt 3 * ε n ≤ Real.sqrt 3 * ε₀ :=
        mul_le_mul_of_nonneg_left (hε_le n) hsqrt.le
      _ = (r - s) / 2 := by
        dsimp [ε₀]
        field_simp [ne_of_gt hsqrt]
  have hclosed_subset : ∀ n, ∀ x ∈ K, Metric.closedBall x (ε n) ⊆ U := by
    intro n x hx y hy
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
    have hxy : ‖y - x‖ ≤ ε n := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hx0 : vecEuclideanNorm (x - x₀) ≤ s :=
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hs.le).1 hx
    have hyx : vecEuclideanNorm (y - x) ≤ Real.sqrt 3 * ‖y - x‖ :=
      native_euclidean_norm_le_sqrt_three_norm (y - x)
    have hsum : vecEuclideanNorm (y - x₀) ≤
        Real.sqrt 3 * ‖y - x‖ + vecEuclideanNorm (x - x₀) := by
      calc
        vecEuclideanNorm (y - x₀) = vecEuclideanNorm ((y - x) + (x - x₀)) := by
          congr 1
          abel
        _ ≤ vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) :=
          native_euclidean_norm_add_le _ _
        _ ≤ Real.sqrt 3 * ‖y - x‖ + vecEuclideanNorm (x - x₀) :=
          by simpa [add_comm] using add_le_add_right hyx (vecEuclideanNorm (x - x₀))
    calc
      vecEuclideanNorm (y - x₀) ≤ Real.sqrt 3 * ε n + s := by
        exact hsum.trans (add_le_add (mul_le_mul_of_nonneg_left hxy hsqrt.le) hx0)
      _ ≤ (r + s) / 2 := by linarith only [hsqrtε n]
      _ < r := by linarith only [hsr]
  have huExt : MemLp (U.indicator u.toFun) 2 (volume : Measure (Vec 3)) := by
    exact (memLp_indicator_iff_restrict hUmeas).2 u.memL2
  have hgExt (i : Fin 3) :
      MemLp (U.indicator (fun x => u.grad x i)) 2
        (volume : Measure (Vec 3)) := by
    exact (memLp_indicator_iff_restrict hUmeas).2 (u.grad_memL2 i)
  have hweakExt (i : Fin 3) :
      HasWeakPartialDerivOn U i (U.indicator u.toFun)
        (U.indicator (fun x => u.grad x i)) := by
    intro φ hφ hcompact hsupport
    calc
      ∫ x in U, U.indicator u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume =
          ∫ x in U, u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
            apply MeasureTheory.setIntegral_congr_fun hUmeas
            intro x hx
            simp [Set.indicator_of_mem hx]
      _ = -∫ x in U, u.grad x i * φ x ∂volume :=
        u.hasWeakPartialDerivOn i φ hφ hcompact hsupport
      _ = -∫ x in U, U.indicator (fun x => u.grad x i) x * φ x ∂volume := by
            congr 1
            apply MeasureTheory.setIntegral_congr_fun hUmeas
            intro x hx
            simp [Set.indicator_of_mem hx]
  let v : ℕ → Vec 3 → ℝ := fun n =>
    mollify (U.indicator u.toFun) (ε n) (hε_pos n)
  let w : Fin 3 → ℕ → Vec 3 → ℝ := fun i n =>
    mollify (U.indicator (fun x => u.grad x i)) (ε n) (hε_pos n)
  have hvMem (n : ℕ) : MemLp (v n) 2 (volume : Measure (Vec 3)) := by
    exact mollify_memLp_two huExt (hε_pos n)
  have hwMem (i : Fin 3) (n : ℕ) :
      MemLp (w i n) 2 (volume : Measure (Vec 3)) := by
    exact mollify_memLp_two (hgExt i) (hε_pos n)
  have hderiv (n : ℕ) (i : Fin 3) {x : Vec 3} (hx : x ∈ K) :
      (fderiv ℝ (v n) x) (basisVec i) = w i n x := by
    dsimp [v, w]
    exact fderiv_mollify_eq_mollify_on_compact hUopen hKcompact
      (huExt.locallyIntegrable (by norm_num))
      ((hgExt i).locallyIntegrable (by norm_num))
      (hweakExt i) (hε_pos n) (hclosed_subset n) hx
  let D : ℕ → Vec 3 → Vec 3 := fun n x i =>
    (fderiv ℝ (v n) x) (basisVec i)
  let W : ℕ → Vec 3 → Vec 3 := fun n x i => w i n x
  have hWmem (n : ℕ) : MemLp (W n) 2 (volume : Measure (Vec 3)) := by
    apply (memLp_pi_iff).2
    intro i
    simpa [W] using hwMem i n
  have hDmem (n : ℕ) : MemLp (D n) 2 μB := by
    have hWloc : MemLp (W n) 2 μB :=
      (hWmem n).mono_measure Measure.restrict_le_self
    apply (memLp_congr_ae ?_).2 hWloc
    filter_upwards [ae_restrict_mem hBmeas] with x hx
    funext i
    exact hderiv n i (hBsubK hx)
  have hGmem : MemLp u.grad 2 μB := by
    apply (memLp_pi_iff).2
    intro i
    exact (u.grad_memL2 i).mono_measure
      (Measure.restrict_mono_set volume (hBsubK.trans hKsubU))
  have hvalGlobal : Tendsto
      (fun n => eLpNorm (fun x => v n x - U.indicator u.toFun x) 2 volume)
        atTop (nhds 0) := by
    simpa [v, sub_eq_add_neg] using
      (tendsto_eLpNorm_sub_zero_mollify (p := (2 : ENNReal)) (by norm_num)
        ENNReal.coe_ne_top huExt hε_tendsto hε_pos)
  have hvalLocal : Tendsto
      (fun n => eLpNorm (fun x => v n x - u.toFun x) 2 μB)
        atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hvalGlobal
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [] with n
    calc
      eLpNorm (fun x => v n x - u.toFun x) 2 μB =
          eLpNorm (fun x => v n x - U.indicator u.toFun x) 2 μB := by
            apply eLpNorm_congr_ae
            filter_upwards [ae_restrict_mem hBmeas] with x hx
            simp [Set.indicator_of_mem (hKsubU (hBsubK hx))]
      _ ≤ eLpNorm (fun x => v n x - U.indicator u.toFun x) 2 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
  have hgradGlobal (i : Fin 3) : Tendsto
      (fun n => eLpNorm (fun x => w i n x - U.indicator (fun y => u.grad y i) x)
        2 volume) atTop (nhds 0) := by
    simpa [w, sub_eq_add_neg] using
      (tendsto_eLpNorm_sub_zero_mollify (p := (2 : ENNReal)) (by norm_num)
        ENNReal.coe_ne_top (hgExt i) hε_tendsto hε_pos)
  have hgradLocal (i : Fin 3) : Tendsto
      (fun n => eLpNorm (fun x => w i n x - u.grad x i) 2 μB)
        atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (hgradGlobal i)
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [] with n
    calc
      eLpNorm (fun x => w i n x - u.grad x i) 2 μB =
          eLpNorm (fun x => w i n x - U.indicator (fun y => u.grad y i) x)
            2 μB := by
            apply eLpNorm_congr_ae
            filter_upwards [ae_restrict_mem hBmeas] with x hx
            simp [Set.indicator_of_mem (hKsubU (hBsubK hx))]
      _ ≤ eLpNorm
          (fun x => w i n x - U.indicator (fun y => u.grad y i) x) 2 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
  have hWerr : Tendsto
      (fun n => eLpNorm (fun x => W n x - u.grad x) 2 μB)
        atTop (nhds 0) := by
    have hsum : Tendsto
        (fun n => ∑ i : Fin 3,
          eLpNorm (fun x => w i n x - u.grad x i) 2 μB)
          atTop (nhds 0) := by
      exact tendsto_sum_zero_fin_three_weak (fun i => hgradLocal i)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [] with n
    have hWloc : MemLp (W n) 2 μB :=
      (hWmem n).mono_measure Measure.restrict_le_self
    calc
      eLpNorm (fun x => W n x - u.grad x) 2 μB ≤
          ∑ i : Fin 3, eLpNorm (fun x => (W n x - u.grad x) i) 2 μB := by
            apply eLpNorm_pi_le_sum_weak
            exact (hWloc.sub hGmem).aestronglyMeasurable
      _ = ∑ i : Fin 3, eLpNorm (fun x => w i n x - u.grad x i) 2 μB := by
            congr 1
  have hDerr : Tendsto
      (fun n => eLpNorm (fun x => D n x - u.grad x) 2 μB)
        atTop (nhds 0) := by
    apply hWerr.congr'
    exact Eventually.of_forall (fun n => by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hBmeas] with x hx
      funext i
      simp only [Pi.sub_apply, D, W]
      simpa using congrArg (fun z => z - u.grad x i)
        (hderiv n i (hBsubK hx)).symm)
  have hgradTendsto : Tendsto
      (fun n => eLpNorm (D n) 2 μB) atTop
        (nhds (eLpNorm u.grad 2 μB)) :=
    eLpNorm_tendsto_of_diff_weak hGmem (fun n => hDmem n) hDerr
  have huB : MemLp u.toFun 2 μB :=
    u.memL2.mono_measure (Measure.restrict_mono_set volume (hBsubK.trans hKsubU))
  have hvB (n : ℕ) : MemLp (v n) 2 μB :=
    (hvMem n).mono_measure Measure.restrict_le_self
  have hInt : Tendsto
      (fun n => ∫ x, v n x - u.toFun x ∂μB) atTop (nhds 0) :=
    integral_sub_tendsto_zero_of_eLpNorm_two huB hvB hvalLocal
  have havgDiff (n : ℕ) :
      average μB (v n) - average μB u.toFun =
        (μB Set.univ).toReal⁻¹ * ∫ x, v n x - u.toFun x ∂μB := by
    rw [← average_sub ((hvB n).integrable (by norm_num))
      (huB.integrable (by norm_num)), average_eq]
    simp [Measure.real, smul_eq_mul]
  have havg : Tendsto (fun n => average μB (v n)) atTop
      (nhds (average μB u.toFun)) := by
    have hdiff : Tendsto
        (fun n => average μB (v n) - average μB u.toFun) atTop (nhds 0) := by
      rw [show (fun n => average μB (v n) - average μB u.toFun) =
          (fun n => (μB Set.univ).toReal⁻¹ *
            ∫ x, v n x - u.toFun x ∂μB) by
            funext n; exact havgDiff n]
      simpa using (tendsto_const_nhds.mul hInt)
    have hsum := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => average μB u.toFun)
        atTop (nhds (average μB u.toFun))).add hdiff
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  let F : ℕ → Vec 3 → ℝ := fun n =>
    fun x => v n x - average μB (v n)
  let F₀ : Vec 3 → ℝ := fun x => u.toFun x - average μB u.toFun
  obtain ⟨ns, hns_mono, hns_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (μ := μB) (p := (2 : ENNReal))
      (by norm_num) hvalLocal).exists_seq_tendsto_ae
  have havg_sub : Tendsto (fun k => average μB (v (ns k))) atTop
      (nhds (average μB u.toFun)) := havg.comp hns_mono.tendsto_atTop
  have hFae : ∀ᵐ x ∂μB, Tendsto (fun k => F (ns k) x) atTop (nhds (F₀ x)) := by
    filter_upwards [hns_ae] with x hx
    simpa [F, F₀] using hx.sub havg_sub
  have hleft : eLpNorm F₀ 6 μB ≤
      atTop.liminf (fun k => eLpNorm (F (ns k)) 6 μB) := by
    apply MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
    · intro k
      exact ((hvB (ns k)).sub (memLp_const (μ := μB) _)).aestronglyMeasurable
    · exact (huB.sub (memLp_const (μ := μB) _)).aestronglyMeasurable
    · exact hFae
  have hD_eq (n : ℕ) : D n = classicalGradient (v n) := by
    funext x i
    simp [D, classicalGradient_apply]
  have hineq (n : ℕ) : eLpNorm (F n) 6 μB ≤
      sobolevPoincareL6Constant * eLpNorm (D n) 2 μB := by
    have hsmooth := sobolevPoincare_L6_ball x₀ hs (v n)
      (mollify_contDiff (hε_pos n) (huExt.locallyIntegrable (by norm_num)) (n := 1))
    calc
      eLpNorm (F n) 6 μB =
          lpNormOn 6 B (fun x => v n x - average μB (v n)) := by
            simp [F, μB, lpNormOn]
      _ ≤ sobolevPoincareL6Constant * gradientLpNormOn 2 B (v n) := by
        simpa [μB] using hsmooth
      _ = sobolevPoincareL6Constant * eLpNorm (D n) 2 μB := by
        rw [hD_eq n]
        rfl
  have hRhs : Tendsto
      (fun n => sobolevPoincareL6Constant * eLpNorm (D n) 2 μB) atTop
        (nhds (sobolevPoincareL6Constant * eLpNorm u.grad 2 μB)) :=
    by
      have hCtop : sobolevPoincareL6Constant ≠ ∞ := by
        unfold sobolevPoincareL6Constant
        apply ENNReal.mul_ne_top
        · unfold localSobolevConstant
          finiteness
        · apply ENNReal.add_ne_top.mpr
          constructor
          · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
            apply ENNReal.add_ne_top.mpr
            constructor
            · norm_num
            · apply ENNReal.mul_ne_top
              · norm_num
              · simp [euclideanBallPoincareConstant]
          · apply ENNReal.mul_ne_top
            · norm_num
            · apply ENNReal.mul_ne_top
              · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
                norm_num
              · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
                simp [euclideanBallPoincareConstant]
      simpa using ENNReal.Tendsto.const_mul hgradTendsto (Or.inr hCtop)
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδpos hδtop
  have hRhsSub := hRhs.comp hns_mono.tendsto_atTop
  have hupper : ∀ᶠ k in atTop,
      sobolevPoincareL6Constant * eLpNorm (D (ns k)) 2 μB <
        sobolevPoincareL6Constant * eLpNorm u.grad 2 μB + δ :=
    (tendsto_order.1 hRhsSub).2 _ (by
      have hlt : sobolevPoincareL6Constant * eLpNorm u.grad 2 μB <
          sobolevPoincareL6Constant * eLpNorm u.grad 2 μB + (δ : ℝ≥0∞) :=
        ENNReal.lt_add_right (ne_of_lt hδtop)
          (ENNReal.coe_ne_zero.mpr hδpos.ne')
      exact hlt)
  have hlimδ : atTop.liminf (fun k => eLpNorm (F (ns k)) 6 μB) ≤
      sobolevPoincareL6Constant * eLpNorm u.grad 2 μB + δ :=
    liminf_le_of_frequently_le'
      (hupper.mono (fun k hk => (hineq (ns k)).trans hk.le)).frequently
  simpa [F₀, μB, lpNormOn, weakGradientLpNormOn] using hleft.trans hlimδ

theorem sobolevPoincare_L6_ball_weak
    (x₀ : Vec 3) {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ r)) :
    lpNormOn 6 (euclideanBall x₀ r)
        (fun x => u.toFun x -
          average (volume.restrict (euclideanBall x₀ r)) u.toFun) ≤
      sobolevPoincareL6Constant *
        weakGradientLpNormOn 2 (euclideanBall x₀ r) u.grad := by
  let B : Set (Vec 3) := euclideanBall x₀ r
  let ρ : ℕ → ℝ := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 2)
  let s : ℕ → ℝ := fun n => r * ρ n
  let Bn : ℕ → Set (Vec 3) := fun n => euclideanBall x₀ (s n)
  have hρ_pos (n : ℕ) : 0 < ρ n := by
    dsimp [ρ]
    positivity
  have hρ_lt (n : ℕ) : ρ n < 1 := by
    dsimp [ρ]
    apply (div_lt_one₀ (by positivity)).2
    norm_num
  have hs_pos (n : ℕ) : 0 < s n := by
    dsimp [s]
    exact mul_pos hr (hρ_pos n)
  have hs_lt (n : ℕ) : s n < r := by
    dsimp [s]
    simpa using mul_lt_mul_of_pos_left (hρ_lt n) hr
  have hρ_mono : Monotone ρ := by
    intro n m hnm
    dsimp [ρ]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
    calc
      ((n : ℝ) + 1) * ((m : ℝ) + 2) ≤
          ((n : ℝ) + 1) * ((m : ℝ) + 2) + ((m : ℝ) - n) :=
        le_add_of_nonneg_right (sub_nonneg.mpr hcast)
      _ = ((m : ℝ) + 1) * ((n : ℝ) + 2) := by ring
  have hs_mono : Monotone s := by
    intro n m hnm
    exact mul_le_mul_of_nonneg_left (hρ_mono hnm) hr.le
  have hBn_mono : Monotone Bn := by
    intro n m hnm x hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (hs_pos m)).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (hs_pos n)).1 hx).trans_le
      (hs_mono hnm)
  have hρ_tendsto : Tendsto ρ atTop (nhds 1) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
      simpa only [add_comm] using
        (tendsto_atTop_add_const_left atTop (2 : ℝ)
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hden
    have hlim : Tendsto
        (fun n : ℕ => (1 : ℝ) - ((n : ℝ) + 2)⁻¹) atTop (nhds 1) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hinv)
    convert hlim using 1
    funext n
    dsimp [ρ, div_eq_mul_inv]
    field_simp
    ring
  have hs_tendsto : Tendsto s atTop (nhds r) := by
    simpa [s] using
      (tendsto_const_nhds.mul hρ_tendsto : Tendsto
        (fun n : ℕ => r * ρ n) atTop (nhds (r * 1)))
  have hBopen : IsOpen B := by
    change IsOpen {x | euclideanSqDist x x₀ < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hBnopen (n : ℕ) : IsOpen (Bn n) := by
    change IsOpen {x | euclideanSqDist x x₀ < (s n) ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hBnmeas (n : ℕ) : MeasurableSet (Bn n) := (hBnopen n).measurableSet
  have hBn_sub_B (n : ℕ) : Bn n ⊆ B := by
    intro x hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (hs_pos n)).1 hx).trans
      (hs_lt n)
  have hB_union : (⋃ n, Bn n) = B := by
    apply Set.Subset.antisymm
    · exact iUnion_subset (fun n => hBn_sub_B n)
    · intro x hx
      have hxnorm : vecEuclideanNorm (x - x₀) < r :=
        (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
      have hev : ∀ᶠ n in atTop, vecEuclideanNorm (x - x₀) < s n :=
        hs_tendsto.eventually (Ioi_mem_nhds hxnorm)
      rcases hev.exists with ⟨n, hn⟩
      exact mem_iUnion_of_mem n
        ((mem_euclideanBall_iff_vecEuclideanNorm_lt (hs_pos n)).2 hn)
  have hBmetric : B ⊆ Metric.ball x₀ r := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    exact (native_norm_le_euclidean_norm (x - x₀)).trans_lt
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx)
  have hBfinite : volume B < ∞ :=
    (measure_mono hBmetric).trans_lt MeasureTheory.measure_ball_lt_top
  let μB : Measure (Vec 3) := volume.restrict B
  let _ : IsFiniteMeasure μB := by
    refine ⟨?_⟩
    simpa [μB, Measure.restrict_apply_univ, hBmeas] using hBfinite
  have huB : MemLp u.toFun 2 μB := by
    simpa [μB] using u.memL2
  have huB_one : IntegrableOn u.toFun B volume := by
    exact (huB.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable
      (by norm_num)
  have hnum : Tendsto
      (fun n => ∫ x in Bn n, u.toFun x ∂volume) atTop
        (nhds (∫ x in B, u.toFun x ∂volume)) := by
    have hu_union : IntegrableOn u.toFun (⋃ n, Bn n) volume := by
      rw [hB_union]
      exact huB_one
    have h := tendsto_setIntegral_of_monotone (f := u.toFun)
      (fun n => hBnmeas n) hBn_mono hu_union
    rw [hB_union] at h
    exact h
  have hB_pos : 0 < volume B := by
    exact hBopen.measure_pos volume ⟨x₀, by
      exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
        (by simpa [vecEuclideanNorm, vecNormSq, vecDot] using hr)⟩
  have hB_real_pos : 0 < (volume B).toReal :=
    ENNReal.toReal_pos hB_pos.ne' hBfinite.ne
  have hmeasure : Tendsto (fun n => (volume (Bn n)).toReal) atTop
      (nhds (volume B).toReal) := by
    have h := tendsto_measure_iUnion_atTop (μ := volume) hBn_mono
    rw [hB_union] at h
    exact (ENNReal.tendsto_toReal hBfinite.ne).comp h
  have havg : Tendsto (fun n => average (volume.restrict (Bn n)) u.toFun) atTop
      (nhds (average μB u.toFun)) := by
    have hinv : Tendsto (fun n => (volume (Bn n)).toReal⁻¹) atTop
        (nhds (volume B).toReal⁻¹) :=
      (tendsto_inv₀ hB_real_pos.ne').comp hmeasure
    have hmul := hinv.mul hnum
    have hformula (n : ℕ) :
        average (volume.restrict (Bn n)) u.toFun =
          (volume (Bn n)).toReal⁻¹ * ∫ x in Bn n, u.toFun x ∂volume := by
      change (⨍ x in Bn n, u.toFun x ∂volume) = _
      rw [MeasureTheory.setAverage_eq]
      simp [Measure.real, smul_eq_mul]
    have hformulaB : average μB u.toFun =
        (volume B).toReal⁻¹ * ∫ x in B, u.toFun x ∂volume := by
      change (⨍ x in B, u.toFun x ∂volume) = _
      rw [MeasureTheory.setAverage_eq]
      simp [Measure.real, smul_eq_mul]
    rw [show (fun n => average (volume.restrict (Bn n)) u.toFun) =
        (fun n => (volume (Bn n)).toReal⁻¹ * ∫ x in Bn n, u.toFun x ∂volume) by
          funext n; exact hformula n, hformulaB]
    exact hmul
  let F : ℕ → Vec 3 → ℝ := fun n =>
    (Bn n).indicator (fun x => u.toFun x - average (volume.restrict (Bn n)) u.toFun)
  let F₀ : Vec 3 → ℝ := B.indicator
    (fun x => u.toFun x - average μB u.toFun)
  have hFmem (n : ℕ) : MemLp (F n) 2 (volume : Measure (Vec 3)) := by
    let _ : IsFiniteMeasure (volume.restrict (Bn n)) := by
      refine ⟨?_⟩
      simpa [Measure.restrict_apply_univ, hBnmeas n] using
        (measure_mono (hBn_sub_B n)).trans_lt hBfinite
    apply (memLp_indicator_iff_restrict (hBnmeas n)).2
    exact (huB.mono_measure
      (Measure.restrict_mono_set volume (hBn_sub_B n))).sub
      (memLp_const (μ := volume.restrict (Bn n)) _)
  have hF0mem : MemLp F₀ 2 (volume : Measure (Vec 3)) := by
    apply (memLp_indicator_iff_restrict hBmeas).2
    exact huB.sub (memLp_const (μ := μB) _)
  have hFae : ∀ᵐ x ∂(volume : Measure (Vec 3)),
      Tendsto (fun n => F n x) atTop (nhds (F₀ x)) := by
    filter_upwards [] with x
    by_cases hx : x ∈ B
    · have hxnorm : vecEuclideanNorm (x - x₀) < r :=
        (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
      have hev : ∀ᶠ n in atTop, x ∈ Bn n := by
        filter_upwards [hs_tendsto.eventually (Ioi_mem_nhds hxnorm)] with n hn
        exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (hs_pos n)).2 hn
      have hsub : Tendsto
          (fun n => u.toFun x - average (volume.restrict (Bn n)) u.toFun) atTop
            (nhds (u.toFun x - average μB u.toFun)) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => u.toFun x) atTop (nhds (u.toFun x))).sub havg
      have hF0x : F₀ x = u.toFun x - average μB u.toFun := by
        simp [F₀, hx]
      rw [hF0x]
      exact hsub.congr' (hev.mono (fun n hn => by simp [F, hn]))
    · have hnot (n : ℕ) : x ∉ Bn n := fun hxn => hx (hBn_sub_B n hxn)
      simp [F, F₀, hx, hnot]
  have hleft : eLpNorm F₀ 6 volume ≤
      atTop.liminf (fun n => eLpNorm (F n) 6 volume) := by
    apply MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
    · intro n
      exact (hFmem n).aestronglyMeasurable
    · exact hF0mem.aestronglyMeasurable
    · exact hFae
  have hineq (n : ℕ) : eLpNorm (F n) 6 volume ≤
      sobolevPoincareL6Constant *
        weakGradientLpNormOn 2 B u.grad := by
    have hinner := sobolevPoincare_L6_ball_weak_inner x₀ hr (hs_pos n) (hs_lt n) u
    calc
      eLpNorm (F n) 6 volume =
          lpNormOn 6 (Bn n)
            (fun x => u.toFun x -
              average (volume.restrict (Bn n)) u.toFun) := by
        simp [F, lpNormOn,
          eLpNorm_indicator_eq_eLpNorm_restrict (hBnmeas n)]
      _ ≤ sobolevPoincareL6Constant * weakGradientLpNormOn 2 (Bn n) u.grad := by
        simpa [lpNormOn, weakGradientLpNormOn] using hinner
      _ ≤ sobolevPoincareL6Constant * weakGradientLpNormOn 2 B u.grad := by
        gcongr
        exact eLpNorm_mono_measure _
          (Measure.restrict_mono_set volume (hBn_sub_B n))
  have hlim : atTop.liminf (fun n => eLpNorm (F n) 6 volume) ≤
      sobolevPoincareL6Constant * weakGradientLpNormOn 2 B u.grad :=
    liminf_le_of_frequently_le'
      (Frequently.of_forall (fun n => hineq n))
  have hF0norm : eLpNorm F₀ 6 volume =
      lpNormOn 6 B (fun x => u.toFun x - average μB u.toFun) := by
    simp [F₀, lpNormOn,
      eLpNorm_indicator_eq_eLpNorm_restrict hBmeas]
  rw [hF0norm] at hleft
  simpa [B, μB, lpNormOn, weakGradientLpNormOn] using hleft.trans hlim

end
end CKN
