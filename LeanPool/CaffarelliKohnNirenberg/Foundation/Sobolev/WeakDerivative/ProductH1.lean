/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Product H1

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Convolution Pointwise

namespace CKN

noncomputable section

private theorem eLpNorm_mul_two_two_le
    {f g : Vec 3 → ℝ} {μ : Measure (Vec 3)}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x * g x) 1 μ ≤
      eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have h := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (μ := μ) (f := f) (g := g) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
    (r := (1 : ℝ≥0∞)) (b := fun a b : ℝ => a * b) (c := (1 : NNReal))
    (by exact continuous_mul) hf hg (by
      filter_upwards [] with x
      simp only [one_mul]
      simp [nnnorm_mul])
  simpa using h

private theorem tendsto_eLpNorm_mul_sub_mul_zero
    {f g : Vec 3 → ℝ} {F G : ℕ → Vec 3 → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hF : ∀ n, MemLp (F n) 2 volume)
    (hG : ∀ n, MemLp (G n) 2 volume)
    (hFzero : Tendsto
      (fun n => eLpNorm (fun x => F n x - f x) 2 volume)
      atTop (nhds 0))
    (hGzero : Tendsto
      (fun n => eLpNorm (fun x => G n x - g x) 2 volume)
      atTop (nhds 0)) :
    Tendsto
      (fun n => eLpNorm (fun x => F n x * G n x - f x * g x) 1 volume)
      atTop (nhds 0) := by
  let A : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => F n x - f x) 2 volume
  let B : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => G n x - g x) 2 volume
  have hA : Tendsto A atTop (nhds 0) := by
    simpa only [A] using hFzero
  have hB : Tendsto B atTop (nhds 0) := by
    simpa only [B] using hGzero
  have hFbound (n : ℕ) :
      eLpNorm (F n) 2 volume ≤ A n + eLpNorm f 2 volume := by
    have hsum := MeasureTheory.eLpNorm_add_le
      (f := fun x => F n x - f x) (g := f)
      (μ := volume) (p := (2 : ℝ≥0∞)) (by norm_num)
    calc
      eLpNorm (fun x => F n x) 2 volume =
          eLpNorm ((fun x => F n x - f x) + f) 2 volume := by
        congr 1
        funext x
        change F n x = (F n x - f x) + f x
        ring
      _ ≤ eLpNorm (fun x => F n x - f x) 2 volume +
          eLpNorm f 2 volume := hsum
      _ = A n + eLpNorm f 2 volume := by rfl
  have hGbound (n : ℕ) :
      eLpNorm (G n) 2 volume ≤ B n + eLpNorm g 2 volume := by
    have hsum := MeasureTheory.eLpNorm_add_le
      (f := fun x => G n x - g x) (g := g)
      (μ := volume) (p := (2 : ℝ≥0∞)) (by norm_num)
    calc
      eLpNorm (fun x => G n x) 2 volume =
          eLpNorm ((fun x => G n x - g x) + g) 2 volume := by
        congr 1
        funext x
        change G n x = (G n x - g x) + g x
        ring
      _ ≤ eLpNorm (fun x => G n x - g x) 2 volume +
          eLpNorm g 2 volume := hsum
      _ = B n + eLpNorm g 2 volume := by rfl
  have hlimit : Tendsto
      (fun n => A n * (B n + eLpNorm g 2 volume) +
        eLpNorm f 2 volume * B n) atTop (nhds 0) := by
    have hBg : Tendsto (fun n => B n + eLpNorm g 2 volume) atTop
        (nhds (eLpNorm g 2 volume)) := by
      simpa only [zero_add] using hB.add tendsto_const_nhds
    have hfirst : Tendsto
        (fun n => A n * (B n + eLpNorm g 2 volume)) atTop (nhds 0) := by
      have h := ENNReal.Tendsto.mul hA
        (Or.inr hg.eLpNorm_lt_top.ne) hBg (Or.inr ENNReal.zero_ne_top)
      simpa only [zero_mul, zero_add] using h
    have hsecond : Tendsto
        (fun n => eLpNorm f 2 volume * B n) atTop (nhds 0) := by
      have h := ENNReal.Tendsto.const_mul hB
        (Or.inr hf.eLpNorm_lt_top.ne)
      simpa only [mul_zero] using h
    simpa only [zero_add, add_zero] using hfirst.add hsecond
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [] with n
  have hfirst0 := eLpNorm_mul_two_two_le
    ((hF n).sub hf).aestronglyMeasurable (hG n).aestronglyMeasurable
  have hFsub : F n - f = (fun x => F n x - f x) := by
    funext x
    rfl
  rw [hFsub] at hfirst0
  have hfirst := hfirst0
  have hsecond0 := eLpNorm_mul_two_two_le
    hf.aestronglyMeasurable ((hG n).sub hg).aestronglyMeasurable
  have hGsub : G n - g = (fun x => G n x - g x) := by
    funext x
    rfl
  rw [hGsub] at hsecond0
  have hsecond := hsecond0
  have hsum := MeasureTheory.eLpNorm_add_le
    (f := fun x => (F n x - f x) * G n x)
    (g := fun x => f x * (G n x - g x))
    (μ := volume) (p := (1 : ℝ≥0∞)) (by norm_num)
  have hdecomp :
      (fun x => F n x * G n x - f x * g x) =
        (fun x => (F n x - f x) * G n x) +
          (fun x => f x * (G n x - g x)) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have htarget : eLpNorm (fun x => F n x * G n x - f x * g x) 1 volume ≤
      A n * (B n + eLpNorm g 2 volume) + eLpNorm f 2 volume * B n := by
    calc
      eLpNorm (fun x => F n x * G n x - f x * g x) 1 volume =
        eLpNorm ((fun x => (F n x - f x) * G n x) +
          (fun x => f x * (G n x - g x))) 1 volume := by
        exact congrArg (fun q => eLpNorm q 1 volume) hdecomp
      _ ≤
        eLpNorm (fun x => (F n x - f x) * G n x) 1 volume +
          eLpNorm (fun x => f x * (G n x - g x)) 1 volume := hsum
      _ ≤ A n * (B n + eLpNorm g 2 volume) +
        eLpNorm f 2 volume * B n := by
        exact (add_le_add hfirst hsecond).trans (add_le_add
          (by simpa only [A] using
            mul_le_mul_of_nonneg_left (hGbound n) (by positivity))
          (by simpa only [B] using (le_refl _)))
  exact htarget

private theorem tendsto_eLpNorm_mul_test_zero
    {f : Vec 3 → ℝ} {F : ℕ → Vec 3 → ℝ} {φ : Vec 3 → ℝ}
    (_ : MemLp f 1 volume) (_ : ∀ n, MemLp (F n) 1 volume)
    (hF : Tendsto (fun n => eLpNorm (fun x => F n x - f x) 1 volume)
      atTop (nhds 0))
    (hφ : MemLp φ ∞ volume) :
    Tendsto (fun n => eLpNorm (fun x => F n x * φ x - f x * φ x) 1 volume)
      atTop (nhds 0) := by
  have hφbound : eLpNorm φ ∞ volume < ∞ := hφ.eLpNorm_lt_top
  have hlimit : Tendsto
      (fun n => eLpNorm φ ∞ volume *
        eLpNorm (fun x => F n x - f x) 1 volume) atTop (nhds 0) := by
    have h := ENNReal.Tendsto.const_mul hF
      (Or.inr hφbound.ne)
    simpa only [mul_zero] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [] with n
  have hprod := MeasureTheory.eLpNorm_le_eLpNorm_top_mul_eLpNorm
    (μ := volume) (f := φ) (g := fun x => F n x - f x)
    (p := (1 : ℝ≥0∞)) (b := fun a b : ℝ => a * b) (c := (1 : NNReal))
    (by exact continuous_mul) hφ.aestronglyMeasurable (by
      filter_upwards [] with x
      simp [nnnorm_mul])
  have hfun : (fun x => F n x * φ x - f x * φ x) =
      (fun x => φ x * (F n x - f x)) := by
    funext x
    ring
  rw [hfun]
  simpa using hprod

private theorem HasWeakGradientOn.mul_of_memLp_two_global
    {U : Set (Vec 3)} (hU : IsOpen U)
    {u v : Vec 3 → ℝ} {Du Dv : Vec 3 → Vec 3}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hDu : ∀ i : Fin 3, MemLp (fun x => Du x i) 2 volume)
    (hDv : ∀ i : Fin 3, MemLp (fun x => Dv x i) 2 volume)
    (hwu : HasWeakGradientOn U u Du)
    (hwv : HasWeakGradientOn U v Dv) :
    HasWeakGradientOn U (fun x => u x * v x)
      (fun x i => Du x i * v x + u x * Dv x i) := by
  intro i φ hφ hφCompact hφU
  let K : Set (Vec 3) := tsupport φ
  have hK : IsCompact K := hφCompact.isCompact
  have hKU : K ⊆ U := hφU
  obtain ⟨ε₀, hε₀, hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKε₀ : ∀ x ∈ K, Metric.closedBall x ε₀ ⊆ U := by
    intro x hx
    exact (Metric.closedBall_subset_cthickening hx ε₀).trans hthick
  let ε : ℕ → ℝ := fun n => ε₀ / ((n : ℝ) + 2)
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hε_le : ∀ n, ε n ≤ ε₀ := by
    intro n
    dsimp [ε]
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hden : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith only [hn]
    simpa only [div_one] using
      (div_le_div_of_nonneg_left hε₀.le (by positivity) hden)
  have hε_tendsto : Tendsto ε atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
      simpa only [add_comm] using
        (tendsto_atTop_add_const_left atTop (2 : ℝ)
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹)
        atTop (nhds 0) := tendsto_inv_atTop_zero.comp hden
    have hmul :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ε₀) atTop (nhds ε₀)).mul hinv
    simpa only [ε, div_eq_mul_inv, mul_zero] using hmul
  have huLoc : LocallyIntegrable u volume := hu.locallyIntegrable (by norm_num)
  have hvLoc : LocallyIntegrable v volume := hv.locallyIntegrable (by norm_num)
  have hDuLoc : ∀ j : Fin 3, LocallyIntegrable (fun x => Du x j) volume := by
    intro j
    exact (hDu j).locallyIntegrable (by norm_num)
  have hDvLoc : ∀ j : Fin 3, LocallyIntegrable (fun x => Dv x j) volume := by
    intro j
    exact (hDv j).locallyIntegrable (by norm_num)
  let Uₙ : ℕ → Vec 3 → ℝ := fun n => mollify u (ε n) (hε_pos n)
  let Vₙ : ℕ → Vec 3 → ℝ := fun n => mollify v (ε n) (hε_pos n)
  let DUₙ : ℕ → Vec 3 → ℝ := fun n =>
    mollify (fun x => Du x i) (ε n) (hε_pos n)
  let DVₙ : ℕ → Vec 3 → ℝ := fun n =>
    mollify (fun x => Dv x i) (ε n) (hε_pos n)
  have hUmem : ∀ n, MemLp (Uₙ n) 2 volume := by
    intro n
    apply (memLp_iff).2
    have hbound := young_convolution_nonneg_integral_one_of_aemeasurable
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (mollifier_nonneg (hε_pos n))
      (integrable_of_integral_eq_one (mollifier_integral_one (hε_pos n)))
      (mollifier_integral_one (hε_pos n))
      (mollifier_contDiff (hε_pos n) (n := 0)).continuous.measurable
        hu.aestronglyMeasurable.aemeasurable
    have hbound' : eLpNorm (Uₙ n) 2 volume ≤ eLpNorm u 2 volume := by
      simpa only [Uₙ, mollify] using hbound
    exact hbound'.trans_lt hu.eLpNorm_lt_top
  have hVmem : ∀ n, MemLp (Vₙ n) 2 volume := by
    intro n
    apply (memLp_iff).2
    have hbound := young_convolution_nonneg_integral_one_of_aemeasurable
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (mollifier_nonneg (hε_pos n))
      (integrable_of_integral_eq_one (mollifier_integral_one (hε_pos n)))
      (mollifier_integral_one (hε_pos n))
      (mollifier_contDiff (hε_pos n) (n := 0)).continuous.measurable
        hv.aestronglyMeasurable.aemeasurable
    have hbound' : eLpNorm (Vₙ n) 2 volume ≤ eLpNorm v 2 volume := by
      simpa only [Vₙ, mollify] using hbound
    exact hbound'.trans_lt hv.eLpNorm_lt_top
  have hDUmem : ∀ n, MemLp (DUₙ n) 2 volume := by
    intro n
    apply (memLp_iff).2
    have hbound := young_convolution_nonneg_integral_one_of_aemeasurable
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (mollifier_nonneg (hε_pos n))
      (integrable_of_integral_eq_one (mollifier_integral_one (hε_pos n)))
      (mollifier_integral_one (hε_pos n))
      (mollifier_contDiff (hε_pos n) (n := 0)).continuous.measurable
        (hDu i).aestronglyMeasurable.aemeasurable
    have hbound' : eLpNorm (DUₙ n) 2 volume ≤ eLpNorm (fun x => Du x i) 2 volume := by
      simpa only [DUₙ, mollify] using hbound
    exact hbound'.trans_lt (hDu i).eLpNorm_lt_top
  have hDVmem : ∀ n, MemLp (DVₙ n) 2 volume := by
    intro n
    apply (memLp_iff).2
    have hbound := young_convolution_nonneg_integral_one_of_aemeasurable
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (mollifier_nonneg (hε_pos n))
      (integrable_of_integral_eq_one (mollifier_integral_one (hε_pos n)))
      (mollifier_integral_one (hε_pos n))
      (mollifier_contDiff (hε_pos n) (n := 0)).continuous.measurable
        (hDv i).aestronglyMeasurable.aemeasurable
    have hbound' : eLpNorm (DVₙ n) 2 volume ≤ eLpNorm (fun x => Dv x i) 2 volume := by
      simpa only [DVₙ, mollify] using hbound
    exact hbound'.trans_lt (hDv i).eLpNorm_lt_top
  have hUzero : Tendsto
      (fun n => eLpNorm (fun x => Uₙ n x - u x) 2 volume)
      atTop (nhds 0) := by
    simpa only [Uₙ] using
      tendsto_eLpNorm_sub_zero_mollify (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        hu hε_tendsto hε_pos
  have hVzero : Tendsto
      (fun n => eLpNorm (fun x => Vₙ n x - v x) 2 volume)
      atTop (nhds 0) := by
    simpa only [Vₙ] using
      tendsto_eLpNorm_sub_zero_mollify (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        hv hε_tendsto hε_pos
  have hDUzero : Tendsto
      (fun n => eLpNorm (fun x => DUₙ n x - Du x i) 2 volume)
      atTop (nhds 0) := by
    simpa only [DUₙ] using
      tendsto_eLpNorm_sub_zero_mollify (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        (hDu i) hε_tendsto hε_pos
  have hDVzero : Tendsto
      (fun n => eLpNorm (fun x => DVₙ n x - Dv x i) 2 volume)
      atTop (nhds 0) := by
    simpa only [DVₙ] using
      tendsto_eLpNorm_sub_zero_mollify (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        (hDv i) hε_tendsto hε_pos
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ENNReal.HolderConjugate.instTwoTwo
  have hUVmem : ∀ n, MemLp (fun x => Uₙ n x * Vₙ n x) 1 volume := by
    intro n
    exact (hUmem n).mul (hVmem n)
  have hDUVmem : ∀ n, MemLp (fun x => DUₙ n x * Vₙ n x) 1 volume := by
    intro n
    exact (hDUmem n).mul (hVmem n)
  have hUDVmem : ∀ n, MemLp (fun x => Uₙ n x * DVₙ n x) 1 volume := by
    intro n
    exact (hUmem n).mul (hDVmem n)
  have hUVtargetMem : MemLp (fun x => u x * v x) 1 volume := hu.mul hv
  have hDUVtargetMem : MemLp (fun x => Du x i * v x) 1 volume := (hDu i).mul hv
  have hUDVtargetMem : MemLp (fun x => u x * Dv x i) 1 volume := hu.mul (hDv i)
  have hprodUV : Tendsto
      (fun n => eLpNorm (fun x => Uₙ n x * Vₙ n x - u x * v x) 1 volume)
      atTop (nhds 0) :=
    tendsto_eLpNorm_mul_sub_mul_zero hu hv hUmem hVmem hUzero hVzero
  have hprodDUV : Tendsto
      (fun n => eLpNorm (fun x => DUₙ n x * Vₙ n x - Du x i * v x) 1 volume)
      atTop (nhds 0) :=
    tendsto_eLpNorm_mul_sub_mul_zero (hDu i) hv hDUmem hVmem hDUzero hVzero
  have hprodUDV : Tendsto
      (fun n => eLpNorm (fun x => Uₙ n x * DVₙ n x - u x * Dv x i) 1 volume)
      atTop (nhds 0) :=
    tendsto_eLpNorm_mul_sub_mul_zero hu (hDv i) hUmem hDVmem hUzero hDVzero
  have hdφCont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) := by
    simpa using (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφCompact : HasCompactSupport
      (fun x => (fderiv ℝ φ x) (basisVec i)) :=
    hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hdφTop : MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) ∞ volume :=
    hdφCont.memLp_of_hasCompactSupport hdφCompact
  have hφTop : MemLp φ ∞ volume :=
    hφ.continuous.memLp_of_hasCompactSupport hφCompact
  have hleftzero : Tendsto
      (fun n => eLpNorm
        (fun x => Uₙ n x * Vₙ n x *
          (fderiv ℝ φ x) (basisVec i) -
          u x * v x * (fderiv ℝ φ x) (basisVec i)) 1 volume)
      atTop (nhds 0) := by
    simpa only [mul_assoc] using
      tendsto_eLpNorm_mul_test_zero hUVtargetMem hUVmem hprodUV hdφTop
  have hrightDUzero : Tendsto
      (fun n => eLpNorm
        (fun x => DUₙ n x * Vₙ n x * φ x - Du x i * v x * φ x) 1 volume)
      atTop (nhds 0) := by
    simpa only [mul_assoc] using
      tendsto_eLpNorm_mul_test_zero hDUVtargetMem hDUVmem hprodDUV hφTop
  have hrightUDVzero : Tendsto
      (fun n => eLpNorm
        (fun x => Uₙ n x * DVₙ n x * φ x - u x * Dv x i * φ x) 1 volume)
      atTop (nhds 0) := by
    simpa only [mul_assoc] using
      tendsto_eLpNorm_mul_test_zero hUDVtargetMem hUDVmem hprodUDV hφTop
  have hUVint (n : ℕ) : Integrable (fun x => Uₙ n x * Vₙ n x) volume :=
    (hUmem n).integrable_mul (hVmem n)
  have hDUVint (n : ℕ) : Integrable (fun x => DUₙ n x * Vₙ n x) volume :=
    (hDUmem n).integrable_mul (hVmem n)
  have hUDVint (n : ℕ) : Integrable (fun x => Uₙ n x * DVₙ n x) volume :=
    (hUmem n).integrable_mul (hDVmem n)
  have hUVtarget : Integrable (fun x => u x * v x) volume :=
    hu.integrable_mul hv
  have hDUVtarget : Integrable (fun x => Du x i * v x) volume :=
    (hDu i).integrable_mul hv
  have hUDVtarget : Integrable (fun x => u x * Dv x i) volume :=
    hu.integrable_mul (hDv i)
  have hleftInt : ∀ n, Integrable
      (fun x => Uₙ n x * Vₙ n x * (fderiv ℝ φ x) (basisVec i)) volume := by
    intro n
    have h := (hUVint n).mul_of_top_right hdφTop
    convert h using 1
    funext x
    change Uₙ n x * Vₙ n x * (fderiv ℝ φ x) (basisVec i) =
      (fderiv ℝ φ x) (basisVec i) * (Uₙ n x * Vₙ n x)
    ring
  have hleftTargetInt : Integrable
      (fun x => u x * v x * (fderiv ℝ φ x) (basisVec i)) volume := by
    have h := hUVtarget.mul_of_top_right hdφTop
    convert h using 1
    funext x
    change u x * v x * (fderiv ℝ φ x) (basisVec i) =
      (fderiv ℝ φ x) (basisVec i) * (u x * v x)
    ring
  have hrightDUInt : ∀ n, Integrable
      (fun x => DUₙ n x * Vₙ n x * φ x) volume := by
    intro n
    have h := (hDUVint n).mul_of_top_right hφTop
    convert h using 1
    funext x
    change DUₙ n x * Vₙ n x * φ x = φ x * (DUₙ n x * Vₙ n x)
    ring
  have hrightUDVInt : ∀ n, Integrable
      (fun x => Uₙ n x * DVₙ n x * φ x) volume := by
    intro n
    have h := (hUDVint n).mul_of_top_right hφTop
    convert h using 1
    funext x
    change Uₙ n x * DVₙ n x * φ x = φ x * (Uₙ n x * DVₙ n x)
    ring
  have hrightDUTargetInt : Integrable
      (fun x => Du x i * v x * φ x) volume := by
    have h := hDUVtarget.mul_of_top_right hφTop
    convert h using 1
    funext x
    change Du x i * v x * φ x = φ x * (Du x i * v x)
    ring
  have hrightUDVTargetInt : Integrable
      (fun x => u x * Dv x i * φ x) volume := by
    have h := hUDVtarget.mul_of_top_right hφTop
    convert h using 1
    funext x
    change u x * Dv x i * φ x = φ x * (u x * Dv x i)
    ring
  have hleftLimit : Tendsto
      (fun n => ∫ x in U, Uₙ n x * Vₙ n x *
        (fderiv ℝ φ x) (basisVec i)) atTop
      (nhds (∫ x in U, u x * v x * (fderiv ℝ φ x) (basisVec i))) := by
    exact MeasureTheory.tendsto_setIntegral_of_L1' (μ := volume)
      (f := fun x => u x * v x * (fderiv ℝ φ x) (basisVec i))
      (F := fun n x => Uₙ n x * Vₙ n x * (fderiv ℝ φ x) (basisVec i))
      (Eventually.of_forall fun n => hleftInt n) hleftzero U
  have hrightDULimit : Tendsto
      (fun n => ∫ x in U, DUₙ n x * Vₙ n x * φ x) atTop
      (nhds (∫ x in U, Du x i * v x * φ x)) := by
    exact MeasureTheory.tendsto_setIntegral_of_L1' (μ := volume)
      (f := fun x => Du x i * v x * φ x)
      (F := fun n x => DUₙ n x * Vₙ n x * φ x)
      (Eventually.of_forall fun n => hrightDUInt n) hrightDUzero U
  have hrightUDVLimit : Tendsto
      (fun n => ∫ x in U, Uₙ n x * DVₙ n x * φ x) atTop
      (nhds (∫ x in U, u x * Dv x i * φ x)) := by
    exact MeasureTheory.tendsto_setIntegral_of_L1' (μ := volume)
      (f := fun x => u x * Dv x i * φ x)
      (F := fun n x => Uₙ n x * DVₙ n x * φ x)
      (Eventually.of_forall fun n => hrightUDVInt n) hrightUDVzero U
  have hidentity : ∀ n, ∫ x in U, Uₙ n x * Vₙ n x *
      (fderiv ℝ φ x) (basisVec i) =
      -∫ x in U, (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x := by
    intro n
    have hUdiff : ContDiff ℝ (⊤ : ℕ∞) (Uₙ n) :=
      mollify_contDiff (hε_pos n) huLoc
    have hVdiff : ContDiff ℝ (⊤ : ℕ∞) (Vₙ n) :=
      mollify_contDiff (hε_pos n) hvLoc
    have hprodDiff : ContDiff ℝ 1 (fun x => Uₙ n x * Vₙ n x) := by
      exact (hUdiff.mul hVdiff).of_le (by simp)
    have hprodWeak : HasWeakGradientOn U (fun x => Uₙ n x * Vₙ n x)
        (fun x j => (fderiv ℝ (fun y => Uₙ n y * Vₙ n y) x)
          (basisVec j)) := HasWeakGradientOn.of_contDiff hprodDiff
    have hraw := hprodWeak i φ hφ hφCompact hφU
    have heps : ∀ x ∈ K, Metric.closedBall x (ε n) ⊆ U := by
      intro x hx
      exact (Metric.closedBall_subset_cthickening hx (ε n)).trans
        ((Metric.cthickening_mono (hε_le n) K).trans hthick)
    have hderivU : ∀ x ∈ K,
        (fderiv ℝ (Uₙ n) x) (basisVec i) = DUₙ n x := by
      intro x hx
      simpa only [Uₙ, DUₙ] using
        fderiv_mollify_eq_mollify_on_compact hU hK huLoc (hDuLoc i) (hwu i)
          (hε_pos n)
          heps hx
    have hderivV : ∀ x ∈ K,
        (fderiv ℝ (Vₙ n) x) (basisVec i) = DVₙ n x := by
      intro x hx
      simpa only [Vₙ, DVₙ] using
        fderiv_mollify_eq_mollify_on_compact hU hK hvLoc (hDvLoc i) (hwv i)
          (hε_pos n)
          heps hx
    have hφzero : ∀ x, x ∉ K → φ x = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport hx
    have hdφzero : ∀ x, x ∉ K →
        (fderiv ℝ φ x) (basisVec i) = 0 := by
      intro x hx
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
      simp
    have hmul : ∀ x,
        (fderiv ℝ (fun y => Uₙ n y * Vₙ n y) x) (basisVec i) =
          (fderiv ℝ (Uₙ n) x) (basisVec i) * Vₙ n x +
            Uₙ n x * (fderiv ℝ (Vₙ n) x) (basisVec i) := by
      intro x
      have hu' := hUdiff.differentiable (by simp) x
      have hv' := hVdiff.differentiable (by simp) x
      have h := congrArg (fun L : Vec 3 →L[ℝ] ℝ => L (basisVec i))
        (fderiv_fun_mul hu' hv')
      calc
        (fderiv ℝ (fun y => Uₙ n y * Vₙ n y) x) (basisVec i) =
            Uₙ n x * (fderiv ℝ (Vₙ n) x) (basisVec i) +
              Vₙ n x * (fderiv ℝ (Uₙ n) x) (basisVec i) := by
          simpa only [add_apply, smul_apply, smul_eq_mul] using h
        _ = (fderiv ℝ (Uₙ n) x) (basisVec i) * Vₙ n x +
              Uₙ n x * (fderiv ℝ (Vₙ n) x) (basisVec i) := by ring
    calc
      (∫ x in U, Uₙ n x * Vₙ n x *
          (fderiv ℝ φ x) (basisVec i)) =
          -∫ x in U, (fderiv ℝ (fun y => Uₙ n y * Vₙ n y) x)
            (basisVec i) * φ x := hraw
      _ = -∫ x in U, (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x := by
        congr 1
        apply setIntegral_congr_fun hU.measurableSet
        intro x hx
        by_cases hxK : x ∈ K
        · change (fderiv ℝ (fun y => Uₙ n y * Vₙ n y) x) (basisVec i) * φ x =
            (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x
          rw [hmul x, hderivU x hxK, hderivV x hxK]
        · change (fderiv ℝ (fun y => Uₙ n y * Vₙ n y) x) (basisVec i) * φ x =
            (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x
          rw [hφzero x hxK, mul_zero]
          simp
  have hrightLimit : Tendsto
      (fun n => -∫ x in U, (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x)
      atTop (nhds (-∫ x in U, (Du x i * v x + u x * Dv x i) * φ x)) := by
    have hsumLimit : Tendsto
        (fun n => ∫ x in U, (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x)
        atTop (nhds (∫ x in U, (Du x i * v x + u x * Dv x i) * φ x)) := by
      have hsumInt : ∀ n, Integrable
          (fun x => (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x) volume := by
        intro n
        have hA := (hrightDUInt n).mul_const (1 : ℝ)
        have hB := hrightUDVInt n
        have hsum0 := hA.add hB
        have hsum : Integrable
            (fun x => DUₙ n x * Vₙ n x * φ x + Uₙ n x * DVₙ n x * φ x) volume := by
          convert hsum0 using 1
          funext x
          change DUₙ n x * Vₙ n x * φ x + Uₙ n x * DVₙ n x * φ x =
            DUₙ n x * Vₙ n x * φ x * 1 + Uₙ n x * DVₙ n x * φ x
          simp
        convert hsum using 1
        funext x
        ring
      have hsumTarget : Integrable
          (fun x => (Du x i * v x + u x * Dv x i) * φ x) volume := by
        have hsum := hrightDUTargetInt.add hrightUDVTargetInt
        convert hsum using 1
        funext x
        change (Du x i * v x + u x * Dv x i) * φ x =
          Du x i * v x * φ x + u x * Dv x i * φ x
        ring
      have hsumzero : Tendsto
          (fun n => eLpNorm
            (fun x => (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x -
              (Du x i * v x + u x * Dv x i) * φ x) 1 volume)
          atTop (nhds 0) := by
        have hdecomp : ∀ n, (fun x =>
            (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x -
              (Du x i * v x + u x * Dv x i) * φ x) =
            (fun x => DUₙ n x * Vₙ n x * φ x - Du x i * v x * φ x) +
              (fun x => Uₙ n x * DVₙ n x * φ x - u x * Dv x i * φ x) := by
          intro n
          funext x
          change (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x -
            (Du x i * v x + u x * Dv x i) * φ x =
            (DUₙ n x * Vₙ n x * φ x - Du x i * v x * φ x) +
              (Uₙ n x * DVₙ n x * φ x - u x * Dv x i * φ x)
          ring
        have hsumBound : ∀ n, eLpNorm
            (fun x => (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x -
              (Du x i * v x + u x * Dv x i) * φ x) 1 volume ≤
            eLpNorm (fun x => DUₙ n x * Vₙ n x * φ x - Du x i * v x * φ x) 1 volume +
              eLpNorm (fun x => Uₙ n x * DVₙ n x * φ x - u x * Dv x i * φ x) 1 volume := by
          intro n
          rw [hdecomp n]
          exact MeasureTheory.eLpNorm_add_le (p := (1 : ℝ≥0∞)) (by norm_num)
        have hlim := hrightDUzero.add hrightUDVzero
        have hlim' : Tendsto (fun n =>
            eLpNorm (fun x => DUₙ n x * Vₙ n x * φ x - Du x i * v x * φ x) 1 volume +
              eLpNorm (fun x => Uₙ n x * DVₙ n x * φ x - u x * Dv x i * φ x) 1 volume)
            atTop (nhds 0) := by
          simpa only [add_zero] using hlim
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
          (Eventually.of_forall fun _ => zero_le)
        filter_upwards [] with n
        exact hsumBound n
      exact MeasureTheory.tendsto_setIntegral_of_L1' (μ := volume)
        (f := fun x => (Du x i * v x + u x * Dv x i) * φ x)
        (F := fun n x => (DUₙ n x * Vₙ n x + Uₙ n x * DVₙ n x) * φ x)
        (Eventually.of_forall fun n => hsumInt n) hsumzero U
    exact hsumLimit.neg
  have hrightLimit' := hrightLimit.congr'
    (Eventually.of_forall fun n => (hidentity n).symm)
  exact tendsto_nhds_unique hleftLimit hrightLimit'

theorem HasWeakGradientOn.mul_of_memLp_two
    {U : Set (Vec 3)} (hU : IsOpen U)
    {u v : Vec 3 → ℝ} {Du Dv : Vec 3 → Vec 3}
    (hu : MemLp u 2 (volume.restrict U))
    (hv : MemLp v 2 (volume.restrict U))
    (hDu : ∀ i : Fin 3, MemLp (fun x => Du x i) 2 (volume.restrict U))
    (hDv : ∀ i : Fin 3, MemLp (fun x => Dv x i) 2 (volume.restrict U))
    (hwu : HasWeakGradientOn U u Du)
    (hwv : HasWeakGradientOn U v Dv) :
    HasWeakGradientOn U (fun x => u x * v x)
      (fun x i => Du x i * v x + u x * Dv x i) := by
  have huExt : MemLp (U.indicator u) 2 volume := by
    exact (memLp_indicator_iff_restrict hU.measurableSet).2 hu
  have hvExt : MemLp (U.indicator v) 2 volume := by
    exact (memLp_indicator_iff_restrict hU.measurableSet).2 hv
  have hDuExt : ∀ i : Fin 3,
      MemLp (fun x => U.indicator (fun y => Du y i) x) 2 volume := by
    intro i
    exact (memLp_indicator_iff_restrict hU.measurableSet).2 (hDu i)
  have hDvExt : ∀ i : Fin 3,
      MemLp (fun x => U.indicator (fun y => Dv y i) x) 2 volume := by
    intro i
    exact (memLp_indicator_iff_restrict hU.measurableSet).2 (hDv i)
  have hwuExt : HasWeakGradientOn U (U.indicator u)
      (fun x i => U.indicator (fun y => Du y i) x) := by
    intro i φ hφ hφc hφU
    calc
      ∫ x in U, U.indicator u x * (fderiv ℝ φ x) (basisVec i) =
          ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) := by
            apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
            intro x hx
            simp [Set.indicator_of_mem hx]
      _ = -∫ x in U, Du x i * φ x := hwu i φ hφ hφc hφU
      _ = -∫ x in U, U.indicator (fun y => Du y i) x * φ x := by
        congr 1
        apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
        intro x hx
        simp [Set.indicator_of_mem hx]
  have hwvExt : HasWeakGradientOn U (U.indicator v)
      (fun x i => U.indicator (fun y => Dv y i) x) := by
    intro i φ hφ hφc hφU
    calc
      ∫ x in U, U.indicator v x * (fderiv ℝ φ x) (basisVec i) =
          ∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) := by
            apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
            intro x hx
            simp [Set.indicator_of_mem hx]
      _ = -∫ x in U, Dv x i * φ x := hwv i φ hφ hφc hφU
      _ = -∫ x in U, U.indicator (fun y => Dv y i) x * φ x := by
        congr 1
        apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
        intro x hx
        simp [Set.indicator_of_mem hx]
  have hglobal := HasWeakGradientOn.mul_of_memLp_two_global hU huExt hvExt
    hDuExt hDvExt hwuExt hwvExt
  intro i φ hφ hφc hφU
  have h := hglobal i φ hφ hφc hφU
  calc
    ∫ x in U, u x * v x * (fderiv ℝ φ x) (basisVec i) =
        ∫ x in U, U.indicator u x * U.indicator v x *
          (fderiv ℝ φ x) (basisVec i) := by
            apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
            intro x hx
            simp [Set.indicator_of_mem hx]
    _ = -∫ x in U,
        (U.indicator (fun y => Du y i) x * U.indicator v x +
          U.indicator u x * U.indicator (fun y => Dv y i) x) * φ x := h
    _ = -∫ x in U, (Du x i * v x + u x * Dv x i) * φ x := by
          congr 1
          apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
          intro x hx
          simp [Set.indicator_of_mem hx]

end

end CKN
