/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.BasicLemmas
public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent

/-!
# Finite-measure downgrades from `H¹` to `W^{1,p}`

On a finite-measure domain, the `L²` value and weak-gradient data carried by
an `H1Function` also provide `W^{1,p}` data at every finite exponent `p ≤ 2`.
The analogous conversion for `H10Function` preserves its smooth, compactly
supported approximating sequence and therefore its zero-trace witness.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace H1Function

/-- Regard an `H¹` witness on a finite-measure domain as a `W^{1,p}` witness
whenever `p ≤ 2`.  The value and weak-gradient representatives are unchanged. -/
noncomputable def toW1pOfExponentLETwo {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (u : H1Function U) (p : FiniteLpExponent) (hp : p.exponent ≤ 2) :
    W1pFunction U p.exponent :=
  { toFun := u.toFun
    grad := u.grad
    memLp := u.memL2.mono_exponent hp
    gradMemLp := fun i => (u.gradMemL2 i).mono_exponent hp
    hasWeakGradient := u.hasWeakGradient }

@[simp] theorem toW1pOfExponentLETwo_toFun {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (u : H1Function U) (p : FiniteLpExponent) (hp : p.exponent ≤ 2) :
    (u.toW1pOfExponentLETwo p hp).toFun = u.toFun :=
  rfl

@[simp] theorem toW1pOfExponentLETwo_grad {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (u : H1Function U) (p : FiniteLpExponent) (hp : p.exponent ≤ 2) :
    (u.toW1pOfExponentLETwo p hp).grad = u.grad :=
  rfl

end H1Function

namespace H10Function

private theorem tendsto_eLpNorm_downgrade_of_two
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    {p : FiniteLpExponent} (hp : p.exponent ≤ 2)
    {F : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (hF2 : ∀ n, MeasureTheory.MemLp (F n) 2 (MeasureTheory.volume.restrict U))
    (hf2 : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict U))
    (hTendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => F n x - f x) 2
        (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => F n x - f x) p.exponent
        (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0) := by
  let μ : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  have hdiff_meas : ∀ n,
      MeasureTheory.AEStronglyMeasurable (fun x => F n x - f x) μ := by
    intro n
    exact (hF2 n).aestronglyMeasurable.sub hf2.aestronglyMeasurable
  have hp_real : 0 ≤ 1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal := by
    have hple : p.exponent.toReal ≤ (2 : ℝ≥0∞).toReal :=
      (ENNReal.toReal_le_toReal p.lt_top.ne (by norm_num)).mpr hp
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le
      (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne) hple
  have hbound : ∀ n,
      MeasureTheory.eLpNorm (fun x => F n x - f x) p.exponent μ ≤
        MeasureTheory.eLpNorm (fun x => F n x - f x) 2 μ *
          μ Set.univ ^ (1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal) := by
    intro n
    exact MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hdiff_meas n)
  have hfactor_ne_top :
      μ Set.univ ^ (1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    refine (ENNReal.rpow_lt_top_of_nonneg hp_real ?_).ne
    exact (MeasureTheory.measure_lt_top μ Set.univ).ne
  have hscaled : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => F n x - f x) 2 μ *
        μ Set.univ ^ (1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal))
      Filter.atTop
      (nhds (0 * μ Set.univ ^
        (1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal))) := by
    exact ENNReal.Tendsto.mul_const (by simpa only [μ] using hTendsto)
      (Or.inr hfactor_ne_top)
  have hscaled_zero : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => F n x - f x) 2 μ *
        μ Set.univ ^ (1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal))
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hscaled_zero (fun _ => zero_le) hbound

/-- Regard an `H¹₀` witness on a finite-measure domain as a zero-trace
`W^{1,p}` witness whenever `p ≤ 2`.  The value, weak-gradient, and smooth
compactly supported approximation representatives are unchanged. -/
noncomputable def toW10pOfExponentLETwo {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (u : H10Function U) (p : FiniteLpExponent) (hp : p.exponent ≤ 2) :
    W10pFunction U p.exponent :=
  { toW1pFunction := u.toH1Function.toW1pOfExponentLETwo p hp
    approx := u.approx
    approx_smooth := u.approx_smooth
    approx_hasCompactSupport := u.approx_hasCompactSupport
    approx_support_subset := u.approx_support_subset
    tendsto_approx := by
      apply tendsto_eLpNorm_downgrade_of_two hp
      · intro n
        exact ((u.approx_smooth n).differentiable (by simp)).continuous
          |>.memLp_of_hasCompactSupport (u.approx_hasCompactSupport n) |>.restrict U
      · exact u.toH1Function.memL2
      · exact u.tendsto_approx
    tendsto_approx_grad := by
      intro i
      apply tendsto_eLpNorm_downgrade_of_two hp
      · intro n
        have hcont : Continuous (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := by
          simpa using
            ((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
        have hsupp : HasCompactSupport
            (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := by
          simpa using (u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i)
        exact hcont.memLp_of_hasCompactSupport hsupp |>.restrict U
      · exact u.toH1Function.gradMemL2 i
      · exact u.tendsto_approx_grad i }

@[simp] theorem toW10pOfExponentLETwo_toFun {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (u : H10Function U) (p : FiniteLpExponent) (hp : p.exponent ≤ 2) :
    (u.toW10pOfExponentLETwo p hp).toW1pFunction.toFun = u.toH1Function.toFun :=
  rfl

@[simp] theorem toW10pOfExponentLETwo_grad {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (u : H10Function U) (p : FiniteLpExponent) (hp : p.exponent ≤ 2) :
    (u.toW10pOfExponentLETwo p hp).toW1pFunction.grad = u.toH1Function.grad :=
  rfl

end H10Function

/-- The finite-measure comparison from a lower finite exponent to `L²`. -/
theorem eLpNorm_finiteMeasure_downgrade_le {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    (p : FiniteLpExponent) (hp : p.exponent ≤ 2) (f : Vec d → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict U)) :
    MeasureTheory.eLpNorm f p.exponent (MeasureTheory.volume.restrict U) ≤
      MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict U) *
        (MeasureTheory.volume.restrict U) Set.univ ^
          (1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal) := by
  exact MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf

/-- On a normalized cube, lowering an exponent from `2` costs no measure
factor because the normalized cube measure is a probability measure. -/
theorem eLpNorm_normalizedCubeMeasure_downgrade_le {d : ℕ} (Q : TriadicCube d)
    (p : FiniteLpExponent) (hp : p.exponent ≤ 2) (f : Vec d → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable f (normalizedCubeMeasure Q)) :
    MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure Q) ≤
      MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) := by
  let : MeasureTheory.IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hp

/-- The normalized-cube exponent downgrade for the value representative of
an `H¹` function. -/
theorem H1Function.eLpNorm_normalizedCubeMeasure_downgrade_le {d : ℕ}
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (p : FiniteLpExponent) (hp : p.exponent ≤ 2) :
    MeasureTheory.eLpNorm u.toFun p.exponent (normalizedCubeMeasure Q) ≤
      MeasureTheory.eLpNorm u.toFun 2 (normalizedCubeMeasure Q) :=
  Homogenization.eLpNorm_normalizedCubeMeasure_downgrade_le Q p hp u.toFun
    u.memL2_normalizedCubeMeasure.aestronglyMeasurable

/-- The normalized-cube exponent downgrade for a gradient coordinate of an
`H¹` function. -/
theorem H1Function.grad_eLpNorm_normalizedCubeMeasure_downgrade_le {d : ℕ}
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) (i : Fin d)
    (p : FiniteLpExponent) (hp : p.exponent ≤ 2) :
    MeasureTheory.eLpNorm (fun x => u.grad x i) p.exponent (normalizedCubeMeasure Q) ≤
      MeasureTheory.eLpNorm (fun x => u.grad x i) 2 (normalizedCubeMeasure Q) :=
  Homogenization.eLpNorm_normalizedCubeMeasure_downgrade_le Q p hp (fun x => u.grad x i)
    (u.grad_memL2_normalizedCubeMeasure i).aestronglyMeasurable

end

end Homogenization
