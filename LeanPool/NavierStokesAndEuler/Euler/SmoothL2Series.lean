/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySmoothLimit
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldPhysicalSobolev
import LeanPool.NavierStokesAndEuler.Euler.SmoothL2ScalingContinuity
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! A series of genuine smooth spatial L² fields that is absolutely
summable at every finite Sobolev order has one smooth L² sum. -/

@[expose] public section


noncomputable section

namespace EulerSmoothL2Series

open Set Filter Finset MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerPhysicalL2Scaling
  EulerSmoothFieldSobolevTime EulerMeanSmoothRepresentative
open scoped Topology ContDiff

local instance instSmoothL2Series1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem tensorNorm_eq_derivativeSum (A : SmoothL2Field Space) (s : ℕ) :
    tensorNorm s A=derivativeSum s A.field := by
  unfold tensorNorm derivativeSum
  apply sum_congr rfl
  intro n _
  rw [norm_jetLp,toReal_eLpNorm (A.integrable n).aestronglyMeasurable]

theorem tensorNorm_add_le (A B : SmoothL2Field Space) (s : ℕ) :
    tensorNorm s (addField A B) ≤ tensorNorm s A+tensorNorm s B := by
  simp only [tensorNorm,← sum_add_distrib]
  exact sum_le_sum (fun n _ => by rw [jetLp_addField]; exact norm_add_le _ _)

theorem zeroField_jet (n : ℕ) : (zeroField : SmoothL2Field Space).jetLp n=0 := by
  apply norm_eq_zero.mp
  simp only [norm_jetLp,zeroField,iteratedFDeriv_zero,eLpNorm_zero,ENNReal.toReal_zero]

theorem zeroField_value : (zeroField : SmoothL2Field Space).toLp=0 := by
  apply norm_eq_zero.mp
  rw [← norm_jetLp_zero,zeroField_jet,norm_zero]

/-- Partial sum as an element of `ℕ → SmoothL2Field Space | 0 => zeroField | n+1 => addField
(partialSum A n) (A n)`. -/
def partialSum (A : ℕ → SmoothL2Field Space) : ℕ → SmoothL2Field Space
  | 0 => zeroField
  | n+1 => addField (partialSum A n) (A n)

theorem partialSum_field (A : ℕ → SmoothL2Field Space) (n : ℕ) (x : Space) :
    (partialSum A n).field x=∑ i ∈ range n, (A i).field x := by
  induction n with
  | zero => simp only [partialSum,zeroField,sum_range_zero]; rfl
  | succ n ih => simp only [partialSum,addField_field,ih,sum_range_succ]

theorem partialSum_jet (A : ℕ → SmoothL2Field Space) (n q : ℕ) :
    (partialSum A n).jetLp q=∑ i ∈ range n, (A i).jetLp q := by
  induction n with
  | zero => simp only [partialSum,zeroField_jet,sum_range_zero]
  | succ n ih => simp only [partialSum,jetLp_addField,ih,sum_range_succ]

theorem partialSum_value (A : ℕ → SmoothL2Field Space) (n : ℕ) :
    (partialSum A n).toLp=∑ i ∈ range n, (A i).toLp := by
  induction n with
  | zero => simp only [partialSum,zeroField_value,sum_range_zero]
  | succ n ih => simp only [partialSum,toLp_addField,ih,sum_range_succ]

theorem partialSum_norm (A : ℕ → SmoothL2Field Space) (n q : ℕ) :
    tensorNorm q (partialSum A n) ≤ ∑ i ∈ range n, tensorNorm q (A i) := by
  induction n with
  | zero =>
      simp only [partialSum, tensorNorm, zeroField_jet, norm_zero, sum_const_zero, sum_range_zero,
          le_refl]
  | succ n ih =>
    exact (tensorNorm_add_le _ _ q).trans
      (by simpa only [sum_range_succ] using add_le_add ih (le_refl (tensorNorm q (A n))))

theorem tensorNorm_zero (A : SmoothL2Field Space) : tensorNorm 0 A=‖A.toLp‖ := by
  simp only [tensorNorm,Nat.zero_add,sum_range_one,norm_jetLp_zero]

variable (A : ℕ → SmoothL2Field Space) (hA : ∀ q, Summable (fun n => tensorNorm q (A n)))

include hA

theorem partialSum_uniform_bound (n q : ℕ) :
    tensorNorm q (partialSum A n) ≤ ∑' i, tensorNorm q (A i) :=
  (partialSum_norm A n q).trans
    (Summable.sum_le_tsum (range n) (fun i _ => tensorNorm_nonneg q (A i)) (hA q))

theorem partialSum_value_cauchy : CauchySeq (fun n => (partialSum A n).toLp) := by
  have hs : Summable (fun n => ‖(A n).toLp‖) := by simpa only [tensorNorm_zero] using hA 0
  simpa only [partialSum_value] using hs.of_norm.hasSum.tendsto_sum_nat.cauchySeq

theorem partialSum_path_cauchy :
    CauchySeq (fun n => fieldPath (fun _ : Icc (0 : ℝ) 0 => partialSum A n)
      (fun _ => continuous_const)) := by
  let C : EulerMeanSolenoidal.L2 →L[ℝ] C(Icc (0 : ℝ) 0,EulerMeanSolenoidal.L2) :=
    ContinuousLinearMap.const ℝ _
  have hc : CauchySeq (fun n => C ((partialSum A n).toLp)) := by
    simpa only [CauchySeq,Filter.map_map,Function.comp_def] using
      (partialSum_value_cauchy A hA).map C.uniformContinuous
  exact hc

/-- Limit data, constructed using `smoothLimitData`. -/
def limitData : SmoothLimitData (fun (n : ℕ) (_ : Icc (0 : ℝ) 0) => partialSum A n)
    (fun _ _ => continuous_const) :=
  smoothLimitData (by norm_num) _ _
    (fun q => ⟨∑' i, tensorNorm q (A i),fun n _ => partialSum_uniform_bound A hA n q⟩)
    (partialSum_path_cauchy A hA)

/-- Sum field, given by `(limitData A hA).field ⟨0,le_rfl,le_rfl⟩`. -/
def sumField : SmoothL2Field Space := (limitData A hA).field ⟨0,le_rfl,le_rfl⟩

theorem sumField_jet_tendsto (q : ℕ) :
    Tendsto (fun n => (partialSum A n).jetLp q) atTop (𝓝 ((sumField A hA).jetLp q)) :=
  (limitData A hA).jet_convergence q ⟨0,le_rfl,le_rfl⟩

theorem sumField_value_tendsto :
    Tendsto (fun n => (partialSum A n).toLp) atTop (𝓝 ((sumField A hA).toLp)) :=
  (limitData A hA).toLp_convergence ⟨0,le_rfl,le_rfl⟩

theorem sumField_Hm_tendsto (q : ℕ) :
    Tendsto (fun n => ∑ j ∈ range (q+1),
      ‖(partialSum A n).jetLp j-(sumField A hA).jetLp j‖) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (range (q+1)) (fun j _ =>
    ((sumField_jet_tendsto A hA j).sub
      (tendsto_const_nhds (x := (sumField A hA).jetLp j))).norm)
  simpa only [sub_self,norm_zero,sum_const_zero] using h

theorem sumField_derivativeSum_tendsto (q : ℕ) :
    Tendsto (fun n => derivativeSum q ((partialSum A n).field-(sumField A hA).field))
      atTop (𝓝 0) := by
  have he (n : ℕ) : derivativeSum q ((partialSum A n).field-(sumField A hA).field) =
      ∑ j ∈ range (q+1), ‖(partialSum A n).jetLp j-(sumField A hA).jetLp j‖ := by
    change derivativeSum q (subField (partialSum A n) (sumField A hA)).field= _
    rw [← tensorNorm_eq_derivativeSum]
    simp only [tensorNorm,jetLp_subField]
  simpa only [he] using sumField_Hm_tendsto A hA q

theorem sumField_sobolev_tendsto (q : ℕ) :
    Tendsto (fun n => ordinarySobolev q (partialSum A n).toLp (partialSum A n).translation_contDiff)
      atTop (𝓝 (ordinarySobolev q (sumField A hA).toLp (sumField A hA).translation_contDiff)) := by
  let t : Icc (0 : ℝ) 0 := ⟨0,le_rfl,le_rfl⟩
  have h := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto _).comp
    ((limitData A hA).sobolev_convergence q)
  have he := (limitData A hA).tower.smoothField_realization q t
  simp only [ContinuousMap.evalCLM_apply,Function.comp_def] at h
  rw [← he] at h
  exact h

theorem sumField_pointwise_tendsto (x : Space) :
    Tendsto (fun n => (partialSum A n).field x) atTop (𝓝 ((sumField A hA).field x)) := by
  have h := ((observation 3 (le_refl 3) (x,0)).continuous.tendsto _).comp
    (sumField_sobolev_tendsto A hA 3)
  simpa only [Function.comp_def,observation_apply] using h

theorem sumField_support (S : Set Space) (hS : IsClosed S)
    (hs : ∀ n, tsupport (A n).field ⊆ S) : tsupport (sumField A hA).field ⊆ S := by
  apply closure_minimal ?_ hS
  intro x hx
  by_contra hn
  have hzero (n : ℕ) : (partialSum A n).field x=0 := by
    rw [partialSum_field]
    exact sum_eq_zero (fun i _ => image_eq_zero_of_notMem_tsupport (fun hi => hn (hs i hi)))
  have ht := sumField_pointwise_tendsto A hA x
  simp only [hzero] at ht
  have he : (sumField A hA).field x=0 := tendsto_nhds_unique ht tendsto_const_nhds
  exact hx he

end EulerSmoothL2Series
