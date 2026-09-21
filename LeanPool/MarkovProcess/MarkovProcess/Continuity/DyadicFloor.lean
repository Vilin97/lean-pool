/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Continuity.DyadicChaining
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Dyadic floor approximation and the unit-interval continuous modification

This file merges the following former modules, one section each:

* `DyadicFloorApproximation`: Left dyadic approximations of unit-interval times
* `DyadicFloorPair`: Comparing two dyadic floor approximations
* `DyadicFloorSampleCauchy`: Cauchy control of dyadic floor samples
* `DyadicFloorDenseTime`: Dyadic floor samples at dyadic times
* `DyadicFloorSampleLimit`: Limits of dyadic floor samples
* `DyadicFloorLimitControl`: Uniform control of dyadic floor-sample limits
* `DyadicFloorLimitPath`: The canonical unit-interval dyadic-floor limit path
* `DyadicFloorConvergenceInMeasure`: Convergence in measure of dyadic floor samples
* `DyadicFloorUnitModification`: A continuous modification on the unit interval
-/

noncomputable section PortComputability

namespace MarkovProcess

section DyadicFloorApproximation


section

/-- The index of the left endpoint of the level-`n` dyadic cell containing `t ∈ [0, 1]`. -/
def unitDyadicFloorIndex (n : ℕ) (t : Set.Icc (0 : ℝ) 1) : Fin (2 ^ n + 1) :=
  ⟨⌊(2 ^ n : ℝ) * t.1⌋₊, by
    have hnonneg : 0 ≤ (2 ^ n : ℝ) * t.1 :=
      mul_nonneg (by positivity) t.2.1
    have hfloor_real : (⌊(2 ^ n : ℝ) * t.1⌋₊ : ℝ) ≤ (2 ^ n : ℝ) * t.1 :=
      Nat.floor_le hnonneg
    have hscaled_le : (2 ^ n : ℝ) * t.1 ≤ (2 ^ n : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left t.2.2 (by positivity)
    have hfloor_nat : ⌊(2 ^ n : ℝ) * t.1⌋₊ ≤ 2 ^ n := by
      exact_mod_cast hfloor_real.trans hscaled_le
    omega⟩

@[simp]
theorem unitDyadicFloorIndex_val (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (unitDyadicFloorIndex n t).val = ⌊(2 ^ n : ℝ) * t.1⌋₊ :=
  rfl

/-- The rational level-`n` left dyadic approximation of `t`. -/
def unitDyadicFloorValue (n : ℕ) (t : Set.Icc (0 : ℝ) 1) : NNRat :=
  unitDyadicGrid n (unitDyadicFloorIndex n t)

/-- The left dyadic approximation does not exceed the represented real time. -/
theorem unitDyadicFloorValue_le (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (unitDyadicFloorValue n t : ℝ) ≤ t.1 := by
  have hnonneg : 0 ≤ (2 ^ n : ℝ) * t.1 :=
    mul_nonneg (by positivity) t.2.1
  have hfloor := Nat.floor_le hnonneg
  unfold unitDyadicFloorValue unitDyadicGrid
  simp only [unitDyadicFloorIndex_val]
  push_cast
  exact (div_le_iff₀' (by positivity)).2 (by simpa only [mul_comm] using hfloor)

/-- The gap from `t` to its level-`n` left approximation is at most one dyadic cell. -/
theorem sub_unitDyadicFloorValue_le (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    t.1 - (unitDyadicFloorValue n t : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by
  have hupper := Nat.lt_floor_add_one ((2 ^ n : ℝ) * t.1)
  unfold unitDyadicFloorValue unitDyadicGrid
  simp only [unitDyadicFloorIndex_val]
  push_cast
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  apply le_of_lt
  rw [sub_lt_iff_lt_add, inv_eq_one_div]
  calc
    t.1 = ((2 : ℝ) ^ n * t.1) / (2 : ℝ) ^ n := by field_simp
    _ < (⌊(2 ^ n : ℝ) * t.1⌋₊ + 1) / (2 : ℝ) ^ n :=
      (div_lt_div_iff_of_pos_right hpow).2 hupper
    _ = 1 / (2 : ℝ) ^ n + (⌊(2 ^ n : ℝ) * t.1⌋₊ : ℝ) / (2 : ℝ) ^ n := by
      rw [add_div]
      ring

/-- Passing from level `n + 1` to its canonical parent recovers the level-`n` left index. -/
theorem unitDyadicParentIndex_floorIndex (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    unitDyadicParentIndex n (unitDyadicFloorIndex (n + 1) t) =
      unitDyadicFloorIndex n t := by
  apply Fin.ext
  simp only [unitDyadicParentIndex_val, unitDyadicFloorIndex_val]
  have harg : (2 ^ (n + 1) : ℝ) * t.1 = ((2 ^ n : ℝ) * t.1) * 2 := by
    rw [pow_succ]
    ring
  rw [harg]
  exact Nat.mul_cast_floor_div_cancel (R := ℝ) (by norm_num : 2 ≠ 0)
    ((2 ^ n : ℝ) * t.1)

/-- At consecutive levels, the fine left index is either the refinement of the coarse index or
the immediately following fine-grid index. -/
theorem unitDyadicFloorIndex_sub_refineIndex_le_one (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (unitDyadicFloorIndex (n + 1) t).val -
        (unitDyadicRefineIndex n (unitDyadicFloorIndex n t)).val ≤ 1 := by
  rw [← unitDyadicParentIndex_floorIndex n t]
  exact unitDyadic_child_sub_refineIndex_parent_le_one n (unitDyadicFloorIndex (n + 1) t)

end

end DyadicFloorApproximation

section DyadicFloorPair

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


section

/-- Dyadic floor indices preserve the order of their represented times. -/
theorem unitDyadicFloorIndex_mono (n : ℕ) {s t : Set.Icc (0 : ℝ) 1}
    (hst : s.1 ≤ t.1) :
    (unitDyadicFloorIndex n s).val ≤ (unitDyadicFloorIndex n t).val := by
  simp only [unitDyadicFloorIndex_val]
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left hst (by positivity))

/-- Two ordered times separated by at most one level-`n` cell have floor indices separated by
at most one. -/
theorem unitDyadicFloorIndex_sub_le_one_of_sub_le_inv_pow
    (n : ℕ) {s t : Set.Icc (0 : ℝ) 1} (hst : s.1 ≤ t.1)
    (hgap : t.1 - s.1 ≤ ((2 : ℝ) ^ n)⁻¹) :
    (unitDyadicFloorIndex n t).val - (unitDyadicFloorIndex n s).val ≤ 1 := by
  let c : ℝ := (2 : ℝ) ^ n
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hscaled : c * (t.1 - s.1) ≤ 1 := by
    calc
      c * (t.1 - s.1) ≤ c * c⁻¹ :=
        mul_le_mul_of_nonneg_left hgap hc.le
      _ = 1 := mul_inv_cancel₀ hc.ne'
  have hmul : c * t.1 ≤ c * s.1 + 1 := by
    calc
      c * t.1 = c * s.1 + c * (t.1 - s.1) := by ring
      _ ≤ c * s.1 + 1 := add_le_add_right hscaled _
  have hfloor : ⌊c * t.1⌋₊ ≤ ⌊c * s.1⌋₊ + 1 := by
    calc
      ⌊c * t.1⌋₊ ≤ ⌊c * s.1 + 1⌋₊ := Nat.floor_mono hmul
      _ = ⌊c * s.1⌋₊ + 1 := Nat.floor_add_one (mul_nonneg hc.le s.2.1)
  have hmono : ⌊c * s.1⌋₊ ≤ ⌊c * t.1⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hst hc.le)
  simp only [unitDyadicFloorIndex_val]
  change ⌊c * t.1⌋₊ - ⌊c * s.1⌋₊ ≤ 1
  omega

/-- Adjacent-increment control on level `n` controls the process increment between two ordered
times lying at most one level-`n` cell apart. -/
theorem edist_unitDyadicFloorValue_le_of_sub_le_inv_pow_of_adjacent_le
    {Ω E : Type*} [PseudoEMetricSpace E] {X : NNRat → Ω → E}
    {n : ℕ} {ε : ℝ≥0∞} {ω : Ω}
    (hadj : ∀ k : Fin (2 ^ n),
      edist (X (unitDyadicGrid n k.castSucc) ω)
          (X (unitDyadicGrid n k.succ) ω) ≤ ε)
    {s t : Set.Icc (0 : ℝ) 1} (hst : s.1 ≤ t.1)
    (hgap : t.1 - s.1 ≤ ((2 : ℝ) ^ n)⁻¹) :
    edist (X (unitDyadicFloorValue n s) ω)
        (X (unitDyadicFloorValue n t) ω) ≤ ε := by
  have hmono := unitDyadicFloorIndex_mono n hst
  have hdiff := unitDyadicFloorIndex_sub_le_one_of_sub_le_inv_pow n hst hgap
  calc
    edist (X (unitDyadicFloorValue n s) ω)
        (X (unitDyadicFloorValue n t) ω) ≤
        ((unitDyadicFloorIndex n t).val - (unitDyadicFloorIndex n s).val : ℕ) * ε := by
      simpa only [unitDyadicFloorValue] using
        edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le hadj
          (unitDyadicFloorIndex n s) (unitDyadicFloorIndex n t) hmono
    _ ≤ (1 : ℝ≥0∞) * ε := by
      have hcast :
          (((unitDyadicFloorIndex n t).val - (unitDyadicFloorIndex n s).val : ℕ) :
            ℝ≥0∞) ≤ 1 := by
        exact_mod_cast hdiff
      exact mul_le_mul_of_nonneg_right hcast bot_le
    _ = ε := one_mul ε

/-- Almost surely, on all sufficiently fine dyadic levels, any two ordered unit-interval times
within one cell have process increment bounded by that level's Kolmogorov--Chentsov threshold. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicFloorValue_le_threshold
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ s t : Set.Icc (0 : ℝ) 1,
      s.1 ≤ t.1 → t.1 - s.1 ≤ ((2 : ℝ) ^ n)⁻¹ →
        edist (X (unitDyadicFloorValue n s) ω)
            (X (unitDyadicFloorValue n t) ω) ≤ dyadicIncrementThreshold γ n := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_adjacent_lt_threshold
      hX hγ hγq] with ω hω
  filter_upwards [hω] with n hn
  intro s t hst hgap
  exact edist_unitDyadicFloorValue_le_of_sub_le_inv_pow_of_adjacent_le
    (fun k ↦ (hn k).le) hst hgap

end

end DyadicFloorPair

section DyadicFloorSampleCauchy

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- Iterating canonical parents of the level-`n + r` floor index recovers the level-`n`
floor index. -/
theorem unitDyadicAncestorIndex_floorIndex
    (n r : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    unitDyadicAncestorIndex n r (unitDyadicFloorIndex (n + r) t) =
      unitDyadicFloorIndex n t := by
  induction r with
  | zero => rfl
  | succ r ihr =>
      have hparent :
          unitDyadicParentIndex (n + r) (unitDyadicFloorIndex (n + (r + 1)) t) =
            unitDyadicFloorIndex (n + r) t := by
        simpa only [Nat.add_assoc] using! unitDyadicParentIndex_floorIndex (n + r) t
      rw [unitDyadicAncestorIndex_succ, hparent]
      exact ihr

/-- Almost surely, above every sufficiently fine base level, the floor samples at levels
`n + r` and `n` are bounded uniformly in the depth `r` and time `t` by the vanishing
ancestor tail. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicFloorValue_add_le_tail
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ r (t : Set.Icc (0 : ℝ) 1),
      edist (X (unitDyadicFloorValue (n + r) t) ω)
          (X (unitDyadicFloorValue n t) ω) ≤
        dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_ancestor_le_tail
      hX hγ hγq] with ω hω
  filter_upwards [hω] with n hn
  intro r t
  simpa only [unitDyadicFloorValue, unitDyadicAncestorIndex_floorIndex] using
    hn r (unitDyadicFloorIndex (n + r) t)

/-- Almost surely, for every time in the unit interval, the sequence of process samples at
its left dyadic approximations is Cauchy. -/
theorem IsKolmogorovProcess.ae_cauchySeq_unitDyadicFloorValue
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) 1,
      CauchySeq (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω) := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicFloorValue_add_le_tail
      hX hγ hγq] with ω hω
  rw [eventually_atTop] at hω
  obtain ⟨N₀, hN₀⟩ := hω
  intro t
  apply EMetric.cauchySeq_iff'.2
  intro ε hε
  have htail : ∀ᶠ n : ℕ in atTop,
      dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹ < ε :=
    (tendsto_dyadicIncrementThreshold_ancestor_tail_zero hγ).eventually
      (gt_mem_nhds hε)
  rw [eventually_atTop] at htail
  obtain ⟨N₁, hN₁⟩ := htail
  let N := max N₀ N₁
  refine ⟨N, fun m hm ↦ ?_⟩
  let r := m - N
  have hNm : N + r = m := Nat.add_sub_of_le hm
  have hbound := hN₀ N (le_max_left N₀ N₁) r t
  have htailN := hN₁ N (le_max_right N₀ N₁)
  rw [hNm] at hbound
  exact hbound.trans_lt htailN

end DyadicFloorSampleCauchy

section DyadicFloorDenseTime


section

/-- A point of the level-`n` unit dyadic grid, regarded as a real time in `[0, 1]`. -/
def unitDyadicGridTime (n : ℕ) (i : Fin (2 ^ n + 1)) : Set.Icc (0 : ℝ) 1 :=
  ⟨(unitDyadicGrid n i : ℝ), by
    constructor
    · positivity
    · unfold unitDyadicGrid
      push_cast
      apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.le_of_lt_succ i.isLt⟩

@[simp]
theorem unitDyadicGridTime_val (n : ℕ) (i : Fin (2 ^ n + 1)) :
    (unitDyadicGridTime n i).1 = (unitDyadicGrid n i : ℝ) :=
  rfl

/-- At every refinement of a dyadic grid, the left floor index of an old grid point is
the correspondingly refined integer index. -/
theorem unitDyadicFloorIndex_gridTime_add (n r : ℕ) (i : Fin (2 ^ n + 1)) :
    (unitDyadicFloorIndex (n + r) (unitDyadicGridTime n i)).val = i.val * 2 ^ r := by
  simp only [unitDyadicFloorIndex_val, unitDyadicGridTime_val, unitDyadicGrid]
  push_cast
  have harg :
      (2 ^ (n + r) : ℝ) * ((i.val : ℝ) / (2 ^ n : ℝ)) =
        (i.val * 2 ^ r : ℕ) := by
    rw [pow_add]
    push_cast
    field_simp
  rw [harg, Nat.floor_natCast]

/-- Every refinement-level left dyadic approximation of a dyadic grid point is exactly
that grid point. -/
theorem unitDyadicFloorValue_gridTime_add (n r : ℕ) (i : Fin (2 ^ n + 1)) :
    unitDyadicFloorValue (n + r) (unitDyadicGridTime n i) = unitDyadicGrid n i := by
  unfold unitDyadicFloorValue unitDyadicGrid
  simp only [unitDyadicFloorIndex_gridTime_add]
  push_cast
  rw [pow_add]
  field_simp

/-- From the level where a dyadic time first appears onward, all its dyadic floor
approximations equal that time. -/
theorem unitDyadicFloorValue_gridTime_of_le
    {n m : ℕ} (hnm : n ≤ m) (i : Fin (2 ^ n + 1)) :
    unitDyadicFloorValue m (unitDyadicGridTime n i) = unitDyadicGrid n i := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact unitDyadicFloorValue_gridTime_add n r i

/-- Sampling any dense-time family along dyadic floor approximations at a dyadic time is
eventually exactly the original dense-time sample. -/
theorem eventually_sample_unitDyadicFloorValue_gridTime
    {E Ω : Type*} (X : NNRat → Ω → E) (n : ℕ) (i : Fin (2 ^ n + 1)) (ω : Ω) :
    ∀ᶠ m in Filter.atTop,
      X (unitDyadicFloorValue m (unitDyadicGridTime n i)) ω = X (unitDyadicGrid n i) ω := by
  rw [Filter.eventually_atTop]
  exact ⟨n, fun m hnm ↦ congrArg (fun q ↦ X q ω)
    (unitDyadicFloorValue_gridTime_of_le hnm i)⟩

/-- Any topological limit of the dyadic floor samples at a dyadic time is the original
dense-time sample at that time. -/
theorem eq_sample_of_tendsto_unitDyadicFloorValue_gridTime
    {E Ω : Type*} [TopologicalSpace E] [T2Space E]
    (X : NNRat → Ω → E) (n : ℕ) (i : Fin (2 ^ n + 1)) (ω : Ω) (y : E)
    (hlim : Filter.Tendsto
      (fun m ↦ X (unitDyadicFloorValue m (unitDyadicGridTime n i)) ω)
      Filter.atTop (nhds y)) :
    y = X (unitDyadicGrid n i) ω := by
  have horiginal : Filter.Tendsto
      (fun m ↦ X (unitDyadicFloorValue m (unitDyadicGridTime n i)) ω)
      Filter.atTop (nhds (X (unitDyadicGrid n i) ω)) :=
    tendsto_const_nhds.congr'
      ((eventually_sample_unitDyadicFloorValue_gridTime X n i ω).mono
        fun _ hm ↦ hm.symm)
  exact tendsto_nhds_unique hlim horiginal

end

end DyadicFloorDenseTime

section DyadicFloorSampleLimit

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [T2Space E] [CompleteSpace E]

/-- Almost surely, at every time in the unit interval, the process samples along the left
dyadic approximations converge to a unique point. -/
theorem IsKolmogorovProcess.ae_existsUnique_tendsto_unitDyadicFloorValue
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) 1,
      ∃! y : E, Tendsto (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω) atTop (𝓝 y) := by
  filter_upwards
    [IsKolmogorovProcess.ae_cauchySeq_unitDyadicFloorValue hX hγ hγq] with ω hω
  intro t
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hω t)
  refine ⟨y, hy, fun z hz ↦ ?_⟩
  exact tendsto_nhds_unique hz hy

end DyadicFloorSampleLimit

section DyadicFloorLimitControl

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The deterministic modulus obtained from two ancestor tails and one same-level increment. -/
def dyadicFloorLimitModulus (γ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  dyadicIncrementThreshold γ (n + 1) *
      (1 - dyadicIncrementThresholdRatio γ)⁻¹ +
    dyadicIncrementThreshold γ n +
    dyadicIncrementThreshold γ (n + 1) *
      (1 - dyadicIncrementThresholdRatio γ)⁻¹

/-- For a positive exponent, the dyadic floor-limit modulus vanishes at fine scales. -/
theorem tendsto_dyadicFloorLimitModulus_zero {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (dyadicFloorLimitModulus γ) atTop (nhds 0) := by
  have hratio : dyadicIncrementThresholdRatio γ < 1 :=
    dyadicIncrementThresholdRatio_lt_one hγ
  have hthreshold :
      Tendsto (dyadicIncrementThreshold γ) atTop (nhds 0) := by
    rw [show dyadicIncrementThreshold γ =
        fun n : ℕ ↦ dyadicIncrementThresholdRatio γ ^ n by
      funext n
      exact dyadicIncrementThreshold_eq_ratio_pow γ n]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio
  have htail := tendsto_dyadicIncrementThreshold_ancestor_tail_zero hγ
  simpa only [dyadicFloorLimitModulus, zero_add] using!
    (htail.add hthreshold).add htail

/-- A uniform ancestor-tail bound and a same-level comparison bound pass to arbitrary limits of
the two floor-sample sequences. -/
theorem edist_limit_le_dyadicFloorLimitModulus
    {X : NNRat → Ω → E} {γ : ℝ} {n : ℕ} {ω : Ω}
    {s t : Set.Icc (0 : ℝ) 1} {y z : E}
    (htail : ∀ r (u : Set.Icc (0 : ℝ) 1),
      edist (X (unitDyadicFloorValue (n + r) u) ω)
          (X (unitDyadicFloorValue n u) ω) ≤
        dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹)
    (hpair : edist (X (unitDyadicFloorValue n s) ω)
        (X (unitDyadicFloorValue n t) ω) ≤ dyadicIncrementThreshold γ n)
    (hy : Tendsto (fun m : ℕ ↦ X (unitDyadicFloorValue m s) ω) atTop (nhds y))
    (hz : Tendsto (fun m : ℕ ↦ X (unitDyadicFloorValue m t) ω) atTop (nhds z)) :
    edist y z ≤ dyadicFloorLimitModulus γ n := by
  have hy_shift : Tendsto
      (fun r : ℕ ↦ X (unitDyadicFloorValue (n + r) s) ω) atTop (nhds y) :=
    by simpa only [Nat.add_comm] using (tendsto_add_atTop_iff_nat n).mpr hy
  have hz_shift : Tendsto
      (fun r : ℕ ↦ X (unitDyadicFloorValue (n + r) t) ω) atTop (nhds z) :=
    by simpa only [Nat.add_comm] using (tendsto_add_atTop_iff_nat n).mpr hz
  have hy_base : edist y (X (unitDyadicFloorValue n s) ω) ≤
      dyadicIncrementThreshold γ (n + 1) *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
    rw [edist_comm]
    refine le_of_tendsto (tendsto_const_nhds.edist hy_shift) ?_
    exact Eventually.of_forall fun r ↦ by
      simpa only [edist_comm] using htail r s
  have hz_base : edist (X (unitDyadicFloorValue n t) ω) z ≤
      dyadicIncrementThreshold γ (n + 1) *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
    refine le_of_tendsto (tendsto_const_nhds.edist hz_shift) ?_
    exact Eventually.of_forall fun r ↦ by
      simpa only [edist_comm] using htail r t
  unfold dyadicFloorLimitModulus
  calc
    edist y z ≤ edist y (X (unitDyadicFloorValue n s) ω) +
        edist (X (unitDyadicFloorValue n s) ω) z :=
      edist_triangle _ _ _
    _ ≤ edist y (X (unitDyadicFloorValue n s) ω) +
        (edist (X (unitDyadicFloorValue n s) ω)
            (X (unitDyadicFloorValue n t) ω) +
          edist (X (unitDyadicFloorValue n t) ω) z) :=
      add_le_add le_rfl (edist_triangle _ _ _)
    _ = (edist y (X (unitDyadicFloorValue n s) ω) +
          edist (X (unitDyadicFloorValue n s) ω)
            (X (unitDyadicFloorValue n t) ω)) +
        edist (X (unitDyadicFloorValue n t) ω) z := by
      rw [add_assoc]
    _ ≤ (dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹) +
        dyadicIncrementThreshold γ n +
        (dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹) := by
      exact add_le_add (add_le_add hy_base hpair) hz_base

/-- Almost surely, at every sufficiently fine dyadic scale, any limits of the floor-sample
sequences at two ordered times in one cell obey the vanishing floor-limit modulus. -/
theorem IsKolmogorovProcess.ae_eventually_edist_floorSample_limits_le_modulus
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ s t : Set.Icc (0 : ℝ) 1,
      s.1 ≤ t.1 → t.1 - s.1 ≤ ((2 : ℝ) ^ n)⁻¹ →
        ∀ y z : E,
          Tendsto (fun m : ℕ ↦ X (unitDyadicFloorValue m s) ω) atTop (nhds y) →
          Tendsto (fun m : ℕ ↦ X (unitDyadicFloorValue m t) ω) atTop (nhds z) →
          edist y z ≤ dyadicFloorLimitModulus γ n := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicFloorValue_add_le_tail hX hγ hγq,
      IsKolmogorovProcess.ae_eventually_edist_unitDyadicFloorValue_le_threshold hX hγ hγq]
      with ω htail hpair
  filter_upwards [htail, hpair] with n hn_tail hn_pair
  intro s t hst hgap y z hy hz
  exact edist_limit_le_dyadicFloorLimitModulus hn_tail (hn_pair s t hst hgap) hy hz

end

end DyadicFloorLimitControl

section DyadicFloorLimitPath

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoMetricSpace E] [CompleteSpace E]

/-- The canonical Mathlib limit of the left dyadic samples on the unit interval. -/
def unitDyadicFloorLimit (X : NNRat → Ω → E) (ω : Ω)
    (t : Set.Icc (0 : ℝ) 1) : E :=
  letI : Nonempty E := ⟨X 0 ω⟩
  limUnder atTop (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω)

/-- A Cauchy sequence of left dyadic samples converges to its canonical dyadic-floor limit. -/
theorem tendsto_unitDyadicFloorLimit_of_cauchySeq
    {X : NNRat → Ω → E} {ω : Ω} {t : Set.Icc (0 : ℝ) 1}
    (h : CauchySeq (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω)) :
    Tendsto (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω) atTop
      (nhds (unitDyadicFloorLimit X ω t)) := by
  simpa only [unitDyadicFloorLimit] using h.tendsto_limUnder

/-- Almost surely, the left dyadic samples converge to the canonical limit simultaneously
at every time in the unit interval. -/
theorem IsKolmogorovProcess.ae_tendsto_unitDyadicFloorLimit
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω) atTop
        (nhds (unitDyadicFloorLimit X ω t)) := by
  filter_upwards
    [IsKolmogorovProcess.ae_cauchySeq_unitDyadicFloorValue hX hγ hγq] with ω hω
  exact fun t ↦ tendsto_unitDyadicFloorLimit_of_cauchySeq (hω t)

/-- Almost surely, on every sufficiently fine scale, the canonical limit path obeys the
dyadic floor-limit modulus for all ordered pairs of nearby unit-interval times. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicFloorLimit_le_modulus
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ s t : Set.Icc (0 : ℝ) 1,
      s.1 ≤ t.1 → t.1 - s.1 ≤ ((2 : ℝ) ^ n)⁻¹ →
        edist (unitDyadicFloorLimit X ω s) (unitDyadicFloorLimit X ω t) ≤
          dyadicFloorLimitModulus γ n := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_floorSample_limits_le_modulus hX hγ hγq,
      IsKolmogorovProcess.ae_tendsto_unitDyadicFloorLimit hX hγ hγq]
      with ω hmod hlim
  filter_upwards [hmod] with n hn
  intro s t hst hgap
  exact hn s t hst hgap _ _ (hlim s) (hlim t)

/-- Almost surely, the canonical dyadic-floor limit is continuous on the unit interval. -/
theorem IsKolmogorovProcess.ae_continuous_unitDyadicFloorLimit
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, Continuous (unitDyadicFloorLimit X ω) := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicFloorLimit_le_modulus
      hX hγ hγq] with ω hω
  apply UniformContinuous.continuous
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hεE : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hsmall : ∀ᶠ n : ℕ in atTop,
      dyadicFloorLimitModulus γ n < ENNReal.ofReal ε :=
    (tendsto_dyadicFloorLimitModulus_zero hγ).eventually (gt_mem_nhds hεE)
  obtain ⟨n, hn, hmodε⟩ := (hω.and hsmall).exists
  refine ⟨((2 : ℝ) ^ n)⁻¹, by positivity, ?_⟩
  intro s t hst
  have hgap_abs : |t.1 - s.1| < ((2 : ℝ) ^ n)⁻¹ := by
    change dist s.1 t.1 < ((2 : ℝ) ^ n)⁻¹ at hst
    simpa only [Real.dist_eq, abs_sub_comm] using hst
  have hedist :
      edist (unitDyadicFloorLimit X ω s) (unitDyadicFloorLimit X ω t) <
        ENNReal.ofReal ε := by
    rcases le_total s.1 t.1 with hle | hle
    · exact (hn s t hle (le_abs_self _ |>.trans hgap_abs.le)).trans_lt hmodε
    · rw [edist_comm]
      exact (hn t s hle (le_abs_self _ |>.trans (by
        simpa only [abs_sub_comm] using hgap_abs.le))).trans_lt hmodε
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] at hedist
  exact hedist

end

end DyadicFloorLimitPath

section DyadicFloorConvergenceInMeasure

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- A nonnegative rational bounded by one, embedded in the real unit interval. -/
def unitIccOfNNRat (t : NNRat) (ht : t ≤ 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(t : ℝ), by positivity, by exact_mod_cast ht⟩

@[simp]
theorem unitIccOfNNRat_val (t : NNRat) (ht : t ≤ 1) :
    (unitIccOfNNRat t ht).1 = (t : ℝ) :=
  rfl

/-- The dyadic-floor time is within one level-`n` cell of the original nonnegative rational
time. -/
theorem edist_unitDyadicFloorValue_unitIccOfNNRat_le
    (n : ℕ) (t : NNRat) (ht : t ≤ 1) :
    edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t ≤
      ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) := by
  rw [edist_dist, NNRat.dist_eq, Rat.dist_eq]
  push_cast
  rw [abs_of_nonpos]
  · apply ENNReal.ofReal_le_ofReal
    simpa only [unitIccOfNNRat_val, neg_sub] using
      sub_unitDyadicFloorValue_le n (unitIccOfNNRat t ht)
  · exact sub_nonpos.mpr (by
      simpa only [unitIccOfNNRat_val] using
        unitDyadicFloorValue_le n (unitIccOfNNRat t ht))

/-- Markov's inequality applied to one increment of a Kolmogorov process. -/
theorem measure_edist_ge_le_of_isKolmogorovProcess
    {T : Type*} [PseudoEMetricSpace T] {P : Measure Ω}
    {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (s t : T) (ε : ℝ≥0∞)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P {ω | ε ≤ edist (X s ω) (X t ω)} ≤ M * edist s t ^ q / ε ^ p := by
  calc
    P {ω | ε ≤ edist (X s ω) (X t ω)} =
        P {ω | ε ^ p ≤ edist (X s ω) (X t ω) ^ p} := by
      congr 1
      ext ω
      change (ε ≤ edist (X s ω) (X t ω)) ↔
        (ε ^ p ≤ edist (X s ω) (X t ω) ^ p)
      exact (ENNReal.rpow_le_rpow_iff hX.p_pos).symm
    _ ≤ (∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P) / ε ^ p := by
      apply meas_ge_le_lintegral_div
      · exact (hX.measurable_edist.pow_const p).aemeasurable
      · exact (ENNReal.rpow_eq_zero_iff_of_pos hX.p_pos).not.mpr hε0
      · exact (ENNReal.rpow_eq_top_iff_of_pos hX.p_pos).not.mpr hεtop
    _ ≤ M * edist s t ^ q / ε ^ p := by
      gcongr
      exact hX.kolmogorovCondition s t

/-- The dyadic-floor times converge to the represented nonnegative rational time. -/
theorem tendsto_edist_unitDyadicFloorValue_unitIccOfNNRat
    (t : NNRat) (ht : t ≤ 1) :
    Tendsto (fun n ↦ edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t)
      atTop (nhds 0) := by
  have hbound : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹))
      atTop (nhds 0) := by
    have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    convert ENNReal.tendsto_ofReal hpow using 1
    · funext n
      rw [inv_pow]
    · simp only [ENNReal.ofReal_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ zero_le)
    (fun n ↦ edist_unitDyadicFloorValue_unitIccOfNNRat_le n t ht)

/-- At a fixed nonnegative rational time in `[0, 1]`, samples of a Kolmogorov process at the left
dyadic approximations converge in measure to the original process sample. -/
theorem IsKolmogorovProcess.tendstoInMeasure_unitDyadicFloorValue
    {P : Measure Ω} {X : NNRat → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (t : NNRat) (ht : t ≤ 1) :
    TendstoInMeasure P
      (fun n ↦ X (unitDyadicFloorValue n (unitIccOfNNRat t ht))) atTop (X t) := by
  refine tendstoInMeasure_of_ne_top fun ε hε hεtop ↦ ?_
  have hed := tendsto_edist_unitDyadicFloorValue_unitIccOfNNRat t ht
  have hrpow : Tendsto
      (fun n ↦ edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t ^ q)
      atTop (nhds 0) := by
    simpa only [ENNReal.zero_rpow_of_pos hX.q_pos] using hed.ennrpow_const q
  have hrhs : Tendsto
      (fun n ↦ M * edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t ^ q / ε ^ p)
      atTop (nhds 0) := by
    have hmul : Tendsto
        (fun n ↦ (M : ℝ≥0∞) *
          edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t ^ q)
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul (a := (M : ℝ≥0∞)) hrpow
          (Or.inr ENNReal.coe_ne_top)
    have hdenom0 : ε ^ p ≠ 0 :=
      (ENNReal.rpow_eq_zero_iff_of_pos hX.p_pos).not.mpr hε.ne'
    have hscaled := ENNReal.Tendsto.const_mul (a := (ε ^ p)⁻¹) hmul
      (Or.inr (ENNReal.inv_ne_top.mpr hdenom0))
    simpa only [mul_zero, div_eq_mul_inv, mul_comm] using hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
    (fun _ ↦ zero_le) (fun n ↦
      measure_edist_ge_le_of_isKolmogorovProcess hX _ _ ε hε.ne' hεtop)

end DyadicFloorConvergenceInMeasure

section DyadicFloorUnitModification

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- At every fixed nonnegative rational time in `[0, 1]`, the canonical floor-sample limit is a
modification of the original process sample. -/
theorem IsKolmogorovProcess.ae_eq_unitDyadicFloorLimit
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (t : NNRat) (ht : t ≤ 1) :
    X t =ᵐ[P] fun ω ↦ unitDyadicFloorLimit X ω (unitIccOfNNRat t ht) := by
  let samples : ℕ → Ω → E :=
    fun n ↦ X (unitDyadicFloorValue n (unitIccOfNNRat t ht))
  let limit : Ω → E := fun ω ↦ unitDyadicFloorLimit X ω (unitIccOfNNRat t ht)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ samples n ω) atTop (nhds (limit ω)) := by
    filter_upwards [IsKolmogorovProcess.ae_tendsto_unitDyadicFloorLimit hX hγ hγq]
      with ω hω
    exact hω (unitIccOfNNRat t ht)
  have hsamples : ∀ n, AEStronglyMeasurable (samples n) P := by
    intro n
    exact (hX.measurable (unitDyadicFloorValue n (unitIccOfNNRat t ht))).aestronglyMeasurable
  have htendsto_limit : TendstoInMeasure P samples atTop limit :=
    tendstoInMeasure_of_tendsto_ae hsamples hlim
  have htendsto_original : TendstoInMeasure P samples atTop (X t) :=
    IsKolmogorovProcess.tendstoInMeasure_unitDyadicFloorValue hX t ht
  exact tendstoInMeasure_ae_unique htendsto_original htendsto_limit

/-- A total version of the canonical unit-interval path: retain it when it is continuous and use
the constant initial-sample path on the exceptional set. -/
def continuousUnitDyadicFloorLimit (X : NNRat → Ω → E) (ω : Ω) :
    Set.Icc (0 : ℝ) 1 → E := by
  classical
  exact if Continuous (unitDyadicFloorLimit X ω) then
      unitDyadicFloorLimit X ω
    else
      fun _ ↦ X 0 ω

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The totalized unit-interval path is continuous for every sample. -/
theorem continuous_continuousUnitDyadicFloorLimit
    (X : NNRat → Ω → E) (ω : Ω) :
    Continuous (continuousUnitDyadicFloorLimit X ω) := by
  by_cases h : Continuous (unitDyadicFloorLimit X ω)
  · simpa only [continuousUnitDyadicFloorLimit, ite_eq_left h] using h
  · simp only [continuousUnitDyadicFloorLimit, ite_eq_right h]
    exact continuous_const

/-- At each fixed unit-interval rational time, the totalized continuous path remains a
modification of the original process sample. -/
theorem IsKolmogorovProcess.ae_eq_continuousUnitDyadicFloorLimit
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (t : NNRat) (ht : t ≤ 1) :
    X t =ᵐ[P] fun ω ↦ continuousUnitDyadicFloorLimit X ω (unitIccOfNNRat t ht) := by
  filter_upwards
    [IsKolmogorovProcess.ae_eq_unitDyadicFloorLimit hX hγ hγq t ht,
      IsKolmogorovProcess.ae_continuous_unitDyadicFloorLimit hX hγ hγq]
      with ω hident hcont
  simpa only [continuousUnitDyadicFloorLimit, ite_eq_left hcont] using hident

end

end DyadicFloorUnitModification

end MarkovProcess

end PortComputability
