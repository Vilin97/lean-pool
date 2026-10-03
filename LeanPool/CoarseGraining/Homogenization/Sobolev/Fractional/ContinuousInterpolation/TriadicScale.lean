/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousKFunctional

/-!
# Triadic scale calculus for the continuous `K`-functional

This module contains only the convention-neutral conversion between the
continuous scale variable in the exact `K`-seminorm and its canonical triadic
samples.  The intervals use `(t_{j+1}, t_j] ∩ (0,1)`: this makes them disjoint
and removes the endpoint at which the open-scale representative is totalized
to zero.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal
open MeasureTheory

noncomputable section

/-- The canonical triadic member of the source scale carrier: `t_j = 3^{-j}`. -/
def triadicContinuousKScale (j : ℕ) : ContinuousKScale :=
  ⟨((3 : ℝ)⁻¹) ^ j, by
    constructor
    · positivity
    · exact pow_le_one₀ (by positivity) (by norm_num)⟩

@[simp] theorem triadicContinuousKScale_zero : triadicContinuousKScale 0 = ⟨1, by
    constructor <;> norm_num⟩ := by
  rfl

theorem triadicContinuousKScale_pos (j : ℕ) : 0 < (triadicContinuousKScale j).1 :=
  ContinuousKScale.pos _

theorem triadicContinuousKScale_le_one (j : ℕ) : (triadicContinuousKScale j).1 ≤ 1 :=
  ContinuousKScale.le_one _

theorem triadicContinuousKScale_succ (j : ℕ) :
    (triadicContinuousKScale (j + 1)).1 = (triadicContinuousKScale j).1 / 3 := by
  simp only [triadicContinuousKScale, inv_pow, pow_succ]
  ring

theorem triadicContinuousKScale_succ_lt (j : ℕ) :
    (triadicContinuousKScale (j + 1)).1 < (triadicContinuousKScale j).1 := by
  rw [triadicContinuousKScale_succ]
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)]
  nlinarith [triadicContinuousKScale_pos j]

theorem triadicContinuousKScale_antitone {j k : ℕ} (hjk : j ≤ k) :
    (triadicContinuousKScale k).1 ≤ (triadicContinuousKScale j).1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction m with
  | zero => exact le_rfl
  | succ m ihm =>
    calc
      (triadicContinuousKScale (j + (m + 1))).1 =
          (triadicContinuousKScale (j + m + 1)).1 := by congr 1
      _ ≤ (triadicContinuousKScale (j + m)).1 :=
          (triadicContinuousKScale_succ_lt (j + m)).le
      _ ≤ (triadicContinuousKScale j).1 := ihm

/-- The disjoint scale interval associated to the sample at depth `j`. -/
def triadicContinuousKInterval (j : ℕ) : Set ℝ :=
  Set.Ioc (triadicContinuousKScale (j + 1)).1 (triadicContinuousKScale j).1 ∩
    Set.Ioo (0 : ℝ) 1

theorem measurableSet_triadicContinuousKInterval (j : ℕ) :
    MeasurableSet (triadicContinuousKInterval j) :=
  measurableSet_Ioc.inter measurableSet_Ioo

theorem triadicContinuousKInterval_subset_openScale (j : ℕ) :
    triadicContinuousKInterval j ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro t ht
  exact ht.2

theorem mem_triadicContinuousKInterval_iff (j : ℕ) {t : ℝ} :
    t ∈ triadicContinuousKInterval j ↔
      (triadicContinuousKScale (j + 1)).1 < t ∧
      t ≤ (triadicContinuousKScale j).1 ∧ 0 < t ∧ t < 1 := by
  simp only [triadicContinuousKInterval, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hpos, hone⟩
    exact ⟨hlower, hupper, hpos, hone⟩
  · rintro ⟨hlower, hupper, hpos, hone⟩
    exact ⟨⟨hlower, hupper⟩, hpos, hone⟩

theorem triadicContinuousKInterval_pairwiseDisjoint :
    Pairwise (fun j k =>
      Disjoint (triadicContinuousKInterval j) (triadicContinuousKInterval k)) := by
  intro j k hjk
  have disjoint_of_lt : ∀ {a b : ℕ}, a < b →
      Disjoint (triadicContinuousKInterval a) (triadicContinuousKInterval b) := by
    intro a b hab
    apply Set.disjoint_left.2
    intro t hta htb
    obtain ⟨hta_lower, -, -, -⟩ := (mem_triadicContinuousKInterval_iff a).1 hta
    obtain ⟨-, htb_upper, -, -⟩ := (mem_triadicContinuousKInterval_iff b).1 htb
    have hscale : (triadicContinuousKScale b).1 ≤
        (triadicContinuousKScale (a + 1)).1 :=
      triadicContinuousKScale_antitone (Nat.succ_le_iff.2 hab)
    exact (not_lt_of_ge (htb_upper.trans hscale)) hta_lower
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · exact disjoint_of_lt hjk
  · exact (disjoint_of_lt hkj).symm

/-- The triadic intervals form a disjoint partition of the exact open scale
interval.  The choice `(t_{j+1},t_j]` assigns every triadic endpoint to its
finer neighbor, while the extra intersection removes `1`. -/
theorem iUnion_triadicContinuousKInterval :
    ⋃ j : ℕ, triadicContinuousKInterval j = Set.Ioo (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun j => triadicContinuousKInterval_subset_openScale j
  · intro t ht
    have hlimit : Filter.Tendsto (fun n : ℕ => ((3 : ℝ)⁻¹) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have hex : ∃ n : ℕ, ((3 : ℝ)⁻¹) ^ n < t := by
      rcases (hlimit.eventually (eventually_lt_nhds ht.1)).exists with ⟨n, hn⟩
      exact ⟨n, hn⟩
    let n := Nat.find hex
    have hn : ((3 : ℝ)⁻¹) ^ n < t := Nat.find_spec hex
    have hn_ne_zero : n ≠ 0 := by
      intro hn_zero
      have : (1 : ℝ) < t := by simpa [hn_zero] using hn
      exact (not_lt_of_ge ht.2.le) this
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne_zero
    refine Set.mem_iUnion.2 ⟨j, (mem_triadicContinuousKInterval_iff j).2 ?_⟩
    constructor
    · simpa [triadicContinuousKScale, hj, Nat.succ_eq_add_one] using hn
    constructor
    · apply le_of_not_gt
      intro hcontra
      have hp : ((3 : ℝ)⁻¹) ^ j < t := by
        simpa [triadicContinuousKScale] using hcontra
      have hmin := Nat.find_min' hex hp
      change n ≤ j at hmin
      rw [hj] at hmin
      omega
    · exact ⟨ht.1, ht.2⟩

/-- On a triadic interval, the sampled `K`-functional at the lower endpoint
is bounded by the continuous value, which is bounded by the upper sample. -/
theorem continuousKFunctional_bounds_on_triadicContinuousKInterval {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) (j : ℕ) {t : ℝ}
    (ht : t ∈ triadicContinuousKInterval j) :
    continuousKFunctional (triadicContinuousKScale (j + 1)) F ≤
      continuousKFunctional ⟨t, ⟨ht.2.1, ht.2.2.le⟩⟩ F ∧
    continuousKFunctional ⟨t, ⟨ht.2.1, ht.2.2.le⟩⟩ F ≤
      continuousKFunctional (triadicContinuousKScale j) F := by
  constructor
  · exact continuousKFunctional_mono ht.1.1.le F
  · exact continuousKFunctional_mono ht.1.2 F

/-- The lower sampled square-weight used for a single triadic interval. -/
noncomputable def triadicContinuousKLowerSampleWeight {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (triadicContinuousKScale j).1 (-2 * s.1)) *
    ENNReal.ofReal (continuousKFunctional (triadicContinuousKScale (j + 1)) F ^ 2) *
    ENNReal.ofReal ((triadicContinuousKScale j).1)⁻¹

/-- The upper sampled square-weight used for a single triadic interval. -/
noncomputable def triadicContinuousKUpperSampleWeight {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (triadicContinuousKScale (j + 1)).1 (-2 * s.1)) *
    ENNReal.ofReal (continuousKFunctional (triadicContinuousKScale j) F ^ 2) *
    ENNReal.ofReal ((triadicContinuousKScale (j + 1)).1)⁻¹

private theorem continuousKSeminormIntegrand_bounds_on_triadicContinuousKInterval {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (j : ℕ) {t : ℝ}
    (ht : t ∈ triadicContinuousKInterval j) :
    triadicContinuousKLowerSampleWeight s F j ≤ continuousKSeminormIntegrand s.1 F t ∧
      continuousKSeminormIntegrand s.1 F t ≤ triadicContinuousKUpperSampleWeight s F j := by
  rw [continuousKSeminormIntegrand_eq_of_mem s.1 F ht.2]
  obtain ⟨hK_lower, hK_upper⟩ :=
    continuousKFunctional_bounds_on_triadicContinuousKInterval F j ht
  have hs : 0 ≤ s.1 := s.2.1.le
  have hrpow_lower : Real.rpow (triadicContinuousKScale j).1 (-2 * s.1) ≤
      Real.rpow t (-2 * s.1) := by
    exact Real.rpow_le_rpow_of_nonpos ht.2.1 ht.1.2 (by linarith)
  have hrpow_upper : Real.rpow t (-2 * s.1) ≤
      Real.rpow (triadicContinuousKScale (j + 1)).1 (-2 * s.1) := by
    exact Real.rpow_le_rpow_of_nonpos (triadicContinuousKScale_pos (j + 1)) ht.1.1.le
      (by linarith)
  have hsq_lower : continuousKFunctional (triadicContinuousKScale (j + 1)) F ^ 2 ≤
      continuousKFunctional ⟨t, ⟨ht.2.1, ht.2.2.le⟩⟩ F ^ 2 := by
    exact (sq_le_sq₀ (continuousKFunctional_nonneg _ F)
      (continuousKFunctional_nonneg _ F)).2 hK_lower
  have hsq_upper : continuousKFunctional ⟨t, ⟨ht.2.1, ht.2.2.le⟩⟩ F ^ 2 ≤
      continuousKFunctional (triadicContinuousKScale j) F ^ 2 := by
    exact (sq_le_sq₀ (continuousKFunctional_nonneg _ F)
      (continuousKFunctional_nonneg _ F)).2 hK_upper
  have hinv_lower : ((triadicContinuousKScale j).1)⁻¹ ≤ t⁻¹ := by
    exact (inv_le_inv₀ (triadicContinuousKScale_pos j) ht.2.1).2 ht.1.2
  have hinv_upper : t⁻¹ ≤ ((triadicContinuousKScale (j + 1)).1)⁻¹ := by
    exact (inv_le_inv₀ ht.2.1 (triadicContinuousKScale_pos (j + 1))).2 ht.1.1.le
  constructor
  · exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hrpow_lower)
        (ENNReal.ofReal_le_ofReal hsq_lower)) (ENNReal.ofReal_le_ofReal hinv_lower)
  · exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hrpow_upper)
        (ENNReal.ofReal_le_ofReal hsq_upper)) (ENNReal.ofReal_le_ofReal hinv_upper)

/-- A two-sided comparison of one continuous weighted scale interval with its
two adjacent sampled weighted squares.  It is valid in `ℝ≥0∞` with no
finiteness assumption. -/
theorem triadicContinuousKInterval_lintegral_bounds {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (j : ℕ) :
    triadicContinuousKLowerSampleWeight s F j *
        volume (triadicContinuousKInterval j) ≤
      ∫⁻ t in triadicContinuousKInterval j, continuousKSeminormIntegrand s.1 F t ∧
    (∫⁻ t in triadicContinuousKInterval j, continuousKSeminormIntegrand s.1 F t) ≤
      triadicContinuousKUpperSampleWeight s F j *
        volume (triadicContinuousKInterval j) := by
  constructor
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' (measurableSet_triadicContinuousKInterval j) fun t ht =>
      (continuousKSeminormIntegrand_bounds_on_triadicContinuousKInterval s F j ht).1
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' (measurableSet_triadicContinuousKInterval j) fun t ht =>
      (continuousKSeminormIntegrand_bounds_on_triadicContinuousKInterval s F j ht).2

end

end Homogenization
