/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.GlobalExistence
public import Mathlib.Analysis.ODE.ExistUnique

/-! Global solutions of continuous linear ODEs with coefficients bounded on
each compact time interval. -/

@[expose] public section

open Set
open scoped NNReal Topology

namespace AVenhance.Infra.Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Clamp time to the radius-n window around a specified starting time. -/
def LinearGlobalExistence.linearWindowClamp (s : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  max (s - (n : ℝ)) (min (s + (n : ℝ)) t)

theorem LinearGlobalExistence.linearWindowClamp_mem (s : ℝ) (n : ℕ) (t : ℝ) :
    LinearGlobalExistence.linearWindowClamp s n t ∈ Icc (s - (n : ℝ)) (s + (n : ℝ)) := by
  dsimp [LinearGlobalExistence.linearWindowClamp]
  constructor
  · exact le_max_left _ _
  · apply (max_le_iff).2
    constructor
    · have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · exact min_le_left _ _

theorem LinearGlobalExistence.linearWindowClamp_eq_of_mem (s : ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (s - (n : ℝ)) (s + (n : ℝ))) :
    LinearGlobalExistence.linearWindowClamp s n t = t := by
  simp [LinearGlobalExistence.linearWindowClamp, max_eq_right ht.1, min_eq_right ht.2]

/-- A continuous operator-valued function is bounded on every compact time
interval. -/
lemma LinearGlobalExistence.exists_linearOperator_norm_bound_on_Icc
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (a d : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, t ∈ Icc a d → ‖A t‖ ≤ M := by
  let S : Set ℝ := (fun t => ‖A t‖) '' Icc a d
  have hS : BddAbove S := by
    apply isCompact_Icc.bddAbove_image
    exact continuous_norm.comp hA |>.continuousOn
  let M : ℝ := max (sSup S) 0
  refine ⟨M, le_max_right _ _, ?_⟩
  intro t ht
  have hle : ‖A t‖ ≤ sSup S := le_csSup hS ⟨t, ht, rfl⟩
  exact hle.trans (le_max_left _ _)

/-- Linear vector field with time clamped to a finite window. -/
def LinearGlobalExistence.linearWindowField (A : ℝ → E →L[ℝ] E) (s : ℝ) (n : ℕ) :
    ℝ → E → E := fun t z => A (LinearGlobalExistence.linearWindowClamp s n t) z

theorem LinearGlobalExistence.linearWindowField_continuous (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) (s : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × E => LinearGlobalExistence.linearWindowField A s n p.1 p.2) := by
  have hclamp : Continuous (LinearGlobalExistence.linearWindowClamp s n) := by
    change Continuous (fun t : ℝ => max (s - (n : ℝ)) (min (s + (n : ℝ)) t))
    fun_prop
  have hcoef : Continuous (fun t => A (LinearGlobalExistence.linearWindowClamp s n t)) := hA.comp
      hclamp
  have hcoef' : Continuous (fun p : ℝ × E => A (LinearGlobalExistence.linearWindowClamp s n p.1)) :=
    hcoef.comp continuous_fst
  exact hcoef'.clm_apply continuous_snd

theorem LinearGlobalExistence.exists_linearWindowLip (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) (s : ℝ) (n : ℕ) :
    ∃ K : ℝ≥0, ∀ t, LipschitzWith K (LinearGlobalExistence.linearWindowField A s n t) := by
  obtain ⟨M, hM₀, hM⟩ := LinearGlobalExistence.exists_linearOperator_norm_bound_on_Icc A hA
    (s - (n : ℝ)) (s + (n : ℝ))
  let K : ℝ≥0 := ⟨M, hM₀⟩
  refine ⟨K, ?_⟩
  intro t
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hbound := hM (LinearGlobalExistence.linearWindowClamp s n t)
      (LinearGlobalExistence.linearWindowClamp_mem s n t)
  calc
    ‖LinearGlobalExistence.linearWindowField A s n t x - LinearGlobalExistence.linearWindowField A
        s n t y‖ =
        ‖A (LinearGlobalExistence.linearWindowClamp s n t) (x - y)‖ := by
          simp [LinearGlobalExistence.linearWindowField, map_sub]
    _ ≤ ‖A (LinearGlobalExistence.linearWindowClamp s n t)‖ * ‖x - y‖ :=
      (A (LinearGlobalExistence.linearWindowClamp s n t)).le_opNorm _
    _ ≤ (K : ℝ) * ‖x - y‖ := by
      exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

variable [CompleteSpace E]

theorem LinearGlobalExistence.exists_linearWindowFlow (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) (s : ℝ) (n : ℕ) :
    ∃ Y : ℝ → E → ℝ → E,
      IsFlowOn (LinearGlobalExistence.linearWindowField A s n) Y := by
  obtain ⟨K, hK⟩ := LinearGlobalExistence.exists_linearWindowLip A hA s n
  exact (existsUnique_flowOn_uniform (LinearGlobalExistence.linearWindowField A s n)
    (LinearGlobalExistence.linearWindowField_continuous A hA s n) ⟨K, hK⟩).exists

/-- Chosen flow of the finite-window linear vector field. -/
noncomputable def LinearGlobalExistence.linearWindowFlow (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) (s : ℝ) (n : ℕ) : ℝ → E → ℝ → E :=
  Classical.choose (LinearGlobalExistence.exists_linearWindowFlow A hA s n)

theorem LinearGlobalExistence.linearWindowFlow_isFlow (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) (s : ℝ) (n : ℕ) :
    IsFlowOn (LinearGlobalExistence.linearWindowField A s n)
        (LinearGlobalExistence.linearWindowFlow A hA s n) :=
  Classical.choose_spec (LinearGlobalExistence.exists_linearWindowFlow A hA s n)

theorem LinearGlobalExistence.linearWindowFlow_spec (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) (s : ℝ) (n : ℕ) :
    (∀ x, LinearGlobalExistence.linearWindowFlow A hA s n s x s = x) ∧
    (∀ x, ContinuousOn (fun t => LinearGlobalExistence.linearWindowFlow A hA s n t x s)
      (Icc (s - (n : ℝ)) (s + (n : ℝ)))) ∧
    (∀ x t, t ∈ Ioo (s - (n : ℝ)) (s + (n : ℝ)) →
      HasDerivAt (fun r => LinearGlobalExistence.linearWindowFlow A hA s n r x s)
        (A t (LinearGlobalExistence.linearWindowFlow A hA s n t x s)) t) := by
  have hflow := LinearGlobalExistence.linearWindowFlow_isFlow A hA s n
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact hflow.1 x s
  · intro x
    exact HasDerivAt.continuousOn (fun t _ => hflow.2 x s t)
  · intro x t ht
    have hmem : t ∈ Icc (s - (n : ℝ)) (s + (n : ℝ)) := Ioo_subset_Icc_self ht
    have h := hflow.2 x s t
    simp only [LinearGlobalExistence.linearWindowField,
        LinearGlobalExistence.linearWindowClamp_eq_of_mem s n hmem] at h
    simpa [LinearGlobalExistence.linearWindowField] using h

theorem LinearGlobalExistence.linearWindowFlow_eqOn_overlap (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) (s : ℝ) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (x : E) :
    EqOn (fun t => LinearGlobalExistence.linearWindowFlow A hA s n t x s)
      (fun t => LinearGlobalExistence.linearWindowFlow A hA s m t x s)
      (Icc (s - (min n m : ℕ)) (s + (min n m : ℕ))) := by
  let k : ℝ := (min n m : ℝ)
  have hk : 0 < k := by dsimp [k]; exact_mod_cast lt_min hn hm
  obtain ⟨M, hM₀, hM⟩ := LinearGlobalExistence.exists_linearOperator_norm_bound_on_Icc A hA
    (s - k) (s + k)
  let K : ℝ≥0 := ⟨M, hM₀⟩
  have hLip (t : ℝ) (ht : t ∈ Ioo (s - k) (s + k)) :
      LipschitzOnWith K (fun z => A t z) Set.univ := by
    have htime : t ∈ Icc (s - k) (s + k) := Ioo_subset_Icc_self ht
    have hbound := hM t htime
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    have hdiff : A t u - A t v = A t (u - v) := by rw [map_sub]
    rw [hdiff]
    calc
      ‖A t (u - v)‖ ≤ ‖A t‖ * ‖u - v‖ := (A t).le_opNorm _
    _ ≤ (K : ℝ) * ‖u - v‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  have hn' : k ≤ (n : ℝ) := by dsimp [k]; exact_mod_cast min_le_left n m
  have hm' : k ≤ (m : ℝ) := by dsimp [k]; exact_mod_cast min_le_right n m
  have hsubn : Icc (s - k) (s + k) ⊆ Icc (s - (n : ℝ)) (s + (n : ℝ)) := by
    intro r hr
    constructor <;> rcases hr with ⟨hl, hu⟩
    · linarith
    · linarith
  have hsubm : Icc (s - k) (s + k) ⊆ Icc (s - (m : ℝ)) (s + (m : ℝ)) := by
    intro r hr
    constructor <;> rcases hr with ⟨hl, hu⟩
    · linarith
    · linarith
  have hY := LinearGlobalExistence.linearWindowFlow_spec A hA s n
  have hZ := LinearGlobalExistence.linearWindowFlow_spec A hA s m
  have hwindow (r : ℝ) (hr : r ∈ Ioo (s - k) (s + k)) :
      r ∈ Ioo (s - (n : ℝ)) (s + (n : ℝ)) ∧
      r ∈ Ioo (s - (m : ℝ)) (s + (m : ℝ)) := by
    constructor <;> constructor <;> rcases hr with ⟨hl, hu⟩
    · linarith
    · linarith
    · linarith
    · linarith
  have htime : s ∈ Ioo (s - k) (s + k) := by constructor <;> linarith
  have hEq := ODE_solution_unique_of_mem_Icc
    (v := fun t z => A t z) (s := fun _ => Set.univ)
    (K := K) (f := fun t => LinearGlobalExistence.linearWindowFlow A hA s n t x s)
    (g := fun t => LinearGlobalExistence.linearWindowFlow A hA s m t x s)
    (a := s - k) (b := s + k) (t₀ := s)
    hLip htime
    ((hY.2.1 x).mono hsubn)
    (fun t ht => hY.2.2 x t (hwindow t ht).1)
    (fun _ _ => Set.mem_univ _)
    ((hZ.2.1 x).mono hsubm)
    (fun t ht => hZ.2.2 x t (hwindow t ht).2)
    (fun _ _ => Set.mem_univ _)
    (by rw [hY.1 x, hZ.1 x])
  intro t ht
  have ht' : t ∈ Icc (s - k) (s + k) := by simpa [k, Nat.cast_min] using ht
  exact hEq ht'

/-- Least natural radius strictly greater than the elapsed time for a linear flow. -/
noncomputable def LinearGlobalExistence.linearRadiusIndex (s t : ℝ) : ℕ :=
  Nat.find (exists_nat_gt |t - s|)

theorem LinearGlobalExistence.linearRadiusIndex_spec (s t : ℝ) :
    |t - s| < (LinearGlobalExistence.linearRadiusIndex s t : ℝ) :=
  Nat.find_spec (exists_nat_gt |t - s|)

/-- Global linear flow obtained by patching compatible finite-window flows. -/
noncomputable def LinearGlobalExistence.globalLinearFlow (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) : ℝ → E → ℝ → E := fun t x s =>
  LinearGlobalExistence.linearWindowFlow A hA s (LinearGlobalExistence.linearRadiusIndex s t + 1)
      t x s

theorem LinearGlobalExistence.globalLinearFlow_initial (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) (s : ℝ) (x : E) :
    LinearGlobalExistence.globalLinearFlow A hA s x s = x := by
  exact (LinearGlobalExistence.linearWindowFlow_spec A hA s
      (LinearGlobalExistence.linearRadiusIndex s s + 1)).1 x

theorem LinearGlobalExistence.globalLinearFlow_hasDerivAt (A : ℝ → E →L[ℝ] E)
    (hA : Continuous A) (s : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (fun r => LinearGlobalExistence.globalLinearFlow A hA r x s)
      (A t (LinearGlobalExistence.globalLinearFlow A hA t x s)) t := by
  let n := LinearGlobalExistence.linearRadiusIndex s t + 1
  have htRadius : |t - s| < (n : ℝ) := by
    dsimp [n]
    exact lt_trans (LinearGlobalExistence.linearRadiusIndex_spec s t) (Nat.cast_lt.mpr
        (Nat.lt_succ_self _))
  have htWindow : t ∈ Ioo (s - (n : ℝ)) (s + (n : ℝ)) := by
    apply abs_lt.mp at htRadius
    constructor <;> dsimp [n] <;> linarith
  have hderiv := (LinearGlobalExistence.linearWindowFlow_spec A hA s n).2.2 x t htWindow
  have hlocal : (fun r => LinearGlobalExistence.globalLinearFlow A hA r x s) =ᶠ[𝓝 t]
      (fun r => LinearGlobalExistence.linearWindowFlow A hA s n r x s) := by
    filter_upwards [Ioo_mem_nhds htWindow.1 htWindow.2] with r hr
    let m := LinearGlobalExistence.linearRadiusIndex s r + 1
    have hrRadius : |r - s| < (m : ℝ) := by
      dsimp [m]
      exact lt_trans (LinearGlobalExistence.linearRadiusIndex_spec s r)
        (Nat.cast_lt.mpr (Nat.lt_succ_self _))
    have hrWindow : r ∈ Ioo (s - (m : ℝ)) (s + (m : ℝ)) := by
      apply abs_lt.mp at hrRadius
      constructor <;> dsimp [m] <;> linarith
    have heq := LinearGlobalExistence.linearWindowFlow_eqOn_overlap A hA s n m
      (Nat.succ_pos _) (Nat.succ_pos _) x
    have hrmin : r ∈ Icc (s - (min n m : ℕ)) (s + (min n m : ℕ)) := by
      have hn' : (min n m : ℝ) ≤ (n : ℝ) := by exact_mod_cast min_le_left n m
      have hm' : (min n m : ℝ) ≤ (m : ℝ) := by exact_mod_cast min_le_right n m
      have hrn : r ∈ Icc (s - (n : ℝ)) (s + (n : ℝ)) := Ioo_subset_Icc_self hr
      have hrm : r ∈ Icc (s - (m : ℝ)) (s + (m : ℝ)) := Ioo_subset_Icc_self hrWindow
      rcases hrn with ⟨hnl, hnu⟩
      rcases hrm with ⟨hml, hmu⟩
      simp only [mem_Icc, Nat.cast_min]
      by_cases hnm : n ≤ m
      · have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
        rw [min_eq_left hnmR]
        exact ⟨hnl, hnu⟩
      · have hmn : m ≤ n := le_of_not_ge hnm
        have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
        rw [min_eq_right hmnR]
        exact ⟨hml, hmu⟩
    have heq' := heq hrmin
    simpa [LinearGlobalExistence.globalLinearFlow, m, n] using heq'.symm
  have hval : LinearGlobalExistence.globalLinearFlow A hA t x s =
      LinearGlobalExistence.linearWindowFlow A hA s n t x s :=
    hlocal.self_of_nhds
  rw [hval]
  exact hderiv.congr_of_eventuallyEq hlocal

/-- A continuous time-dependent linear system has a unique global flow; no
uniform-in-time bound on its operator coefficients is required. -/
theorem existsUnique_linearFlowOn
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) :
    ∃! V : ℝ → E → ℝ → E,
      IsFlowOn (fun t z => A t z) V := by
  let V : ℝ → E → ℝ → E := LinearGlobalExistence.globalLinearFlow A hA
  have hV : IsFlowOn (fun t z => A t z) V := by
    constructor
    · intro x s
      exact LinearGlobalExistence.globalLinearFlow_initial A hA s x
    · intro x s t
      exact LinearGlobalExistence.globalLinearFlow_hasDerivAt A hA s x t
  refine ⟨V, hV, ?_⟩
  intro W hW
  funext t
  funext x
  funext s
  let a := min s t - 1
  let d := max s t + 1
  obtain ⟨M, hM₀, hM⟩ := LinearGlobalExistence.exists_linearOperator_norm_bound_on_Icc A hA a d
  let K : ℝ≥0 := ⟨M, hM₀⟩
  have hLip (r : ℝ) (hr : r ∈ Icc a d) :
      LipschitzOnWith K (fun z => A r z) Set.univ := by
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro u w
    rw [dist_eq_norm, dist_eq_norm]
    have hdiff : A r u - A r w = A r (u - w) := by rw [map_sub]
    rw [hdiff]
    calc
      ‖A r (u - w)‖ ≤ ‖A r‖ * ‖u - w‖ := (A r).le_opNorm _
      _ ≤ (K : ℝ) * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hM r hr) (norm_nonneg _)
  have hYcont : Continuous (fun r => V r x s) := by
    exact continuous_iff_continuousAt.mpr fun r => (hV.2 x s r).continuousAt
  have hWcont : Continuous (fun r => W r x s) := by
    exact continuous_iff_continuousAt.mpr fun r => (hW.2 x s r).continuousAt
  by_cases hst : s ≤ t
  · have hEq := ODE_solution_unique_of_mem_Icc_right
      (a := s) (b := t) (v := fun r z => A r z)
      (s := fun _ => Set.univ) (K := K)
      (f := fun r => V r x s) (g := fun r => W r x s)
      (fun r hr => hLip r (by
        change min s t - 1 ≤ r ∧ r ≤ max s t + 1
        rw [min_eq_left hst, max_eq_right hst]
        exact ⟨by linarith [hr.1], by linarith [hr.2]⟩))
      (hYcont.continuousOn.mono (Set.subset_univ _))
      (fun r hr => (hV.2 x s r).hasDerivWithinAt)
      (fun _ _ => Set.mem_univ _)
      (hWcont.continuousOn.mono (Set.subset_univ _))
      (fun r hr => (hW.2 x s r).hasDerivWithinAt)
      (fun _ _ => Set.mem_univ _)
      (by rw [hV.1 x s, hW.1 x s])
    exact (hEq ⟨hst, le_rfl⟩).symm
  · have hts : t ≤ s := le_of_not_ge hst
    have hEq := ODE_solution_unique_of_mem_Icc_left
      (a := t) (b := s) (v := fun r z => A r z)
      (s := fun _ => Set.univ) (K := K)
      (f := fun r => V r x s) (g := fun r => W r x s)
      (fun r hr => hLip r (by
        change min s t - 1 ≤ r ∧ r ≤ max s t + 1
        rw [min_eq_right hts, max_eq_left hts]
        exact ⟨by linarith [hr.1], by linarith [hr.2]⟩))
      (hYcont.continuousOn.mono (Set.subset_univ _))
      (fun r hr => (hV.2 x s r).hasDerivWithinAt)
      (fun _ _ => Set.mem_univ _)
      (hWcont.continuousOn.mono (Set.subset_univ _))
      (fun r hr => (hW.2 x s r).hasDerivWithinAt)
      (fun _ _ => Set.mem_univ _)
      (by rw [hV.1 x s, hW.1 x s])
    exact (hEq ⟨le_rfl, hts⟩).symm

end AVenhance.Infra.Flow
