/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.Basic

/-!
# Maximum closure and clamping of firing scripts

Winning scripts for a fixed divisor are closed under pointwise maximum.
Consequently an effective divisor stays effective after truncating a winning
script from below. A script winning for an effective divisor with one chip
demanded at `q` can also be made nonnegative and zero at `q`.

These statements require neither connectedness nor a choice of vertex type.
They use only the basic chip-firing API. The general truncation statement also
appears in `Utilities.Gonality.LegalFiring`; here it is a short consequence of
maximum closure, without importing the gonality development.
-/

namespace Utilities

variable {G : CFGraph}

/-- Raising a script away from a vertex, while fixing its value at that
vertex, can only increase the principal divisor there. -/
theorem prin_le_of_script_le_of_eq {σ τ : firing_script G}
    (hle : ∀ w, σ w ≤ τ w) {v : G.V} (heq : σ v = τ v) :
    prin G σ v ≤ prin G τ v := by
  rw [prin_apply, prin_apply]
  refine Finset.sum_le_sum fun w _ => ?_
  apply mul_le_mul_of_nonneg_right _ (Int.natCast_nonneg _)
  rw [heq]
  exact sub_le_sub_right (hle w) _

/-- The pointwise maximum of two winning scripts wins for the same divisor.
The starting divisor itself need not be effective. -/
theorem effective_add_prin_max {D : CFDiv G} {σ τ : firing_script G}
    (hσ : effective (D + prin G σ)) (hτ : effective (D + prin G τ)) :
    effective (D + prin G (fun v => max (σ v) (τ v))) := by
  intro v
  by_cases h : σ v ≤ τ v
  · have hle := prin_le_of_script_le_of_eq
      (fun w => le_max_right (σ w) (τ w)) (max_eq_right h).symm
    exact le_trans (hτ v) (add_le_add le_rfl hle)
  · have hle := prin_le_of_script_le_of_eq
      (fun w => le_max_left (σ w) (τ w))
      (max_eq_left (le_of_not_ge h)).symm
    exact le_trans (hσ v) (add_le_add le_rfl hle)

/-- Subtract a constant from a script and replace negative values by zero. -/
def clampScript (σ : firing_script G) (c : ℤ) : firing_script G :=
  fun v => max (σ v - c) 0

@[simp] theorem clampScript_apply (σ : firing_script G) (c : ℤ) (v : G.V) :
    clampScript σ c v = max (σ v - c) 0 := rfl

theorem clampScript_nonneg (σ : firing_script G) (c : ℤ) (v : G.V) :
    0 ≤ clampScript σ c v := le_max_right _ _

theorem clampScript_eq_zero_of_le (σ : firing_script G) {c : ℤ} {v : G.V}
    (h : σ v ≤ c) : clampScript σ c v = 0 :=
  max_eq_right (sub_nonpos.mpr h)

theorem clampScript_eq_sub_of_le (σ : firing_script G) {c : ℤ} {v : G.V}
    (h : c ≤ σ v) : clampScript σ c v = σ v - c :=
  max_eq_left (sub_nonneg.mpr h)

@[simp] theorem clampScript_at_base (σ : firing_script G) (q : G.V) :
    clampScript σ (σ q) q = 0 := by
  simp [clampScript]

/-- Truncating a winning script preserves effectivity of an effective
starting divisor. No nonnegativity assumption on the script or cutoff is
needed. This does not retain an extra demanded chip. -/
theorem effective_add_prin_clamp {D : CFDiv G} {σ : firing_script G}
    (hD : effective D) (hσ : effective (D + prin G σ)) (c : ℤ) :
    effective (D + prin G (clampScript σ c)) := by
  have hshift : effective (D + prin G (fun v => σ v - c)) := by
    simpa only [prin_sub_const] using hσ
  have hzero : effective (D + prin G (fun _ : G.V => (0 : ℤ))) := by
    simpa only [prin_const, add_zero] using hD
  exact effective_add_prin_max hshift hzero

/-- At a pole where the script vanishes, a nonnegative cutoff keeps it zero. -/
theorem clampScript_eq_zero_of_eq_zero (σ : firing_script G) {q : G.V}
    (hq : σ q = 0) {c : ℤ} (hc : 0 ≤ c) :
    clampScript σ c q = 0 := by
  apply clampScript_eq_zero_of_le
  simpa only [hq] using hc

/-- If a divisor is effective away from `q`, normalize a winning script at
`q` and clamp it at zero without losing effectivity, including at `q`. -/
theorem effective_add_prin_clamp_at {D : CFDiv G} {σ : firing_script G}
    (q : G.V) (hD : q_effective q D) (hσ : effective (D + prin G σ)) :
    effective (D + prin G (clampScript σ (σ q))) := by
  intro v
  by_cases hv : σ q ≤ σ v
  · have hle : prin G (fun w => σ w - σ q) v ≤
        prin G (clampScript σ (σ q)) v :=
      prin_le_of_script_le_of_eq
        (fun w => le_max_left (σ w - σ q) 0)
        (clampScript_eq_sub_of_le σ hv).symm
    rw [prin_sub_const] at hle
    exact le_trans (hσ v) (add_le_add le_rfl hle)
  · have hvq : v ≠ q := by
      intro h
      subst v
      exact hv le_rfl
    have hzero : clampScript σ (σ q) v = 0 :=
      clampScript_eq_zero_of_le σ (le_of_not_ge hv)
    have hle : prin G (fun _ : G.V => (0 : ℤ)) v ≤
        prin G (clampScript σ (σ q)) v :=
      prin_le_of_script_le_of_eq (clampScript_nonneg σ (σ q)) hzero.symm
    have hnonneg : 0 ≤ prin G (clampScript σ (σ q)) v := by
      simpa only [prin_const, Pi.zero_apply] using hle
    exact add_nonneg (hD v hvq) hnonneg

/-- A winning script for an effective divisor with one chip demanded at `q`
can be normalized and clamped at `q`. -/
theorem effective_sub_one_chip_add_prin_clamp_at
    {D : CFDiv G} {σ : firing_script G} (q : G.V)
    (hD : effective D) (hσ : effective (D - one_chip q + prin G σ)) :
    effective (D - one_chip q + prin G (clampScript σ (σ q))) := by
  apply effective_add_prin_clamp_at q _ hσ
  intro v hv
  simpa only [Pi.sub_apply, one_chip, if_neg hv, sub_zero] using hD v

/-- Winnability for a divisor effective away from `q` has a nonnegative
script witness vanishing at `q`. -/
theorem exists_nonneg_firing_script_of_winnable {D : CFDiv G}
    (q : G.V) (hD : q_effective q D) (hwin : winnable G D) :
    ∃ σ : firing_script G,
      σ q = 0 ∧ (∀ v, 0 ≤ σ v) ∧ effective (D + prin G σ) := by
  obtain ⟨D', hD', hEquiv⟩ := hwin
  obtain ⟨σ, hσ⟩ := (principal_iff_eq_prin G (D' - D)).mp hEquiv
  have hWinning : effective (D + prin G σ) := by
    have heq : D + prin G σ = D' := by
      rw [← hσ]
      abel
    rw [heq]
    exact hD'
  exact ⟨clampScript σ (σ q), clampScript_at_base σ q,
    clampScript_nonneg σ (σ q), effective_add_prin_clamp_at q hD hWinning⟩

/-- Reachability of `q` from an effective divisor has a nonnegative winning
script that vanishes at the demanded vertex. -/
theorem exists_nonneg_firing_script_sub_one_chip {D : CFDiv G}
    (q : G.V) (hD : effective D) (hwin : winnable G (D - one_chip q)) :
    ∃ σ : firing_script G,
      σ q = 0 ∧ (∀ v, 0 ≤ σ v) ∧ effective (D - one_chip q + prin G σ) := by
  apply exists_nonneg_firing_script_of_winnable q _ hwin
  intro v hv
  simpa only [Pi.sub_apply, one_chip, if_neg hv, sub_zero] using hD v

end Utilities

/-!
# Degree bounds on the slopes of a winning firing script

On every edge, a script taking an effective divisor to an effective divisor
changes height by at most its degree. To see this, clamp the script at the
lower endpoint. The resulting effective divisor has the same degree, while
its coefficient at that endpoint bounds the contribution of the chosen edge.

The same bound holds when the script first has to pay an effective demand.
No connectedness hypothesis is needed.
-/

namespace Utilities

variable {G : CFGraph}

/-- A winning script for an effective divisor changes height along any
edge by at most the degree of that divisor. This is the one-sided form. -/
theorem script_sub_le_deg_of_effective_add_prin
    {D : CFDiv G} {f : firing_script G}
    (hD : effective D) (hWin : effective (D + prin G f))
    {u v : G.V} (hEdge : 0 < num_edges G u v) :
    f u - f v ≤ deg D := by
  let t := clampScript f (f v)
  have ht : ∀ w, 0 ≤ t w := clampScript_nonneg f (f v)
  have hv : t v = 0 := clampScript_at_base f v
  have hEffective : effective (D + prin G t) :=
    effective_add_prin_clamp hD hWin (f v)
  have hCoeff : (D + prin G t) v ≤ deg (D + prin G t) :=
    Finset.single_le_sum (fun w _ => hEffective w) (Finset.mem_univ v)
  have hDegree : deg (D + prin G t) = deg D := by
    apply (linear_equiv_preserves_deg G D (D + prin G t) _).symm
    change (D + prin G t - D) ∈ principal_divisors G
    apply (principal_iff_eq_prin G _).mpr
    exact ⟨t, by abel⟩
  have hPrin : t u * (num_edges G v u : ℤ) ≤ prin G t v := by
    rw [prin_apply, hv]
    simp only [sub_zero]
    exact Finset.single_le_sum
      (fun w _ => mul_nonneg (ht w) (Int.natCast_nonneg _))
      (Finset.mem_univ u)
  have hMultiplicity : (1 : ℤ) ≤ (num_edges G v u : ℤ) := by
    have hEdge' : 0 < num_edges G v u := by
      simpa only [num_edges_symmetric G u v] using hEdge
    exact_mod_cast hEdge'
  have hMul : t u ≤ t u * (num_edges G v u : ℤ) := by
    nlinarith [ht u]
  have hDifference : f u - f v ≤ t u := le_max_left _ _
  have hDv := hD v
  rw [hDegree] at hCoeff
  change D v + prin G t v ≤ deg D at hCoeff
  omega

/-- The absolute edge slope of a winning script is bounded by the degree
of the effective starting divisor. -/
theorem abs_script_sub_le_deg_of_effective_add_prin
    {D : CFDiv G} {f : firing_script G}
    (hD : effective D) (hWin : effective (D + prin G f))
    {u v : G.V} (hEdge : 0 < num_edges G u v) :
    |f u - f v| ≤ deg D := by
  apply abs_le.mpr
  constructor
  · have hEdge' : 0 < num_edges G v u := by
      simpa only [num_edges_symmetric G u v] using hEdge
    have hReverse := script_sub_le_deg_of_effective_add_prin hD hWin hEdge'
    omega
  · exact script_sub_le_deg_of_effective_add_prin hD hWin hEdge

/-- An effective pointwise majorant gives the same edge-slope bound for a
script winning from a possibly signed starting divisor. -/
theorem abs_script_sub_le_deg_of_le
    {D R : CFDiv G} {f : firing_script G}
    (hD : effective D) (hRD : ∀ w, R w ≤ D w)
    (hWin : effective (R + prin G f))
    {u v : G.V} (hEdge : 0 < num_edges G u v) :
    |f u - f v| ≤ deg D := by
  apply abs_script_sub_le_deg_of_effective_add_prin hD _ hEdge
  intro w
  have h := hWin w
  have hle := hRD w
  change 0 ≤ R w + prin G f w at h
  change 0 ≤ D w + prin G f w
  omega

/-- Subtracting an effective demand before applying the script does not
increase the degree bound on any edge slope. -/
theorem abs_script_sub_le_deg_of_effective_sub_add_prin
    {D E : CFDiv G} {f : firing_script G}
    (hD : effective D) (hE : effective E)
    (hWin : effective (D - E + prin G f))
    {u v : G.V} (hEdge : 0 < num_edges G u v) :
    |f u - f v| ≤ deg D := by
  apply abs_script_sub_le_deg_of_effective_add_prin hD _ hEdge
  intro w
  have h := hWin w
  have he := hE w
  change 0 ≤ D w - E w + prin G f w at h
  change 0 ≤ D w + prin G f w
  omega

end Utilities
