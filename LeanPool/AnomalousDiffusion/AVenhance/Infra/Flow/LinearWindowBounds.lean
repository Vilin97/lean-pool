/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.LinearGlobalExistence
public import Mathlib.Analysis.ODE.Gronwall

/-! Grönwall bounds for global linear flows with coefficients bounded only on
the finite time window under consideration. -/

@[expose] public section

open Set
open scoped Topology

namespace AVenhance.Infra.Flow

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : ℝ → E →L[ℝ] E} {V : ℝ → E → ℝ → E}

theorem LinearWindowBounds.linearFlow_norm_bound_forward
    (hV : IsFlowOn (fun t z => A t z) V)
    {a d s t M : ℝ} (has : a ≤ s) (hst : s ≤ t) (htd : t ≤ d)
    (hM : ∀ r, r ∈ Icc a d → ‖A r‖ ≤ M) :
    ∀ v, ‖V t v s‖ ≤ Real.exp (M * (t - s)) * ‖v‖ := by
  intro v
  have hfcont : ContinuousOn (fun r => V r v s) (Icc s t) :=
    HasDerivAt.continuousOn (fun r _ => hV.2 v s r)
  have hfderiv (r : ℝ) : HasDerivAt (fun q => V q v s)
      (A r (V r v s)) r := by
    simpa using hV.2 v s r
  have hfwithin : ∀ r ∈ Ico s t,
      HasDerivWithinAt (fun q => V q v s) (A r (V r v s)) (Ici r) r :=
    fun r _ => (hfderiv r).hasDerivWithinAt
  have hstart : ‖V s v s‖ ≤ ‖v‖ := by rw [hV.1]
  have hbound (r : ℝ) (hr : r ∈ Ico s t) :
      ‖A r (V r v s)‖ ≤ M * ‖V r v s‖ := by
    calc
      ‖A r (V r v s)‖ ≤ ‖A r‖ * ‖V r v s‖ := (A r).le_opNorm _
      _ ≤ M * ‖V r v s‖ := mul_le_mul_of_nonneg_right
        (hM r ⟨le_trans has hr.1, le_trans hr.2.le htd⟩)
        (norm_nonneg _)
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (δ := ‖v‖) (K := M) (ε := 0) (a := s) (b := t)
    hfcont hfwithin (by simp [hV.1]) (fun r hr => by simpa using hbound r hr)
    t ⟨hst, le_rfl⟩
  calc
    ‖V t v s‖ ≤ ‖v‖ * Real.exp (M * (t - s)) := by
      simpa [gronwallBound_ε0] using hgr
    _ = Real.exp (M * (t - s)) * ‖v‖ := mul_comm _ _

/-- A linear solution grows at most exponentially on a compact window, in
either target-time orientation. The coefficient needs a bound only on that
window. -/
theorem linearFlow_norm_bound_on_window
    (hV : IsFlowOn (fun t z => A t z) V)
    {a d s M : ℝ} (hs : s ∈ Icc a d)
    (hM : ∀ r, r ∈ Icc a d → ‖A r‖ ≤ M)
    (v : E) :
    ∀ t, t ∈ Icc a d →
      ‖V t v s‖ ≤ Real.exp (M * |t - s|) * ‖v‖ := by
  intro t ht
  by_cases hst : s ≤ t
  · have h := LinearWindowBounds.linearFlow_norm_bound_forward hV hs.1 hst ht.2 hM v
    simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using h
  · have hts : t ≤ s := le_of_not_ge hst
    let Ar : ℝ → E →L[ℝ] E := fun r => -(A (-r))
    let Vr : ℝ → E → ℝ → E := fun q z u => V (-q) z (-u)
    have hVr : IsFlowOn (fun q z => Ar q z) Vr := by
      constructor
      · intro z u
        exact hV.1 z (-u)
      · intro z u q
        have hbase : HasDerivAt (fun r => V r z (-u))
            (A (0 - q) (V (0 - q) z (-u))) (0 - q) := by
          simpa only [zero_sub] using hV.2 z (-u) (-q)
        have hcomp := hbase.comp_const_sub 0 q
        simpa [Ar, Vr, map_neg] using hcomp
    have hrevBound (r : ℝ) (hr : r ∈ Icc (-s) (-t)) : ‖Ar r‖ ≤ M := by
      have htime : -r ∈ Icc a d := by
        constructor
        · exact le_trans ht.1 (by linarith [hr.2])
        · exact le_trans (by linarith [hr.1]) hs.2
      simpa [Ar] using hM (-r) htime
    have h := LinearWindowBounds.linearFlow_norm_bound_forward hVr
      (a := -s) (d := -t) (s := -s) (t := -t) (M := M)
      (by rfl) (by linarith [hts]) (by rfl) (fun r hr => hrevBound r hr) v
    have habs : |t - s| = s - t := by
      rw [abs_of_nonpos (sub_nonpos.mpr hts)]
      ring
    have hrev : ‖V t v s‖ ≤ Real.exp (M * (s - t)) * ‖v‖ := by
      have heq : (-t) - (-s) = s - t := by ring
      simpa [Vr, heq] using h
    calc
      ‖V t v s‖ ≤ Real.exp (M * (s - t)) * ‖v‖ := hrev
      _ = Real.exp (M * |t - s|) * ‖v‖ := by rw [habs]

end

end AVenhance.Infra.Flow
