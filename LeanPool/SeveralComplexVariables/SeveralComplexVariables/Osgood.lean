/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CauchySeries

/-!
# Osgood's theorem in finite products

Joint continuity and separate holomorphy imply joint analyticity on an open subset of a finite
complex coordinate space. The stronger Hartogs theorem without continuity is not proved here.
The polydisc Cauchy formula and its series construction live in the imported modules and remain
available through this file.

## Main results

`analyticOnNhd_pi_of_analyticOnNhd_update` is Osgood's theorem on an arbitrary finite coordinate
space `ι → ℂ`: continuity on an open set together with holomorphy in each coordinate separately
yields joint analyticity.
-/

public section

open Complex Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Osgood's theorem on `Fin d → ℂ`, before reindexing to an arbitrary finite coordinate type. -/
private theorem analyticOnNhd_fin_of_analyticOnNhd_update {d : ℕ}
    {U : Set (Fin d → ℂ)} {f : (Fin d → ℂ) → E}
    (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  intro c hc
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hc)
  have hP : closedPolydisc c (fun _ => R) ⊆ U := by
    rw [closedPolydisc_eq_closedBall hR.le]
    exact hRU
  have hfcP : ContinuousOn f (closedPolydisc c (fun _ => R)) := hfc.mono hP
  have hfaP : ∀ z ∈ closedPolydisc c (fun _ => R), ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i) := fun z hz => hf z (hP hz)
  have hPcpt : IsCompact (closedPolydisc c (fun _ => R)) := by
    rw [closedPolydisc_eq_closedBall hR.le]
    exact isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hPcpt.bddAbove_image hfcP.norm
  exact (hasFPowerSeriesOnBall_polydiscCauchy hR hfcP hfaP
    (fun z hz => hM (mem_image_of_mem _ hz))).analyticAt

/-- **Osgood's theorem, finite-product form.** A jointly continuous function on an open subset of
a finite product of copies of `ℂ` is jointly analytic when all of its one-coordinate restrictions
are analytic.

This is weaker than Hartogs' theorem `analyticOnNhd_of_separately_analytic`, which drops the
continuity hypothesis. It is the first step in the proof of that theorem, through the locally
bounded version `analyticOnNhd_of_separately_analytic_locally_bounded`, and therefore cannot be
derived from it. Continuity is present in every application preceding Hartogs' theorem in this
library. -/
theorem analyticOnNhd_pi_of_analyticOnNhd_update
    {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → E}
    (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hf : ∀ z ∈ U, ∀ i,
      AnalyticAt ℂ (fun w => f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let L : (Fin (Fintype.card ι) → ℂ) ≃L[ℂ] (ι → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : ι => ℂ) e
  let V : Set (Fin (Fintype.card ι) → ℂ) := L ⁻¹' U
  let g : (Fin (Fintype.card ι) → ℂ) → E := f ∘ L
  have hV : IsOpen V := hU.preimage L.continuous
  have hgc : ContinuousOn g V :=
    hfc.comp L.continuous.continuousOn (fun _ hz => hz)
  have hL_apply (z : Fin (Fintype.card ι) → ℂ)
      (j : Fin (Fintype.card ι)) : L z (e j) = z j := by
    change (Equiv.piCongrLeft (fun _ : ι => ℂ) e) z (e j) = z j
    exact Equiv.piCongrLeft_apply_apply (fun _ : ι => ℂ) e z j
  have hL_update (z : Fin (Fintype.card ι) → ℂ)
      (j : Fin (Fintype.card ι)) (w : ℂ) :
      L (update z j w) = update (L z) (e j) w := by
    funext i
    obtain ⟨k, rfl⟩ := e.surjective i
    by_cases hkj : k = j
    · subst k
      simp [hL_apply]
    · have hek : e k ≠ e j := fun he => hkj (e.injective he)
      simp [hkj, hek, hL_apply]
  have hga : ∀ z ∈ V, ∀ j,
      AnalyticAt ℂ (fun w => g (update z j w)) (z j) := by
    intro z hz j
    have h := hf (L z) hz (e j)
    convert h using 1
    · funext w
      simp only [g, Function.comp_apply]
      rw [hL_update]
    · exact (hL_apply z j).symm
  have hg := analyticOnNhd_fin_of_analyticOnNhd_update hV hgc hga
  intro z hz
  have hzV : L.symm z ∈ V := by
    change L (L.symm z) ∈ U
    simpa
  have hcomp : AnalyticAt ℂ (g ∘ ⇑L.symm.toContinuousLinearMap) z :=
    AnalyticAt.compContinuousLinearMap (u := L.symm.toContinuousLinearMap)
      (hg (L.symm z) hzV)
  simpa [g, Function.comp_def] using hcomp

end SeveralComplexVariables

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
