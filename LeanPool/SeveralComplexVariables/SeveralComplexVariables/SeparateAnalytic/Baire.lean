/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Baire.Lemmas
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LocallyBounded

/-!
# The Baire step in Hartogs' separate-analyticity theorem

A separately continuous function on a product with a compact second factor is uniformly bounded
on some open cylinder. For separately analytic functions of two complex variables, locally
bounded Osgood then gives joint analyticity on that cylinder, retaining the entire interior of
the second factor.

This is the initial cylinder in the proof of Hartogs' theorem in [Boas][Boas2013] (2013),
Section 2.7, Theorem 8. No joint continuity or boundedness is assumed.

## Main results

`exists_open_bounded_cylinder_of_separately_continuous` produces an open cylinder of uniform
boundedness. `exists_analytic_cylinder_of_separately_analytic` is joint analyticity on that
cylinder for separately analytic functions of two variables.

## References

* [H. P. Boas, *Lecture Notes on Several Complex Variables*][Boas2013]
-/

public section

open Filter Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

/-- Baire's theorem gives a uniform bound on an open cylinder from separate continuity and
compactness of the second factor. The compact set may be empty. -/
theorem exists_open_bounded_cylinder_of_separately_continuous
    {X Y F : Type*} [TopologicalSpace X] [BaireSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup F] {U : Set X} {K : Set Y} {f : X → Y → F}
    (hU : IsOpen U) (hne : U.Nonempty) (hK : IsCompact K)
    (hx : ∀ y ∈ K, ContinuousOn (fun x => f x y) U)
    (hy : ∀ x ∈ U, ContinuousOn (f x) K) :
    ∃ V : Set X, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∃ M : ℝ, ∀ x ∈ V, ∀ y ∈ K, ‖f x y‖ ≤ M := by
  let : BaireSpace U := hU.baireSpace
  let : Nonempty U := hne.to_subtype
  let S : ℕ → Set U := fun n => {x | ∀ y ∈ K, ‖f x y‖ ≤ n}
  have hclosed (n : ℕ) : IsClosed (S n) := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun y => isClosed_iInter fun hy =>
      isClosed_le ((continuousOn_iff_continuous_domRestrict.mp (hx y hy)).norm) continuous_const
  have hcover : ⋃ n, S n = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨M, hM⟩ := hK.bddAbove_image (hy x x.property).norm
    obtain ⟨n, hn⟩ := exists_nat_ge M
    exact mem_iUnion.mpr ⟨n, fun y hy => (hM (mem_image_of_mem _ hy)).trans hn⟩
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  refine ⟨Subtype.val '' interior (S n),
    hU.isOpenMap_subtype_val _ isOpen_interior, hn.image _, ?_, n, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · rintro _ ⟨x, hx, rfl⟩ y hy
    exact interior_subset hx y hy

/-- A separately analytic function on a two-variable cylinder is jointly analytic on a smaller
nonempty base times the entire open fiber disc. Only the base shrinks. -/
theorem exists_analytic_cylinder_of_separately_analytic
    {U : Set ℂ} {c : ℂ} {R : ℝ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : (Fin 2 → ℂ) → F} (hU : IsOpen U) (hne : U.Nonempty)
    (hf : ∀ z : Fin 2 → ℂ, z 0 ∈ U → z 1 ∈ closedBall c R →
      ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    ∃ V : Set ℂ, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      AnalyticOnNhd ℂ f {z | z 0 ∈ V ∧ z 1 ∈ ball c R} := by
  have hx (y : ℂ) (hy : y ∈ closedBall c R) :
      ContinuousOn (fun x => f ![x, y]) U := by
    intro x hx
    have h := (hf ![x, y] hx hy 0).continuousAt
    simpa [show (fun w => update ![x, y] 0 w) = (fun w => ![w, y]) by
      funext w i; fin_cases i <;> simp] using h.continuousWithinAt (s := U)
  have hy (x : ℂ) (hx : x ∈ U) :
      ContinuousOn (fun y => f ![x, y]) (closedBall c R) := by
    intro y hy
    have h := (hf ![x, y] hx hy 1).continuousAt
    simpa [show (fun w => update ![x, y] 1 w) = (fun w => ![x, w]) by
      funext w i; fin_cases i <;> simp] using
      h.continuousWithinAt (s := closedBall c R)
  obtain ⟨V, hV, hneV, hVU, M, hM⟩ :=
    exists_open_bounded_cylinder_of_separately_continuous hU hne
      (isCompact_closedBall c R) hx hy
  have hopen : IsOpen {z : Fin 2 → ℂ | z 0 ∈ V ∧ z 1 ∈ ball c R} := by
    change IsOpen ((fun z : Fin 2 → ℂ => z 0) ⁻¹' V ∩
      (fun z : Fin 2 → ℂ => z 1) ⁻¹' ball c R)
    exact (hV.preimage (continuous_apply 0)).inter
      (isOpen_ball.preimage (continuous_apply 1))
  refine ⟨V, hV, hneV, hVU,
    analyticOnNhd_of_separately_analytic_locally_bounded hopen
      (fun z hz i => by
        simpa +unfoldPartialApp only [update] using
          hf z (hVU hz.1) (ball_subset_closedBall hz.2) i) ?_⟩
  intro z hz
  refine ⟨M, Filter.mem_of_superset (hopen.mem_nhds hz) ?_⟩
  intro w hw
  change ‖f w‖ ≤ M
  have he : ![w 0, w 1] = w := by ext i; fin_cases i <;> rfl
  simpa only [he] using hM (w 0) hw.1 (w 1) (ball_subset_closedBall hw.2)

/-- A separately analytic function of two complex variables has a point of joint analyticity in
every nonempty open part of its domain. -/
theorem exists_analyticAt_of_separately_analytic_fin_two
    {U : Set (Fin 2 → ℂ)} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : (Fin 2 → ℂ) → F} (hU : IsOpen U) (hne : U.Nonempty)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    ∃ z ∈ U, AnalyticAt ℂ f z := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  have hprod {z : Fin 2 → ℂ} (h0 : z 0 ∈ ball (a 0) R)
      (h1 : z 1 ∈ closedBall (a 1) R) : z ∈ U := by
    apply hRU
    rw [mem_closedBall, dist_pi_le_iff hR.le]
    intro i
    fin_cases i
    · exact (mem_ball.mp h0).le
    · exact h1
  obtain ⟨V, hV, ⟨x, hx⟩, hVB, hfa⟩ := exists_analytic_cylinder_of_separately_analytic
    isOpen_ball (nonempty_ball.mpr hR) (fun z h0 h1 => hf z (hprod h0 h1))
  have hz : (![x, a 1] : Fin 2 → ℂ) ∈ {z | z 0 ∈ V ∧ z 1 ∈ ball (a 1) R} :=
    ⟨hx, mem_ball_self hR⟩
  exact ⟨![x, a 1], hprod (hVB hx) (mem_closedBall_self hR.le), hfa _ hz⟩

/-- The locus of joint analyticity of a separately analytic two-variable function is a dense open
subset of its open domain. -/
theorem dense_isOpen_analyticAt_of_separately_analytic_fin_two
    {U : Set (Fin 2 → ℂ)} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : (Fin 2 → ℂ) → F} (hU : IsOpen U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    Dense {z : U | AnalyticAt ℂ f z} ∧ IsOpen {z : U | AnalyticAt ℂ f z} := by
  refine ⟨dense_iff_inter_open.mpr ?_,
    (isOpen_analyticAt ℂ f).preimage continuous_subtype_val⟩
  intro V hV hne
  have hVU : Subtype.val '' V ⊆ U := by rintro _ ⟨z, _, rfl⟩; exact z.property
  obtain ⟨z, ⟨w, hw, rfl⟩, ha⟩ := exists_analyticAt_of_separately_analytic_fin_two
    (hU.isOpenMap_subtype_val V hV) (hne.image _) (fun z hz => hf z (hVU hz))
  exact ⟨w, hw, ha⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
