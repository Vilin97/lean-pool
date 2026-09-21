/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticSet.Codimension
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HartogsContinuation

/-!
# Removal across a coordinate subspace of codimension two

The model subspace has two final coordinates equal to zero and arbitrary remaining parameters.
Hartogs continuation on cylinders proves removal on any open domain, with Banach-valued targets,
independently of the general analytic-set theorem. The parameter space may have dimension zero,
recovering isolated-point removal in `ℂ²`.

## Main definitions

* `complexCoordinatePlane`: The coordinate subspace obtained by setting the last two complex
  coordinates to zero.

## Main results

* `exists_extension_across_coordinatePlane`: **Coordinate-subspace removal.** The proof uses the
  already proved Hartogs cylinder theorem and gluing, with no dependence on general codimension-two
  removal or local algebra.
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- The coordinate subspace obtained by setting the last two complex coordinates to zero. -/
@[expose] def complexCoordinatePlane : Set ((P × ℂ) × ℂ) := {z | z.1.2 = 0 ∧ z.2 = 0}

/-- The model coordinate subspace is analytic on every open domain. -/
theorem isAnalyticSet_coordinatePlane {U : Set ((P × ℂ) × ℂ)} (hU : IsOpen U) :
    IsAnalyticSet U (U ∩ complexCoordinatePlane) := by
  have h₁ := isAnalyticSet_zeroSet hU
    (f := fun z : (P × ℂ) × ℂ => z.1.2)
    (fun _ _ => analyticAt_snd.comp analyticAt_fst)
  have h₂ := isAnalyticSet_zeroSet hU
    (f := fun z : (P × ℂ) × ℂ => z.2) (fun _ _ => analyticAt_snd)
  convert h₁.inter h₂ using 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, complexCoordinatePlane, mem_ofPred_eq]
  tauto

/-- The last two coordinate directions provide the isolated two-plane slice. -/
theorem hasComplexSliceCodimensionAtLeast_coordinatePlane :
    HasComplexSliceCodimensionAtLeast (complexCoordinatePlane (P := P)) 2 := by
  intro a ha
  let L : (Fin 2 → ℂ) →L[ℂ] ((P × ℂ) × ℂ) :=
    ((0 : (Fin 2 → ℂ) →L[ℂ] P).prod (ContinuousLinearMap.proj 0)).prod
      (ContinuousLinearMap.proj 1)
  have hL (z : Fin 2 → ℂ) : L z = ((0, z 0), z 1) := rfl
  refine ⟨L, ?_, Filter.Eventually.of_forall ?_⟩
  · intro x y he
    have h₀ := congrArg (fun z : (P × ℂ) × ℂ => z.1.2) he
    have h₁ := congrArg (fun z : (P × ℂ) × ℂ => z.2) he
    funext i
    fin_cases i
    · exact h₀
    · exact h₁
  · intro z hz
    have hz₀ : z 0 = 0 := by simpa [complexCoordinatePlane, hL, ha.1] using hz.1
    have hz₁ : z 1 = 0 := by simpa [complexCoordinatePlane, hL, ha.2] using hz.2
    funext i
    fin_cases i
    · exact hz₀
    · exact hz₁

/-- **Coordinate-subspace removal.** The proof uses the already proved Hartogs cylinder
theorem and gluing, with no dependence on general codimension-two removal or local algebra. -/
theorem exists_extension_across_coordinatePlane [FiniteDimensional ℂ P]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ((P × ℂ) × ℂ)} (hU : IsOpen U) {f : ((P × ℂ) × ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (U \ complexCoordinatePlane)) :
    ∃ g, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ complexCoordinatePlane) := by
  let : NormedSpace ℝ P := NormedSpace.restrictScalars ℝ ℂ P
  have hA := isAnalyticSet_coordinatePlane hU
  have hcodim := hasComplexSliceCodimensionAtLeast_coordinatePlane (P := P)
  have hi := (hcodim.mono (inter_subset_right (s := U))).interior_eq_empty (by decide)
  have hdiff : U \ (U ∩ complexCoordinatePlane) = U \ complexCoordinatePlane := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  have hdense : U ⊆ closure (U \ complexCoordinatePlane) := by
    simpa only [hdiff] using hA.subset_closure_sdiff hi
  have hopen : IsOpen (U \ complexCoordinatePlane) := by
    simpa only [hdiff] using hA.isOpen_sdiff
  apply exists_analyticOnNhd_extension_of_local sdiff_subset hdense
  intro a ha
  by_cases haA : a ∈ complexCoordinatePlane
  · obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
    let D : Set (P × ℂ) := ball a.1.1 r ×ˢ ball 0 r
    let D₀ : Set (P × ℂ) := ball a.1.1 r ×ˢ (ball 0 r \ {0})
    let V : Set ((P × ℂ) × ℂ) := D ×ˢ ball 0 r
    have haeq : a = ((a.1.1, 0), 0) := by
      ext <;> simp_all [complexCoordinatePlane]
    have hVU : V ⊆ U := by
      apply Subset.trans _ hrU
      rw [haeq]
      simp only [← ball_prod_same, V, D]
      exact Subset.rfl
    have hne : D₀.Nonempty := by
      have hz : (0 : ℂ) ∈ closure ({0}ᶜ : Set ℂ) := by simp
      obtain ⟨z, hzne, hzr⟩ := Metric.mem_closure_iff.mp hz r hr
      exact ⟨(a.1.1, z), mem_ball_self hr, by simpa [dist_comm] using hzr, hzne⟩
    have hcyl : hartogsCylinder D D₀ 0 r = V \ complexCoordinatePlane := by
      ext z
      simp only [hartogsCylinder, D, D₀, V, complexCoordinatePlane,
        mem_union, mem_prod, Set.mem_sdiff, mem_ofPred_eq, closedBall_zero,
        mem_singleton_iff]
      tauto
    obtain ⟨g, hg, he⟩ := exists_extension_hartogsCylinder (D := D) (D₀ := D₀) (ρ := 0) (R := r)
      (isOpen_ball.prod isOpen_ball) (isPreconnected_ball.prod isPreconnected_ball)
      (isOpen_ball.prod (isOpen_ball.sdiff isClosed_singleton)) hne
      (fun _ hz => ⟨hz.1, hz.2.1⟩) le_rfl hr
      (hf.mono (by rw [hcyl]; exact sdiff_subset_sdiff_left hVU))
    refine ⟨V, g, (isOpen_ball.prod isOpen_ball).prod isOpen_ball, ?_, hVU, hg, ?_⟩
    · exact ⟨⟨mem_ball_self hr, haA.1 ▸ mem_ball_self hr⟩, haA.2 ▸ mem_ball_self hr⟩
    · intro z hz
      exact he (hcyl.symm ▸ ⟨hz.1, hz.2.2⟩)
  · exact ⟨U \ complexCoordinatePlane, f, hopen, ⟨ha, haA⟩, sdiff_subset, hf,
      fun _ _ => rfl⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
