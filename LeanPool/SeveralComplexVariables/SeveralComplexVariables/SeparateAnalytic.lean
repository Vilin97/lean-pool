/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.SeparateAnalytic.Baire
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.SeparateAnalytic.FiberExtension

/-!
# Separate analyticity

Hartogs' theorem asserts joint analyticity from analyticity of all coordinate slices, without
continuity or local boundedness assumptions. The versions with those extra hypotheses are proved
in `Osgood` and `LocallyBounded`.

The proof is by induction on the number of coordinates. One coordinate is split off as a fiber
variable. Baire's theorem and the locally bounded Osgood theorem give joint analyticity on a
thin cylinder whose fiber disc is close to the given point. Hartogs' fiber extension lemma,
which rests on Hartogs' growth lemma for roots of the fiber Taylor coefficients, then gives a
local bound at the given point. The locally bounded Osgood theorem completes the induction step.

References: [Boas][Boas2013] (2013), Section 2.4; [Hörmander][Hormander1973] (1973), Theorem
2.2.8; [Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Theorem 1.5.1.

## Main definitions

* `optionSplit`: Splitting off the `none` coordinate of a finite coordinate space as the fiber
  variable.

## Main results

* `analyticOnNhd_of_separately_analytic`: **Hartogs' separate-holomorphy theorem.** On an open
  finite complex coordinate domain, analyticity of every coordinate slice implies joint analyticity,
  with no continuity or local boundedness hypothesis.

## References

* [H. P. Boas, *Lecture Notes on Several Complex Variables*][Boas2013]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Function Metric Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

section Split

variable (κ : Type*) [Fintype κ] [DecidableEq κ]

/-- Splitting off the `none` coordinate of a finite coordinate space as the fiber variable. The
remaining coordinates form the base. -/
@[expose] def optionSplit : (Option κ → ℂ) ≃L[ℂ] (κ → ℂ) × ℂ :=
  ((LinearEquiv.piOptionEquivProd ℂ (M := fun _ : Option κ => ℂ)).trans
    (LinearEquiv.prodComm ℂ ℂ (κ → ℂ))).toContinuousLinearEquiv

variable {κ}

omit [DecidableEq κ] in
/-- The splitting map records the base coordinates and the fiber coordinate. -/
theorem optionSplit_apply (z : Option κ → ℂ) :
    optionSplit κ z = (fun i => z (some i), z none) := rfl

omit [DecidableEq κ] in
/-- The inverse splitting map reassembles a point from base and fiber coordinates. -/
theorem optionSplit_symm_apply (z' : κ → ℂ) (w : ℂ) :
    (optionSplit κ).symm (z', w) = fun o => o.elim w z' := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  rfl

/-- Updating the missing coordinate of a split point changes only the fiber. -/
theorem optionSplit_symm_update_none (z' : κ → ℂ) (w v : ℂ) :
    update ((optionSplit κ).symm (z', w)) none v = (optionSplit κ).symm (z', v) := by
  rw [optionSplit_symm_apply, optionSplit_symm_apply]
  funext o
  cases o <;> simp [update]

/-- Updating a present coordinate of a split point changes only the corresponding base
coordinate. -/
theorem optionSplit_symm_update_some (z' : κ → ℂ) (w v : ℂ) (i : κ) :
    update ((optionSplit κ).symm (z', w)) (some i) v =
      (optionSplit κ).symm (update z' i v, w) := by
  rw [optionSplit_symm_apply, optionSplit_symm_apply]
  funext o
  cases o with
  | none => simp
  | some j => by_cases hji : j = i <;> simp [hji, update]

omit [DecidableEq κ] in
/-- Closed balls in the product coordinates are products of closed balls. -/
theorem optionSplit_symm_mem_closedBall {c : Option κ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (z' : κ → ℂ) (w : ℂ) :
    (optionSplit κ).symm (z', w) ∈ closedBall c R ↔
      z' ∈ closedBall ((optionSplit κ) c).1 R ∧ w ∈ closedBall ((optionSplit κ) c).2 R := by
  have hnone : (optionSplit κ).symm (z', w) none = w := by rw [optionSplit_symm_apply]; rfl
  have hsome (i : κ) : (optionSplit κ).symm (z', w) (some i) = z' i := by
    rw [optionSplit_symm_apply]; rfl
  rw [mem_closedBall, dist_pi_le_iff hR, Option.forall, mem_closedBall, mem_closedBall,
    dist_pi_le_iff hR, hnone]
  simp only [hsome, optionSplit_apply]
  exact and_comm

end Split

/-- The induction step of Hartogs' theorem: one further coordinate. The hypothesis is Hartogs'
theorem for the coordinate type `κ`. -/
theorem analyticOnNhd_of_separately_analytic_option {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ih : ∀ {U : Set (κ → ℂ)} {g : (κ → ℂ) → F}, IsOpen U →
      (∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => g (update z i w)) (z i)) → AnalyticOnNhd ℂ g U)
    {U : Set (Option κ → ℂ)} {f : (Option κ → ℂ) → F} (hU : IsOpen U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  set L := optionSplit κ with hL
  -- analyticity of the base slices, by the induction hypothesis
  have hslice_base (w : ℂ) :
      AnalyticOnNhd ℂ (fun z' => f (L.symm (z', w))) {z' | L.symm (z', w) ∈ U} := by
    apply ih (hU.preimage (by fun_prop))
    intro z' hz' i
    have h := hf _ hz' (some i)
    dsimp only at h
    have : L.symm (z', w) (some i) = z' i := by rw [optionSplit_symm_apply]; rfl
    rw [this] at h
    convert h using 2
    rw [optionSplit_symm_update_some]
  -- analyticity of the fiber slices
  have hslice_fiber (z' : κ → ℂ) :
      AnalyticOnNhd ℂ (fun w => f (L.symm (z', w))) {w | L.symm (z', w) ∈ U} := by
    intro w hw
    have h := hf _ hw none
    have : L.symm (z', w) none = w := by rw [optionSplit_symm_apply]; rfl
    rw [this] at h
    convert h using 2
    rw [optionSplit_symm_update_none]
  -- the decidability instance of the coordinate type is adjusted by `convert`
  refine analyticOnNhd_of_separately_analytic_locally_bounded hU
    (fun z hz i => by convert hf z hz i) ?_
  intro c hc
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hc)
  set z₀ : κ → ℂ := (L c).1 with hz₀
  set w₀ : ℂ := (L c).2 with hw₀
  have hmem (z' : κ → ℂ) (w : ℂ) :
      L.symm (z', w) ∈ closedBall c R ↔ z' ∈ closedBall z₀ R ∧ w ∈ closedBall w₀ R := by
    simpa [hz₀, hw₀] using optionSplit_symm_mem_closedBall hR.le z' w
  -- Baire: a bounded cylinder over the whole closed base ball
  have hR2 : 0 < R / 2 := by positivity
  obtain ⟨W, hWo, hWne, hWsub, M₁, hM₁⟩ := exists_open_bounded_cylinder_of_separately_continuous
    (X := ℂ) (Y := κ → ℂ) (f := fun w z' => f (L.symm (z', w))) isOpen_ball
    (nonempty_ball.mpr hR2) (isCompact_closedBall z₀ R)
    (fun z' hz' => (hslice_fiber z').continuousOn.mono fun w hw => hRU ((hmem z' w).mpr
      ⟨hz', ball_subset_closedBall (ball_subset_ball (half_le_self hR.le) hw)⟩))
    (fun w hw => (hslice_base w).continuousOn.mono fun z' hz' => hRU ((hmem z' w).mpr
      ⟨hz', ball_subset_closedBall (ball_subset_ball (half_le_self hR.le) hw)⟩))
  obtain ⟨b, hb⟩ := hWne
  obtain ⟨ε₁, hε₁, hbW⟩ := nhds_basis_closedBall.mem_iff.mp (hWo.mem_nhds hb)
  have hbw₀ : dist b w₀ < R / 2 := mem_ball.mp (hWsub hb)
  -- Osgood: joint analyticity on the bounded cylinder
  set Ω := L ⁻¹' (ball z₀ R ×ˢ W) with hΩ
  have hΩo : IsOpen Ω := (isOpen_ball.prod hWo).preimage L.continuous
  have hΩU : Ω ⊆ U := by
    intro z hz
    have := (hmem (L z).1 (L z).2).mpr ⟨ball_subset_closedBall hz.1,
      ball_subset_closedBall (ball_subset_ball (half_le_self hR.le) (hWsub hz.2))⟩
    rw [Prod.mk.eta, L.symm_apply_apply] at this
    exact hRU this
  have hfΩ : AnalyticOnNhd ℂ f Ω := by
    refine analyticOnNhd_of_separately_analytic_locally_bounded hΩo
      (fun z hz i => by convert hf z (hΩU hz) i) ?_
    intro z hz
    refine ⟨M₁, Filter.mem_of_superset (hΩo.mem_nhds hz) fun y hy => ?_⟩
    have := hM₁ (L y).2 hy.2 (L y).1 (ball_subset_closedBall hy.1)
    rwa [Prod.mk.eta, L.symm_apply_apply] at this
  -- Hartogs' fiber extension lemma in product coordinates
  have hg1 : AnalyticOnNhd ℂ (f ∘ L.symm) (ball z₀ R ×ˢ ball b ε₁) := by
    intro q hq
    have hq' : L.symm q ∈ Ω := by
      change L (L.symm q) ∈ ball z₀ R ×ˢ W
      rw [L.apply_symm_apply]
      exact ⟨hq.1, hbW (ball_subset_closedBall hq.2)⟩
    exact (hfΩ _ hq').comp_of_eq (L.symm.analyticAt q) rfl
  have hg2 : ∀ z' ∈ ball z₀ R,
      AnalyticOnNhd ℂ (fun w => (f ∘ L.symm) (z', w)) (ball b (R - dist b w₀)) := by
    intro z' hz'
    apply (hslice_fiber z').mono
    intro w hw
    apply hRU
    rw [hmem]
    refine ⟨ball_subset_closedBall hz', ?_⟩
    rw [mem_closedBall]
    have := mem_ball.mp hw
    calc dist w w₀ ≤ dist w b + dist b w₀ := dist_triangle _ _ _
      _ ≤ R := by linarith
  have hw₀ : w₀ ∈ ball b (R - dist b w₀) := by
    rw [mem_ball, dist_comm]
    linarith
  obtain ⟨M, hM⟩ := exists_eventually_norm_le_of_fiber_analytic isOpen_ball hε₁ hg1 hg2
    (mem_ball_self hR) hw₀
  refine ⟨M, ?_⟩
  have := (L.continuous.tendsto c).eventually hM
  simpa only [Function.comp_def, L.symm_apply_apply] using this

omit [CompleteSpace F] in
/-- Hartogs' theorem transports along a bijection of coordinate types. -/
theorem analyticOnNhd_of_separately_analytic_of_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β)
    (hα : ∀ {U : Set (α → ℂ)} {g : (α → ℂ) → F}, IsOpen U →
      (∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => g (update z i w)) (z i)) → AnalyticOnNhd ℂ g U)
    {U : Set (β → ℂ)} {f : (β → ℂ) → F} (hU : IsOpen U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  let L : (α → ℂ) ≃L[ℂ] (β → ℂ) := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : β => ℂ) e
  have hL_apply (z : α → ℂ) (j : α) : L z (e j) = z j :=
    Equiv.piCongrLeft_apply_apply (fun _ : β => ℂ) e z j
  have hL_update (z : α → ℂ) (j : α) (w : ℂ) : L (update z j w) = update (L z) (e j) w := by
    funext i
    obtain ⟨k, rfl⟩ := e.surjective i
    by_cases hkj : k = j
    · subst k
      simp [hL_apply]
    · have hek : e k ≠ e j := fun he => hkj (e.injective he)
      simp [hkj, hek, hL_apply]
  have hg : AnalyticOnNhd ℂ (f ∘ L) (L ⁻¹' U) := by
    apply hα (hU.preimage L.continuous)
    intro z hz j
    have h := hf (L z) hz (e j)
    rw [← hL_apply z j]
    convert h using 2
    simp only [Function.comp_apply, hL_update]
  intro z hz
  have hzV : L.symm z ∈ L ⁻¹' U := by
    change L (L.symm z) ∈ U
    simpa
  have := (hg _ hzV).comp_of_eq (L.symm.analyticAt z) rfl
  simpa only [Function.comp_def, L.apply_symm_apply] using this

/-- **Hartogs' separate-holomorphy theorem.** On an open finite complex coordinate domain,
analyticity of every coordinate slice implies joint analyticity, with no continuity or local
boundedness hypothesis. Empty and singleton coordinate types are included. -/
theorem analyticOnNhd_of_separately_analytic
    {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hU : IsOpen U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  suffices H : ∀ [DecidableEq ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}, IsOpen U →
      (∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) → AnalyticOnNhd ℂ f U from
    H hU hf
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ [DecidableEq ι] {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}, IsOpen U →
      (∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i)) → AnalyticOnNhd ℂ f U)
    ?_ ?_ ?_ ι
  · intro α β _ e hα _ U f hU hf
    classical
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    exact analyticOnNhd_of_separately_analytic_of_equiv e (fun hU hf => hα hU hf) hU hf
  · intro _ U f hU hf
    exact analyticOnNhd_of_separately_analytic_locally_bounded hU hf fun c _ =>
      ⟨‖f c‖, .of_forall fun z => by rw [Subsingleton.elim z c]⟩
  · intro α _ ih _ U f hU hf
    classical
    exact analyticOnNhd_of_separately_analytic_option (fun hU hf => ih hU hf) hU
      (fun z hz i => by convert hf z hz i)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
