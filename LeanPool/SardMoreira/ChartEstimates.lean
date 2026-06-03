/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.MeasureTheory.Measure.Hausdorff
import LeanPool.SardMoreira.Chart

/-!
# LeanPool.SardMoreira.ChartEstimates
-/

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set Metric Function MeasureTheory Measure

local notation "dim" => Module.finrank ℝ

namespace Moreira2001


namespace Chart

universe u v w

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k : ℕ} {α : I} {s : Set (E × F)} {a : E × F}

instance (ψ : Chart k α s) : MeasurableSpace ψ.Dom := borel _

instance (ψ : Chart k α s) : BorelSpace ψ.Dom := ⟨rfl⟩

theorem eventually_contDiffAt_comp {f : E × F → G} {ψ : Chart 1 α s} {x : E × ψ.Dom}
    (hx : x ∈ ψ.set) (hfk : ∀ᶠ (y : E × F) in 𝓝[s] ψ x, ContDiffMoreiraHolderAt k α f y)
    (hk : k ≠ 0) :
    ∀ᶠ y in 𝓝 x.2, ContDiffAt ℝ 1 (fun y ↦ f (ψ (x.1, y))) y := by
  have htendsto : Tendsto (fun y ↦ ψ (x.1, y)) (𝓝 x.2) (𝓝 (ψ x)) :=
    ψ.continuousAt hx |>.comp (continuousAt_const.prodMk continuousAt_id) |>.tendsto
  filter_upwards [htendsto.eventually <|
    hfk.self_of_nhdsWithin (ψ.mapsTo hx) |>.contDiffAt |>.eventually (by simp),
    (continuousAt_const.prodMk continuousAt_id).eventually <|
      ψ.contDiffMoreiraHolderAt hx |>.contDiffAt.eventually (by simp)] with y hfy hψy
  exact .comp _ (hfy.of_le (by simpa [Nat.one_le_iff_ne_zero])) <|
    .comp _ (hψy.of_le (by simp)) (by fun_prop)

theorem eventually_differentiableAt_comp {f : E × F → G} {ψ : Chart 1 α s} {x : E × ψ.Dom}
    (hx : x ∈ ψ.set) (hfk : ∀ᶠ (y : E × F) in 𝓝[s] ψ x, ContDiffMoreiraHolderAt k α f y)
    (hk : k ≠ 0) :
    ∀ᶠ y in 𝓝 x.2, DifferentiableAt ℝ (fun y ↦ f (ψ (x.1, y))) y := by
  exact eventually_contDiffAt_comp hx hfk hk |>.mono fun y hy ↦
    hy.differentiableAt (by simp)

theorem fderiv₂_comp_eventuallyEq {f : E × F → G} (ψ : Chart 1 α s) {x : E × ψ.Dom} (hx : x ∈ ψ.set)
    (hfk : ContDiffAt ℝ k f (ψ x)) (hk : k ≠ 0) :
    (fderiv ℝ fun y ↦ f (ψ (x.1, y))) =ᶠ[𝓝 x.2] fun y ↦
      (fderiv ℝ f (ψ (x.1, y)) ∘L .inr ℝ E F) ∘L (fderiv ℝ (fun y ↦ (ψ (x.1, y)).2) y) := by
  have hdf : ∀ᶠ y in 𝓝 x.2, DifferentiableAt ℝ f (ψ (x.1, y)) := by
    have : ContinuousAt (fun y ↦ ψ (x.1, y)) x.2 := by
      have := ψ.continuousAt hx
      fun_prop
    exact this.eventually <| hfk.eventually (by simp) |>.mono fun y hy ↦
        hy.differentiableAt (by simpa [Nat.one_le_iff_ne_zero])
  have hdψ : ∀ᶠ y in 𝓝 x.2, DifferentiableAt ℝ ψ (x.1, y) := by
    have : ContinuousAt (x.1, ·) x.2 := by fun_prop
    exact this.eventually <| ψ.eventually_differentiableAt hx (by simp)
  filter_upwards [hdf, hdψ] with y hfy hψy
  rw [← fderiv_comp_prodMk', ← fderiv_comp (f := fun y ↦ (ψ (x.1, y)).2)]
  · simp [Function.comp_def]
  · simp only [Chart.fst_apply]
    rw [← Chart.prodMk_fst_snd_apply] at hfy
    fun_prop
  · fun_prop
  · simpa using hfy

theorem step_aux {f : E × F → G} (ψ : Chart 1 α s) {x : E × ψ.Dom} (hx : x ∈ ψ.set)
    (hfk : ContDiffAt ℝ k f (ψ x)) (hk : k ≠ 0) :
    (fderiv ℝ fun y ↦ f (ψ (x.1, y))) =O[𝓝 x.2]
      fun y ↦ (fderiv ℝ f (ψ (x.1, y)) ∘L .inr ℝ E F) := by
  calc
    _ =ᶠ[𝓝 x.2] (fun y ↦ (fderiv ℝ f (ψ (x.1, y)) ∘L .inr ℝ E F) ∘L
                  fderiv ℝ (fun y ↦ (ψ (x.1, y)).2) y) := by
      apply ψ.fderiv₂_comp_eventuallyEq hx hfk hk
    _ =O[𝓝 x.2] fun y ↦ ‖fderiv ℝ f (ψ (x.1, y)) ∘L .inr ℝ E F‖ *
                  ‖fderiv ℝ (fun z ↦ (ψ (x.1, z)).2) y‖ := by
      refine .of_norm_le fun _ ↦ ContinuousLinearMap.opNorm_comp_le _ _
    _ =O[𝓝 x.2] fun y ↦ (fderiv ℝ f (ψ (x.1, y)) ∘L .inr ℝ E F) := by
      have : ContinuousAt (fderiv ℝ (fun z ↦ (ψ (x.1, z)).2)) x.2 := by
        refine ContDiffAt.continuousAt_fderiv ?_ (n := 1) (by simp)
        have := ψ.contDiffMoreiraHolderAt hx |>.contDiffAt |>.of_le (m := 1) (by simp)
        fun_prop
      refine (isBigO_refl _ _).mul (this.isBigO_one ℝ).norm_left |>.trans ?_
      simp [isBigO_refl]


end Chart

namespace Atlas

section Aux

universe u v w

variable {E : Type u} {F : Type v} {G : Type (max v w)}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k : ℕ} {α : I} {s : Set (E × F)} {a : E × F}
  {f : E × F → G} {ψ : Chart 1 α s} {x : E × ψ.Dom}

-- TODO: this proof was written before I extracted some lemmas.
-- Reuse them here.
theorem isBigO_main_aux
    (hψ : ψ ∈ (main k α s).charts) (hx : x ∈ ψ.set)
    (hfk : ∀ᶠ y in 𝓝[s] (ψ x), ContDiffMoreiraHolderAt k α f y)
    (hf₀ : f =ᶠ[𝓝[s] (ψ x)] 0) :
    (fun y ↦ f (ψ (x.1, y))) =O[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ)) := by
  induction k generalizing F G with
  | zero =>
    calc
      _ =O[𝓝 x.2] (fun y ↦ ‖ψ (x.1, y) - ψ x‖ ^ (α : ℝ)) := by
        replace hfk := hfk.self_of_nhdsWithin (ψ.mapsTo hx)
        rw [ContDiffMoreiraHolderAt.zero_left_iff] at hfk
        have := hfk.2.comp_tendsto
          ((ψ.continuousAt hx).comp (continuousAt_const.prodMk continuousAt_id))
        simpa [Function.comp_def, hf₀.self_of_nhdsWithin (ψ.mapsTo hx)] using this
      _ =O[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (α : ℝ)) := by
        have := ψ.differentiableAt one_ne_zero hx |>.isBigO_sub |>.norm_norm
          |>.rpow α.2.1 (by simp [EventuallyLE])
          |>.comp_tendsto (k := (x.1, ·)) (continuousAt_const.prodMk continuousAt_id)
        simpa [Function.comp_def, Prod.sub_def] using this
      _ = _ := by simp
  | succ k ihk =>
    simp only [main, mem_iUnion, mem_image] at hψ
    rcases hψ with ⟨ψ, hψ, φ, hφ, rfl⟩
    suffices (fun y ↦ f (ψ (φ (x.1, y)))) =O[𝓝 x.2] fun y ↦ ‖y - x.2‖ ^ (k + α + 1 : ℝ) by
      simpa [add_right_comm _ (1 : ℝ)]
    have hmems : ψ (φ x) ∈ s := ψ.mapsTo (φ.mapsTo hx).1
    have hψ_tendsto : Tendsto ψ (𝓝[ψ.set] (φ x)) (𝓝[s] (ψ (φ x))) :=
      .inf (ψ.continuousAt (φ.mapsTo hx).1) ψ.mapsTo.tendsto
    have hkey :
        (fun y ↦ fderiv ℝ (f ∘ ψ) (φ (x.1, y)) ∘L .inr ℝ E ψ.Dom) =O[𝓝 x.2]
          (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ)) := by
      refine ihk (f := fun z ↦ fderiv ℝ (f ∘ ψ) z ∘L .inr ℝ _ _) hφ hx ?_ ?_
      · filter_upwards [eventually_mem_nhdsWithin,
          (hψ_tendsto.eventually hfk).filter_mono (nhdsWithin_mono _ (sep_subset _ _))]
          with y hy hfy
        refine (hfy.comp ?_ k.succ_ne_zero).fderiv le_rfl |>.continuousLinearMap_comp
          (.precomp _ (.inr ℝ E ψ.Dom))
        exact ψ.contDiffMoreiraHolderAt hy.1
      · rw [EventuallyEq, eventually_nhdsWithin_iff]
        replace hfk := hψ_tendsto.eventually hfk
        rw [eventually_nhdsWithin_iff, ← eventually_eventually_nhds] at hfk
        replace hf₀ := hψ_tendsto.eventually hf₀
        rw [eventually_nhdsWithin_iff, ← eventually_eventually_nhds] at hf₀
        filter_upwards [hfk, hf₀] with y hy_contDiff hy₀ hy_mem
        apply hy_mem.2.fderiv_comp_inr_eq_zero
        · rw [eventually_nhdsWithin_iff]
          filter_upwards [hy_contDiff] with z hz hz_mem
          exact .comp (hz hz_mem) (ψ.contDiffMoreiraHolderAt hz_mem) k.succ_ne_zero
        · rwa [EventuallyEq, eventually_nhdsWithin_iff]
    have hφdiff : ∀ᶠ y in 𝓝 x.2, DifferentiableAt ℝ φ (x.1, y) := by
      refine Continuous.prodMk_right _ |>.tendsto _ |>.eventually ?_
      exact φ.contDiffMoreiraHolderAt hx |>.contDiffAt |>.eventually (by simp)
        |>.mono fun y hy ↦ hy.differentiableAt (by simp)
    have hψdiff : ∀ᶠ y in 𝓝 x.2, DifferentiableAt ℝ ψ (φ (x.1, y)) := by
      have := (φ.continuousAt hx).comp (continuousAt_const.prodMk continuousAt_id)
      refine this.eventually ?_
      exact ψ.contDiffMoreiraHolderAt (φ.mapsTo hx).1 |>.contDiffAt |>.eventually (by simp)
        |>.mono fun y hy ↦ hy.differentiableAt (by simp)
    have hfdiff : ∀ᶠ y in 𝓝 x.2, DifferentiableAt ℝ f (ψ (φ (x.1, y))) := by
      have : ContinuousAt (fun y ↦ ψ (φ (x.1, y))) x.2 := by
        have := hψdiff.self_of_nhds.continuousAt
        have := φ.continuousAt hx
        fun_prop
      refine this.eventually ?_
      exact hfk.self_of_nhdsWithin hmems |>.contDiffAt |>.eventually (by simp)
        |>.mono fun y hy ↦ hy.differentiableAt (by simp)
    apply isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero
    · exact add_nonneg k.cast_nonneg α.2.1
    · filter_upwards [hφdiff, hψdiff, hfdiff] with y hφy hψy hfy
      exact .comp _ hfy <| .comp _ hψy <| .comp _ hφy (by fun_prop)
    · refine (φ.step_aux (f := (f <| ψ ·)) (k := k + 1) hx ?_ (by simp)).trans hkey
      refine .comp _ ?_ ?_
      · exact hfk.self_of_nhdsWithin (Chart.mapsTo _ hx) |>.contDiffAt
      · exact ψ.contDiffAt (φ.mapsTo hx).1
    · exact hf₀.self_of_nhdsWithin hmems

end Aux

universe u v w

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k : ℕ} {α : I} {s : Set (E × F)} {a : E × F}
  {f : E × F → G} {ψ : Chart 1 α s} {x : E × ψ.Dom}

theorem _root_.Moreira2001.Atlas.isBigO_main_inr
    (hψ : ψ ∈ (main k α s).charts) (hx : x ∈ ψ.set)
    (hfk : ∀ᶠ y in 𝓝[s] (ψ x), ContDiffMoreiraHolderAt k α f y)
    (hf₀ : f =ᶠ[𝓝[s] (ψ x)] 0) :
    (fun y ↦ f (ψ (x.1, y))) =O[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ)) := by
  set e : G ≃L[ℝ] ULift.{v} G := .symm ⟨ULift.moduleEquiv, by fun_prop, by fun_prop⟩
  set g : E × F → ULift.{v} G := e ∘ f
  have hgk : ∀ᶠ y in 𝓝[s] (ψ x), ContDiffMoreiraHolderAt k α g y :=
    hfk.mono fun _ ↦ e.contDiffMoreiraHolderAt_left_comp.mpr
  have hg₀ : g =ᶠ[𝓝[s] (ψ x)] 0 := hf₀.fun_comp e
  refine .trans ?_ (isBigO_main_aux hψ hx hgk hg₀)
  apply e.isBigO_comp_rev

theorem _root_.Moreira2001.Atlas.isBigO_main_sub_of_fderiv_zero_right
    (hψ : ψ ∈ (main k α s).charts) (hx : x ∈ ψ.set)
    (hfk : ∀ᶠ y in 𝓝[s] (ψ x), ContDiffMoreiraHolderAt (k + 1) α f y)
    (hf₀ : (fderiv ℝ f · ∘L .inr ℝ E F) =ᶠ[𝓝[s] (ψ x)] 0) :
    (fun y ↦ f (ψ (x.1, y)) - f (ψ x)) =O[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + 1 + α : ℝ)) := by
  rw [add_right_comm]
  apply sub_isBigO_norm_rpow_add_one_of_fderiv (f := fun y ↦ f (ψ (x.1, y)))
  · exact add_nonneg k.cast_nonneg α.2.1
  · exact ψ.eventually_differentiableAt_comp hx hfk (by simp)
  · have hcontDiff := (hfk.self_of_nhdsWithin (ψ.mapsTo hx)).contDiffAt
    refine .trans ?_ (isBigO_main_inr hψ hx (hfk.mono fun y hy ↦ ?_) hf₀)
    · apply ψ.step_aux hx hcontDiff (by simp)
    · exact (hy.fderiv le_rfl).continuousLinearMap_comp (.precomp _ (.inr ℝ E F))

theorem _root_.Moreira2001.Atlas.isLittleO_main_sub_of_fderiv_zero_right
    (hψ : ψ ∈ (main k α s).charts) (hx : x ∈ ψ.set)
    (hfk : ∀ᶠ y in 𝓝[s] (ψ x), ContDiffMoreiraHolderAt (k + 1) α f y)
    (hf₀ : (fderiv ℝ f · ∘L .inr ℝ E F) =ᶠ[𝓝[s] (ψ x)] 0)
    (hdensity : Tendsto (fun r ↦
      μH[dim ψ.Dom] ({y | (x.1, y) ∈ closure ψ.set} ∩ closedBall x.2 r) /
        μH[↑(dim ψ.Dom)] (closedBall x.2 r))
      (𝓝[>] 0) (𝓝 1)) :
    (fun y ↦ f (ψ (x.1, y)) - f (ψ x)) =o[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + 1 + α : ℝ)) := by
  rw [add_right_comm]
  have htendsto : Tendsto (fun y ↦ ψ (x.1, y)) (𝓝 x.2) (𝓝 (ψ x)) :=
    ψ.continuousAt hx |>.comp (continuousAt_const.prodMk continuousAt_id) |>.tendsto
  have hcontDiff := (hfk.self_of_nhdsWithin (ψ.mapsTo hx)).contDiffAt
  apply sub_isLittleO_norm_rpow_add_one_of_fderiv_of_density_point
    (f := fun y ↦ f (ψ (x.1, y))) (μ := μH[dim ψ.Dom]) (s := {y | (x.1, y) ∈ closure ψ.set})
  · exact add_nonneg k.cast_nonneg α.2.1
  · exact ψ.eventually_differentiableAt_comp hx hfk (by simp)
  · refine .trans ?_ (isBigO_main_inr hψ hx (hfk.mono fun y hy ↦ ?_) hf₀)
    · apply ψ.step_aux hx hcontDiff (by simp)
    · exact (hy.fderiv le_rfl).continuousLinearMap_comp (.precomp _ (.inr ℝ E F))
  · replace hf₀ : ∀ᶠ y in 𝓝 x.2, (x.1, y) ∈ closure ψ.set →
        fderiv ℝ f (ψ (x.1, y)) ∘L .inr ℝ E F = 0 := by
      have H₁ : ∀ᶠ y in 𝓝 x.2, ContinuousAt (fderiv ℝ f · ∘L .inr ℝ E F) (ψ (x.1, y)) := by
        refine htendsto.eventually ?_
        refine hcontDiff.eventually (by simp) |>.mono fun y hy ↦ ?_
        simp only [← ContinuousLinearMap.precomp_apply]
        exact .comp (by fun_prop) (hy.continuousAt_fderiv (by simp))
      have H₂ := htendsto.eventually
        (eventually_eventually_nhds.mpr <| eventually_nhdsWithin_iff.mp hf₀)
      have H₃ : ∀ᶠ y in 𝓝 x.2, ContinuousAt ψ (x.1, y) := by
        refine (show ContinuousAt (x.1, ·) x.2 by fun_prop).eventually ?_
        exact ψ.contDiffAt hx |>.eventually (by simp) |>.mono fun y hy ↦ hy.continuousAt
      filter_upwards [H₁, H₂, H₃]
      intro y hycont hy hψcont hyclos
      rw [mem_closure_iff_nhdsWithin_neBot] at hyclos
      refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[ψ.set] (x.1, y))
        (f := (fun y ↦ fderiv ℝ f (ψ y) ∘L .inr ℝ E F)) ?_ tendsto_const_nhds ?_
      · exact hycont.comp_continuousWithinAt hψcont.continuousWithinAt
      · rw [EventuallyEq, eventually_nhdsWithin_iff]
        filter_upwards [hψcont.eventually hy] with z hz hψz using hz (ψ.mapsTo hψz)
    rw [EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [ψ.fderiv₂_comp_eventuallyEq hx hcontDiff (by simp), hf₀] with y hy_eq hy hy_mem
    rw [hy_eq, hy hy_mem]
    simp
  · exact hdensity

end Moreira2001.Atlas
