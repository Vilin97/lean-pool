/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section

/-! Closed differentiability for strongly continuous linear isometric actions. -/

noncomputable section

namespace EulerIsometricAction

open Filter
open scoped Topology

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_all (τ : P → E →ₗᵢ[ℝ] E)
    (hadd : ∀ a b u, τ a (τ b u) = τ (a + b) u)
    (u : E) (D : P →L[ℝ] E) (h : HasFDerivAt (fun a => τ a u) D 0) (a : P) :
    HasFDerivAt (fun b => τ b u) ((τ a).toContinuousLinearMap.comp D) a := by
  have hs := (τ a).toContinuousLinearMap.hasFDerivAt.comp (0 : P) h
  have hs' : HasFDerivAt (fun b : P => τ a (τ b u))
      ((τ a).toContinuousLinearMap.comp D) (a-a) := by
    simpa only [sub_self, Function.comp_def, LinearIsometry.coe_toContinuousLinearMap] using hs
  have hsub : HasFDerivAt (fun b : P => b-a) (ContinuousLinearMap.id ℝ P) a := by
    simpa only [id_eq] using (hasFDerivAt_id a).sub_const a
  have hd := HasFDerivAt.comp (f := fun b : P => b-a) a hs' hsub
  have he : (fun b : P => τ a (τ (b-a) u)) = fun b : P => τ b u := by
    funext b
    rw [hadd]
    congr 1
    abel_nf
  simpa only [Function.comp_def, id_eq, sub_self, he, ContinuousLinearMap.comp_id] using hd

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem orbits_tendstoUniformly (τ : P → E →ₗᵢ[ℝ] E) {ι : Type*} {l : Filter ι}
    (u : ι → E) (v : E) (hu : Tendsto u l (𝓝 v)) :
    TendstoUniformly (fun n a => τ a (u n)) (fun a => τ a v) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hu.eventually (Metric.ball_mem_nhds v hε)] with n hn a
  rw [(τ a).dist_map]
  simpa only [Metric.mem_ball, dist_comm] using hn

theorem derivatives_tendstoUniformly (τ : P → E →ₗᵢ[ℝ] E) {ι : Type*} {l : Filter ι}
    (D : ι → P →L[ℝ] E) (D₀ : P →L[ℝ] E) (hD : Tendsto D l (𝓝 D₀)) :
    TendstoUniformly (fun n a => (τ a).toContinuousLinearMap.comp (D n))
      (fun a => (τ a).toContinuousLinearMap.comp D₀) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hD.eventually (Metric.ball_mem_nhds D₀ hε)] with n hn a
  have hb : dist ((τ a).toContinuousLinearMap.comp D₀)
      ((τ a).toContinuousLinearMap.comp (D n)) ≤ dist D₀ (D n) := by
    rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] using (D₀-D n).le_opNorm v
  exact hb.trans_lt (by simpa only [Metric.mem_ball, dist_comm] using hn)

/-- Derivatives of an isometric orbit form a closed operator. -/
theorem hasFDerivAt_limit (τ : P → E →ₗᵢ[ℝ] E)
    (hadd : ∀ a b u, τ a (τ b u) = τ (a + b) u) (hzero : ∀ u, τ 0 u = u)
    (u : ℕ → E) (D : ℕ → P →L[ℝ] E) (u₀ : E) (D₀ : P →L[ℝ] E)
    (h : ∀ n, HasFDerivAt (fun a => τ a (u n)) (D n) 0)
    (hu : Tendsto u atTop (𝓝 u₀)) (hD : Tendsto D atTop (𝓝 D₀)) :
    HasFDerivAt (fun a => τ a u₀) D₀ 0 := by
  have hh := hasFDerivAt_of_tendstoUniformly (derivatives_tendstoUniformly τ D D₀ hD)
    (fun n a => hasFDerivAt_all τ hadd (u n) (D n) (h n) a)
    (fun a => (τ a).continuous.continuousAt.tendsto.comp hu) (0 : P)
  have hz : (τ 0).toContinuousLinearMap.comp D₀ = D₀ := by
    ext a
    exact hzero (D₀ a)
  rwa [hz] at hh

end EulerIsometricAction
