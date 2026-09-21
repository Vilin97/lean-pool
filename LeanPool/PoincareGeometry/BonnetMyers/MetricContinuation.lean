/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Finite-speed endpoint control

A geodesic-continuation proof has a metric component which is independent of
coordinates: a curve whose distance grows at most linearly in time has a
limit at every finite endpoint in a complete metric space.  This file records
that component without presupposing a global geodesic flow.  The remaining
geometric work is to show that the tangent state has a compatible limiting
coordinate description.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace BonnetMyersEntry

/-- A curve with a uniform finite speed bound has a left endpoint in a
complete metric space. -/
theorem exists_tendsto_nhdsLT_of_dist_le_linear
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {γ : ℝ → X} {b C : ℝ} (hC : 0 ≤ C)
    (hγ : ∀ s ∈ Iio b, ∀ t ∈ Iio b,
      dist (γ s) (γ t) ≤ C * |s - t|) :
    ∃ x : X, Tendsto γ (𝓝[<] b) (𝓝 x) := by
  let _ : NeBot (𝓝[<] b) := nhdsLT_neBot b
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  constructor
  · exact inferInstance
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hden : 0 < 2 * (C + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hε hden
  let U : Set ℝ := Iio b ∩ Metric.ball b δ
  have hU : U ∈ 𝓝[<] b := by
    exact inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds b hδ))
  refine ⟨γ '' U, ?_, ?_⟩
  · rw [Filter.mem_map]
    exact mem_of_superset hU (subset_preimage_image _ _)
  intro x hx y hy
  rcases hx with ⟨s, hs, rfl⟩
  rcases hy with ⟨t, ht, rfl⟩
  have hsball : dist s b < δ := Metric.mem_ball.mp hs.2
  have htball : dist t b < δ := Metric.mem_ball.mp ht.2
  have hst : |s - t| < 2 * δ := by
    calc
      |s - t| = dist s t := by rw [Real.dist_eq]
      _ ≤ dist s b + dist b t := dist_triangle _ _ _
      _ < δ + δ := by
        gcongr
        simpa [dist_comm] using htball
      _ = 2 * δ := by ring
  by_cases hCzero : C = 0
  · calc
      dist (γ s) (γ t) ≤ C * |s - t| := hγ s hs.1 t ht.1
      _ = 0 := by simp [hCzero]
      _ < ε := hε
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hscale : C * (2 * δ) < ε := by
      dsimp [δ]
      rw [show C * (2 * (ε / (2 * (C + 1)))) =
          ε * (C / (C + 1)) by field_simp]
      have hratio : C / (C + 1) < 1 :=
        (div_lt_one₀ hC1).2 (by linarith)
      nlinarith [hε]
    calc
      dist (γ s) (γ t) ≤ C * |s - t| := hγ s hs.1 t ht.1
      _ < C * (2 * δ) := mul_lt_mul_of_pos_left hst hCpos
      _ < ε := hscale

/-- The finite-speed endpoint lemma only needs its estimate on a sufficiently
small left tail.  This is the useful form for continuation: compactness and
coordinate bounds are normally obtained only after the curve has entered an
endpoint chart. -/
theorem exists_tendsto_nhdsLT_of_dist_le_linear_eventually
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {γ : ℝ → X} {b C : ℝ} (hC : 0 ≤ C)
    (hγ : ∃ a < b, ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b,
      dist (γ s) (γ t) ≤ C * |s - t|) :
    ∃ x : X, Tendsto γ (𝓝[<] b) (𝓝 x) := by
  rcases hγ with ⟨a, hab, hγ⟩
  letI : NeBot (𝓝[<] b) := nhdsLT_neBot b
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  constructor
  · exact inferInstance
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hden : 0 < 2 * (C + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hε hden
  let U : Set ℝ := Ioo a b ∩ Metric.ball b δ
  have hU : U ∈ 𝓝[<] b := by
    exact inter_mem (Ioo_mem_nhdsLT hab)
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds b hδ))
  refine ⟨γ '' U, ?_, ?_⟩
  · rw [Filter.mem_map]
    exact mem_of_superset hU (subset_preimage_image _ _)
  intro x hx y hy
  rcases hx with ⟨s, hs, rfl⟩
  rcases hy with ⟨t, ht, rfl⟩
  have hsball : dist s b < δ := Metric.mem_ball.mp hs.2
  have htball : dist t b < δ := Metric.mem_ball.mp ht.2
  have hst : |s - t| < 2 * δ := by
    calc
      |s - t| = dist s t := by simp [Real.dist_eq]
      _ ≤ dist s b + dist b t := dist_triangle _ _ _
      _ < δ + δ := by
        gcongr
        simpa [dist_comm] using htball
      _ = 2 * δ := by ring
  by_cases hCzero : C = 0
  · calc
      dist (γ s) (γ t) ≤ C * |s - t| := hγ s hs.1 t ht.1
      _ = 0 := by simp [hCzero]
      _ < ε := hε
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hscale : C * (2 * δ) < ε := by
      dsimp [δ]
      rw [show C * (2 * (ε / (2 * (C + 1)))) =
          ε * (C / (C + 1)) by field_simp]
      have hratio : C / (C + 1) < 1 :=
        (div_lt_one₀ hC1).2 (by linarith)
      nlinarith [hε]
    calc
      dist (γ s) (γ t) ≤ C * |s - t| := hγ s hs.1 t ht.1
      _ < C * (2 * δ) := mul_lt_mul_of_pos_left hst hCpos
      _ < ε := hscale

/-- A curve with a uniform finite speed bound has a right endpoint in a
complete metric space. -/
theorem exists_tendsto_nhdsGT_of_dist_le_linear
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {γ : ℝ → X} {a C : ℝ} (hC : 0 ≤ C)
    (hγ : ∀ s ∈ Ioi a, ∀ t ∈ Ioi a,
      dist (γ s) (γ t) ≤ C * |s - t|) :
    ∃ x : X, Tendsto γ (𝓝[>] a) (𝓝 x) := by
  let _ : NeBot (𝓝[>] a) := nhdsGT_neBot a
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  constructor
  · exact inferInstance
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hden : 0 < 2 * (C + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hε hden
  let U : Set ℝ := Ioi a ∩ Metric.ball a δ
  have hU : U ∈ 𝓝[>] a := by
    exact inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds a hδ))
  refine ⟨γ '' U, ?_, ?_⟩
  · rw [Filter.mem_map]
    exact mem_of_superset hU (subset_preimage_image _ _)
  intro x hx y hy
  rcases hx with ⟨s, hs, rfl⟩
  rcases hy with ⟨t, ht, rfl⟩
  have hsball : dist s a < δ := Metric.mem_ball.mp hs.2
  have htball : dist t a < δ := Metric.mem_ball.mp ht.2
  have hst : |s - t| < 2 * δ := by
    calc
      |s - t| = dist s t := by rw [Real.dist_eq]
      _ ≤ dist s a + dist a t := dist_triangle _ _ _
      _ < δ + δ := by
        gcongr
        simpa [dist_comm] using htball
      _ = 2 * δ := by ring
  by_cases hCzero : C = 0
  · calc
      dist (γ s) (γ t) ≤ C * |s - t| := hγ s hs.1 t ht.1
      _ = 0 := by simp [hCzero]
      _ < ε := hε
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hscale : C * (2 * δ) < ε := by
      dsimp [δ]
      rw [show C * (2 * (ε / (2 * (C + 1)))) =
          ε * (C / (C + 1)) by field_simp]
      have hratio : C / (C + 1) < 1 :=
        (div_lt_one₀ hC1).2 (by linarith)
      nlinarith [hε]
    calc
      dist (γ s) (γ t) ≤ C * |s - t| := hγ s hs.1 t ht.1
      _ < C * (2 * δ) := mul_lt_mul_of_pos_left hst hCpos
      _ < ε := hscale

/-- A bounded derivative gives the finite-speed hypothesis used by the left
endpoint lemma.  This is the coordinate estimate needed for the velocity
component of a geodesic state once its acceleration is bounded on a compact
coordinate neighbourhood. -/
theorem exists_tendsto_nhdsLT_of_norm_deriv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {b C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Iio b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Iio b, ‖f' t‖ ≤ C) :
    ∃ x : E, Tendsto f (𝓝[<] b) (𝓝 x) := by
  apply exists_tendsto_nhdsLT_of_dist_le_linear hC
  intro s hs t ht
  rcases le_total s t with hst | hts
  · have hdiff : ∀ x ∈ Icc s t, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hderiv x (lt_of_le_of_lt hx.2 ht)).differentiableAt
    have hderiv_bound : ∀ x ∈ Icc s t, ‖deriv f x‖ ≤ C := by
      intro x hx
      rw [(hderiv x (lt_of_le_of_lt hx.2 ht)).deriv]
      exact hbound x (lt_of_le_of_lt hx.2 ht)
    have hsegment := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv_bound
      (convex_Icc s t) (left_mem_Icc.2 hst) (right_mem_Icc.2 hst)
    calc
      dist (f s) (f t) = ‖f t - f s‖ := by
        rw [dist_eq_norm_sub, norm_sub_rev]
      _ ≤ C * ‖t - s‖ := hsegment
      _ = C * |s - t| := by rw [Real.norm_eq_abs, abs_sub_comm]
  · have hdiff : ∀ x ∈ Icc t s, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hderiv x (lt_of_le_of_lt hx.2 hs)).differentiableAt
    have hderiv_bound : ∀ x ∈ Icc t s, ‖deriv f x‖ ≤ C := by
      intro x hx
      rw [(hderiv x (lt_of_le_of_lt hx.2 hs)).deriv]
      exact hbound x (lt_of_le_of_lt hx.2 hs)
    have hsegment := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv_bound
      (convex_Icc t s) (left_mem_Icc.2 hts) (right_mem_Icc.2 hts)
    calc
      dist (f s) (f t) = ‖f s - f t‖ := dist_eq_norm_sub _ _
      _ ≤ C * ‖s - t‖ := hsegment
      _ = C * |s - t| := by rw [Real.norm_eq_abs]

/-- A derivative bound which holds only eventually on the left still supplies
the coordinate endpoint limit. -/
theorem exists_tendsto_nhdsLT_of_norm_deriv_eventually_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {b C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Iio b, HasDerivAt f (f' t) t)
    (hbound : ∀ᶠ t in 𝓝[<] b, ‖f' t‖ ≤ C) :
    ∃ x : E, Tendsto f (𝓝[<] b) (𝓝 x) := by
  obtain ⟨a, hab, htail⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hbound
  apply exists_tendsto_nhdsLT_of_dist_le_linear_eventually hC
  refine ⟨a, hab, ?_⟩
  intro s hs t ht
  rcases le_total s t with hst | hts
  · have hdiff : ∀ x ∈ Icc s t, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hderiv x (lt_of_le_of_lt hx.2 ht.2)).differentiableAt
    have hderiv_bound : ∀ x ∈ Icc s t, ‖deriv f x‖ ≤ C := by
      intro x hx
      rw [(hderiv x (lt_of_le_of_lt hx.2 ht.2)).deriv]
      exact htail ⟨lt_of_lt_of_le hs.1 hx.1, lt_of_le_of_lt hx.2 ht.2⟩
    have hsegment := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv_bound
      (convex_Icc s t) (left_mem_Icc.2 hst) (right_mem_Icc.2 hst)
    calc
      dist (f s) (f t) = ‖f t - f s‖ := by
        rw [dist_eq_norm_sub, norm_sub_rev]
      _ ≤ C * ‖t - s‖ := hsegment
      _ = C * |s - t| := by rw [Real.norm_eq_abs, abs_sub_comm]
  · have hdiff : ∀ x ∈ Icc t s, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hderiv x (lt_of_le_of_lt hx.2 hs.2)).differentiableAt
    have hderiv_bound : ∀ x ∈ Icc t s, ‖deriv f x‖ ≤ C := by
      intro x hx
      rw [(hderiv x (lt_of_le_of_lt hx.2 hs.2)).deriv]
      exact htail ⟨lt_of_lt_of_le ht.1 hx.1, lt_of_le_of_lt hx.2 hs.2⟩
    have hsegment := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv_bound
      (convex_Icc t s) (left_mem_Icc.2 hts) (right_mem_Icc.2 hts)
    calc
      dist (f s) (f t) = ‖f s - f t‖ := dist_eq_norm_sub _ _
      _ ≤ C * ‖s - t‖ := hsegment
      _ = C * |s - t| := by rw [Real.norm_eq_abs]

/-- The derivative estimate used to obtain a left endpoint is itself local:
both differentiability and the norm bound may be known only on the final
left tail. -/
theorem exists_tendsto_nhdsLT_of_norm_deriv_eventually_le_of_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {b C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ᶠ t in 𝓝[<] b, HasDerivAt f (f' t) t)
    (hbound : ∀ᶠ t in 𝓝[<] b, ‖f' t‖ ≤ C) :
    ∃ x : E, Tendsto f (𝓝[<] b) (𝓝 x) := by
  obtain ⟨aD, haD, hderivTail⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp hderiv
  obtain ⟨aB, haB, hboundTail⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp hbound
  let a : ℝ := max aD aB
  have ha : a < b := by
    dsimp [a]
    exact max_lt haD haB
  have haD : aD ≤ a := by
    dsimp [a]
    exact le_max_left _ _
  have haB : aB ≤ a := by
    dsimp [a]
    exact le_max_right _ _
  apply exists_tendsto_nhdsLT_of_dist_le_linear_eventually hC
  refine ⟨a, ha, ?_⟩
  intro s hs t ht
  rcases le_total s t with hst | hts
  · have hdiff : ∀ x ∈ Icc s t, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hderivTail
        ⟨lt_of_le_of_lt haD (lt_of_lt_of_le hs.1 hx.1),
          lt_of_le_of_lt hx.2 ht.2⟩).differentiableAt
    have hderiv_bound : ∀ x ∈ Icc s t, ‖deriv f x‖ ≤ C := by
      intro x hx
      rw [(hderivTail
        ⟨lt_of_le_of_lt haD (lt_of_lt_of_le hs.1 hx.1),
          lt_of_le_of_lt hx.2 ht.2⟩).deriv]
      exact hboundTail
        ⟨lt_of_le_of_lt haB (lt_of_lt_of_le hs.1 hx.1),
          lt_of_le_of_lt hx.2 ht.2⟩
    have hsegment := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv_bound
      (convex_Icc s t) (left_mem_Icc.2 hst) (right_mem_Icc.2 hst)
    calc
      dist (f s) (f t) = ‖f t - f s‖ := by
        rw [dist_eq_norm_sub, norm_sub_rev]
      _ ≤ C * ‖t - s‖ := hsegment
      _ = C * |s - t| := by rw [Real.norm_eq_abs, abs_sub_comm]
  · have hdiff : ∀ x ∈ Icc t s, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hderivTail
        ⟨lt_of_le_of_lt haD (lt_of_lt_of_le ht.1 hx.1),
          lt_of_le_of_lt hx.2 hs.2⟩).differentiableAt
    have hderiv_bound : ∀ x ∈ Icc t s, ‖deriv f x‖ ≤ C := by
      intro x hx
      rw [(hderivTail
        ⟨lt_of_le_of_lt haD (lt_of_lt_of_le ht.1 hx.1),
          lt_of_le_of_lt hx.2 hs.2⟩).deriv]
      exact hboundTail
        ⟨lt_of_le_of_lt haB (lt_of_lt_of_le ht.1 hx.1),
          lt_of_le_of_lt hx.2 hs.2⟩
    have hsegment := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv_bound
      (convex_Icc t s) (left_mem_Icc.2 hts) (right_mem_Icc.2 hts)
    calc
      dist (f s) (f t) = ‖f s - f t‖ := dist_eq_norm_sub _ _
      _ ≤ C * ‖s - t‖ := hsegment
      _ = C * |s - t| := by rw [Real.norm_eq_abs]

end BonnetMyersEntry
