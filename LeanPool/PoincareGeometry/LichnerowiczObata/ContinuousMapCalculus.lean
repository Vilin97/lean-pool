/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Differentiating superposition on compact-domain path spaces -/

@[expose] public noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace LichnerowiczObata
universe u v
variable {S : Type v} {E F : Type u} [TopologicalSpace S] [CompactSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous family of linear maps acts boundedly on continuous paths. -/
def continuousMapApplyCLM (D : C(S, E →L[ℝ] F)) : C(S, E) →L[ℝ] C(S, F) :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun t => D t (u t), D.continuous.clm_apply u.continuous⟩
      map_add' := by intro u v; ext t; simp
      map_smul' := by intro c u; ext t; simp }
    ‖D‖ (by
      intro u
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg D) (norm_nonneg u))).mpr
      intro t
      exact ((D t).le_opNorm (u t)).trans
        (mul_le_mul (D.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem continuousMapApplyCLM_apply (D : C(S, E →L[ℝ] F)) (u : C(S, E)) (t : S) :
    continuousMapApplyCLM D u t = D t (u t) := rfl

theorem norm_continuousMapApplyCLM_le (D : C(S, E →L[ℝ] F)) :
    ‖continuousMapApplyCLM D‖ ≤ ‖D‖ := by
  apply (continuousMapApplyCLM D).opNorm_le_bound (norm_nonneg D)
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg D) (norm_nonneg u))).mpr
  intro t
  exact ((D t).le_opNorm (u t)).trans
    (mul_le_mul (D.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

/-- Forming the pathwise derivative operator is itself a bounded linear operation. -/
def continuousMapApplyOperatorCLM : C(S, E →L[ℝ] F) →L[ℝ] (C(S, E) →L[ℝ] C(S, F)) := by
  let L : C(S, E →L[ℝ] F) →ₗ[ℝ] (C(S, E) →L[ℝ] C(S, F)) :=
    { toFun := continuousMapApplyCLM
      map_add' := by intro D D'; ext u t; simp
      map_smul' := by intro c D; ext u t; simp }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(S, E →L[ℝ] F)) (F := C(S, E) →L[ℝ] C(S, F)) L 1 ?_
  intro D
  change ‖continuousMapApplyCLM D‖ ≤ 1 * ‖D‖
  simpa only [one_mul] using norm_continuousMapApplyCLM_le D

/-- Superposition by a continuous map, as a map of continuous path spaces. -/
def continuousMapSuperposition (f : C(E, F)) (u : C(S, E)) : C(S, F) := f.comp u

/-- A continuously differentiable map acts strictly differentiably on the
Banach path space. Compactness supplies a uniform derivative remainder; no
uniform differentiability hypothesis is assumed separately. -/
theorem hasStrictFDerivAt_continuousMapSuperposition
    (f : C(E, F)) (D : C(E, E →L[ℝ] F))
    (hD : ∀ x, HasFDerivAt f (D x) x) (u : C(S, E)) :
    HasStrictFDerivAt (continuousMapSuperposition f)
      (continuousMapApplyCLM (D.comp u)) u := by
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hc : IsCompact (range u) := isCompact_range u.continuous
  have hu := hc.uniformContinuousAt_of_continuousAt D
    (fun _ _ => D.continuous.continuousAt) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hδD⟩ := Metric.mem_uniformity_dist.mp hu
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨v, w⟩ hvw
  rw [← ball_prod_same, prodMk_mem_set_prod_eq] at hvw
  simp only [Metric.mem_ball] at hvw
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro t
  have hv : v t ∈ Metric.ball (u t) δ := by
    change dist (v t) (u t) < δ
    apply lt_of_le_of_lt _ hvw.1
    simpa only [dist_eq_norm, ContinuousMap.sub_apply] using (v - u).norm_coe_le_norm t
  have hw : w t ∈ Metric.ball (u t) δ := by
    change dist (w t) (u t) < δ
    apply lt_of_le_of_lt _ hvw.2
    simpa only [dist_eq_norm, ContinuousMap.sub_apply] using (w - u).norm_coe_le_norm t
  have hbound : ∀ z ∈ Metric.ball (u t) δ, ‖D z - D (u t)‖ ≤ ε := by
    intro z hz
    have hd : dist (D (u t)) (D z) < ε :=
      hδD (show dist (u t) z < δ by simpa only [Metric.mem_ball, dist_comm] using hz) (mem_range_self t)
    simpa only [dist_eq_norm, norm_sub_rev] using hd.le
  have hrem := (convex_ball (u t) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hD z).hasFDerivWithinAt) hbound hw hv
  exact hrem.trans (mul_le_mul_of_nonneg_left ((v - w).norm_coe_le_norm t) hε.le)

/-- Superposition preserves every finite order of smoothness. -/
theorem contDiff_continuousMapSuperposition (n : ℕ) (f : C(E, F))
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (continuousMapSuperposition (S := S) f) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr f.continuous_postcomp
  | succ n ih =>
    obtain ⟨D, hDc, hD⟩ := contDiff_succ_iff_hasFDerivAt.mp hf
    let Dc : C(E, E →L[ℝ] F) := ⟨D, hDc.continuous⟩
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun u => continuousMapApplyCLM (Dc.comp u), ?_, ?_⟩
    · have hlin : ContDiff ℝ n (continuousMapApplyOperatorCLM (S := S) (E := E) (F := F)) :=
        ContinuousLinearMap.contDiff _
      change ContDiff ℝ n ((continuousMapApplyOperatorCLM (S := S) (E := E) (F := F)) ∘
        continuousMapSuperposition (S := S) Dc)
      exact hlin.comp (ih Dc hDc)
    · intro u
      exact (hasStrictFDerivAt_continuousMapSuperposition f Dc hD u).hasFDerivAt

/-- Smooth vector fields therefore induce smooth operators on compact path spaces. -/
theorem contDiff_infty_continuousMapSuperposition (f : C(E, F))
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (continuousMapSuperposition (S := S) f) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_continuousMapSuperposition n f (contDiff_infty.mp hf n)

end LichnerowiczObata
