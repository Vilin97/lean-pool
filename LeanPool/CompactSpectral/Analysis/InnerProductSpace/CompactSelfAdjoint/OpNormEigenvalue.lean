/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.NNNorm
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.RayleighCompact

/-!
# Compact self-adjoint operators: an eigenvalue at the operator norm

This file provides two Hilbert-space facts about compact operators:

* A compact operator attains its operator norm on the unit sphere.
* A compact self-adjoint operator has an eigenvalue whose norm is its operator norm.

These are used downstream to turn “no eigenvalues above `ε`” into an operator-norm estimate.
-/

namespace CompactSelfAdjoint

open CompactSpectral
open Filter Topology Metric
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-! ### Weak continuity of the norm on a weakly-closed ball -/

lemma continuousOn_weakClosedBall_norm_apply_of_isCompactOperator
    (T : E →L[𝕜] E) (hTc : IsCompactOperator (T : E → E)) (r : ℝ) :
    ContinuousOn (fun x : WeakSpace 𝕜 E => ‖T (x : E)‖)
      (weakClosedBall (𝕜 := 𝕜) (E := E) r) := by
  classical
  intro x hx
  -- Unfold `ContinuousWithinAt` via `Tendsto`, then use `tendsto_apply_of_isCompactOperator`.
  refine (continuous_norm.tendsto _).comp ?_
  have hx_mem :
      ∀ᶠ y in 𝓝[weakClosedBall (𝕜 := 𝕜) (E := E) r] x,
        y ∈ weakClosedBall (𝕜 := 𝕜) (E := E) r := by
    simpa using
      (eventually_mem_nhdsWithin : ∀ᶠ y in 𝓝[weakClosedBall (𝕜 := 𝕜) (E := E) r] x,
        y ∈ weakClosedBall (𝕜 := 𝕜) (E := E) r)
  have hid :
      Tendsto (fun y : WeakSpace 𝕜 E => y)
        (𝓝[weakClosedBall (𝕜 := 𝕜) (E := E) r] x) (𝓝 x) := by
    -- `map id` is the identity filter, so this is just `nhdsWithin_le_nhds`.
    simpa [Filter.Tendsto, Filter.map_id] using
      (nhdsWithin_le_nhds :
        (𝓝[weakClosedBall (𝕜 := 𝕜) (E := E) r] x) ≤ 𝓝 x)
  exact
    tendsto_apply_of_isCompactOperator (𝕜 := 𝕜) (E := E) (T := T) hTc
      (x := fun y : WeakSpace 𝕜 E => y) (x0 := x) (r := r) hx_mem hid
/-! ### Norm attainment for compact operators -/
theorem exists_unit_norm_eq_opNorm_of_isCompactOperator
    [Nontrivial E] (T : E →L[𝕜] E) (hTc : IsCompactOperator (T : E → E)) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  classical
  by_cases hT0 : T = 0
  · subst hT0
    obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne (0 : E)
    let c : 𝕜 := (((‖x‖)⁻¹ : ℝ) : 𝕜)
    refine ⟨c • x, ?_, ?_⟩
    · simp [c, hx, norm_smul]
    · simp [c]
  -- Work on the unit weak closed ball, which is weakly compact in a Hilbert space.
  let s : Set (WeakSpace 𝕜 E) := weakClosedBall (𝕜 := 𝕜) (E := E) (1 : ℝ)
  let f : WeakSpace 𝕜 E → ℝ := fun x => ‖T (x : E)‖
  have hs_compact : IsCompact s := isCompact_weakClosedBall (𝕜 := 𝕜) (E := E) (1 : ℝ)
  have hs_nonempty : s.Nonempty := by
    refine ⟨(0 : WeakSpace 𝕜 E), ?_⟩
    change (0 : E) ∈ closedBall (α := E) (0 : E) (1 : ℝ)
    exact Metric.mem_closedBall_self zero_le_one
  have hf_cont : ContinuousOn f s :=
    continuousOn_weakClosedBall_norm_apply_of_isCompactOperator (𝕜 := 𝕜) (E := E) T hTc (1 : ℝ)
  rcases hs_compact.exists_isMaxOn hs_nonempty hf_cont with ⟨xMax, hxMax_mem, hxMax⟩
  have hxMax_closed :
      (xMax : E) ∈ closedBall (α := E) (0 : E) (1 : ℝ) := hxMax_mem
  have hxMax_bound :
      ∀ x : E, x ∈ closedBall (α := E) (0 : E) (1 : ℝ) → ‖T x‖ ≤ ‖T (xMax : E)‖ := by
    intro x hx
    have hx' : (x : WeakSpace 𝕜 E) ∈ s := hx
    have hle : f (x : WeakSpace 𝕜 E) ≤ f xMax :=
      (isMaxOn_iff.1 hxMax) (x : WeakSpace 𝕜 E) hx'
    simpa [f] using hle
  -- Show the maximum value is `‖T‖` (the sSup on the closed unit ball).
  have hsSup :
      sSup (Set.image (fun x : E => ‖T x‖) (closedBall (α := E) (0 : E) (1 : ℝ))) = ‖T‖ := by
    simpa using (ContinuousLinearMap.sSup_unitClosedBall_eq_norm (f := T))
  have hmem_image :
      ‖T (xMax : E)‖ ∈
        Set.image (fun x : E => ‖T x‖) (closedBall (α := E) (0 : E) (1 : ℝ)) := by
    refine ⟨(xMax : E), hxMax_closed, rfl⟩
  have hbd : BddAbove (Set.image (fun x : E => ‖T x‖) (closedBall (α := E) (0 : E) (1 : ℝ))) := by
    refine ⟨‖T (xMax : E)‖, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hxMax_bound x hx
  have hsSup_le : sSup (Set.image (fun x : E => ‖T x‖) (closedBall (α := E) (0 : E) (1 : ℝ))) ≤
      ‖T (xMax : E)‖ := by
    have hne :
        (Set.image (fun x : E => ‖T x‖) (closedBall (α := E) (0 : E) (1 : ℝ))).Nonempty := by
      simp_all
    refine csSup_le hne ?_
    simp_all
  have hle_sSup :
      ‖T (xMax : E)‖ ≤
        sSup (Set.image (fun x : E => ‖T x‖) (closedBall (α := E) (0 : E) (1 : ℝ))) := by
    exact le_csSup hbd hmem_image
  have hmax_eq :
      ‖T (xMax : E)‖ =
        sSup (Set.image (fun x : E => ‖T x‖) (closedBall (α := E) (0 : E) (1 : ℝ))) :=
    le_antisymm hle_sSup hsSup_le
  have hTxMax : ‖T (xMax : E)‖ = ‖T‖ := by
    simpa [hsSup] using hmax_eq
  let xe : E := xMax
  have hxMax_norm_le : ‖xe‖ ≤ (1 : ℝ) :=
    (mem_closedBall_zero_iff (a := xe) (r := (1 : ℝ))).1 hxMax_closed
  have hxMax_norm_eq : ‖xe‖ = (1 : ℝ) := by
    by_contra hne
    have hxlt : ‖xe‖ < (1 : ℝ) := lt_of_le_of_ne hxMax_norm_le hne
    have hxpos : 0 < ‖xe‖ := by
      have hnormT_pos : 0 < ‖T‖ := by
        simp_all
      have : 0 < ‖T xe‖ := by rw [hTxMax]; exact hnormT_pos
      -- If `xMax = 0`, then `‖T xMax‖ = 0`, contradiction.
      have hxMax_ne0 : xe ≠ 0 := by
        intro hx0
        simp [hx0, map_zero] at this
      exact (norm_pos_iff).2 hxMax_ne0
    let c : 𝕜 := (((‖xe‖)⁻¹ : ℝ) : 𝕜)
    let y : E := c • xe
    have hy_norm : ‖y‖ = (1 : ℝ) := by
      simp [y, c, norm_smul, hxpos.ne']
    have hy_mem : y ∈ closedBall (α := E) (0 : E) (1 : ℝ) := by
      simp_all
    have hTy :
        ‖T y‖ = (‖xe‖)⁻¹ * ‖T xe‖ := by
      simp [y, c, norm_smul, map_smul]
    have hgt :
        ‖T y‖ > ‖T xe‖ := by
      have hinv : (1 : ℝ) < (‖xe‖)⁻¹ := (one_lt_inv₀ hxpos).2 hxlt
      have hTx_pos : 0 < ‖T xe‖ := by
        have hnormT_pos : 0 < ‖T‖ := by
          simp_all
        rw [hTxMax]; exact hnormT_pos
      simp_all
    exact (not_lt_of_ge (hxMax_bound y hy_mem)) hgt
  refine ⟨xe, hxMax_norm_eq, ?_⟩
  exact hTxMax
/-! ### A compact self-adjoint operator has an eigenvalue at the operator norm -/
theorem exists_hasEigenvector_norm_eq_opNorm_of_isCompactOperator_of_isSelfAdjoint
    [Nontrivial E] (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E)) :
    ∃ μ : 𝕜, ∃ v : E, Module.End.HasEigenvector (T : E →ₗ[𝕜] E) μ v ∧ ‖μ‖ = ‖T‖ := by
  classical
  by_cases hT0 : T = 0
  · subst hT0
    obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := exists_ne (0 : E)
    refine ⟨0, v, ?_, by simp⟩
    refine Module.End.hasEigenvector_iff.mpr ?_
    simp_all
  obtain ⟨x0, hx0_norm, hTx0⟩ :=
    exists_unit_norm_eq_opNorm_of_isCompactOperator (𝕜 := 𝕜) (E := E) T hTc
  have hx0_ne0 : x0 ≠ 0 := by
    intro hx
    simp_all
  -- Apply Rayleigh calculus to `T ∘ T` at a maximiser for `‖T x‖`.
  let A : E →L[𝕜] E := T ∘L T
  have hA : IsSelfAdjoint A := by
    have hT' : ContinuousLinearMap.adjoint T = T := ContinuousLinearMap.isSelfAdjoint_iff'.mp hT
    refine ContinuousLinearMap.isSelfAdjoint_iff'.mpr ?_
    simp [A, ContinuousLinearMap.adjoint_comp, hT']
  have hAc : IsCompactOperator (A : E → E) := by
    -- Precompose `T` with a bounded map, then postcompose by `T`.
    have h1 : IsCompactOperator (fun x : E => T (T x)) := by
      -- `T` is compact, and `T` is continuous.
      exact hTc.clm_comp T
    exact h1
  -- `A.reApplyInnerSelf x = ‖T x‖^2` for self-adjoint `T`.
  have hA_apply (x : E) : A.reApplyInnerSelf x = ‖T x‖ ^ 2 := by
    have hT' : ContinuousLinearMap.adjoint T = T := ContinuousLinearMap.isSelfAdjoint_iff'.mp hT
    -- Use `‖T x‖^2 = re ⟪(T† ∘ T) x, x⟫` and rewrite `T† = T`.
    simpa [A, ContinuousLinearMap.reApplyInnerSelf_apply, hT', ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left (A := T) (x := x)).symm
  have hmax : IsMaxOn A.reApplyInnerSelf (sphere (0 : E) (1 : ℝ)) x0 := by
    intro y hy
    have hy_norm : ‖y‖ = (1 : ℝ) := by simpa using (mem_sphere_zero_iff_norm.1 hy)
    have hle : ‖T y‖ ≤ ‖T‖ := by
      simpa [hy_norm] using (ContinuousLinearMap.le_opNorm T y)
    have hle_sq : ‖T y‖ ^ 2 ≤ ‖T‖ ^ 2 := by
      -- Avoid lemma name drift: prove by expanding `pow_two` and using `mul_le_mul`.
      have hy0 : 0 ≤ ‖T y‖ := norm_nonneg _
      have hT0 : 0 ≤ ‖T‖ := ContinuousLinearMap.opNorm_nonneg T
      have : ‖T y‖ * ‖T y‖ ≤ ‖T‖ * ‖T‖ :=
        mul_le_mul hle hle hy0 hT0
      simpa [pow_two] using this
    simp_all
  have hsup : (⨆ x : { x : E // x ≠ 0 }, A.rayleighQuotient x) = ‖T‖ ^ 2 := by
    classical
    -- First show a uniform upper bound.
    have hbound :
        ∀ x : { x : E // x ≠ 0 }, A.rayleighQuotient x ≤ ‖T‖ ^ 2 := by
      rintro ⟨x, hx⟩
      have hxnorm : ‖x‖ ≠ 0 := by simpa [norm_eq_zero] using hx
      have hRQ :
          A.rayleighQuotient x = (‖T x‖ ^ 2) / (‖x‖ ^ 2) := by
        simp [ContinuousLinearMap.rayleighQuotient, hA_apply]
      have hle : ‖T x‖ ≤ ‖T‖ * ‖x‖ := by
        simpa using (ContinuousLinearMap.le_opNorm T x)
      have hx0 : 0 ≤ ‖T x‖ := norm_nonneg _
      have hT0 : 0 ≤ ‖T‖ * ‖x‖ := by
        exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg T) (norm_nonneg x)
      have hle_sq : ‖T x‖ ^ 2 ≤ (‖T‖ * ‖x‖) ^ 2 := by
        have : ‖T x‖ * ‖T x‖ ≤ (‖T‖ * ‖x‖) * (‖T‖ * ‖x‖) :=
          mul_le_mul hle hle hx0 hT0
        simpa [pow_two] using this
      have hx2_pos : 0 < ‖x‖ ^ 2 := by
        simp_all
      have := (div_le_div_of_nonneg_right hle_sq (le_of_lt hx2_pos))
      have hmul : (‖T‖ * ‖x‖) ^ 2 / (‖x‖ ^ 2) = ‖T‖ ^ 2 := by
        field_simp [pow_two, hxnorm, mul_assoc, mul_left_comm, mul_comm]
      simpa [hRQ, hmul] using this
    have hbdd :
        BddAbove (Set.range fun x : { x : E // x ≠ 0 } => A.rayleighQuotient x) := by
      refine ⟨‖T‖ ^ 2, ?_⟩
      rintro y ⟨x, rfl⟩
      exact hbound x
    refine le_antisymm ?_ ?_
    · -- upper bound
      haveI : Nonempty { x : E // x ≠ 0 } := by
        rcases exists_ne (0 : E) with ⟨x, hx⟩
        exact ⟨⟨x, hx⟩⟩
      exact ciSup_le hbound
    · -- lower bound using the attained value at `x0`
      have hx0ci : A.rayleighQuotient x0 ≤ ⨆ x : { x : E // x ≠ 0 }, A.rayleighQuotient x := by
        let x0' : { x : E // x ≠ 0 } := ⟨x0, hx0_ne0⟩
        have hx0' : A.rayleighQuotient (x0' : E) ≤
            ⨆ x : { x : E // x ≠ 0 }, A.rayleighQuotient x := le_ciSup hbdd x0'
        simpa [x0'] using hx0'
      have hRQx0 : A.rayleighQuotient x0 = ‖T‖ ^ 2 := by
        simp [ContinuousLinearMap.rayleighQuotient, hA_apply, hx0_norm, hTx0]
      -- rewrite the lower bound via `hRQx0`
      simpa [hRQx0] using hx0ci
  have hEigenA :
      Module.End.HasEigenvector (A : E →ₗ[𝕜] E) (↑(‖T‖ ^ 2) : 𝕜) x0 := by
    -- Use the Rayleigh theorem at the maximiser.
    have hA' : IsSelfAdjoint A := hA
    have hmax' : IsMaxOn A.reApplyInnerSelf (sphere (0 : E) ‖x0‖) x0 := by
      simpa [hx0_norm] using hmax
    have hEv :
        Module.End.HasEigenvector (A : E →ₗ[𝕜] E)
          (↑(⨆ x : { x : E // x ≠ 0 }, A.rayleighQuotient x)) x0 :=
      IsSelfAdjoint.hasEigenvector_of_isMaxOn (T := A) hA' (by simpa [hx0_norm] using hx0_ne0) hmax'
    simpa [hsup] using hEv
  -- Extract an eigenvector for `T` with eigenvalue `±‖T‖`.
  let a : 𝕜 := (‖T‖ : 𝕜)
  have ha_ne0 : a ≠ 0 := by
    have : (‖T‖ : ℝ) ≠ 0 := by
      simp_all
    have : ((‖T‖ : ℝ) : 𝕜) ≠ 0 := by
      exact_mod_cast this
    simpa [a] using this
  let u : E := (a⁻¹ : 𝕜) • T x0
  have hTx0_u : T x0 = a • u := by
    simp [u, smul_smul, ha_ne0]
  have hTu_x0 : T u = a • x0 := by
    -- `T u = a⁻¹ • T (T x0) = a⁻¹ • (a^2 • x0) = a • x0`.
    have hAeq :
        T (T x0) = (↑(‖T‖ ^ 2) : 𝕜) • x0 := by
      rcases (Module.End.hasEigenvector_iff.mp hEigenA) with ⟨hxMem, hxNe⟩
      have : ((A : E →ₗ[𝕜] E) x0) = (↑(‖T‖ ^ 2) : 𝕜) • x0 := by
        simpa [Module.End.mem_eigenspace_iff] using hxMem
      simpa [A, ContinuousLinearMap.comp_apply] using this
    have ha2 : (↑(‖T‖ ^ 2) : 𝕜) = a * a := by
      simp [a, pow_two]
    calc
      T u = T ((a⁻¹ : 𝕜) • T x0) := rfl
      _ = (a⁻¹ : 𝕜) • T (T x0) := by simp [map_smul]
      _ = (a⁻¹ : 𝕜) • ((↑(‖T‖ ^ 2) : 𝕜) • x0) := by simp [hAeq]
      _ = ((a⁻¹ : 𝕜) * (↑(‖T‖ ^ 2) : 𝕜)) • x0 := by simp [smul_smul]
      _ = a • x0 := by
            -- `a⁻¹ * (a*a) = a`
            simp [ha2, ha_ne0]
  by_cases hplus : x0 + u = 0
  · -- Then `x0 - u` is a nonzero eigenvector with eigenvalue `-a`.
    have hminus_ne0 : x0 - u ≠ 0 := by
      have hu' : u + x0 = 0 := by simpa [add_comm] using hplus
      have hu : u = -x0 := by simpa [eq_neg_iff_add_eq_zero] using hu'
      -- `x0 - u = 2 • x0`.
      have : x0 - u = (2 : 𝕜) • x0 := by
        simp [hu, two_smul]
      simp_all
    refine ⟨-a, x0 - u, ?_, by simp [a]⟩
    refine Module.End.hasEigenvector_iff.mpr ?_
    refine ⟨?_, hminus_ne0⟩
    rw [Module.End.mem_eigenspace_iff]
    have :
        (T : E →ₗ[𝕜] E) (x0 - u) = (-a) • (x0 - u) := by
      calc
        T (x0 - u) = T x0 - T u := by simp [map_sub]
        _ = a • u - a • x0 := by simp [hTx0_u, hTu_x0]
        _ = (-a) • (x0 - u) := by
              calc
                a • u - a • x0 = a • u + (-a) • x0 := by simp [sub_eq_add_neg]
                _ = (-a) • x0 + a • u := by ac_rfl
                _ = (-a) • (x0 - u) := by
                      simp [sub_eq_add_neg, smul_add]
    simpa using this
  · -- Otherwise `x0 + u` is a nonzero eigenvector with eigenvalue `a`.
    refine ⟨a, x0 + u, ?_, by simp [a]⟩
    refine Module.End.hasEigenvector_iff.mpr ?_
    refine ⟨?_, hplus⟩
    rw [Module.End.mem_eigenspace_iff]
    have :
        (T : E →ₗ[𝕜] E) (x0 + u) = a • (x0 + u) := by
      calc
        T (x0 + u) = T x0 + T u := by simp [map_add]
        _ = a • u + a • x0 := by simp [hTx0_u, hTu_x0]
        _ = a • (x0 + u) := by
              calc
                a • u + a • x0 = a • x0 + a • u := by ac_rfl
                _ = a • (x0 + u) := by simp [smul_add]
    simpa using this
end CompactSelfAdjoint
