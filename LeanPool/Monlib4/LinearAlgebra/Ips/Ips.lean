/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.LinearAlgebra.InvariantSubmodule
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import LeanPool.Monlib4.LinearAlgebra.Ips.Symm

/-!
# Finite-dimensional inner product spaces

In this file, we prove some results in finite-dimensional inner product spaces.

## Notation

This file uses the local notation `P _` for `orthogonal_projection _`
and `↥P _` for the extended orthogonal projection `orthogonal_projection' _`.

We let $V$ be an inner product space over $\mathbb{k}$.
-/


variable {V 𝕜 : Type _} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

local notation "P" => Submodule.orthogonalProjection

-- local notation `↥P` := orthogonal_projection'

open LinearMap in
/-- $U$ is $T$-invariant if and only if $U^\bot$ is $T^*$ invariant -/
theorem Submodule.invariantUnder_iff_ortho_adjoint_invariant [FiniteDimensional 𝕜 V]
    (U : Submodule 𝕜 V) (T : V →ₗ[𝕜] V) :
    Submodule.InvariantUnder U T ↔ Submodule.InvariantUnder Uᗮ (adjoint T) :=
  by
  suffices
    ∀ U : Submodule 𝕜 V,
      ∀ T : V →ₗ[𝕜] V, Submodule.InvariantUnder U T → Submodule.InvariantUnder Uᗮ (adjoint T)
    by
    refine ⟨this U T, ?_⟩
    intro h
    rw [← LinearMap.adjoint_adjoint T, ← Submodule.orthogonal_orthogonal U]
    apply this
    exact h
  clear U T
  simp only [Submodule.invariantUnder_iff, SetLike.mem_coe, Set.subset_def,
    Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro U T h x hx y hy
  rw [LinearMap.adjoint_inner_right]
  apply (Submodule.mem_orthogonal U x).mp hx
  apply h y hy

open ContinuousLinearMap in
theorem Submodule.invariantUnder_iff_ortho_adjoint_invariant' (U : Submodule 𝕜 V) [CompleteSpace V]
    [hU : CompleteSpace U] (T : V →L[𝕜] V) : U.InvariantUnder T ↔ Uᗮ.InvariantUnder (adjoint T) :=
  by
  suffices
    ∀ U : Submodule 𝕜 V,
      ∀ T : V →L[𝕜] V, CompleteSpace U → U.InvariantUnder T → Uᗮ.InvariantUnder (adjoint T)
    by
    refine ⟨this U T hU, fun h => ?_⟩
    rw [← adjoint_adjoint T, ← U.orthogonal_orthogonal]
    exact this _ _ (Submodule.instOrthogonalCompleteSpace U) h
  clear hU U T
  simp_rw [Submodule.invariantUnder_iff, ContinuousLinearMap.coe_coe,
    Set.image_subset_iff, Set.subset_def, Set.mem_preimage]
  intro U T _inst_4 h x hx y hy
  rw [ContinuousLinearMap.adjoint_inner_right]
  apply (U.mem_orthogonal x).mp hx
  apply h y hy

/-- $T$ is self adjoint implies
  $U$ is $T$-invariant if and only if $U^\bot$ is $T$-invariant -/
theorem IsSelfAdjoint.submodule_invariant_iff_ortho_submodule_invariant [FiniteDimensional 𝕜 V]
    (U : Submodule 𝕜 V) (T : V →ₗ[𝕜] V) (h : IsSelfAdjoint T) :
    Submodule.InvariantUnder U T ↔ Submodule.InvariantUnder Uᗮ T := by
  rw [Submodule.invariantUnder_iff_ortho_adjoint_invariant, LinearMap.isSelfAdjoint_iff'.mp h]

open LinearMap in
/-- $\textnormal{ker}(T) = \textnormal{range}(T^*)^\bot$ -/
theorem ker_ortho_adjoint_range {W : Type _} [FiniteDimensional 𝕜 V] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] (T : V →ₗ[𝕜] W) :
    ker T = (range (adjoint T))ᗮ :=
  by
  ext x
  simp_rw [LinearMap.mem_ker, Submodule.mem_orthogonal, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, LinearMap.adjoint_inner_left]
  exact
    ⟨fun h => by simp only [h, inner_zero_right, forall_const], fun h =>
      inner_self_eq_zero.mp (h (T x))⟩

/-- given any idempotent operator $T \in L(V)$, then `is_compl T.ker T.range`;
in other words, there exists unique $v \in \textnormal{ker}(T)$ and
$w \in \textnormal{range}(T)$ such that $x = v + w$ -/
theorem LinearMap.IsProj.isCompl_range_ker {V R : Type _} [Ring R] [AddCommGroup V] [Module R V]
    (U : Submodule R V) (T : V →ₗ[R] V) (h : LinearMap.IsProj U T) : IsCompl (ker T) (range T) :=
  by
  have : IsIdempotentElem T := T.isProj_iff_isIdempotentElem.mp ⟨U, h⟩
  constructor
  · rw [disjoint_iff]
    ext x
    simp only [Submodule.mem_bot, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro h'
      rcases h'.2 with ⟨y, hy⟩
      rw [← hy, ← IsIdempotentElem.eq this, Module.End.mul_apply, hy]
      exact h'.1
    · intro h'
      rw [h', map_zero]
      simp only [true_and]
      use x
      simp only [h', map_zero]
  · suffices ∀ x : V, ∃ v : ker T, ∃ w : range T, x = v + w
      by
      rw [codisjoint_iff, ← Submodule.add_eq_sup]
      ext x
      rcases this x with ⟨v, w, hvw⟩
      simp only [Submodule.mem_top, iff_true, hvw]
      apply Submodule.add_mem_sup (SetLike.coe_mem v) (SetLike.coe_mem w)
    intro x
    use ⟨x - T x, ?_⟩, ⟨T x, ?_⟩
    · simp only [sub_add_cancel]
    · rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, IsIdempotentElem.eq this, sub_self]
    · rw [LinearMap.mem_range]
      simp only [exists_apply_eq_apply]

/--
idempotent $T$ is self-adjoint if and only if $\textnormal{ker}(T)^\bot=\textnormal{range}(T)$ -/
theorem LinearMap.is_idempotent_isSelfAdjoint_iff_ker_ortho_range [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (h : IsIdempotentElem T) :
    IsSelfAdjoint T ↔ (ker T)ᗮ = range T :=
  by
  rw [LinearMap.isSelfAdjoint_iff']
  constructor
  · intro l; rw [ker_ortho_adjoint_range, Submodule.orthogonal_orthogonal]
    revert l; exact congr_arg LinearMap.range
  · intro h1; apply eq_of_sub_eq_zero
    simp only [← inner_map_self_eq_zero]
    intro x
    obtain ⟨U, hT⟩ := T.isProj_iff_isIdempotentElem.mpr h
    obtain ⟨v, w, hvw, _⟩ :=
      Submodule.existsUnique_add_of_isCompl (LinearMap.IsProj.isCompl_range_ker U T hT) x
    simp only [LinearMap.sub_apply, inner_sub_left, LinearMap.adjoint_inner_left]
    rcases SetLike.coe_mem w with ⟨y, hy⟩
    rw [← hvw, map_add, LinearMap.mem_ker.mp (SetLike.coe_mem v), ← hy,
      ← Module.End.mul_apply, IsIdempotentElem.eq h, zero_add, hy, inner_add_left,
      inner_add_right, ← inner_conj_symm (w : V) (v : V),
      (Submodule.mem_orthogonal (ker T) (w : V)).mp (by rw [h1]; exact SetLike.coe_mem w) v
        (SetLike.coe_mem v),
      map_zero, zero_add, sub_self]

section IsStarNormal

open LinearMap

/-- linear map `is_star_normal` if and only if it commutes with its adjoint -/
theorem LinearMap.isStarNormal_iff_adjoint [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ Commute T (adjoint T) :=
by rw [Commute.symm_iff]; exact ⟨fun hT => hT.star_comm_self, IsStarNormal.mk⟩

theorem ContinuousLinearMap.isStarNormal_iff_adjoint [CompleteSpace V] (T : V →L[𝕜] V) :
    IsStarNormal T ↔ Commute T (adjoint T) :=
by rw [Commute.symm_iff]; exact ⟨fun hT => hT.star_comm_self, IsStarNormal.mk⟩

theorem isSymmetric_hMul_adjoint_self [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V) :
    IsSymmetric (T * (adjoint T)) := fun u v => by
  simp_rw [Module.End.mul_apply, ← adjoint_inner_left T, ← adjoint_inner_right T]

theorem IsSymmetric.neg (T : V →ₗ[𝕜] V) (hT : T.IsSymmetric) : IsSymmetric (-T) :=
  by
  intro u v
  simp_rw [neg_apply, inner_neg_left, inner_neg_right, neg_inj]
  exact hT u v

theorem IsSymmetric.sub {T S : V →ₗ[𝕜] V} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T - S).IsSymmetric := by
  rw [sub_eq_add_neg]
  exact IsSymmetric.add hT (IsSymmetric.neg S hS)

/-- $T$ is normal if and only if $\forall v, \|T v\| = \|T^* v\|$ -/
theorem LinearMap.IsStarNormal.norm_eq_adjoint [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ ∀ v : V, ‖T v‖ = ‖adjoint T v‖ :=
  by
  rw [T.isStarNormal_iff_adjoint, Commute, SemiconjBy, ← sub_eq_zero]
  simp_rw [←
    IsSymmetric.inner_map_self_eq_zero
      (IsSymmetric.sub (isSymmetric_hMul_adjoint_self T) (isSymmetric_adjoint_mul_self T)),
    sub_apply, inner_sub_left, Module.End.mul_apply, adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← adjoint_inner_right T, inner_self_eq_norm_sq_to_K, sub_eq_zero, ←
    sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  norm_cast
  simp_rw [eq_comm]

theorem ContinuousLinearMap.IsStarNormal.norm_eq_adjoint [CompleteSpace V] (T : V →L[𝕜] V) :
    IsStarNormal T ↔ ∀ v : V, ‖T v‖ = ‖adjoint T v‖ :=
  by
  rw [T.isStarNormal_iff_adjoint, Commute, SemiconjBy, ← sub_eq_zero]
  simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_sub,
    ← LinearMap.ext_iff, ContinuousLinearMap.coe_zero]
  have : IsSymmetric ((T.comp (adjoint T) : V →ₗ[𝕜] V) - ((adjoint T).comp T : V →ₗ[𝕜] V)) :=
    fun u v => by
    simp_rw [← ContinuousLinearMap.mul_def, LinearMap.sub_apply,
      ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.mul_apply, inner_sub_left, inner_sub_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, sub_left_inj,
      ← ContinuousLinearMap.adjoint_inner_left T, ← ContinuousLinearMap.adjoint_inner_right T]
  simp_rw [← ContinuousLinearMap.mul_def] at this
  rw [← IsSymmetric.inner_map_self_eq_zero this]
  simp_rw [LinearMap.sub_apply, inner_sub_left, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← ContinuousLinearMap.adjoint_inner_right T,
    inner_self_eq_norm_sq_to_K, sub_eq_zero, ←
    sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), eq_comm]
  norm_cast

/-- if $T$ is normal, then $\textnormal{ker}(T) = \textnormal{ker}(T^*)$ -/
theorem LinearMap.IsStarNormal.ker_eq_ker_adjoint [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (h : IsStarNormal T) : ker T = ker (adjoint T) := by
  ext
  rw [mem_ker, mem_ker, ← norm_eq_zero, Iff.comm, ← norm_eq_zero,
    ← (LinearMap.IsStarNormal.norm_eq_adjoint T).mp h]

/-- if $T$ is normal, then $\textnormal{range}(T)=\textnormal{range}(T^*)$ -/
theorem LinearMap.IsStarNormal.range_eq_range_adjoint [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (h : IsStarNormal T) : range T = range (adjoint T) := by
  rw [← Submodule.orthogonal_orthogonal (range (adjoint T)), ← ker_ortho_adjoint_range,
    LinearMap.IsStarNormal.ker_eq_ker_adjoint T h, ker_ortho_adjoint_range, adjoint_adjoint,
    Submodule.orthogonal_orthogonal]

theorem ContinuousLinearMap.IsStarNormal.ker_eq_ker_adjoint [CompleteSpace V] {T : V →L[𝕜] V}
    (h : IsStarNormal T) : T.ker = (adjoint T).ker := by
  exact (ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker h).symm


theorem ContinuousLinearMap.ker_eq_ortho_adjoint_range {W : Type _} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W] (T : V →L[𝕜] W) :
    T.ker = (adjoint T).rangeᗮ := by
  simpa [ContinuousLinearMap.adjoint_adjoint] using
    (ContinuousLinearMap.orthogonal_range (adjoint T)).symm

theorem ContinuousLinearMap.ker_adjoint_eq_ortho_range {W : Type _} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W] (T : V →L[𝕜] W) :
    (adjoint T).ker = T.rangeᗮ := by
  simpa using (ContinuousLinearMap.orthogonal_range T).symm

theorem ContinuousLinearMap.ker_adjoint_ortho_eq_range {W : Type _} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W] (T : V →L[𝕜] W)
    [T.range.HasOrthogonalProjection] :
    ((adjoint T).ker)ᗮ = T.range := by
  rw [ker_adjoint_eq_ortho_range, Submodule.orthogonal_orthogonal]

theorem ContinuousLinearMap.IsStarNormal.isCompl_ker_range (T : V →L[𝕜] V)
  [CompleteSpace V]
  [T.range.HasOrthogonalProjection]
  (h : IsStarNormal T) : IsCompl T.ker T.range := by
  simpa [ContinuousLinearMap.IsStarNormal.orthogonal_range h] using
    (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection (K := T.range)).symm

theorem ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_ker_isOrtho_to_range
    [InnerProductSpace ℂ V] [CompleteSpace V] (T : V →L[ℂ] V) (h : IsIdempotentElem T) :
    IsSelfAdjoint T ↔ T.ker = T.rangeᗮ := by
  constructor
  · intro hT;
    rw [← ContinuousLinearMap.adjoint_adjoint T, ←
      ContinuousLinearMap.ker_eq_ortho_adjoint_range, ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.IsStarNormal.ker_eq_ker_adjoint hT.isStarNormal
  · intro h1
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    apply eq_of_sub_eq_zero
    simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_sub, ContinuousLinearMap.coe_zero,
      ← LinearMap.ext_iff, ← inner_map_self_eq_zero]
    intro x
    have h_toLinearMap : IsIdempotentElem T.toLinearMap :=
      ContinuousLinearMap.IsIdempotentElem.toLinearMap h
    have h_idempotent := IsIdempotentElem.eq h_toLinearMap
    rw [Module.End.mul_eq_comp] at h_idempotent
    obtain ⟨U, hT⟩ := T.toLinearMap.isProj_iff_isIdempotentElem.mpr h_idempotent
    obtain ⟨v, w, hvw, _⟩ :=
      Submodule.existsUnique_add_of_isCompl (LinearMap.IsProj.isCompl_range_ker U (↑T) hT) x
    simp only [LinearMap.sub_apply, inner_sub_left]
    rcases SetLike.coe_mem w with ⟨y, hy⟩
    simp_rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.adjoint_inner_left, ←
      ContinuousLinearMap.coe_coe, ← hvw, map_add, LinearMap.mem_ker.mp (SetLike.coe_mem v), ← hy,
      ← Module.End.mul_apply, IsIdempotentElem.eq h_toLinearMap, zero_add, hy,
      inner_add_left, inner_add_right, ←
      inner_conj_symm (w : V) (v : V),
      (Submodule.mem_orthogonal T.ker (w : V)).mp
        (by rw [h1]; intro y hy; rw [inner_eq_zero_symm]; exact hy w (SetLike.coe_mem w)) v
        (SetLike.coe_mem v),
      map_zero, zero_add, sub_self]

open scoped ComplexConjugate

open Module.End

/--
If $T$ is normal, then $\forall x \in V$,
$x \in \textnormal{eigenspace}(T ,\mu) \iff x \in \textnormal{eigenspace}(T^* ,\bar{\mu})$.
-/
theorem LinearMap.IsStarNormal.eigenvec_in_eigenspace_iff_eigenvec_in_adjoint_conj_eigenspace
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (h : IsStarNormal T) (μ : ℂ) :
    ∀ x : V, x ∈ eigenspace T μ ↔ x ∈ eigenspace (adjoint T) (conj μ) :=
  by
  suffices
    ∀ T : V →ₗ[ℂ] V,
      IsStarNormal T → ∀ μ : ℂ, ∀ v : V, v ∈ eigenspace T μ → v ∈ eigenspace (adjoint T) (conj μ)
    by
    intro v; refine ⟨this T h μ v, ?_⟩
    intro hv; rw [← adjoint_adjoint T, ← RCLike.conj_conj μ]
    apply this _ _ _ _ hv; exact IsStarNormal.star
  clear h μ T
  intro T h μ v hv
  have t1 : (T - μ • 1) v = 0 :=
    by
    rw [sub_apply, smul_apply, one_apply, sub_eq_zero]
    exact mem_eigenspace_iff.mp hv
  suffices (adjoint T - conj μ • 1) v = 0
    by
    rw [mem_eigenspace_iff, ← sub_eq_zero]
    rw [sub_apply, smul_apply, one_apply] at this; exact this
  rw [← norm_eq_zero]
  have nh : IsStarNormal (T - μ • 1) := by
    apply IsStarNormal.mk
    rw [star_sub, star_smul, RCLike.star_def, star_one, Commute, SemiconjBy]
    simp only [sub_mul, mul_sub, Commute.eq h.star_comm_self]
    simp only [smul_one_mul, smul_smul, mul_smul_comm, mul_one]
    rw [mul_comm, sub_sub_sub_comm]
  have : adjoint (T - μ • 1) = adjoint T - conj μ • 1 := by
    simp only [← star_eq_adjoint, star_sub, star_smul, RCLike.star_def, star_one]
  rw [← this, ← (LinearMap.IsStarNormal.norm_eq_adjoint (T - μ • 1)).mp nh, t1, norm_zero]

end IsStarNormal

lemma ContinuousLinearMap.ker_to_linearMap_ker {W : Type _} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] (T : V →L[𝕜] W) :
    ∀ x, x ∈ LinearMap.ker (T : V →ₗ[𝕜] W) ↔ T x = 0 := by
  intro x
  rfl

/-- $T$ is injective if and only if $T^*$ is surjective. -/
theorem ContinuousLinearMap.adjoint_injective_iff_surjective {W : Type _} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [CompleteSpace W] [CompleteSpace V] (T : V →L[𝕜] W)
    [T.range.HasOrthogonalProjection] :
    Function.Injective (adjoint T) ↔ Function.Surjective T := by
  change Function.Injective (adjoint T).toLinearMap ↔ Function.Surjective T.toLinearMap
  rw [← LinearMap.ker_eq_bot, ← LinearMap.range_eq_top]
  change (adjoint T).ker = ⊥ ↔ T.range = ⊤
  rw [ContinuousLinearMap.ker_adjoint_eq_ortho_range, Submodule.orthogonal_eq_bot_iff]

/-- $T$ is injective if and only if $T^*$ is surjective. -/
theorem LinearMap.injective_iff_adjoint_surjective {W : Type _} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) :
    Function.Injective T ↔ Function.Surjective (adjoint T) := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.range_eq_top, ker_ortho_adjoint_range,
    Submodule.orthogonal_eq_bot_iff]
