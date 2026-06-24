/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import LeanPool.Monlib4.LinearAlgebra.InvariantSubmodule
import LeanPool.Monlib4.LinearAlgebra.Ips.RankOne
import LeanPool.Monlib4.LinearAlgebra.End
import Mathlib.Analysis.InnerProductSpace.Positive
import LeanPool.Monlib4.Preq.RCLikeLe

/-!

# Positive linear maps

This file generalises the notion of positivity to linear maps. We follow the same definition as
`continuous_linear_map.IsPositive'` but change the `self-adjoinnt` property to `is_symmertric`.
A linear map is positive if it is symmetric and `∀ x, 0 ≤ re ⟪T x, x⟫`.

## Main statements

for linear maps:
* `linear_map.IsPositive'.conj_adjoint` : if `T : E →ₗ[𝕜] E` and `E` is a finite-dimensional space,
  then for any `S : E →ₗ[𝕜] F`, we have `S.comp (T.comp S.adjoint)` is also positive.

-/

open InnerProductSpace RCLike

open scoped InnerProduct ComplexConjugate

variable {𝕜 E F : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

namespace LinearMap

open scoped ComplexOrder

/-- `T` is (semi-definite) **positive** if `T` is symmetric
and `∀ x : V, 0 ≤ re ⟪x, T x⟫` -/
def IsPositive' (T : E →ₗ[𝕜] E) : Prop :=
  T.IsSymmetric ∧ ∀ x : E, 0 ≤ ⟪x, T x⟫

theorem IsPositive'Zero : (0 : E →ₗ[𝕜] E).IsPositive' := by
  refine ⟨IsSymmetric.zero, fun x => ?_⟩
  simp_rw [zero_apply, inner_zero_right, le_rfl]

theorem IsPositive'One : (1 : E →ₗ[𝕜] E).IsPositive' :=
  ⟨IsSymmetric.id, fun _ => inner_self_nonneg'⟩

theorem _root_.LinearMap.IsPositive'.add {S T : E →ₗ[𝕜] E}
    (hS : S.IsPositive') (hT : T.IsPositive') :
    (S + T).IsPositive' := by
  refine ⟨IsSymmetric.add hS.1 hT.1, fun x => ?_⟩
  rw [add_apply, inner_add_right]
  exact add_nonneg (hS.2 _) (hT.2 _)

theorem _root_.LinearMap.IsPositive'.inner_nonneg_left {T : E →ₗ[𝕜] E}
    (hT : IsPositive' T) (x : E) :
    0 ≤ ⟪T x, x⟫ := by rw [hT.1]; exact hT.2 x

theorem _root_.LinearMap.IsPositive'.inner_nonneg_right {T : E →ₗ[𝕜] E}
    (hT : IsPositive' T) (x : E) :
    0 ≤ ⟪x, T x⟫ :=
  hT.2 x

/-- a linear projection onto `U` along its complement `V` is positive if
and only if `U` and `V` are pairwise orthogonal -/
theorem linear_proj_IsPositive'_iff {U V : Submodule 𝕜 E} (hUV : IsCompl U V) :
    (U.subtype.comp (U.projectionOnto V hUV)).IsPositive' ↔ U ⟂ V := by
  constructor
  · intro h u hu v hv
    rw [← Subtype.coe_mk u hu, ← Subtype.coe_mk v hv, ←
      Submodule.projectionOnto_apply_left hUV ⟨u, hu⟩, ← Submodule.subtype_apply (p := U), ←
      comp_apply, ← h.1 _ _, comp_apply, Submodule.projectionOnto_apply_right hUV ⟨v, hv⟩,
      map_zero, inner_zero_left]
  · intro h
    have : (U.subtype.comp (U.projectionOnto V hUV)).IsSymmetric := by
      intro x y
      nth_rw 1 [← Submodule.linear_proj_add_linearProjOfIsCompl_eq_self hUV y]
      nth_rw 2 [← Submodule.linear_proj_add_linearProjOfIsCompl_eq_self hUV x]
      rw [Submodule.isOrtho_iff_inner_eq] at h
      simp_rw [inner_add_right, inner_add_left, comp_apply, Submodule.subtype_apply _]
      rw [@h _ (SetLike.coe_mem _) _ (SetLike.coe_mem _),
        inner_eq_zero_symm.mp (h _ (SetLike.coe_mem _) _ (SetLike.coe_mem _))]
    refine ⟨this, ?_⟩
    intro x
    let p : E →ₗ[𝕜] E := U.subtype.comp (U.projectionOnto V hUV)
    change 0 ≤ ⟪x, p x⟫
    have hp : p (p x) = p x := by
      change
        ((U.subtype.comp (U.projectionOnto V hUV)) *
            (U.subtype.comp (U.projectionOnto V hUV))) x =
          (U.subtype.comp (U.projectionOnto V hUV)) x
      rw [Submodule.linearProjOfIsCompl_idempotent hUV]
    rw [← hp, ← this x (p x)]
    exact inner_self_nonneg'

theorem _root_.ContinuousLinearMap.IsPositive.toLinearMap' [FiniteDimensional 𝕜 E] (T : E →L[𝕜] E) :
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  T.IsPositive ↔ T.toLinearMap.IsPositive' := by
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  simp_rw [LinearMap.IsPositive', ContinuousLinearMap.coe_coe, ContinuousLinearMap.IsPositive,
    ← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    ContinuousLinearMap.reApplyInnerSelf_apply T, and_congr_right_iff, ← @zero_le_real 𝕜]
  intro h
  simp_rw [IsSelfAdjoint.inner_re_eq h, ← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint]
  rw [h]

lemma isPositive'_iff_isPositive
  [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
  T.IsPositive' ↔ T.IsPositive := by
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  rw [← T.isPositive_toContinuousLinearMap_iff, ContinuousLinearMap.IsPositive.toLinearMap']
  rfl

lemma _root_.LinearMap.IsPositive.isPositive' [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}
  (hT : T.IsPositive) : T.IsPositive' :=
(isPositive'_iff_isPositive T).mpr hT

section FiniteDimensional

local notation "e" => IsSymmetric.eigenvectorBasis

local notation "α" => IsSymmetric.eigenvalues

local notation "√" => Real.sqrt

variable [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E)

open scoped ComplexOrder

omit [FiniteDimensional 𝕜 E] in
private theorem _root_.spec_subseteq_nonneg :
  (spectrum 𝕜 T) ⊆ { x : 𝕜 | 0 ≤ x } ↔ ∀ x ∈ spectrum 𝕜 T, 0 ≤ x := by
  simp_rw [Set.subset_def, Set.mem_setOf_eq]

/-- the spectrum of a positive linear map is non-negative -/
theorem _root_.LinearMap.IsPositive'.nonneg_spectrum (h : T.IsPositive') :
  (spectrum 𝕜 T) ⊆ { x : 𝕜 | 0 ≤ x } := by
  intro μ hμ
  simp_rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  simp only [Set.mem_setOf_eq, @RCLike.nonneg_def' 𝕜]
  have : ↑(re μ) = μ := by
    simp_rw [← conj_eq_iff_re]
    exact IsSymmetric.conj_eigenvalue_eq_self h.1 hμ
  rw [← this] at hμ
  exact ⟨this, eigenvalue_nonneg_of_nonneg hμ (fun _ => ((@RCLike.nonneg_def 𝕜 _ _).mp (h.2 _)).1)⟩

open scoped BigOperators

/-- given a symmetric linear map with a non-negative spectrum,
we can write `T x = ∑ i, √α i • √α i • ⟪e i, x⟫` for any `x ∈ E`,
where `α i` are the eigenvalues of `T` and `e i` are the respective eigenvectors
that form an eigenbasis (`isSymmetric.eigenvector_basis`) -/
theorem sq_mul_sq_eq_self_of_isSymmetric_and_nonneg_spectrum
    (hT : T.IsSymmetric) (hT1 : (spectrum 𝕜 T) ⊆ { x : 𝕜 | 0 ≤ x })
    (v : E) : T v = ∑ i, (√ (α hT rfl i) • √ (α hT rfl i) : 𝕜) • ⟪e hT rfl i, v⟫ • e hT rfl i := by
  have : ∀ i, 0 ≤ α hT rfl i := fun i => by
    rw [spec_subseteq_nonneg] at hT1
    specialize hT1 (hT.eigenvalues rfl i)
    simp only [zero_le_real] at hT1
    apply
      hT1
        (Module.End.hasEigenvalue_iff_mem_spectrum.mp (hT.hasEigenvalue_eigenvalues rfl i))
  calc
    T v = ∑ i, ⟪e hT rfl i, v⟫ • T (e hT rfl i) := by
      simp_rw [← OrthonormalBasis.repr_apply_apply, ← map_smul_of_tower, ← map_sum,
        OrthonormalBasis.sum_repr (e hT rfl) v]
    _ = ∑ i, (√ (α hT rfl i) • √ (α hT rfl i) : 𝕜) • ⟪e hT rfl i, v⟫ • e hT rfl i := by
      simp_rw [IsSymmetric.apply_eigenvectorBasis, smul_smul,
        real_smul_ofReal, ← ofReal_mul, ← Real.sqrt_mul (this _), Real.sqrt_mul_self (this _),
        mul_comm]

/-- given a symmetric linear map `T` and a real number `r`,
we can define a linear map `S` such that `S = T ^ r` -/
noncomputable def rePow
    (hT : T.IsSymmetric) (r : ℝ) : E →ₗ[𝕜] E
    where
  toFun v := ∑ i, (((α hT rfl i : ℝ) ^ r : ℝ) : 𝕜) • ⟪e hT rfl i, v⟫ • e hT rfl i
  map_add' x y := by simp_rw [inner_add_right, add_smul, smul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [inner_smul_right, ← smul_smul, Finset.smul_sum, RingHom.id_apply, smul_smul, ←
      mul_assoc, mul_comm]

section

/-- Complex functional calculus power of a positive linear map. -/
noncomputable def cpow [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsPositive') (c : ℂ) : E →ₗ[ℂ] E
    where
  toFun v := ∑ i, (α hT.1 rfl i ^ c : ℂ) • ⟪e hT.1 rfl i, v⟫_ℂ • e hT.1 rfl i
  map_add' x y := by simp_rw [inner_add_right, add_smul, smul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [inner_smul_right, ← smul_smul, Finset.smul_sum, RingHom.id_apply, smul_smul, ←
      mul_assoc, mul_comm]

theorem cpow_apply [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsPositive') (c : ℂ) (v : E) :
    T.cpow hT c v = ∑ i, (α hT.1 rfl i ^ c : ℂ) • ⟪e hT.1 rfl i, v⟫_ℂ • e hT.1 rfl i :=
  rfl

end

theorem _root_.LinearMap.rePow_apply (hT : T.IsSymmetric)
    (r : ℝ) (v : E) :
    T.rePow hT r v = ∑ i, (((α hT rfl i : ℝ) ^ r : ℝ) : 𝕜) • ⟪e hT rfl i, v⟫ • e hT rfl i :=
  rfl

/-- the square root of a symmetric linear map can then directly be defined with `re_pow` -/
noncomputable def _root_.LinearMap.sqrt
    (h : T.IsSymmetric) : E →ₗ[𝕜] E :=
  T.rePow h (1 / 2 : ℝ)

/-- the square root of a symmetric linear map `T`
is written as `T x = ∑ i, √ (α i) • ⟪e i, x⟫ • e i` for any `x ∈ E`,
where `α i` are the eigenvalues of `T` and `e i` are the respective eigenvectors
that form an eigenbasis (`isSymmetric.eigenvector_basis`) -/
theorem _root_.LinearMap.sqrt_apply (hT : T.IsSymmetric)
    (x : E) : T.sqrt hT x = ∑ i, (√ (α hT rfl i) : 𝕜) • ⟪e hT rfl i, x⟫ • e hT rfl i := by
  simp_rw [Real.sqrt_eq_rpow _]; rfl

/-- given a symmetric linear map `T` with a non-negative spectrum,
the square root of `T` composed with itself equals itself, i.e., `T.sqrt ^ 2 = T`. -/
theorem _root_.LinearMap.sqrt_sq_eq_self_of_isSymmetric_and_nonneg_spectrum
  (hT : T.IsSymmetric) (hT1 : (spectrum 𝕜 T) ⊆ {x : 𝕜 | 0 ≤ x}) :
    T.sqrt hT ^ 2 = T := by
  simp_rw [pow_two, Module.End.mul_eq_comp, LinearMap.ext_iff, comp_apply, sqrt_apply, inner_sum,
    inner_smul_real_right, smul_smul, inner_smul_right, ← OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.repr_self, PiLp.single_apply, mul_boole, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Algebra.mul_smul_comm,
    sq_mul_sq_eq_self_of_isSymmetric_and_nonneg_spectrum T hT hT1,
    OrthonormalBasis.repr_apply_apply, ← smul_eq_mul, ← smul_assoc, forall_const]

/-- given a symmetric linear map `T`, we have that its root is positive -/
theorem _root_.LinearMap.IsSymmetric.sqrtIsPositive'
    (hT : T.IsSymmetric) : (T.sqrt hT).IsPositive' := by
  have : (T.sqrt hT).IsSymmetric := by
    intro x y
    simp_rw [sqrt_apply T hT, inner_sum, sum_inner, smul_smul, inner_smul_right, inner_smul_left]
    have : ∀ i, conj (√ (α hT rfl i) : 𝕜) = (√ (α hT rfl i) : 𝕜) := fun i => by
      simp_rw [conj_eq_iff_re, ofReal_re]
    simp_rw [mul_assoc, map_mul, this _, inner_conj_symm, mul_comm ⟪e hT rfl _, y⟫ _, ← mul_assoc]
  refine ⟨this, ?_⟩
  intro x
  simp_rw [sqrt_apply _ hT, inner_sum, inner_smul_right]
  apply Finset.sum_nonneg'
  intro i
  simp_rw [← inner_conj_symm x _, ← OrthonormalBasis.repr_apply_apply, mul_conj,
    ← ofReal_pow, ← ofReal_mul, ofReal_nonneg]
  exact mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)

/-- `T` is positive if and only if `T` is symmetric
(which is automatic from the definition of positivity)
and has a non-negative spectrum -/
theorem _root_.LinearMap.isPositive'_iff_isSymmetric_and_nonneg_spectrum :
    T.IsPositive' ↔ T.IsSymmetric ∧ (spectrum 𝕜 T) ⊆ {x : 𝕜 | 0 ≤ x} := by
  classical
  refine ⟨fun h => ⟨h.1, fun μ hμ => IsPositive'.nonneg_spectrum T h hμ⟩,
    fun h => ⟨h.1, ?_⟩⟩
  intro x
  rw [← sqrt_sq_eq_self_of_isSymmetric_and_nonneg_spectrum T h.1 h.2, pow_two,
    Module.End.mul_apply, ← adjoint_inner_left,
    isSelfAdjoint_iff'.mp
      ((isSymmetric_iff_isSelfAdjoint _).mp (IsSymmetric.sqrtIsPositive' T h.1).1)]
  exact inner_self_nonneg'

/-- `T` is positive if and only if there exists a
linear map `S` such that `T = S.adjoint * S` -/
theorem _root_.LinearMap.isPositive'_iff_exists_adjoint_hMul_self :
    T.IsPositive' ↔ ∃ S : E →ₗ[𝕜] E, T = adjoint S * S := by
  classical
  constructor
  · rw [isPositive'_iff_isSymmetric_and_nonneg_spectrum T]
    rintro ⟨hT, hT1⟩
    use T.sqrt hT
    rw [isSelfAdjoint_iff'.mp
        ((isSymmetric_iff_isSelfAdjoint _).mp (IsSymmetric.sqrtIsPositive' T hT).1),
      ← pow_two]
    exact (sqrt_sq_eq_self_of_isSymmetric_and_nonneg_spectrum T hT hT1).symm
  · intro h
    rcases h with ⟨S, rfl⟩
    refine ⟨isSymmetric_adjoint_mul_self S, ?_⟩
    intro x
    simp_rw [Module.End.mul_apply, adjoint_inner_right]
    exact inner_self_nonneg'

section Complex

/-- for spaces `V` over `ℂ`, it suffices to define positivity with
`0 ≤ ⟪v, T v⟫_ℂ` for all `v ∈ V` -/
theorem _root_.LinearMap.complex_isPositive' {V : Type _} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V]
    (T : V →ₗ[ℂ] V) : T.IsPositive' ↔ ∀ v : V, 0 ≤ ⟪v, T v⟫_ℂ := by
  simp_rw [IsPositive', isSymmetric_iff_inner_map_self_real, eq_comm, inner_conj_symm,
    ← inner_conj_symm (T _), @RCLike.nonneg_def' ℂ,
    RCLike.re_to_complex, Complex.conj_eq_iff_re,
    ← forall_and]
  exact ⟨fun h v => ⟨(h v).1, (h v).2.2⟩,
    fun h v => ⟨(h v).1, (h v).1, (h v).2⟩⟩

end Complex

theorem _root_.LinearMap.IsPositive'.conjAdjoint [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] E) (S : E →ₗ[𝕜] F)
    (h : T.IsPositive') : (S.comp (T.comp (adjoint S))).IsPositive' := by
  constructor
  · intro u v
    simp_rw [comp_apply, ← adjoint_inner_left _ (T _), ← adjoint_inner_right _ (T _) _]
    exact h.1 _ _
  · intro v
    simp_rw [comp_apply, ← adjoint_inner_left _ (T _)]
    exact h.2 _

theorem _root_.LinearMap.IsPositive'.adjointConj [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] E) (S : F →ₗ[𝕜] E)
    (h : T.IsPositive') : (S.adjoint.comp (T.comp S)).IsPositive' := by
  constructor
  · intro u v
    simp_rw [comp_apply, adjoint_inner_left, adjoint_inner_right]
    exact h.1 _ _
  · intro v
    simp_rw [comp_apply, adjoint_inner_right]
    exact h.2 _

local notation "√T⋆" T =>
  LinearMap.sqrt ((LinearMap.adjoint T) ∘ₗ T) (isSymmetric_adjoint_mul_self T)

/-- we have `(T.adjoint.comp T).sqrt` is positive, given any linear map `T` -/
theorem _root_.LinearMap.sqrtAdjointSelfIsPositive' (T : E →ₗ[𝕜] E) : (√T⋆T).IsPositive' :=
  IsSymmetric.sqrtIsPositive' _ (isSymmetric_adjoint_mul_self T)

open Module.End

/-- given any linear map `T` and `x ∈ E` we have
`‖(T.adjoint.comp T).sqrt x‖ = ‖T x‖` -/
theorem _root_.LinearMap.norm_of_sqrt_adjoint_mul_self_eq (T : E →ₗ[𝕜] E) (x : E) :
    ‖(√T⋆T) x‖ = ‖T x‖ := by
  simp_rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← @inner_self_eq_norm_sq 𝕜, ←
    adjoint_inner_left,
    isSelfAdjoint_iff'.mp
      ((isSymmetric_iff_isSelfAdjoint _).mp (sqrtAdjointSelfIsPositive' T).1),
    ← mul_eq_comp, ← mul_apply, ← pow_two, mul_eq_comp]
  congr
  apply sqrt_sq_eq_self_of_isSymmetric_and_nonneg_spectrum
  apply IsPositive'.nonneg_spectrum _ ⟨isSymmetric_adjoint_mul_self T, _⟩
  intro x
  simp_rw [mul_apply, adjoint_inner_right]
  exact inner_self_nonneg'

theorem _root_.LinearMap.invertibleIff_inner_map_self_pos
    (hT : T.IsPositive') : Function.Bijective T ↔ ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫ := by
  constructor
  · intro h v hv
    rcases (isPositive'_iff_exists_adjoint_hMul_self T).mp hT with ⟨S, hS⟩
    rw [hS, mul_apply, adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    suffices S v ≠ 0 by
      rw [← norm_ne_zero_iff] at this
      rw [← RCLike.ofReal_pow, RCLike.zero_lt_real]
      exact sq_pos_iff.mpr this
    by_contra hSv
    rw [LinearMap.ext_iff] at hS
    specialize hS v
    rw [mul_apply, hSv, map_zero] at hS
    apply hv
    apply_fun T
    · rw [map_zero]
      exact hS
    · exact h.1
  · intro h
    by_contra hbij
    rw [Function.Bijective, ← injective_iff_surjective,
      and_self_iff, injective_iff_map_eq_zero] at hbij
    push Not at hbij
    rcases hbij with ⟨a, ha⟩
    specialize h a ha.2
    rw [ha.1, inner_zero_left, lt_self_iff_false] at h
    exact h

theorem _root_.LinearMap.invertiblePos (T : E →ₗ[𝕜] E) [hTi : Invertible T]
    (hT : T.IsPositive') : IsPositive' (⅟ T) := by
  have : Function.Bijective T := by
    refine (Module.End.isUnit_iff T).mp ?_
    exact isUnit_of_invertible T
  rw [invertibleIff_inner_map_self_pos T hT] at this
  constructor
  · intro u v
    rw [← adjoint_inner_left]
    revert v
    have ugh := ((isSymmetric_iff_isSelfAdjoint T).mp hT.1).star_eq
    have t : star (⅟ T) = ⅟ (star T) := star_invOf _
    rw [← ext_inner_left_iff ((⅟ T) u) (adjoint (⅟ T) u), ← star_eq_adjoint]
    simp_rw [t, ugh]
  · intro x
    by_cases b : ⅟ T x = 0
    · rw [b, inner_zero_right]
    · specialize this _ b
      rw [← mul_apply, mul_invOf_self, one_apply] at this
      exact le_of_lt this

theorem _root_.LinearMap.IsSymmetric.rePow_eq_rankOne {𝕜 E : Type _} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (r : ℝ) :
    LinearMap.rePow T hT r =
      ∑ i,
        ((hT.eigenvalues rfl i ^ r : ℝ) : 𝕜) •
          (_root_.rankOne 𝕜 (hT.eigenvectorBasis rfl i) (hT.eigenvectorBasis rfl i)) := by
  simp_rw [LinearMap.ext_iff, LinearMap.rePow_apply,
    ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
    LinearMap.sum_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe]
  intros
  rfl

theorem _root_.LinearMap.IsSymmetric.invertible (hT : T.IsSymmetric) [Invertible T] :
    (⅟ T).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, isSelfAdjoint_iff] at hT ⊢
  simp only [star_invOf, hT]

theorem _root_.LinearMap.isPositive'_and_invertible_pos_eigenvalues
    (hT : T.IsPositive') [Invertible T]
    (i : Fin (Module.finrank 𝕜 E)) : 0 < hT.1.eigenvalues rfl i := by
  have fs : Function.Bijective ⇑T := by
    rw [Function.bijective_iff_has_inverse]
    use⇑(⅟ T)
    simp_rw [Function.RightInverse, Function.LeftInverse, ← Module.End.mul_apply, invOf_mul_self,
      mul_invOf_self, one_apply, and_self_iff, forall_const]
  obtain ⟨v, hv, gh⟩ :=
    Module.End.has_eigenvector_iff_hasEigenvalue.mpr
      (@LinearMap.IsSymmetric.hasEigenvalue_eigenvalues 𝕜 _ E _ _ T _ _ hT.1 rfl i)
  have ugh := (LinearMap.invertibleIff_inner_map_self_pos T hT).mp fs v gh
  rw [hv, inner_smul_real_left, inner_self_eq_norm_sq_to_K, ← ofReal_pow, real_smul_ofReal,
    ← ofReal_mul, zero_lt_real, mul_pos_iff] at ugh
  simp_rw [not_lt_of_ge (sq_nonneg _), and_false, or_false] at ugh
  exact ugh.1

/-- Invertibility of real powers of a positive invertible linear map. -/
@[reducible]
noncomputable def _root_.LinearMap.IsPositive'.rePowIsInvertible (hT : T.IsPositive') [Invertible T]
    (r : ℝ) : Invertible (T.rePow hT.1 r) := by
  apply Invertible.mk (T.rePow hT.1 (-r)) <;> ext1 <;>
      simp_rw [Module.End.mul_apply, LinearMap.rePow_apply, inner_sum, inner_smul_right,
        orthonormal_iff_ite.mp (hT.1.eigenvectorBasis rfl).orthonormal, mul_boole, mul_ite,
        MulZeroClass.mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_smul, ← mul_assoc,
        ← RCLike.ofReal_mul, ←
        Real.rpow_add (LinearMap.isPositive'_and_invertible_pos_eigenvalues _ hT _),
        Module.End.one_apply] <;>
    simp only [add_neg_cancel, neg_add_cancel, Real.rpow_zero, RCLike.ofReal_one, one_mul, ←
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr]

theorem _root_.LinearMap.IsPositive'.sum {𝕜 E : Type _} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}
    {T : Fin n → E →ₗ[𝕜] E} (hT : ∀ i, (T i).IsPositive') :
    (∑ i, T i).IsPositive' := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, LinearMap.IsPositive'Zero]
  | succ d hd =>
    simp_rw [Fin.sum_univ_castSucc]
    apply LinearMap.IsPositive'.add
    · apply hd
      intro i
      exact hT _
    · exact hT _

theorem _root_.LinearMap.IsPositive'.smulNonneg {𝕜 E : Type _} [RCLike 𝕜]
    [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsPositive') {r : ℝ} (hr : 0 ≤ r) :
    ((r : 𝕜) • T).IsPositive' := by
  simp_rw [LinearMap.IsPositive', LinearMap.IsSymmetric, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, hT.1 _ _, forall₂_true_iff, true_and]
  rw [← @zero_le_real 𝕜] at hr
  simp_rw [mul_nonneg hr (hT.2 _), forall_true_iff]
theorem _root_.LinearMap.IsPositive'.smulNNReal {𝕜 E : Type _} [RCLike 𝕜]
    [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsPositive') (r : NNReal) :
    (((r : ℝ) : 𝕜) • T).IsPositive' :=
hT.smulNonneg r.2

end FiniteDimensional

end LinearMap

theorem rankOne_self_isPositive {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {x : E} :
  (_root_.rankOne 𝕜 x x).IsPositive := by
  refine ⟨rankOne_self_isSymmetric, ?_⟩
  intro y
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, _root_.rankOne_apply, inner_smul_left,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  exact sq_nonneg _

theorem LinearMap.IsPositive'.nonneg_eigenvalue {E : Type _} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsPositive') {α : ℝ}
    (hα : Module.End.HasEigenvalue T α) : 0 ≤ α := by
  have this := ((spec_subseteq_nonneg _).mp (LinearMap.IsPositive'.nonneg_spectrum T hT)) α
    (Module.End.hasEigenvalue_iff_mem_spectrum.mp hα)
  rw [zero_le_real] at this
  exact this

open scoped BigOperators

theorem LinearMap.isPositive'_iff_eq_sum_rankOne [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) :
    T.IsPositive' ↔
      ∃ (m : ℕ) (u : Fin m → E),
        T = ∑ i : Fin m, ((_root_.rankOne 𝕜 (u i) (u i)) : E →ₗ[𝕜] E) := by
  constructor
  · intro hT
    let a : Fin (Module.finrank 𝕜 E) → E := fun i =>
      (Real.sqrt (hT.1.eigenvalues rfl i) : 𝕜) • hT.1.eigenvectorBasis rfl i
    refine ⟨Module.finrank 𝕜 E, a, ?_⟩
    ext1
    simp_rw [LinearMap.sum_apply, ContinuousLinearMap.coe_coe, _root_.rankOne_apply, a,
      inner_smul_left,
      smul_smul, mul_assoc, RCLike.conj_ofReal, mul_comm (⟪_, _⟫_𝕜),
      ← mul_assoc, ← RCLike.ofReal_mul, ←
      Real.sqrt_mul (hT.nonneg_eigenvalue (hT.1.hasEigenvalue_eigenvalues rfl _)),
      Real.sqrt_mul_self (hT.nonneg_eigenvalue (hT.1.hasEigenvalue_eigenvalues rfl _)),
      mul_comm _ (inner _ _ _), ← smul_eq_mul, smul_assoc, ← hT.1.apply_eigenvectorBasis, ←
      LinearMap.map_smul, ← map_sum, ← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr]
  · rintro ⟨m, u, hu⟩
    simp_rw [LinearMap.IsPositive', LinearMap.IsSymmetric, hu, LinearMap.sum_apply,
      ContinuousLinearMap.coe_coe, _root_.rankOne_apply, inner_sum, sum_inner, inner_smul_left,
      inner_smul_right, inner_conj_symm, mul_comm, forall₂_true_iff, true_and,
      ← inner_conj_symm _ (u _), RCLike.conj_mul, ← RCLike.ofReal_pow,
      ← ofReal_sum, zero_le_real]
    exact fun _ => Finset.sum_nonneg' (fun _ => sq_nonneg _)

theorem LinearMap.IsSymmetric.rePowIsPositive'OfIsPositive' {𝕜 E : Type _} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsPositive') (r : ℝ) :
    (T.rePow hT.1 r).IsPositive' := by
  haveI := FiniteDimensional.complete 𝕜 E
  simp_rw [LinearMap.IsSymmetric.rePow_eq_rankOne, ContinuousLinearMap.toLinearMap_sum]
  apply LinearMap.IsPositive'.sum
  intro i
  apply LinearMap.IsPositive'.smulNonneg
  · rw [← ContinuousLinearMap.IsPositive.toLinearMap']
    exact rankOne_self_isPositive
  · apply Real.rpow_nonneg
    exact hT.nonneg_eigenvalue (hT.1.hasEigenvalue_eigenvalues rfl _)
