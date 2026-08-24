/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 20915-21166.
Modifications: extracted the normal-fixed and orthogonal representations and
changed carrier names and namespace for Zhou §4. See the upstream PORT_MAP.md.
-/
import LeanPool.ConnesRigidity.Core

/-!
The normal fixed component of the Connes rigidity formalization.
-/

namespace Connes

universe u v

noncomputable section

variable {G : Type u} [Group G]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Vectors fixed by a subgroup under a unitary representation. Paper: §4. -/
def normalFixedSubmodule (N : Subgroup G)
    (π : UnitaryRepresentation G K) : Submodule ℂ K where
  carrier := {x : K | ∀ n : N, (π (n : G) : K →L[ℂ] K) x = x}
  zero_mem' n := map_zero (π (n : G) : K →L[ℂ] K)
  add_mem' hx hy n := by
    rw [map_add, hx n, hy n]
  smul_mem' c x hx n := by
    rw [map_smul, hx n]

@[simp] theorem mem_normalFixedSubmodule
    (N : Subgroup G) (π : UnitaryRepresentation G K) (x : K) :
    x ∈ normalFixedSubmodule N π ↔
      ∀ n : N, (π (n : G) : K →L[ℂ] K) x = x := Iff.rfl

/-- The fixed subspace is closed, hence complete. Paper: §4. -/
theorem normalFixedSubmodule_isClosed
    (N : Subgroup G) (π : UnitaryRepresentation G K) :
    IsClosed (normalFixedSubmodule N π : Set K) := by
  have hset : (normalFixedSubmodule N π : Set K) =
      ⋂ n : N, {x : K | (π (n : G) : K →L[ℂ] K) x = x} := by
    ext x
    simp only [SetLike.mem_coe, mem_normalFixedSubmodule, Subtype.forall,
      Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun n =>
    isClosed_eq (π (n : G) : K →L[ℂ] K).continuous continuous_id

instance normalFixedSubmodule_completeSpace
    (N : Subgroup G) (π : UnitaryRepresentation G K) :
    CompleteSpace (normalFixedSubmodule N π) :=
  (normalFixedSubmodule_isClosed N π).isComplete.completeSpace_coe

section Normality

variable (N : Subgroup G) [N.Normal] (π : UnitaryRepresentation G K)

/-- Normality makes the fixed subspace invariant. Paper: §4. -/
theorem unitary_mem_normalFixedSubmodule
    (g : G) {x : K} (hx : x ∈ normalFixedSubmodule N π) :
    (π g : K →L[ℂ] K) x ∈ normalFixedSubmodule N π := by
  intro n
  let n' : N :=
    ⟨g⁻¹ * (n : G) * g,
      by simpa only [inv_inv] using
        (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹⟩
  calc
    (π (n : G) : K →L[ℂ] K) ((π g : K →L[ℂ] K) x) =
        (π ((n : G) * g) : K →L[ℂ] K) x := by
          rw [map_mul]
          rfl
    _ = (π (g * (n' : G)) : K →L[ℂ] K) x := by
      have heq : (n : G) * g = g * (g⁻¹ * (n : G) * g) := by
        group
      change (π ((n : G) * g) : K →L[ℂ] K) x =
        (π (g * (g⁻¹ * (n : G) * g)) : K →L[ℂ] K) x
      rw [heq]
    _ = (π g : K →L[ℂ] K)
          ((π (n' : G) : K →L[ℂ] K) x) := by
      rw [map_mul]
      rfl
    _ = (π g : K →L[ℂ] K) x := by rw [hx n']

/-- The orthogonal complement is invariant as well. Paper: §4. -/
theorem unitary_mem_normalFixedSubmodule_orthogonal
    (g : G) {x : K} (hx : x ∈ (normalFixedSubmodule N π)ᗮ) :
    (π g : K →L[ℂ] K) x ∈ (normalFixedSubmodule N π)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hy' := unitary_mem_normalFixedSubmodule N π g⁻¹ hy
  have hinner := (Submodule.mem_orthogonal _ _).mp hx
    ((π g⁻¹ : K →L[ℂ] K) y) hy'
  calc
    @inner ℂ K _ y ((π g : K →L[ℂ] K) x) =
        @inner ℂ K _
          ((π g : K →L[ℂ] K)
            ((π g⁻¹ : K →L[ℂ] K) y))
          ((π g : K →L[ℂ] K) x) := by
      congr 1
      change y = (↑(π g * π g⁻¹) : K →L[ℂ] K) y
      rw [← map_mul]
      simp only [mul_inv_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
    _ = @inner ℂ K _
          ((π g⁻¹ : K →L[ℂ] K) y) x :=
      Unitary.inner_map_map (π g)
        ((π g⁻¹ : K →L[ℂ] K) y) x
    _ = 0 := hinner

/--
The `normalFixedLinearIsometryEquiv` construction used in the Connes rigidity formalization.
-/
def normalFixedLinearIsometryEquiv (g : G) :
    normalFixedSubmodule N π ≃ₗᵢ[ℂ] normalFixedSubmodule N π where
  toFun x :=
    ⟨(π g : K →L[ℂ] K) x,
      unitary_mem_normalFixedSubmodule N π g x.property⟩
  invFun x :=
    ⟨(π g⁻¹ : K →L[ℂ] K) x,
      unitary_mem_normalFixedSubmodule N π g⁻¹ x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (↑(π g⁻¹ * π g) : K →L[ℂ] K) x = x
    rw [← map_mul]
    simp only [inv_mul_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
  right_inv x := by
    apply Subtype.ext
    change (↑(π g * π g⁻¹) : K →L[ℂ] K) x = x
    rw [← map_mul]
    simp only [mul_inv_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
  map_add' x y := Subtype.ext
    (map_add (π g : K →L[ℂ] K) (x : K) (y : K))
  map_smul' c x := Subtype.ext
    (map_smul (π g : K →L[ℂ] K) c (x : K))
  norm_map' x := Unitary.norm_map (π g) (x : K)

/-- The restricted representation on the fixed subspace. Paper: §4. -/
def normalFixedRepresentation :
    UnitaryRepresentation G (normalFixedSubmodule N π) where
  toFun g := Unitary.linearIsometryEquiv.symm
    (normalFixedLinearIsometryEquiv N π g)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (π 1 : K →L[ℂ] K) (x : K) = x
    simp only [map_one, OneMemClass.coe_one, one_apply_eq_self]
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (π (g * h) : K →L[ℂ] K) (x : K) =
      (π g : K →L[ℂ] K) ((π h : K →L[ℂ] K) (x : K))
    rw [map_mul]
    rfl

@[simp] theorem normalFixedRepresentation_apply
    (g : G) (x : normalFixedSubmodule N π) :
    ((normalFixedRepresentation N π g :
      normalFixedSubmodule N π →L[ℂ] normalFixedSubmodule N π) x : K) =
      (π g : K →L[ℂ] K) (x : K) := rfl

theorem normalFixedRepresentation_apply_eq_one
    (n : G) (hn : n ∈ N) : normalFixedRepresentation N π n = 1 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change (π n : K →L[ℂ] K) (x : K) = x
  exact x.property ⟨n, hn⟩

/-- The quotient representation on the normal-fixed subspace. Paper: §4. -/
def normalFixedQuotientRepresentation :
    UnitaryRepresentation (G ⧸ N) (normalFixedSubmodule N π) :=
  QuotientGroup.lift N (normalFixedRepresentation N π)
    (fun n hn => normalFixedRepresentation_apply_eq_one N π n hn)

theorem normalFixedQuotientRepresentation_apply_mk
    (g : G) (x : normalFixedSubmodule N π) :
    ((normalFixedQuotientRepresentation N π (QuotientGroup.mk' N g) :
      normalFixedSubmodule N π →L[ℂ] normalFixedSubmodule N π) x : K) =
      (π g : K →L[ℂ] K) (x : K) := rfl

/--
The `normalFixedOrthogonalLinearIsometryEquiv` construction used in the
Connes rigidity formalization.
-/
def normalFixedOrthogonalLinearIsometryEquiv (g : G) :
    (normalFixedSubmodule N π)ᗮ ≃ₗᵢ[ℂ]
      (normalFixedSubmodule N π)ᗮ where
  toFun x :=
    ⟨(π g : K →L[ℂ] K) x,
      unitary_mem_normalFixedSubmodule_orthogonal N π g x.property⟩
  invFun x :=
    ⟨(π g⁻¹ : K →L[ℂ] K) x,
      unitary_mem_normalFixedSubmodule_orthogonal N π g⁻¹ x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (↑(π g⁻¹ * π g) : K →L[ℂ] K) x = x
    rw [← map_mul]
    simp only [inv_mul_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
  right_inv x := by
    apply Subtype.ext
    change (↑(π g * π g⁻¹) : K →L[ℂ] K) x = x
    rw [← map_mul]
    simp only [mul_inv_cancel, map_one, OneMemClass.coe_one, one_apply_eq_self]
  map_add' x y := Subtype.ext
    (map_add (π g : K →L[ℂ] K) (x : K) (y : K))
  map_smul' c x := Subtype.ext
    (map_smul (π g : K →L[ℂ] K) c (x : K))
  norm_map' x := Unitary.norm_map (π g) (x : K)

/-- The restricted representation on the orthogonal complement. Paper: §4. -/
def normalFixedOrthogonalRepresentation :
    UnitaryRepresentation G ((normalFixedSubmodule N π)ᗮ) where
  toFun g := Unitary.linearIsometryEquiv.symm
    (normalFixedOrthogonalLinearIsometryEquiv N π g)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (π 1 : K →L[ℂ] K) (x : K) = x
    simp only [map_one, OneMemClass.coe_one, one_apply_eq_self]
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (π (g * h) : K →L[ℂ] K) (x : K) =
      (π g : K →L[ℂ] K) ((π h : K →L[ℂ] K) (x : K))
    rw [map_mul]
    rfl

@[simp] theorem normalFixedOrthogonalRepresentation_apply
    (g : G) (x : (normalFixedSubmodule N π)ᗮ) :
    ((normalFixedOrthogonalRepresentation N π g :
      (normalFixedSubmodule N π)ᗮ →L[ℂ]
        (normalFixedSubmodule N π)ᗮ) x : K) =
      (π g : K →L[ℂ] K) (x : K) := rfl

theorem normalFixedOrthogonalRepresentation_no_fixed
    (x : (normalFixedSubmodule N π)ᗮ)
    (hx : ∀ n : N,
      (normalFixedOrthogonalRepresentation N π (n : G) :
        (normalFixedSubmodule N π)ᗮ →L[ℂ]
          (normalFixedSubmodule N π)ᗮ) x = x) : x = 0 := by
  have hfixed : (x : K) ∈ normalFixedSubmodule N π := by
    intro n
    exact congrArg Subtype.val (hx n)
  have hinner : @inner ℂ K _ (x : K) (x : K) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hfixed x.property
  apply Subtype.ext
  exact inner_self_eq_zero.mp hinner

/-- The normal fixed projection commutes with the representation. Paper: §4. -/
theorem normalFixed_starProjection_commute
    (g : G) (x : K) :
    (normalFixedSubmodule N π).starProjection
        ((π g : K →L[ℂ] K) x) =
      (π g : K →L[ℂ] K)
        ((normalFixedSubmodule N π).starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact unitary_mem_normalFixedSubmodule N π g
      (Submodule.starProjection_apply_mem
        (normalFixedSubmodule N π) x)
  · rw [← map_sub]
    exact unitary_mem_normalFixedSubmodule_orthogonal N π g
      (Submodule.sub_starProjection_mem_orthogonal x)

/-- Passing to the orthogonal residual cannot increase displacement. Paper: §4. -/
theorem normalFixed_orthogonalResidual_displacement_le
    (g : G) (x : K) :
    ‖(π g : K →L[ℂ] K)
          (x - (normalFixedSubmodule N π).starProjection x) -
        (x - (normalFixedSubmodule N π).starProjection x)‖ ≤
      ‖(π g : K →L[ℂ] K) x - x‖ := by
  calc
    ‖(π g : K →L[ℂ] K)
          (x - (normalFixedSubmodule N π).starProjection x) -
        (x - (normalFixedSubmodule N π).starProjection x)‖ =
        ‖((π g : K →L[ℂ] K) x - x) -
          ((π g : K →L[ℂ] K)
            ((normalFixedSubmodule N π).starProjection x) -
              (normalFixedSubmodule N π).starProjection x)‖ := by
      rw [map_sub]
      congr 1
      abel
    _ = ‖((π g : K →L[ℂ] K) x - x) -
          (normalFixedSubmodule N π).starProjection
            ((π g : K →L[ℂ] K) x - x)‖ := by
      rw [map_sub, normalFixed_starProjection_commute]
    _ = ‖(normalFixedSubmodule N π)ᗮ.starProjection
          ((π g : K →L[ℂ] K) x - x)‖ := by
      rw [Submodule.starProjection_orthogonal_val]
    _ ≤ ‖(π g : K →L[ℂ] K) x - x‖ :=
      (normalFixedSubmodule N π)ᗮ.norm_starProjection_apply_le _

end Normality
end
end Connes
