/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import LeanPool.Polytopes.Pre

/-!
Halfspaces in inner product spaces and their basic geometric operations.
-/

open Pointwise


/-- A halfspace of `E`. For convenience it is described by a continuous linear functional of
norm `1` together with a real number bound. -/
structure Halfspace (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The bounding functional, of norm `1`. -/
  f : {f : (StrongDual ℝ E) // norm f = 1}
  /-- The real bound defining the halfspace. -/
  α : ℝ

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable instance NegUnitSphereDual :
  Neg {f : (StrongDual ℝ E) // norm f = 1} :=
  ⟨fun f => ⟨-f.1, by simp [f.2]⟩⟩

lemma unitSphereDual_neg :
  ∀ f : {f : (StrongDual ℝ E) // norm f = 1}, (-f).1 = -f.1 := fun f => by
  change (⟨-f.1, _ ⟩: {f : (StrongDual ℝ E) // norm f = 1}).1 = -f.1
  simp

lemma unitSphereDual_surj : ∀ f : {f : (StrongDual ℝ E) // norm f = 1},
  Function.Surjective f.val := by
  intro f
  apply LinearMap.surjective_of_ne_zero
  intro h
  rw [← ContinuousLinearMap.toLinearMap_zero, ContinuousLinearMap.coe_inj] at h
  have := h ▸ f.2
  simp only [norm_zero, zero_ne_one] at this

/-- The underlying set of points of a halfspace `H_`. -/
def Halfspace.S (H_ : Halfspace E) : Set E := H_.f.1 ⁻¹' {x | x ≤ H_.α}

variable [CompleteSpace E]

instance Halfspace.SetLike : SetLike (Halfspace E) E where
  coe := Halfspace.S
  coe_injective := by
    intro H1 H2 h
    obtain ⟨f1, α1⟩ := H1
    obtain ⟨f2, α2⟩ := H2
    simp only [Halfspace.S] at h
    let p1 := (InnerProductSpace.toDual ℝ E).symm f1.1
    have hp1norm : norm p1 = 1 :=
      (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _).symm f1.1) ▸ f1.2
    have hf1 : f1.1 = (InnerProductSpace.toDual ℝ E) p1 :=
      (LinearIsometryEquiv.apply_symm_apply (InnerProductSpace.toDual ℝ E) _).symm
    have hf1p1 : f1.1 p1 = 1 := by
      rw [hf1, InnerProductSpace.toDual_apply_apply, real_inner_self_eq_norm_sq, hp1norm, sq,
        one_mul]
    have hfeq : f1 = f2 := by
      rw [Subtype.ext_iff]
      refine LinearIsometryEquiv.injective (InnerProductSpace.toDual ℝ E).symm ?_
      contrapose! h
      let p2 := (InnerProductSpace.toDual ℝ E).symm f2.1
      have hp2norm : norm p2 = 1 :=
        (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _).symm f2.1) ▸ f2.2
      have hf2 : f2.1 = (InnerProductSpace.toDual ℝ E) p2 :=
        (LinearIsometryEquiv.apply_symm_apply (InnerProductSpace.toDual ℝ E) _).symm
      change p1 ≠ p2 at h
      have hinnerlt1 := (inner_lt_one_iff_real_of_norm_eq_one hp1norm hp2norm).mpr h
      let v := p1 - p2
      let v' := (norm v)⁻¹ • v
      have hDiffNormPos : 0 < ‖p1 - p2‖⁻¹ := inv_pos.mpr <| norm_pos_iff.mpr <| sub_ne_zero_of_ne h
      have hv'1 : 0 < f1.1 v' := by
        rw [hf1, InnerProductSpace.toDual_apply_apply, real_inner_smul_right, inner_sub_right,
          real_inner_self_eq_norm_sq, hp1norm, sq, one_mul, mul_pos_iff]
        left
        exact ⟨ hDiffNormPos, by linarith ⟩
      have hv'2 : f2.1 v' < 0 := by
        rw [hf2, InnerProductSpace.toDual_apply_apply, real_inner_smul_right, inner_sub_right,
          real_inner_self_eq_norm_sq, hp2norm, sq, one_mul, mul_neg_iff]
        left
        exact ⟨ hDiffNormPos, sub_neg.mpr ((real_inner_comm p1 p2) ▸ hinnerlt1) ⟩
      have hv'1out : ∃ M1 : ℝ, ∀ m > M1, (m • v') ∉ f1.1 ⁻¹' {x | x ≤ α1} := by
        use α1 / f1.1 v'
        intro m hm hmem
        rw [Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul,
          ← le_div_iff₀ hv'1] at hmem
        exact not_lt_of_ge hmem hm
      have hv'2in : ∃ M2 : ℝ, ∀ m > M2, (m • v') ∈ f2.1 ⁻¹' {x | x ≤ α2} := by
        use α2 / f2.1 v'
        intro m hm
        rw [Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul]
        have : m * f2.1 v' ≤ α2 / f2.1 v' * f2.1 v' := by
          rw [← neg_le_neg_iff, ← mul_neg, ← mul_neg,
            mul_le_mul_iff_of_pos_right (neg_pos_of_neg hv'2)]
          exact le_of_lt hm
        apply le_trans this
        rw [div_mul_cancel₀ _ (ne_of_lt hv'2)]
      rcases hv'1out with ⟨ M1, hM1 ⟩
      rcases hv'2in with ⟨ M2, hM2 ⟩
      have : M1 < 1 + max M1 M2 := by
        have := le_max_left M1 M2
        linarith
      have : M2 < 1 + max M1 M2 := by
        have := le_max_right M1 M2
        linarith
      rw [← Set.symmDiff_nonempty, Set.nonempty_def]
      use (1 + max M1 M2) • v'
      rw [Set.mem_symmDiff]
      right
      exact ⟨ hM2 (1 + max M1 M2) (by assumption), hM1 (1 + max M1 M2) (by assumption) ⟩
    congr
    contrapose! h
    rw [← Set.symmDiff_nonempty, Set.nonempty_def]
    use (max α1 α2) • p1
    rw [Set.mem_symmDiff]
    rcases (max_choice α1 α2) with hmax1 | hmax2
    · left
      rw [hmax1, Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul,
        Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul, ← hfeq, hf1p1,
        mul_one]
      rw [max_eq_left_iff] at hmax1
      exact ⟨ le_refl _, not_le_of_gt <| lt_of_le_of_ne hmax1 h.symm ⟩
    · right
      rw [hmax2, Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul,
        Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul, ← hfeq, hf1p1,
        mul_one]
      rw [max_eq_right_iff] at hmax2
      exact ⟨ le_refl _, not_le_of_gt <| lt_of_le_of_ne hmax2 h ⟩

/-- The coercion of a halfspace to a set equals the sublevel preimage of its functional. -/
lemma Halfspace.h (H_ : Halfspace E) : ↑H_ = H_.f.1 ⁻¹' {x | x ≤ H_.α} := rfl

lemma Halfspace_mem (H_ : Halfspace E) : ∀ x, x ∈ (SetLike.coe H_) ↔ H_.f.1 x ≤ H_.α := by
  intro x
  rw [H_.h]
  rfl

lemma Halfspace_convex (H_ : Halfspace E) : Convex ℝ (SetLike.coe H_) := by
  rw [H_.h]
  exact convex_halfSpace_le (LinearMap.isLinear H_.f.1.1) H_.α

lemma Halfspace_closed (H_ : Halfspace E) : IsClosed (SetLike.coe H_) := by
  rw [H_.h]
  exact IsClosed.preimage (H_.f.1.cont) isClosed_Iic

lemma Halfspace_span (H_ : Halfspace E) : affineSpan ℝ (SetLike.coe H_) = ⊤ := by
  -- affine span of a ball(simplex, in general) is entire
  apply affineSpan_eq_top_of_nonempty_interior
  apply Set.Nonempty.mono
    (?_ : H_.f.1 ⁻¹' (Metric.ball (H_.α - 1) (1 / 2)) ⊆ (interior ((convexHull ℝ) H_.S)))
  · -- preimage of ball is not empty as f is surjective
    obtain ⟨x, hx⟩ := unitSphereDual_surj H_.f (H_.α - 1)
    use x
    rw [Set.mem_preimage, Metric.mem_ball, dist_sub_eq_dist_add_right, hx, sub_add_cancel,
      dist_self]
    linarith
  -- this open set is subset of the halfspace
  have hopen : IsOpen (H_.f.1 ⁻¹' Metric.ball (H_.α - 1) (1 / 2)) :=
    IsOpen.preimage H_.f.1.cont Metric.isOpen_ball
  rw [IsOpen.subset_interior_iff hopen]
  apply subset_trans ?_ (subset_convexHull ℝ (SetLike.coe H_))
  intro x hx
  rw [Set.mem_preimage, Real.ball_eq_Ioo, Set.mem_Ioo] at hx
  rw [Halfspace_mem H_]
  linarith

/-- The halfspace `H_` translated by the vector `x`. -/
noncomputable def halfspaceTranslation (x : E) (H_ : Halfspace E) : Halfspace E :=
  Halfspace.mk H_.f (H_.α + (H_.f.1 x))

lemma halfspaceTranslation.S (x : E) (H_ : Halfspace E) :
  ↑(halfspaceTranslation x H_) = (· + x) '' ↑H_ := by
  ext y
  rw [halfspaceTranslation, Halfspace_mem, Set.image_add_right, Set.mem_preimage, ← sub_eq_add_neg,
    Halfspace_mem, ContinuousLinearMap.map_sub, sub_le_iff_le_add]

lemma mem_halfspaceTranslation (x : E) (H_ : Halfspace E) :
  ∀ y, y ∈ (SetLike.coe <| halfspaceTranslation x H_) ↔ y - x ∈ SetLike.coe H_ := by
  intro y
  rw [halfspaceTranslation.S, Set.image_add_right, Set.mem_preimage, sub_eq_add_neg]

lemma halfspaceTranslation.injective (x : E) :
  Function.Injective (halfspaceTranslation x · : Halfspace E → Halfspace E ) := by
  intro H1 H2 h
  rw [SetLike.ext_iff]
  intro y
  rw [SetLike.ext_iff] at h
  specialize h (y + x)
  rwa [← SetLike.mem_coe, ← SetLike.mem_coe, mem_halfspaceTranslation, mem_halfspaceTranslation,
    add_sub_cancel_right] at h

lemma frontierHalfspace_Hyperplane {Hi_ : Halfspace E} :
  frontier Hi_ = {x : E | Hi_.f.1 x = Hi_.α } := by
  have := ContinuousLinearMap.frontier_preimage Hi_.f.1 (unitSphereDual_surj Hi_.f) (Set.Iic Hi_.α)
  simp only [Set.nonempty_Ioi, frontier_Iic'] at this
  change frontier ( Hi_.f.1 ⁻¹' {x | x ≤ Hi_.α}) = Hi_.f.1 ⁻¹' {Hi_.α} at this
  rw [Hi_.h, this]; clear this
  unfold Set.preimage
  simp only [Set.mem_singleton_iff]

omit [CompleteSpace E] in
lemma Hyperplane_convex (Hi_ : Halfspace E) :
  Convex ℝ {x : E | Hi_.f.1 x = Hi_.α } :=
  convex_hyperplane (LinearMap.isLinear Hi_.f.1.1) Hi_.α

omit [CompleteSpace E] in
lemma Hyperplane_affineClosed (Hi_ : Halfspace E) :
  ∀ s : Fin n → E, Set.range s ⊆ {x : E | Hi_.f.1 x = Hi_.α }
    → ∀ a : Fin n → ℝ, Finset.univ.sum a = 1 →
    Finset.affineCombination ℝ Finset.univ s a ∈ {x : E | Hi_.f.1 x = Hi_.α } := by
  intro s hs a ha
  rw [Finset.affineCombination_eq_linear_combination _ _ _ ha, Set.mem_setOf, map_sum]
  have hg : (fun i => Hi_.f.1 (a i • s i)) = fun i => a i * Hi_.α := by
    ext i
    rw [Set.range_subset_iff] at hs
    specialize hs i
    rw [Set.mem_setOf] at hs
    rw [ContinuousLinearMap.map_smulₛₗ, smul_eq_mul, RingHom.id_apply, hs]
  rw [hg, ←Finset.sum_mul, ha, one_mul]

omit [CompleteSpace E] in
lemma Halfspace.val_raw (p : Subspace ℝ E) [CompleteSpace p] (H_' : Halfspace p) :
  ∃ H_ : Halfspace E, ((∀ (x : { x // x ∈ p }), H_.f.1 x = H_'.f.1 x) ∧ ‖H_.f.1‖ = ‖H_'.f.1‖) ∧
    H_.α = H_'.α := by
  rcases H_' with ⟨ ⟨ f, hf ⟩, C ⟩
  choose g hg using exists_extension_norm_eq p f
  exact ⟨ ⟨ ⟨ g, hg.2 ▸ hf ⟩, C ⟩, hg, rfl ⟩

/-- A halfspace of the subspace `p` extended to a halfspace of the whole space `E`. -/
noncomputable def Halfspace.val (p : Subspace ℝ E) [CompleteSpace p] (H_' : Halfspace p) :
  Halfspace E := by
  choose H_ _ using (Halfspace.val_raw p H_')
  exact H_

omit [CompleteSpace E] in
lemma Halfspace.val_f (p : Subspace ℝ E) [CompleteSpace p] (H_' : Halfspace p) :
  ∀ (x : { x // x ∈ p }), (Halfspace.val p H_').f.1 x = H_'.f.1 x := by
  unfold val
  exact (Classical.choose_spec (Halfspace.val_raw p H_')).1.1

omit [CompleteSpace E] in
lemma Halfspace.val_C (p : Subspace ℝ E) [CompleteSpace p] (H_' : Halfspace p) :
  (Halfspace.val p H_').α = H_'.α := by
  unfold val
  exact (Classical.choose_spec (Halfspace.val_raw p H_')).2

lemma Halfspace.val_eq (p : Subspace ℝ E) [CompleteSpace p] (H_' : Halfspace p) :
  (Halfspace.val p H_' : Set E) ∩ ↑p = (Subtype.val '' (H_' : Set p)) := by
  have := Halfspace.val_f p H_'
  apply subset_antisymm <;> intro x <;> rw [Set.mem_inter_iff, Set.mem_image]
  · rintro ⟨ hxH_', hxp ⟩
    refine ⟨ ⟨ x, hxp ⟩, ?_, rfl ⟩
    rwa [Halfspace_mem, ← (this ⟨ x, hxp ⟩), ← Halfspace.val_C p H_']
  · rintro ⟨ ⟨ x', hx'p ⟩, hx'H_', rfl ⟩
    refine ⟨ ?_, hx'p ⟩
    rw [Halfspace_mem, ← (this ⟨ x', hx'p ⟩), ← Halfspace.val_C p H_'] at hx'H_'
    exact hx'H_'

lemma Halfspace.val_eq' (p : Subspace ℝ E) [CompleteSpace p] : ∀ (H_' : Halfspace p),
  (fun H_ => (Halfspace.val p H_ : Set E) ∩ ↑p) H_' =
    (fun H_ => (@Subtype.val E fun x => x ∈ p) '' (H_ : Set p)) (SetLike.coe H_') := by
  intro H_'
  have := Halfspace.val_f p H_'
  apply subset_antisymm <;> intro x <;> rw [Set.mem_inter_iff, Set.mem_image]
  · rintro ⟨ hxH_', hxp ⟩
    refine ⟨ ⟨ x, hxp ⟩, ?_, rfl ⟩
    rwa [Halfspace_mem, ← (this ⟨ x, hxp ⟩), ← Halfspace.val_C p H_']
  · rintro ⟨ ⟨ x', hx'p ⟩, hx'H_', rfl ⟩
    refine ⟨ ?_, hx'p ⟩
    rw [Halfspace_mem, ← (this ⟨ x', hx'p ⟩), ← Halfspace.val_C p H_'] at hx'H_'
    exact hx'H_'
