/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import LeanPool.Polytopes.Halfspace
import Mathlib.Analysis.Convex.KreinMilman

/-!
Polar duals and their compactness properties.
-/

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The unit dual functional in the direction of a nonzero vector `p`. -/
noncomputable def pointDualLin (p : {p : E // p ≠ 0}) :
  {f : (StrongDual ℝ E) // norm f = 1} :=
  ⟨ (InnerProductSpace.toDual ℝ _ ((norm p.1)⁻¹ • p.1)), (by
  simp only [ne_eq, map_smulₛₗ, map_inv₀, RCLike.conj_to_real]
  have : norm ((InnerProductSpace.toDual ℝ E) ↑p) = norm p.1 := by simp
  rw [← this]
  refine norm_smul_inv_norm ?_
  simpa only [ne_eq, AddEquivClass.map_eq_zero_iff] using p.2
  ) ⟩

/-- Given a nonzero vector `p`, the halfspace `{x | inner p x ≤ 1}`. -/
noncomputable def pointDual (p : {p : E // p ≠ 0}) : Halfspace E :=
  Halfspace.mk (pointDualLin p) (norm p.1)⁻¹

lemma pointDual.α (p : {p : E // p ≠ 0}) :
  (pointDual p).α = (norm p.1)⁻¹ := by rfl

lemma pointDual.h (p : {p : E // p ≠ 0}) :
  (pointDual p) =
    (InnerProductSpace.toDual ℝ _ ((norm p.1)⁻¹ • p.1)) ⁻¹' {x | x ≤ (norm p.1)⁻¹} := by rfl

lemma pointDual_origin (p : {p : E // p ≠ 0}) :
  (0 : E) ∈ (SetLike.coe <| pointDual p) := by
  rw [pointDual.h, map_smulₛₗ, map_inv₀, RCLike.conj_to_real, Set.preimage_setOf_eq,
    Set.mem_setOf_eq, map_zero, ← one_div]
  apply le_of_lt
  rw [div_pos_iff]
  left
  exact ⟨ zero_lt_one, by rw [norm_pos_iff]; exact p.2 ⟩

lemma mem_pointDual (p : {p : E // p ≠ 0}) (x : E) :
  x ∈ (SetLike.coe <| pointDual p) ↔ inner ℝ p.1 x ≤ (1:ℝ) := by
  rw [pointDual.h, Set.mem_preimage, InnerProductSpace.toDual_apply_apply, Set.mem_setOf,
    inner_smul_left, RCLike.conj_to_real,
    ← mul_le_mul_iff_of_pos_left (by rw [norm_pos_iff]; exact p.2 : 0 < norm p.1),
    ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr p.2), one_mul]

lemma pointDual_comm (p q : {p : E // p ≠ 0}) :
  p.1 ∈ (SetLike.coe <| pointDual q) ↔ q.1 ∈ (SetLike.coe <| pointDual p) := by
  rw [mem_pointDual, mem_pointDual, real_inner_comm]


/-- The polar dual of a set `X`: `{v | ∀ x ∈ X, inner x v ≤ 1}`. -/
noncomputable def polarDual (X : Set E) : Set E :=
  ⋂₀ (SetLike.coe '' (pointDual '' (Subtype.val ⁻¹' X)))

lemma polarDual_closed (X : Set E) : IsClosed (polarDual X) := by
  apply isClosed_sInter
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, _, rfl ⟩
  exact Halfspace_closed _

lemma polarDual_convex (X : Set E) : Convex ℝ (polarDual X) := by
  apply convex_sInter
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, _, rfl ⟩
  exact Halfspace_convex _

lemma polarDual_origin (X : Set E) :
  (0 : E) ∈ polarDual X := by
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, h, rfl ⟩
  rw [Set.mem_image] at h
  rcases h with ⟨ p, _, rfl ⟩
  exact pointDual_origin p

lemma mem_polarDual {X : Set E} {v : E} :
  v ∈ polarDual X ↔ ∀ x ∈ X, inner ℝ x v ≤ (1:ℝ) := by
  unfold polarDual
  rw [Set.mem_sInter]
  constructor
  · -- 1.
    intro h x hx
    rcases em (x = 0) with hx0 | hx0
    · rw [hx0, inner_zero_left]
      exact zero_le_one
    specialize h (SetLike.coe <| pointDual ⟨ x, hx0 ⟩) ?_
    · apply Set.mem_image_of_mem
      apply Set.mem_image_of_mem
      rwa [Set.mem_preimage]
    rwa [mem_pointDual] at h
  · -- 2.
    intro h Hi_s hHi_s
    rw [Set.mem_image] at hHi_s
    rcases hHi_s with ⟨ Hi_, hHi_, rfl ⟩
    rw [Set.mem_image] at hHi_
    rcases hHi_ with ⟨ p, hp, rfl ⟩
    specialize h p.1 hp
    rwa [mem_pointDual]

lemma mem_polarDual' {X : Set E} {v : E} :
  v ∈ polarDual X ↔ ∀ x ∈ X, inner ℝ v x ≤ (1:ℝ) := by
  simp_rw [mem_polarDual, real_inner_comm]

lemma polarDual_comm_half (X Y : Set E) :
  X ⊆ polarDual Y → Y ⊆ polarDual X := by
  rw [Set.subset_def, Set.subset_def]
  intro h y hy
  rw [mem_polarDual]
  intro x hx
  rw [real_inner_comm]
  specialize h x hx
  rw [mem_polarDual] at h
  specialize h y hy
  exact h

lemma polarDual_comm (X Y : Set E) :
  X ⊆ polarDual Y ↔ Y ⊆ polarDual X := by
  constructor <;> exact fun h => polarDual_comm_half _ _ h

lemma doublePolarDual_self {X : Set E}
  (hXcl : IsClosed X) (hXcv : Convex ℝ X) (hX0 : 0 ∈ X) :
  polarDual (polarDual X) = X := by
  apply subset_antisymm
  · -- 1.
    intro x hx
    contrapose! hx
    rw [mem_polarDual]
    push Not
    rcases geometric_hahn_banach_point_closed hXcv hXcl hx with ⟨ f, α, h, hX ⟩
    use (α⁻¹) • (InnerProductSpace.toDual ℝ E).symm f
    rw [mem_polarDual']
    have hαneg : 0 < -α := (neg_pos.mpr ((ContinuousLinearMap.map_zero f) ▸ (hX 0 hX0)))
    constructor <;> intros <;> (try apply le_of_lt) <;>
      rw [real_inner_smul_left, InnerProductSpace.toDual_symm_apply, ←neg_lt_neg_iff, ←neg_mul,
        mul_comm, neg_inv, ← division_def]
    · -- 1.
      rw [lt_div_iff₀ hαneg, neg_one_mul, neg_neg]
      exact hX (by assumption) (by assumption)
    · -- 2.
      rwa [div_lt_iff₀ hαneg, neg_one_mul, neg_neg]
  · -- 2.
    rw [polarDual_comm]


lemma polarDual_empty : polarDual (∅ : Set E) = Set.univ := by
  rw [polarDual, Set.preimage_empty, Set.image_empty, Set.image_empty, Set.sInter_empty]

lemma polarDual_zero : polarDual ({0} : Set E) = Set.univ := by
  rw [polarDual]
  have : (@Subtype.val E fun p => p ≠ 0) ⁻¹' {0} = ∅ := by
    rw [Set.preimage_singleton_eq_empty]
    simp only [ne_eq, Subtype.range_coe_subtype, Set.mem_setOf_eq, not_true, not_false_eq_true]
  rw [this, Set.image_empty, Set.image_empty, Set.sInter_empty]

lemma compact_polarDual_iff [FiniteDimensional ℝ E] {X : Set E} (hXcl : IsClosed X) :
  0 ∈ interior (polarDual X) ↔ IsCompact X := by
  rcases em (X \ {0}).Nonempty with hXnonempty | hXempty
  · constructor <;> rw [Metric.isCompact_iff_isClosed_bounded, isBounded_iff_forall_norm_le]
    · -- 1.
      intro h
      have : IsOpen (interior (polarDual X)) := isOpen_interior
      rw [Metric.isOpen_iff] at this
      rcases this 0 h with ⟨ ε, hε, hball ⟩; clear this h
      refine ⟨ hXcl, 2/ε, fun x hx => ?_ ⟩
      rcases em (x = 0) with hx0 | hx0
      · rw [hx0, norm_zero]
        exact div_nonneg zero_le_two (le_of_lt hε)
      let u : E := (ε/2/(norm x)) • x
      have hnormu : ‖u‖ = ε/2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (half_pos hε) (norm_pos_iff.mpr hx0)),
          div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx0)]
      have hu : u ∈ Metric.ball (0:E) ε := by
        rw [Metric.mem_ball, dist_zero_right, hnormu]
        exact half_lt_self hε
      have h := interior_subset <| hball hu
      rw [mem_polarDual] at h
      specialize h x hx
      rwa [real_inner_smul_right, real_inner_self_eq_norm_mul_norm, ←mul_assoc,
        div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx0), mul_comm,
        ← div_le_div_iff_of_pos_right (div_pos hε zero_lt_two),
        mul_div_cancel_right₀ _ (Ne.symm <| ne_of_lt (div_pos hε zero_lt_two)), one_div_div] at h
    · -- 2.
      rw [interior_eq_compl_closure_compl, Set.mem_compl_iff, Metric.mem_closure_iff]
      simp only [dist_zero_left]
      push Not
      intro h
      rcases h with ⟨ _, M, hM ⟩
      use 1/M
      refine ⟨ ?_, ?_ ⟩
      · rw [gt_iff_lt, one_div]
        exact inv_pos.mpr <| lt_of_lt_of_le (norm_pos_iff.mpr hXnonempty.some_mem.2)
          (hM hXnonempty.some hXnonempty.some_mem.1)
      · intro b hb
        rw [Set.mem_compl_iff, mem_polarDual] at hb
        push Not at hb
        rcases hb with ⟨ y, hy, hb ⟩
        specialize hM y hy
        have hnorminner: |inner ℝ y b| ≤ ‖y‖ * ‖b‖ := abs_real_inner_le_norm y b
        rw [abs_of_pos (lt_trans zero_lt_one hb)] at hnorminner
        have : (1:ℝ) ≤ ‖y‖ * ‖b‖ := le_trans (le_of_lt hb) hnorminner
        have hynezero: y ≠ 0 := by
          rintro rfl
          rw [norm_zero, zero_mul] at this
          exact not_lt_of_ge this zero_lt_one
        rw [← norm_pos_iff] at hynezero
        have hMpos : 0 < M := lt_of_lt_of_le hynezero hM
        have hbnonneg : 0 ≤ ‖b‖ := norm_nonneg b
        rw [div_le_iff₀ hMpos]
        calc (1 : ℝ) ≤ ‖y‖ * ‖b‖ := this
          _ ≤ M * ‖b‖ := by apply mul_le_mul_of_nonneg_right hM hbnonneg
          _ = ‖b‖ * M := mul_comm _ _
  · rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty, Set.subset_singleton_iff_eq] at hXempty
    rcases hXempty with hXempty | hX0
    · rw [hXempty, polarDual_empty, interior_univ]
      exact ⟨ fun _ => isCompact_empty, fun _ => trivial ⟩
    · rw [hX0, polarDual_zero, interior_univ]
      exact ⟨ fun _ => isCompact_singleton, fun _ => trivial ⟩

lemma polarDual_compact_if [FiniteDimensional ℝ E] {X : Set E} (hXcl : IsClosed X)
  (hXcv : Convex ℝ X) :
  0 ∈ interior X → IsCompact (polarDual X) := by
  intro h
  rwa [← doublePolarDual_self hXcl hXcv (interior_subset h),
    compact_polarDual_iff (polarDual_closed _)] at h
