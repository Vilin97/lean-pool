/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.FaceReflectionLines
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.OneDimIBP
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.PeelFubini
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Face Reflection -/

@[expose] public section

namespace Homogenization

open Homogenization MeasureTheory
open scoped BigOperators

/-!
# Single-face even reflection: weak-gradient transport

Assembles the per-line calculus (`FaceReflectionLines`), the kink integration by
parts (`OneDimIBP`), and coordinate-peeling Fubini (`PeelFubini`) into the weak
gradient of the even reflection `faceReflect v a i`.
-/

noncomputable section

variable {d : ℕ}

/-- A continuous compactly supported function is bounded. -/
theorem exists_norm_bound_of_continuous_hasCompactSupport
    {w : Vec d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖w x‖ ≤ C := by
  have hcpt : IsCompact (tsupport w) := hwc
  rcases (tsupport w).eq_empty_or_nonempty with hemp | hne
  · refine ⟨0, le_refl 0, fun x => ?_⟩
    have : x ∉ tsupport w := by rw [hemp]; exact Set.notMem_empty x
    simp [image_eq_zero_of_notMem_tsupport this]
  · obtain ⟨x₀, hx₀_mem, hx₀_max⟩ :=
      hcpt.exists_isMaxOn hne hw.norm.continuousOn
    refine ⟨‖w x₀‖, norm_nonneg _, fun x => ?_⟩
    by_cases hx : x ∈ tsupport w
    · exact hx₀_max hx
    · simp [image_eq_zero_of_notMem_tsupport hx]

/-- On the face `{x_i = a}` the reflection is the identity. -/
theorem coordFaceReflection_eq_self_of_face {a : ℝ} {i : Fin d} {x : Vec d}
    (hx : x i = a) : coordFaceReflection a i x = x := by
  funext j
  rw [coordFaceReflection_apply]
  rcases eq_or_ne j i with h | h
  · subst h; rw [if_pos rfl, hx]; ring
  · rw [if_neg h]

/-- The even reflection of a continuous function is continuous (the two branches
agree on the face). -/
theorem continuous_faceReflect {v : Vec d → ℝ} (hv : Continuous v)
    (a : ℝ) (i : Fin d) : Continuous (faceReflect v a i) := by
  refine Continuous.if_le hv (hv.comp (continuous_coordFaceReflection a i))
    continuous_const (continuous_apply i) ?_
  intro x hx
  rw [coordFaceReflection_eq_self_of_face hx.symm]

/-- The even reflection has compact support when `v` does. -/
theorem hasCompactSupport_faceReflect {v : Vec d → ℝ}
    (hvc : HasCompactSupport v) (a : ℝ) (i : Fin d) :
    HasCompactSupport (faceReflect v a i) := by
  have hcv : IsCompact (tsupport v) := hvc
  set K : Set (Vec d) := tsupport v ∪ coordFaceReflection a i ⁻¹' tsupport v with hK
  have hpre_eq : coordFaceReflection a i '' (tsupport v)
      = coordFaceReflection a i ⁻¹' (tsupport v) :=
    congrFun (Set.image_eq_preimage_of_inverse (coordFaceReflection_involutive a i)
      (coordFaceReflection_involutive a i)) (tsupport v)
  have hK_compact : IsCompact K := by
    rw [hK, ← hpre_eq]
    exact hcv.union (hcv.image (continuous_coordFaceReflection a i))
  have hK_closed : IsClosed K :=
    (isClosed_tsupport v).union
      ((isClosed_tsupport v).preimage (continuous_coordFaceReflection a i))
  have hsupp_sub : Function.support (faceReflect v a i) ⊆ K := by
    intro x hx
    rw [Function.mem_support] at hx
    by_cases h : a ≤ x i
    · refine Or.inl (subset_tsupport v ?_)
      rw [Function.mem_support]; intro h0; apply hx; unfold faceReflect; rw [if_pos h, h0]
    · refine Or.inr ?_
      rw [Set.mem_preimage]
      refine subset_tsupport v ?_
      rw [Function.mem_support]; intro h0; apply hx; unfold faceReflect; rw [if_neg h, h0]
  exact IsCompact.of_isClosed_subset hK_compact (isClosed_tsupport _)
    (closure_minimal hsupp_sub hK_closed)

end

end Homogenization
