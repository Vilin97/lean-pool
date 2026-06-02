/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
import LeanPool.BrauerGroupNew.CentralSimple
import LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# LeanPool.BrauerGroupNew.LemmasAboutSimpleRing

Imported Lean Pool material for `LeanPool.BrauerGroupNew.LemmasAboutSimpleRing`.
-/
universe u
variable (K : Type u) [Field K]
open TensorProduct in
lemma IsSimpleRing.left_of_tensor (B C : Type u)
    [Ring B] [Ring C] [Algebra K C] [Algebra K B]
    [hbc : IsSimpleRing (B ⊗[K] C)] :
    IsSimpleRing B := by
  have hB : Subsingleton B ∨ Nontrivial B := subsingleton_or_nontrivial B
  have hC : Subsingleton C ∨ Nontrivial C := subsingleton_or_nontrivial C
  rcases hB with hB|hB
  · have : Subsingleton (B ⊗[K] C) := by
      rw [← subsingleton_iff_zero_eq_one, show (0 : B ⊗[K] C) = 0 ⊗ₜ 0 by simp,
        show (1 : B ⊗[K] C) = 1 ⊗ₜ 1 by rfl, show (1 : B) = 0 from Subsingleton.elim _ _]
      simp only [tmul_zero, zero_tmul]
    have : Subsingleton (TwoSidedIdeal (B ⊗[K] C)) := by
      constructor
      intro I J
      refine SetLike.ext fun x ↦ ?_
      rw [show x = 0 from Subsingleton.elim _ _]
      refine ⟨fun _ => TwoSidedIdeal.zero_mem _, fun _ ↦ TwoSidedIdeal.zero_mem _⟩
    have H := hbc.1.1
    rw [← not_subsingleton_iff_nontrivial] at H
    contradiction
  rcases hC with hC|hC
  · have : Subsingleton (B ⊗[K] C) := by
      rw [← subsingleton_iff_zero_eq_one, show (0 : B ⊗[K] C) = 0 ⊗ₜ 0 by simp,
        show (1 : B ⊗[K] C) = 1 ⊗ₜ 1 by rfl, show (1 : C) = 0 from Subsingleton.elim _ _]
      simp only [tmul_zero]
    have : Subsingleton (TwoSidedIdeal (B ⊗[K] C)) := by
      constructor
      intro I J
      refine SetLike.ext fun x ↦ ?_
      rw [show x = 0 from Subsingleton.elim _ _]
      refine ⟨fun _ => TwoSidedIdeal.zero_mem _, fun _ ↦ TwoSidedIdeal.zero_mem _⟩
    have H := hbc.1.1
    rw [← not_subsingleton_iff_nontrivial] at H
    contradiction
  by_contra h
  rw [IsSimpleRing.iff_eq_zero_or_injective' (k := K) (A := B)] at h
  push Not at h
  obtain ⟨B', _, _, f, h1, h2⟩ := h
  have : Nontrivial B' := by
    contrapose! h1
    refine SetLike.ext ?_
    intro b
    simp only [TwoSidedIdeal.mem_ker]
    refine ⟨fun _ => trivial, fun _ ↦ Subsingleton.elim _ _⟩
  let F : B ⊗[K] C →ₐ[K] (B' ⊗[K] C) := Algebra.TensorProduct.map f (AlgHom.id _ _)
  have hF := IsSimpleRing.iff_eq_zero_or_injective' (B ⊗[K] C) K |>.1 inferInstance F
  rcases hF with hF|hF
  · have : Nontrivial (B' ⊗[K] C) := by
      rw [← rank_pos_iff_nontrivial (R := K), rank_tensorProduct]
      simp only [CanonicallyOrderedAdd.mul_pos, Cardinal.zero_lt_lift_iff]
      rw [rank_pos_iff_nontrivial, rank_pos_iff_nontrivial]
      aesop
    have : 1 ∈ TwoSidedIdeal.ker F := by rw [hF]; trivial
    simp only [TwoSidedIdeal.mem_ker, _root_.map_one, one_ne_zero] at this
  · have h : Module.FaithfullyFlat K C := inferInstance
    have : Function.Exact (0 : PUnit.{u + 1} →ₗ[K] _) F := by
      intro x
      simp only [Set.mem_range, LinearMap.zero_apply, exists_const]
      rw [← show F 0 = 0 by simp, @Eq.comm _ 0 x]
      constructor
      · apply hF
      · rintro rfl; simp
    have : Function.Exact (0 : PUnit.{u + 1} →ₗ[K] _) f :=
      Module.FaithfullyFlat.iff_exact_iff_rTensor_exact K C|>.1 inferInstance
        (l12 := (0 : PUnit →ₗ[K] _) ) (l23 := f.toLinearMap) |>.2
          fun x ↦ show F x = 0 ↔ _ by aesop
    refine h2 fun x y hxy => ?_
    specialize this (x - y)
    simp only [map_sub, sub_eq_zero, Set.mem_range, LinearMap.zero_apply, exists_const] at this
    simpa [Eq.comm, sub_eq_zero] using this.1 hxy
open TensorProduct in
lemma IsSimpleRing.right_of_tensor (B C : Type u)
    [Ring B] [Ring C] [Algebra K C] [Algebra K B]
    [hbc : IsSimpleRing (B ⊗[K] C)] :
    IsSimpleRing C := by
  haveI : IsSimpleRing (C ⊗[K] B) := by
    let e : C ⊗[K] B ≃ₐ[K] (B ⊗[K] C) := Algebra.TensorProduct.comm _ _ _
    have := TwoSidedIdeal.orderIsoOfRingEquiv e.toRingEquiv
    exact ⟨(OrderIso.isSimpleOrder_iff this).mpr hbc.1⟩
  apply IsSimpleRing.left_of_tensor (K := K) (B := C) (C := B)
