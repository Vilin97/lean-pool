/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
import LeanPool.BrauerGroupNew.BrauerGroup
import Mathlib.RingTheory.LittleWedderburn

/-!
# Brauer groups over finite fields

This file proves that the Brauer group of a finite field is trivial.
-/

variable (K : Type*) [Field K] [Finite K]

suppress_compilation

lemma BrauerTrivial (A : CSA K) : ∃ n ≠ 0, Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨n, hn, D, hD1, hD2, ⟨iso⟩⟩ := WedderburnArtin_algebra_version K A
  have : Finite D := Module.finite_iff_finite.1 <| is_fin_dim_of_wdb K A hn D iso
  let _ := littleWedderburn D
  have eq1 := is_central_of_wdb K A n D hn iso |>.center_eq_bot
  have eq2 : Subalgebra.center K D = ⊤ := SetLike.ext fun x ↦
    ⟨fun _ ↦ by trivial, fun _ ↦ by
      rw [Subalgebra.mem_center_iff]
      simp [mul_comm]⟩
  have e : D ≃ₐ[K] K := Subalgebra.topEquiv.symm.trans <| Subalgebra.equivOfEq ⊤ ⊥
    (eq2.symm.trans eq1) |>.trans <| Algebra.botEquiv K D
  exact ⟨n, hn, ⟨iso.trans e.mapMatrix⟩⟩

theorem trivialBrauer : ∀ a : BrauerGroup K, a = 1 := fun a ↦ by
  induction a using Quotient.inductionOn with
  | h A =>
    change _ = Quotient.mk (Brauer.CSA_Setoid K) _
    simp only [Quotient.eq]
    change IsBrauerEquivalent _ ⟨.of K K⟩
    obtain ⟨n, hn, ⟨iso⟩⟩ := BrauerTrivial K A
    exact ⟨1, n, one_ne_zero, hn, ⟨BrauerGroup.dimOneIso A |>.trans iso⟩⟩

instance BrauerOverFinite : Unique (BrauerGroup K) where
  default := 1
  uniq := trivialBrauer K
