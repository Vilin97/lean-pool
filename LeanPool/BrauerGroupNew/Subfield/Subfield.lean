/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.DoubleCentralizer
import LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Basic
import LeanPool.BrauerGroupNew.Subfield.Defs

/-!
# LeanPool.BrauerGroupNew.Subfield.Subfield

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Subfield.Subfield`.
-/

universe u

section cors_of_DC

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    [Algebra.IsCentral K D]

/-- A maximal subfield of a finite-dimensional central division algebra has square dimension. -/
theorem dim_max_subfield (k : SubField K D) (hk : IsMax k) :
    Module.finrank K D = Module.finrank K k * Module.finrank K k := by
  letI : Field k.1 := inferInstanceAs <| Field k
  have dimdim := dim_centralizer K (A := D) k.1 |>.symm
  have := Subalgebra.le_centralizer_self.2 k.2
  have eq : k.1 = Subalgebra.centralizer K (A := D) k.1 := by
    by_contra! hneq
    have lt := LE.le.lt_iff_ne this |>.2 hneq
    obtain ⟨a, ha1, ha2⟩ : ∃ a ∈ Subalgebra.centralizer K (A := D) k.1, a ∉ k.1 :=
      Set.ssubset_iff_of_subset this |>.1 <| Set.lt_iff_ssubset.1 lt
    letI : CommRing (Algebra.adjoin K (insert a k.1) : Subalgebra K D) :=
    { mul_comm := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
        refine Algebra.adjoin_induction₂  ?_ ?_ ?_
          ?_ ?_ ?_ ?_ ?_ hx hy
        · intro α β hα hβ
          simp only [Set.mem_insert_iff, SetLike.mem_coe] at hα hβ
          rcases hα with rfl | hα <;> rcases hβ with rfl | hβ
          · rfl
          · rw [Subalgebra.mem_centralizer_iff] at ha1
            refine ha1 _ hβ |>.symm
          · rw [Subalgebra.mem_centralizer_iff] at ha1
            apply ha1
            exact hα
          · apply k.mul_comm hα hβ
        · intros
          rw [Algebra.commutes]
        · intros
          rw [Algebra.commutes]
        · intros
          rw [Algebra.commutes]
        · intro _ _ _ _ _ _ h1 h2
          simp only [add_mul, h1, h2, mul_add]
        · intro _ _ _ _ _ _ h1 h2
          simp only [add_mul, h1, h2, mul_add]
        · intro _ _ _ _ _ _ h1 h2
          rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
        · intro _ _ _ _ _ _ h1 h2
          rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc] }
    have : IsField (Algebra.adjoin K (insert a k) : Subalgebra K D) := by
      rw [← Algebra.IsIntegral.isField_iff_isField (R := K)]
      · exact Semifield.toIsField K
      · exact FaithfulSMul.algebraMap_injective K _
    let L : SubField K D := {
      __ := Algebra.adjoin K (insert a k.1)
      mul_comm x hx y hy := by
        have := this.2 ⟨x, hx⟩ ⟨y, hy⟩
        change (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ :
          (Algebra.adjoin K (insert a k.1) : Subalgebra K D)) = ⟨_, _⟩ at this
        simp only [Subtype.mk.injEq] at this ⊢
        exact this
      exists_inverse x hx hx0 := by
         have := this.3 (Subtype.coe_ne_coe.1 hx0 : (⟨x, hx⟩ :
          (Algebra.adjoin K (insert a k.1) : Subalgebra K D)) ≠ 0)
         use this.choose.1
         exact ⟨this.choose.2, by
          have eq := this.choose_spec
          change ⟨x * this.choose.1, _⟩ = (1 : Algebra.adjoin K (insert a k.1)) at eq
          exact Subtype.ext_iff.1 eq⟩
    }
    refine ha2 <| hk (b := L) ?_ ?_
    · change k.1 ≤ Algebra.adjoin K (insert a k.1)
      nth_rw 1 [← Algebra.adjoin_eq k.1]
      refine Algebra.adjoin_mono ?_
      exact Set.subset_insert _ _
    · change _ ∈ Algebra.adjoin K _
      have adjoin_le : Algebra.adjoin K {a} ≤ Algebra.adjoin K (insert a k.1) :=
        Algebra.adjoin_mono (s := {a}) (Set.singleton_subset_iff.mpr (Set.mem_insert a k.1))
      have := Algebra.adjoin_le_iff |>.1 adjoin_le
      exact this rfl
  rw [← eq] at dimdim
  exact dimdim

/-- The centralizer condition for a subfield is equivalent to having square dimension. -/
lemma cor_two_1to2 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] (L : SubField K A) :
    Subalgebra.centralizer K L.1 = L.1 ↔
      Module.finrank K A = Module.finrank K L * Module.finrank K L where
  mp h := by
    letI : Field L.1 := inferInstanceAs <| Field L
    have := dim_centralizer K (A := A) L.1
    rw [h] at this
    exact this.symm
  mpr h := by
    letI : Field L.1 := inferInstanceAs <| Field L
    have := dim_centralizer K (A := A) L.1
    rw [h] at this
    erw [mul_eq_mul_right_iff] at this
    obtain h1 | h2 := this
    · exact Subalgebra.eq_of_le_of_finrank_eq (Subalgebra.le_centralizer_self.2 L.2)
        h1.symm |>.symm
    · have := Module.finrank_pos (R := K) (M := L.1)
      simp_all only [lt_self_iff_false]

/-- The square-dimension condition implies maximality among commutative subalgebras. -/
lemma cor_two_2to3 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] (L : SubField K A) :
    Module.finrank K A = Module.finrank K L * Module.finrank K L →
    (∀ (L' : Subalgebra K A) (_ : ∀ x ∈ L', ∀ y ∈ L',  x * y = y * x), L.1 ≤ L' →
      L.1 = L') :=
  fun hrank L' hL' hLL ↦ by
  letI : Field L.1 := inferInstanceAs <| Field L
  have := dim_centralizer K (A := A) L.1 |>.symm
  simp only [this, SubField.coe_toSubalgebra] at hrank
  erw [mul_eq_mul_right_iff] at hrank
  obtain h1 | h2 := hrank
  · have := Subalgebra.eq_of_le_of_finrank_eq (Subalgebra.le_centralizer_self.2 L.2) h1.symm
    exact le_antisymm hLL fun x hx => this.symm ▸ Subalgebra.mem_centralizer_iff _ |>.2
      fun y hy => hL' _ hx _ (hLL hy) |>.symm
  · have := Module.finrank_pos (R := K) (M := L.1)
    simp_all only [mul_zero, lt_self_iff_false]

/-- Maximality among commutative subalgebras implies that the centralizer is the subfield itself. -/
lemma cor_two_3to1 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] (L : SubField K A) :
    (∀ (L' : Subalgebra K A)  (_ : ∀ x ∈ L', ∀ y ∈ L',  x * y = y * x), L.1 ≤ L' →
      L.1 = L') →
    Subalgebra.centralizer K L = L.1 := by
  intro H
  refine le_antisymm ?_ ?_
  · by_contra! hL'
    have := Subalgebra.le_centralizer_self.2 L.2
    have Llt := lt_of_le_not_ge this hL'
    have exist_ele : ∃ a ∈ Subalgebra.centralizer K L.1, a ∉ L.1 :=
      Set.ssubset_iff_of_subset this |>.1 <| Set.lt_iff_ssubset.1 Llt
    obtain ⟨a, ⟨ha1, ha2⟩⟩ := exist_ele
    specialize H (Algebra.adjoin K (insert a L.1)) (fun x hx y hy ↦ by
      refine Algebra.adjoin_induction₂ (fun x y hx hy ↦ by
        simp only [Set.mem_insert_iff, SetLike.mem_coe] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · rfl
        · rw [Subalgebra.mem_centralizer_iff] at ha1
          exact ha1 _ hy |>.symm
        · rw [Subalgebra.mem_centralizer_iff] at ha1
          rename_i hxx
          exact ha1 _ hxx
        · exact L.2 hx hy)
        (fun k1 k2 ↦ Algebra.commutes _ _) (fun k x _ ↦ Algebra.commutes _ _)
        (fun k x _ ↦ Algebra.commutes _ _ |>.symm)
        (fun x y z _ _ _ hxz hyz ↦ by rw [mul_add, add_mul, hxz, hyz])
        (fun x y z _ _ _ hxz hyz ↦ by rw [mul_add, add_mul, hxz, hyz])
        (fun x y z _ _ _ hxz hyz ↦ by rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc])
        (fun x y z _ _ _ hxy hxz ↦ by rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc])
        hx hy)
      (by
        nth_rw 1 [← Algebra.adjoin_eq L.1]
        exact Algebra.adjoin_mono (Set.subset_insert _ _))
    have : L.1 ≠ Algebra.adjoin K (insert a L.1) := ne_of_mem_of_not_mem' (a := a)
      (by
        exact (Algebra.adjoin_le_iff |>.1 (Algebra.adjoin_mono (R := K) (s := {a})
          (Set.singleton_subset_iff.mpr (Set.mem_insert a L.1)))) rfl) ha2 |>.symm
    tauto
  · exact Subalgebra.le_centralizer_self.2 L.2

/-- Maximal subfields of a division algebra are exactly maximal commutative subalgebras. -/
lemma maxsubfield_of_div_iff (L : SubField K D) : (∀ (L' : Subalgebra K D)
    (_ : ∀ x ∈ L', ∀ y ∈ L',  x * y = y * x), L.1 ≤ L' → L.1 = L') ↔
    IsMax L :=
  ⟨fun h ↦ fun L' hL' ↦ le_of_eq <| SubField.toSubalgebra_inj.1 <|
    h L'.1 (fun _ a _ a_1 ↦ L'.2 a a_1) hL' |>.symm,
  fun h ↦ cor_two_2to3 K D L <| dim_max_subfield K D L h⟩

/-- Algebra equivalences preserve maximality of subfields. -/
lemma IsMaxSubfield.ofAlgEquiv (L1 L2 : SubField K D) (e : L1 ≃ₐ[K] L2)
    (hL1 : IsMax L1) : IsMax L2 := by
  have hL11 := dim_max_subfield K D L1 hL1
  have dim_eq := e.toLinearEquiv.finrank_eq
  rw [dim_eq] at hL11
  exact maxsubfield_of_div_iff K D L2 |>.1 <| cor_two_2to3 K D L2 hL11

end cors_of_DC
