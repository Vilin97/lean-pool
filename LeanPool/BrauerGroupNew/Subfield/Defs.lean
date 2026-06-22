/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# LeanPool.BrauerGroupNew.Subfield.Defs

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Subfield.Defs`.
-/

open Function TensorProduct MulOpposite

/-- A subalgebra whose carrier is commutative and contains inverses of all nonzero elements. -/
structure SubField (K A : Type*) [CommSemiring K] [Semiring A] [Algebra K A]
    extends Subalgebra K A where
  protected mul_comm ⦃x : A⦄ (hx : x ∈ carrier) ⦃y : A⦄ (hy : y ∈ carrier) : x * y = y * x
  exists_inverse ⦃x : A⦄ : x ∈ carrier → x ≠ 0 → ∃ y ∈ carrier, x * y = 1

/-- Reinterpret SubFields as `Subalgebras` -/
add_decl_doc SubField.toSubalgebra

namespace SubField
variable {R K A : Type*}

section CommSemiring
variable [CommSemiring R] [Semiring A] [Algebra R A] {L L₁ L₂ : SubField R A} {a : A}

lemma toSubalgebra_injective : Injective (toSubalgebra : SubField R A → Subalgebra R A) := by
  rintro ⟨L⟩; congr!

@[simp] lemma toSubalgebra_inj : L₁.toSubalgebra = L₂.toSubalgebra ↔ L₁ = L₂ :=
  toSubalgebra_injective.eq_iff

instance : SetLike (SubField R A) A where
  coe L := L.1
  coe_injective := SetLike.coe_injective.comp toSubalgebra_injective

instance : PartialOrder (SubField R A) := .ofSetLike (SubField R A) A

lemma mem_carrier : a ∈ L.carrier ↔ a ∈ L := .rfl
@[simp] lemma mem_toSubalgebra : a ∈ L.toSubalgebra ↔ a ∈ L := .rfl

@[simp] lemma coe_toSubalgebra (L : SubField R A) : (L.toSubalgebra : Set A) = L := rfl

@[ext] lemma ext (h : ∀ x, x ∈ L₁ ↔ x ∈ L₂) : L₁ = L₂ := SetLike.ext h

@[simp] lemma toSubalgebra_le_toSubalgebra : L₁.toSubalgebra ≤ L₂.toSubalgebra ↔ L₁ ≤ L₂ := .rfl
@[simp] lemma toSubalgebra_lt_toSubalgebra : L₁.toSubalgebra < L₂.toSubalgebra ↔ L₁ < L₂ := .rfl

instance : SubsemiringClass (SubField R A) A where
  mul_mem {s} := mul_mem (s := s.1)
  one_mem {s} := one_mem (s := s.1)
  add_mem {s} := add_mem (s := s.1)
  zero_mem {s} := zero_mem (s := s.1)

instance (priority := low) algebra' {K' : Type*} [CommSemiring K'] [SMul K' R] [Algebra K' A]
    [IsScalarTower K' R A] (S : SubField R A) : Algebra K' S := S.toSubalgebra.algebra'

open scoped Classical in
noncomputable instance _root_.SubField.carrier.instSemifield [Nontrivial A] : Semifield L.1 where
  __ := L
  mul_comm := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ Subtype.ext_iff.2 <| L.2 ha hb
  inv := fun ⟨x, hx⟩ ↦ if h0 : x = 0 then 0 else ⟨L.3 hx h0|>.choose,
    L.3 hx h0|>.choose_spec.1⟩
  exists_pair_ne := ⟨⟨0, Subalgebra.zero_mem L.1⟩, ⟨1, Subalgebra.one_mem L.1⟩, by simp⟩
  mul_inv_cancel a ha := by ext; simpa [ha] using (L.3 a.2 <| mod_cast ha).choose_spec.2
  inv_zero := by simp only [↓reduceDIte]
  nnqsmul := _

/-- The directed supremum of a set of subfields. -/
@[simps toSubalgebra]
def dSup (s : Set (SubField R A)) (hs : s.Nonempty) (hsdir : DirectedOn (· ≤ ·) s) :
    SubField R A where
  toSubalgebra := ⨆ L ∈ s, L.1
  mul_comm := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
      Subalgebra.coe_biSup_of_directedOn hs hsdir, coe_toSubalgebra, Set.iSup_eq_iUnion,
      Set.mem_iUnion, SetLike.mem_coe, exists_prop, forall_exists_index, and_imp]
    rintro x L₁ hL₁ hx y L₂ hL₂ hy
    obtain ⟨L, hL, hLL₁, hLL₂⟩ := hsdir _ hL₁ _ hL₂
    exact L.mul_comm (hLL₁ hx) (hLL₂ hy)
  exists_inverse := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
      Subalgebra.coe_biSup_of_directedOn hs hsdir, coe_toSubalgebra, Set.iSup_eq_iUnion,
      Set.mem_iUnion, SetLike.mem_coe, exists_prop, ne_eq, forall_exists_index, and_imp]
    rintro x L hL hx hx₀
    obtain ⟨y, hy, hxy⟩ := L.exists_inverse hx hx₀
    exact ⟨y, ⟨L, hL, hy⟩, hxy⟩

lemma isLUB_dSup (s : Set (SubField R A)) (hs hsdir) : IsLUB s (dSup s hs hsdir) := by
  simpa [IsLUB, IsLeast, lowerBounds, upperBounds, ← toSubalgebra_le_toSubalgebra]
    using isLUB_biSup (s := s) (f := toSubalgebra)

end CommSemiring

section CommRing
variable [CommRing R] [Ring A] [Algebra R A] {L : SubField R A} {a : A}

instance : SubringClass (SubField R A) A where
  mul_mem {s} := mul_mem (s := s.1)
  one_mem {s} := one_mem (s := s.1)
  add_mem {s} := add_mem (s := s.1)
  zero_mem {s} := zero_mem (s := s.1)
  neg_mem {s} := neg_mem (s := s.1)

lemma _root_.SubField.mem_toSubring : a ∈ L.toSubring ↔ a ∈ L := .rfl
@[simp] lemma _root_.SubField.coe_toSubring (L : SubField R A) :
    (L.toSubring : Set A) = L := rfl

noncomputable instance _root_.SubField.carrier.instField [Nontrivial A] : Field L where
  __ : Ring L := inferInstance
  __ := carrier.instSemifield
  qsmul := _

end CommRing

section Semifield
variable [Semifield K] [Semiring A] [Algebra K A]

instance : Bot (SubField K A) where
  bot.toSubalgebra := ⊥
  bot.mul_comm := by simp [← map_mul, _root_.mul_comm]
  bot.exists_inverse := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring, Algebra.coe_bot,
      Set.mem_range, ne_eq, exists_exists_eq_and, forall_exists_index, forall_apply_eq_imp_iff]
    exact fun x hx ↦ ⟨x⁻¹, by rw [← map_mul, mul_inv_cancel₀ (by aesop), map_one]⟩

instance : Nonempty (SubField K A) := ⟨⊥⟩

variable (K A) in
lemma _root_.SubField.exists_isMax : ∃ L : SubField K A, IsMax L :=
  zorn_le_nonempty fun s hschain hs ↦ ⟨dSup s hs hschain.directedOn, (isLUB_dSup ..).1⟩

end Semifield
end SubField
