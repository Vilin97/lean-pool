/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.FieldTheory.Finite.Extension

/-!
# Nested canonical finite-field extensions

If `a ∣ b`, finite-field theory supplies an embedding from the chosen
degree-`a` extension into the chosen degree-`b` extension.  This file fixes
one such embedding and records the scalar-tower and degree consequences used
by the constant-extension Hasse--Weil argument.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

variable (K : Type*) [Field K] [Fintype K]
variable (p a b : ℕ) [Fact p.Prime] [CharP K p]
variable [NeZero a] [NeZero b]

/-- A chosen `K`-algebra embedding between canonical finite-field extensions
whose degrees satisfy `a ∣ b`. -/
noncomputable def finiteFieldExtensionAlgHomOfDvd (h : a ∣ b) :
    FiniteField.Extension K p a →ₐ[K]
      FiniteField.Extension K p b :=
  (FiniteField.nonempty_algHom_of_finrank_dvd (F := K)
    (K := FiniteField.Extension K p a)
    (L := FiniteField.Extension K p b) (by
      rw [FiniteField.finrank_extension, FiniteField.finrank_extension]
      exact h)).some

/-- The algebra structure selected by `finiteFieldExtensionAlgHomOfDvd`. -/
@[reducible] noncomputable def finiteFieldExtensionAlgebraOfDvd
    (h : a ∣ b) :
    Algebra (FiniteField.Extension K p a)
      (FiniteField.Extension K p b) :=
  (finiteFieldExtensionAlgHomOfDvd K p a b h).toAlgebra

/-- The selected divisible-degree embedding is compatible with the original
coefficient field. -/
theorem finiteFieldExtension_isScalarTower_of_dvd (h : a ∣ b) :
    letI : Algebra (FiniteField.Extension K p a)
        (FiniteField.Extension K p b) :=
      finiteFieldExtensionAlgebraOfDvd K p a b h
    IsScalarTower K (FiniteField.Extension K p a)
      (FiniteField.Extension K p b) := by
  let : Algebra (FiniteField.Extension K p a)
      (FiniteField.Extension K p b) :=
    finiteFieldExtensionAlgebraOfDvd K p a b h
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  exact (finiteFieldExtensionAlgHomOfDvd K p a b h).commutes c |>.symm

/-- The relative degree of the chosen nested extension is the quotient of
the two absolute degrees. -/
theorem finrank_finiteFieldExtension_of_dvd (h : a ∣ b) :
    letI : Algebra (FiniteField.Extension K p a)
        (FiniteField.Extension K p b) :=
      finiteFieldExtensionAlgebraOfDvd K p a b h
    Module.finrank (FiniteField.Extension K p a)
        (FiniteField.Extension K p b) = b / a := by
  let E := FiniteField.Extension K p a
  let L := FiniteField.Extension K p b
  let : Algebra E L := finiteFieldExtensionAlgebraOfDvd K p a b h
  let : IsScalarTower K E L :=
    finiteFieldExtension_isScalarTower_of_dvd K p a b h
  let : Module.Finite E L := Module.Finite.of_finite
  have hmul : Module.finrank K E * Module.finrank E L =
      Module.finrank K L := Module.finrank_mul_finrank K E L
  rw [FiniteField.finrank_extension K p a,
    FiniteField.finrank_extension K p b] at hmul
  apply (Nat.eq_div_iff_mul_eq_left (NeZero.ne a) h).2
  simpa [Nat.mul_comm] using hmul.symm

/-- The chosen degree-`2a` extension is quadratic over the chosen degree-`a`
subfield. -/
theorem finrank_double_finiteFieldExtension :
    letI : Algebra (FiniteField.Extension K p a)
        (FiniteField.Extension K p (2 * a)) :=
      finiteFieldExtensionAlgebraOfDvd K p a (2 * a) ⟨2, by omega⟩
    Module.finrank (FiniteField.Extension K p a)
        (FiniteField.Extension K p (2 * a)) = 2 := by
  rw [finrank_finiteFieldExtension_of_dvd K p a (2 * a) ⟨2, by omega⟩]
  simpa [Nat.mul_comm] using Nat.mul_div_cancel_left 2 (NeZero.pos a)

/-- Cardinality of the degree-`2a` extension is the square of the
degree-`a` extension's cardinality. -/
theorem natCard_double_finiteFieldExtension_eq_sq :
    Nat.card (FiniteField.Extension K p (2 * a)) =
      Nat.card (FiniteField.Extension K p a) ^ 2 := by
  rw [FiniteField.natCard_extension K p (2 * a),
    FiniteField.natCard_extension K p a]
  ring

/-- A positive multiple of the extension degree is already large enough to
dominate that degree.  This elementary growth estimate is what makes one
fixed multiple work uniformly in the Stepanov construction. -/
theorem degree_le_natCard_finiteFieldExtension_mul
    (d n : ℕ) [NeZero (d * n)] (hn : 0 < n) :
    d ≤ Nat.card (FiniteField.Extension K p (d * n)) := by
  rw [FiniteField.natCard_extension K p (d * n)]
  have hcard : 1 < Nat.card K := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card K)
  have hdPow : d ≤ Nat.card K ^ d :=
    (Nat.lt_pow_self hcard).le
  exact hdPow.trans (Nat.pow_le_pow_right (Nat.card_pos)
    (Nat.le_mul_of_pos_right d hn))

end

end BGS.HasseWeil
