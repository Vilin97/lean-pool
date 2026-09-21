/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorExact
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SymPermCast

/-!
# Whiskering by a nonzero object is faithful

In a rigid symmetric abelian category with simple unit, tensoring
with a nonzero object kills no nonzero morphism.  The contraction
`X ⊗ Xᘁ ⟶ 𝟙` (evaluation through the braiding) is nonzero — else
the zigzag identity kills `𝟙 X` — hence an epimorphism onto the
simple unit; whiskering preserves it, and the exchange law then
cancels it against `f ▷ (X ⊗ Xᘁ) = 0`.

Simplicity of the unit is carried as a hypothesis and discharged
where `End 𝟙 = ℂ` is available.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {A : Type u}

/-- The evaluation of a nonzero object is nonzero: were it zero,
the zigzag identity would make `𝟙 X` zero. -/
theorem evaluation_ne_zero [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [RigidCategory A]
    {X : A} (hX : ¬ IsZero X) :
    (ε_ X (Xᘁ)) ≠ 0 := by
  intro hz
  apply hX
  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 X
      = (λ_ X).inv ≫ ((λ_ X).hom ≫ (ρ_ X).inv) ≫ (ρ_ X).hom := by
        simp
    _ = (λ_ X).inv ≫ (η_ X (Xᘁ) ▷ X ≫ (α_ _ _ _).hom ≫
          X ◁ ε_ X (Xᘁ)) ≫ (ρ_ X).hom := by
        rw [ExactPairing.evaluation_coevaluation]
    _ = 0 := by
        rw [hz]
        simp

/-- **Whiskering by a nonzero object is faithful** on morphisms: in
a rigid symmetric abelian category with simple unit, `f ▷ X = 0`
forces `f = 0` when `X` is nonzero. -/
theorem eq_zero_of_whiskerRight_eq_zero
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalPreadditive A] [RigidCategory A]
    (hs : Simple (𝟙_ A))
    {X : A} (hX : ¬ IsZero X) {P Q : A} {f : P ⟶ Q}
    (hw : f ▷ X = 0) : f = 0 := by
  haveI := hs
  set ev' : X ⊗ (Xᘁ) ⟶ 𝟙_ A := (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)
    with hev'
  have hne : ev' ≠ 0 := by
    intro hz
    refine evaluation_ne_zero hX ?_
    have := congrArg (fun g => (β_ X (Xᘁ)).inv ≫ g) hz
    simpa [hev'] using this
  haveI : Epi ev' := epi_of_nonzero_to_simple hne
  haveI : Epi (P ◁ ev') := by
    have heq : (tensorLeft P).map ev' = P ◁ ev' := rfl
    haveI : (tensorLeft P).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction
        (tensorLeftAdjunction (ᘁP) P)
    rw [← heq]
    exact (tensorLeft P).map_epi ev'
  have hmid : f ▷ (X ⊗ (Xᘁ)) = 0 := by
    rw [MonoidalCategory.whiskerRight_tensor, hw]
    simp
  have hexch : (P ◁ ev') ≫ (f ▷ (𝟙_ A)) = 0 := by
    rw [whisker_exchange, hmid, zero_comp]
  have hzero : f ▷ (𝟙_ A) = 0 := by
    have h0 : (P ◁ ev') ≫ (f ▷ (𝟙_ A)) = (P ◁ ev') ≫ 0 := by
      rw [hexch, comp_zero]
    exact (cancel_epi (P ◁ ev')).mp h0
  calc f = (ρ_ P).inv ≫ (f ▷ (𝟙_ A)) ≫ (ρ_ Q).hom := by simp
    _ = 0 := by rw [hzero]; simp

section Transport

/-- **Nonvanishing transports up the standard embedding**: if an
element of the group algebra acts nonzero at its own size, it acts
nonzero at every larger size — the extended action is the whiskered
one, and whiskering by the nonzero `X` is faithful. -/
private theorem whiskerPowAlg_ne_zero
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalPreadditive A] [RigidCategory A] [Linear ℂ A]
    [MonoidalLinear ℂ A]
    (hs : Simple (𝟙_ A))
    {X : A} (hX : ¬ Limits.IsZero X) {m : ℕ} (k : ℕ)
    (f : End (tensorPow A X m)) (hf : f ≠ 0) :
    whiskerPowAlg X m k f ≠ 0 := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    intro hz
    exact ih (eq_zero_of_whiskerRight_eq_zero hs hX
      (show (whiskerPowAlg X m k f) ▷ X = 0 from hz))

theorem permAlg_symCast_ne_zero
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalPreadditive A] [RigidCategory A] [Linear ℂ A]
    [MonoidalLinear ℂ A]
    (hs : Simple (𝟙_ A))
    {X : A} (hX : ¬ Limits.IsZero X) {m n : ℕ} (h : m ≤ n)
    (x : SymGroupAlgebra m) (hx : permAlg X m x ≠ 0) :
    permAlg X n (symCast h x) ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [permAlg_symCast]
  exact whiskerPowAlg_ne_zero hs hX k _ hx

end Transport

/-- A zero factor makes the tensor zero. -/
theorem isZero_tensor_of_isZero_left
    [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A]
    {B V : A}
    (hB : Limits.IsZero B) : Limits.IsZero (B ⊗ V) := by
  rw [Limits.IsZero.iff_id_eq_zero] at hB ⊢
  rw [show 𝟙 (B ⊗ V) = 𝟙 B ▷ V from
    (MonoidalCategory.id_whiskerRight _ _).symm, hB,
    MonoidalPreadditive.zero_whiskerRight]

/-- **Base-change faithfulness** (the kernel of Deligne 2.3): if
the tensor with a nonzero dualizable object vanishes, the other
factor vanishes — the whiskered evaluation is an epimorphism from
a zero object. -/
theorem isZero_left_of_tensor_isZero
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalPreadditive A] [RigidCategory A]
    (hs : Simple (𝟙_ A))
    {B V : A} (hV : ¬ Limits.IsZero V)
    (h : Limits.IsZero (B ⊗ V)) : Limits.IsZero B := by
  -- The braided evaluation out of `V ⊗ Vᘁ` is epi onto the unit.
  have hev : Epi ((β_ V (Vᘁ)).hom ≫ ε_ V (Vᘁ)) := by
    have hne : (β_ V (Vᘁ)).hom ≫ ε_ V (Vᘁ) ≠ 0 := by
      intro h0
      apply evaluation_ne_zero (A := A) hV
      rw [show ε_ V (Vᘁ) =
        (β_ V (Vᘁ)).inv ≫ ((β_ V (Vᘁ)).hom ≫ ε_ V (Vᘁ)) from by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp],
        h0, Limits.comp_zero]
    haveI := hs
    exact epi_of_nonzero_to_simple hne
  -- Whisker it by `B`: an epi onto `B`, from a zero object.
  have hepi : Epi ((B ◁ ((β_ V (Vᘁ)).hom ≫ ε_ V (Vᘁ))) ≫
      (ρ_ B).hom) := by
    have : Epi (B ◁ ((β_ V (Vᘁ)).hom ≫ ε_ V (Vᘁ))) := by
      have hpc : Limits.PreservesColimitsOfSize.{v, v}
          (tensorLeft B) := tensorLeft_preservesColimits B
      exact (tensorLeft B).map_epi _
    exact epi_comp _ _
  have hsrc : Limits.IsZero (B ⊗ (V ⊗ Vᘁ)) := by
    have h1 : Limits.IsZero ((B ⊗ V) ⊗ Vᘁ) :=
      isZero_tensor_of_isZero_left h
    exact h1.of_iso (α_ B V (Vᘁ)).symm
  -- An epi from a zero object kills the target.
  rw [Limits.IsZero.iff_id_eq_zero]
  have hzero : (B ◁ ((β_ V (Vᘁ)).hom ≫ ε_ V (Vᘁ))) ≫
      (ρ_ B).hom = 0 := hsrc.eq_of_src _ _
  rw [← cancel_epi ((B ◁ ((β_ V (Vᘁ)).hom ≫ ε_ V (Vᘁ))) ≫
    (ρ_ B).hom), hzero, Limits.zero_comp, Limits.comp_zero]

end RS
