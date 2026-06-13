/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Adic Completion of a Noetherian Local Ring is Local

The M-adic completion of a Noetherian local ring (R, M) is again
a local ring. The maximal ideal of the completion is the kernel
of the natural surjection onto the residue field R/M.
-/

open scoped Pointwise
open AdicCompletion Ideal Finset

variable {R : Type*} [CommRing R]

/-! ### Transition compatibility for evalₐ -/
section Compat
namespace AdicCompletion

variable (I : Ideal R)

/-- The transition ring hom `factorPow` is compatible with `evalₐ`:
`factorPow I hmn (evalₐ I n x) = evalₐ I m x`. -/
lemma factorPow_comp_evalₐ {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x := by
  simp only [evalₐ, AlgHom.comp_apply, AlgHom.ofLinearMap_apply, eval_apply]
  rw [← x.property hmn]
  induction x.val n using Quotient.inductionOn' with | _ r => rfl

end AdicCompletion
end Compat

/-! ### Constructing inverses from componentwise units -/
section InverseConstruction
namespace AdicCompletion

variable (I : Ideal R) [I.IsMaximal]

omit [I.IsMaximal] in
/-- If `evalOneₐ I x` is a unit (in the residue field `R ⧸ I`), then
`evalₐ I n x` is a unit in `R ⧸ I ^ n` for every `n`. -/
lemma evalₐ_isUnit_of_evalOneₐ_isUnit (x : AdicCompletion I R)
    (hu : IsUnit (evalOneₐ I x)) (n : ℕ) : IsUnit (evalₐ I n x) := by
  induction n with
  | zero =>
    have : Subsingleton (R ⧸ I ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact isUnit_of_subsingleton _
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I 1 x)
      rw [← hr]
      rw [Quotient.isUnit_mk_pow_iff_isUnit_mk I one_ne_zero]
      convert hu using 1
      show Ideal.Quotient.mk I r = evalOneₐ I x
      simp only [evalOneₐ, AlgHom.comp_apply, ← hr]
      rfl
    · apply factorPowSucc.isUnit_of_isUnit_image (npos := Nat.zero_lt_of_ne_zero hn)
      rwa [factorPow_comp_evalₐ]

/-- Given `x` with all `evalₐ` components invertible, construct the inverse
as an element of `AdicCompletion`. -/
noncomputable def mkInverse (x : AdicCompletion I R)
    (hu : ∀ n, IsUnit (evalₐ I n x)) : AdicCompletion I R := by
  have h_smul_eq : ∀ n, (I ^ n • ⊤ : Ideal R) = I ^ n := fun n => by ext
                                                                     simp
  refine ⟨fun n => (Ideal.quotientEquivAlgOfEq R (h_smul_eq n)).symm
    (↑(hu n).unit⁻¹ : R ⧸ I ^ n), ?_⟩
  intro m n hmn
  apply (Ideal.quotientEquivAlgOfEq R (h_smul_eq m)).injective
  simp only [AlgEquiv.apply_symm_apply]
  have key : ∀ (y : R ⧸ I ^ n),
    (Ideal.quotientEquivAlgOfEq R (h_smul_eq m))
      (transitionMap I R hmn ((Ideal.quotientEquivAlgOfEq R (h_smul_eq n)).symm y)) =
      Quotient.factorPow I hmn y := by
    intro y
    induction y using Quotient.inductionOn' with | _ r => rfl
  rw [key]
  -- factorPow I hmn (↑u_n⁻¹) = ↑u_m⁻¹
  have h_map := factorPow_comp_evalₐ I hmn x
  have hfp : Quotient.factorPow I hmn (↑(hu n).unit⁻¹) * evalₐ I m x = 1 := by
    rw [← h_map, ← map_mul, (hu n).val_inv_mul, map_one]
  have hright : evalₐ I m x * ↑(hu m).unit⁻¹ = 1 := (hu m).mul_val_inv
  rw [← one_mul (↑(hu m).unit⁻¹ : R ⧸ I ^ m), ← hfp, mul_assoc, hright, mul_one]

omit [I.IsMaximal] in
lemma evalₐ_mkInverse (x : AdicCompletion I R) (hu : ∀ n, IsUnit (evalₐ I n x)) (n : ℕ) :
    evalₐ I n (mkInverse I x hu) = ↑(hu n).unit⁻¹ := by
  have h_eq : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext
                                                  simp
  have : (mkInverse I x hu).val n =
      (Ideal.quotientEquivAlgOfEq R h_eq).symm (↑(hu n).unit⁻¹) := rfl
  change (Ideal.quotientEquivAlgOfEq R h_eq) ((mkInverse I x hu).val n) = ↑(hu n).unit⁻¹
  rw [this]
  exact AlgEquiv.apply_symm_apply _ _

omit [I.IsMaximal] in
lemma mkInverse_mul (x : AdicCompletion I R) (hu : ∀ n, IsUnit (evalₐ I n x)) :
    mkInverse I x hu * x = 1 := by
  apply ext_evalₐ
  intro n
  simp only [map_mul, map_one]
  rw [evalₐ_mkInverse]
  exact (hu n).val_inv_mul

omit [I.IsMaximal] in
/-- An element of the adic completion whose image under `evalOneₐ` is a unit (in the
residue field) is itself a unit. -/
lemma isUnit_of_evalOneₐ_isUnit (x : AdicCompletion I R) (hu : IsUnit (evalOneₐ I x)) :
    IsUnit x := by
  have hu_all := evalₐ_isUnit_of_evalOneₐ_isUnit I x hu
  have hmul : mkInverse I x hu_all * x = 1 := mkInverse_mul I x hu_all
  have hmul' : x * mkInverse I x hu_all = 1 := by
    apply ext_evalₐ
    intro n
    simp only [map_mul, map_one]
    rw [evalₐ_mkInverse]
    exact (hu_all n).mul_val_inv
  exact ⟨⟨x, mkInverse I x hu_all, hmul', hmul⟩, rfl⟩

end AdicCompletion
end InverseConstruction

/-! ### Main theorem -/
section Main
namespace AdicCompletion

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- Local abbreviation for the maximal ideal `IsLocalRing.maximalIdeal R`. -/
abbrev M' := IsLocalRing.maximalIdeal R

instance adicCompletion_nontrivial :
    Nontrivial (AdicCompletion (M' R) R) := by
  have hsurj := evalOneₐ_surjective (M' R) (R := R)
  have : Nontrivial (R ⧸ M' R) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal (R := R)).ne_top
  exact hsurj.nontrivial

omit [IsLocalRing R] in
lemma field_isUnit_or_isUnit {K : Type*} [Field K] {a b : K} (hab : a + b = 1) :
    IsUnit a ∨ IsUnit b := by
  by_cases ha : a = 0
  · right
    rw [ha, zero_add] at hab
    rw [hab]
    exact isUnit_one
  · exact Or.inl (IsUnit.mk0 a ha)

theorem adicCompletion_isLocalRing :
    IsLocalRing (AdicCompletion (M' R) R) := by
  letI := adicCompletion_nontrivial R
  refine .of_is_unit_or_is_unit_of_add_one fun {a b} hab => ?_
  letI : Field (R ⧸ M' R) := Ideal.Quotient.field (M' R)
  have hab' : evalOneₐ (M' R) a + evalOneₐ (M' R) b = 1 := by
    rw [← map_add, hab, map_one]
  rcases field_isUnit_or_isUnit hab' with hu | hu
  · left
    exact isUnit_of_evalOneₐ_isUnit _ a hu
  · right
    exact isUnit_of_evalOneₐ_isUnit _ b hu

end AdicCompletion
end Main

theorem adicCompletion_isLocalRing
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  AdicCompletion.adicCompletion_isLocalRing R
