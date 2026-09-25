/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.UnitEnd
import LeanPool.RegtsSevenster.RS.Classical.Deligne.BiprodTransfer

/-!
# Scalar self-braidings and the vanishing for even and odd lines

When the self-braiding of an object is a scalar, the whole
symmetric-group action on its tensor powers is by that scalar's
sign character: the top swap acts by the scalar, every
transposition is conjugate to it, and transpositions generate.
For a trivial self-braiding (the unit) the central idempotents
then act by the plain character sum — the Schur specialisation at
one even variable — and for braiding `−1` (an odd line) by the
signed sum — the specialisation at one odd variable.  The
one-variable indicator evaluations kill every non-row
(respectively non-column) Schur functor, and iterated direct sums
give the vanishing half of Deligne 1.9 for `𝟙^p ⊕ 1̄^q` inside any
ambient category — the engine of the trichotomy 2.9.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits Finset

universe v u

variable {A : Type u}

private theorem conj_smul_id [Category.{v} A] [Preadditive A] [Linear ℂ A]
    {W V : A} (e : W ≅ V) (c : ℂ) :
    e.hom ≫ (c • 𝟙 V) ≫ e.inv = c • 𝟙 W := by
  simp

/-- A scalar self-braiding makes the top swap act by the
scalar. -/
theorem swapTop_of_scalar
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    {X : A} {c : ℂ}
    (hβ : (β_ X X).hom = c • 𝟙 (X ⊗ X)) (n : ℕ) :
    swapTop X n = c • 𝟙 (tensorPow A X (n + 2)) := by
  rw [swapTop, hβ, MonoidalLinear.whiskerLeft_smul,
    MonoidalCategory.whiskerLeft_id]
  exact conj_smul_id (α_ (tensorPow A X n) X X) c

/-- Every transposition acts by the scalar: the top swap does, and
transpositions are conjugate with central scalar values. -/
theorem permMor_swap_of_scalar
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    {X : A} {c : ℂ}
    (hβ : (β_ X X).hom = c • 𝟙 (X ⊗ X)) :
    ∀ {n : ℕ} (x y : Fin n), x ≠ y →
      permMor X n (Equiv.swap x y) =
        c • 𝟙 (tensorPow A X n) := by
  intro n
  match n with
  | 0 => exact fun x _ _ => absurd x.isLt (by omega)
  | 1 => exact fun x y hxy => absurd (Subsingleton.elim x y) hxy
  | m + 2 =>
    intro x y hxy
    have htop : permMor X (m + 2) topSwap =
        c • 𝟙 (tensorPow A X (m + 2)) := by
      rw [permMor_topSwap_eq, swapTop_of_scalar hβ]
    have hconj : IsConj (topSwap : Equiv.Perm (Fin (m + 2)))
        (Equiv.swap x y) := by
      rw [topSwap]
      exact Equiv.Perm.isConj_swap
        (by
          intro h
          have := congrArg Fin.val h
          simp [Fin.last] at this) hxy
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg, permMor_mul, permMor_mul, htop, Linear.smul_comp,
      Linear.comp_smul, Category.id_comp, ← permMor_mul,
      mul_inv_cancel, permMor_one]

/-- **Scalar self-braiding acts by the sign character**: with a
scalar square root of unity as self-braiding, every permutation
acts by the scalar raised to its sign. -/
theorem permMor_of_scalar
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    {X : A} {c : ℂ}
    (hβ : (β_ X X).hom = c • 𝟙 (X ⊗ X)) (hc2 : c * c = 1)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permMor X n σ =
      (if Equiv.Perm.sign σ = 1 then (1 : ℂ) else c) •
        𝟙 (tensorPow A X n) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [permMor_one, Equiv.Perm.sign_one, ite_eq_left rfl,
      one_smul]
  | swap_mul σ x y hxy ih =>
    rw [permMor_mul, ih, permMor_swap_of_scalar hβ x y hxy,
      Linear.smul_comp, Linear.comp_smul, Category.comp_id,
      smul_smul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
    by_cases hs : Equiv.Perm.sign σ = 1
    · rw [ite_eq_left hs, hs]
      norm_num
    · have hs' : Equiv.Perm.sign σ = -1 :=
        (Int.units_eq_one_or _).resolve_left hs
      rw [ite_eq_right hs, hs']
      norm_num [hc2]

/-- The group-algebra action under a scalar self-braiding is
multiplication by the twisted coefficient sum. -/
theorem permAlg_of_scalar
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    {X : A} {c : ℂ}
    (hβ : (β_ X X).hom = c • 𝟙 (X ⊗ X)) (hc2 : c * c = 1)
    {n : ℕ} (x : SymGroupAlgebra n) :
    permAlg X n x =
      (∑ σ : Equiv.Perm (Fin n), x.coeff σ *
        (if Equiv.Perm.sign σ = 1 then (1 : ℂ) else c)) •
        𝟙 (tensorPow A X n) := by
  classical
  have hlift : permAlg X n x =
      x.coeff.sum fun σ r => r • permMor X n σ := by
    rw [permAlg]
    exact MonoidAlgebra.lift_apply _ _
  rw [hlift]
  rw [show (x.coeff.sum fun σ r => r • permMor X n σ) =
    ∑ σ ∈ x.coeff.support, x.coeff σ • permMor X n σ from rfl]
  rw [Finset.sum_congr rfl fun σ _ => by
    rw [permMor_of_scalar hβ hc2 σ, smul_smul]]
  rw [← Finset.sum_smul]
  congr 1
  refine Finset.sum_subset (Finset.subset_univ _) fun σ _ hσ => ?_
  rw [Finsupp.notMem_support_iff.mp hσ, zero_mul]

/-- The identification of the raw idempotent with its Shape form
at its own size. -/
theorem pe_eq_shape_e (P : SchurPackage.{v}) (lam : YoungDiagram) :
    P.e lam = Shape.e P (⟨lam, rfl⟩ : Shape lam.card) := by
  unfold Shape.e
  erw [symCast_le_refl]

/-- The plain coefficient sum of the central idempotent is the
dimension times the Schur specialisation at one even variable. -/
theorem sum_e_coeff (P : SchurPackage.{v}) (lam : YoungDiagram) :
    (∑ σ : Equiv.Perm (Fin lam.card), (P.e lam).coeff σ) =
      (P.dim lam : ℂ) * diagramSchur lam (superPS 1 0) := by
  classical
  have hfrob : ((lam.card.factorial : ℂ))⁻¹ *
      ∑ π : Equiv.Perm (Fin lam.card),
        jtChar lam (permCast (rfl : lam.card = lam.card).symm π) *
          cycleFun (superPS 1 0) π =
      diagramSchur lam (superPS 1 0) :=
    jtChar_shape_frobenius (⟨lam, rfl⟩ : Shape lam.card)
      (superPS 1 0)
  have hone : ∀ π : Equiv.Perm (Fin lam.card),
      cycleFun (superPS 1 0) π = 1 := fun π => by
    rw [cycleFun_superPS_h]
    norm_num
  rw [show (∑ π : Equiv.Perm (Fin lam.card),
      jtChar lam (permCast (rfl : lam.card = lam.card).symm π) *
        cycleFun (superPS 1 0) π) =
    ∑ π : Equiv.Perm (Fin lam.card),
      jtChar lam (permCast (rfl : lam.card = lam.card).symm π)
    from Finset.sum_congr rfl fun π _ => by
      rw [hone π, mul_one]] at hfrob
  calc ∑ σ : Equiv.Perm (Fin lam.card), (P.e lam).coeff σ
      = ∑ σ : Equiv.Perm (Fin lam.card),
        ((P.dim lam : ℂ) / (lam.card.factorial : ℂ)) *
          jtChar lam (permCast (rfl : lam.card = lam.card).symm
            σ) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [pe_eq_shape_e]
        exact shape_e_coeff P (⟨lam, rfl⟩ : Shape lam.card) σ
    _ = ((P.dim lam : ℂ) / (lam.card.factorial : ℂ)) *
        ∑ σ : Equiv.Perm (Fin lam.card),
          jtChar lam (permCast (rfl : lam.card = lam.card).symm
            σ) := by
        rw [← Finset.mul_sum]
    _ = (P.dim lam : ℂ) * diagramSchur lam (superPS 1 0) := by
        rw [← hfrob]
        field_simp

/-- The signed coefficient sum of the central idempotent is the
dimension times the Schur specialisation at one odd variable. -/
theorem sum_e_coeff_sign (P : SchurPackage.{v})
    (lam : YoungDiagram) :
    (∑ σ : Equiv.Perm (Fin lam.card), (P.e lam).coeff σ *
      ((Equiv.Perm.sign σ : ℤ) : ℂ)) =
      (P.dim lam : ℂ) * diagramSchur lam (superPS 0 1) := by
  classical
  have hfrob : ((lam.card.factorial : ℂ))⁻¹ *
      ∑ π : Equiv.Perm (Fin lam.card),
        jtChar lam (permCast (rfl : lam.card = lam.card).symm π) *
          cycleFun (superPS 0 1) π =
      diagramSchur lam (superPS 0 1) :=
    jtChar_shape_frobenius (⟨lam, rfl⟩ : Shape lam.card)
      (superPS 0 1)
  have hsgn : ∀ π : Equiv.Perm (Fin lam.card),
      cycleFun (superPS 0 1) π =
        ((Equiv.Perm.sign π : ℤ) : ℂ) := fun π => by
    rw [cycleFun_superPS_e]
    norm_num
  rw [show (∑ π : Equiv.Perm (Fin lam.card),
      jtChar lam (permCast (rfl : lam.card = lam.card).symm π) *
        cycleFun (superPS 0 1) π) =
    ∑ π : Equiv.Perm (Fin lam.card),
      jtChar lam (permCast (rfl : lam.card = lam.card).symm π) *
        ((Equiv.Perm.sign π : ℤ) : ℂ)
    from Finset.sum_congr rfl fun π _ => by rw [hsgn π]] at hfrob
  calc ∑ σ : Equiv.Perm (Fin lam.card), (P.e lam).coeff σ *
      ((Equiv.Perm.sign σ : ℤ) : ℂ)
      = ∑ σ : Equiv.Perm (Fin lam.card),
        ((P.dim lam : ℂ) / (lam.card.factorial : ℂ)) *
          (jtChar lam (permCast (rfl : lam.card = lam.card).symm
            σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        have hc : (P.e lam).coeff σ =
            ((P.dim lam : ℂ) / (lam.card.factorial : ℂ)) *
              jtChar lam
                (permCast (rfl : lam.card = lam.card).symm σ) := by
          rw [pe_eq_shape_e]
          exact shape_e_coeff P (⟨lam, rfl⟩ : Shape lam.card) σ
        rw [hc]
        ring
    _ = ((P.dim lam : ℂ) / (lam.card.factorial : ℂ)) *
        ∑ σ : Equiv.Perm (Fin lam.card),
          jtChar lam (permCast (rfl : lam.card = lam.card).symm
            σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
        rw [← Finset.mul_sum]
    _ = (P.dim lam : ℂ) * diagramSchur lam (superPS 0 1) := by
        rw [← hfrob]
        field_simp

/-- **Trivial self-braiding kills every non-row Schur functor**:
the central idempotent acts by the plain character sum, the Schur
specialisation at one even variable. -/
theorem schurKilled_of_braiding_id
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (P : SchurPackage.{v}) {X : A}
    (hβ : (β_ X X).hom = 𝟙 (X ⊗ X)) {lam : YoungDiagram}
    (hlam : 1 < lam.colLen 0) : SchurKilled P X lam := by
  classical
  rw [SchurKilled]
  have hβ' : (β_ X X).hom = (1 : ℂ) • 𝟙 (X ⊗ X) := by
    rw [one_smul, hβ]
  rw [permAlg_of_scalar hβ' (by norm_num)]
  rw [show (∑ σ : Equiv.Perm (Fin lam.card), (P.e lam).coeff σ *
      (if Equiv.Perm.sign σ = 1 then (1 : ℂ) else 1)) =
    ∑ σ : Equiv.Perm (Fin lam.card), (P.e lam).coeff σ from
    Finset.sum_congr rfl fun σ _ => by rw [ite_self, mul_one]]
  rw [sum_e_coeff, diagramSchur_superPS_row,
    ite_eq_right (by omega), mul_zero, zero_smul]

/-- **Self-braiding `−1` kills every non-column Schur functor**:
the central idempotent acts by the signed character sum, the Schur
specialisation at one odd variable. -/
theorem schurKilled_of_braiding_neg
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (P : SchurPackage.{v}) {X : A}
    (hβ : (β_ X X).hom = -(𝟙 (X ⊗ X))) {lam : YoungDiagram}
    (hlam : 1 < lam.rowLen 0) : SchurKilled P X lam := by
  classical
  rw [SchurKilled]
  have hβ' : (β_ X X).hom = (-1 : ℂ) • 𝟙 (X ⊗ X) := by
    rw [neg_one_smul, hβ]
  rw [permAlg_of_scalar hβ' (by norm_num)]
  rw [show (∑ σ : Equiv.Perm (Fin lam.card), (P.e lam).coeff σ *
      (if Equiv.Perm.sign σ = 1 then (1 : ℂ) else -1)) =
    ∑ σ : Equiv.Perm (Fin lam.card), (P.e lam).coeff σ *
      ((Equiv.Perm.sign σ : ℤ) : ℂ) from
    Finset.sum_congr rfl fun σ _ => by
      by_cases hs : Equiv.Perm.sign σ = 1
      · rw [ite_eq_left hs, hs]
        norm_num
      · rw [ite_eq_right hs,
          (Int.units_eq_one_or _).resolve_left hs]
        norm_num]
  rw [sum_e_coeff_sign, diagramSchur_superPS_col,
    ite_eq_right (by omega), mul_zero, zero_smul]

/-- The unit is killed at the two-cell column. -/
theorem schurKilled_unit_col
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (P : SchurPackage.{v}) :
    SchurKilled P (𝟙_ A) (colShape 2).val := by
  refine schurKilled_of_braiding_id P braiding_unit_self ?_
  have hmem : ((1, 0) : ℕ × ℕ) ∈ (colShape 2).val := by
    rw [YoungDiagram.mem_iff_lt_rowLen,
      colShape_rowLen_lt 2 one_lt_two]
    omega
  exact YoungDiagram.mem_iff_lt_colLen.mp hmem

/-- An odd line is killed at the two-cell row. -/
theorem schurKilled_odd_row
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (P : SchurPackage.{v}) {U : A}
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) :
    SchurKilled P U (rowShape 2).val := by
  refine schurKilled_of_braiding_neg P hβ ?_
  rw [rowShape_rowLen_zero]
  omega

section Sums

/-- `p + 1` biproduct copies of an object. -/
noncomputable def sumPow
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : A) : ℕ → A
  | 0 => X
  | k + 1 => sumPow X k ⊞ X

/-- Column bound for the one-column shape. -/
theorem colShape_colLen_le (m : ℕ) :
    (colShape m).val.colLen 0 ≤ m := by
  by_contra h
  have hmem : ((m, 0) : ℕ × ℕ) ∈ (colShape m).val :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  rw [YoungDiagram.mem_iff_lt_rowLen,
    colShape_rowLen_le m le_rfl] at hmem
  omega

/-- Iterated unit sums are killed at the corresponding column. -/
theorem schurKilled_sumPow_unit
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [HasBinaryBiproducts A]
    (P : SchurPackage.{v}) (p : ℕ) :
    SchurKilled P (sumPow (𝟙_ A) p) (colShape (p + 2)).val := by
  induction p with
  | zero => exact schurKilled_unit_col P
  | succ k ih =>
    refine SchurKilled.biprod P (p := k + 1) (q := 0) (r := 1)
      (s := 0) ?_ ?_ ?_ ?_ ih (schurKilled_unit_col P) ?_
    · exact colShape_colLen_le (k + 2)
    · exact colShape_rowLen_zero_le (k + 2)
    · exact colShape_colLen_le 2
    · exact colShape_rowLen_zero_le 2
    · rw [YoungDiagram.mem_iff_lt_rowLen,
        colShape_rowLen_lt (k + 3) (by omega)]
      omega

/-- Row bound for the one-row shape. -/
theorem rowShape_colLen_le (m : ℕ) :
    (rowShape m).val.colLen 0 ≤ 1 :=
  rowShape_colLen m

/-- Iterated odd sums are killed at the corresponding row. -/
theorem schurKilled_sumPow_odd
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [HasBinaryBiproducts A]
    (P : SchurPackage.{v}) {U : A}
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) (q : ℕ) :
    SchurKilled P (sumPow U q) (rowShape (q + 2)).val := by
  induction q with
  | zero => exact schurKilled_odd_row P hβ
  | succ k ih =>
    refine SchurKilled.biprod P (p := 0) (q := k + 1) (r := 0)
      (s := 1) ?_ ?_ ?_ ?_ ih (schurKilled_odd_row P hβ) ?_
    · exact rowShape_colLen_le (k + 2)
    · rw [rowShape_rowLen_zero]
    · exact rowShape_colLen_le 2
    · rw [rowShape_rowLen_zero]
    · rw [YoungDiagram.mem_iff_lt_rowLen, rowShape_rowLen_zero]
      omega

/-- **The vanishing half of Deligne 1.9, internally**: a direct
sum of `p + 1` unit copies and `q + 1` odd-line copies is killed
at every diagram containing the cell `(p + 1, q + 1)`. -/
theorem schurKilled_unit_odd
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [HasBinaryBiproducts A]
    (P : SchurPackage.{v}) {U : A}
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) (p q : ℕ)
    {lam : YoungDiagram} (hcell : (p + 1, q + 1) ∈ lam) :
    SchurKilled P (sumPow (𝟙_ A) p ⊞ sumPow U q) lam := by
  refine SchurKilled.biprod P (p := p + 1) (q := 0) (r := 0)
    (s := q + 1) ?_ ?_ ?_ ?_ (schurKilled_sumPow_unit P p)
    (schurKilled_sumPow_odd P hβ q) ?_
  · exact colShape_colLen_le (p + 2)
  · exact colShape_rowLen_zero_le (p + 2)
  · exact rowShape_colLen_le (q + 2)
  · rw [rowShape_rowLen_zero]
  · show (p + 1 + 0, 0 + (q + 1)) ∈ lam
    rw [Nat.add_zero, Nat.zero_add]
    exact hcell

end Sums

end RS
