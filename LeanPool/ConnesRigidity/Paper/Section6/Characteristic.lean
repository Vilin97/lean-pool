/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

This file contains the concrete algebraic characteristic-subgroup input for
the Zhou-shaped construction. The proof is independently written from the
paper's cited public mathematical argument in Section 6.
-/

import LeanPool.ConnesRigidity.Construction.PaperActionInstances

/-!
The characteristic component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperCharacteristic

open Construction
open Construction.PaperKernel

noncomputable section

/--
The `R` construction used in the Connes rigidity formalization.
-/
abbrev R := SpecialLinear.R
/--
The `I` construction used in the Connes rigidity formalization.
-/
abbrev I := Fin 3
/--
The `M` construction used in the Connes rigidity formalization.
-/
abbrev M := Matrix I I R
/--
The `G` construction used in the Connes rigidity formalization.
-/
abbrev G := SpecialLinear.SL3

/--
The `paperTransvection` construction used in the Connes rigidity formalization.
-/
def paperTransvection (i j : I) (hij : i ≠ j) (f : R) : G :=
  Matrix.SpecialLinearGroup.transvection hij f

/- The characteristic-two square identity for the transvection (Zhou §6). -/
theorem paperTransvection_square (i j : I) (hij : i ≠ j) (f : R) :
    paperTransvection i j hij f * paperTransvection i j hij f = 1 := by
  apply Subtype.ext
  have hself : Matrix.single i j f + Matrix.single i j f = 0 := by
    ext r s
    exact CharTwo.add_self_eq_zero _
  change ((1 : M) + Matrix.single i j f) *
    ((1 : M) + Matrix.single i j f) = 1
  simp only [Matrix.mul_add, Matrix.add_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, one_mul, mul_one,
    add_zero]
  rw [add_assoc, hself, add_zero]

theorem paperDiagonalEntryEquation (i j : I) (hij : i ≠ j) (b : G) (f : R)
    (hcomm : Commute b
      (paperTransvection i j hij f * b * (paperTransvection i j hij f)⁻¹)) :
    f * ((b : M) * (b : M)) j i +
        f ^ 2 * ((b : M) j i * (b : M) j i) = 0 := by
  have hinv : (paperTransvection i j hij f)⁻¹ = paperTransvection i j hij f := by
    apply inv_eq_of_mul_eq_one_left
    exact paperTransvection_square i j hij f
  have hmat := congrArg (fun z : G => (z : M)) hcomm.eq
  rw [hinv] at hmat
  change (b : M) *
      (((1 : M) + Matrix.single i j f) * (b : M) *
        ((1 : M) + Matrix.single i j f)) =
    (((1 : M) + Matrix.single i j f) * (b : M) *
      ((1 : M) + Matrix.single i j f)) * (b : M) at hmat
  have hentry := congrArg (fun m : M => m i i) hmat
  simp only [Matrix.mul_add, Matrix.add_mul, one_mul, mul_one] at hentry
  simp only [Matrix.single_mul_mul_single, Matrix.add_apply, ne_eq, hij,
    not_false_eq_true, Matrix.mul_single_apply_of_ne, add_zero,
    Matrix.single_mul_apply_same] at hentry
  have hBBE : ((b : M) * (b : M) * Matrix.single i j f) i i = 0 := by
    apply Matrix.mul_single_apply_of_ne
    exact hij
  have hEBB : (Matrix.single i j f * (b : M) * (b : M)) i i =
      f * ((b : M) * (b : M)) j i := by
    rw [Matrix.mul_assoc]
    simp
  have hBEB : ((b : M) * Matrix.single i j f * (b : M)) i i =
      ((b : M) * (Matrix.single i j f * (b : M))) i i := by
    rw [← Matrix.mul_assoc]
  have hB2E : ((b : M) * ((b : M) * Matrix.single i j f)) i i = 0 := by
    rw [← Matrix.mul_assoc]
    exact hBBE
  rw [hB2E, hEBB, hBEB] at hentry
  linear_combination -hentry

theorem paperOffDiagonalZeroOfMemNormalCommuting
    (B : Subgroup G) (hBnormal : B.Normal)
    (hcommute : ∀ x y : B, x * y = y * x)
    (b : G) (hb : b ∈ B) {i j : I} (hij : i ≠ j) :
    (b : M) j i = 0 := by
  let hconj (f : R) : G := paperTransvection i j hij f * b *
    (paperTransvection i j hij f)⁻¹
  have hcomm (f : R) : Commute b (hconj f) := by
    have hmem : hconj f ∈ B := by
      exact hBnormal.conj_mem b hb (paperTransvection i j hij f)
    change b * hconj f = hconj f * b
    exact congrArg Subtype.val (hcommute ⟨b, hb⟩ ⟨hconj f, hmem⟩)
  have hone := paperDiagonalEntryEquation i j hij b 1 (by
    simpa [hconj] using hcomm 1)
  have ht := paperDiagonalEntryEquation i j hij b Polynomial.X (by
    simpa [hconj] using hcomm Polynomial.X)
  simp only [one_mul, one_pow] at hone
  have hscaled : Polynomial.X * (((b : M) * (b : M)) j i) +
      Polynomial.X * ((b : M) j i * (b : M) j i) = 0 := by
    calc
      Polynomial.X * (((b : M) * (b : M)) j i) +
          Polynomial.X * ((b : M) j i * (b : M) j i) =
          Polynomial.X * ((((b : M) * (b : M)) j i) +
            (b : M) j i * (b : M) j i) := by rw [mul_add]
      _ = Polynomial.X * 0 := congrArg (fun z : R => Polynomial.X * z) hone
      _ = 0 := mul_zero _
  have hsum :
      (Polynomial.X * (((b : M) * (b : M)) j i) +
          Polynomial.X ^ 2 * ((b : M) j i * (b : M) j i)) +
        (Polynomial.X * (((b : M) * (b : M)) j i) +
          Polynomial.X * ((b : M) j i * (b : M) j i)) = 0 := by
    rw [ht, hscaled, add_zero]
  have hpoly : (Polynomial.X + Polynomial.X ^ 2) *
      ((b : M) j i * (b : M) j i) = 0 := by
    calc
      (Polynomial.X + Polynomial.X ^ 2) *
          ((b : M) j i * (b : M) j i) =
          (Polynomial.X * (((b : M) * (b : M)) j i) +
            Polynomial.X ^ 2 * ((b : M) j i * (b : M) j i)) +
            (Polynomial.X * (((b : M) * (b : M)) j i) +
              Polynomial.X * ((b : M) j i * (b : M) j i)) := by
          rw [add_mul]
          have hself : Polynomial.X * (((b : M) * (b : M)) j i) +
              Polynomial.X * (((b : M) * (b : M)) j i) = 0 :=
            CharTwo.add_self_eq_zero _
          calc
            Polynomial.X * ((b : M) j i * (b : M) j i) +
                Polynomial.X ^ 2 * ((b : M) j i * (b : M) j i) =
                (Polynomial.X * (((b : M) * (b : M)) j i) +
                  Polynomial.X * (((b : M) * (b : M)) j i)) +
                  (Polynomial.X * ((b : M) j i * (b : M) j i) +
                  Polynomial.X ^ 2 * ((b : M) j i * (b : M) j i)) := by
              rw [hself, zero_add]
            _ = _ := by abel
      _ = 0 := hsum
  have hcoef : (Polynomial.X : R) + (Polynomial.X : R) ^ 2 ≠ 0 := by
    intro hzero
    have hc := congrArg (fun p : R => p.coeff 2) hzero
    norm_num [Polynomial.coeff_X, Polynomial.coeff_X_pow] at hc
  have hsquare : (b : M) j i * (b : M) j i = 0 :=
    (mul_eq_zero.mp hpoly).resolve_left hcoef
  rcases mul_eq_zero.mp hsquare with hzero | hzero
  · exact hzero
  · exact hzero

private theorem paperPolynomialUnitEqOne {p : R} (hp : IsUnit p) : p = 1 := by
  have hdegree : p.degree = 0 := Polynomial.degree_eq_zero_of_isUnit hp
  have hpC : p = Polynomial.C (p.coeff 0) :=
    Polynomial.eq_C_of_degree_eq_zero hdegree
  have hcoeff : p.coeff 0 = 1 := by
    have hcunit : IsUnit (p.coeff 0) := by
      rw [hpC] at hp
      exact Polynomial.isUnit_C.mp hp
    have hcne : p.coeff 0 ≠ 0 := isUnit_iff_ne_zero.mp hcunit
    have hval : (p.coeff 0).val < 2 := ZMod.val_lt _
    have hvalne : (p.coeff 0).val ≠ 0 := by
      intro hzero
      apply hcne
      exact (ZMod.val_eq_zero _).mp hzero
    have hvalone : (p.coeff 0).val = 1 := by omega
    apply ZMod.val_injective 2
    simpa [ZMod.val_one] using hvalone
  rw [hpC, hcoeff]
  simp

theorem paperSL3NoNontrivialAbelianNormalSubgroup
    (B : Subgroup G) (hBnormal : B.Normal)
    (hcommute : ∀ x y : B, x * y = y * x) : B = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  have hoff : ∀ {i j : I}, i ≠ j → (b : M) i j = 0 := by
    intro i j hij
    exact paperOffDiagonalZeroOfMemNormalCommuting B hBnormal hcommute b hb
      hij.symm
  have hdiag : (b : M) = Matrix.diagonal (fun i => (b : M) i i) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · simpa [Matrix.diagonal, hij] using hoff hij
  have hprod : (b : M) 0 0 * ((b : M) 1 1 * (b : M) 2 2) = 1 := by
    have hdet := b.property
    rw [hdiag] at hdet
    simpa [Matrix.det_diagonal, Fin.prod_univ_three, mul_assoc] using hdet
  have hunit0 : IsUnit ((b : M) 0 0) :=
    IsUnit.of_mul_eq_one ((b : M) 1 1 * (b : M) 2 2) hprod
  have hunit1 : IsUnit ((b : M) 1 1) := by
    apply IsUnit.of_mul_eq_one ((b : M) 0 0 * (b : M) 2 2)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod
  have hunit2 : IsUnit ((b : M) 2 2) := by
    apply IsUnit.of_mul_eq_one ((b : M) 0 0 * (b : M) 1 1)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod
  apply Subtype.ext
  rw [hdiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [paperPolynomialUnitEqOne hunit0,
      paperPolynomialUnitEqOne hunit1, paperPolynomialUnitEqOne hunit2]

end
end PaperCharacteristic
end Connes
