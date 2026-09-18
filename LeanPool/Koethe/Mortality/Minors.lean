/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.SimpleRing.Principal
/-!
# Determinantal rank and sandwich compression

The mortality proof uses vanishing minors as a natural-number rank bound.
This avoids choosing bases for exterior powers.  All matrix products in this
file are ordinary products over a commutative scalar ring.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Matrix

namespace KoetheCounterexample.Mortality

section Determinants

variable {R : Type*} [CommRing R] {n m : Type*}
variable {r : ℕ}

/-- All minors of a specified size vanish.  Repeated rows or columns are allowed
in the indexing functions; their determinants are automatically zero. -/
def MinorsVanish (A : Matrix n n R) (r : ℕ) : Prop :=
  ∀ I J : Fin r → n, (A.submatrix I J).det = 0

theorem det_submatrix_zero_of_not_injective (A : Matrix n m R)
    (I : Fin r → n) (J : Fin r → m) (hI : ¬ Function.Injective I) :
    (A.submatrix I J).det = 0 := by
  classical
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hI
  exact Matrix.det_zero_of_row_eq hne (by ext c; simp [hij])

theorem injective_of_det_submatrix_ne_zero (A : Matrix n m R)
    (I : Fin r → n) (J : Fin r → m) (h : (A.submatrix I J).det ≠ 0) :
    Function.Injective I := by
  by_contra hi
  exact h (det_submatrix_zero_of_not_injective A I J hi)

theorem minorsVanish_above [Fintype n] (A : Matrix n n R) (h : Fintype.card n < r) :
    MinorsVanish A r := by
  intro I J
  apply det_submatrix_zero_of_not_injective A I J
  intro hi
  have := Fintype.card_le_of_injective I hi
  simp only [Fintype.card_fin] at this
  omega

theorem eq_zero_of_minorsVanish_one (A : Matrix n n R) (h : MinorsVanish A 1) :
    A = 0 := by
  ext i j
  simpa using h (fun _ => i) (fun _ => j)

/-- Expansion by multilinearity in the rows.  Unlike a compound-matrix formula,
this involves no ordering of subsets and no division by a factorial. -/
theorem det_mul_expand_rows [Fintype n] (A : Matrix (Fin r) n R) (B : Matrix n (Fin r) R) :
    (A * B).det = ∑ f : Fin r → n,
      (∏ i : Fin r, A i (f i)) * (B.submatrix f id).det := by
  classical
  let D := (Matrix.detRowAlternating : (Fin r → R) [⋀^Fin r]→ₗ[R] R).toMultilinearMap
  have heq : A * B = fun i => ∑ j : n, A i j • B j := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change D (A * B) = _
  rw [heq, D.map_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [D.map_smul_univ]
  rfl

/-- Restricting only the outside indices of a rectangular product. -/
theorem submatrix_mul_outer [Fintype n] {l o p q : Type*}
    (A : Matrix l n R) (B : Matrix n o R) (I : p → l) (J : q → o) :
    (A * B).submatrix I J = A.submatrix I id * B.submatrix id J := by
  simpa using (Matrix.submatrix_mul_equiv A B I (Equiv.refl n) J).symm

theorem det_map {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix (Fin r) (Fin r) R) :
    (A.map φ).det = φ A.det := (φ.map_det A).symm

end Determinants

section Compression

variable {K : Type*} [Field K] {n : Type*} {r : ℕ}

/-- A nonzero `r`-minor, together with vanishing `(r+1)`-minors, gives the
usual pivot factorization.  The inverse is taken only over a field. -/
theorem pivot_factorization (P : Matrix n n K)
    (I J : Fin r → n) (hp : (P.submatrix I J).det ≠ 0)
    (hnext : MinorsVanish P (r + 1)) :
    P = P.submatrix id J * (P.submatrix I J)⁻¹ * P.submatrix I id := by
  classical
  let A := P.submatrix I J
  let _ : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hp)
  ext i j
  let B : Matrix (Fin r) (Fin 1) K := fun a _ => P (I a) j
  let C : Matrix (Fin 1) (Fin r) K := fun _ b => P i (J b)
  let D : Matrix (Fin 1) (Fin 1) K := fun _ _ => P i j
  let I' : Fin r ⊕ Fin 1 → n := Sum.elim I (fun _ => i)
  let J' : Fin r ⊕ Fin 1 → n := Sum.elim J (fun _ => j)
  have hz : (P.submatrix I' J').det = 0 := by
    let e : Fin (r + 1) ≃ (Fin r ⊕ Fin 1) := finSumFinEquiv.symm
    have h := hnext (I' ∘ e) (J' ∘ e)
    simpa only [← Matrix.submatrix_submatrix, Matrix.det_submatrix_equiv_self] using h
  have hblocks : P.submatrix I' J' = Matrix.fromBlocks A B C D := by
    ext a b
    cases a <;> cases b <;> rfl
  rw [hblocks, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
    Matrix.det_unique (D - C * A⁻¹ * B)] at hz
  have hz' := (mul_eq_zero.mp hz).resolve_left hp
  change P i j - (P.submatrix id J * (P.submatrix I J)⁻¹ *
    P.submatrix I id) i j = 0 at hz'
  exact sub_eq_zero.mp hz'

/-- The pivot detects every `r`-minor of a sandwiched product. -/
theorem sandwich_minors_vanish_field [Fintype n] (P C : Matrix n n K)
    (I J : Fin r → n) (hp : (P.submatrix I J).det ≠ 0)
    (hnext : MinorsVanish P (r + 1))
    (hz : ((P * C * P).submatrix I J).det = 0) :
    MinorsVanish (P * C * P) r := by
  classical
  let A := P.submatrix I J
  let U := P.submatrix id J
  let V := P.submatrix I id
  have hP : P = U * A⁻¹ * V := pivot_factorization P I J hp hnext
  have hT : (V * C * U).det = 0 := by
    simpa only [submatrix_mul_outer, Matrix.submatrix_submatrix,
      Matrix.submatrix_id_id, Function.comp_id, Function.id_comp] using hz
  have hB : P * C * P = U * A⁻¹ * (V * C * U) * A⁻¹ * V := by
    calc
      P * C * P = (U * A⁻¹ * V) * C * (U * A⁻¹ * V) :=
        congrArg₂ (fun X Y => X * C * Y) hP hP
      _ = _ := by simp only [Matrix.mul_assoc]
  intro I' J'
  rw [hB]
  simp only [submatrix_mul_outer, Matrix.submatrix_id_id]
  simp only [Matrix.det_mul, hT, mul_zero, zero_mul]

end Compression

section DomainCompression

variable {R : Type*} [CommRing R] [IsDomain R] {n : Type*} [Fintype n] {r : ℕ}

/-- Polynomial/domain version of sandwich compression.  Localization is used
only to invert the fixed nonzero pivot; injectivity returns the identity to
its original commutative domain. -/
theorem sandwich_minors_vanish (P C : Matrix n n R)
    (I J : Fin r → n) (hp : (P.submatrix I J).det ≠ 0)
    (hnext : MinorsVanish P (r + 1))
    (hz : ((P * C * P).submatrix I J).det = 0) :
    MinorsVanish (P * C * P) r := by
  classical
  let φ := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hp' : ((P.map φ).submatrix I J).det ≠ 0 := by
    rw [Matrix.submatrix_map, det_map]
    exact fun h => hp (hφ (by simpa using h))
  have hnext' : MinorsVanish (P.map φ) (r + 1) := by
    intro I' J'
    rw [Matrix.submatrix_map, det_map, hnext I' J', map_zero]
  have hz' : (((P.map φ) * (C.map φ) * (P.map φ)).submatrix I J).det = 0 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.submatrix_map,
      det_map, hz, map_zero]
  have h := sandwich_minors_vanish_field (P.map φ) (C.map φ) I J hp' hnext' hz'
  intro I' J'
  apply hφ
  simpa only [map_zero, ← det_map, ← Matrix.submatrix_map,
    Matrix.map_mul] using h I' J'

end DomainCompression

end KoetheCounterexample.Mortality

end
