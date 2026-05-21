/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Ring.Idempotent
import LeanPool.ArtinWedderburn.PrimeRing
import LeanPool.ArtinWedderburn.CornerRing
import LeanPool.ArtinWedderburn.Idempotents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Matrix units and the matrix-ring representation

A ring with abstract matrix units `eᵢⱼ` is isomorphic to a matrix ring over the
corner subring of `e₀₀`. This file packages the class `hasMatrixUnits`, the
construction of matrix units from `OrtIdemDiv`, and the explicit ring
isomorphism `R ≃+* Matrix (Fin n) (Fin n) (e₀₀ R e₀₀)`.
-/

namespace LeanPool.ArtinWedderburn

-- first we introduce the notion of rings with abstract matrix units
/-- Class packaging a system of `n × n` matrix units `eᵢⱼ` in a ring `R`. -/
class hasMatrixUnits (R : Type*) [Ring R] (n : ℕ) where
  /-- The matrix units indexed by `Fin n × Fin n`. -/
  es : Fin n → Fin n → R
  diag_sum_eq_one : ∑ i, es i i = 1
  mul_ij_kl_eq_kron_delta_jk_mul_es_il :
    ∀ i j k l, es i j * es k l = (if j = k then es i l else 0)

open hasMatrixUnits

variable (R : Type*) [Ring R]

-- in a nontrivial ring, 0 and 1 are different elements
theorem nontrivial_zero_not_one (nontriv : Nontrivial R) : (0 : R) ≠ (1 : R) :=
  haveI := nontriv; zero_ne_one

theorem nontrivial_ortidem_n_pos (nontriv : Nontrivial R) (ort_idem : OrtIdemDiv R) :
    0 < ort_idem.n := by
  by_contra n_zero
  push Not at n_zero
  haveI : IsEmpty (Fin ort_idem.n) := isEmpty_iff.mpr fun ⟨n, hn⟩ => absurd hn (by omega)
  have : (1 : R) = 0 := by
    calc (1 : R) = ∑ i : Fin ort_idem.n, ort_idem.f i := ort_idem.sum_one.symm
      _ = 0 := Fintype.sum_empty ort_idem.f
  exact nontrivial_zero_not_one R nontriv this.symm

theorem OrtIdem_imply_MatUnits' {n : ℕ} (hn : 0 < n)
    (diag_es : Fin n → R)
    (idem : (∀ i : Fin n, IsIdempotentElem (diag_es i)))
    (ort : (∀ i j : Fin n, i ≠ j → PairwiseOrthogonal (diag_es i) (diag_es j)))
    (sum_eq_one : ∑ i, diag_es i = 1)
    (row_es : Fin n → R)
    (row_in : ∀ i : Fin n, row_es i ∈ both_mul (diag_es ⟨0, hn⟩) (diag_es i))
    (col_es : Fin n → R)
    (col_in : ∀ i : Fin n, col_es i ∈ both_mul (diag_es i) (diag_es ⟨0, hn⟩))
    (comp1 : ∀ i, row_es i * col_es i = diag_es ⟨0, hn⟩)
    (comp2 : ∀ i, col_es i * row_es i = diag_es i) :
    ∃ mat_units : hasMatrixUnits R n, mat_units.es ⟨0, hn⟩ ⟨0, hn⟩ = diag_es ⟨0, hn⟩ := by
  let es := fun i j => (col_es i) * (row_es j)
  let diag_sum_eq_one : ∑ i, es i i = 1 := by
    calc ∑ i, es i i = ∑ i, col_es i * row_es i := rfl
      _ = ∑ i, diag_es i := by simp_rw [comp2]
      _ = 1 := sum_eq_one
  let delta : ∀ i j k l, es i j * es k l = (if j = k then es i l else 0) := by
    intro i j k l
    split_ifs with h
    · rw [h]
      have col_mul_diag : col_es i * diag_es ⟨0, hn⟩ = col_es i := by
        obtain ⟨r, hr⟩ := col_in i
        calc col_es i * diag_es ⟨0, hn⟩
            = diag_es i * r * (diag_es ⟨0, hn⟩ * diag_es ⟨0, hn⟩) := by rw [hr]; noncomm_ring
          _ = diag_es i * r * diag_es ⟨0, hn⟩ := by rw [idem ⟨0, hn⟩]
          _ = col_es i := by rw [hr]
      calc (col_es i * row_es k) * (col_es k * row_es l)
          = col_es i * (row_es k * col_es k) * row_es l := by noncomm_ring
        _ = col_es i * diag_es ⟨0, hn⟩ * row_es l := by rw [comp1 k]
        _ = col_es i * row_es l := by rw [col_mul_diag]
    · obtain ⟨r, hr⟩ := row_in j
      obtain ⟨s, hs⟩ := col_in k
      calc (col_es i * row_es j) * (col_es k * row_es l)
          = col_es i * (diag_es ⟨0, hn⟩ * r * (diag_es j * diag_es k) * s * diag_es ⟨0, hn⟩) *
              row_es l := by rw [hr, hs]; noncomm_ring
        _ = 0 := by rw [(ort j k h).left]; noncomm_ring
  let mat_units : hasMatrixUnits R n :=
    { es := es,
      diag_sum_eq_one := diag_sum_eq_one,
      mul_ij_kl_eq_kron_delta_jk_mul_es_il := delta }
  exact ⟨mat_units, comp2 ⟨0, hn⟩⟩

theorem lemma_2_20' (prime : IsPrimeRing R) (ort_idem : OrtIdemDiv R) (n_pos : 0 < ort_idem.n) :
    ∃ mat_units : hasMatrixUnits R ort_idem.n,
      mat_units.es ⟨0, n_pos⟩ ⟨0, n_pos⟩ = ort_idem.f ⟨0, n_pos⟩ := by
  let proof_uv := fun i =>
    lemma_2_19' prime (ort_idem.f ⟨0, n_pos⟩) (ort_idem.f i) (ort_idem.h ⟨0, n_pos⟩)
      (ort_idem.h i) (ort_idem.div ⟨0, n_pos⟩) (ort_idem.div i)
  exact @OrtIdem_imply_MatUnits' R _ ort_idem.n n_pos ort_idem.f ort_idem.h ort_idem.orthogonal
    ort_idem.sum_one (fun i => (proof_uv i).u) (fun i => (proof_uv i).u_mem)
    (fun i => (proof_uv i).v) (fun i => (proof_uv i).v_mem)
    (fun i => (proof_uv i).u_mul_v) (fun i => (proof_uv i).v_mul_u)

variable {n : ℕ} {hn : 0 < n} [mu : hasMatrixUnits R n]

-- abbreviations for the corner ring of the first matrix unit
theorem e00_idem : IsIdempotentElem (mu.es ⟨0, hn⟩ ⟨0, hn⟩) :=
  mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩

/-- The corner ring of the `(0, 0)` matrix unit. -/
abbrev e00_cornerring := CornerSubring (@e00_idem R _ n hn mu)

-- some trivial rewriting lemmas
lemma e00_cornerring_1 : (1 : CornerSubring (@e00_idem R _ n hn mu)) = mu.es ⟨0, hn⟩ ⟨0, hn⟩ := rfl

lemma e00e0i_eq_e_0i (i : Fin n) :
    mu.es ⟨0, hn⟩ ⟨0, hn⟩ * mu.es ⟨0, hn⟩ i = mu.es ⟨0, hn⟩ i := by
  rw [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il]
  simp

lemma ei0e00_eq_e_ei0 (i : Fin n) :
    mu.es i ⟨0, hn⟩ * mu.es ⟨0, hn⟩ ⟨0, hn⟩ = mu.es i ⟨0, hn⟩ := by
  rw [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il]
  simp only [↓reduceIte]

lemma ei0e0j_eq_eij (i j : Fin n) : mu.es i ⟨0, hn⟩ * mu.es ⟨0, hn⟩ j = mu.es i j := by
  rw [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il]
  simp only [↓reduceIte]

-- the projection of a's "i, j"-th element according to the (abstract) matrix units
/-- The `(i, j)`-component `e₀ᵢ * a * eⱼ₀` of `a : R` in the corner ring of `e₀₀`. -/
def ij_corner (i j : Fin n) (a : R) : @CornerSubring R _ _ (@e00_idem R _ n hn mu) :=
  ⟨es ⟨0, hn⟩ i * a * es j ⟨0, hn⟩, by
    rw [subring_mem_idem, ← mul_assoc, ← mul_assoc, e00e0i_eq_e_0i,
      mul_assoc, mul_assoc, mul_assoc, ei0e00_eq_e_ei0]⟩

-- abbreviations for the matrix ring over the corner ring of the first matrix unit
/-- The matrix ring `Matrix (Fin n) (Fin n) (e₀₀ R e₀₀)`. -/
abbrev matrix_corner := Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu)

-- define the map from R to matrix ring by a ↦ e_{0i}ae_{j0} for all i, j
/-- The map sending `a : R` to the matrix with entries `e₀ᵢ * a * eⱼ₀`. -/
def ring_to_matrix_ring (n : ℕ) (hn : 0 < n) (mu : hasMatrixUnits R n) :
    R → Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) :=
  fun a => fun i j => (ij_corner R i j a)

-- show that this map is additive
theorem ring_to_matrix_ring_additive (a b : R) :
    (ring_to_matrix_ring R n hn mu) (a + b) =
      (ring_to_matrix_ring R n hn mu) a + (ring_to_matrix_ring R n hn mu) b := by
  ext i j
  unfold ring_to_matrix_ring
  simp only [ij_corner, Matrix.add_apply, NonUnitalSubring.val_add]
  noncomm_ring

theorem matrixunit_iz_zi_eq_ii :
    ∀ i : Fin n, es i i = (mu.es i ⟨0, hn⟩) * (mu.es ⟨0, hn⟩ i) := by
  intro i
  rw [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il i ⟨0, hn⟩ ⟨0, hn⟩ i]
  simp

-- if a ring has matrix units then 1 = sum_i e_i0e0i
theorem one_eq_sum_es_00e_00e (n : ℕ) (hn : 0 < n) (mu : hasMatrixUnits R n) :
    1 = ∑ i, mu.es i ⟨0, hn⟩ * mu.es ⟨0, hn⟩ i := by
  rw [← mu.diag_sum_eq_one]
  have h (i : Fin n) : mu.es i i = (mu.es i ⟨0, hn⟩) * (mu.es ⟨0, hn⟩ i) :=
    matrixunit_iz_zi_eq_ii R i
  simp [h]

-- auxiliary lemma for lifting finite sums from the corner ring to R
theorem _lift_sum (f : Fin n → (@e00_cornerring R _ n hn mu)) :
    ((∑ i : Fin n, f i : (@e00_cornerring R _ n hn mu)) : R) = ∑ i : Fin n, (f i : R) :=
  AddSubmonoidClass.coe_finset_sum f Finset.univ

-- show that the map is multiplicative
theorem ring_to_matrix_ring_multiplicative (a b : R) :
    (ring_to_matrix_ring R n hn mu) (a * b) =
      (ring_to_matrix_ring R n hn mu) a * (ring_to_matrix_ring R n hn mu) b := by
  ext i j
  unfold ring_to_matrix_ring
  have hab : a * b = a * 1 * b := by simp
  rw [hab]
  rw [one_eq_sum_es_00e_00e R n hn mu]
  simp only [Matrix.mul_apply, SetLike.coe_eq_coe]
  unfold ij_corner
  apply Subtype.ext
  simp only [MulMemClass.mk_mul_mk]
  calc es ⟨0, hn⟩ i * ((a * ∑ i : Fin n, es i ⟨0, hn⟩ * es ⟨0, hn⟩ i) * b) * es j ⟨0, hn⟩
      = (es ⟨0, hn⟩ i * a) * (∑ i : Fin n, es i ⟨0, hn⟩ * es ⟨0, hn⟩ i) * (b * es j ⟨0, hn⟩) := by
        noncomm_ring
    _ = ∑ i_1 : Fin n, es ⟨0, hn⟩ i * a * (es i_1 ⟨0, hn⟩ * es ⟨0, hn⟩ i_1) *
          (b * es j ⟨0, hn⟩) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ j_1 : Fin n, es ⟨0, hn⟩ i * a * es j_1 ⟨0, hn⟩ *
          (es ⟨0, hn⟩ j_1 * b * es j ⟨0, hn⟩) := by
        apply Finset.sum_congr rfl; intro x _; noncomm_ring
  symm
  rw [_lift_sum]

-- auxiliary lemma to rewrite matrix 1
theorem matrix_one (S : Type*) [One S] [Zero S] [DecidableEq (Fin n)] :
    (1 : Matrix (Fin n) (Fin n) S) = (fun i j => if i = j then 1 else 0) := rfl

-- a criterion that element is 0 if all its matrix elements are 0
theorem corner_matrix_zero_equiv (a : R) :
    (∀ (i j : Fin n), (es i i) * a * (es j j) = 0) ↔ a = 0 := by
  constructor
  · intro hij
    have h : ∀ (i : Fin n), (es i i) * a = 0 := by
      intro i
      have : a = a * 1 := by simp
      rw [this, ← mu.diag_sum_eq_one, Finset.mul_sum, Finset.mul_sum]
      simp only [mul_assoc] at hij
      simp [hij]
    have hs : ∑ i : Fin n, (es i i) * a = 0 := by simp [h]
    rw [← Finset.sum_mul, mu.diag_sum_eq_one, one_mul] at hs
    exact hs
  · rintro rfl
    simp

-- same as previous but in a more applicable form
theorem corner_matrix_zero_crit (a : R) :
    (∀ (i j : Fin n), @ij_corner R _ n hn mu i j a = 0) → a = 0 := by
  rw [← (@corner_matrix_zero_equiv R _ n)]
  intro h i j
  have l' : mu.es ⟨0, hn⟩ i * a * mu.es j ⟨0, hn⟩ = 0 :=
    congrArg Subtype.val (h i j)
  have h'' : (mu.es i ⟨0, hn⟩ * mu.es ⟨0, hn⟩ i) * a *
      (mu.es j ⟨0, hn⟩ * mu.es ⟨0, hn⟩ j) = 0 := by
    have key : mu.es i ⟨0, hn⟩ * (mu.es ⟨0, hn⟩ i * a * mu.es j ⟨0, hn⟩) * mu.es ⟨0, hn⟩ j = 0 :=
      by rw [l']; noncomm_ring
    calc (mu.es i ⟨0, hn⟩ * mu.es ⟨0, hn⟩ i) * a * (mu.es j ⟨0, hn⟩ * mu.es ⟨0, hn⟩ j)
        = mu.es i ⟨0, hn⟩ * (mu.es ⟨0, hn⟩ i * a * mu.es j ⟨0, hn⟩) * mu.es ⟨0, hn⟩ j := by
          noncomm_ring
      _ = 0 := key
  simp only [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il i ⟨0, hn⟩ ⟨0, hn⟩ i,
    mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il j ⟨0, hn⟩ ⟨0, hn⟩ j, ↓reduceIte] at h''
  exact h''

-- the actual definition of the homomorphism
/-- The ring homomorphism from `R` to the matrix ring over its `e₀₀` corner ring. -/
def ring_to_matrix_ring_hom :
    R →+* Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) :=
  { toFun := ring_to_matrix_ring R n hn mu,
    map_one' := by
      ext i j
      simp only [SetLike.coe_eq_coe]
      unfold ring_to_matrix_ring ij_corner
      simp only [mul_one, matrix_one (@e00_cornerring R _ n hn mu),
        mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ i j ⟨0, hn⟩]
      split_ifs <;> rfl
    map_add' := ring_to_matrix_ring_additive R
    map_mul' := ring_to_matrix_ring_multiplicative R
    map_zero' := by
      ext i j
      unfold ring_to_matrix_ring ij_corner
      simp }

-- define the reverse map from matrix ring to R
/-- Reassemble a ring element from its matrix of corner components by summing
`eᵢ₀ * M i j * e₀ⱼ`. -/
def matrix_to_ring (n : ℕ) (hn : 0 < n) (mu : hasMatrixUnits R n) :
    Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) → R :=
  fun M => ∑ i, ∑ j, (mu.es i ⟨0, hn⟩) * M i j * (mu.es ⟨0, hn⟩ j)

-- lemma: multiplying e0k with ∑ ei0 f i = e0k ek0 fk = e00 f k
lemma e0k_left_mul_sum {k : Fin n} {f : Fin n → R} :
    mu.es ⟨0, hn⟩ k * ∑ i, mu.es i ⟨0, hn⟩ * f i = mu.es ⟨0, hn⟩ ⟨0, hn⟩ * f k := by
  rw [Finset.mul_sum]
  have hif : ∀ i,
      es ⟨0, hn⟩ k * (es i ⟨0, hn⟩ * f i) = if k = i then es ⟨0, hn⟩ ⟨0, hn⟩ * f k else 0 := by
    intro i
    rw [← mul_assoc, mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ k i ⟨0, hn⟩]
    split_ifs with h
    · simp only [h]
    · simp only [zero_mul]
  simp only [hif]
  exact Fintype.sum_ite_eq k fun _ ↦ es ⟨0, hn⟩ ⟨0, hn⟩ * f k

-- same but now from the right: ∑ f i e0i and ek0 = fk e0k ek0 = f k e00
lemma right_mul_sum_e0k {k : Fin n} {f : Fin n → R} :
    (∑ i, f i * mu.es ⟨0, hn⟩ i) * mu.es k ⟨0, hn⟩ = f k * mu.es ⟨0, hn⟩ ⟨0, hn⟩ := by
  rw [Finset.sum_mul]
  have hif : ∀ i,
      (f i * mu.es ⟨0, hn⟩ i) * mu.es k ⟨0, hn⟩ =
        if i = k then f k * mu.es ⟨0, hn⟩ ⟨0, hn⟩ else 0 := by
    intro i
    rw [mul_assoc, mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ i k ⟨0, hn⟩]
    split_ifs with h
    · simp only [h]
    · simp only [mul_zero]
  simp only [hif]
  exact Fintype.sum_ite_eq' k fun _ ↦ f k * es ⟨0, hn⟩ ⟨0, hn⟩

lemma matrixcorner1 :
    (1 : Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu)) =
      (fun i j => if i = j then (1 : (@e00_cornerring R _ n hn mu)) else 0) := rfl

lemma e00_unit (a : @e00_cornerring R _ n hn mu) :
    mu.es ⟨0, hn⟩ ⟨0, hn⟩ * (a : R) = a := by
  nth_rewrite 2 [show a = 1 * a from (one_mul a).symm]; rfl

lemma unit_e00 (a : @e00_cornerring R _ n hn mu) :
    (a : R) * mu.es ⟨0, hn⟩ ⟨0, hn⟩ = a := by
  nth_rewrite 2 [show a = a * 1 from (mul_one a).symm]; rfl

-- the main statement of this file: if a ring has matrix units then it is isomorphic to the
-- matrix ring over the corner ring of the first matrix unit
/-- A ring with matrix units `eᵢⱼ` is ring-isomorphic to the matrix ring over the corner
ring of `e₀₀`. -/
noncomputable
def ring_to_matrix_iso [mu : hasMatrixUnits R n] :
    R ≃+* Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) := by
  apply RingEquiv.ofBijective (ring_to_matrix_ring_hom R)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun a h => ?_, fun A => ?_⟩
  · apply @corner_matrix_zero_crit R _ n hn mu
    intro i j
    exact congrFun (congrFun h i) j
  · refine ⟨∑ i, ∑ j, es i ⟨0, hn⟩ * ((A i j : R) * es ⟨0, hn⟩ j), ?_⟩
    simp only [ring_to_matrix_ring_hom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    unfold ring_to_matrix_ring
    ext i j
    simp only [SetLike.coe_eq_coe]
    unfold ij_corner
    have h : es ⟨0, hn⟩ i *
          ∑ i : Fin n, ∑ j : Fin n, es i ⟨0, hn⟩ * ((A i j : R) * es ⟨0, hn⟩ j) =
        es ⟨0, hn⟩ i * ∑ i : Fin n, es i ⟨0, hn⟩ * ∑ j : Fin n,
            ((A i j : R) * es ⟨0, hn⟩ j) := by
      congr 1; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    simp only [h, e0k_left_mul_sum, mul_assoc, right_mul_sum_e0k, unit_e00, e00_unit]

-- Lemma 2.17
-- hypothesis: R is a ring with matrix units
-- conclusion: R is isomorphic to matrix ring over ring e_11Re_11
/-- Lemma 2.17: a ring with matrix units is ring-isomorphic to the matrix ring over the
corner ring of `e₀₀`. -/
noncomputable
def ring_with_matrix_units_isomorphic_to_matrix_ring (n : ℕ) (hn : 0 < n)
    (mu : hasMatrixUnits R n) :
    R ≃+* Matrix (Fin n) (Fin n) (@e00_cornerring R _ n hn mu) := ring_to_matrix_iso R

/-- Convert a proof of `HasMatrixUnits` (a `Prop`) into a `hasMatrixUnits` instance
(a `class`) via choice. -/
@[reducible]
noncomputable
def HasMatrixUnits_to_hasMatrixUnits (mu : HasMatrixUnits R n) : hasMatrixUnits R n := by
  let es := Classical.choose mu
  let h := Classical.choose_spec mu
  obtain ⟨h_sum, h_diag⟩ := h
  exact
    { es := es,
      diag_sum_eq_one := h_sum,
      mul_ij_kl_eq_kron_delta_jk_mul_es_il := h_diag }

end LeanPool.ArtinWedderburn
