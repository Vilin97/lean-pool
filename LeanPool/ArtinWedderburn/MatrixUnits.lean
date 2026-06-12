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
theorem nontrivial_zero_not_one (nontriv : Nontrivial R) : (0 : R) ≠ (1 : R) := by
  intro h
  obtain ⟨x, y, x_neq_y⟩ := nontriv.exists_pair_ne
  have x_eq_y : x = y := by
    calc
      x = x * 1 := by noncomm_ring
      _ = x * 0 := by rw [← h]
      _ = y * 0 := by noncomm_ring
      _ = y * 1 := by rw [h]
      _ = y := by noncomm_ring
  exact x_neq_y x_eq_y

theorem nontrivial_ortidem_n_pos (nontriv : Nontrivial R) (ort_idem : OrtIdemDiv R) :
    0 < ort_idem.n := by
  refine Nat.pos_of_ne_zero ?_
  by_contra n_zero
  have not_less_zero (n : ℕ) : ¬ n < ort_idem.n := by rw [n_zero]; exact Nat.not_lt_zero n
  have fin_empty : IsEmpty (Fin ort_idem.n) := isEmpty_iff.mpr (fun ⟨n, hn⟩ => not_less_zero n hn)
  have zero_eq_one : (1 : R) = (0 : R) := by
    haveI := fin_empty
    calc
      1 = ∑ i : Fin ort_idem.n, ort_idem.f i := Eq.symm ort_idem.sum_one
      _ = 0 := Fintype.sum_empty ort_idem.f
  exact nontrivial_zero_not_one R nontriv (Eq.symm zero_eq_one)

theorem OrtIdem_imply_MatUnits' {n : ℕ} (hn : 0 < n)
    (diag_es : Fin n → R)
    (idem : (∀ i : Fin n, IsIdempotentElem (diag_es i)))
    (ort : (∀ i j : Fin n, i ≠ j → PairwiseOrthogonal (diag_es i) (diag_es j)))
    (sum_eq_one : ∑ i, diag_es i = 1)
    (row_es : Fin n → R)
    (row_in : ∀ i : Fin n, row_es i ∈ bothMul (diag_es ⟨0, hn⟩) (diag_es i))
    (col_es : Fin n → R)
    (col_in : ∀ i : Fin n, col_es i ∈ bothMul (diag_es i) (diag_es ⟨0, hn⟩))
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
        calc
          col_es i * diag_es ⟨0, hn⟩ = diag_es i * r * (diag_es ⟨0, hn⟩ * diag_es ⟨0, hn⟩) := by
            rw [hr]; noncomm_ring
          _ = diag_es i * r * diag_es ⟨0, hn⟩ := by rw [idem ⟨0, hn⟩]
          _ = col_es i := by rw [hr]
      calc
        (col_es i * row_es k) * (col_es k * row_es l) =
            col_es i * (row_es k * col_es k) * row_es l := by noncomm_ring
        _ = col_es i * diag_es ⟨0, hn⟩ * row_es l := by rw [comp1 k]
        _ = col_es i * row_es l := by rw [col_mul_diag]
    · obtain ⟨r, hr⟩ := row_in j
      obtain ⟨s, hs⟩ := col_in k
      calc
        (col_es i * row_es j) * (col_es k * row_es l) =
            col_es i *
              (diag_es ⟨0, hn⟩ * r * (diag_es j * diag_es k) * s * diag_es ⟨0, hn⟩) *
              row_es l := by rw [hr, hs]; noncomm_ring
        _ = 0 := by rw [(ort j k h).left]; noncomm_ring
  let mat_units : hasMatrixUnits R n :=
    { es := es,
      diag_sum_eq_one := diag_sum_eq_one,
      mul_ij_kl_eq_kron_delta_jk_mul_es_il := delta }
  refine ⟨mat_units, ?_⟩
  calc
    mat_units.es ⟨0, hn⟩ ⟨0, hn⟩ = col_es ⟨0, hn⟩ * row_es ⟨0, hn⟩ := rfl
    _ = diag_es ⟨0, hn⟩ := by simp_rw [comp2]

theorem lemma_2_20' (prime : IsPrimeRing R) (ort_idem : OrtIdemDiv R) (n_pos : 0 < ort_idem.n) :
    ∃ mat_units : hasMatrixUnits R ort_idem.n,
      mat_units.es ⟨0, n_pos⟩ ⟨0, n_pos⟩ = ort_idem.f ⟨0, n_pos⟩ := by
  have proof_uv := fun i =>
    lemma219' prime (ort_idem.f ⟨0, n_pos⟩) (ort_idem.f i) (ort_idem.h ⟨0, n_pos⟩)
      (ort_idem.h i) (ort_idem.div ⟨0, n_pos⟩) (ort_idem.div i)
  let row_es : Fin ort_idem.n → R := fun i => (proof_uv i).u
  let col_es : Fin ort_idem.n → R := fun i => (proof_uv i).v
  let row_in := fun i => (proof_uv i).u_mem
  let col_in := fun i => (proof_uv i).v_mem
  let comp1 := fun i => (proof_uv i).u_mul_v
  let comp2 := fun i => (proof_uv i).v_mul_u
  have mat_units :=
    @OrtIdem_imply_MatUnits' R _ ort_idem.n n_pos ort_idem.f ort_idem.h ort_idem.orthogonal
      ort_idem.sum_one row_es row_in col_es col_in comp1 comp2
  exact mat_units

variable {n : ℕ} {hn : 0 < n} [mu : hasMatrixUnits R n]

-- abbreviations for the corner ring of the first matrix unit
theorem e00_idem : IsIdempotentElem (mu.es ⟨0, hn⟩ ⟨0, hn⟩) :=
  mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩

/-- The corner ring of the `(0, 0)` matrix unit. -/
abbrev e00Cornerring := CornerSubring (@e00_idem R _ n hn mu)

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
def ijCorner (i j : Fin n) (a : R) : @CornerSubring R _ _ (@e00_idem R _ n hn mu) :=
  ⟨es ⟨0, hn⟩ i * a * es j ⟨0, hn⟩, by
    rw [subring_mem_idem, ← mul_assoc, ← mul_assoc, e00e0i_eq_e_0i,
      mul_assoc, mul_assoc, mul_assoc, ei0e00_eq_e_ei0]⟩

-- abbreviations for the matrix ring over the corner ring of the first matrix unit
/-- The matrix ring `Matrix (Fin n) (Fin n) (e₀₀ R e₀₀)`. -/
abbrev matrixCorner := Matrix (Fin n) (Fin n) (@e00Cornerring R _ n hn mu)

-- define the map from R to matrix ring by a ↦ e_{0i}ae_{j0} for all i, j
/-- The map sending `a : R` to the matrix with entries `e₀ᵢ * a * eⱼ₀`. -/
def ringToMatrixRing (n : ℕ) (hn : 0 < n) (mu : hasMatrixUnits R n) :
    R → Matrix (Fin n) (Fin n) (@e00Cornerring R _ n hn mu) :=
  fun a => fun i j => (ijCorner R i j a)

-- show that this map is additive
theorem ring_to_matrix_ring_additive (a b : R) :
    (ringToMatrixRing R n hn mu) (a + b) =
      (ringToMatrixRing R n hn mu) a + (ringToMatrixRing R n hn mu) b := by
  ext i j
  unfold ringToMatrixRing
  simp only [ijCorner, Matrix.add_apply, NonUnitalSubring.val_add]
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
theorem _lift_sum (f : Fin n → (@e00Cornerring R _ n hn mu)) :
    ((∑ i : Fin n, f i : (@e00Cornerring R _ n hn mu)) : R) = ∑ i : Fin n, (f i : R) :=
  AddSubmonoidClass.coe_finsetSum f Finset.univ

-- show that the map is multiplicative
theorem ring_to_matrix_ring_multiplicative (a b : R) :
    (ringToMatrixRing R n hn mu) (a * b) =
      (ringToMatrixRing R n hn mu) a * (ringToMatrixRing R n hn mu) b := by
  ext i j
  unfold ringToMatrixRing
  have hab : a * b = a * 1 * b := by simp
  rw [hab]
  rw [one_eq_sum_es_00e_00e R n hn mu]
  simp only [Matrix.mul_apply, SetLike.coe_eq_coe]
  unfold ijCorner
  apply Subtype.ext
  simp only [MulMemClass.mk_mul_mk]
  calc
    es ⟨0, hn⟩ i * ((a * ∑ i : Fin n, es i ⟨0, hn⟩ * es ⟨0, hn⟩ i) * b) * es j ⟨0, hn⟩ =
        (es ⟨0, hn⟩ i * a) * (∑ i : Fin n, es i ⟨0, hn⟩ * es ⟨0, hn⟩ i) * (b * es j ⟨0, hn⟩) := by
      rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    _ = (∑ i_1 : Fin n, es ⟨0, hn⟩ i * a * (es i_1 ⟨0, hn⟩ * es ⟨0, hn⟩ i_1)) *
          (b * es j ⟨0, hn⟩) := by
      rw [Finset.mul_sum Finset.univ]
    _ = (∑ i_1 : Fin n, es ⟨0, hn⟩ i * a * (es i_1 ⟨0, hn⟩ * es ⟨0, hn⟩ i_1) *
          (b * es j ⟨0, hn⟩)) := by
      rw [Finset.sum_mul]
    _ = ∑ j_1 : Fin n, es ⟨0, hn⟩ i * a * es j_1 ⟨0, hn⟩ *
          (es ⟨0, hn⟩ j_1 * b * es j ⟨0, hn⟩) := by
      apply Finset.sum_congr
      · simp
      · intro x hx
        rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
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
      have a1 : a = a * 1 := by simp
      rw [a1, ← mu.diag_sum_eq_one]
      intro i
      rw [Finset.mul_sum Finset.univ, Finset.mul_sum Finset.univ]
      simp only [mul_assoc] at hij
      simp only [hij]
      apply Fintype.sum_eq_zero
      simp
    have hs : ∑ (i : Fin n), (es i i) * a = 0 := by
      simp only [h]
      exact Fintype.sum_eq_zero (fun a ↦ 0) (congrFun rfl)
    rw [← Finset.sum_mul Finset.univ] at hs
    rw [mu.diag_sum_eq_one] at hs
    simp only [one_mul] at hs
    exact hs
  · intro h
    rw [h]
    simp only [mul_zero, zero_mul, implies_true]

-- same as previous but in a more applicable form
theorem corner_matrix_zero_crit (a : R) :
    (∀ (i j : Fin n), @ijCorner R _ n hn mu i j a = 0) → a = 0 := by
  rw [← (@corner_matrix_zero_equiv R _ n)]
  intro h
  unfold ijCorner at h
  intro i j
  have h' : (mu.es i ⟨0, hn⟩ * (mu.es ⟨0, hn⟩ i * a * mu.es j ⟨0, hn⟩) * mu.es ⟨0, hn⟩ j) = 0 := by
    have l := h i j
    have l' : (mu.es ⟨0, hn⟩ i * a * mu.es j ⟨0, hn⟩) = 0 := congrArg Subtype.val l
    simp only [l']
    simp only [mul_zero, zero_mul]
  have h'' : (mu.es i ⟨0, hn⟩ * mu.es ⟨0, hn⟩ i) * a *
        (mu.es j ⟨0, hn⟩ * mu.es ⟨0, hn⟩ j) = 0 := by
    rw [← h']
    repeat rw [mul_assoc]
  simp only [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il i ⟨0, hn⟩ ⟨0, hn⟩ i] at h''
  simp only [mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il j ⟨0, hn⟩ ⟨0, hn⟩ j] at h''
  simp only [↓reduceIte] at h''
  exact h''

-- the actual definition of the homomorphism
/-- The ring homomorphism from `R` to the matrix ring over its `e₀₀` corner ring. -/
def ringToMatrixRingHom :
    R →+* Matrix (Fin n) (Fin n) (@e00Cornerring R _ n hn mu) :=
  { toFun := ringToMatrixRing R n hn mu,
    map_one' := by
      ext i j
      simp only [SetLike.coe_eq_coe]
      unfold ringToMatrixRing ijCorner
      simp only [mul_one]
      simp only [matrix_one (@e00Cornerring R _ n hn mu)]
      have h := mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, hn⟩ i j ⟨0, hn⟩
      simp only [h]
      split_ifs
      · rfl
      · rfl
    map_add' := ring_to_matrix_ring_additive R
    map_mul' := ring_to_matrix_ring_multiplicative R
    map_zero' := by
      ext i j
      simp only [Matrix.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero]
      unfold ringToMatrixRing ijCorner
      simp only [mul_zero, zero_mul]
      rfl }

-- define the reverse map from matrix ring to R
/-- Reassemble a ring element from its matrix of corner components by summing
`eᵢ₀ * M i j * e₀ⱼ`. -/
def matrixToRing (n : ℕ) (hn : 0 < n) (mu : hasMatrixUnits R n) :
    Matrix (Fin n) (Fin n) (@e00Cornerring R _ n hn mu) → R :=
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
    (1 : Matrix (Fin n) (Fin n) (@e00Cornerring R _ n hn mu)) =
      (fun i j => if i = j then (1 : (@e00Cornerring R _ n hn mu)) else 0) := rfl

lemma e00_unit (a : @e00Cornerring R _ n hn mu) :
    mu.es ⟨0, hn⟩ ⟨0, hn⟩ * (a : R) = a := by
  have h : 1 * a = a := one_mul a
  nth_rewrite 2 [← h]
  rfl

lemma unit_e00 (a : @e00Cornerring R _ n hn mu) :
    (a : R) * mu.es ⟨0, hn⟩ ⟨0, hn⟩ = a := by
  have h : a * 1 = a := mul_one a
  nth_rewrite 2 [← h]
  rfl

-- the main statement of this file: if a ring has matrix units then it is isomorphic to the
-- matrix ring over the corner ring of the first matrix unit
/-- A ring with matrix units `eᵢⱼ` is ring-isomorphic to the matrix ring over the corner
ring of `e₀₀`. -/
noncomputable
def ringToMatrixIso :
    R ≃+* Matrix (Fin n) (Fin n) (@e00Cornerring R _ n hn mu) := by
  apply RingEquiv.ofBijective (ringToMatrixRingHom R)
  refine ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (ringToMatrixRingHom R)).mpr ?_
    intro a
    simp only [ringToMatrixRingHom]
    unfold ringToMatrixRing
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    intro h
    apply @corner_matrix_zero_crit R _ n hn mu
    intro i j
    have fn_lemma {α β} {f g : α → β} (h : f = g) (a : α) : f a = g a := by rw [h]
    have h := fn_lemma h i
    exact fn_lemma h j
  · intro A
    let a : R := ∑ i, ∑ j, es i ⟨0, hn⟩ * ((A i j : R) * es ⟨0, hn⟩ j)
    refine ⟨a, ?_⟩
    simp only [ringToMatrixRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    unfold ringToMatrixRing
    ext i j
    unfold ijCorner
    simp only [a]
    have h : (es ⟨0, hn⟩ i *
          ∑ i : Fin n, ∑ j : Fin n, es i ⟨0, hn⟩ * ((A i j : R) * es ⟨0, hn⟩ j)) =
        (es ⟨0, hn⟩ i * ∑ i : Fin n, es i ⟨0, hn⟩ * ∑ j : Fin n,
            ((A i j : R) * es ⟨0, hn⟩ j)) := by
      rw [Finset.sum_congr]
      · rfl
      · intro i _
        rw [Finset.mul_sum]
    rw [h, e0k_left_mul_sum]
    simp only [mul_assoc]
    rw [right_mul_sum_e0k]
    simp only [unit_e00, e00_unit]

-- Lemma 2.17
-- hypothesis: R is a ring with matrix units
-- conclusion: R is isomorphic to matrix ring over ring e_11Re_11
/-- Lemma 2.17: a ring with matrix units is ring-isomorphic to the matrix ring over the
corner ring of `e₀₀`. -/
noncomputable
def ringWithMatrixUnitsIsomorphicToMatrixRing (n : ℕ) (hn : 0 < n)
    (mu : hasMatrixUnits R n) :
    R ≃+* Matrix (Fin n) (Fin n) (@e00Cornerring R _ n hn mu) := ringToMatrixIso R

/-- Convert a proof of `HasMatrixUnits` (a `Prop`) into a `hasMatrixUnits` instance
(a `class`) via choice. -/
@[reducible]
noncomputable
def HasMatrixUnitsToHasMatrixUnits (mu : HasMatrixUnits R n) : hasMatrixUnits R n := by
  let es := Classical.choose mu
  let h := Classical.choose_spec mu
  obtain ⟨h_sum, h_diag⟩ := h
  exact
    { es := es,
      diag_sum_eq_one := h_sum,
      mul_ij_kl_eq_kron_delta_jk_mul_es_il := h_diag }

end LeanPool.ArtinWedderburn
