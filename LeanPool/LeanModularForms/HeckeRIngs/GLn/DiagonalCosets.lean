/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.GLn.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Determinant

/-!
# Diagonal Coset Representatives for GL_n Hecke Ring

Defines the double coset elements `T(a₁,...,aₙ)` corresponding to diagonal matrices
`diag[a₁,...,aₙ]` in the Hecke ring, and proves that every double coset has a diagonal
representative (elementary divisor theorem / Smith normal form).

## Main definitions

* `diagMat` — diagonal matrix `diag[a₁,...,aₙ]` as element of `GL_n(ℚ)`
* `DivChain` — the divisibility chain condition `a₁ | a₂ | ⋯ | aₙ`
* `TDiag` — double coset `Γ · diag[a₁,...,aₙ] · Γ`
* `TElem` — Hecke ring basis element `T(a₁,...,aₙ)` with coefficient 1

## Main results

* `exists_diagonal_representative` — every double coset has a diagonal representative
  with the divisibility chain `a₁ | a₂ | ⋯ | aₙ` (Smith normal form)
* `diagonal_representative_unique` — uniqueness of elementary divisors
* `T_diag_span` — `T(a₁,...,aₙ)` elements span the Hecke ring

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.2
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

section Diagonal

variable (n : ℕ)

/-- The diagonal `GL_n(ℚ)` matrix with natural number entries.
    Positivity is needed to ensure the determinant is nonzero. -/
private def natDiagDetNeZero (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (Matrix.diagonal (fun i => (a i : ℚ))).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact ne_of_gt (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (ha i))

/-- The diagonal `GL_n(ℚ)` element `diag(a₁,...,aₙ)` with positive natural number entries.
Returns `1` (the identity matrix) when the positivity condition `∀ i, 0 < a i` fails;
this is a junk value that simplifies the API by avoiding an explicit positivity argument. -/
noncomputable def diagMat (a : Fin n → ℕ) : GL (Fin n) ℚ :=
  if h : ∀ i, 0 < a i then
    GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal (fun i => (a i : ℚ)))
      (natDiagDetNeZero n a h)
  else 1

@[simp] lemma diagMat_val (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(diagMat n a) : Matrix (Fin n) (Fin n) ℚ) =
    Matrix.diagonal (fun i => (a i : ℚ)) := by unfold diagMat; rw [dif_pos ha]; rfl

lemma diagMat_hasIntEntries (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) : HasIntEntries n (diagMat n a) :=
  ⟨Matrix.diagonal (fun i => (a i : ℤ)),
    by ext i j; simp [ha, Matrix.diagonal_apply, Matrix.map_apply]⟩

lemma diagMat_det_pos (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    0 < (↑(diagMat n a) : Matrix (Fin n) (Fin n) ℚ).det := by
  simp only [ha, implies_true, diagMat_val, det_diagonal]
  exact Finset.prod_pos (fun i _ => by positivity [ha i])

lemma diagMat_mem_posDetInt (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    diagMat n a ∈ posDetIntSubmonoid n :=
  ⟨diagMat_hasIntEntries n a ha, diagMat_det_pos n a ha⟩

lemma diagMat_det (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(diagMat n a) : Matrix (Fin n) (Fin n) ℚ).det = ∏ i, (a i : ℚ) := by
  simp [ha, Matrix.det_diagonal]

lemma diagMat_one : diagMat n (fun _ => 1) = 1 := by
  simp only [diagMat, dif_pos (fun _ => Nat.one_pos)]
  apply Units.ext
  ext i j; simp [Matrix.one_apply]

end Diagonal

variable (n : ℕ)

section HeckeDiagonal

variable [NeZero n]

/-- The diagonal matrix `diag(a₁,...,aₙ)` as an element of Shimura's `Δ`. -/
noncomputable def diagMatDelta (a : Fin n → ℕ) : (GLPair n).Δ :=
  if h : ∀ i, 0 < a i then
    ⟨diagMat n a, diagMat_mem_posDetInt n a h⟩
  else ⟨1, (GLPair n).Δ.one_mem⟩

@[simp] lemma diagMat_delta_val (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(diagMatDelta n a) : GL (Fin n) ℚ) = diagMat n a := by
  simp only [diagMatDelta, dif_pos ha]

end HeckeDiagonal

/-- The divisibility chain condition `a₁ | a₂ | ... | aₙ` for positive integer sequences. -/
def DivChain (a : Fin n → ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < n), a ⟨i, by omega⟩ ∣ a ⟨i + 1, hi⟩

lemma divChain_const (c : ℕ) : DivChain n (fun _ => c) :=
  fun _ _ => dvd_refl _

/-- Transitivity of the divisibility chain: `a i ∣ a j` whenever `i ≤ j`. -/
lemma divChain_dvd {a : Fin n → ℕ} (ha : DivChain n a) {i j : Fin n} (hij : i ≤ j) :
    a i ∣ a j := by
  suffices h : ∀ (d : ℕ) (hd : i.val + d < n), a i ∣ a ⟨i.val + d, hd⟩ by
    have := h (j.val - i.val) (by omega)
    simp only [Nat.add_sub_cancel' (Fin.val_le_of_le hij)] at this; exact this
  intro d
  induction d with
  | zero =>
    intro hd; change _ ∣ a ⟨i.val, hd⟩; rfl
  | succ m ih =>
    intro hd
    exact dvd_trans (ih (by omega)) (ha (i.val + m) hd)

/-- The quotient `a j / a i` is positive when `i ≤ j` in a divisibility chain. -/
lemma divChain_div_pos {a : Fin n → ℕ} (hpos : ∀ i, 0 < a i) (ha : DivChain n a) {i j : Fin n}
    (hij : i ≤ j) : 0 < a j / a i :=
  Nat.div_pos (Nat.le_of_dvd (hpos j) (divChain_dvd n ha hij)) (hpos i)

section TDiag

variable {n} [NeZero n]

/-- `T(a₁,...,aₙ) = Γ · diag[a₁,...,aₙ] · Γ` as a double coset.
Hypotheses `ha` (positivity) and `hdiv` (divisibility chain) belong in lemmas,
not the definition; the result is junk when they fail. -/
noncomputable def TDiag (a : Fin n → ℕ) : HeckeCoset (GLPair n) :=
  ⟦diagMatDelta n a⟧

/-- `T(a₁,...,aₙ)` as a Hecke ring element with coefficient `1`. -/
noncomputable def TElem (a : Fin n → ℕ) : HeckeAlgebra n :=
  Finsupp.single (TDiag a) 1

/-- The representative of TDiag lies in the double coset of diagMat. -/
lemma T_diag_rep_mem_doubleCoset (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (HeckeCoset.rep (TDiag a) : GL (Fin n) ℚ) ∈ DoubleCoset.doubleCoset
      (diagMat n a : GL (Fin n) ℚ) (GLPair n).H (GLPair n).H := by
  have h1 := HeckeCoset.rep_mem (TDiag a)
  rw [HeckeCoset.toSet_eq_rep] at h1
  have h2 : (⟦HeckeCoset.rep (TDiag a)⟧ : HeckeCoset (GLPair n)) = TDiag a :=
    Quotient.out_eq _
  simp only [TDiag] at h2
  have h3 : DoubleCoset.doubleCoset (HeckeCoset.rep (TDiag a) : GL (Fin n) ℚ)
      (GLPair n).H (GLPair n).H =
    DoubleCoset.doubleCoset (↑(diagMatDelta n a) : GL (Fin n) ℚ)
      (GLPair n).H (GLPair n).H :=
    (HeckeCoset.eq_iff _ _).mp h2
  rw [h3] at h1; rwa [diagMat_delta_val n a ha] at h1

/-- Decompose the TDiag representative as L * diagMat * R with L, R in H. -/
lemma T_diag_rep_decompose (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    ∃ (L : GL (Fin n) ℚ), L ∈ (GLPair n).H ∧ ∃ (R : GL (Fin n) ℚ), R ∈ (GLPair n).H ∧
      (HeckeCoset.rep (TDiag a) : GL (Fin n) ℚ) = L * diagMat n a * R :=
  DoubleCoset.mem_doubleCoset.mp (T_diag_rep_mem_doubleCoset a ha)

lemma T_diag_ones : TDiag (fun _ : Fin n => 1) = HeckeCoset.one (GLPair n) := by
  simp only [TDiag, HeckeCoset.one]
  rw [HeckeCoset.eq_iff]
  simp only [diagMatDelta, dif_pos (fun _ => Nat.one_pos)]
  congr 1; exact diagMat_one n

/-- Two diagonal double cosets are equal iff the underlying double cosets in `GL_n(ℚ)` coincide. -/
lemma T_diag_eq_iff (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    TDiag a = TDiag b ↔
    DoubleCoset.doubleCoset (diagMat n a : GL (Fin n) ℚ) (SLnZSubgroup n) (SLnZSubgroup n) =
    DoubleCoset.doubleCoset (diagMat n b : GL (Fin n) ℚ) (SLnZSubgroup n) (SLnZSubgroup n) := by
  constructor
  · intro h; have := congr_arg HeckeCoset.toSet h
    simp only [TDiag, HeckeCoset.toSet_mk, diagMat_delta_val n a ha,
      diagMat_delta_val n b hb] at this
    exact this
  · intro h
    simp only [TDiag]
    rw [HeckeCoset.eq_iff]
    simp only [diagMat_delta_val n a ha, diagMat_delta_val n b hb]; exact h

end TDiag

section Transvections

private lemma transvection_det_ne_zero {i j : Fin n} (hij : i ≠ j) (c : ℤ) :
    ((Matrix.TransvectionStruct.mk i j hij c).toMatrix.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
  rw [det_intMat_cast, (Matrix.TransvectionStruct.mk i j hij c).det]; exact one_ne_zero

/-- An elementary transvection `I + c * E_{ij}` as an element of `GL_n(ℚ)`. -/
noncomputable def transvectionGL {i j : Fin n} (hij : i ≠ j) (c : ℤ) : GL (Fin n) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero
    ((Matrix.TransvectionStruct.mk i j hij c).toMatrix.map (Int.cast : ℤ → ℚ))
    (transvection_det_ne_zero n hij c)

lemma transvectionGL_hasIntEntries {i j : Fin n} (hij : i ≠ j) (c : ℤ) :
    HasIntEntries n (transvectionGL n hij c) :=
  ⟨(Matrix.TransvectionStruct.mk i j hij c).toMatrix, rfl⟩

lemma transvectionGL_mem_SLnZ {i j : Fin n} (hij : i ≠ j) (c : ℤ) :
    transvectionGL n hij c ∈ SLnZSubgroup n := by
  rw [MonoidHom.mem_range]
  refine ⟨⟨(Matrix.TransvectionStruct.mk i j hij c).toMatrix,
    (Matrix.TransvectionStruct.mk i j hij c).det⟩, ?_⟩; apply Units.ext
  simp [mapGL_coe_matrix, algebraMap_int_eq, transvectionGL]

end Transvections

section SmithNormalForm

private lemma mulVecLin_injective_of_det_ne_zero (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) : Function.Injective A.mulVecLin := by
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro v hv
  have h1 : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rw [hv, mulVec_zero] at h1; ext i
  have := congr_fun h1.symm i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left hdet

private lemma finrank_range_mulVecLin (A : Matrix (Fin n) (Fin n) ℤ) (hdet : A.det ≠ 0) :
    Module.finrank ℤ (LinearMap.range A.mulVecLin) = Module.finrank ℤ (Fin n → ℤ) :=
  LinearMap.finrank_range_of_inj (mulVecLin_injective_of_det_ne_zero (n := n) A hdet)

/-- Given `L * A * Q = diag(d)` with `d` positive and `det(L) * det(Q) = 1`, produce
`SL_n(ℤ)` matrices `L', Q'` with `L' * A * Q' = diag(d)`. When both determinants are
already `+1` the original matrices work; when both are `-1` a coordinate-flip corrects
the signs. -/
private lemma sign_correct_unit_transform (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ)
    (L_mat Q_mat : Matrix (Fin n) (Fin n) ℤ) (hd_pos : ∀ i, 0 < d i)
    (hL_eq : L_mat * A * Q_mat = Matrix.diagonal d) (hLQ_one : L_mat.det * Q_mat.det = 1)
    (hL_unit : IsUnit L_mat.det) (hQ_unit : IsUnit Q_mat.det) :
    ∃ (L R : SpecialLinearGroup (Fin n) ℤ),
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal d := by
  rcases Int.isUnit_iff.mp hL_unit with hLd | hLd <;>
    rcases Int.isUnit_iff.mp hQ_unit with hQd | hQd
  · exact ⟨⟨L_mat, hLd⟩, ⟨Q_mat, hQd⟩, hL_eq⟩
  · exfalso; nlinarith [hLQ_one]
  · exfalso; nlinarith [hLQ_one]
  · have hn : 0 < n := by
      by_contra h; push Not at h; interval_cases n; simp [Matrix.det_isEmpty] at hLd
    haveI : NeZero n := ⟨by omega⟩
    set flip : Matrix (Fin n) (Fin n) ℤ := Matrix.diagonal (Function.update 1 0 (-1))
    have hflip_det : flip.det = -1 := by
      rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ 0)]; simp
    have hflip_sq : flip * flip = 1 := by
      rw [Matrix.diagonal_mul_diagonal]; ext i j; simp only [Matrix.diagonal_apply,
        Matrix.one_apply]
      by_cases h : i = j
      · subst h; by_cases hi : i = 0 <;> simp [hi]
      · simp [h]
    have hflip_diag : flip * Matrix.diagonal d * flip = Matrix.diagonal d := by
      have hcomm : flip * Matrix.diagonal d = Matrix.diagonal d * flip := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]; congr 1; ext i
        simp only [Function.update_apply]; by_cases hi : i = 0 <;> simp [hi, mul_comm]
      rw [hcomm, Matrix.mul_assoc, hflip_sq, Matrix.mul_one]
    have hflip_L_det : (flip * L_mat).det = 1 := by rw [det_mul, hflip_det, hLd]; norm_num
    have hflip_Q_det : (Q_mat * flip).det = 1 := by rw [det_mul, hQd, hflip_det]; norm_num
    have hflip_eq : flip * L_mat * A * (Q_mat * flip) = Matrix.diagonal d := by
      have : flip * L_mat * A * (Q_mat * flip) = flip * (L_mat * A * Q_mat) * flip := by
        simp only [Matrix.mul_assoc]
      rw [this, hL_eq, hflip_diag]
    exact ⟨⟨flip * L_mat, hflip_L_det⟩, ⟨Q_mat * flip, hflip_Q_det⟩, hflip_eq⟩

/-- Every integer matrix with positive determinant is `SL_n(ℤ)`-equivalent to a positive
diagonal. -/
theorem exists_diagonal_of_posdet (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    ∃ (d : Fin n → ℤ) (_ : ∀ i, 0 < d i), ∃ (L R : SpecialLinearGroup (Fin n) ℤ),
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal d := by
  have hdet_ne : A.det ≠ 0 := ne_of_gt hdet
  have hinj := mulVecLin_injective_of_det_ne_zero (n := n) A hdet_ne
  have hrank : Module.finrank ℤ (LinearMap.range A.mulVecLin) = Module.finrank ℤ (Fin n → ℤ) :=
    finrank_range_mulVecLin (n := n) A hdet_ne
  obtain ⟨b', a, ab', hsnf⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq (Pi.basisFun ℤ (Fin n)) hrank
  have ha_ne : ∀ i, a i ≠ 0 := by
    intro i hi
    have : (ab' i : Fin n → ℤ) = 0 := by rw [hsnf i, hi, zero_smul]
    exact ab'.ne_zero i (Subtype.ext this)
  choose r hr using fun i => LinearMap.mem_range.mp (ab' i).2
  have hkey : ∀ j, A *ᵥ r j = a j • b' j := by
    intro j
    have h1 : A.mulVecLin (r j) = ↑(ab' j) := hr j
    have h2 : (↑(ab' j) : Fin n → ℤ) = a j • b' j := hsnf j
    change A *ᵥ r j = a j • b' j; rw [← h2, ← h1]; rfl
  set e := Pi.basisFun ℤ (Fin n)
  set P_mat : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun k j => b' j k) with hP_def
  set Q_mat : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun k j => r j k) with hQ_def
  have hmat_eq : A * Q_mat = P_mat * Matrix.diagonal a := by
    ext k j; simp only [Matrix.mul_apply, hQ_def, hP_def, Matrix.of_apply, Matrix.diagonal_apply]
    conv_lhs => rw [show ∑ l, A k l * r j l = (A *ᵥ r j) k from by simp [mulVec, dotProduct]]
    rw [hkey j]; simp only [Pi.smul_apply, smul_eq_mul]
    simp [Finset.sum_ite_eq', Finset.mem_univ, mul_comm]
  have hP_eq : P_mat = e.toMatrix b' := by
    ext k j; change b' j k = e.toMatrix b' k j; rw [e.toMatrix_apply, Pi.basisFun_repr]
  have hP_unit : IsUnit P_mat.det := by rw [hP_eq]; exact e.isUnit_det b'
  have hr_li : LinearIndependent ℤ r := by
    rw [linearIndependent_iff']; intro s g hg i hi
    have hab_li := ab'.linearIndependent; rw [linearIndependent_iff'] at hab_li
    apply hab_li s g _ i hi
    have h_zero : (∑ j ∈ s, g j • (ab' j : Fin n → ℤ) : Fin n → ℤ) = 0 := by
      have hmapped : A.mulVecLin (∑ j ∈ s, g j • r j) =
          ∑ j ∈ s, (g j • (ab' j : Fin n → ℤ)) := by
        rw [map_sum]; congr 1; ext j; simp only [LinearMap.map_smul, hr j]
      rw [hg, LinearMap.map_zero] at hmapped; exact hmapped.symm
    apply Subtype.val_injective
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_zero]; exact h_zero
  have hr_span : Submodule.span ℤ (Set.range r) = ⊤ := by
    rw [eq_top_iff]; intro v _
    set w : LinearMap.range A.mulVecLin := ⟨A.mulVecLin v, LinearMap.mem_range_self _ v⟩
    set c := ab'.repr w
    have hAeq : A.mulVecLin v = A.mulVecLin (∑ i, c i • r i) := by
      have hw_sum : (w : Fin n → ℤ) = ∑ i, c i • (ab' i : Fin n → ℤ) := by
        conv_lhs => rw [show w = ∑ i, c i • ab' i from (ab'.sum_repr w).symm]
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
      have hw_eq : (w : Fin n → ℤ) = A.mulVecLin v := rfl
      rw [← hw_eq, hw_sum, map_sum]
      congr 1; ext i; rw [LinearMap.map_smul, hr i]
    rw [hinj hAeq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hQ_eq : Q_mat = e.toMatrix r := by
    ext k j; change r j k = e.toMatrix r k j; rw [e.toMatrix_apply, Pi.basisFun_repr]
  have hQ_unit : IsUnit Q_mat.det := by
    rw [hQ_eq]
    set r_basis : Module.Basis (Fin n) ℤ (Fin n → ℤ) := Module.Basis.mk hr_li hr_span.ge
    suffices h : e.toMatrix r = e.toMatrix (⇑r_basis) by rw [h]; exact e.isUnit_det r_basis
    congr 1; funext j; exact (Module.Basis.mk_apply hr_li hr_span.ge j).symm
  have h_diag_eq : P_mat⁻¹ * A * Q_mat = Matrix.diagonal a := by
    rw [Matrix.mul_assoc, hmat_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP_unit,
      Matrix.one_mul]
  set d := fun i => |a i| with hd_def
  have hd_pos : ∀ i, 0 < d i := fun i => abs_pos.mpr (ha_ne i)
  set sv := fun i => if (0 : ℤ) < a i then (1 : ℤ) else -1 with hsv_def
  have hsv_sq : ∀ i, sv i * sv i = 1 := by intro i; simp only [hsv_def]; split_ifs <;> ring
  have hsv_mul_d : ∀ i, sv i * d i = a i := by
    intro i; simp only [hsv_def, hd_def]; rcases lt_trichotomy (a i) 0 with h | h | h
    · rw [if_neg (not_lt.mpr h.le), abs_of_neg h]; ring
    · exact absurd h (ha_ne i)
    · rw [if_pos h, abs_of_pos h, one_mul]
  have h_sd : Matrix.diagonal a = Matrix.diagonal sv * Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; ext i; exact (hsv_mul_d i).symm
  have hss : Matrix.diagonal sv * Matrix.diagonal sv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; ext i j; simp only [Matrix.diagonal_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp [hsv_sq]
    · simp [h]
  have hs_det_unit : IsUnit (Matrix.diagonal sv).det := by
    rw [Matrix.det_diagonal]; exact IsUnit.of_mul_eq_one _
      (by rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one (fun i _ => hsv_sq i))
  set L_mat := Matrix.diagonal sv * P_mat⁻¹ with hL_def
  have hL_eq : L_mat * A * Q_mat = Matrix.diagonal d := by
    calc L_mat * A * Q_mat
        = Matrix.diagonal sv * (P_mat⁻¹ * A * Q_mat) := by rw [hL_def]; simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal sv * Matrix.diagonal a := by rw [h_diag_eq]
      _ = Matrix.diagonal sv * (Matrix.diagonal sv * Matrix.diagonal d) := by rw [h_sd]
      _ = (Matrix.diagonal sv * Matrix.diagonal sv) * Matrix.diagonal d := by rw [Matrix.mul_assoc]
      _ = Matrix.diagonal d := by rw [hss, Matrix.one_mul]
  have hL_unit : IsUnit L_mat.det := by
    rw [hL_def, det_mul]; exact IsUnit.mul hs_det_unit (isUnit_nonsing_inv_det _ hP_unit)
  have hLQ_one : L_mat.det * Q_mat.det = 1 := by
    have h_prod : L_mat.det * A.det * Q_mat.det = ∏ i, d i := by
      rw [← det_mul, ← det_mul, hL_eq, Matrix.det_diagonal]
    rcases Int.isUnit_iff.mp (IsUnit.mul hL_unit hQ_unit) with hone | hneg
    · exact hone
    · exfalso
      have hmul_eq : L_mat.det * Q_mat.det * A.det = ∏ i, d i := by
        have : L_mat.det * Q_mat.det * A.det = L_mat.det * A.det * Q_mat.det := by ring
        linarith [h_prod]
      rw [hneg] at hmul_eq
      have hprod_pos : (0 : ℤ) < ∏ i, d i := Finset.prod_pos fun i _ => hd_pos i
      nlinarith
  exact ⟨d, hd_pos,
    sign_correct_unit_transform (n := n) A d L_mat Q_mat hd_pos hL_eq hLQ_one hL_unit hQ_unit⟩

private noncomputable def finEquivSum (k : ℕ) : Fin (k + 2) ≃ Fin 2 ⊕ Fin k :=
  (Fin.castOrderIso (by omega : k + 2 = 2 + k)).toEquiv.trans finSumFinEquiv.symm

private lemma diagonal_submatrix_finEquivSum (k : ℕ) (d : Fin (k + 2) → ℤ) :
    (Matrix.diagonal (d ∘ (finEquivSum k).symm)).submatrix (finEquivSum k) (finEquivSum k) =
    Matrix.diagonal d := by ext i j; simp [submatrix_apply, diagonal_apply]

private lemma gcd_2x2_det_L (a b : ℤ) (ha : 0 < a) :
    let g : ℤ := ↑(a.gcd b); let s := a.gcdA b; let t := a.gcdB b
    (!![s, t; -(b / g), a / g] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  simp only [det_fin_two, Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
    cons_val_one, mul_neg, sub_neg_eq_add]
  have hg_pos : (0 : ℤ) < ↑(a.gcd b) := by positivity
  suffices h : (a.gcdA b * (a / ↑(a.gcd b)) + a.gcdB b * (b / ↑(a.gcd b))) * ↑(a.gcd b) =
      1 * ↑(a.gcd b) by exact mul_right_cancel₀ (ne_of_gt hg_pos) h
  rw [one_mul]
  calc (a.gcdA b * (a / ↑(a.gcd b)) + a.gcdB b * (b / ↑(a.gcd b))) * ↑(a.gcd b)
      = a.gcdA b * (a / ↑(a.gcd b) * ↑(a.gcd b)) +
        a.gcdB b * (b / ↑(a.gcd b) * ↑(a.gcd b)) := by ring
    _ = a.gcdA b * a + a.gcdB b * b := by
        rw [Int.ediv_mul_cancel (Int.gcd_dvd_left a b),
          Int.ediv_mul_cancel (Int.gcd_dvd_right a b)]
    _ = a * a.gcdA b + b * a.gcdB b := by ring
    _ = ↑(a.gcd b) := (Int.gcd_eq_gcd_ab a b).symm

private lemma gcd_2x2_det_R (a b : ℤ) :
    let g : ℤ := ↑(a.gcd b); let t := a.gcdB b; let q := b / g
    (!![(1 : ℤ), -(t * q); 1, 1 - t * q] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  simp [det_fin_two]

private lemma gcd_2x2_mul (a b : ℤ) :
    let g : ℤ := ↑(a.gcd b); let s := a.gcdA b; let t := a.gcdB b
    let p := a / g; let q := b / g
    !![s, t; -q, p] * !![a, (0 : ℤ); 0, b] * !![1, -(t * q); 1, 1 - t * q] =
    (!![g, 0; 0, p * q * g] : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro g s t p q
  have hpg : p * g = a := Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hqg : q * g = b := Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  have hbez : s * a + t * b = g := by linarith [Int.gcd_eq_gcd_ab a b]
  have h1 : !![s, t; -q, p] * (!![a, (0 : ℤ); 0, b] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![s * a, t * b; -(q * a), p * b] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  rw [h1]; ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, mul_apply, of_apply, cons_val', cons_val_fin_one,
      cons_val_zero, Fin.sum_univ_two, mul_one, cons_val_one, Fin.mk_one, mul_neg, neg_mul, neg_neg]
  · linarith
  · have key : -(s * a * (t * q)) + t * b * (1 - t * q) =
        (1 - (s * p + t * q)) * (t * q * g) := by rw [← hpg, ← hqg]; ring
    rw [key]
    have h2 : (1 - (s * p + t * q)) * g = 0 := by
      have : (s * p + t * q) * g = g := by
        calc (s * p + t * q) * g = s * (p * g) + t * (q * g) := by ring
          _ = s * a + t * b := by rw [hpg, hqg]
          _ = g := hbez
      linarith
    calc (1 - (s * p + t * q)) * (t * q * g) =
          t * q * ((1 - (s * p + t * q)) * g) := by ring
      _ = t * q * 0 := by rw [h2]
      _ = 0 := by ring
  · rw [← hpg, ← hqg]; ring
  · rw [← hpg, ← hqg]; ring

private lemma gcd_step_divchain (k : ℕ) (d : Fin (k + 2) → ℤ) (hd : ∀ i, 0 < d i) :
    let a := d ⟨0, by omega⟩; let b := d ⟨1, by omega⟩
    let g : ℤ := ↑(a.gcd b); let p := a / g; let q := b / g
    ∃ (L R : SpecialLinearGroup (Fin (k + 2)) ℤ) (d' : Fin (k + 2) → ℤ),
      (∀ i, 0 < d' i) ∧ d' ⟨0, by omega⟩ = g ∧ d' ⟨1, by omega⟩ = p * q * g ∧
      (∀ j : Fin k, d' ⟨j.val + 2, by omega⟩ = d ⟨j.val + 2, by omega⟩) ∧
      g ∣ (p * q * g) ∧ (g.natAbs ≤ a.natAbs) ∧ (¬(a ∣ b) → g.natAbs < a.natAbs) ∧
      (L : Matrix _ _ ℤ) * Matrix.diagonal d * (R : Matrix _ _ ℤ) = Matrix.diagonal d' := by
  intro a b g p q
  set e := finEquivSum k
  set d' : Fin (k + 2) → ℤ := fun i =>
    if i.val = 0 then g else if i.val = 1 then p * q * g else d i
  have ha : 0 < a := hd ⟨0, by omega⟩; have hb : 0 < b := hd ⟨1, by omega⟩
  have hg_pos : (0 : ℤ) < g :=
    Int.natCast_pos.mpr (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr (ne_of_gt ha)))
  have hp_pos : 0 < p := Int.ediv_pos_of_pos_of_dvd ha (le_of_lt hg_pos) (Int.gcd_dvd_left a b)
  have hq_pos : 0 < q := Int.ediv_pos_of_pos_of_dvd hb (le_of_lt hg_pos) (Int.gcd_dvd_right a b)
  have hd'_pos : ∀ i, 0 < d' i := by
    intro i; simp only [d']; split_ifs <;> [exact hg_pos; positivity; exact hd i]
  set L22 := !![a.gcdA b, a.gcdB b; -(b / g), a / g]
  set R22 := !![(1 : ℤ), -(a.gcdB b * (b / g)); 1, 1 - a.gcdB b * (b / g)]
  set L_big : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    (fromBlocks L22 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e
  set R_big : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    (fromBlocks R22 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e
  have hL_det_big : L_big.det = 1 := by
    simp only [L_big]; rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one,
      gcd_2x2_det_L a b ha]
  have hR_det_big : R_big.det = 1 := by
    simp only [R_big]; rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one,
      gcd_2x2_det_R a b]
  refine ⟨⟨L_big, hL_det_big⟩, ⟨R_big, hR_det_big⟩, d', hd'_pos,
    by simp [d'], by simp [d'], ?_, dvd_mul_left g (p * q), ?_, ?_, ?_⟩
  · intro j; simp [d', show j.val + 2 ≠ 1 by omega]
  · exact Nat.le_of_dvd (Int.natAbs_pos.mpr (ne_of_gt ha))
      (Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_left a b))
  · intro hndvd
    have hle : g.natAbs ≤ a.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr (ne_of_gt ha))
      (Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_left a b))
    exact lt_of_le_of_ne hle (fun heq => hndvd (by
      have h1 : g.natAbs = a.gcd b := by simp [g]
      have h2 : a.gcd b = a.natAbs := by omega
      exact Int.natAbs_dvd_natAbs.mp (h2 ▸ Nat.gcd_dvd_right a.natAbs b.natAbs)))
  · change L_big * Matrix.diagonal d * R_big = Matrix.diagonal d'
    rw [show Matrix.diagonal d = (Matrix.diagonal (d ∘ e.symm)).submatrix e e from
      (diagonal_submatrix_finEquivSum k d).symm]
    simp only [L_big, R_big, Matrix.submatrix_mul_equiv]
    rw [show Matrix.diagonal d' = (Matrix.diagonal (d' ∘ e.symm)).submatrix e e from
      (diagonal_submatrix_finEquivSum k d').symm]; congr 1
    have h_diag_decomp : Matrix.diagonal (d ∘ e.symm) =
        fromBlocks (Matrix.diagonal (fun i : Fin 2 => (d ∘ e.symm) (Sum.inl i)))
          0 0 (Matrix.diagonal (fun i : Fin k => (d ∘ e.symm) (Sum.inr i))) := by
      ext (i | i) (j | j) <;> simp [fromBlocks, diagonal_apply, Sum.elim, Function.comp]
    rw [h_diag_decomp]
    rw [fromBlocks_multiply]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul]
    rw [fromBlocks_multiply]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_one]
    have h_diag'_decomp : Matrix.diagonal (d' ∘ e.symm) =
        fromBlocks (Matrix.diagonal (fun i : Fin 2 => (d' ∘ e.symm) (Sum.inl i)))
          0 0 (Matrix.diagonal (fun i : Fin k => (d' ∘ e.symm) (Sum.inr i))) := by
      ext (i | i) (j | j) <;> simp [fromBlocks, diagonal_apply, Sum.elim, Function.comp]
    rw [h_diag'_decomp]; congr 1
    · have he0 : e.symm (Sum.inl (0 : Fin 2)) = (0 : Fin (k + 2)) := by
        apply e.injective; rw [Equiv.apply_symm_apply]; change finEquivSum k ⟨0, by omega⟩ = _
        unfold finEquivSum; simp [Equiv.trans_apply, Fin.castOrderIso]; rfl
      have he1 : e.symm (Sum.inl (1 : Fin 2)) = (1 : Fin (k + 2)) := by
        apply e.injective; rw [Equiv.apply_symm_apply]; change finEquivSum k ⟨1, by omega⟩ = _
        unfold finEquivSum; simp [Equiv.trans_apply, Fin.castOrderIso]; rfl
      have h_head : Matrix.diagonal (fun i : Fin 2 => (d ∘ e.symm) (Sum.inl i)) =
          !![a, (0 : ℤ); 0, b] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Function.comp, he0, he1, a, b]
      have h_head' : Matrix.diagonal (fun i : Fin 2 => (d' ∘ e.symm) (Sum.inl i)) =
          !![g, (0 : ℤ); 0, p * q * g] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Function.comp, he0, he1, d', g, p, q]
      rw [h_head, h_head']; exact gcd_2x2_mul a b
    · congr 1; ext i
      have h1 : e.symm (Sum.inr i) ≠ ⟨0, by omega⟩ := by
        intro h
        have h_ap := Equiv.apply_symm_apply e (Sum.inr i)
        rw [h] at h_ap
        have h_e0 : e ⟨0, by omega⟩ = Sum.inl ⟨0, by omega⟩ := by
          change finEquivSum k ⟨0, by omega⟩ = _
          unfold finEquivSum; simp [Equiv.trans_apply, Fin.castOrderIso]; rfl
        rw [h_e0] at h_ap; exact (by nomatch h_ap)
      have h2 : e.symm (Sum.inr i) ≠ ⟨1, by omega⟩ := by
        intro h
        have h_ap := Equiv.apply_symm_apply e (Sum.inr i)
        rw [h] at h_ap
        have h_e1 : e ⟨1, by omega⟩ = Sum.inl ⟨1, by omega⟩ := by
          change finEquivSum k ⟨1, by omega⟩ = _
          unfold finEquivSum; simp [Equiv.trans_apply, Fin.castOrderIso]; rfl
        rw [h_e1] at h_ap; exact (by nomatch h_ap)
      have hv1 : (e.symm (Sum.inr i)).val ≠ 0 := fun h => h1 (Fin.ext h)
      have hv2 : (e.symm (Sum.inr i)).val ≠ 1 := fun h => h2 (Fin.ext h)
      simp only [Function.comp, d', ite_false, hv1, hv2]

private noncomputable def genEquiv (k : ℕ) (j : Fin (k + 2)) (_hj : j.val ≠ 0) :
    Fin (k + 2) ≃ Fin 2 ⊕ Fin k :=
  (Equiv.swap (⟨1, by omega⟩ : Fin (k + 2)) j).trans (finEquivSum k)

private lemma diagonal_submatrix_genEquiv (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0)
    (d : Fin (k + 2) → ℤ) : (Matrix.diagonal (d ∘ (genEquiv k j hj).symm)).submatrix
    (genEquiv k j hj) (genEquiv k j hj) = Matrix.diagonal d := by
  ext i m; simp [submatrix_apply, diagonal_apply]

private lemma genEquiv_zero (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    genEquiv k j hj ⟨0, by omega⟩ = Sum.inl ⟨0, by omega⟩ := by
  simp only [genEquiv, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne (by intro h; simp at h) (fun h => hj (by rw [← h]))]
  show finEquivSum k ⟨0, by omega⟩ = _
  unfold finEquivSum; simp [Equiv.trans_apply, Fin.castOrderIso]; rfl

private lemma genEquiv_j (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    genEquiv k j hj j = Sum.inl ⟨1, by omega⟩ := by
  simp only [genEquiv, Equiv.trans_apply, Equiv.swap_apply_right]
  change finEquivSum k ⟨1, by omega⟩ = _; unfold finEquivSum
  simp [Equiv.trans_apply, Fin.castOrderIso]; rfl

private lemma genEquiv_symm_inl0 (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    (genEquiv k j hj).symm (Sum.inl (0 : Fin 2)) = (0 : Fin (k + 2)) := by
  apply (genEquiv k j hj).injective; rw [Equiv.apply_symm_apply]
  exact (genEquiv_zero k j hj).symm

private lemma genEquiv_symm_inl1 (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    (genEquiv k j hj).symm (Sum.inl (1 : Fin 2)) = j := by
  apply (genEquiv k j hj).injective; rw [Equiv.apply_symm_apply]
  exact (genEquiv_j k j hj).symm

private lemma genEquiv_symm_inr_ne_zero (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) (i : Fin k) :
    (genEquiv k j hj).symm (Sum.inr i) ≠ ⟨0, by omega⟩ := by
  intro h; have := Equiv.apply_symm_apply (genEquiv k j hj) (Sum.inr i)
  rw [h, genEquiv_zero] at this; exact (by nomatch this)

private lemma genEquiv_symm_inr_ne_j (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) (i : Fin k) :
    (genEquiv k j hj).symm (Sum.inr i) ≠ j := by
  intro h; have := Equiv.apply_symm_apply (genEquiv k j hj) (Sum.inr i)
  rw [h, genEquiv_j] at this; exact (by nomatch this)

private lemma gcd_step_general (k : ℕ) (d : Fin (k + 2) → ℤ) (hd : ∀ i, 0 < d i)
    (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    let a := d ⟨0, by omega⟩; let b := d j; let g : ℤ := ↑(a.gcd b)
    ∃ (L R : SpecialLinearGroup (Fin (k + 2)) ℤ) (d' : Fin (k + 2) → ℤ),
      (∀ i, 0 < d' i) ∧ d' ⟨0, by omega⟩ = g ∧
      (∀ i, i ≠ ⟨0, by omega⟩ → i ≠ j → d' i = d i) ∧
      (g.natAbs ≤ a.natAbs) ∧ (¬(a ∣ b) → g.natAbs < a.natAbs) ∧
      (L : Matrix _ _ ℤ) * Matrix.diagonal d * (R : Matrix _ _ ℤ) = Matrix.diagonal d' := by
  intro a b g
  set e := genEquiv k j hj
  set p := a / g; set q := b / g
  set d' : Fin (k + 2) → ℤ := fun i =>
    if i = (0 : Fin (k + 2)) then g else if i = j then p * q * g else d i
  have ha : 0 < a := hd ⟨0, by omega⟩; have hb : 0 < b := hd j
  have hg_pos : (0 : ℤ) < g :=
    Int.natCast_pos.mpr (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr (ne_of_gt ha)))
  have hp_pos : 0 < p := Int.ediv_pos_of_pos_of_dvd ha (le_of_lt hg_pos) (Int.gcd_dvd_left a b)
  have hq_pos : 0 < q := Int.ediv_pos_of_pos_of_dvd hb (le_of_lt hg_pos) (Int.gcd_dvd_right a b)
  have hd'_pos : ∀ i, 0 < d' i := by
    intro i; simp only [d']; split_ifs <;> [exact hg_pos; positivity; exact hd i]
  set L22 := !![a.gcdA b, a.gcdB b; -(b / g), a / g]
  set R22 := !![(1 : ℤ), -(a.gcdB b * (b / g)); 1, 1 - a.gcdB b * (b / g)]
  set L_big : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    (fromBlocks L22 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e
  set R_big : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    (fromBlocks R22 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e
  have hL_det_big : L_big.det = 1 := by
    simp only [L_big]; rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one,
      gcd_2x2_det_L a b ha]
  have hR_det_big : R_big.det = 1 := by
    simp only [R_big]; rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one,
      gcd_2x2_det_R a b]
  have hj_ne_zero : j ≠ (0 : Fin (k + 2)) := fun h => hj (by rw [h]; rfl)
  refine ⟨⟨L_big, hL_det_big⟩, ⟨R_big, hR_det_big⟩, d', hd'_pos,
    by show d' ⟨0, _⟩ = g; simp [d'], ?_, ?_, ?_, ?_⟩
  · intro i hi1 hi2; show d' i = d i
    simp only [d']; rw [if_neg (show i ≠ (0 : Fin (k + 2)) from hi1), if_neg hi2]
  · exact Nat.le_of_dvd (Int.natAbs_pos.mpr (ne_of_gt ha))
      (Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_left a b))
  · intro hndvd
    have hle : g.natAbs ≤ a.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr (ne_of_gt ha))
      (Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_left a b))
    exact lt_of_le_of_ne hle (fun heq => hndvd (by
      have h1 : g.natAbs = a.gcd b := by simp [g]
      have h2 : a.gcd b = a.natAbs := by omega
      exact Int.natAbs_dvd_natAbs.mp (h2 ▸ Nat.gcd_dvd_right a.natAbs b.natAbs)))
  · change L_big * Matrix.diagonal d * R_big = Matrix.diagonal d'
    rw [show Matrix.diagonal d = (Matrix.diagonal (d ∘ e.symm)).submatrix e e from
      (diagonal_submatrix_genEquiv k j hj d).symm]
    simp only [L_big, R_big, Matrix.submatrix_mul_equiv]
    rw [show Matrix.diagonal d' = (Matrix.diagonal (d' ∘ e.symm)).submatrix e e from
      (diagonal_submatrix_genEquiv k j hj d').symm]; congr 1
    have h_diag_decomp : Matrix.diagonal (d ∘ e.symm) =
        fromBlocks (Matrix.diagonal (fun i : Fin 2 => (d ∘ e.symm) (Sum.inl i)))
          0 0 (Matrix.diagonal (fun i : Fin k => (d ∘ e.symm) (Sum.inr i))) := by
      ext (i | i) (j | j) <;> simp [fromBlocks, diagonal_apply, Sum.elim, Function.comp]
    rw [h_diag_decomp]
    rw [fromBlocks_multiply]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul]
    rw [fromBlocks_multiply]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_one]
    have h_diag'_decomp : Matrix.diagonal (d' ∘ e.symm) =
        fromBlocks (Matrix.diagonal (fun i : Fin 2 => (d' ∘ e.symm) (Sum.inl i)))
          0 0 (Matrix.diagonal (fun i : Fin k => (d' ∘ e.symm) (Sum.inr i))) := by
      ext (i | i) (j | j) <;> simp [fromBlocks, diagonal_apply, Sum.elim, Function.comp]
    rw [h_diag'_decomp]; congr 1
    · have he0 : e.symm (Sum.inl (0 : Fin 2)) = (0 : Fin (k + 2)) := by
        simp only [e]; exact genEquiv_symm_inl0 k j hj
      have he1 : e.symm (Sum.inl (1 : Fin 2)) = j := by
        simp only [e]; exact genEquiv_symm_inl1 k j hj
      have h_head : Matrix.diagonal (fun i : Fin 2 => (d ∘ e.symm) (Sum.inl i)) =
          !![a, (0 : ℤ); 0, b] := by
        ext i m; fin_cases i <;> fin_cases m <;> simp [Function.comp, he0, he1, a, b]
      have h_head' : Matrix.diagonal (fun i : Fin 2 => (d' ∘ e.symm) (Sum.inl i)) =
          !![g, (0 : ℤ); 0, p * q * g] := by
        ext i m; fin_cases i <;> fin_cases m <;> simp [Function.comp, he0, he1, d', hj_ne_zero,
          g, p, q]
      rw [h_head, h_head']; exact gcd_2x2_mul a b
    · congr 1; ext i; simp only [Function.comp, d']
      rw [if_neg (by simp only [e]; exact genEquiv_symm_inr_ne_zero k j hj i),
        if_neg (by simp only [e]; exact genEquiv_symm_inr_ne_j k j hj i)]

private lemma dvd_diag_of_SL_transform (m : ℕ) (d d' : Fin m → ℤ) (c : ℤ) (hc : ∀ i, c ∣ d i)
    (L R : Matrix (Fin m) (Fin m) ℤ) (heq : L * Matrix.diagonal d * R = Matrix.diagonal d') :
    ∀ i, c ∣ d' i := by
  intro i; rw [show d' i = (Matrix.diagonal d') i i from by simp, ← heq, mul_apply]
  apply Finset.dvd_sum; intro k _; rw [mul_apply]; apply dvd_mul_of_dvd_left
  apply Finset.dvd_sum; intro l _; simp only [diagonal_apply]; split_ifs with h
  · subst h; exact dvd_mul_of_dvd_right (hc l) _
  · simp

private noncomputable def fin1Sum (k : ℕ) : Fin (k + 1) ≃ Fin 1 ⊕ Fin k :=
  (Fin.castOrderIso (show k + 1 = 1 + k by omega)).toEquiv.trans finSumFinEquiv.symm

private lemma fin1Sum_zero (k : ℕ) : fin1Sum k (0 : Fin (k + 1)) = Sum.inl (0 : Fin 1) := by
  unfold fin1Sum; simp [Equiv.trans_apply, Fin.castOrderIso]; rfl

private lemma fin1Sum_succ (k : ℕ) (i : Fin k) :
    fin1Sum k ⟨i.val + 1, by omega⟩ = Sum.inr i := by
  unfold fin1Sum; simp only [Equiv.trans_apply, Fin.castOrderIso]; rw [Equiv.symm_apply_eq]
  simp only [finSumFinEquiv, Fin.addCases, Equiv.coe_fn_mk, Fin.cast_mk, Order.lt_one_iff,
    Fin.val_eq_zero_iff, eq_rec_constant, Sum.elim_inr]; ext; simp; omega

private lemma fin1Sum_symm_inl (k : ℕ) :
    (fin1Sum k).symm (Sum.inl (0 : Fin 1)) = (0 : Fin (k + 1)) := by
  apply (fin1Sum k).injective; rw [Equiv.apply_symm_apply]; exact (fin1Sum_zero k).symm

private lemma fin1Sum_symm_inr (k : ℕ) (i : Fin k) :
    (fin1Sum k).symm (Sum.inr i) = ⟨i.val + 1, by omega⟩ := by
  apply (fin1Sum k).injective; rw [Equiv.apply_symm_apply]; exact (fin1Sum_succ k i).symm

private lemma diagonal_submatrix_fin1Sum (k : ℕ) (d : Fin (k + 1) → ℤ) :
    (Matrix.diagonal (d ∘ (fin1Sum k).symm)).submatrix (fin1Sum k) (fin1Sum k) =
    Matrix.diagonal d := by ext i m; simp [submatrix_apply, diagonal_apply]

private lemma make_first_divide_all (k : ℕ) (d : Fin (k + 2) → ℤ) (hd : ∀ i, 0 < d i) :
    ∃ (d' : Fin (k + 2) → ℤ) (_ : ∀ i, 0 < d' i) (_ : ∀ j, d' (0 : Fin (k + 2)) ∣ d' j),
    ∃ (L R : SpecialLinearGroup (Fin (k + 2)) ℤ),
      (L : Matrix _ _ ℤ) * Matrix.diagonal d * (R : Matrix _ _ ℤ) = Matrix.diagonal d' := by
  have ha_pos : 0 < d (0 : Fin (k + 2)) := hd 0
  obtain ⟨N, hN⟩ : ∃ N, (d (0 : Fin (k + 2))).natAbs = N := ⟨_, rfl⟩
  revert d hd ha_pos
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro d hd ha_pos hN
    by_cases hall : ∀ j, d (0 : Fin (k + 2)) ∣ d j
    · exact ⟨d, hd, hall, 1, 1, by simp⟩
    · push Not at hall
      obtain ⟨j, hj_ndvd⟩ := hall
      have hj_ne : j.val ≠ 0 := by
        intro h; apply hj_ndvd; have : j = 0 := Fin.ext h; subst this; exact dvd_refl _
      obtain ⟨L₁, R₁, d₁, hd₁_pos, hd₁_zero, hd₁_rest, _, hlt, hmul₁⟩ :=
        gcd_step_general k d hd j hj_ne
      have hN₁ : (d₁ (0 : Fin (k + 2))).natAbs < N := by
        have : d₁ (0 : Fin (k + 2)) = d₁ ⟨0, by omega⟩ := rfl
        rw [this, hd₁_zero, ← hN]; exact hlt hj_ndvd
      obtain ⟨d₂, hd₂_pos, hd₂_div, L₂, R₂, hmul₂⟩ :=
        ih _ hN₁ d₁ hd₁_pos (hd₁_pos 0) rfl
      refine ⟨d₂, hd₂_pos, hd₂_div, L₂ * L₁, R₁ * R₂, ?_⟩
      simp only [SpecialLinearGroup.coe_mul]
      rw [show ((L₂ : Matrix _ _ ℤ) * (L₁ : Matrix _ _ ℤ)) * Matrix.diagonal d *
        ((R₁ : Matrix _ _ ℤ) * (R₂ : Matrix _ _ ℤ)) = (L₂ : Matrix _ _ ℤ) *
        ((L₁ : Matrix _ _ ℤ) * Matrix.diagonal d * (R₁ : Matrix _ _ ℤ)) * (R₂ : Matrix _ _ ℤ)
        by simp [Matrix.mul_assoc], hmul₁, hmul₂]

private noncomputable def slSuccEmbed {k : ℕ} (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    SpecialLinearGroup (Fin (k + 2)) ℤ := by
  let e := fin1Sum (k + 1)
  refine ⟨(fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)).submatrix e e, ?_⟩
  rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, one_mul, M.prop]

private lemma slSuccEmbed_mul_diagonal (k : ℕ) (d : Fin (k + 2) → ℤ)
    (L R : SpecialLinearGroup (Fin (k + 1)) ℤ) (d'_tail : Fin (k + 1) → ℤ) (hmul :
    (L : Matrix _ _ ℤ) * Matrix.diagonal (fun i : Fin (k + 1) => d ⟨i.val + 1, by omega⟩) *
    (R : Matrix _ _ ℤ) = Matrix.diagonal d'_tail) :
    let d_out : Fin (k + 2) → ℤ := fun i =>
      if i = (0 : Fin (k + 2)) then d 0 else d'_tail ⟨i.val - 1, by omega⟩
    (slSuccEmbed L : Matrix _ _ ℤ) * Matrix.diagonal d *
      (slSuccEmbed R : Matrix _ _ ℤ) = Matrix.diagonal d_out := by
  intro d_out
  set e := fin1Sum (k + 1)
  have he_inl : e.symm (Sum.inl (0 : Fin 1)) = (0 : Fin (k + 2)) := by
    simp only [e]; exact fin1Sum_symm_inl (k + 1)
  have he_inr : ∀ i : Fin (k + 1), e.symm (Sum.inr i) = ⟨i.val + 1, by omega⟩ := by
    intro i; simp only [e]; exact fin1Sum_symm_inr (k + 1) i
  rw [show Matrix.diagonal d = (Matrix.diagonal (d ∘ e.symm)).submatrix e e
      from (diagonal_submatrix_fin1Sum (k + 1) d).symm]
  change (fromBlocks 1 0 0 (L : Matrix _ _ ℤ)).submatrix e e *
    (Matrix.diagonal (d ∘ e.symm)).submatrix e e *
    (fromBlocks 1 0 0 (R : Matrix _ _ ℤ)).submatrix e e = _
  simp only [Matrix.submatrix_mul_equiv]
  have h_decomp : Matrix.diagonal (d ∘ e.symm) =
      fromBlocks (Matrix.diagonal (fun _ : Fin 1 => d 0))
        0 0 (Matrix.diagonal (fun i : Fin (k + 1) => d ⟨i.val + 1, by omega⟩)) := by
    ext (i | i) (j | j)
    · fin_cases i; fin_cases j; simp [fromBlocks, Function.comp, he_inl]
    · simp [fromBlocks]
    · simp [fromBlocks]
    · simp [fromBlocks, diagonal_apply, Function.comp, he_inr]
  rw [h_decomp]
  rw [fromBlocks_multiply]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul]
  rw [fromBlocks_multiply]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one]
  rw [show Matrix.diagonal d_out = (Matrix.diagonal (d_out ∘ e.symm)).submatrix e e
      from (diagonal_submatrix_fin1Sum (k + 1) d_out).symm]; congr 1
  have h_out_decomp : Matrix.diagonal (d_out ∘ e.symm) =
      fromBlocks (Matrix.diagonal (fun _ : Fin 1 => d 0)) 0 0 (Matrix.diagonal d'_tail) := by
    ext (i | i) (j | j)
    · fin_cases i; fin_cases j; simp [fromBlocks, Function.comp, d_out, he_inl]
    · simp [fromBlocks]
    · simp [fromBlocks]
    · simp [fromBlocks, diagonal_apply, Function.comp, d_out, he_inr]
  rw [h_out_decomp, hmul]

private lemma exists_divchain_of_posdiag (d : Fin n → ℤ) (hd : ∀ i, 0 < d i) :
    ∃ (d' : Fin n → ℤ) (_ : ∀ i, 0 < d' i)
      (_ : ∀ (i : ℕ) (hi : i + 1 < n), d' ⟨i, by omega⟩ ∣ d' ⟨i + 1, hi⟩),
    ∃ (L R : SpecialLinearGroup (Fin n) ℤ),
      (L : Matrix (Fin n) (Fin n) ℤ) * Matrix.diagonal d *
        (R : Matrix (Fin n) (Fin n) ℤ) = Matrix.diagonal d' := by
  suffices h : ∀ (m : ℕ) (d : Fin m → ℤ), (∀ i, 0 < d i) →
    ∃ (d' : Fin m → ℤ) (_ : ∀ i, 0 < d' i)
      (_ : ∀ (i : ℕ) (hi : i + 1 < m), d' ⟨i, by omega⟩ ∣ d' ⟨i + 1, hi⟩),
    ∃ (L R : SpecialLinearGroup (Fin m) ℤ),
      (L : Matrix (Fin m) (Fin m) ℤ) * Matrix.diagonal d *
        (R : Matrix (Fin m) (Fin m) ℤ) = Matrix.diagonal d' from h n d hd
  intro m
  induction m with
  | zero =>
    intro d hd
    exact ⟨d, hd, fun i hi => by omega, 1, 1, by simp⟩
  | succ m ih =>
    cases m with
    | zero =>
      intro d hd
      exact ⟨d, hd, fun i hi => by omega, 1, 1, by simp⟩
    | succ k =>
      intro d hd
      obtain ⟨d₁, hd₁_pos, hd₁_div, L₁, R₁, hmul₁⟩ := make_first_divide_all k d hd
      have ih_tail := ih (fun i : Fin (k + 1) => d₁ ⟨i.val + 1, by omega⟩)
        (fun i => hd₁_pos ⟨i.val + 1, by omega⟩)
      obtain ⟨d_tail', hd_tail'_pos, hd_tail'_chain, L_tail, R_tail, hmul_tail⟩ := ih_tail
      have hmul_embed := slSuccEmbed_mul_diagonal k d₁ L_tail R_tail d_tail' hmul_tail
      set d₂ : Fin (k + 2) → ℤ := fun i =>
        if i = (0 : Fin (k + 2)) then d₁ 0
        else d_tail' ⟨i.val - 1, by omega⟩
      have hd₂_pos : ∀ i, 0 < d₂ i := by
        intro i; simp only [d₂]; split_ifs <;> [exact hd₁_pos 0; exact hd_tail'_pos _]
      have hd₂_chain : ∀ (i : ℕ) (hi : i + 1 < k + 2),
          d₂ ⟨i, by omega⟩ ∣ d₂ ⟨i + 1, hi⟩ := by
        intro i hi
        cases i with
        | zero =>
          simp only [d₂]
          simp only [show (⟨0, by omega⟩ : Fin (k + 2)) = (0 : Fin (k + 2)) from rfl, if_true]
          rw [if_neg (show (⟨1, hi⟩ : Fin (k + 2)) ≠ 0 from fun h =>
            absurd (Fin.ext_iff.mp h) (by simp))]
          exact (dvd_diag_of_SL_transform (k + 1)
            (fun i : Fin (k + 1) => d₁ ⟨i.val + 1, by omega⟩) d_tail' (d₁ 0)
            (fun i => hd₁_div ⟨i.val + 1, by omega⟩) (L_tail : Matrix _ _ ℤ)
            (R_tail : Matrix _ _ ℤ) hmul_tail) ⟨0, by omega⟩
        | succ i =>
          simp only [d₂]
          rw [if_neg (show (⟨i + 1, by omega⟩ : Fin (k + 2)) ≠ 0 from fun h =>
              absurd (Fin.ext_iff.mp h) (by simp)),
            if_neg (show (⟨i + 2, hi⟩ : Fin (k + 2)) ≠ 0 from fun h =>
              absurd (Fin.ext_iff.mp h) (by simp))]
          change d_tail' ⟨i, by omega⟩ ∣ d_tail' ⟨i + 1, by omega⟩
          exact hd_tail'_chain i (by omega)
      refine ⟨d₂, hd₂_pos, hd₂_chain, slSuccEmbed L_tail * L₁, R₁ * slSuccEmbed R_tail, ?_⟩
      simp only [SpecialLinearGroup.coe_mul]
      rw [show ((slSuccEmbed L_tail : Matrix _ _ ℤ) * (L₁ : Matrix _ _ ℤ)) * Matrix.diagonal d *
        ((R₁ : Matrix _ _ ℤ) * (slSuccEmbed R_tail : Matrix _ _ ℤ)) =
        (slSuccEmbed L_tail : Matrix _ _ ℤ) * ((L₁ : Matrix _ _ ℤ) * Matrix.diagonal d *
        (R₁ : Matrix _ _ ℤ)) * (slSuccEmbed R_tail : Matrix _ _ ℤ)
        by simp [Matrix.mul_assoc], hmul₁, hmul_embed]

private theorem exists_divchain_diagonal_of_posdet (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : 0 < A.det) :
    ∃ (d : Fin n → ℤ) (_ : ∀ i, 0 < d i)
      (_ : ∀ (i : ℕ) (hi : i + 1 < n), d ⟨i, by omega⟩ ∣ d ⟨i + 1, hi⟩),
    ∃ (L R : SpecialLinearGroup (Fin n) ℤ),
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal d := by
  obtain ⟨d₀, hd₀_pos, L₀, R₀, hLR₀⟩ := exists_diagonal_of_posdet (n := n) A hdet
  obtain ⟨d', hd'_pos, hd'_div, L₁, R₁, hLR₁⟩ :=
    exists_divchain_of_posdiag (n := n) d₀ hd₀_pos
  refine ⟨d', hd'_pos, hd'_div, L₁ * L₀, R₀ * R₁, ?_⟩
  change (↑(L₁ * L₀) : Matrix _ _ ℤ) * A *
    (↑(R₀ * R₁) : Matrix _ _ ℤ) = Matrix.diagonal d'
  simp only [SpecialLinearGroup.coe_mul]
  calc (↑L₁ : Matrix _ _ ℤ) * ↑L₀ * A * (↑R₀ * ↑R₁)
      = ↑L₁ * (↑L₀ * A * ↑R₀) * ↑R₁ := by simp only [Matrix.mul_assoc]
    _ = ↑L₁ * Matrix.diagonal d₀ * ↑R₁ := by rw [hLR₀]
    _ = Matrix.diagonal d' := hLR₁

variable [NeZero n]

private lemma double_coset_eq_of_SLnZ_equiv (α : (GLPair n).Δ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑(↑α : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (d : Fin n → ℤ) (hd_pos : ∀ i, 0 < d i) (L R : SpecialLinearGroup (Fin n) ℤ)
    (hLR : (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal d) :
    DoubleCoset.doubleCoset (↑α : GL (Fin n) ℚ) (SLnZSubgroup n) (SLnZSubgroup n) =
    DoubleCoset.doubleCoset
      (GeneralLinearGroup.mkOfDetNeZero
        ((Matrix.diagonal d).map (Int.cast : ℤ → ℚ))
        (by rw [det_intMat_cast, Matrix.det_diagonal]
            exact_mod_cast (ne_of_gt (Finset.prod_pos (fun i _ => hd_pos i)))))
      (SLnZSubgroup n) (SLnZSubgroup n) := by
  set diag_GL := GeneralLinearGroup.mkOfDetNeZero
    ((Matrix.diagonal d).map (Int.cast : ℤ → ℚ))
    (by rw [det_intMat_cast, Matrix.det_diagonal]
        exact_mod_cast (ne_of_gt (Finset.prod_pos (fun i _ => hd_pos i))))
  symm; apply DoubleCoset.doubleCoset_eq_of_mem; rw [DoubleCoset.mem_doubleCoset]
  refine ⟨(L : GL (Fin n) ℚ), coe_mem_SLnZ n L, (R : GL (Fin n) ℚ), coe_mem_SLnZ n R, ?_⟩
  have h_map_mul : ∀ (X Y : Matrix (Fin n) (Fin n) ℤ),
      X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) =
      (X * Y).map (Int.cast : ℤ → ℚ) := by
    intro X Y; ext i j; simp [Matrix.mul_apply, Matrix.map_apply]
  apply Units.ext; change (diag_GL : Matrix (Fin n) (Fin n) ℚ) =
    (((L : GL (Fin n) ℚ) * ↑α * (R : GL (Fin n) ℚ) : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)
  simp only [Units.val_mul, mapGL_coe_matrix, algebraMap_int_eq, hA]; symm
  calc (↑L : Matrix _ _ ℤ).map (Int.cast : ℤ → ℚ) *
      A.map (Int.cast : ℤ → ℚ) * (↑R : Matrix _ _ ℤ).map (Int.cast : ℤ → ℚ)
      = ((↑L : Matrix _ _ ℤ) * A).map (Int.cast : ℤ → ℚ) *
        (↑R : Matrix _ _ ℤ).map (Int.cast : ℤ → ℚ) := by rw [h_map_mul]
    _ = ((↑L : Matrix _ _ ℤ) * A * (↑R : Matrix _ _ ℤ)).map (Int.cast : ℤ → ℚ) := by
        rw [h_map_mul]
    _ = (Matrix.diagonal d).map (Int.cast : ℤ → ℚ) := by rw [hLR]

/-- Every element of `Delta` has a diagonal representative with divisibility chain
(Smith normal form). -/
theorem exists_diagonal_representative (α : (GLPair n).Δ) :
    ∃ (a : Fin n → ℕ) (_ha : ∀ i, 0 < a i) (_hdiv : DivChain n a),
      (⟦α⟧ : HeckeCoset (GLPair n)) = TDiag a := by
  obtain ⟨A, hA⟩ : HasIntEntries n (↑α : GL (Fin n) ℚ) := α.2.1
  have h_det : (0 : ℚ) < (↑(↑α : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := α.2.2
  have hdet_pos : 0 < A.det := by
    have h1 : (A.det : ℚ) = (↑(↑α : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
      rw [hA]; exact (det_intMat_cast (n := n) A).symm
    exact_mod_cast h1 ▸ h_det
  obtain ⟨d, hd_pos, hd_div, L, R, hLR⟩ := exists_divchain_diagonal_of_posdet n A hdet_pos
  have hd_pos_nat : ∀ i, 0 < (d i).toNat := by
    intro i; linarith [hd_pos i, (Int.toNat_of_nonneg (le_of_lt (hd_pos i))).symm]
  set a : Fin n → ℕ := fun i => (d i).toNat
  have hd_eq : ∀ i, (d i) = (a i : ℤ) := by
    intro i; simp [a, Int.toNat_of_nonneg (le_of_lt (hd_pos i))]
  have hdiv : DivChain n a := by
    intro i hi; have h1 := hd_div i hi
    rw [hd_eq ⟨i, by omega⟩, hd_eq ⟨i + 1, hi⟩] at h1; exact_mod_cast h1
  refine ⟨a, hd_pos_nat, hdiv, ?_⟩
  simp only [TDiag]; rw [HeckeCoset.eq_iff]
  change DoubleCoset.doubleCoset (↑α : GL (Fin n) ℚ) (SLnZSubgroup n) (SLnZSubgroup n) =
    DoubleCoset.doubleCoset (↑(diagMatDelta n a) : GL (Fin n) ℚ) (SLnZSubgroup n)
      (SLnZSubgroup n)
  rw [diagMat_delta_val n a hd_pos_nat, double_coset_eq_of_SLnZ_equiv n α A hA d hd_pos L R hLR]
  congr 1; apply GeneralLinearGroup.ext; intro i j
  change ((Matrix.diagonal d).map (Int.cast : ℤ → ℚ)) i j =
    (↑(diagMat n a) : Matrix (Fin n) (Fin n) ℚ) i j
  simp only [diagMat_val n a hd_pos_nat, Matrix.diagonal_apply, Matrix.map_apply]
  split_ifs with h
  · rw [hd_eq i]; push_cast; rfl
  · simp

omit [NeZero n] in
private lemma divChain_prod_dvd_of_injective {a : Fin n → ℕ} (hda : DivChain n a)
    (k : ℕ) (hk : k ≤ n) (f : Fin k → Fin n) (hf : Function.Injective f) :
    (∏ j : Fin k, a ⟨j.val, by omega⟩) ∣ (∏ j : Fin k, a (f j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨j₀, _, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun j => (f j).val) Finset.univ_nonempty
    have hge : k ≤ (f j₀).val := by
      by_contra hlt; push Not at hlt
      have : Fintype.card (Fin (k + 1)) ≤ Fintype.card (Fin k) :=
        Fintype.card_le_of_injective
          (fun j : Fin (k + 1) => (⟨(f j).val, by
            exact Nat.lt_of_le_of_lt (hmax j (Finset.mem_univ _)) hlt⟩ : Fin k))
          (fun j₁ j₂ heq => by simp only [Fin.mk.injEq] at heq; exact hf (Fin.ext heq))
      simp at this
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_succAbove _ j₀, mul_comm (a (f j₀)) _]
    exact mul_dvd_mul (ih (by omega) (f ∘ j₀.succAbove)
      (hf.comp Fin.succAbove_right_injective)) (divChain_dvd (n := n) hda (by exact hge))

omit [NeZero n] in
private lemma partialProd_eq_of_SLnZ_equiv {a b : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hda : DivChain n a) (hdb : DivChain n b)
    (L R : SpecialLinearGroup (Fin n) ℤ) (hmat : (diagMat n b : GL (Fin n) ℚ) =
    (L : GL (Fin n) ℚ) * diagMat n a * (R : GL (Fin n) ℚ)) (k : ℕ) (hk : k ≤ n) :
    ∏ j : Fin k, a ⟨j.val, by omega⟩ = ∏ j : Fin k, b ⟨j.val, by omega⟩ := by
  suffices key : ∀ (c d : Fin n → ℕ) (hc_pos : ∀ i, 0 < c i) (hd_pos : ∀ i, 0 < d i),
      DivChain n c →
      ∀ (P Q : SpecialLinearGroup (Fin n) ℤ),
      (diagMat n d : GL (Fin n) ℚ) =
        (P : GL (Fin n) ℚ) * diagMat n c * (Q : GL (Fin n) ℚ) →
      (∏ j : Fin k, c ⟨j.val, by omega⟩) ∣
      (∏ j : Fin k, d ⟨j.val, by omega⟩) by
    exact Nat.dvd_antisymm (key a b ha hb hda L R hmat) (key b a hb ha hdb L⁻¹ R⁻¹ (by
      simp only [show mapGL ℚ L⁻¹ = (mapGL ℚ L)⁻¹ from map_inv _ L,
        show mapGL ℚ R⁻¹ = (mapGL ℚ R)⁻¹ from map_inv _ R]; rw [hmat]; group))
  intro c d hc_pos hd_pos hc P Q hcd
  suffices hint : (∏ j : Fin k, (c ⟨j.val, by omega⟩ : ℤ)) ∣
      (∏ j : Fin k, (d ⟨j.val, by omega⟩ : ℤ)) by exact_mod_cast hint
  set e : Fin k → Fin n := fun j => ⟨j.val, by omega⟩ with he_def
  set P_ℤ := (↑P : Matrix (Fin n) (Fin n) ℤ)
  set Q_ℤ := (↑Q : Matrix (Fin n) (Fin n) ℤ)
  have hmat_int : Matrix.diagonal (fun m : Fin n => (d m : ℤ)) =
      P_ℤ * Matrix.diagonal (fun m => (c m : ℤ)) * Q_ℤ := by
    ext i j; have h := congr_arg (fun (g : GL (Fin n) ℚ) => (↑g : Matrix _ _ ℚ) i j) hcd
    simp only [diagMat_val n d hd_pos, diagMat_val n c hc_pos, Matrix.diagonal_apply,
      Units.val_mul, Matrix.mul_apply,
      show ∀ i j, (↑(mapGL ℚ P) : Matrix _ _ ℚ) i j = ↑(P.val i j) from fun i j => by
        simp [mapGL_coe_matrix, algebraMap_int_eq, Matrix.map_apply],
      show ∀ i j, (↑(mapGL ℚ Q) : Matrix _ _ ℚ) i j = ↑(Q.val i j) from fun i j => by
        simp [mapGL_coe_matrix, algebraMap_int_eq, Matrix.map_apply]] at h
    simp only [Matrix.diagonal_apply, Matrix.mul_apply]; exact_mod_cast h
  have he_inj : Function.Injective e := by intro i j h; exact Fin.ext (Fin.mk.inj h)
  have hprod_d : ∏ j : Fin k, (d (e j) : ℤ) =
      det ((P_ℤ * Matrix.diagonal (fun m => (c m : ℤ)) * Q_ℤ).submatrix e e) := by
    rw [← hmat_int]
    rw [show (Matrix.diagonal (fun m : Fin n => (d m : ℤ))).submatrix e e =
        Matrix.diagonal (fun j : Fin k => (d (e j) : ℤ)) from by
      ext i j; simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, he_inj.eq_iff]]
    exact Matrix.det_diagonal.symm
  rw [hprod_d]
  have hcb : det ((P_ℤ * Matrix.diagonal (fun m => (c m : ℤ)) * Q_ℤ).submatrix e e) =
      ∑ g : Fin k → Fin n, (∏ i : Fin k, (c (g i) : ℤ)) *
        ((∏ i : Fin k, Q_ℤ (g i) (e i)) * det (P_ℤ.submatrix e g)) := by
    simp only [Matrix.det_apply', Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    rw [Finset.sum_comm]; congr 1; ext g; congr 1; ext σ
    simp only [Finset.prod_mul_distrib]; ring
  rw [hcb]
  apply Finset.dvd_sum; intro g _
  by_cases hg : Function.Injective g
  · apply dvd_mul_of_dvd_left
    exact_mod_cast divChain_prod_dvd_of_injective (n := n) hc k hk g hg
  · simp only [Function.not_injective_iff] at hg; obtain ⟨j₁, j₂, hgeq, hjne⟩ := hg
    have : det (P_ℤ.submatrix e g) = 0 := Matrix.det_zero_of_column_eq hjne (fun i => by
      simp only [Matrix.submatrix_apply, hgeq])
    simp [this]

/-- The elementary divisors are uniquely determined by the double coset. -/
theorem diagonal_representative_unique (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hda : DivChain n a) (hdb : DivChain n b)
    (heq : TDiag a = TDiag b) : a = b := by
  rw [T_diag_eq_iff a b ha hb] at heq
  have hmem : (diagMat n b : GL (Fin n) ℚ) ∈ DoubleCoset.doubleCoset
      (diagMat n a : GL (Fin n) ℚ) (SLnZSubgroup n) (SLnZSubgroup n) :=
    heq ▸ DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at hmem; obtain ⟨_, ⟨L, rfl⟩, _, ⟨R, rfl⟩, hmat⟩ := hmem
  funext i
  have hprod₁ :=
    partialProd_eq_of_SLnZ_equiv (n := n) ha hb hda hdb L R hmat (i.val + 1) (by omega)
  have hprod₂ :=
    partialProd_eq_of_SLnZ_equiv (n := n) ha hb hda hdb L R hmat i.val (by omega)
  have split_eq : ∀ (c : Fin n → ℕ),
      ∏ j : Fin (i.val + 1), c ⟨j.val, by omega⟩ =
      (∏ j : Fin i.val, c ⟨j.val, by omega⟩) * c i := by
    intro c; rw [Fin.prod_univ_castSucc]; congr 1
  rw [split_eq a, split_eq b, hprod₂] at hprod₁
  exact Nat.eq_of_mul_eq_mul_left
    (Finset.prod_pos (fun j _ => hb ⟨j.val, by omega⟩)) hprod₁

/-- The Hecke algebra is spanned by diagonal double coset elements `T(a₁,...,aₙ)`. -/
theorem T_diag_span (f : HeckeAlgebra n) :
    ∃ (S : Finset { p : Fin n → ℕ // (∀ i, 0 < p i) ∧ DivChain n p }) (c : S → ℤ),
      f = ∑ s ∈ S.attach, c s • TElem s.1.1 := by
  have h_rep : ∀ t : HeckeCoset (GLPair n),
      ∃ (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hdiv : DivChain n a), t = TDiag a := by
    intro t
    obtain ⟨a, ha, hdiv, hT⟩ := exists_diagonal_representative n (HeckeCoset.rep t)
    have ht : (⟦HeckeCoset.rep t⟧ : HeckeCoset (GLPair n)) = t := Quotient.out_eq t
    exact ⟨a, ha, hdiv, ht ▸ hT⟩
  choose a_fn ha_fn hdiv_fn hrep_fn using h_rep
  let toSub : HeckeCoset (GLPair n) → { p : Fin n → ℕ // (∀ i, 0 < p i) ∧ DivChain n p } :=
    fun t => ⟨a_fn t, ha_fn t, hdiv_fn t⟩
  set S : Finset { p : Fin n → ℕ // (∀ i, 0 < p i) ∧ DivChain n p } := f.support.image toSub
  have htoSub_inj : ∀ t₁ t₂ : HeckeCoset (GLPair n), toSub t₁ = toSub t₂ → t₁ = t₂ := by
    intro t₁ t₂ h; have ha : a_fn t₁ = a_fn t₂ := congr_arg Subtype.val h
    calc t₁ = TDiag (a_fn t₁) := hrep_fn t₁
      _ = TDiag (a_fn t₂) := by simp only [TDiag, diagMatDelta, ha]
      _ = t₂ := (hrep_fn t₂).symm
  refine ⟨S, fun s => f.toFun (TDiag s.1.1), ?_⟩
  have h_smul : ∀ (a : Fin n → ℕ) (c : ℤ), c • TElem a = Finsupp.single (TDiag a) c := by
    intro a c; unfold TElem; rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  simp_rw [h_smul]
  have h_Tdiag : ∀ (s : { p : Fin n → ℕ // (∀ i, 0 < p i) ∧ DivChain n p })
      (t : HeckeCoset (GLPair n)), toSub t = s → TDiag s.1 = t := by
    intro s t hts; convert (hrep_fn t).symm using 2; exact (congr_arg Subtype.val hts).symm
  apply Finsupp.ext; intro x
  rw [Finsupp.finsetSum_apply]
  by_cases hx : x ∈ f.support
  · have hmem : (⟨a_fn x, ha_fn x, hdiv_fn x⟩ :
        { p : Fin n → ℕ // (∀ i, 0 < p i) ∧ DivChain n p }) ∈ S :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rw [Finset.sum_eq_single_of_mem ⟨⟨a_fn x, ha_fn x, hdiv_fn x⟩, hmem⟩
      (Finset.mem_attach _ _)]
    · simp only [show TDiag (a_fn x) = x from (hrep_fn x).symm, Finsupp.single_eq_same]; rfl
    · intro s _ hs; apply Finsupp.single_eq_of_ne
      intro heq; apply hs; apply Subtype.ext
      obtain ⟨t, _, hts⟩ := Finset.mem_image.mp s.2
      have h_tx : t = x := (h_Tdiag s.1 t hts).symm.trans heq.symm
      subst h_tx; exact hts.symm
  · have hfx : Finsupp.toFun f x = 0 := Finsupp.notMem_support_iff.mp hx
    change Finsupp.toFun f x = _; rw [hfx]
    symm; apply Finset.sum_eq_zero; intro s _
    exact Finsupp.single_eq_of_ne (fun heq => by
      obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp s.2
      have h_tx : t = x := (h_Tdiag s.1 t hts).symm.trans heq.symm
      subst h_tx; exact absurd ht hx)

end SmithNormalForm

end HeckeRing.GLn
