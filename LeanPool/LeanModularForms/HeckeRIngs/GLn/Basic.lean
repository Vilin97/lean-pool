/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Commensurable
import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic

/-!
# GL_n HeckePair

Constructs the canonical `HeckePair (GL (Fin n) ℚ)` with:
- `H = SL_n(ℤ)` (embedded in GL_n(ℚ))
- `Δ = {α ∈ M_n(ℤ) ∩ GL_n(ℚ) | det(α) > 0}` (integer matrices with positive determinant)

This is the foundation for the Hecke ring of GL_n following Shimura §3.2.

## Main definitions

* `SLnZSubgroup` — `SL_n(ℤ)` as a subgroup of `GL_n(ℚ)` (via mathlib's `mapGL ℚ`)
* `posDetIntSubmonoid` — positive-determinant integer matrices as a submonoid of `GL_n(ℚ)`
* `GLPair` — the standard `HeckePair`

## Main results

* `SLnZ_le_posDetInt` — `SL_n(ℤ) ⊆ Δ`
* `posDetInt_le_commensurator` — `Δ ⊆ commensurator(SL_n(ℤ))`
-/

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable (n : ℕ)

section Embedding

/-- `SL_n(ℤ)` as a subgroup of `GL_n(ℚ)`, via `mapGL ℚ : SL(n, ℤ) →* GL(n, ℚ)`.
    Following mathlib's pattern for arithmetic subgroups. -/
noncomputable abbrev SLnZSubgroup : Subgroup (GL (Fin n) ℚ) :=
  (mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ).range

/-- Coercion from `SL_n(ℤ)` to `GL_n(ℚ)` via `mapGL ℚ`. -/
noncomputable scoped instance SLnZCoe :
    Coe (SpecialLinearGroup (Fin n) ℤ) (GL (Fin n) ℚ) :=
  ⟨mapGL ℚ⟩


lemma coe_mem_SLnZ (σ : SpecialLinearGroup (Fin n) ℤ) :
    (σ : GL (Fin n) ℚ) ∈ SLnZSubgroup n := ⟨σ, rfl⟩

end Embedding

section PosDetInt

/-- An element of `GL_n(ℚ)` has integer matrix entries if its underlying matrix
    is the image of an integer matrix under `ℤ → ℚ`. -/
def HasIntEntries (g : GL (Fin n) ℚ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℤ,
    (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ)

lemma SLnZ_subgroup_hasIntEntries {g : GL (Fin n) ℚ}
    (hg : g ∈ SLnZSubgroup n) : HasIntEntries n g := by
  obtain ⟨σ, rfl⟩ := hg
  exact ⟨σ.val, by simp [mapGL_coe_matrix, algebraMap_int_eq]⟩

/-- The identity matrix has integer entries. -/
@[simp]
lemma hasIntEntries_one : HasIntEntries n (1 : GL (Fin n) ℚ) :=
  ⟨1, by ext i j; simp [Matrix.map_apply, Matrix.one_apply]⟩

/-- Product of integer-entry matrices has integer entries. -/
lemma HasIntEntries.mul {a b : GL (Fin n) ℚ} (ha : HasIntEntries n a) (hb : HasIntEntries n b) :
    HasIntEntries n (a * b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A * B, by ext i j; simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]⟩

/-- `det (A.map Int.cast) = ↑(det A)` for integer matrices cast to `ℚ`. -/
lemma det_intMat_cast (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.map (Int.cast : ℤ → ℚ)).det = (A.det : ℚ) := by
  have h : A.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix A := by
    ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [h, ← RingHom.map_det, Int.coe_castRingHom]

/-- `(A.map cast) * (B.map cast) = (A * B).map cast` for integer matrices cast to `ℚ`. -/
private lemma intMat_map_mul (A B : Matrix (Fin n) (Fin n) ℤ) :
    (A.map (Int.cast : ℤ → ℚ)) * (B.map (Int.cast : ℤ → ℚ)) =
    (A * B).map (Int.cast : ℤ → ℚ) := by
  ext i j; simp [Matrix.mul_apply, Matrix.map_apply]

/-- The submonoid of `GL_n(ℚ)` consisting of invertible matrices with integer entries
    and positive determinant. This is Shimura's `Δ`. -/
noncomputable def posDetIntSubmonoid : Submonoid (GL (Fin n) ℚ) where
  carrier := {g | HasIntEntries n g ∧ 0 < (↑g : Matrix (Fin n) (Fin n) ℚ).det}
  one_mem' := ⟨hasIntEntries_one n, by simp⟩
  mul_mem' := by
    intro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
    exact ⟨HasIntEntries.mul (n := n) ha hb, by
      simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]; exact mul_pos hda hdb⟩

end PosDetInt

section Pair

/-- `SL_n(ℤ) ⊆ Δ`: elements of `SL_n(ℤ)` have integer entries and det = 1 > 0. -/
lemma SLnZ_le_posDetInt : (SLnZSubgroup n).toSubmonoid ≤ posDetIntSubmonoid n := by
  intro g hg
  rw [Subgroup.mem_toSubmonoid, MonoidHom.mem_range] at hg
  obtain ⟨A, rfl⟩ := hg
  refine ⟨⟨A.val, by simp [mapGL_coe_matrix, algebraMap_int_eq]⟩, ?_⟩
  simp [det_intMat_cast, A.prop]

/-! ### Helper lemmas for the commensurator proof (Shimura Lemma 3.10) -/

/-- `mapGL ℚ` is injective on `SL_n(ℤ)`. -/
private lemma mapGL_injective : Function.Injective
    (mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ) :=
  SpecialLinearGroup.mapGL_injective

/-- Kernel element of `SL_n(ℤ) → SL_n(ℤ/dℤ)` has entries congruent to identity mod d. -/
private lemma ker_entry_dvd (d : ℕ) [NeZero d] (γ : SpecialLinearGroup (Fin n) ℤ)
    (hγ : γ ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod d))).ker) (i j : Fin n) :
    (d : ℤ) ∣ (γ.val i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) := by
  rw [MonoidHom.mem_ker] at hγ
  have h := congr_fun₂ (congr_arg Subtype.val hγ) i j
  simp only [SpecialLinearGroup.map, RingHom.mapMatrix_apply, Int.coe_castRingHom, MonoidHom.coe_mk,
    OneHom.coe_mk, map_apply, coe_one] at h
  rw [Matrix.one_apply] at h ⊢
  split_ifs at h ⊢
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; simp [h])
  · rw [sub_zero]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

/-- When `d | (gamma - I)` entry-wise, decompose `gamma = I + d * M`. -/
private lemma gamma_decompose (d : ℤ) (gamma : Matrix (Fin n) (Fin n) ℤ)
    (hgamma : ∀ i j : Fin n, d ∣ (gamma i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j)) :
    gamma = 1 + d • Matrix.of fun i j => (gamma i j - (1 : Matrix _ _ ℤ) i j) / d := by
  ext i j; simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply]; simp only [Matrix.one_apply] at hgamma
  nlinarith [mul_comm ((gamma i j - if i = j then 1 else 0) / d) d,
             Int.ediv_mul_cancel (hgamma i j)]

/-- If `d | (γ - I)` entry-wise, then `d | (adj(A) * γ * A)` entry-wise.
    Key: `adj(A) * (I + dM) * A = d·I + d·(adj(A)·M·A)`. -/
private lemma adjugate_conj_dvd (A gamma : Matrix (Fin n) (Fin n) ℤ)
    (hgamma : ∀ i j : Fin n, A.det ∣ (gamma i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j))
    (i j : Fin n) :
    A.det ∣ (A.adjugate * gamma * A) i j := by
  set M := Matrix.of fun i j => (gamma i j - (1 : Matrix _ _ ℤ) i j) / A.det
  have : A.adjugate * gamma * A = A.adjugate * A + A.det • (A.adjugate * M * A) := by
    rw [gamma_decompose n A.det gamma hgamma]
    conv_lhs => rw [mul_add, Matrix.mul_one, mul_smul_comm]
    rw [add_mul, smul_mul_assoc]
  rw [this, adjugate_mul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

/-- If `d | P i j` for all entries and `det(P) = d ^ n`, then
    `det(P / d) = 1`, where the division is entry-wise integer division. -/
private lemma det_entrywise_div_eq_one (d : ℤ) (P : Matrix (Fin n) (Fin n) ℤ)
    (hdvd : ∀ i j : Fin n, d ∣ P i j) (hd : d ≠ 0) (hdet : (P.det : ℚ) = (d : ℚ) ^ n) :
    (Matrix.of fun i j => P i j / d).det = 1 := by
  suffices h : ((Matrix.of fun i j => P i j / d).det : ℚ) = 1 by exact_mod_cast h
  have h_mat_eq : (Matrix.of fun i j => P i j / d).map (Int.cast : ℤ → ℚ) =
      (d : ℚ)⁻¹ • (P.map (Int.cast : ℤ → ℚ)) := by
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [Int.cast_div (hdvd i j) (Int.cast_ne_zero.mpr hd)]; ring
  have hdQ : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  rw [← det_intMat_cast, h_mat_eq, det_smul, Fintype.card_fin, det_intMat_cast, hdet]
  exact by rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero n hdQ)

variable [NeZero n]

/-- The integer matrix `(adj(A) * γ * A) / det(A)` has determinant 1
    when `det(γ) = 1`. -/
private lemma conj_mat_det_one (A gamma : Matrix (Fin n) (Fin n) ℤ) (hgamma_det : gamma.det = 1)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A.adjugate * gamma * A) i j) (hAdet : A.det ≠ 0) :
    (Matrix.of fun i j => (A.adjugate * gamma * A) i j / A.det).det = 1 := by
  apply det_entrywise_div_eq_one n A.det _ hdvd hAdet
  simp only [Matrix.det_mul, det_adjugate, hgamma_det]
  push_cast; rw [mul_one, Fintype.card_fin, ← pow_succ,
    Nat.sub_one_add_one_eq_of_pos (NeZero.pos n)]

omit [NeZero n] in
/-- If `A * δ = γ * A` at the integer level, then `g * δ_GL = γ_GL * g` at the GL level,
    so `δ_GL = g⁻¹ * γ_GL * g`. -/
private lemma int_mul_eq (A gamma : Matrix (Fin n) (Fin n) ℤ) (hAdet : A.det ≠ 0)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A.adjugate * gamma * A) i j) :
    A * (Matrix.of fun i j => (A.adjugate * gamma * A) i j / A.det) = gamma * A := by
  set delta := Matrix.of fun i j => (A.adjugate * gamma * A) i j / A.det
  have ha : A.det • delta = A.adjugate * gamma * A := by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, delta]
    exact Int.mul_ediv_cancel' (hdvd i j)
  suffices h : A.det • (A * delta) = A.det • (gamma * A) by
    ext i j; exact mul_left_cancel₀ hAdet
      (by simpa [Matrix.smul_apply, smul_eq_mul] using congr_fun₂ h i j)
  rw [← mul_smul_comm, ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_adjugate, smul_mul_assoc, one_mul, smul_mul_assoc]

/-- Main step: for `g` with integer matrix `A` and `det(A) > 0`,
    kernel elements of `SL_n(ℤ) → SL_n(ℤ/dℤ)` conjugated by `g⁻¹` remain in `SL_n(ℤ)`.
    This is the mathematical heart of Shimura's Lemma 3.10. -/
private lemma conj_ker_mem_SLnZ (g : GL (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ)) (hAdet : A.det ≠ 0)
    (γ : SpecialLinearGroup (Fin n) ℤ)
    (hγ : γ ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker) :
    g⁻¹ * (γ : GL (Fin n) ℚ) * g ∈ SLnZSubgroup n := by
  have hnatAbs_ne : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet⟩
  have h_entry : ∀ i j, A.det ∣ (γ.val i j - (1 : Matrix _ _ ℤ) i j) := by
    intro i j; exact Int.natAbs_dvd.mp (ker_entry_dvd n A.det.natAbs γ hγ i j)
  have hdvd := adjugate_conj_dvd n A γ.val h_entry
  set delta_mat := Matrix.of fun i j => (A.adjugate * γ.val * A) i j / A.det with hdelta_def
  have hdelta_det : delta_mat.det = 1 := conj_mat_det_one n A γ.val γ.prop hdvd hAdet
  set delta : SpecialLinearGroup (Fin n) ℤ := ⟨delta_mat, hdelta_det⟩
  rw [SLnZSubgroup, MonoidHom.mem_range]
  refine ⟨delta, ?_⟩
  have h_int_eq : A * delta_mat = γ.val * A := int_mul_eq n A γ.val hAdet hdvd
  have h_mat_eq : (g * (delta : GL (Fin n) ℚ)).val =
      ((γ : GL (Fin n) ℚ) * g).val := by
    change (g.val * (delta : GL (Fin n) ℚ).val : Matrix _ _ ℚ) =
         ((γ : GL (Fin n) ℚ).val * g.val : Matrix _ _ ℚ)
    simp only [mapGL_coe_matrix, algebraMap_int_eq,
      map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom] at *
    rw [hA, intMat_map_mul, intMat_map_mul, h_int_eq]
  have h_unit_eq : g * (delta : GL (Fin n) ℚ) = (γ : GL (Fin n) ℚ) * g := Units.ext h_mat_eq
  calc (delta : GL (Fin n) ℚ)
      = g⁻¹ * (g * (delta : GL (Fin n) ℚ)) := by rw [inv_mul_cancel_left]
    _ = g⁻¹ * ((γ : GL (Fin n) ℚ) * g) := by rw [h_unit_eq]
    _ = g⁻¹ * (γ : GL (Fin n) ℚ) * g := by rw [mul_assoc]

omit [NeZero n] in
/-- Reverse direction of `adjugate_conj_dvd`: `d | (γ - I)` entry-wise implies
    `d | (A * γ * adj(A))` entry-wise. -/
private lemma conj_dvd_reverse (A gamma : Matrix (Fin n) (Fin n) ℤ)
    (hgamma : ∀ i j : Fin n, A.det ∣ (gamma i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j))
    (i j : Fin n) :
    A.det ∣ (A * gamma * A.adjugate) i j := by
  set M := Matrix.of fun i j =>
    (gamma i j - (1 : Matrix _ _ ℤ) i j) / A.det
  have : A * gamma * A.adjugate =
      A * A.adjugate + A.det • (A * M * A.adjugate) := by
    rw [gamma_decompose n A.det gamma hgamma]
    conv_lhs => rw [mul_add, Matrix.mul_one, mul_smul_comm]
    rw [add_mul, smul_mul_assoc]
  rw [this, mul_adjugate]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

/-- Reverse direction of `conj_mat_det_one`: `(A * γ * adj(A)) / det(A)` has determinant 1
    when `det(γ) = 1`. -/
private lemma conj_mat_det_one_reverse
    (A gamma : Matrix (Fin n) (Fin n) ℤ) (hgamma_det : gamma.det = 1)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A * gamma * A.adjugate) i j) (hAdet : A.det ≠ 0) :
    (Matrix.of fun i j => (A * gamma * A.adjugate) i j / A.det).det = 1 := by
  apply det_entrywise_div_eq_one n A.det _ hdvd hAdet
  simp only [Matrix.det_mul, det_adjugate, hgamma_det, Fintype.card_fin]
  push_cast; simp only [det_intMat_cast]; rw [mul_one,
    show (A.det : ℚ) * (A.det : ℚ) ^ (n - 1) = (A.det : ℚ) ^ n from by
      rw [← pow_succ']; congr 1; exact Nat.succ_pred_eq_of_pos (NeZero.pos n)]

omit [NeZero n] in
/-- Reverse direction of `int_mul_eq`: `δ * A = A * γ` where
    `δ = (A * γ * adj(A)) / det(A)`. -/
private lemma int_mul_eq_reverse (A gamma : Matrix (Fin n) (Fin n) ℤ) (hAdet : A.det ≠ 0)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A * gamma * A.adjugate) i j) :
    (Matrix.of fun i j => (A * gamma * A.adjugate) i j / A.det) * A = A * gamma := by
  set delta := Matrix.of fun i j => (A * gamma * A.adjugate) i j / A.det
  have ha : A.det • delta = A * gamma * A.adjugate := by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, delta]
    exact Int.mul_ediv_cancel' (hdvd i j)
  suffices h : A.det • (delta * A) = A.det • (A * gamma) by
    ext i j; exact mul_left_cancel₀ hAdet
      (by simpa [Matrix.smul_apply, smul_eq_mul] using congr_fun₂ h i j)
  rw [← smul_mul_assoc, ha, Matrix.mul_assoc, adjugate_mul, mul_smul_comm, Matrix.mul_one]

/-- Reverse direction of `conj_ker_mem_SLnZ`: kernel elements conjugated by `g`
    (rather than `g⁻¹`) remain in `SL_n(ℤ)`. -/
private lemma conj_ker_mem_SLnZ_inv (g : GL (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ)) (hAdet : A.det ≠ 0)
    (γ : SpecialLinearGroup (Fin n) ℤ)
    (hγ : γ ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker) :
    g * (γ : GL (Fin n) ℚ) * g⁻¹ ∈ SLnZSubgroup n := by
  have hnatAbs_ne : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet⟩
  have h_entry : ∀ i j, A.det ∣ (γ.val i j - (1 : Matrix _ _ ℤ) i j) := by
    intro i j; exact Int.natAbs_dvd.mp (ker_entry_dvd n A.det.natAbs γ hγ i j)
  have hdvd := conj_dvd_reverse n A γ.val h_entry
  set delta_mat := Matrix.of fun i j => (A * γ.val * A.adjugate) i j / A.det
  have hdelta_det : delta_mat.det = 1 :=
    conj_mat_det_one_reverse n A γ.val γ.prop hdvd hAdet
  set delta : SpecialLinearGroup (Fin n) ℤ := ⟨delta_mat, hdelta_det⟩
  have h_int_eq : delta_mat * A = A * γ.val := int_mul_eq_reverse n A γ.val hAdet hdvd
  have h_mat_eq : ((delta : GL (Fin n) ℚ) * g).val =
      (g * (γ : GL (Fin n) ℚ)).val := by
    change ((delta : GL (Fin n) ℚ).val * g.val : Matrix _ _ ℚ) =
         (g.val * (γ : GL (Fin n) ℚ).val : Matrix _ _ ℚ)
    simp only [mapGL_coe_matrix, algebraMap_int_eq,
      map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom] at *
    rw [hA, intMat_map_mul, intMat_map_mul, h_int_eq]
  have h_unit_eq : (delta : GL (Fin n) ℚ) * g = g * (γ : GL (Fin n) ℚ) := Units.ext h_mat_eq
  rw [SLnZSubgroup, MonoidHom.mem_range]
  exact ⟨delta, by rw [← h_unit_eq]; group⟩

/-- `Δ ⊆ commensurator(SL_n(ℤ))`: for any integer matrix `α` with positive determinant,
    `SL_n(ℤ)` and `α · SL_n(ℤ) · α⁻¹` are commensurable.

    The key idea (Shimura Lemma 3.10): if `α` has integer entries with `det(α) = d > 0`,
    then the congruence subgroup `Γ(d) = ker(SL_n(ℤ) → SL_n(ℤ/dℤ))` has finite index
    in `SL_n(ℤ)` and is contained in both `SL_n(ℤ) ∩ α·SL_n(ℤ)·α⁻¹` and
    `SL_n(ℤ) ∩ α⁻¹·SL_n(ℤ)·α`, establishing commensurability. -/
lemma posDetInt_le_commensurator :
    posDetIntSubmonoid n ≤ (commensurator (SLnZSubgroup n)).toSubmonoid := by
  intro g ⟨⟨A, hA⟩, hdet⟩
  rw [Subgroup.mem_toSubmonoid, commensurator_mem_iff]
  set H := SLnZSubgroup n
  have hAdet_pos : 0 < A.det := by
    have h1 : (0 : ℚ) < (A.det : ℚ) := by
      have h2 : (A.det : ℚ) = (A.map (Int.cast : ℤ → ℚ)).det := (det_intMat_cast n A).symm
      rw [h2, ← hA]; exact hdet
    exact Int.cast_pos.mp h1
  have hAdet_ne : A.det ≠ 0 := ne_of_gt hAdet_pos
  have hnatAbs_ne : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet_ne⟩
  set phi : SpecialLinearGroup (Fin n) ℤ →* SpecialLinearGroup (Fin n) (ZMod A.det.natAbs) :=
    SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs)) with hphi_def
  set K := phi.ker.map ((mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ)) with hK_def
  have hK_le_H : K ≤ H := by
    intro x hx; simp only [K, Subgroup.mem_map] at hx
    obtain ⟨γ, _, rfl⟩ := hx; exact ⟨γ, rfl⟩
  have hK_relIndex : K.relIndex H ≠ 0 := by
    have h1 : H = Subgroup.map ((mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ)) ⊤ := by
      simp [H, MonoidHom.range_eq_map]
    rw [hK_def, h1, Subgroup.relIndex_map_map_of_injective _ _ (mapGL_injective n),
      Subgroup.relIndex_top_right]
    exact (Subgroup.finiteIndex_ker phi).index_ne_zero
  have hK_le_gH : K ≤ ConjAct.toConjAct g • H := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [K, Subgroup.mem_map] at hx
    obtain ⟨γ, hγ_ker, rfl⟩ := hx
    change (ConjAct.toConjAct g)⁻¹ • (γ : GL (Fin n) ℚ) ∈ H
    rw [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]
    exact conj_ker_mem_SLnZ n g A hA hAdet_ne γ hγ_ker
  have hK_le_ginvH : K ≤ ConjAct.toConjAct g⁻¹ • H := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.toConjAct_inv, inv_inv]
    simp only [K, Subgroup.mem_map] at hx
    obtain ⟨γ, hγ_ker, rfl⟩ := hx
    change ConjAct.toConjAct g • (γ : GL (Fin n) ℚ) ∈ H
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    exact conj_ker_mem_SLnZ_inv n g A hA hAdet_ne γ hγ_ker
  constructor
  · exact ne_zero_of_dvd_ne_zero hK_relIndex
      (Subgroup.relIndex_dvd_of_le_left H hK_le_gH)
  · rw [show H.relIndex (ConjAct.toConjAct g • H) =
        (ConjAct.toConjAct g⁻¹ • H).relIndex H from by
      have h1 : ConjAct.toConjAct g⁻¹ • (ConjAct.toConjAct g • H) = H := by
        rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      have := Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct g⁻¹) H
        (ConjAct.toConjAct g • H)
      rw [h1] at this; exact this.symm]
    exact ne_zero_of_dvd_ne_zero hK_relIndex
      (Subgroup.relIndex_dvd_of_le_left H hK_le_ginvH)

/-- The standard arithmetic group pair for number theory:
    `SL_n(ℤ) ≤ Δ ≤ commensurator(SL_n(ℤ))` in `GL_n(ℚ)`. -/
noncomputable def GLPair : HeckePair (GL (Fin n) ℚ) where
  H := SLnZSubgroup n
  Δ := posDetIntSubmonoid n
  h₀ := SLnZ_le_posDetInt n
  h₁ := posDetInt_le_commensurator n

end Pair

section API

variable [NeZero n]

/-- The Hecke algebra for `GL_n`. -/
abbrev HeckeAlgebra := 𝕋 (GLPair n) ℤ

/-- Embed an integer matrix with positive determinant into `Δ` as a `GL_n(ℚ)` element. -/
noncomputable def intMatToDelta (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    (GLPair n).Δ := by
  have hne : (A.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [det_intMat_cast]; exact_mod_cast hdet.ne'
  have hval : (↑(GeneralLinearGroup.mkOfDetNeZero _ hne) : Matrix (Fin n) (Fin n) ℚ) =
      A.map (Int.cast : ℤ → ℚ) := rfl
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hne,
    ⟨A, hval⟩,
    by rw [hval, det_intMat_cast]; exact_mod_cast hdet⟩

/-- Embed an integer matrix with positive determinant into a double coset element `HeckeCoset`. -/
noncomputable def intMatToHeckeCoset (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    HeckeRing.HeckeCoset (GLPair n) :=
  ⟦intMatToDelta n A hdet⟧

end API

end HeckeRing.GLn
