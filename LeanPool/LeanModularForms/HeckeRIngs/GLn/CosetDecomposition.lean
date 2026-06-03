/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.GLn.DiagonalCosets

/-!
# Left Coset Decomposition for GL_n Hecke Ring

Upper-triangular coset representatives for `Γ · diag(a) · Γ`, where `Γ = SL_n(ℤ)`.

For `a = (a₁,...,aₙ)` with `a₁ | a₂ | ⋯ | aₙ`, left coset representatives include
upper-triangular matrices `M = diag(a) · γ` where `γ` is unipotent upper-triangular
with `γ_{ij} ∈ {0,...,(a_j/a_i) - 1}` for `i < j`. These give `∏_{i<j}(a_j/a_i)`
distinct left cosets.

## Main definitions

* `UpperTriRep` -- bounded entry assignment: `γ_{ij} ∈ Fin (a_j / a_i)` for `i < j`
* `upperTriMat` -- the upper-triangular integer matrix `M_{ij} = a_i · γ_{ij}`
* `upperTriGL` -- corresponding `GL_n(ℚ)` element

## Main results

* `upperTriMat_det` -- `det(M) = ∏ i, a_i`
* `upperTriMat_injective` -- different entries produce different matrices
* `upperTriGL_mem_doubleCoset` -- each representative lies in `Γ · diag(a) · Γ`
* `upperTriMat_distinct_cosets` -- distinct representatives give distinct left cosets

## References

* Shimura, Proposition 3.22
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

private lemma det_upper_tri {k : ℕ} {M : Matrix (Fin k) (Fin k) ℤ}
    (h : ∀ i j : Fin k, j < i → M i j = 0) :
    M.det = ∏ i, M i i := by
  simp only [det_apply]
  rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_univ 1)]
  · simp
  · intro σ _ hσ
    have hne : ∃ i, σ i ≠ i := by
      by_contra hc; push Not at hc
      exact hσ (Equiv.Perm.ext (fun i => by simp [hc i]))
    suffices hprod : ∏ i, M (σ i) i = 0 by simp [hprod]
    set S := Finset.univ.filter (fun i : Fin k => σ i ≠ i)
    have hS : S.Nonempty := by
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    set m := S.min' hS
    have hm_ne : σ m ≠ m := (Finset.mem_filter.mp (S.min'_mem hS)).2
    have hm_min : ∀ j, j < m → σ j = j := by
      intro j hj; by_contra hjne
      exact not_lt.mpr (Finset.min'_le S j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjne⟩)) hj
    have hσm_gt : m < σ m := by
      rcases lt_trichotomy m (σ m) with hlt | heq | hgt
      · exact hlt
      · exact absurd heq.symm hm_ne
      · exact absurd (σ.injective (hm_min (σ m) hgt)) hm_ne
    exact Finset.prod_eq_zero (Finset.mem_univ m) (h (σ m) m hσm_gt)

variable (n : ℕ)

/-- Bounded entry assignment for upper-triangular representatives:
    `B_{ij} ∈ Fin (a_j / a_i)` for `i < j`. -/
abbrev UpperTriRep (a : Fin n → ℕ) (hdiv : DivChain n a) :=
  -- `hdiv` records that `a` is a divisibility chain (so the quotients below are
  -- exact); it is consumed here so the type carries this provenance.
  let _ := hdiv
  (p : { ij : Fin n × Fin n // ij.1 < ij.2 }) → Fin (a p.val.2 / a p.val.1)

/-- Upper-triangular matrix with diagonal `a` and off-diagonal `M_{ij} = a_i * B_{ij}`. -/
def upperTriMat (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if h : i < j then (a i : ℤ) * (B ⟨(i, j), h⟩ : ℕ)
    else if i = j then (a i : ℤ)
    else 0

@[simp]
lemma upperTriMat_apply_lt (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv)
    {i j : Fin n} (h : i < j) :
    upperTriMat n a hdiv B i j = (a i : ℤ) * (B ⟨(i, j), h⟩ : ℕ) := by
  simp [upperTriMat, h]

@[simp]
lemma upperTriMat_apply_diag (a : Fin n → ℕ) (hdiv : DivChain n a)
    (B : UpperTriRep n a hdiv) (i : Fin n) :
    upperTriMat n a hdiv B i i = (a i : ℤ) := by
  simp [upperTriMat]

lemma upperTriMat_apply_gt (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv)
    {i j : Fin n} (h : j < i) :
    upperTriMat n a hdiv B i j = 0 := by
  simp [upperTriMat, not_lt.mpr (le_of_lt h), ne_of_gt h]

lemma upperTriMat_det (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    (upperTriMat n a hdiv B).det = ∏ i, (a i : ℤ) := by
  rw [det_upper_tri (fun i j h => upperTriMat_apply_gt n a hdiv B h)]
  congr 1; ext i; simp

lemma upperTriMat_det_pos (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i)
    (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    0 < (upperTriMat n a hdiv B).det := by
  rw [upperTriMat_det]
  exact Finset.prod_pos fun i _ => by exact_mod_cast hpos i

lemma upperTriMat_injective (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i) (hdiv : DivChain n a) :
    Function.Injective (upperTriMat n a hdiv) := by
  intro B₁ B₂ h
  funext ⟨⟨i, j⟩, hij⟩
  have h_eq := congr_fun₂ h i j
  simp only [upperTriMat_apply_lt, hij] at h_eq
  have h_ai_pos : (a i : ℤ) ≠ 0 := by exact_mod_cast (hpos i).ne'
  have := mul_left_cancel₀ h_ai_pos h_eq
  exact Fin.ext (by exact_mod_cast this)

/-- The upper-triangular representative as a `GL_n(ℚ)` element. -/
noncomputable def upperTriGL (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i)
    (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    GL (Fin n) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero
    ((upperTriMat n a hdiv B).map (Int.cast : ℤ → ℚ))
    (by
      rw [det_intMat_cast, upperTriMat_det]
      have := upperTriMat_det_pos n a hpos hdiv B
      rw [upperTriMat_det] at this
      exact_mod_cast this.ne')

@[simp]
lemma upperTriGL_val (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i) (hdiv : DivChain n a)
    (B : UpperTriRep n a hdiv) : (↑(upperTriGL n a hpos hdiv B) : Matrix (Fin n) (Fin n) ℚ) =
    (upperTriMat n a hdiv B).map (Int.cast : ℤ → ℚ) := rfl

lemma upperTriGL_hasIntEntries (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i)
    (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    HasIntEntries n (upperTriGL n a hpos hdiv B) :=
  ⟨upperTriMat n a hdiv B, rfl⟩

lemma upperTriGL_mem_posDetInt (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i)
    (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    upperTriGL n a hpos hdiv B ∈ posDetIntSubmonoid n :=
  ⟨upperTriGL_hasIntEntries n a hpos hdiv B, by
    change 0 < ((upperTriMat n a hdiv B).map (Int.cast : ℤ → ℚ)).det
    rw [det_intMat_cast, upperTriMat_det]
    have := upperTriMat_det_pos n a hpos hdiv B
    rw [upperTriMat_det] at this
    exact_mod_cast this⟩

/-- The unipotent upper-triangular matrix with `1` on the diagonal and `B_{ij}` above. -/
def unipMat (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if h : i < j then (B ⟨(i, j), h⟩ : ℕ)
    else if i = j then 1
    else 0

lemma unipMat_det (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    (unipMat n a hdiv B).det = 1 := by
  rw [det_upper_tri (fun i j h => by simp [unipMat, not_lt.mpr (le_of_lt h), ne_of_gt h])]
  simp [unipMat]

/-- Each upper-triangular representative lies in `Γ · diag(a) · Γ`. -/
theorem upperTriGL_mem_doubleCoset (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i)
    (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    (upperTriGL n a hpos hdiv B : GL (Fin n) ℚ) ∈
    DoubleCoset.doubleCoset (diagMat n a : GL (Fin n) ℚ)
      (SLnZSubgroup n) (SLnZSubgroup n) := by
  rw [DoubleCoset.mem_doubleCoset]
  set γ_SL : SpecialLinearGroup (Fin n) ℤ := ⟨unipMat n a hdiv B, unipMat_det n a hdiv B⟩
  set γ_GL := (γ_SL : GL (Fin n) ℚ)
  refine ⟨1, (SLnZSubgroup n).one_mem, γ_GL, coe_mem_SLnZ n γ_SL, ?_⟩
  rw [one_mul]
  apply Units.ext
  change (upperTriMat n a hdiv B).map (Int.cast : ℤ → ℚ) =
    (↑(diagMat n a) : Matrix (Fin n) (Fin n) ℚ) *
    (↑(γ_SL : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)
  simp only [mapGL_coe_matrix, algebraMap_int_eq, diagMat_val n a hpos]
  ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_mul, zero_mul]
    change ((upperTriMat n a hdiv B i j : ℤ) : ℚ) =
      ((a i : ℤ) : ℚ) * ((unipMat n a hdiv B i j : ℤ) : ℚ)
    simp only [upperTriMat, unipMat]
    split_ifs <;> push_cast <;> ring
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- For `k ≠ j` and columns `< j` already identity-like, the product `σ i k * M₂ k j`
    contributes only from the `k = i, i < j` case. -/
private lemma coset_sum_eq {a : Fin n → ℕ} {hdiv : DivChain n a}
    {B₂ : UpperTriRep n a hdiv}
    {σ : SpecialLinearGroup (Fin n) ℤ}
    {i j : Fin n} (ih : ∀ (k : Fin n), k.val < j.val → ∀ (i : Fin n),
      σ.val i k = if i = k then 1 else 0) :
    ∑ k : Fin n, σ.val i k * upperTriMat n a hdiv B₂ k j =
      σ.val i j * (a j : ℤ) + (if i < j then upperTriMat n a hdiv B₂ i j else 0) := by
  set M₂ := upperTriMat n a hdiv B₂
  have h_sum_rest : ∀ k : Fin n, k ≠ j →
      σ.val i k * M₂ k j =
      if k = i ∧ i < j then M₂ i j else 0 := by
    intro k hkj
    rcases lt_or_ge k j with hkj' | hkj'
    · rw [ih k (by exact_mod_cast hkj') i]
      rcases eq_or_ne i k with rfl | hik
      · simp [hkj']
      · simp [hik, show k ≠ i from fun h => hik h.symm]
    · have hjk : j < k := lt_of_le_of_ne hkj' (Ne.symm hkj)
      have hM₂ : M₂ k j = 0 := upperTriMat_apply_gt n a hdiv B₂ hjk
      simp [hM₂, show ¬(k = i ∧ i < j) from
        fun ⟨hki, hilj⟩ => not_lt.mpr (le_of_lt (hki ▸ hjk)) hilj]
  rw [← Finset.sum_erase_add (f := fun k => σ.val i k * M₂ k j)
    Finset.univ (Finset.mem_univ j),
    show M₂ j j = (a j : ℤ) from upperTriMat_apply_diag n a hdiv B₂ j]
  suffices h_rest : ∑ x ∈ Finset.univ.erase j, σ.val i x * M₂ x j =
      if i < j then M₂ i j else 0 by linarith
  by_cases hij : i < j
  · simp only [hij, ite_true]
    rw [Finset.sum_eq_single_of_mem i
        (Finset.mem_erase.mpr ⟨Fin.ne_of_lt hij, Finset.mem_univ i⟩)]
    · rw [h_sum_rest i (Fin.ne_of_lt hij)]; simp [hij]
    · intro k hk hki
      rw [Finset.mem_erase] at hk; rw [h_sum_rest k hk.1]
      simp [show ¬(k = i ∧ i < j) from fun ⟨h, _⟩ => hki h]
  · simp only [hij, ite_false]
    apply Finset.sum_eq_zero; intro k hk
    rw [Finset.mem_erase] at hk; rw [h_sum_rest k hk.1]
    simp [show ¬(k = i ∧ i < j) from fun ⟨_, h⟩ => hij h]

/-- When `i < j`, the entry `σ i j` must be zero: the bounded difference of `B₁` and `B₂`
    cannot absorb a nonzero integer multiple of `a_j / a_i`. -/
private lemma coset_entry_zero_of_lt {a : Fin n → ℕ} {hpos : ∀ i, 0 < a i}
    {hdiv : DivChain n a}
    {B₁ B₂ : UpperTriRep n a hdiv}
    {σ : SpecialLinearGroup (Fin n) ℤ}
    {i j : Fin n} (hij : i < j) (h_eq : upperTriMat n a hdiv B₁ i j =
      σ.val i j * (a j : ℤ) + upperTriMat n a hdiv B₂ i j) :
    σ.val i j = 0 := by
  simp only [upperTriMat_apply_lt _ _ _ _ hij] at h_eq
  have h_dvd : a i ∣ a j := divChain_dvd n hdiv (le_of_lt hij)
  set q := a j / a i
  have hq_pos : 0 < q := divChain_div_pos n hpos hdiv (le_of_lt hij)
  have h_aj_eq : (a j : ℤ) = (a i : ℤ) * (q : ℤ) := by
    have h := Nat.div_mul_cancel h_dvd
    have : (q : ℤ) * (a i : ℤ) = (a j : ℤ) := by exact_mod_cast h
    linarith
  have h_ai_ne : (a i : ℤ) ≠ 0 := by exact_mod_cast (hpos i).ne'
  have h_cancel : σ.val i j * (q : ℤ) =
      ((B₁ ⟨(i, j), hij⟩ : ℕ) : ℤ) - ((B₂ ⟨(i, j), hij⟩ : ℕ) : ℤ) := by
    apply mul_left_cancel₀ h_ai_ne
    rw [← mul_assoc, mul_comm (a i : ℤ) (σ.val i j), mul_assoc, ← h_aj_eq]
    linarith
  have h1 : ((B₁ ⟨(i, j), hij⟩ : ℕ) : ℤ) < (q : ℤ) := by
    exact_mod_cast (B₁ ⟨(i, j), hij⟩).isLt
  have h2 : ((B₂ ⟨(i, j), hij⟩ : ℕ) : ℤ) < (q : ℤ) := by
    exact_mod_cast (B₂ ⟨(i, j), hij⟩).isLt
  by_contra hσ_ne
  have h_abs : (q : ℤ) ≤ |σ.val i j * (q : ℤ)| := by
    rw [abs_mul, abs_of_nonneg (by omega : (q : ℤ) ≥ 0)]
    exact le_mul_of_one_le_left (by omega) (Int.one_le_abs hσ_ne)
  rw [h_cancel] at h_abs
  rcases le_or_gt ((B₁ ⟨(i, j), hij⟩ : ℕ) : ℤ)
    ((B₂ ⟨(i, j), hij⟩ : ℕ) : ℤ) with h | h
  · rw [abs_of_nonpos (by omega)] at h_abs; omega
  · rw [abs_of_pos (by omega)] at h_abs; omega

/-- Distinct entry assignments give distinct left cosets of `SL_n(ℤ)`. -/
theorem upperTriMat_distinct_cosets (a : Fin n → ℕ)
    (hpos : ∀ i, 0 < a i) (hdiv : DivChain n a)
    (B₁ B₂ : UpperTriRep n a hdiv) (hne : B₁ ≠ B₂) :
    ∀ (γ : GL (Fin n) ℚ), γ ∈ SLnZSubgroup n →
      upperTriGL n a hpos hdiv B₁ ≠
        γ * upperTriGL n a hpos hdiv B₂ := by
  intro γ ⟨σ, hσ⟩ heq; subst hσ; apply hne; clear hne
  have hmat : upperTriMat n a hdiv B₁ = σ.val * upperTriMat n a hdiv B₂ := by
    have h := congr_arg Units.val heq
    have hσ_val : (↑(mapGL ℚ σ) : Matrix _ _ ℚ) = σ.val.map (Int.cast) := by
      simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
    simp only [Units.val_mul, upperTriGL_val, hσ_val] at h
    ext i j
    have hij := congr_fun (congr_fun h i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at hij
    exact_mod_cast hij
  set M₁ := upperTriMat n a hdiv B₁
  set M₂ := upperTriMat n a hdiv B₂
  suffices hσ_cols : ∀ (m : ℕ), ∀ (j : Fin n), j.val < m →
      ∀ (i : Fin n), σ.val i j = if i = j then 1 else 0 by
    have hσ_one : σ.val = 1 := by
      ext i j; rw [hσ_cols (j.val + 1) j (by omega) i, Matrix.one_apply]
    exact upperTriMat_injective n a hpos hdiv
      (show M₁ = M₂ by rw [hmat, hσ_one, Matrix.one_mul])
  intro m
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    intro j hj i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | hjeq
    · exact ih j hlt i
    · have h_eq : M₁ i j = ∑ k : Fin n, σ.val i k * M₂ k j := by
        rw [hmat]; simp [Matrix.mul_apply]
      have ih' : ∀ (k : Fin n), k.val < j.val → ∀ (i : Fin n),
          σ.val i k = if i = k then 1 else 0 :=
        fun k hk => ih k (hjeq ▸ hk)
      have h_sum := @coset_sum_eq n a hdiv B₂ σ i j ih'
      rw [h_sum] at h_eq
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [if_neg (Fin.ne_of_lt hij)]
        exact @coset_entry_zero_of_lt n a hpos hdiv B₁ B₂ σ i j hij
          (by simp only [hij, ↓reduceIte] at h_eq; exact h_eq)
      · simp only [lt_irrefl, ↓reduceIte, M₁, upperTriMat_apply_diag] at h_eq ⊢
        have h_ai_ne : (a i : ℤ) ≠ 0 := by exact_mod_cast (hpos i).ne'
        exact mul_right_cancel₀ h_ai_ne (by linarith)
      · rw [if_neg (Fin.ne_of_gt hij)]
        simp only [show ¬(i < j) from not_lt.mpr (le_of_lt hij), ↓reduceIte,
          M₁, upperTriMat_apply_gt _ _ _ _ hij] at h_eq
        have : (a j : ℤ) ≠ 0 := by exact_mod_cast (hpos j).ne'
        exact (mul_eq_zero.mp (by linarith)).resolve_right this

/-- The number of upper-triangular representatives equals `∏_{i<j} (a_j / a_i)`. -/
lemma upperTriRep_card (a : Fin n → ℕ) (hdiv : DivChain n a) :
    Fintype.card (UpperTriRep n a hdiv) =
    ∏ p : { ij : Fin n × Fin n // ij.1 < ij.2 }, (a p.val.2 / a p.val.1) := by
  unfold UpperTriRep
  rw [Fintype.card_pi]
  congr 1; ext p; exact Fintype.card_fin _

end HeckeRing.GLn
