/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.GLn.CosetDecomposition
import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Degree
import LeanPool.LeanModularForms.HeckeRIngs.GL2.CongruenceIndex

/-!
# Degree Formulas for GL_n Hecke Ring

Degree formulas for the diagonal Hecke operators `T(a₁,...,aₙ)`, including Gaussian binomial
coefficients for the prime-power case.

## Main definitions

* `gaussianBinom q n k` : the Gaussian binomial coefficient `[n choose k]_q`

## Main results

* `upperTriRep_card_le_HeckeCoset_deg` : `∏_{i<j} (a_j / a_i) ≤ deg(T(a₁,...,aₙ))`

## Important note on degree formulas

The degree of `T(a₁,...,aₙ)` is **not** simply `∏_{i<j} (aⱼ/aᵢ)`. The upper-triangular
representatives with fixed diagonal `(a₁,...,aₙ)` account for
`∏_{i<j}(aⱼ/aᵢ)` left cosets,
but the double coset also contains representatives with permuted diagonals (those whose
Hermite Normal Form has a different diagonal but the same Smith Normal Form).

**Counterexample:** For `n = 2`, `a = (1, p)` with `p` prime, the `UpperTriRep` count is `p`,
but the actual degree is `p + 1`. The additional representative is `[[p,0],[0,1]]`, which lies
in the double coset `SL₂(ℤ) · diag(1,p) · SL₂(ℤ)` but has a different diagonal.

**Correct formula for n = 2:** `deg(T(a₁,a₂)) = ψ(a₂/a₁)` where `ψ` is the Dedekind psi
function `ψ(d) = d · ∏_{p | d} (1 + 1/p)`. For the prime-power case needed for Theorem 3.24:
`deg(T(pⁱ, pⁱ⁺ᵏ)) = pᵏ⁻¹(p + 1)` for `k ≥ 1`.

## References

* Shimura, Proposition 3.14, 3.18, Theorem 3.24
-/

open HeckeRing HeckeRing.GL2 Finset CongruenceSubgroup Matrix.SpecialLinearGroup Matrix
  ModularGroup
open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

/-- Gaussian binomial coefficient `[n choose k]_q`. -/
def gaussianBinom (q : ℕ) (m k : ℕ) : ℕ :=
  if k ≤ m then
    (Finset.range k).prod fun i => (q ^ (m - i) - 1) / (q ^ (k - i) - 1)
  else 0

lemma gaussianBinom_zero_right (q m : ℕ) : gaussianBinom q m 0 = 1 := by
  simp only [gaussianBinom, Nat.zero_le, ↓reduceIte, Finset.range_zero, Finset.prod_empty]

lemma gaussianBinom_gt (q m k : ℕ) (h : m < k) : gaussianBinom q m k = 0 := by
  simp only [gaussianBinom, Nat.not_le.mpr h, ↓reduceIte]

private lemma conjAct_smul_eq_of_mem {G : Type*} [Group G] (H : Subgroup G)
    {h : G} (hh : h ∈ H) :
    ConjAct.toConjAct h • H = H := by
  ext x; constructor
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have h_eq : ConjAct.toConjAct h • ((ConjAct.toConjAct h)⁻¹ • x) = x :=
      smul_inv_smul _ x
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at h_eq
    rw [← h_eq]; exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (ConjAct.toConjAct h)⁻¹ • x = h⁻¹ * x * h := by
      change ConjAct.ofConjAct (ConjAct.toConjAct h)⁻¹ * x *
        (ConjAct.ofConjAct (ConjAct.toConjAct h)⁻¹)⁻¹ = _
      simp [ConjAct.ofConjAct_toConjAct, mul_assoc]
    rw [this]; exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

variable (n : ℕ)

private def unipSL (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    SL(n, ℤ) :=
  ⟨unipMat n a hdiv B, unipMat_det n a hdiv B⟩

private lemma upperTriGL_eq_diagMat_mul (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    upperTriGL n a ha hdiv B = diagMat n a * (unipSL n a hdiv B : GL (Fin n) ℚ) := by
  apply Units.ext
  have hunip_val : (↑(mapGL ℚ (unipSL n a hdiv B)) : Matrix _ _ ℚ) =
      (unipSL n a hdiv B).val.map (Int.cast) := by
    simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
  simp only [upperTriGL_val, Units.val_mul, hunip_val, diagMat_val n a ha]
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_mul, zero_mul]
    simp only [unipSL, unipMat, upperTriMat]
    split_ifs <;> push_cast <;> ring
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ i) h

private def invTransposeEquiv : SL(n, ℤ) ≃* SL(n, ℤ) where
  toFun σ := σ.transpose⁻¹
  invFun σ := σ⁻¹.transpose
  left_inv σ := by
    change (σ.transpose⁻¹)⁻¹.transpose = σ
    simp only [inv_inv]; ext i j; simp [coe_transpose]
  right_inv σ := by
    change (σ⁻¹.transpose).transpose⁻¹ = σ
    have : (σ⁻¹.transpose).transpose = σ⁻¹ := by
      ext i j; simp [coe_transpose]
    rw [this, inv_inv]
  map_mul' σ τ := by
    show (σ * τ).transpose⁻¹ = σ.transpose⁻¹ * τ.transpose⁻¹
    have h : (σ * τ).transpose = τ.transpose * σ.transpose :=
      Subtype.ext (by simp only [SpecialLinearGroup.coe_mul,
        SpecialLinearGroup.coe_transpose, Matrix.transpose_mul])
    rw [h, _root_.mul_inv_rev]

private lemma SL_transpose_inv_eq (σ : SL(n, ℤ)) :
    σ.transpose⁻¹ = σ⁻¹.transpose :=
  Subtype.ext (by simp only [SpecialLinearGroup.coe_inv,
    SpecialLinearGroup.coe_transpose, Matrix.adjugate_transpose])

private lemma invTransposeEquiv_invol (σ : SL(n, ℤ)) :
    invTransposeEquiv n (invTransposeEquiv n σ) = σ := by
  rw [show invTransposeEquiv n σ = (invTransposeEquiv n).symm σ from SL_transpose_inv_eq n σ]
  exact (invTransposeEquiv n).apply_symm_apply σ

private lemma relIndex_eq_comap_index (K : Subgroup (GL (Fin n) ℚ)) :
    K.relIndex (SLnZSubgroup n) = (K.comap (mapGL ℚ : SL(n, ℤ) →* GL (Fin n) ℚ)).index := by
  set f := (mapGL ℚ : SL(n, ℤ) →* GL (Fin n) ℚ)
  set H := SLnZSubgroup n
  have h_inj : Function.Injective f := by
    intro x y hxy; ext i j
    have h := congr_arg (fun g => (Units.val g) i j) hxy
    simp only [f, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h; exact_mod_cast h
  have h_H_eq : H = Subgroup.map f ⊤ := by
    simp only [H, SLnZSubgroup]; exact MonoidHom.range_eq_map f
  have h_inf : K ⊓ H = Subgroup.map f (K.comap f) := by
    rw [h_H_eq, ← MonoidHom.range_eq_map f, inf_comm, Subgroup.map_comap_eq]
  calc K.relIndex H
      = (K ⊓ H).relIndex H := (Subgroup.inf_relIndex_right _ _).symm
    _ = (Subgroup.map f (K.comap f)).relIndex (Subgroup.map f ⊤) := by rw [h_inf, h_H_eq]
    _ = (K.comap f).relIndex ⊤ := Subgroup.relIndex_map_map_of_injective _ _ h_inj
    _ = (K.comap f).index := (K.comap f).relIndex_top_right

private lemma transpose_mul_diagMat (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (σ ρ : SL(n, ℤ))
    (h : (σ : GL (Fin n) ℚ) * diagMat n a = diagMat n a * (ρ : GL (Fin n) ℚ)) :
    diagMat n a * (σ.transpose : GL (Fin n) ℚ) =
    (ρ.transpose : GL (Fin n) ℚ) * diagMat n a := by
  apply Units.ext
  simp only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
    diagMat_val n a ha, SpecialLinearGroup.coe_transpose, Matrix.transpose_map]
  have hM := congr_arg Units.val h
  simp only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
    diagMat_val n a ha] at hM
  have h1 := congr_arg Matrix.transpose hM
  simp only [Matrix.transpose_mul, Matrix.diagonal_transpose] at h1
  exact h1

private lemma transpose_mem_conj_inv_of_mem_conj
    (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (σ : SL(n, ℤ))
    (hσ : (σ : GL (Fin n) ℚ) ∈
      ConjAct.toConjAct (diagMat n a) • SLnZSubgroup n) :
    (σ.transpose : GL (Fin n) ℚ) ∈
      ConjAct.toConjAct (diagMat n a)⁻¹ • SLnZSubgroup n := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct] at hσ
  simp only [inv_inv] at hσ
  obtain ⟨ρ, hρ⟩ := MonoidHom.mem_range.mp
    (show _ ∈ SLnZSubgroup n from hσ)
  have h_eq : (σ : GL (Fin n) ℚ) * diagMat n a =
      diagMat n a * (ρ : GL (Fin n) ℚ) := by rw [hρ]; group
  have h_trans := transpose_mul_diagMat n a ha σ ρ h_eq
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  have : diagMat n a * (σ.transpose : GL (Fin n) ℚ) *
      (diagMat n a)⁻¹ = (ρ.transpose : GL (Fin n) ℚ) := by
    have h := congr_arg (· * (diagMat n a)⁻¹) h_trans
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h
    rwa [← mul_assoc] at h
  rw [this]; exact coe_mem_SLnZ n ρ.transpose

private lemma transpose_mem_conj_of_mem_conj_inv
    (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (τ : SL(n, ℤ))
    (hτ : (τ : GL (Fin n) ℚ) ∈
      ConjAct.toConjAct (diagMat n a)⁻¹ • SLnZSubgroup n) :
    (τ.transpose : GL (Fin n) ℚ) ∈
      ConjAct.toConjAct (diagMat n a) • SLnZSubgroup n := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hτ
  obtain ⟨ρ, hρ⟩ := MonoidHom.mem_range.mp
    (show _ ∈ SLnZSubgroup n from hτ)
  have h_eq : (ρ : GL (Fin n) ℚ) * diagMat n a =
      diagMat n a * (τ : GL (Fin n) ℚ) := by rw [hρ]; group
  have h_trans := transpose_mul_diagMat n a ha ρ τ h_eq
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]; simp only [inv_inv]
  have : (diagMat n a)⁻¹ * (τ.transpose : GL (Fin n) ℚ) *
      diagMat n a = (ρ.transpose : GL (Fin n) ℚ) := by
    have := congr_arg ((diagMat n a)⁻¹ * ·) h_trans.symm
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
    exact this
  rw [this]; exact coe_mem_SLnZ n ρ.transpose

private lemma relIndex_conj_inv_eq_conj_diag (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (ConjAct.toConjAct (diagMat n a)⁻¹ • SLnZSubgroup n).relIndex
      (SLnZSubgroup n) =
    (ConjAct.toConjAct (diagMat n a) • SLnZSubgroup n).relIndex
      (SLnZSubgroup n) := by
  rw [relIndex_eq_comap_index, relIndex_eq_comap_index]
  set H := SLnZSubgroup n; set α := diagMat n a
  set f := (mapGL ℚ : SL(n, ℤ) →* GL (Fin n) ℚ)
  set φ := invTransposeEquiv n
  suffices h : (ConjAct.toConjAct α • H).comap f =
      ((ConjAct.toConjAct α⁻¹ • H).comap f).map φ.toMonoidHom by
    rw [h]; simp [Subgroup.index_map_equiv]
  ext σ; simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · intro hσ
    refine ⟨φ σ, ?_, invTransposeEquiv_invol n σ⟩
    change f (φ σ) ∈ ConjAct.toConjAct α⁻¹ • H
    have : f (φ σ) = (f σ.transpose)⁻¹ := by
      change f (σ.transpose⁻¹) = _; exact map_inv f _
    rw [this]
    exact (ConjAct.toConjAct α⁻¹ • H).inv_mem
      (transpose_mem_conj_inv_of_mem_conj n a ha σ hσ)
  · rintro ⟨τ, hτ, rfl⟩
    change f (φ τ) ∈ ConjAct.toConjAct α • H
    have : f (φ τ) = (f τ.transpose)⁻¹ := by
      change f (τ.transpose⁻¹) = _; exact map_inv f _
    rw [this]
    exact (ConjAct.toConjAct α • H).inv_mem
      (transpose_mem_conj_of_mem_conj_inv n a ha τ hτ)

variable [NeZero n]

omit [NeZero n] in
/-- The map sending each upper-triangular representative `B` to the coset of
`(f(unipSL B))⁻¹` in the quotient `H ⧸ (α⁻¹-conjugate of H)` is injective.

This is the core injectivity argument: if two representatives map to the same coset,
then their ratio lies in `H`, contradicting `upperTriMat_distinct_cosets`. -/
private lemma upperTriRep_injective_to_quotient (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (hdiv : DivChain n a)
    (α : GL (Fin n) ℚ) (hα : α = diagMat n a) (H : Subgroup (GL (Fin n) ℚ))
    (hH : H = SLnZSubgroup n) (f : SL(n, ℤ) →* GL (Fin n) ℚ)
    (hf : f = (mapGL ℚ : SL(n, ℤ) →* GL (Fin n) ℚ)) :
    Function.Injective
      (fun B : UpperTriRep n a hdiv =>
        (⟦⟨(f (unipSL n a hdiv B))⁻¹,
          H.inv_mem (show f (unipSL n a hdiv B) ∈ H from
            hH ▸ hf ▸ ⟨unipSL n a hdiv B, rfl⟩)⟩⟧ :
          H ⧸ (ConjAct.toConjAct α⁻¹ • H).subgroupOf H)) := by
  subst hα hH hf
  intro B₁ B₂ heq
  by_contra hne
  have hq := QuotientGroup.eq.mp heq
  rw [Subgroup.mem_subgroupOf] at hq
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] at hq
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hq
  set α := (diagMat n a : GL (Fin n) ℚ)
  set f := (mapGL ℚ : SL(n, ℤ) →* GL (Fin n) ℚ)
  have h1 : upperTriGL n a ha hdiv B₁ = α * f (unipSL n a hdiv B₁) :=
    upperTriGL_eq_diagMat_mul n a ha hdiv B₁
  have h2 : upperTriGL n a ha hdiv B₂ = α * f (unipSL n a hdiv B₂) :=
    upperTriGL_eq_diagMat_mul n a ha hdiv B₂
  have hmem : upperTriGL n a ha hdiv B₁ * (upperTriGL n a ha hdiv B₂)⁻¹ ∈
      SLnZSubgroup n := by
    suffices upperTriGL n a ha hdiv B₁ * (upperTriGL n a ha hdiv B₂)⁻¹ =
        α * (f (unipSL n a hdiv B₁) * (f (unipSL n a hdiv B₂))⁻¹) * α⁻¹ by
      rw [this]; exact hq
    rw [h1, h2]; group
  obtain ⟨γ, hγ⟩ := (MonoidHom.mem_range.mp (show _ ∈ SLnZSubgroup n from hmem))
  have h_eq : upperTriGL n a ha hdiv B₁ = f γ * upperTriGL n a ha hdiv B₂ := by
    have hγ' : f γ = upperTriGL n a ha hdiv B₁ * (upperTriGL n a ha hdiv B₂)⁻¹ := hγ
    rw [hγ', mul_assoc, inv_mul_cancel, mul_one]
  exact upperTriMat_distinct_cosets n a ha hdiv B₁ B₂ hne (f γ) ⟨γ, rfl⟩ h_eq

/-- The cardinality of `UpperTriRep` is at most the relative index
`[H : α⁻¹ H α⁻¹]`, where `α = diagMat a` and `H = SLnZSubgroup n`.

Proved by constructing an injection from `UpperTriRep` into the quotient
`H / (α⁻¹-conjugate ∩ H)` and applying `Fintype.card_le_of_injective`. -/
private lemma upperTriRep_card_le_relIndex (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (hdiv : DivChain n a) (h_rel_ne : (ConjAct.toConjAct (diagMat n a : GL (Fin n) ℚ)⁻¹ •
      (GLPair n).H).relIndex (GLPair n).H ≠ 0) :
    Fintype.card (UpperTriRep n a hdiv) ≤
      (ConjAct.toConjAct (diagMat n a : GL (Fin n) ℚ)⁻¹ •
        (GLPair n).H).relIndex (GLPair n).H := by
  set H := (GLPair n).H
  set α := (diagMat n a : GL (Fin n) ℚ)
  set f := (mapGL ℚ : SL(n, ℤ) →* GL (Fin n) ℚ)
  haveI : Fintype (H ⧸ (ConjAct.toConjAct α⁻¹ • H).subgroupOf H) :=
    Subgroup.fintypeOfIndexNeZero h_rel_ne
  set injMap : UpperTriRep n a hdiv → H ⧸ (ConjAct.toConjAct α⁻¹ • H).subgroupOf H :=
    fun B => ⟦⟨(f (unipSL n a hdiv B))⁻¹,
      H.inv_mem (show f (unipSL n a hdiv B) ∈ H from ⟨unipSL n a hdiv B, rfl⟩)⟩⟧
  have h_inj : Function.Injective injMap :=
    upperTriRep_injective_to_quotient n a ha hdiv α rfl H rfl f rfl
  calc Fintype.card (UpperTriRep n a hdiv)
      ≤ Fintype.card (H ⧸ (ConjAct.toConjAct α⁻¹ • H).subgroupOf H) :=
        Fintype.card_le_of_injective injMap h_inj
    _ = (ConjAct.toConjAct α⁻¹ • H).relIndex H := by
        simp only [Subgroup.relIndex, Subgroup.index, ← Nat.card_eq_fintype_card]

/-- The number of upper-triangular representatives is a lower bound on the degree. -/
theorem upperTriRep_card_le_HeckeCoset_deg (a : Fin n → ℕ) (ha : ∀ i,
  0 < a i) (hdiv : DivChain n a) :
    (Fintype.card (UpperTriRep n a hdiv) : ℤ) ≤
    HeckeCosetDeg (GLPair n) (TDiag a) := by
  set H := (GLPair n).H
  set D := TDiag a
  set δ := (HeckeCoset.rep D : GL (Fin n) ℚ) with hδ_def
  set α := (diagMat n a : GL (Fin n) ℚ) with hα_def
  have h_α_comm : α ∈ Subgroup.Commensurable.commensurator H :=
    (GLPair n).h₁ (diagMat_mem_posDetInt n a ha)
  have h_α_inv_comm : α⁻¹ ∈ Subgroup.Commensurable.commensurator H :=
    (Subgroup.Commensurable.commensurator H).inv_mem h_α_comm
  have h_rel_ne : (ConjAct.toConjAct α⁻¹ • H).relIndex H ≠ 0 :=
    ((Subgroup.Commensurable.commensurator_mem_iff H α⁻¹).mp h_α_inv_comm).1
  have h_card_le : Fintype.card (UpperTriRep n a hdiv) ≤
      (ConjAct.toConjAct α⁻¹ • H).relIndex H :=
    upperTriRep_card_le_relIndex n a ha hdiv h_rel_ne
  have h_S2 := relIndex_conj_inv_eq_conj_diag n a ha
  have h_in_set : δ ∈ HeckeCoset.toSet D := HeckeCoset.rep_mem D
  have h_D_set : HeckeCoset.toSet D = DoubleCoset.doubleCoset α ↑H ↑H := by
    simp only [D, TDiag, HeckeCoset.toSet_mk, hα_def]; congr 1; exact diagMat_delta_val n a ha
  rw [h_D_set, DoubleCoset.mem_doubleCoset] at h_in_set
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hδ_eq⟩ := h_in_set
  have h_smul_σ₁ : ConjAct.toConjAct σ₁ • H = H := conjAct_smul_eq_of_mem H hσ₁
  have h_smul_σ₂ : ConjAct.toConjAct σ₂ • H = H := conjAct_smul_eq_of_mem H hσ₂
  have h_δ_smul : ConjAct.toConjAct δ • H =
      ConjAct.toConjAct σ₁ • (ConjAct.toConjAct α • H) := by
    rw [hδ_eq, map_mul, map_mul, ← smul_smul,
      ← smul_smul, h_smul_σ₂]
  have h_S1 : (ConjAct.toConjAct α • H).relIndex H =
      (ConjAct.toConjAct δ • H).relIndex H := by
    rw [h_δ_smul]
    have := Subgroup.relIndex_pointwise_smul
      (ConjAct.toConjAct σ₁) (ConjAct.toConjAct α • H) H
    rw [h_smul_σ₁] at this; exact this.symm
  have h_def : HeckeCosetDeg (GLPair n) D =
      ↑((ConjAct.toConjAct δ • H).relIndex H) := by
    simp only [HeckeCosetDeg]; rw [← Nat.card_eq_fintype_card]; rfl
  calc (Fintype.card (UpperTriRep n a hdiv) : ℤ)
      ≤ ↑((ConjAct.toConjAct α⁻¹ • H).relIndex H) := by exact_mod_cast h_card_le
    _ = ↑((ConjAct.toConjAct α • H).relIndex H) := by exact_mod_cast h_S2
    _ = ↑((ConjAct.toConjAct δ • H).relIndex H) := by exact_mod_cast h_S1
    _ = HeckeCosetDeg (GLPair n) D := h_def.symm

private lemma a1_eq_a0_mul_pk {p : ℕ} {a : Fin 2 → ℕ} {k : ℕ}
    (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) :
    (a 1 : ℚ) = (a 0 : ℚ) * (↑(p ^ k) : ℚ) := by
  have h1 := Nat.div_mul_cancel h_dvd_a; rw [h_ratio] at h1
  have : a 1 = p ^ k * a 0 := h1.symm
  push_cast [this]; ring

private lemma conj_diagMat_mem_of_Gamma0 (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ)
    (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1)
    (σ : SL(2, ℤ)) (hσ : (↑(p ^ k) : ℤ) ∣ σ.1 1 0) :
    (diagMat 2 a)⁻¹ * (σ : GL (Fin 2) ℚ) * diagMat 2 a ∈ SLnZSubgroup 2 := by
  obtain ⟨c, hc⟩ := hσ
  let τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![σ.1 0 0, ↑(p ^ k) * σ.1 0 1; c, σ.1 1 1]
  have h_det : τ_mat.det = 1 := by
    simp only [τ_mat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hσ_det := σ.prop; simp only [Matrix.det_fin_two] at hσ_det
    rw [hc] at hσ_det; linarith
  let τ : SL(2, ℤ) := ⟨τ_mat, h_det⟩
  rw [MonoidHom.mem_range]
  refine ⟨τ, ?_⟩
  have ha1 := a1_eq_a0_mul_pk h_ratio h_dvd_a
  have hcQ : (σ.1 1 0 : ℚ) = (↑(p ^ k) : ℚ) * (c : ℚ) := by exact_mod_cast hc
  push_cast at ha1 hcQ
  suffices h : diagMat 2 a * (τ : GL (Fin 2) ℚ) = (σ : GL (Fin 2) ℚ) * diagMat 2 a by
    have h' := congr_arg ((diagMat 2 a)⁻¹ * ·) h
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h'; exact h'
  apply Units.ext
  have hτ_val : (↑(mapGL ℚ τ) : Matrix _ _ ℚ) = τ.val.map (Int.cast) := by
    simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
  have hσ_val : (↑(mapGL ℚ σ) : Matrix _ _ ℚ) = σ.val.map (Int.cast) := by
    simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
  simp only [Units.val_mul, hτ_val, hσ_val]
  ext i j
  simp only [diagMat_val 2 a ha, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [τ, τ_mat, Matrix.of_apply, Matrix.cons_val', Fin.isValue] <;>
    push_cast <;> (try rw [hcQ]) <;> (try rw [ha1]) <;> ring

private lemma Gamma0_of_conj_diagMat_mem (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ)
    (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) (σ : SL(2, ℤ))
    (hmem : (diagMat 2 a)⁻¹ * (σ : GL (Fin 2) ℚ) * diagMat 2 a ∈ SLnZSubgroup 2) :
    (↑(p ^ k) : ℤ) ∣ σ.1 1 0 := by
  rw [MonoidHom.mem_range] at hmem
  obtain ⟨τ, hτ⟩ := hmem
  have ha1 := a1_eq_a0_mul_pk h_ratio h_dvd_a
  have ha0_ne : (a 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha 0).ne'
  have h_mul : diagMat 2 a * (τ : GL (Fin 2) ℚ) = (σ : GL (Fin 2) ℚ) * diagMat 2 a := by
    have := congr_arg (diagMat 2 a * ·) hτ
    simp only [← mul_assoc, mul_inv_cancel, one_mul] at this; exact this
  have h_entry : (a 1 : ℚ) * (τ.1 1 0 : ℚ) = (σ.1 1 0 : ℚ) * (a 0 : ℚ) := by
    have h10 : ∀ i j, (↑(diagMat 2 a * (τ : GL (Fin 2) ℚ)) :
        Matrix (Fin 2) (Fin 2) ℚ) i j =
      (↑((σ : GL (Fin 2) ℚ) * diagMat 2 a) : Matrix (Fin 2) (Fin 2) ℚ) i j := by
      intro i j; rw [Units.ext_iff.mp h_mul]
    have := h10 1 0
    simp only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
      diagMat_val 2 a ha, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.map_apply] at this
    exact this
  have h_σ₁₀ : (σ.1 1 0 : ℚ) = ↑(p ^ k) * (τ.1 1 0 : ℚ) := by
    rw [ha1] at h_entry; field_simp at h_entry ⊢; linarith
  exact ⟨τ.1 1 0, by exact_mod_cast h_σ₁₀⟩

private lemma conjDiag_relIndex_eq_Gamma0_index
    (p : ℕ) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ)
    (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) :
    (ConjAct.toConjAct (diagMat 2 a) • SLnZSubgroup 2).relIndex (SLnZSubgroup 2) =
    (Gamma0 (p ^ k)).index := by
  set H := SLnZSubgroup 2
  set α := diagMat 2 a
  set f := (mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ)
  have h_inj : Function.Injective f := by
    intro σ₁ σ₂ h
    have := Units.ext_iff.mp h
    simp only [f, mapGL_coe_matrix, map_apply_coe,
      RingHom.mapMatrix_apply] at this
    ext i j; exact Int.cast_injective (congr_fun₂ this i j)
  have h_H_eq : H = Subgroup.map f ⊤ := by
    simp only [H, f, MonoidHom.range_eq_map]
  have h_gamma0_iff : ∀ σ : SL(2, ℤ),
      σ ∈ Gamma0 (p ^ k) ↔ α⁻¹ * f σ * α ∈ H := by
    intro σ
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨conj_diagMat_mem_of_Gamma0 a ha k h_ratio h_dvd_a σ,
           Gamma0_of_conj_diagMat_mem a ha k h_ratio h_dvd_a σ⟩
  have h_inf_eq : (ConjAct.toConjAct α • H) ⊓ H = Subgroup.map f (Gamma0 (p ^ k)) := by
    ext g; simp only [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨h_smul, h_mem⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_smul
      obtain ⟨σ, rfl⟩ := h_mem
      exact ⟨σ, (h_gamma0_iff σ).mpr h_smul, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨?_, ⟨σ, rfl⟩⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      exact (h_gamma0_iff σ).mp hσ
  calc (ConjAct.toConjAct α • H).relIndex H
      = ((ConjAct.toConjAct α • H) ⊓ H).relIndex H :=
          (Subgroup.inf_relIndex_right _ _).symm
    _ = (Subgroup.map f (Gamma0 (p ^ k))).relIndex (Subgroup.map f ⊤) := by
          rw [h_inf_eq, h_H_eq]
    _ = (Gamma0 (p ^ k)).relIndex ⊤ :=
          Subgroup.relIndex_map_map_of_injective _ _ h_inj
    _ = (Gamma0 (p ^ k)).index := (Gamma0 (p ^ k)).relIndex_top_right

/-- For `n = 2` and prime `p`: `deg(T(p^i, p^(i+k))) = p^(k-1) * (p + 1)` for `k >= 1`. -/
theorem HeckeCoset_deg_T_diag_two_prime (p : ℕ) (hp : Nat.Prime p)
    (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (hdiv : DivChain 2 a) (k : ℕ) (hk : 0 < k)
    (h_ratio : a 1 / a 0 = p ^ k) :
    HeckeCosetDeg (GLPair 2) (TDiag a) =
    ↑(p ^ (k - 1) * (p + 1)) := by
  set D := TDiag a
  set δ := (HeckeCoset.rep D : GL (Fin 2) ℚ) with hδ_def
  set α := (diagMat 2 a : GL (Fin 2) ℚ) with hα_def
  set H := (GLPair 2).H
  have h_dvd_a : a 0 ∣ a 1 := hdiv 0 (by omega)
  have h_in_set : δ ∈ HeckeCoset.toSet D := HeckeCoset.rep_mem D
  have h_D_set : HeckeCoset.toSet D = DoubleCoset.doubleCoset α ↑H ↑H := by
    simp only [D, TDiag, HeckeCoset.toSet_mk, hα_def]; congr 1; exact diagMat_delta_val 2 a ha
  rw [h_D_set, DoubleCoset.mem_doubleCoset] at h_in_set
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hδ_eq⟩ := h_in_set
  have h_smul_σ₁ : ConjAct.toConjAct σ₁ • H = H := conjAct_smul_eq_of_mem H hσ₁
  have h_δ_smul : ConjAct.toConjAct δ • H =
      ConjAct.toConjAct σ₁ • (ConjAct.toConjAct α • H) := by
    rw [hδ_eq, map_mul, map_mul, ← smul_smul,
      ← smul_smul, conjAct_smul_eq_of_mem H hσ₂]
  have h_S1 : (ConjAct.toConjAct α • H).relIndex H =
      (ConjAct.toConjAct δ • H).relIndex H := by
    rw [h_δ_smul]
    have := Subgroup.relIndex_pointwise_smul
      (ConjAct.toConjAct σ₁) (ConjAct.toConjAct α • H) H
    rw [h_smul_σ₁] at this; exact this.symm
  have h_def : HeckeCosetDeg (GLPair 2) D =
      ↑((ConjAct.toConjAct δ • H).relIndex H) := by
    simp only [HeckeCosetDeg]; rw [← Nat.card_eq_fintype_card]; rfl
  have h_Gamma0 : (ConjAct.toConjAct α • H).relIndex H =
      (Gamma0 (p ^ k)).index := conjDiag_relIndex_eq_Gamma0_index p a ha k h_ratio h_dvd_a
  rw [h_def, show (ConjAct.toConjAct δ • H).relIndex H =
      (ConjAct.toConjAct α • H).relIndex H from h_S1.symm,
    h_Gamma0, Gamma0_prime_power_index p hp k hk]

private lemma diagMat_comm_of_const (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (h_const : ∀ i, a i = a 0) (g : GL (Fin n) ℚ) :
    diagMat n a * g = g * diagMat n a := by
  apply Units.ext
  simp only [Units.val_mul, diagMat_val n a ha]
  have h_diag : Matrix.diagonal (fun i => (a i : ℚ)) =
      (a 0 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs with h
    · subst h; simp [h_const]
    · simp
  rw [h_diag, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- For `n = 2`, scalar case: `deg(T(c, c)) = 1`. -/
theorem HeckeCoset_deg_T_diag_two_scalar (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (_hdiv : DivChain 2 a) (h_eq : a 0 = a 1) :
    HeckeCosetDeg (GLPair 2) (TDiag a) = 1 := by
  have h_const : ∀ i, a i = a 0 := fun i => by fin_cases i <;> simp [h_eq]
  set D := TDiag a
  set δ := HeckeCoset.rep D
  set H := (GLPair 2).H
  suffices hsmul : ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H = H by
    have h_def : HeckeCosetDeg (GLPair 2) D =
        ↑((ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H).relIndex H) := by
      simp only [HeckeCosetDeg, Subgroup.relIndex, Subgroup.index,
        ← Nat.card_eq_fintype_card]; rfl
    rw [h_def, hsmul, Subgroup.relIndex_self]; simp
  have hδ_mem : (δ : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (↑(diagMatDelta 2 a)) H H := by
    have h1 : HeckeCoset.toSet D =
        DoubleCoset.doubleCoset (↑(diagMatDelta 2 a)) H H := by
      simp only [D, H, TDiag, HeckeCoset.toSet_mk]
    rw [← h1]; exact HeckeCoset.rep_mem D
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem; obtain ⟨h₁, hh₁, h₂, hh₂, hδ_eq⟩ := hδ_mem
  have h_comm : diagMat 2 a * h₂ = h₂ * diagMat 2 a :=
    diagMat_comm_of_const 2 a ha h_const h₂
  have hδ_simp : (δ : GL (Fin 2) ℚ) = (h₁ * h₂) * diagMat 2 a := by
    rw [hδ_eq, show (↑(diagMatDelta 2 a) : GL (Fin 2) ℚ) =
        diagMat 2 a from diagMat_delta_val 2 a ha, mul_assoc]
    rw [h_comm, ← mul_assoc]
  have h_diag_conj : ∀ (g : GL (Fin 2) ℚ),
      (diagMat 2 a)⁻¹ * g * diagMat 2 a = g := by
    intro g; rw [mul_assoc, ← diagMat_comm_of_const 2 a ha h_const g, ← mul_assoc,
      inv_mul_cancel, one_mul]
  rw [hδ_simp, map_mul, ← smul_smul]
  have h_smul_diag : ConjAct.toConjAct (diagMat 2 a) • H = H := by
    ext x; simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    constructor
    · intro hx; rwa [h_diag_conj] at hx
    · intro hx; rwa [h_diag_conj]
  rw [h_smul_diag]
  exact conjAct_smul_eq_of_mem H (H.mul_mem hh₁ hh₂)

end HeckeRing.GLn
