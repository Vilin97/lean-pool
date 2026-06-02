/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.GLn.DiagonalCosets
import LeanPool.LeanModularForms.HeckeRIngs.GLn.CosetDecomposition
import LeanPool.LeanModularForms.HeckeRIngs.GLn.Degree
import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring
import LeanPool.LeanModularForms.HeckeRIngs.GLn.SLnTransvection

/-!
# Coprime Product and Scalar Multiplication in the Hecke Ring

Shimura Propositions 3.16 and 3.17: when determinants are coprime,
the product of double cosets is a single double coset with multiplicity 1.
Scalar double cosets T(c,...,c) act by scaling.

## Main results

* `T_diag_scalar_mul` — `T(c,...,c) · T(b₁,...,bₙ) = T(cb₁,...,cbₙ)`
* `T_diag_mul_coprime` — `T(a) · T(b) = T(a·b)` when `(∏aᵢ, ∏bᵢ) = 1`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.2
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

section DiagMul

/-- Pointwise product of positive sequences is positive. -/
lemma pi_mul_pos (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∀ i, 0 < (a * b) i := fun i => Nat.mul_pos (ha i) (hb i)

/-- Pointwise product of two divisibility chains is a divisibility chain. -/
lemma DivChain_mul (a b : Fin n → ℕ) (ha : DivChain n a) (hb : DivChain n b) :
    DivChain n (a * b) := fun i hi => by
  simp only [Pi.mul_apply]; exact Nat.mul_dvd_mul (ha i hi) (hb i hi)

/-- Product of diagonal `GL_n(ℚ)` elements is diagonal with pointwise product. -/
@[simp] lemma diagMat_mul (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    diagMat n a * diagMat n b = diagMat n (a * b) := by
  apply Units.ext
  simp only [Units.val_mul, diagMat_val _ _ ha, diagMat_val _ _ hb,
    diagMat_val _ _ (pi_mul_pos n a b ha hb), Pi.mul_apply]
  ext i j; simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; rw [Finset.sum_eq_single i]
    · simp
    · intro b' _ hb'; simp [hb']
    · intro h; exact absurd (Finset.mem_univ i) h
  · simp only [hij, ↓reduceIte]; apply Finset.sum_eq_zero; intro k _
    by_cases hik : i = k
    · subst hik; simp [hij]
    · simp [hik]

variable [NeZero n]

lemma T_diag_eq_T_mk_mul (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (_hab : DivChain n (a * b)) :
    TDiag (a * b) = (⟦⟨diagMat n a * diagMat n b,
      (diagMat_mul n a b ha hb).symm ▸ diagMat_mem_posDetInt n (a * b)
        (pi_mul_pos n a b ha hb)⟩⟧ : HeckeCoset (GLPair n)) := by
  simp only [TDiag]; rw [HeckeCoset.eq_iff]
  simp only [diagMatDelta, dif_pos (pi_mul_pos n a b ha hb)]
  congr 1; exact (diagMat_mul n a b ha hb).symm

end DiagMul

variable [NeZero n]

private lemma doubleCoset_eq_of_mem' (g δ : GL (Fin n) ℚ)
    (h : g ∈ DoubleCoset.doubleCoset δ (GLPair n).H (GLPair n).H) :
    DoubleCoset.doubleCoset g (GLPair n).H (GLPair n).H =
      DoubleCoset.doubleCoset δ (GLPair n).H (GLPair n).H := by
  rw [DoubleCoset.mem_doubleCoset] at h; obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := h; rw [heq]
  exact (DoubleCoset.doubleCoset_mul_right_eq_self (GLPair n) ⟨h₂, hh₂⟩ (h₁ * δ)).trans
    (doset_mul_left_eq_self (GLPair n) ⟨h₁, hh₁⟩ δ)

section Scalar

omit [NeZero n] in
lemma diagMat_scalar_eq (c : ℕ) (hc : 0 < c) :
    (↑(diagMat n (fun _ => c)) : Matrix (Fin n) (Fin n) ℚ) = (c : ℚ) • 1 := by
  simp only [diagMat_val _ _ (fun _ => hc), ← Matrix.smul_one_eq_diagonal]

omit [NeZero n] in
lemma diagMat_scalar_comm (c : ℕ) (hc : 0 < c) (g : GL (Fin n) ℚ) :
    diagMat n (fun _ => c) * g = g * diagMat n (fun _ => c) := by
  apply Units.ext
  simp only [Units.val_mul, diagMat_scalar_eq n c hc, smul_one_mul, mul_smul_one]

omit [NeZero n] in
lemma diagMat_scalar_conj_eq (c : ℕ) (hc : 0 < c) (x : GL (Fin n) ℚ) :
    (diagMat n (fun _ => c))⁻¹ * x * diagMat n (fun _ => c) = x := by
  rw [mul_assoc, ← diagMat_scalar_comm n c hc x, ← mul_assoc, inv_mul_cancel, one_mul]

lemma conjAct_scalar_smul_eq (c : ℕ) (hc : 0 < c) :
    ConjAct.toConjAct (diagMat n (fun _ => c)) • (GLPair n).H = (GLPair n).H := by
  ext x; constructor
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hx
    rwa [diagMat_scalar_conj_eq n c hc] at hx
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    rwa [diagMat_scalar_conj_eq n c hc]

private lemma conjAct_mem_smul_eq (h : GL (Fin n) ℚ) (hh : h ∈ (GLPair n).H) :
    ConjAct.toConjAct h • (GLPair n).H = (GLPair n).H := by
  ext x; simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · intro hx; have : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    rw [this]
    exact (GLPair n).H.mul_mem ((GLPair n).H.mul_mem hh hx) ((GLPair n).H.inv_mem hh)
  · intro hx
    exact (GLPair n).H.mul_mem ((GLPair n).H.mul_mem ((GLPair n).H.inv_mem hh) hx) hh

/-- The degree of a scalar double coset `T(c,...,c)` is `1`. -/
lemma HeckeCoset_deg_scalar (c : ℕ) (hc : 0 < c) :
    HeckeCosetDeg (GLPair n) (TDiag (fun _ : Fin n => c)) = 1 := by
  set D := TDiag (fun _ : Fin n => c)
  set δ := HeckeCoset.rep D
  set H := (GLPair n).H
  suffices hsmul : ConjAct.toConjAct (δ : GL (Fin n) ℚ) • H = H by
    have h_def : HeckeCosetDeg (GLPair n) D =
        ↑((ConjAct.toConjAct (δ : GL (Fin n) ℚ) • H).relIndex H) := by
      simp only [HeckeCosetDeg, Subgroup.relIndex, Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
    rw [h_def, hsmul, Subgroup.relIndex_self]; simp
  have hδ_mem : (δ : GL (Fin n) ℚ) ∈
      DoubleCoset.doubleCoset (↑(diagMatDelta n (fun _ => c))) H H := by
    have h1 : HeckeCoset.toSet D =
        DoubleCoset.doubleCoset (↑(diagMatDelta n (fun _ => c))) H H := by
      simp only [D, H, TDiag, HeckeCoset.toSet_mk]
    rw [← h1]; exact HeckeCoset.rep_mem D
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem; obtain ⟨h₁, hh₁, h₂, hh₂, hδ_eq⟩ := hδ_mem
  have hδ_simp : (δ : GL (Fin n) ℚ) = (h₁ * h₂) * diagMat n (fun _ => c) := by
    rw [hδ_eq, show (↑(diagMatDelta n (fun _ => c)) : GL (Fin n) ℚ) =
        diagMat n (fun _ => c) from diagMat_delta_val n (fun _ => c) (fun _ => hc)]
    rw [mul_assoc, diagMat_scalar_comm n c hc h₂, ← mul_assoc]
  rw [hδ_simp, map_mul, ← smul_smul, conjAct_scalar_smul_eq n c hc]
  exact conjAct_mem_smul_eq n (h₁ * h₂) (H.mul_mem hh₁ hh₂)

private lemma mulMap_scalar_eq (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ) (hb_pos : ∀ i, 0 < b i)
    (_hb : DivChain n b) (_hcb : DivChain n ((fun _ => c) * b))
    (p : decompQuot (GLPair n) (HeckeCoset.rep (TDiag (fun _ : Fin n => c))) ×
      decompQuot (GLPair n) (HeckeCoset.rep (TDiag b))) :
    mulMap (GLPair n) (HeckeCoset.rep (TDiag (fun _ : Fin n => c)))
      (HeckeCoset.rep (TDiag b)) p =
      TDiag ((fun _ => c) * b) := by
  have hcb_pos := pi_mul_pos n (fun _ => c) b (fun _ => hc) hb_pos
  obtain ⟨L_c, hL_c, R_c, hR_c, hα_eq⟩ := T_diag_rep_decompose (fun _ : Fin n => c) (fun _ => hc)
  obtain ⟨L_b, hL_b, R_b, hR_b, hβ_eq⟩ := T_diag_rep_decompose b hb_pos
  set α := (HeckeCoset.rep (TDiag (fun _ : Fin n => c)) : GL (Fin n) ℚ)
  set β := (HeckeCoset.rep (TDiag b) : GL (Fin n) ℚ)
  set H := (GLPair n).H
  have h_prod_mem : ↑p.1.out * α * (↑p.2.out * β) ∈
      DoubleCoset.doubleCoset (diagMat n ((fun _ => c) * b) : GL (Fin n) ℚ)
        (GLPair n).H (GLPair n).H := by
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨(p.1.out : GL (Fin n) ℚ) * L_c * R_c * p.2.out * L_b,
      H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (SetLike.coe_mem p.1.out) hL_c) hR_c)
        (SetLike.coe_mem p.2.out)) hL_b, R_b, hR_b, ?_⟩
    rw [show α = L_c * diagMat n (fun _ => c) * R_c from hα_eq,
        show β = L_b * diagMat n b * R_b from hβ_eq]
    calc ↑p.1.out * (L_c * diagMat n (fun _ => c) * R_c) *
          (↑p.2.out * (L_b * diagMat n b * R_b))
        = ↑p.1.out * L_c * (diagMat n (fun _ => c) * (R_c * ↑p.2.out * L_b)) *
            (diagMat n b * R_b) := by group
      _ = ↑p.1.out * L_c * ((R_c * ↑p.2.out * L_b) * diagMat n (fun _ => c)) *
            (diagMat n b * R_b) := by rw [diagMat_scalar_comm n c hc _]
      _ = ↑p.1.out * L_c * R_c * ↑p.2.out * L_b *
            (diagMat n (fun _ => c) * diagMat n b) * R_b := by group
      _ = ↑p.1.out * L_c * R_c * ↑p.2.out * L_b *
            diagMat n ((fun _ => c) * b) * R_b := by
          rw [diagMat_mul n _ b (fun _ => hc) hb_pos]
  apply HeckeCoset_ext_toSet (P := GLPair n)
  rw [mulMap, HeckeCoset.toSet_mk]
  simp only [TDiag, HeckeCoset.toSet_mk,
    diagMat_delta_val n ((fun _ => c) * b) hcb_pos]
  exact doubleCoset_eq_of_mem' n _ _ h_prod_mem

private lemma heckeMultiplicity_scalar_eq_one (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain n b) (hab : DivChain n ((fun _ => c) * b)) :
    HeckeRing.heckeMultiplicity (GLPair n) (HeckeCoset.rep (TDiag (fun _ : Fin n => c)))
      (HeckeCoset.rep (TDiag b))
      (HeckeCoset.rep (TDiag ((fun _ => c) * b))) = 1 := by
  set D_c := TDiag (fun _ : Fin n => c); set D_b := TDiag b
  set D_cb := TDiag ((fun _ : Fin n => c) * b)
  have h_card : Fintype.card (decompQuot (GLPair n) (HeckeCoset.rep D_c)) = 1 := by
    have := HeckeCoset_deg_scalar n c hc
    simp only [HeckeRing.HeckeCosetDeg] at this; exact_mod_cast this
  haveI : Subsingleton (decompQuot (GLPair n) (HeckeCoset.rep D_c)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
  have h_le : HeckeRing.heckeMultiplicity (GLPair n) (HeckeCoset.rep D_c) (HeckeCoset.rep D_b)
      (HeckeCoset.rep D_cb) ≤ 1 := by
    classical
    simp only [HeckeRing.heckeMultiplicity]; norm_cast; rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_one_iff_subsingleton.mpr; constructor
    intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
    have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
    simp only [Set.mem_setOf_eq] at h₁ h₂
    have hj := HeckeRing.decompQuot_snd_eq_of_fst_eq (GLPair n) (HeckeCoset.rep D_c)
      (HeckeCoset.rep D_b) (HeckeCoset.rep D_cb) i₁ j₁ j₂ h₁ h₂
    subst hj; rfl
  have h_pos : 0 < HeckeRing.heckeMultiplicity (GLPair n) (HeckeCoset.rep D_c) (HeckeCoset.rep D_b)
      (HeckeCoset.rep D_cb) := by
    have h_mem :
        D_cb ∈ HeckeRing.mulSupport (GLPair n) (HeckeCoset.rep D_c) (HeckeCoset.rep D_b) := by
      simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
        true_and, Prod.exists]
      have ⟨i₀⟩ : Nonempty (decompQuot (GLPair n) (HeckeCoset.rep D_c)) :=
        Fintype.card_pos_iff.mp (h_card ▸ Nat.one_pos)
      have ⟨j₀⟩ : Nonempty (decompQuot (GLPair n) (HeckeCoset.rep D_b)) :=
        Fintype.card_pos_iff.mp (by
          have := HeckeRing.HeckeCoset_deg_pos (GLPair n) D_b
          simp only [HeckeRing.HeckeCosetDeg] at this; omega)
      exact ⟨i₀, j₀, mulMap_scalar_eq n c hc b hb_pos hb hab (i₀, j₀)⟩
    exact HeckeRing.heckeMultiplicity_pos_of_mem (GLPair n) _ _ _ h_mem
  omega

private lemma heckeMultiplicity_scalar_eq_zero (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain n b) (hab : DivChain n ((fun _ => c) * b))
    (A : HeckeCoset (GLPair n)) (hA : A ≠ TDiag ((fun _ : Fin n => c) * b)) :
    HeckeRing.heckeMultiplicity (GLPair n) (HeckeCoset.rep (TDiag (fun _ : Fin n => c)))
      (HeckeCoset.rep (TDiag b)) (HeckeCoset.rep A) = 0 := by
  apply HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport; intro h_mem
  simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and] at h_mem
  obtain ⟨⟨i, j⟩, heq⟩ := h_mem
  exact hA (heq.symm.trans (mulMap_scalar_eq n c hc b hb_pos hb hab (i, j)))

/-- Scalar multiplication in the Hecke ring (Shimura Proposition 3.17). -/
theorem T_diag_scalar_mul (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain n b) :
    TElem (fun _ : Fin n => c) * TElem b = TElem ((fun _ => c) * b) := by
  change HeckeRing.TSingle (GLPair n) ℤ (TDiag (fun _ : Fin n => c)) 1 *
      HeckeRing.TSingle (GLPair n) ℤ (TDiag b) 1 =
    HeckeRing.TSingle (GLPair n) ℤ (TDiag ((fun _ : Fin n => c) * b)) 1
  exact HeckeRing.T_single_one_mul_eq_single (GLPair n) (TDiag (fun _ : Fin n => c)) (TDiag b)
    (TDiag ((fun _ : Fin n => c) * b))
    (heckeMultiplicity_scalar_eq_one n c hc b hb_pos hb
      (DivChain_mul n _ _ (divChain_const n c) hb))
    (fun A hA => heckeMultiplicity_scalar_eq_zero n c hc b hb_pos hb
      (DivChain_mul n _ _ (divChain_const n c) hb) A hA)



end Scalar

section Coprime

private def congMod (d : ℕ) (σ : SpecialLinearGroup (Fin n) ℤ) : Prop :=
  ∀ i j, (d : ℤ) ∣ (σ.1 i j - if i = j then 1 else 0)

private def slTransvec (i j : Fin n) (hij : i ≠ j) (c : ℤ) :
    SpecialLinearGroup (Fin n) ℤ :=
  ⟨(Matrix.TransvectionStruct.mk i j hij c).toMatrix,
   (Matrix.TransvectionStruct.mk i j hij c).det⟩

omit [NeZero n] in
private lemma slTransvec_mul (i j : Fin n) (hij : i ≠ j) (a b : ℤ) :
    slTransvec n i j hij a * slTransvec n i j hij b =
      slTransvec n i j hij (a + b) := by
  apply Subtype.ext
  change (Matrix.TransvectionStruct.mk i j hij a).toMatrix *
      (Matrix.TransvectionStruct.mk i j hij b).toMatrix =
    (Matrix.TransvectionStruct.mk i j hij (a + b)).toMatrix
  simp only [Matrix.TransvectionStruct.toMatrix]
  exact Matrix.transvection_mul_transvection_same (n := Fin n) (i := i) (j := j) hij a b

omit [NeZero n] in
private lemma slTransvec_congMod (d : ℕ) (i j : Fin n) (hij : i ≠ j) (c : ℤ)
    (hdc : (d : ℤ) ∣ c) : congMod n d (slTransvec n i j hij c) := by
  intro k l
  simp only [slTransvec, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.single, Matrix.of_apply, add_sub_cancel_left]
  split_ifs with h
  · exact hdc
  · exact dvd_zero _

omit [NeZero n] in
private lemma slTransvec_CRT (d d' : ℕ) (hcop : Nat.Coprime d d')
    (i j : Fin n) (hij : i ≠ j) (c : ℤ) :
    ∃ τ₁ τ₂ : SpecialLinearGroup (Fin n) ℤ,
      slTransvec n i j hij c = τ₁ * τ₂ ∧ congMod n d τ₁ ∧ congMod n d' τ₂ := by
  have hbez : ↑(Nat.gcd d d') = (d : ℤ) * Nat.gcdA d d' + ↑d' * Nat.gcdB d d' :=
    Nat.gcd_eq_gcd_ab d d'
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  refine ⟨slTransvec n i j hij (c * d * Nat.gcdA d d'),
    slTransvec n i j hij (c * d' * Nat.gcdB d d'), ?_, ?_, ?_⟩
  · rw [slTransvec_mul]; congr 1; linear_combination c * hbez
  · exact slTransvec_congMod n d i j hij _ ⟨c * Nat.gcdA d d', by ring⟩
  · exact slTransvec_congMod n d' i j hij _ ⟨c * Nat.gcdB d d', by ring⟩

omit [NeZero n] in
private lemma congMod_one (d : ℕ) : congMod n d 1 :=
  fun i j => by simp [SpecialLinearGroup.coe_one, Matrix.one_apply]

omit [NeZero n] in
private lemma congMod_mul (d : ℕ) (a b : SpecialLinearGroup (Fin n) ℤ)
    (ha : congMod n d a) (hb : congMod n d b) : congMod n d (a * b) := by
  intro i j; simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  have h1 : ∑ k : Fin n, (if i = k then (1 : ℤ) else 0) * b.1 k j = b.1 i j := by
    simp [Finset.mem_univ]
  have h2 : ∑ k, (a.1 i k - if i = k then 1 else 0) * b.1 k j =
      (∑ k, a.1 i k * b.1 k j) - b.1 i j := by
    rw [← h1, ← Finset.sum_sub_distrib]; congr 1; ext k; ring
  rw [show (∑ k, a.1 i k * b.1 k j) - (if i = j then 1 else 0) =
      (∑ k, (a.1 i k - if i = k then 1 else 0) * b.1 k j) +
      (b.1 i j - if i = j then 1 else 0) from by linarith [h2]]
  exact dvd_add (Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_left (ha i k) _)) (hb i j)

omit [NeZero n] in
private lemma congMod_inv (d : ℕ) (a : SpecialLinearGroup (Fin n) ℤ)
    (ha : congMod n d a) : congMod n d a⁻¹ := by
  intro i j
  have h_mul_inv : a.1 * (a⁻¹).1 = 1 := by
    rw [← SpecialLinearGroup.coe_mul, ← SpecialLinearGroup.coe_one]
    exact congr_arg Subtype.val (mul_inv_cancel a)
  have h_entry : ∑ k : Fin n, a.1 i k * (a⁻¹).1 k j = if i = j then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun (congr_fun h_mul_inv i) j
  have h_div : (d : ℤ) ∣
      ∑ k : Fin n, (a.1 i k - if i = k then 1 else 0) * (a⁻¹).1 k j :=
    Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_left (ha i k) _)
  have h_sum_eq : ∑ k : Fin n, (a.1 i k - if i = k then 1 else 0) * (a⁻¹).1 k j =
      (if i = j then 1 else 0) - (a⁻¹).1 i j := by
    trans (∑ k, a.1 i k * (a⁻¹).1 k j) -
        (∑ k, (if i = k then (1 : ℤ) else 0) * (a⁻¹).1 k j)
    · rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
    · rw [h_entry]; simp [Finset.mem_univ]
  rw [show (a⁻¹).1 i j - (if i = j then 1 else 0) =
      -(∑ k : Fin n, (a.1 i k - if i = k then 1 else 0) * (a⁻¹).1 k j) from by
    linarith [h_sum_eq]]
  exact dvd_neg.mpr h_div

omit [NeZero n] in
private lemma congMod_conj (d : ℕ) (σ τ : SpecialLinearGroup (Fin n) ℤ)
    (hτ : congMod n d τ) : congMod n d (σ⁻¹ * τ * σ) := by
  intro i j
  simp only [show σ⁻¹ * τ * σ = σ⁻¹ * (τ * σ) from by group,
    SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  have h_inv : ∀ i' j', ∑ k : Fin n, (σ⁻¹).1 i' k * σ.1 k j' =
      if i' = j' then 1 else 0 := by
    intro i' j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using
      congr_fun (congr_fun (show (σ⁻¹).1 * σ.1 = 1 from by
        rw [← SpecialLinearGroup.coe_mul, ← SpecialLinearGroup.coe_one]
        exact congr_arg Subtype.val (inv_mul_cancel σ)) i') j'
  have h_inner : ∀ k, ∑ l : Fin n, τ.1 k l * σ.1 l j =
      (∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j) + σ.1 k j := by
    intro k
    have h1 : ∑ l : Fin n, (if k = l then (1 : ℤ) else 0) * σ.1 l j = σ.1 k j := by
      simp [Finset.mem_univ]
    have h2 : ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j =
        (∑ l, τ.1 k l * σ.1 l j) - σ.1 k j := by
      rw [← h1, ← Finset.sum_sub_distrib]; congr 1; ext l; ring
    linarith [h2]
  rw [show (∑ k, (σ⁻¹).1 i k * ∑ l, τ.1 k l * σ.1 l j) - (if i = j then 1 else 0) =
      ∑ k, (σ⁻¹).1 i k * ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j from by
    have h3 : (∑ k, (σ⁻¹).1 i k * ∑ l, τ.1 k l * σ.1 l j) =
        (∑ k, (σ⁻¹).1 i k * ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j) +
        (∑ k, (σ⁻¹).1 i k * σ.1 k j) := by
      rw [← Finset.sum_add_distrib]; congr 1; ext k; rw [h_inner k]; ring
    rw [h3, h_inv]; ring]
  exact Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_right
    (Finset.dvd_sum (fun l _ => dvd_mul_of_dvd_left (hτ k l) _)) _)

omit [NeZero n] in
private lemma CRTProd_mul' (d d' : ℕ) (a b : SpecialLinearGroup (Fin n) ℤ)
    (ha : ∃ p q, a = p * q ∧ congMod n d p ∧ congMod n d' q)
    (hb : ∃ p q, b = p * q ∧ congMod n d p ∧ congMod n d' q) :
    ∃ p q, a * b = p * q ∧ congMod n d p ∧ congMod n d' q := by
  obtain ⟨p₁, q₁, rfl, hp₁, hq₁⟩ := ha; obtain ⟨p₂, q₂, rfl, hp₂, hq₂⟩ := hb
  refine ⟨p₁ * (q₁ * p₂ * q₁⁻¹), q₁ * q₂, by group, ?_, congMod_mul n d' _ _ hq₁ hq₂⟩
  have h := congMod_conj n d q₁⁻¹ p₂ hp₂; rw [inv_inv] at h
  exact congMod_mul n d _ _ hp₁ h

omit [NeZero n] in
private lemma slTransvec_in_CRTProd (d d' : ℕ) (hcop : Nat.Coprime d d')
    (i j : Fin n) (hij : i ≠ j) (c : ℤ) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      slTransvec n i j hij c = p * q ∧ congMod n d p ∧ congMod n d' q :=
  slTransvec_CRT n d d' hcop i j hij c

omit [NeZero n] in
private lemma one_in_CRTProd (d d' : ℕ) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      (1 : SpecialLinearGroup (Fin n) ℤ) = p * q ∧ congMod n d p ∧ congMod n d' q :=
  ⟨1, 1, (one_mul 1).symm, congMod_one n d, congMod_one n d'⟩

omit [NeZero n] in
private lemma slTransvecG_eq_slTransvec (i j : Fin n) (hij : i ≠ j) (c : ℤ) :
    slTransvecG i j hij c = slTransvec n i j hij c :=
  Subtype.ext rfl

omit [NeZero n] in
private lemma isTransvec_in_CRTProd (d d' : ℕ) (hcop : Nat.Coprime d d')
    (E : SpecialLinearGroup (Fin n) ℤ) (hE : IsTransvec E) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      E = p * q ∧ congMod n d p ∧ congMod n d' q := by
  obtain ⟨i, j, hij, c, rfl⟩ := hE; rw [slTransvecG_eq_slTransvec]
  exact slTransvec_in_CRTProd n d d' hcop i j hij c

omit [NeZero n] in
private lemma list_prod_in_CRTProd (d d' : ℕ) (_hcop : Nat.Coprime d d')
    (L : List (SpecialLinearGroup (Fin n) ℤ))
    (hL : ∀ E ∈ L, ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      E = p * q ∧ congMod n d p ∧ congMod n d' q) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      L.prod = p * q ∧ congMod n d p ∧ congMod n d' q := by
  induction L with
  | nil => exact one_in_CRTProd n d d'
  | cons E L ihL =>
    simp only [List.prod_cons]
    exact CRTProd_mul' n d d' E L.prod (hL E (by simp))
      (ihL (fun F hF => hL F (by simp [hF])))

omit [NeZero n] in
private lemma SLnZ_in_CRTProd (d d' : ℕ) (_hd : 0 < d) (_hd' : 0 < d')
    (hcop : Nat.Coprime d d') (σ : SpecialLinearGroup (Fin n) ℤ) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      σ = p * q ∧ congMod n d p ∧ congMod n d' q := by
  obtain ⟨L, hL_transvec, hL_prod⟩ := SLnZ_transvec_gen n σ
  rw [hL_prod]
  exact list_prod_in_CRTProd n d d' hcop L
    (fun E hE => isTransvec_in_CRTProd n d d' hcop E (hL_transvec E hE))

omit [NeZero n] in
/-- Chinese Remainder Theorem for `SL_n(ℤ)`: every element decomposes as a product of
congruence classes when gcd(d, d') = 1. -/
lemma SLnZ_CRT_decomposition (d d' : ℕ) (hd : 0 < d) (hd' : 0 < d') (hcop : Nat.Coprime d d')
    (τ : SpecialLinearGroup (Fin n) ℤ) :
    ∃ (τ₁ τ₂ : SpecialLinearGroup (Fin n) ℤ), τ = τ₁ * τ₂ ∧
      (∀ i j, (d : ℤ) ∣ ((τ₁ : Matrix (Fin n) (Fin n) ℤ) i j -
        if i = j then 1 else 0)) ∧
      (∀ i j, (d' : ℤ) ∣ ((τ₂ : Matrix (Fin n) (Fin n) ℤ) i j -
        if i = j then 1 else 0)) :=
  SLnZ_in_CRTProd n d d' hd hd' hcop τ

omit [NeZero n] in
/-- A congruent-to-identity element conjugated by `diag(a)` remains in `SL_n(ℤ)`. -/
lemma conjugate_congruent_mem_SLnZ (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (_hdiv : DivChain n a)
    (τ : SpecialLinearGroup (Fin n) ℤ) (hcong : ∀ i j, (∏ k, (a k : ℤ)) ∣
      ((τ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) :
    ∃ σ : SpecialLinearGroup (Fin n) ℤ,
      (σ : GL (Fin n) ℚ) = diagMat n a * (τ : GL (Fin n) ℚ) * (diagMat n a)⁻¹ := by
  have hdvd : ∀ i j, (a j : ℤ) ∣ (a i : ℤ) * τ.val i j := by
    intro i j; by_cases hij : i = j
    · subst hij; exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (by have := hcong i j; simp only [hij, ↓reduceIte, sub_zero] at this; exact this)) _
  set M : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (a i : ℤ) * τ.val i j / (a j : ℤ)
  set diag_a := Matrix.diagonal (fun i => (a i : ℤ))
  have h_int_eq : diag_a * τ.val = M * diag_a := by
    ext i j; simp only [diag_a, M, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    exact (Int.ediv_mul_cancel (hdvd i j)).symm
  have h_det_ne : diag_a.det ≠ 0 := by
    simp only [diag_a, Matrix.det_diagonal]
    exact ne_of_gt (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (ha i)))
  have hM_det : M.det = 1 := by
    have h := congr_arg Matrix.det h_int_eq
    rw [Matrix.det_mul, Matrix.det_mul, τ.prop, mul_one] at h
    exact (mul_left_cancel₀ h_det_ne (by rw [mul_one, mul_comm]; exact h)).symm
  refine ⟨⟨M, hM_det⟩, ?_⟩
  have h_Q_eq : (diagMat n a : GL (Fin n) ℚ) * (τ : GL (Fin n) ℚ) =
      mapGL ℚ ⟨M, hM_det⟩ * diagMat n a := by
    apply Units.ext
    have hτ_val : (↑(mapGL ℚ τ) : Matrix _ _ ℚ) = τ.val.map (Int.cast) := by
      simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
    have hM_val : (↑(mapGL ℚ (⟨M, hM_det⟩ : SpecialLinearGroup (Fin n) ℤ)) : Matrix _ _ ℚ) =
        M.map (Int.cast) := by
      simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
    simp only [Units.val_mul, hτ_val, hM_val, diagMat_val _ _ ha]
    have h_mul_map : ∀ (A B : Matrix (Fin n) (Fin n) ℤ),
        (A * B).map (Int.cast : ℤ → ℚ) = A.map Int.cast * B.map Int.cast := by
      intro A B; ext i j; simp [Matrix.mul_apply, Matrix.map_apply]
    have h_diag_map : (Matrix.diagonal (fun i => (a i : ℤ))).map (Int.cast : ℤ → ℚ) =
        Matrix.diagonal (fun i => (a i : ℚ)) := by
      ext i j; simp [Matrix.map_apply, Matrix.diagonal_apply]
    rw [← h_diag_map, ← h_mul_map, ← h_mul_map, h_int_eq]
  exact eq_mul_inv_iff_mul_eq.mpr h_Q_eq.symm

omit [NeZero n] in
/-- A congruent-to-identity element conjugated by `diag(b)⁻¹` remains in `SL_n(ℤ)`. -/
lemma inv_conjugate_congruent_mem_SLnZ (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (_hdiv : DivChain n b) (τ : SpecialLinearGroup (Fin n) ℤ)
    (hcong : ∀ i j, (∏ k, (b k : ℤ)) ∣
      ((τ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) :
    ∃ σ : SpecialLinearGroup (Fin n) ℤ,
      (σ : GL (Fin n) ℚ) = (diagMat n b)⁻¹ * (τ : GL (Fin n) ℚ) * diagMat n b := by
  have hdvd : ∀ i j, (b i : ℤ) ∣ (b j : ℤ) * τ.val i j := by
    intro i j; by_cases hij : i = j
    · subst hij; exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
        (by have := hcong i j; simp only [hij, ↓reduceIte, sub_zero] at this; exact this)) _
  set N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (b j : ℤ) * τ.val i j / (b i : ℤ)
  set diag_b := Matrix.diagonal (fun i => (b i : ℤ))
  have h_int_eq : τ.val * diag_b = diag_b * N := by
    ext i j; simp only [diag_b, N, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    calc τ.val i j * (b j : ℤ) = (b j : ℤ) * τ.val i j := mul_comm _ _
      _ = (b j : ℤ) * τ.val i j / (b i : ℤ) * (b i : ℤ) :=
          (Int.ediv_mul_cancel (hdvd i j)).symm
      _ = (b i : ℤ) * ((b j : ℤ) * τ.val i j / (b i : ℤ)) := mul_comm _ _
  have h_det_ne : diag_b.det ≠ 0 := by
    simp only [diag_b, Matrix.det_diagonal]
    exact ne_of_gt (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (hb i)))
  have hN_det : N.det = 1 := by
    have h := congr_arg Matrix.det h_int_eq
    rw [Matrix.det_mul, Matrix.det_mul, τ.prop, one_mul] at h
    exact (mul_left_cancel₀ h_det_ne (by rw [mul_one]; exact h)).symm
  refine ⟨⟨N, hN_det⟩, ?_⟩
  have h_Q_eq : (diagMat n b : GL (Fin n) ℚ) * mapGL ℚ ⟨N, hN_det⟩ =
      (τ : GL (Fin n) ℚ) * diagMat n b := by
    apply Units.ext
    have hτ_val : (↑(mapGL ℚ τ) : Matrix _ _ ℚ) = τ.val.map (Int.cast) := by
      simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
    have hN_val : (↑(mapGL ℚ (⟨N, hN_det⟩ : SpecialLinearGroup (Fin n) ℤ)) : Matrix _ _ ℚ) =
        N.map (Int.cast) := by
      simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
    simp only [Units.val_mul, hτ_val, hN_val, diagMat_val _ _ hb]
    have h_mul_map : ∀ (A B : Matrix (Fin n) (Fin n) ℤ),
        (A * B).map (Int.cast : ℤ → ℚ) = A.map Int.cast * B.map Int.cast := by
      intro A B; ext i j; simp [Matrix.mul_apply, Matrix.map_apply]
    have h_diag_map : (Matrix.diagonal (fun i => (b i : ℤ))).map (Int.cast : ℤ → ℚ) =
        Matrix.diagonal (fun i => (b i : ℚ)) := by
      ext i j; simp [Matrix.map_apply, Matrix.diagonal_apply]
    rw [← h_diag_map, ← h_mul_map, ← h_mul_map, h_int_eq]
  calc mapGL ℚ ⟨N, hN_det⟩
      = (diagMat n b)⁻¹ * (diagMat n b * mapGL ℚ ⟨N, hN_det⟩) := by rw [inv_mul_cancel_left]
    _ = (diagMat n b)⁻¹ * ((τ : GL (Fin n) ℚ) * diagMat n b) := by rw [h_Q_eq]
    _ = (diagMat n b)⁻¹ * (τ : GL (Fin n) ℚ) * diagMat n b := by rw [mul_assoc]

omit [NeZero n] in
/-- Set-level coprime product (Shimura Proposition 3.16, key step). -/
lemma doubleCoset_mul_coprime_mem (a b : Fin n → ℕ)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (ha : DivChain n a) (hb : DivChain n b) (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i))
    (τ : SpecialLinearGroup (Fin n) ℤ) :
    diagMat n a * (τ : GL (Fin n) ℚ) * diagMat n b ∈
      DoubleCoset.doubleCoset (diagMat n (a * b) : GL (Fin n) ℚ)
        (SLnZSubgroup n) (SLnZSubgroup n) := by
  obtain ⟨τ₁, τ₂, hτ, hτ₁, hτ₂⟩ := SLnZ_CRT_decomposition n (∏ i, a i) (∏ i, b i)
    (Finset.prod_pos (fun i _ => ha_pos i)) (Finset.prod_pos (fun i _ => hb_pos i)) hcop τ
  have hτ₁_cong : ∀ i j, (∏ k, (a k : ℤ)) ∣
      ((τ₁ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0) := by
    intro i j; convert hτ₁ i j using 1; simp
  obtain ⟨σ₁, hσ₁⟩ := conjugate_congruent_mem_SLnZ n a ha_pos ha τ₁ hτ₁_cong
  have hτ₂_cong : ∀ i j, (∏ k, (b k : ℤ)) ∣
      ((τ₂ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0) := by
    intro i j; convert hτ₂ i j using 1; simp
  obtain ⟨σ₂, hσ₂⟩ := inv_conjugate_congruent_mem_SLnZ n b hb_pos hb τ₂ hτ₂_cong
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨(σ₁ : GL (Fin n) ℚ), coe_mem_SLnZ n σ₁,
    (σ₂ : GL (Fin n) ℚ), coe_mem_SLnZ n σ₂, ?_⟩
  have hσ₁' : diagMat n a * (τ₁ : GL (Fin n) ℚ) =
      (σ₁ : GL (Fin n) ℚ) * diagMat n a := by rw [hσ₁]; group
  have hσ₂' : (τ₂ : GL (Fin n) ℚ) * diagMat n b =
      diagMat n b * (σ₂ : GL (Fin n) ℚ) := by rw [hσ₂]; group
  rw [hτ, map_mul (mapGL ℚ)]
  calc diagMat n a * ((τ₁ : GL (Fin n) ℚ) * (τ₂ : GL (Fin n) ℚ)) * diagMat n b
      = diagMat n a * (τ₁ : GL (Fin n) ℚ) *
          ((τ₂ : GL (Fin n) ℚ) * diagMat n b) := by group
    _ = diagMat n a * (τ₁ : GL (Fin n) ℚ) *
          (diagMat n b * (σ₂ : GL (Fin n) ℚ)) := by rw [hσ₂']
    _ = (σ₁ : GL (Fin n) ℚ) * diagMat n a *
          (diagMat n b * (σ₂ : GL (Fin n) ℚ)) := by rw [hσ₁']
    _ = (σ₁ : GL (Fin n) ℚ) * (diagMat n a * diagMat n b) *
          (σ₂ : GL (Fin n) ℚ) := by group
    _ = (σ₁ : GL (Fin n) ℚ) * diagMat n (a * b) *
          (σ₂ : GL (Fin n) ℚ) := by rw [diagMat_mul n a b ha_pos hb_pos]

lemma mulMap_coprime_eq (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (ha : DivChain n a) (hb : DivChain n b) (_hab : DivChain n (a * b))
    (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i))
    (p : decompQuot (GLPair n) (HeckeCoset.rep (TDiag a)) ×
      decompQuot (GLPair n) (HeckeCoset.rep (TDiag b))) :
    mulMap (GLPair n) (HeckeCoset.rep (TDiag a)) (HeckeCoset.rep (TDiag b)) p =
      TDiag (a * b) := by
  set H := (GLPair n).H
  obtain ⟨h₁a, hh₁a, h₂a, hh₂a, hδa_eq⟩ := T_diag_rep_decompose a ha_pos
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := T_diag_rep_decompose b hb_pos
  set α := (HeckeCoset.rep (TDiag a) : GL (Fin n) ℚ)
  set β := (HeckeCoset.rep (TDiag b) : GL (Fin n) ℚ)
  obtain ⟨σ, hσ⟩ := (SLnZSubgroup n).mul_mem
    ((SLnZSubgroup n).mul_mem hh₂a (SetLike.coe_mem p.2.out)) hh₁b
  have h_cop := doubleCoset_mul_coprime_mem n a b ha_pos hb_pos ha hb hcop σ
  rw [hσ, DoubleCoset.mem_doubleCoset] at h_cop
  obtain ⟨hc₁, hhc₁, hc₂, hhc₂, h_eq⟩ := h_cop
  have h_product_mem : (p.1.out : GL (Fin n) ℚ) * α *
      ((p.2.out : GL (Fin n) ℚ) * β) ∈
      DoubleCoset.doubleCoset (diagMat n (a * b) : GL (Fin n) ℚ) H H := by
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨(p.1.out : GL (Fin n) ℚ) * h₁a * hc₁,
      H.mul_mem (H.mul_mem (SetLike.coe_mem p.1.out) hh₁a) hhc₁,
      hc₂ * h₂b, H.mul_mem hhc₂ hh₂b, ?_⟩
    rw [show α = h₁a * diagMat n a * h₂a from hδa_eq,
        show β = h₁b * diagMat n b * h₂b from hδb_eq]
    rw [show (p.1.out : GL (Fin n) ℚ) * (h₁a * diagMat n a * h₂a) *
        ((p.2.out : GL (Fin n) ℚ) * (h₁b * diagMat n b * h₂b)) =
        (p.1.out : GL (Fin n) ℚ) * h₁a *
          (diagMat n a * (h₂a * (p.2.out : GL (Fin n) ℚ) * h₁b) * diagMat n b) * h₂b
      from by group,
      h_eq]; group
  apply HeckeCoset_ext_toSet (P := GLPair n)
  rw [mulMap, HeckeCoset.toSet_mk]
  simp only [TDiag, HeckeCoset.toSet_mk,
    diagMat_delta_val n (a * b) (fun i => Nat.mul_pos (ha_pos i) (hb_pos i))]
  exact doubleCoset_eq_of_mem' n _ _ h_product_mem

omit [NeZero n] in
private lemma GLnQ_mem_SLnZ_of_coprime_scaling (C : GL (Fin n) ℚ)
    (pa pb : ℕ) (hcop : Nat.Coprime pa pb) (h_det : (↑C : Matrix (Fin n) (Fin n) ℚ).det = 1)
    (h_a : ∀ i j, ∃ z : ℤ, (pa : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z)
    (h_b : ∀ i j, ∃ z : ℤ, (pb : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z) :
    C ∈ SLnZSubgroup n := by
  obtain ⟨s, t, hst⟩ := (show IsCoprime (pa : ℤ) (pb : ℤ) from by exact_mod_cast hcop.isCoprime)
  have h_int : ∀ i j, ∃ z : ℤ, (↑C : Matrix (Fin n) (Fin n) ℚ) i j = (z : ℚ) := by
    intro i j; obtain ⟨za, hza⟩ := h_a i j; obtain ⟨zb, hzb⟩ := h_b i j
    refine ⟨s * za + t * zb, ?_⟩
    have h1 : (↑C : Matrix (Fin n) (Fin n) ℚ) i j =
        s * ((pa : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) +
        t * ((pb : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) := by
      have hst_Q : (s : ℚ) * (pa : ℚ) + (t : ℚ) * (pb : ℚ) = 1 := by exact_mod_cast hst
      have := congr_arg (· * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) hst_Q
      simp only [add_mul, one_mul] at this; linarith
    rw [h1, hza, hzb]; push_cast; ring
  set N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (h_int i j).choose
  have hN_eq : ∀ i j, (↑C : Matrix (Fin n) (Fin n) ℚ) i j = ((N i j : ℤ) : ℚ) :=
    fun i j => (h_int i j).choose_spec
  have hN_det : N.det = 1 := by
    have hN_cast : (↑C : Matrix (Fin n) (Fin n) ℚ) = N.map (Int.cast : ℤ → ℚ) := by
      ext i j; simp only [N, Matrix.of_apply, Matrix.map_apply]; exact hN_eq i j
    exact_mod_cast show (N.det : ℚ) = 1 by rw [← (Int.cast_det N).symm, ← hN_cast, h_det]
  rw [MonoidHom.mem_range]; refine ⟨⟨N, hN_det⟩, ?_⟩
  apply Units.ext; simp only [mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply]
  ext i j; simp only [Matrix.map_apply]; exact (hN_eq i j).symm

omit [NeZero n] in
private lemma diagConj_scaling (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (σ : SpecialLinearGroup (Fin n) ℤ) (i j : Fin n) :
    ∃ z : ℤ, (∏ k, (a k : ℚ)) *
      ((↑((diagMat n a)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a) :
        Matrix (Fin n) (Fin n) ℚ) i j) = z := by
  set C := (diagMat n a)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a
  have h_mul : diagMat n a * C = (σ : GL (Fin n) ℚ) * diagMat n a := by
    simp only [C, mul_assoc]; rw [mul_inv_cancel_left]
  have h_entry := congr_arg (fun (g : GL (Fin n) ℚ) => (↑g : Matrix _ _ ℚ) i j) h_mul
  simp only [Units.val_mul, diagMat_val _ _ ha, mapGL_coe_matrix, map_apply_coe,
    RingHom.mapMatrix_apply, Int.coe_castRingHom, algebraMap_int_eq,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply] at h_entry
  have h_dvd : (a i : ℤ) ∣ ∏ k, (a k : ℤ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨(∏ k, (a k : ℤ)) / (a i : ℤ) * σ.val i j * (a j : ℤ), ?_⟩
  have hai_ne : (a i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha i).ne'
  have : (∏ k, (a k : ℚ)) * (↑C : Matrix _ _ ℚ) i j =
      (∏ k, (a k : ℚ)) / (a i : ℚ) * ((a i : ℚ) * (↑C : Matrix _ _ ℚ) i j) := by field_simp
  rw [this, h_entry]
  have hai_ne_int : (a i : ℤ) ≠ 0 := ne_of_gt (Int.natCast_pos.mpr (ha i))
  rw [show ((∏ k, (a k : ℤ)) / (a i : ℤ) * σ.val i j * (a j : ℤ) : ℤ) =
      (∏ k, (a k : ℤ)) / (a i : ℤ) * ((σ.val i j : ℤ) * (a j : ℤ)) from by ring]
  push_cast [Int.cast_div h_dvd (show ((a i : ℤ) : ℚ) ≠ 0 from Int.cast_ne_zero.mpr hai_ne_int)]
  ring

omit [NeZero n] in
private lemma diagSandwich_scaling (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (F G E : SpecialLinearGroup (Fin n) ℤ) (i j : Fin n) :
    ∃ z : ℤ, (∏ k, (b k : ℚ)) *
      ((↑((F : GL (Fin n) ℚ) * diagMat n b * (G : GL (Fin n) ℚ) *
        (diagMat n b)⁻¹ * (E : GL (Fin n) ℚ)) :
        Matrix (Fin n) (Fin n) ℚ) i j) = z := by
  set C := (F : GL (Fin n) ℚ) * diagMat n b * (G : GL (Fin n) ℚ) *
    (diagMat n b)⁻¹ * (E : GL (Fin n) ℚ)
  set D := diagMat n b * (G : GL (Fin n) ℚ) * (diagMat n b)⁻¹
  set F_GL := (F : GL (Fin n) ℚ); set E_GL := (E : GL (Fin n) ℚ)
  have h_C_entry : (↑C : Matrix (Fin n) (Fin n) ℚ) i j = ∑ p, ∑ q,
      (↑F_GL : Matrix (Fin n) (Fin n) ℚ) i p *
      (↑D : Matrix (Fin n) (Fin n) ℚ) p q *
      (↑E_GL : Matrix (Fin n) (Fin n) ℚ) q j := by
    have := congr_arg (fun (g : GL (Fin n) ℚ) => (↑g : Matrix (Fin n) (Fin n) ℚ) i j)
      (show C = (F : GL (Fin n) ℚ) * D * (E : GL (Fin n) ℚ) from by simp only [C, D, mul_assoc])
    simp only [Units.val_mul, Matrix.mul_apply] at this
    rw [this]; simp only [Finset.sum_mul, mul_assoc]; rw [Finset.sum_comm]
  set D_mat := (↑D : Matrix (Fin n) (Fin n) ℚ)
  have h_D_scale : ∀ p q, ∃ z : ℤ, (∏ k, (b k : ℚ)) * D_mat p q = z := by
    intro p q
    have h_D_entry : D_mat p q = (b p : ℚ) * (↑(G.val p q) : ℚ) * ((b q : ℚ)⁻¹) := by
      have h_Db : D * diagMat n b = diagMat n b * (G : GL (Fin n) ℚ) := by
        simp only [D, mul_assoc, inv_mul_cancel, mul_one]
      have h_entry := congr_arg
        (fun (g : GL (Fin n) ℚ) => (↑g : Matrix (Fin n) (Fin n) ℚ) p q) h_Db
      simp only [Units.val_mul, diagMat_val _ _ hb, mapGL_coe_matrix, map_apply_coe,
        RingHom.mapMatrix_apply, Int.coe_castRingHom, algebraMap_int_eq,
        Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at h_entry
      have hbq_ne : (b q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hb q).ne'
      field_simp at h_entry ⊢; linarith
    rw [h_D_entry]
    have h_dvd : (b q : ℤ) ∣ ∏ k, (b k : ℤ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ q)
    have hbq_ne : (b q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hb q).ne'
    have hbq_ne_int : (b q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (hb q).ne'
    refine ⟨(∏ k, (b k : ℤ)) / (b q : ℤ) * (b p : ℤ) * G.val p q, ?_⟩
    have h_div_eq : (∏ k, (b k : ℚ)) * ((b p : ℚ) * ↑(G.val p q) * ((b q : ℚ)⁻¹)) =
        (∏ k, (b k : ℚ)) / (b q : ℚ) * ((b p : ℚ) * ↑(G.val p q)) := by
      rw [div_eq_mul_inv]; ring
    rw [h_div_eq]
    push_cast [Int.cast_div h_dvd (show ((b q : ℤ) : ℚ) ≠ 0 from Int.cast_ne_zero.mpr hbq_ne_int)]
    ring
  rw [h_C_entry, Finset.mul_sum]; simp_rw [Finset.mul_sum, mul_assoc]
  refine ⟨∑ p, ∑ q, (F.val i p) * (h_D_scale p q).choose * (E.val q j), ?_⟩
  push_cast; apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro q _
  have hDpq := (h_D_scale p q).choose_spec
  simp only [F_GL, E_GL, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
    Int.coe_castRingHom, algebraMap_int_eq, Matrix.map_apply]
  set z := (h_D_scale p q).choose
  have h1 : (∏ k, (b k : ℚ)) * ((↑(F.val i p) : ℚ) * (D_mat p q * (↑(E.val q j) : ℚ))) =
      (↑(F.val i p) : ℚ) * ((∏ k, (b k : ℚ)) * D_mat p q) * (↑(E.val q j) : ℚ) := by ring
  rw [h1, hDpq]

omit [NeZero n] in
private lemma coprime_coupling_mem_H (a b : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (_hda : DivChain n a) (_hdb : DivChain n b) (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i))
    (σ F G E : SpecialLinearGroup (Fin n) ℤ)
    (h_eq : (diagMat n a)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a =
      (F : GL (Fin n) ℚ) * diagMat n b * (G : GL (Fin n) ℚ) *
        (diagMat n b)⁻¹ * (E : GL (Fin n) ℚ)) :
    (diagMat n a)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a ∈ SLnZSubgroup n := by
  set C := (diagMat n a)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a
  have h_det : (↑C : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
    simp only [C, Units.val_mul, Matrix.det_mul, mapGL_coe_matrix, map_apply_coe,
      RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom]
    rw [show (σ.val.map (Int.cast : ℤ → ℚ)).det = 1 from by
      rw [show σ.val.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix σ.val from by
        ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply],
        ← RingHom.map_det]; simp [σ.prop]]
    rw [mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  have h_scale_a : ∀ i j, ∃ z : ℤ,
      (↑(∏ i, a i) : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z := by
    intro i j; simp only [C]; convert diagConj_scaling n a ha σ i j using 2; push_cast; ring
  have h_scale_b : ∀ i j, ∃ z : ℤ,
      (↑(∏ i, b i) : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z := by
    intro i j; rw [h_eq]; convert diagSandwich_scaling n b hb F G E i j using 2; push_cast; ring
  exact GLnQ_mem_SLnZ_of_coprime_scaling n C (∏ i, a i) (∏ i, b i) hcop h_det
    h_scale_a h_scale_b

private lemma heckeMultiplicity_coprime_le_one (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i)
    (hb_pos : ∀ i, 0 < b i) (ha : DivChain n a) (hb : DivChain n b)
    (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i)) :
    HeckeRing.heckeMultiplicity (GLPair n) (HeckeCoset.rep (TDiag a))
      (HeckeCoset.rep (TDiag b))
      (HeckeCoset.rep (TDiag (a * b))) ≤ 1 := by
  classical
  set D_a := TDiag a; set D_b := TDiag b
  simp only [HeckeRing.heckeMultiplicity]; norm_cast; rw [Nat.card_eq_fintype_card]
  apply Fintype.card_le_one_iff_subsingleton.mpr; constructor
  intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩; simp only [Set.mem_setOf_eq] at h₁ h₂
  set H := (GLPair n).H
  set δ_a' := (HeckeCoset.rep D_a : GL (Fin n) ℚ) with hδ_a_def
  set δ_b' := (HeckeCoset.rep D_b : GL (Fin n) ℚ) with hδ_b_def
  have hi : i₁ = i₂ := by
    by_contra hne; apply HeckeRing.decompQuot_coset_diff (GLPair n) (HeckeCoset.rep D_a) i₁ i₂ hne
    obtain ⟨h₁a, hh₁a, h₂a, hh₂a, hδa_eq⟩ := T_diag_rep_decompose a ha_pos
    obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := T_diag_rep_decompose b hb_pos
    obtain ⟨σ', hσ'⟩ := show h₁a⁻¹ * ((i₂.out : GL (Fin n) ℚ)⁻¹ *
        (i₁.out : GL (Fin n) ℚ)) * h₁a ∈ SLnZSubgroup n from
      show _ ∈ H from H.mul_mem (H.mul_mem (H.inv_mem hh₁a)
        (H.mul_mem (H.inv_mem (SetLike.coe_mem i₂.out)) (SetLike.coe_mem i₁.out))) hh₁a
    have h12 := h₁.trans h₂.symm
    have hmem12 : (i₁.out : GL (Fin n) ℚ) * δ_a' *
        ((j₁.out : GL (Fin n) ℚ) * δ_b') ∈
        ({(i₂.out : GL (Fin n) ℚ) * δ_a' *
          ((j₂.out : GL (Fin n) ℚ) * δ_b')} : Set _) * (H : Set _) := by
      have h12' : ({(i₁.out : GL (Fin n) ℚ) * δ_a' *
          ((j₁.out : GL (Fin n) ℚ) * δ_b')} : Set _) * (H : Set _) =
          ({(i₂.out : GL (Fin n) ℚ) * δ_a' *
          ((j₂.out : GL (Fin n) ℚ) * δ_b')} : Set _) * (H : Set _) := by
        rw [Set.singleton_mul_singleton, Set.singleton_mul_singleton] at h12; exact h12
      rw [← h12']; exact ⟨_, Set.mem_singleton _, 1, H.one_mem, by simp⟩
    obtain ⟨_, h_sing, κ, hκ, hκ_eq⟩ := hmem12
    rw [Set.mem_singleton_iff] at h_sing; subst h_sing
    have h_beta_eq : δ_a'⁻¹ * (i₂.out : GL (Fin n) ℚ)⁻¹ *
        (i₁.out : GL (Fin n) ℚ) * δ_a' =
        (j₂.out : GL (Fin n) ℚ) * δ_b' * κ * δ_b'⁻¹ *
          (j₁.out : GL (Fin n) ℚ)⁻¹ := by
      apply mul_left_cancel (a := (i₂.out : GL (Fin n) ℚ) * δ_a')
      apply mul_right_cancel (b := (j₁.out : GL (Fin n) ℚ) * δ_b')
      simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      simp only [mul_assoc] at hκ_eq; exact hκ_eq.symm
    have hσ'_eq : (σ' : GL (Fin n) ℚ) =
        h₁a⁻¹ * ((i₂.out : GL (Fin n) ℚ)⁻¹ * (i₁.out : GL (Fin n) ℚ)) * h₁a := hσ'
    have hδa_eq' : δ_a' = h₁a * diagMat n a * h₂a := by rw [hδ_a_def]; exact hδa_eq
    have h_lhs_eq : δ_a'⁻¹ * (i₂.out : GL (Fin n) ℚ)⁻¹ *
        (i₁.out : GL (Fin n) ℚ) * δ_a' =
        h₂a⁻¹ * ((diagMat n a)⁻¹ * (σ' : GL (Fin n) ℚ) * diagMat n a) * h₂a := by
      rw [hσ'_eq, hδa_eq']
      group
    obtain ⟨F_pre, hF_pre⟩ := show (j₂.out : GL (Fin n) ℚ) * h₁b ∈ SLnZSubgroup n from
      show _ ∈ H from H.mul_mem (SetLike.coe_mem j₂.out) hh₁b
    obtain ⟨G_pre, hG_pre⟩ := show h₂b * κ * h₂b⁻¹ ∈ SLnZSubgroup n from
      show _ ∈ H from H.mul_mem (H.mul_mem hh₂b hκ) (H.inv_mem hh₂b)
    obtain ⟨E_pre, hE_pre⟩ := show h₁b⁻¹ * (j₁.out : GL (Fin n) ℚ)⁻¹ ∈ SLnZSubgroup n from
      show _ ∈ H from H.mul_mem (H.inv_mem hh₁b) (H.inv_mem (SetLike.coe_mem j₁.out))
    have hδb_eq' : δ_b' = h₁b * diagMat n b * h₂b := by rw [hδ_b_def]; exact hδb_eq
    have h_rhs_eq : (j₂.out : GL (Fin n) ℚ) * δ_b' * κ * δ_b'⁻¹ *
        (j₁.out : GL (Fin n) ℚ)⁻¹ =
        (F_pre : GL (Fin n) ℚ) * diagMat n b * (G_pre : GL (Fin n) ℚ) *
          (diagMat n b)⁻¹ * (E_pre : GL (Fin n) ℚ) := by
      rw [hF_pre, hG_pre, hE_pre, hδb_eq']
      group
    obtain ⟨FF, hFF⟩ := show h₂a * (F_pre : GL (Fin n) ℚ) ∈ SLnZSubgroup n from
      show _ ∈ H from H.mul_mem hh₂a (coe_mem_SLnZ n F_pre)
    obtain ⟨EE, hEE⟩ := show (E_pre : GL (Fin n) ℚ) * h₂a⁻¹ ∈ SLnZSubgroup n from
      show _ ∈ H from H.mul_mem (coe_mem_SLnZ n E_pre) (H.inv_mem hh₂a)
    have h_C_eq : (diagMat n a)⁻¹ * (σ' : GL (Fin n) ℚ) * diagMat n a =
        (FF : GL (Fin n) ℚ) * diagMat n b * (G_pre : GL (Fin n) ℚ) *
          (diagMat n b)⁻¹ * (EE : GL (Fin n) ℚ) := by
      rw [h_lhs_eq, h_rhs_eq] at h_beta_eq
      apply mul_left_cancel (a := h₂a⁻¹); apply mul_right_cancel (b := h₂a)
      rw [hFF, hEE]; simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
      simp only [mul_assoc] at h_beta_eq; exact h_beta_eq
    have h_beta_in_H : δ_a'⁻¹ * (i₂.out : GL (Fin n) ℚ)⁻¹ *
        (i₁.out : GL (Fin n) ℚ) * δ_a' ∈ H := by
      rw [h_lhs_eq]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh₂a)
        (coprime_coupling_mem_H n a b ha_pos hb_pos ha hb hcop σ' FF G_pre EE h_C_eq)) hh₂a
    exact HeckeRing.leftCoset_eq_of_not_disjoint (H := (GLPair n).H) _ _ (by
      rw [Set.not_disjoint_iff]
      exact ⟨(i₁.out : GL (Fin n) ℚ) * δ_a', ⟨1, H.one_mem, mul_one _⟩,
        ⟨δ_a'⁻¹ * (i₂.out : GL (Fin n) ℚ)⁻¹ * (i₁.out : GL (Fin n) ℚ) * δ_a',
          h_beta_in_H, by simp only [smul_eq_mul, ← hδ_a_def]; group⟩⟩)
  subst hi
  have hj := HeckeRing.decompQuot_snd_eq_of_fst_eq (GLPair n) (HeckeCoset.rep D_a)
    (HeckeCoset.rep D_b) (HeckeCoset.rep (TDiag (a * b)))
    i₁ j₁ j₂ h₁ h₂
  subst hj; rfl

private lemma heckeMultiplicity_coprime_pos (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i)
    (hb_pos : ∀ i, 0 < b i) (ha : DivChain n a) (hb : DivChain n b)
    (hab : DivChain n (a * b)) (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i)) :
    0 < HeckeRing.heckeMultiplicity (GLPair n) (HeckeCoset.rep (TDiag a))
      (HeckeCoset.rep (TDiag b))
      (HeckeCoset.rep (TDiag (a * b))) := by
  set D_a := TDiag a; set D_b := TDiag b; set D_ab := TDiag (a * b)
  have h_mem :
      D_ab ∈ HeckeRing.mulSupport (GLPair n) (HeckeCoset.rep D_a) (HeckeCoset.rep D_b) := by
    simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
      true_and, Prod.exists]
    have ⟨i₀⟩ : Nonempty (decompQuot (GLPair n) (HeckeCoset.rep D_a)) :=
      Fintype.card_pos_iff.mp (by
        have := HeckeRing.HeckeCoset_deg_pos (GLPair n) D_a
        simp only [HeckeRing.HeckeCosetDeg] at this; omega)
    have ⟨j₀⟩ : Nonempty (decompQuot (GLPair n) (HeckeCoset.rep D_b)) :=
      Fintype.card_pos_iff.mp (by
        have := HeckeRing.HeckeCoset_deg_pos (GLPair n) D_b
        simp only [HeckeRing.HeckeCosetDeg] at this; omega)
    exact ⟨i₀, j₀, mulMap_coprime_eq n a b ha_pos hb_pos ha hb hab hcop (i₀, j₀)⟩
  exact HeckeRing.heckeMultiplicity_pos_of_mem (GLPair n) _ _ _ h_mem

/-- Coprime product in the Hecke ring (Shimura Proposition 3.16). -/
theorem T_diag_mul_coprime (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (ha : DivChain n a) (hb : DivChain n b) (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i)) :
    TElem a * TElem b = TElem (a * b) := by
  have hab := DivChain_mul n a b ha hb
  refine HeckeRing.T_single_one_mul_eq_single (GLPair n) (TDiag a) (TDiag b)
    (TDiag (a * b)) (by
      have h_le := heckeMultiplicity_coprime_le_one n a b ha_pos hb_pos ha hb hcop
      have h_pos := heckeMultiplicity_coprime_pos n a b ha_pos hb_pos ha hb hab hcop
      omega) ?_
  · intro A hA; apply HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport; intro h_mem
    simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
      true_and] at h_mem
    obtain ⟨⟨i, j⟩, heq⟩ := h_mem
    exact hA (heq.symm.trans (mulMap_coprime_eq n a b ha_pos hb_pos ha hb hab hcop (i, j)))

end Coprime

end HeckeRing.GLn
