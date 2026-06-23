/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition

/-!
# GL₂ Hecke Algebra: Definitions for Theorem 3.24

Specialization of the GL_n Hecke algebra to n=2. Defines T(a,d), T(m), and
structural lemmas for Shimura's Theorem 3.24.

## Main definitions

* `TAd` -- `T(a,d)` basis element
* `TPp` -- scalar double coset `T(p,p)`
* `TSum` -- Shimura's `T(m) = Σ T(a,d)` over divisor pairs

## References

* Shimura, Theorem 3.24
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset HeckeRing.GLn

open scoped Pointwise

namespace HeckeRing.GL2

/-- `T(a,d)` for n=2: the Hecke basis element for diagonal `(a,d)` with `a | d`.
    Returns 0 when `a = 0` or `d = 0` or `a ∤ d`. -/
noncomputable def TAd (a d : ℕ) : HeckeAlgebra 2 :=
  if _ : 0 < a ∧ 0 < d ∧ a ∣ d then TElem ![a, d] else 0

/-- Unfold `TAd` to `TElem` when all positivity and divisibility conditions hold. -/
lemma T_ad_of_pos (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (h : a ∣ d) :
    TAd a d = TElem ![a, d] :=
  dif_pos ⟨ha, hd, h⟩

/-- `TAd a d` is zero when the positivity or divisibility conditions fail. -/
lemma T_ad_eq_zero {a d : ℕ} (h : ¬(0 < a ∧ 0 < d ∧ a ∣ d)) : TAd a d = 0 :=
  dif_neg h

/-- `T(p,p)`: the scalar double coset for prime `p`, equal to `TAd p p`. -/
noncomputable def TPp (p : ℕ) : HeckeAlgebra 2 := TAd p p

/-- For `p` prime, `T(p,p)` equals the scalar diagonal element `TElem(p,p)`. -/
lemma T_pp_of_pos (p : ℕ) (hp : p.Prime) : TPp p = TElem (fun _ : Fin 2 => p) := by
  simp only [TPp, T_ad_of_pos p p hp.pos hp.pos (dvd_refl _)]
  exact T_elem_congr_diag 2 (funext fun i => by fin_cases i <;> rfl)

/-- `T(p,p)` is definitionally equal to `TAd p p`. -/
lemma T_pp_eq_T_ad (p : ℕ) : TPp p = TAd p p := rfl

/-- The all-ones diagonal element is the identity in the Hecke algebra. -/
lemma T_elem_ones_eq : TElem (fun _ : Fin 2 => 1) = 1 := by
  change TSingle (GLPair 2) ℤ (TDiag (fun _ : Fin 2 => 1)) 1 = 1
  rw [T_diag_ones]; exact (one_def (GLPair 2) (Z := ℤ)).symm

/-- T(1,1) is the identity element. -/
@[simp] lemma T_ad_one_one : TAd 1 1 = 1 := by
  rw [T_ad_of_pos 1 1 Nat.one_pos Nat.one_pos (dvd_refl _)]
  exact (T_elem_congr_diag 2
    (funext fun i => by fin_cases i <;> rfl)).trans T_elem_ones_eq

/-- `T(m) = Σ_{a | m} T(a, m/a)`. -/
noncomputable def TSum (m : ℕ+) : HeckeAlgebra 2 :=
  ∑ a ∈ (m : ℕ).divisors, TAd a ((m : ℕ) / a)

section Structural

variable (p : ℕ) (hp : p.Prime)

private lemma doubleCoset_eq_of_mem' (g δ : GL (Fin 2) ℚ)
    (h : g ∈ DoubleCoset.doubleCoset δ (SLnZSubgroup 2) (SLnZSubgroup 2)) :
    DoubleCoset.doubleCoset g (SLnZSubgroup 2) (SLnZSubgroup 2) =
      DoubleCoset.doubleCoset δ (SLnZSubgroup 2) (SLnZSubgroup 2) := by
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := DoubleCoset.mem_doubleCoset.mp h
  rw [heq]
  exact (doubleCoset_mul_right_eq_self (GLPair 2) ⟨h₂, hh₂⟩ (h₁ * δ)).trans
    (doset_mul_left_eq_self (GLPair 2) ⟨h₁, hh₁⟩ δ)

/-- For p prime, T(p) = TAd(1,p). -/
lemma T_sum_prime : TSum ⟨p, hp.pos⟩ = TAd 1 p := by
  change ∑ a ∈ p.divisors, TAd a (p / a) = _
  rw [hp.sum_divisors, Nat.div_self hp.pos, Nat.div_one]
  have h1 : TAd p 1 = 0 := T_ad_eq_zero (by
    push Not; exact fun _ _ hdvd => hp.one_lt.not_ge (Nat.le_of_dvd Nat.one_pos hdvd))
  rw [h1, zero_add]

private lemma diagMul_scalar_comm (b : Fin 2 → ℕ) (c : ℕ) :
    b * (fun _ => c) = (fun _ => c) * b :=
  funext fun _ => Nat.mul_comm _ _

private lemma scalar_product_mem_doubleCoset
    (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (_hb : DivChain 2 b) (c : ℕ) (hc : 0 < c)
    (x1 db x2 dc : GL (Fin 2) ℚ)
    (h₁b : GL (Fin 2) ℚ) (hh₁b : h₁b ∈ (GLPair 2).H)
    (h₂b : GL (Fin 2) ℚ) (hh₂b : h₂b ∈ (GLPair 2).H)
    (h₁c : GL (Fin 2) ℚ) (hh₁c : h₁c ∈ (GLPair 2).H)
    (h₂c : GL (Fin 2) ℚ) (hh₂c : h₂c ∈ (GLPair 2).H)
    (hx1 : x1 ∈ (GLPair 2).H) (hx2 : x2 ∈ (GLPair 2).H)
    (hδb_eq : db = h₁b * diagMat 2 b * h₂b)
    (hδc_eq : dc = h₁c * diagMat 2 (fun _ => c) * h₂c) :
    x1 * db * (x2 * dc) ∈ DoubleCoset.doubleCoset
      (diagMat 2 (b * (fun _ => c)) : GL (Fin 2) ℚ) (GLPair 2).H (GLPair 2).H := by
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨x1 * h₁b, (GLPair 2).H.mul_mem hx1 hh₁b,
          h₂b * x2 * h₁c * h₂c,
          (GLPair 2).H.mul_mem ((GLPair 2).H.mul_mem
            ((GLPair 2).H.mul_mem hh₂b hx2) hh₁c) hh₂c, ?_⟩
  rw [hδb_eq, hδc_eq]
  have h_comm := diagMat_scalar_comm 2 c hc (h₂b * x2 * h₁c)
  calc x1 * (h₁b * diagMat 2 b * h₂b) *
      (x2 * (h₁c * diagMat 2 (fun _ => c) * h₂c))
      = x1 * h₁b * (diagMat 2 b * (h₂b * x2 * h₁c)) *
        (diagMat 2 (fun _ => c) * h₂c) := by group
    _ = x1 * h₁b * (diagMat 2 b *
          (diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c))) * h₂c := by
        have : (h₂b * x2 * h₁c) * diagMat 2 (fun _ => c) =
            diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c) := h_comm.symm
        calc x1 * h₁b * (diagMat 2 b * (h₂b * x2 * h₁c)) *
            (diagMat 2 (fun _ => c) * h₂c)
            = x1 * h₁b * (diagMat 2 b *
                ((h₂b * x2 * h₁c) * diagMat 2 (fun _ => c))) * h₂c := by group
          _ = x1 * h₁b * (diagMat 2 b *
                (diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c))) * h₂c := by rw [this]
    _ = x1 * h₁b * (diagMat 2 (b * (fun _ => c)) *
          (h₂b * x2 * h₁c)) * h₂c := by
        rw [show diagMat 2 b * (diagMat 2 (fun _ => c) * (h₂b * x2 * h₁c)) =
            (diagMat 2 b * diagMat 2 (fun _ => c)) * (h₂b * x2 * h₁c) from by group,
          diagMat_mul 2 b (fun _ => c) hb_pos (fun _ => hc)]
    _ = x1 * h₁b * diagMat 2 (b * (fun _ => c)) *
        (h₂b * x2 * h₁c * h₂c) := by group

private lemma mulMap_right_scalar_eq (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain 2 b)
    (c : ℕ) (hc : 0 < c) (_hbc : DivChain 2 (b * (fun _ => c)))
    (p : decompQuot (GLPair 2) (HeckeCoset.rep (TDiag b)) ×
         decompQuot (GLPair 2) (HeckeCoset.rep (TDiag (fun _ : Fin 2 => c)))) :
    mulMap (GLPair 2) (HeckeCoset.rep (TDiag b))
      (HeckeCoset.rep (TDiag (fun _ : Fin 2 => c))) p =
      TDiag (b * (fun _ => c)) := by
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := T_diag_rep_decompose b hb_pos
  obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ :=
    T_diag_rep_decompose (fun _ : Fin 2 => c) (fun _ => hc)
  have hbc_pos : ∀ i, 0 < (b * (fun (_ : Fin 2) => c)) i := fun i => Nat.mul_pos (hb_pos i) hc
  have h_mem := scalar_product_mem_doubleCoset b hb_pos hb c hc
      p.1.out _ p.2.out _ h₁b hh₁b h₂b hh₂b h₁c hh₁c h₂c hh₂c
      (SetLike.coe_mem _) (SetLike.coe_mem _) hδb_eq hδc_eq
  rw [show (diagMat 2 (b * fun _ => c) : GL (Fin 2) ℚ) =
    ↑(diagMatDelta 2 (b * fun _ => c)) from (diagMat_delta_val 2 _ hbc_pos).symm] at h_mem
  exact HeckeCoset_ext_toSet (P := GLPair 2)
    (doubleCoset_eq_of_mem' _ _ h_mem)

private lemma scalar_coset_rep_normalizes (c : ℕ) (hc : 0 < c) :
    let D_c := TDiag (fun _ : Fin 2 => c)
    let H' := (GLPair 2).H
    let δ_c := (HeckeCoset.rep D_c : GL (Fin 2) ℚ)
    ({δ_c} : Set (GL (Fin 2) ℚ)) * (H' : Set (GL (Fin 2) ℚ)) =
    (H' : Set (GL (Fin 2) ℚ)) * {δ_c} := by
  intro D_c H' δ_c
  obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ :=
    T_diag_rep_decompose (fun _ : Fin 2 => c) (fun _ => hc)
  have hδc_simp : δ_c = (h₁c * h₂c) * diagMat 2 (fun _ => c) := by
    have : δ_c = ↑(HeckeCoset.rep (TDiag (fun _ : Fin 2 => c))) := rfl
    rw [this, hδc_eq, mul_assoc, diagMat_scalar_comm 2 c hc h₂c, ← mul_assoc]
  have hδc_norm : ConjAct.toConjAct δ_c • H' = H' := by
    rw [hδc_simp, map_mul, ← smul_smul, conjAct_scalar_smul_eq 2 c hc]
    exact HeckeRing.conjAct_smul_elt_eq H' ⟨h₁c * h₂c, H'.mul_mem hh₁c hh₂c⟩
  have h_norm_coe : ({δ_c} : Set (GL (Fin 2) ℚ)) * (H' : Set (GL (Fin 2) ℚ)) * {δ_c⁻¹} =
      (H' : Set (GL (Fin 2) ℚ)) := by
    have h1 : (ConjAct.toConjAct δ_c • H' : Set (GL (Fin 2) ℚ)) =
        (H' : Set (GL (Fin 2) ℚ)) := by
      rw [show (ConjAct.toConjAct δ_c • H' : Set (GL (Fin 2) ℚ)) =
          ((ConjAct.toConjAct δ_c • H' : Subgroup _) : Set (GL (Fin 2) ℚ)) by rfl]
      congr 1
    rw [conjAct_smul_coe_eq] at h1; exact h1
  have := congrFun (congrArg HMul.hMul h_norm_coe) {δ_c}
  simp_rw [mul_assoc, Set.singleton_mul_singleton] at this; simpa using this

private lemma mem_mulSupport_right_scalar (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (b * (fun _ => c))) :
    let D_b := TDiag b
    let D_c := TDiag (fun _ : Fin 2 => c)
    let D_bc := TDiag (b * (fun _ => c))
    D_bc ∈ HeckeRing.mulSupport (GLPair 2)
      (HeckeCoset.rep D_b) (HeckeCoset.rep D_c) := by
  intro D_b D_c D_bc
  simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and, Prod.exists]
  have ⟨i₀⟩ : Nonempty (decompQuot (GLPair 2) (HeckeCoset.rep D_b)) :=
    Fintype.card_pos_iff.mp (by
      have := HeckeRing.HeckeCoset_deg_pos (GLPair 2) D_b
      simp only [HeckeRing.HeckeCosetDeg] at this; omega)
  have h_card : Fintype.card (decompQuot (GLPair 2) (HeckeCoset.rep D_c)) = 1 := by
    have := HeckeCoset_deg_scalar 2 c hc
    simp only [HeckeRing.HeckeCosetDeg] at this; exact_mod_cast this
  have ⟨j₀⟩ : Nonempty (decompQuot (GLPair 2) (HeckeCoset.rep D_c)) :=
    Fintype.card_pos_iff.mp (by rw [h_card]; exact Nat.one_pos)
  exact ⟨i₀, j₀, mulMap_right_scalar_eq b hb_pos hb c hc hbc (i₀, j₀)⟩

private lemma heckeMultiplicity_right_scalar_eq_one (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain 2 b)
    (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (b * (fun _ => c)))
    (D_b : HeckeCoset (GLPair 2)) (hDb : D_b = TDiag b)
    (D_c : HeckeCoset (GLPair 2)) (hDc : D_c = TDiag (fun _ : Fin 2 => c))
    (D_bc : HeckeCoset (GLPair 2)) (hDbc : D_bc = TDiag (b * (fun _ => c))) :
    HeckeRing.heckeMultiplicity (GLPair 2) (HeckeCoset.rep D_b)
      (HeckeCoset.rep D_c) (HeckeCoset.rep D_bc) = 1 := by
  subst hDb; subst hDc; subst hDbc
  have h_card :
      Fintype.card (decompQuot (GLPair 2) (HeckeCoset.rep (TDiag (fun _ : Fin 2 => c)))) = 1 := by
    have := HeckeCoset_deg_scalar 2 c hc
    simp only [HeckeRing.HeckeCosetDeg] at this; exact_mod_cast this
  haveI : Subsingleton (decompQuot (GLPair 2) (HeckeCoset.rep (TDiag (fun _ : Fin 2 => c)))) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
  have h_le : HeckeRing.heckeMultiplicity (GLPair 2) (HeckeCoset.rep (TDiag b))
      (HeckeCoset.rep (TDiag (fun _ : Fin 2 => c)))
      (HeckeCoset.rep (TDiag (b * (fun _ => c)))) ≤ 1 := by
    classical
    simp only [HeckeRing.heckeMultiplicity]; norm_cast; rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor; intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
    have hj : j₁ = j₂ := Subsingleton.elim j₁ j₂; subst hj
    simp only [Set.mem_setOf_eq] at h₁ h₂
    have hi : i₁ = i₂ := by
      by_contra hne
      apply HeckeRing.decompQuot_coset_diff (GLPair 2) (HeckeCoset.rep (TDiag b)) i₁ i₂ hne
      let δ_c := (HeckeCoset.rep (TDiag (fun _ : Fin 2 => c)) : GL (Fin 2) ℚ)
      have h_coset : ({(j₁.out : GL (Fin 2) ℚ) * δ_c} : Set _) *
          ((GLPair 2).H : Set _) = ((GLPair 2).H : Set _) * {δ_c} := by
        rw [← Set.singleton_mul_singleton, mul_assoc, scalar_coset_rep_normalizes c hc,
          ← mul_assoc, Subgroup.singleton_mul_subgroup (SetLike.coe_mem j₁.out)]
      have h12' :
          ({(i₁.out : GL (Fin 2) ℚ) * (HeckeCoset.rep (TDiag b) : GL (Fin 2) ℚ)} : Set _) *
            (((GLPair 2).H : Set _) * {δ_c}) =
          ({(i₂.out : GL (Fin 2) ℚ) * (HeckeCoset.rep (TDiag b) : GL (Fin 2) ℚ)} : Set _) *
            (((GLPair 2).H : Set _) * {δ_c}) := by
        have lhs_eq :
            ({(i₁.out : GL (Fin 2) ℚ) * (HeckeCoset.rep (TDiag b) : GL (Fin 2) ℚ)} : Set _) *
            {(j₁.out : GL (Fin 2) ℚ) * δ_c} * ((GLPair 2).H : Set _) =
            ({(i₁.out : GL (Fin 2) ℚ) * (HeckeCoset.rep (TDiag b) : GL (Fin 2) ℚ)} : Set _) *
              (((GLPair 2).H : Set _) * {δ_c}) := by rw [mul_assoc, h_coset]
        have rhs_eq :
            ({(i₂.out : GL (Fin 2) ℚ) * (HeckeCoset.rep (TDiag b) : GL (Fin 2) ℚ)} : Set _) *
            {(j₁.out : GL (Fin 2) ℚ) * δ_c} * ((GLPair 2).H : Set _) =
            ({(i₂.out : GL (Fin 2) ℚ) * (HeckeCoset.rep (TDiag b) : GL (Fin 2) ℚ)} : Set _) *
              (((GLPair 2).H : Set _) * {δ_c}) := by rw [mul_assoc, h_coset]
        rw [← lhs_eq, ← rhs_eq]; exact h₁.trans h₂.symm
      rw [← mul_assoc, ← mul_assoc] at h12'
      exact HeckeRing.mul_singleton_right_cancel δ_c _ _ h12'
    subst hi; rfl
  have h_pos : 0 < HeckeRing.heckeMultiplicity (GLPair 2) (HeckeCoset.rep (TDiag b))
      (HeckeCoset.rep (TDiag (fun _ : Fin 2 => c)))
      (HeckeCoset.rep (TDiag (b * (fun _ => c)))) :=
    HeckeRing.heckeMultiplicity_pos_of_mem (GLPair 2) _ _ _
      (mem_mulSupport_right_scalar b hb_pos hb c hc hbc)
  exact HeckeRing.heckeMultiplicity_eq_one_of_le_one_and_pos (GLPair 2) _ _ _ h_le h_pos

private lemma heckeMultiplicity_right_scalar_eq_zero (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) (hbc : DivChain 2 (b * (fun _ => c)))
    (A : HeckeCoset (GLPair 2)) (hA : A ≠ TDiag (b * (fun _ : Fin 2 => c))) :
    HeckeRing.heckeMultiplicity (GLPair 2) (HeckeCoset.rep (TDiag b))
      (HeckeCoset.rep (TDiag (fun _ : Fin 2 => c))) (HeckeCoset.rep A) = 0 := by
  apply HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport; intro h_mem
  simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and] at h_mem
  exact h_mem.elim fun ⟨i, j⟩ heq =>
    hA (heq.symm.trans (mulMap_right_scalar_eq b hb_pos hb c hc hbc (i, j)))

/-- Multiplication by a scalar diagonal element: `TElem(b) * TElem(c,c) = TElem(b * c)`. -/
theorem T_elem_mul_scalar (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain 2 b) (c : ℕ) (hc : 0 < c) :
    TElem b * TElem (fun _ : Fin 2 => c) = TElem (b * (fun _ => c)) := by
  set D_b := TDiag b; set D_c := TDiag (fun _ : Fin 2 => c)
  set D_bc := TDiag (b * (fun _ : Fin 2 => c))
  have hbc := DivChain_mul 2 b (fun _ => c) hb (divChain_const 2 c)
  change TSingle (GLPair 2) ℤ D_b 1 * TSingle (GLPair 2) ℤ D_c 1 =
    TSingle (GLPair 2) ℤ D_bc 1
  rw [HeckeRing.T_single_one_mul_T_single_one]; apply Finsupp.ext; intro A
  simp only [HeckeRing.m, Finsupp.coe_mk, HeckeRing.TSingle]
  by_cases h1 : A = D_bc
  · subst h1; norm_num [Finsupp.single_apply]
    exact heckeMultiplicity_right_scalar_eq_one b hb_pos hb c hc hbc D_b rfl D_c rfl D_bc rfl
  · norm_num [Finsupp.single_apply, h1]
    exact heckeMultiplicity_right_scalar_eq_zero b hb_pos hb c hc hbc A h1

/-- `T(p,p)` commutes with every diagonal element `TElem(a)` for `p` prime. -/
lemma T_pp_comm_T_elem (p : ℕ) (hp : p.Prime) (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha : DivChain 2 a) : TPp p * TElem a = TElem a * TPp p := by
  rw [T_pp_of_pos p hp, T_diag_scalar_mul 2 p hp.pos a ha_pos ha,
    T_elem_mul_scalar a ha_pos ha p hp.pos]
  exact (T_elem_congr_diag 2 (diagMul_scalar_comm a p)).symm

include hp in
/-- `T(p,p)^i = TElem(p^i, p^i)`: the `i`-th power of the scalar double coset. -/
lemma T_pp_pow (i : ℕ) : TPp p ^ i = TElem (fun _ : Fin 2 => p ^ i) := by
  induction i with
  | zero =>
    simp only [pow_zero]; symm
    exact (T_elem_congr_diag 2 (funext fun _ => by simp)).trans T_elem_ones_eq
  | succ i ih =>
    rw [pow_succ', ih, T_pp_of_pos p hp, T_diag_scalar_mul 2 p hp.pos (fun _ => p ^ i)
      (fun _ => pow_pos hp.pos i) (divChain_const 2 _)]
    exact T_elem_congr_diag 2 (funext fun _ => by simp [Pi.mul_apply, pow_succ, mul_comm])

/-- Expand `T(p^k)` as a sum over divisor pairs with non-zero `TAd` terms. -/
lemma T_sum_ppow_expansion (k : ℕ) :
    TSum ⟨p ^ k, pow_pos hp.pos k⟩ =
    ∑ i ∈ Finset.range (k / 2 + 1), TAd (p ^ i) (p ^ (k - i)) := by
  change ∑ a ∈ (p ^ k).divisors, TAd a (p ^ k / a) = _
  rw [Nat.sum_divisors_prime_pow hp]
  have h_div : ∀ j ∈ Finset.range (k + 1),
      TAd (p ^ j) (p ^ k / p ^ j) = TAd (p ^ j) (p ^ (k - j)) :=
    fun j hj => by rw [Finset.mem_range] at hj; congr 1; exact Nat.pow_div (by omega) hp.pos
  rw [Finset.sum_congr rfl h_div]
  exact (Finset.sum_subset (Finset.range_mono (by omega)) (fun j hj hnj => by
    simp only [Finset.mem_range] at hj hnj; apply T_ad_eq_zero; push Not; intro _ _
    exact fun hdvd => absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd)
      (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (by omega))))).symm

end Structural

end HeckeRing.GL2
