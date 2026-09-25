/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.BranchTrace
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.MixedCount
import LeanPool.RegtsSevenster.RS.Classical.SymFun.CoeffSplit
import LeanPool.RegtsSevenster.RS.Classical.SymFun.PieriChain

/-!
# Positivity of the restriction pairing

The pairing `restrPairing lam mu` is nonzero whenever `lam ≤ mu`,
bridging the combinatorial Pieri chain to the representation-theoretic
branching sandwich.
-/

namespace RS

open Finset MvPolynomial Equiv

-- rowLen vanishes beyond colLen 0
private theorem rowLen_eq_zero_of_ge_colLen (ν : YoungDiagram) {i : ℕ}
    (hi : ν.colLen 0 ≤ i) : ν.rowLen i = 0 := by
  by_contra h
  have hp : 0 < ν.rowLen i := Nat.pos_of_ne_zero h
  have : (i, 0) ∈ ν := by
    rw [YoungDiagram.mem_iff_lt_rowLen]; omega
  have := YoungDiagram.mem_iff_lt_colLen.mp this
  omega

-- Step 1: sum of rowLen over Fin k = card, when k ≥ colLen 0
private theorem sum_rowLen_fin (ν : YoungDiagram) {k : ℕ}
    (hk : ν.colLen 0 ≤ k) :
    ∑ i : Fin k, ν.rowLen (i : ℕ) = ν.card := by
  classical
  rw [card_eq_sum_rowLens]
  rw [Fin.sum_univ_eq_sum_range (fun i => ν.rowLen i)]
  have hrange : ν.rowLens.sum =
      ∑ i ∈ Finset.range (ν.colLen 0), ν.rowLen i := by
    rw [show ν.rowLens = (List.range (ν.colLen 0)).map ν.rowLen from rfl]
    induction ν.colLen 0 with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih]
      simp
  rw [hrange]
  exact (Finset.sum_subset (Finset.range_mono hk)
    (fun i hi hni => by
      rw [Finset.mem_range] at hni; push Not at hni
      exact rowLen_eq_zero_of_ge_colLen ν hni)).symm

-- Step 2: the shifted composition sums to m
private theorem sum_comp_pad {k m : ℕ} (vl : Fin k → ℕ)
    (σ' : Equiv.Perm (Fin k))
    (hg : ∀ i : Fin k, 0 ≤ (vl i : ℤ) + ((σ' i : Fin k) : ℕ) - (i : ℕ))
    (hsum : ∑ i : Fin k, vl i = m) :
    ∑ i : Fin k,
      ((vl i : ℤ) + ((σ' i : Fin k) : ℕ) - (i : ℕ)).toNat = m := by
  have h1 : ((∑ i : Fin k,
      ((vl i : ℤ) + ((σ' i : Fin k) : ℕ) - (i : ℕ)).toNat : ℕ) : ℤ) =
    (m : ℤ) := by
    rw [Nat.cast_sum]
    rw [Finset.sum_congr rfl
      (fun (i : Fin k) (_ : i ∈ Finset.univ) =>
        show ((((vl i : ℤ) + ((σ' i : Fin k) : ℕ) - (i : ℕ)).toNat : ℕ) : ℤ) =
          (vl i : ℤ) + ((σ' i : Fin k) : ℕ) - (i : ℕ) from
        Int.toNat_of_nonneg (hg i))]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [show (∑ i : Fin k, (((σ' i : Fin k) : ℕ) : ℤ)) =
        ∑ i : Fin k, ((i : ℕ) : ℤ) from
      Equiv.sum_comp σ' (fun i : Fin k => ((i : ℕ) : ℤ))]
    rw [add_sub_cancel_right, ← Nat.cast_sum, hsum]
  exact_mod_cast h1

-- The inner sum identity: connects the σ-sum of colourChar products
-- to a polynomial coefficient via pair counting
open scoped Classical in
private theorem inner_sum_eq {m n k : ℕ} (h : m ≤ n)
    (α β : Fin k → ℕ) (hα : ∑ i, α i = n) (hβ : ∑ i, β i = m) :
    (∑ σ : Equiv.Perm (Fin m),
      (colourChar β σ : ℂ) *
        (colourChar α
          (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) : ℂ)) =
    (m.factorial : ℂ) *
      ((∏ i, hSub (Finset.univ : Finset (Fin k)) (β i)) *
          (∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ (n - m)).coeff (∑ a,
              Finsupp.single a (α a)) := by
  set r := n - m
  set P := ∏ i, hSub (Finset.univ : Finset (Fin k)) (β i)
  set Q := (∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ r
  set W := Fintype.piFinset (fun _ : Fin k => Finset.range (n + 1))
  -- ═══════ STAGE 1: EXPAND THE CHARACTER ALONG THE EMBEDDING ═══════
  have hstep1 : ∀ (σ : Equiv.Perm (Fin m)),
      (colourChar β σ : ℂ) *
        (colourChar α (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) : ℂ) =
      ∑ w ∈ W,
        (if ∀ a, w a ≤ α a then
          (colourChar β σ : ℂ) * (colourChar (fun a => α a - w a) σ : ℂ) *
            ((Finset.univ.filter
              (fun t : ({i : Fin n // m ≤ (i : ℕ)} → Fin k) =>
                ∀ a, (Finset.univ.filter (fun i => t i = a)).card = w a)).card :
                  ℂ)
          else 0) := by
    intro σ
    have hcve := colourChar_viaEmbedding h σ α
    rw [show (colourChar α (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) : ℂ)
      =
      (∑ w ∈ W, (if ∀ a, w a ≤ α a then
        colourChar (fun a => α a - w a) σ *
          (Finset.univ.filter
            (fun t : ({i : Fin n // m ≤ (i : ℕ)} → Fin k) =>
              ∀ a, (Finset.univ.filter (fun i => t i = a)).card = w a)).card
        else 0) : ℂ) from by rw [hcve]; push_cast; rfl]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs with hw
    · ring
    · simp
  rw [Finset.sum_congr rfl fun σ _ => hstep1 σ]
  rw [Finset.sum_comm]
  -- ═══════ STAGE 2: PULL OUT THE TAIL COUNT, ONE `w` AT A TIME ═══════
  have hstep2 : ∀ w ∈ W,
      (∑ σ : Equiv.Perm (Fin m),
        (if ∀ a, w a ≤ α a then
          (colourChar β σ : ℂ) * (colourChar (fun a => α a - w a) σ : ℂ) *
            ((Finset.univ.filter
              (fun t : ({i : Fin n // m ≤ (i : ℕ)} → Fin k) =>
                ∀ a, (Finset.univ.filter (fun i => t i = a)).card = w a)).card :
                  ℂ)
          else 0)) =
      (if ∀ a, w a ≤ α a then
        (m.factorial : ℂ) *
          (Fintype.card {W' : ∀ a : Fin k, Sym (Fin k) (β a) //
            ∀ b : Fin k, (∑ a : Fin k, (W' a).1.count b) =
              α b - w b} : ℂ) *
          ((Finset.univ.filter
            (fun t : ({i : Fin n // m ≤ (i : ℕ)} → Fin k) =>
              ∀ a, (Finset.univ.filter (fun i => t i = a)).card = w a)).card :
                ℂ)
        else 0) := by
    intro w _
    by_cases hw : ∀ a, w a ≤ α a
    · rw [Finset.sum_congr rfl fun σ _ => by rw [ite_eq_left hw]]
      rw [← Finset.sum_mul]
      rw [ite_eq_left hw]
      congr 1
      -- ∑_σ cc(β,σ) * cc(α-w,σ) as ℂ = (∑_σ cc(β,σ)*cc(α-w,σ) as ℕ) as ℂ
      -- = (∑_σ |pairs|) as ℂ  via colourChar_mul
      -- = (m! * |Sym pairs|) as ℂ  via pair_count_sum
      -- = m! as ℂ * |tuples| as ℂ  via pair_tuple_card
      -- Work in ℕ: ∑ cc*cc = ∑ |pairs| = m! * |Sym| = m! * |tuples|
      have hnat : (∑ σ : Equiv.Perm (Fin m),
          colourChar β σ * colourChar (fun a => α a - w a) σ) =
        m.factorial * Fintype.card {W' : ∀ a : Fin k, Sym (Fin k) (β a) //
          ∀ b : Fin k, (∑ a : Fin k, (W' a).1.count b) = α b - w b} := by
        rw [Finset.sum_congr rfl fun σ _ => colourChar_mul β _ σ]
        rw [pair_count_sum β (fun a => α a - w a)]
        rw [pair_tuple_card β (fun a => α a - w a) hβ]
      -- Cast to ℂ
      exact_mod_cast hnat
    · rw [ite_eq_right hw, Finset.sum_eq_zero fun σ _ => by rw [ite_eq_right hw]]
  rw [Finset.sum_congr rfl hstep2]
  -- ═══════ STAGE 3: FACTOR OUT `m!` ═══════
  rw [show ∑ w ∈ W,
      (if ∀ a, w a ≤ α a then
        (m.factorial : ℂ) *
          (Fintype.card {W' : ∀ a : Fin k, Sym (Fin k) (β a) //
            ∀ b : Fin k, (∑ a : Fin k, (W' a).1.count b) = α b - w b} : ℂ) *
          ((Finset.univ.filter
            (fun t : ({i : Fin n // m ≤ (i : ℕ)} → Fin k) =>
              ∀ a, (Finset.univ.filter (fun i => t i = a)).card = w a)).card :
                ℂ)
        else 0) =
    (m.factorial : ℂ) * ∑ w ∈ W,
      (if ∀ a, w a ≤ α a then
        (Fintype.card {W' : ∀ a : Fin k, Sym (Fin k) (β a) //
          ∀ b : Fin k, (∑ a : Fin k, (W' a).1.count b) = α b - w b} : ℂ) *
        ((Finset.univ.filter
          (fun t : ({i : Fin n // m ≤ (i : ℕ)} → Fin k) =>
            ∀ a, (Finset.univ.filter (fun i => t i = a)).card = w a)).card : ℂ)
        else 0) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> ring]
  congr 1
  -- ═══════ ASSEMBLY: MATCH EACH `w`-TERM TO `coeff_mul_split` ═══════
  rw [coeff_mul_split P Q α n (fun a => by
    have := hα ▸ Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ a); exact this)]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ a, w a ≤ α a
  · rw [ite_eq_left hw, ite_eq_left hw]
    -- coeff(α-w)(P) = |tuples|  via coeff_hSub_prod
    -- coeff(w)(Q) = |tail functions|  via coeff_p1_pow
    congr 1
    · rw [coeff_hSub_prod]
      exact_mod_cast Fintype.card_congr
        (Equiv.subtypeEquivRight fun W' => by
          constructor
          · intro hW j; rw [sum_single_apply]; exact hW j
          · intro hW j; have := hW j; rw [sum_single_apply] at this; exact this)
    · -- coeff(w)(Q) = |tail functions| via coeff_p1_pow
      dsimp only [Q]
      rw [show r = Fintype.card {i : Fin n // m ≤ (i : ℕ)} from
        (card_tail h).symm, coeff_p1_pow]
      simp_rw [sum_single_apply]
      norm_cast
      convert rfl using 5
  · rw [ite_eq_right hw, ite_eq_right hw]

-- Coefficient of w in (jtMat v).det * Q: signed guarded sum with extra Q
open scoped Classical in
private theorem coeff_det_jtMat_mul {k : ℕ}
    (v : Fin k → ℕ) (Q : MvPolynomial (Fin k) ℂ) (w : Fin k →₀ ℕ) :
    ((jtMat v).det * Q).coeff w =
      ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (if ∀ i : Fin k,
              0 ≤ (v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
            then ((∏ i, hSub (Finset.univ : Finset (Fin k))
                (((v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)).toNat)) * Q).coeff w
            else 0) := by
  rw [det_jtMat_expand]
  rw [Finset.sum_congr rfl
    (fun (σ : Equiv.Perm (Fin k)) (_ : σ ∈ Finset.univ) => by
      rw [jt_term_guard v σ])]
  rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl
    (fun (σ : Equiv.Perm (Fin k)) (_ : σ ∈ Finset.univ) => by
      rw [mul_assoc])]
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin k) ℂ) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) from by simp,
    MvPolynomial.coeff_C_mul]
  by_cases hp : ∀ i : Fin k,
      0 ≤ (v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp, zero_mul, AddMonoidAlgebra.coeff_zero]
    rfl

-- The main algebraic reduction
open scoped Classical in
private theorem pairing_eq_factorial_coeff
    (Hpad : ∀ (μ : YoungDiagram) {k : ℕ}
      (_hk : μ.rowLens.length ≤ k) (π : Equiv.Perm (Fin μ.card)),
      jtChar μ π =
        ∑ σ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (if ∀ i : Fin k,
                0 ≤ (μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
              then (colourChar
                (fun i : Fin k =>
                  ((μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) -
                    (i : ℕ)).toNat) π : ℂ)
              else 0))
    (lam mu : YoungDiagram) (_hle : lam ≤ mu)
    (h : lam.card ≤ mu.card)
    {k : ℕ} {m : ℕ} {n : ℕ} {r : ℕ}
    (_hk_eq : k = mu.rowLens.length) (hm_eq : m = lam.card)
    (hn_eq : n = mu.card) (hr_eq : r = n - m)
    (hkl : lam.rowLens.length ≤ k) (hkm : mu.rowLens.length ≤ k)
    (_hk_col_lam : lam.colLen 0 ≤ k) (_hk_col_mu : mu.colLen 0 ≤ k)
    (hsum_lam : ∑ i : Fin k, lam.rowLen (i : ℕ) = m)
    (hsum_mu : ∑ i : Fin k, mu.rowLen (i : ℕ) = n) :
    restrPairing lam mu h =
      (m.factorial : ℂ) *
        ((∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ r *
            altDet (eVec lam k)).coeff (∑ i : Fin k, Finsupp.single i (eVec mu k i)) := by
  classical
  set Q := (∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ r
  set vl : Fin k → ℕ := fun i => lam.rowLen (i : ℕ) with hvl_def
  set vm : Fin k → ℕ := fun i => mu.rowLen (i : ℕ) with hvm_def
  -- ═══════ SETUP: THE SHIFTED COMPOSITIONS AND THEIR GUARDS ═══════
  let β (σ' : Equiv.Perm (Fin k)) (i : Fin k) :=
    ((vl i : ℤ) + ((σ' i : Fin k) : ℕ) - (i : ℕ)).toNat
  let α (τ : Equiv.Perm (Fin k)) (a : Fin k) :=
    ((vm a : ℤ) + ((τ a : Fin k) : ℕ) - (a : ℕ)).toNat
  let guard_lam (σ' : Equiv.Perm (Fin k)) :=
    ∀ i : Fin k, 0 ≤ (vl i : ℤ) + ((σ' i : Fin k) : ℕ) - (i : ℕ)
  let guard_mu (τ : Equiv.Perm (Fin k)) :=
    ∀ i : Fin k, 0 ≤ (vm i : ℤ) + ((τ i : Fin k) : ℕ) - (i : ℕ)
  -- ═══════ STAGE 1: THE COEFFICIENT AS A DOUBLE SUM ═══════
  have rhs_chain :
      (Q * altDet (eVec lam k)).coeff (∑ i : Fin k, Finsupp.single i (eVec mu k i)) =
      ∑ τ : Equiv.Perm (Fin k), ∑ σ' : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign σ' : ℤ) : ℂ) *
          (if guard_mu τ ∧ guard_lam σ'
            then ((∏ i, hSub (Finset.univ : Finset (Fin k)) (β σ' i)) * Q).coeff (∑ a,
                Finsupp.single a (α τ a))
            else 0) := by
    -- eVec finsupp = diagExp vm
    have heVec : (∑ i : Fin k, Finsupp.single i (eVec mu k i)) =
        diagExp vm := by
      ext j; rw [sum_single_apply, diagExp_apply]; rfl
    -- altDet = powMat.det
    have haltDet : altDet (eVec lam k) = (powMat vl).det := rfl
    rw [heVec, show Q * altDet (eVec lam k) =
      ((jtMat vl).det * Q) * (powMat (fun _ : Fin k => 0)).det from by
      rw [haltDet, bialternant]; ring]
    rw [coeff_mul_alternant]
    refine Finset.sum_congr rfl fun τ _ => ?_
    by_cases hτ : stairShift τ ≤ diagExp vm
    · rw [ite_eq_left hτ, coeff_det_jtMat_mul, Finset.mul_sum]
      have hguard_mu : guard_mu τ := (stair_guard_iff vm τ).mp hτ
      refine Finset.sum_congr rfl fun σ' _ => ?_
      by_cases hσ : guard_lam σ'
      · have hmargin : diagExp vm - stairShift τ =
            ∑ a, Finsupp.single a (α τ a) := by
          ext j; rw [sum_single_apply]; exact stair_margin_eq vm τ hτ j
        rw [mul_assoc, ite_eq_left hσ, ite_eq_left ⟨hguard_mu, hσ⟩, hmargin]
      · rw [mul_assoc, ite_eq_right hσ, ite_eq_right (fun ⟨_, h⟩ => hσ h), mul_zero]
    · rw [ite_eq_right hτ]
      have hguard_mu_neg : ¬ guard_mu τ := fun h =>
        hτ ((stair_guard_iff vm τ).mpr h)
      have hsum_zero : (∑ σ' : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign σ' : ℤ) : ℂ) *
            (if guard_mu τ ∧ guard_lam σ'
              then ((∏ i, hSub (Finset.univ : Finset (Fin k)) (β σ' i)) * Q).coeff (∑ a,
                  Finsupp.single a (α τ a))
              else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro σ' _
        rw [ite_eq_right (fun ⟨h, _⟩ => hguard_mu_neg h)]; ring
      rw [hsum_zero, mul_zero]
  -- ═══════ STAGE 2: THE PAIRING AS `m!` TIMES THAT SUM ═══════
  have lhs_chain :
      restrPairing lam mu h =
      (m.factorial : ℂ) *
        ∑ σ' : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ' : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
            (if guard_lam σ' ∧ guard_mu τ
              then ((∏ i, hSub (Finset.univ : Finset (Fin k)) (β σ' i)) * Q).coeff (∑ a,
                  Finsupp.single a (α τ a))
              else 0) := by
    -- Expand restrPairing
    unfold restrPairing
    -- Apply Hpad
    rw [Finset.sum_congr rfl fun π _ => by
      rw [Hpad lam hkl π, Hpad mu hkm
        (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) π)]]
    -- Expand products (controlled order: sum_mul first so σ_lam is outer)
    conv_lhs => simp only [Finset.sum_mul]
    conv_lhs => simp only [Finset.mul_sum]
    -- Distribute m! into the sums on the RHS
    rw [Finset.mul_sum]
    -- Swap LHS: ∑ π σ_lam → ∑ σ_lam π (σ' = λ-perm)
    conv_lhs => rw [Finset.sum_comm]
    -- Push m! into inner sum
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    -- σ' is the λ permutation; swap inner: ∑ π σ_mu → ∑ σ_mu π (τ = μ-perm)
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    -- Per (σ', τ): show ∑ π, f(π) = m! * g
    by_cases hσ : guard_lam σ'
    · have hσ_exp : ∀ i : Fin k,
          (0 : ℤ) ≤ ↑(lam.rowLen ↑i) + ↑↑(σ' i) - ↑↑i := hσ
      by_cases hτ : guard_mu τ
      · have hτ_exp : ∀ i : Fin k,
            (0 : ℤ) ≤ ↑(mu.rowLen ↑i) + ↑↑(τ i) - ↑↑i := hτ
        -- Both guards hold: apply inner_sum_eq
        simp_rw [ite_eq_left hσ_exp, ite_eq_left hτ_exp]
        rw [ite_eq_left ⟨hσ, hτ⟩]
        -- Rearrange: (sign * cc) * (sign * cc') → (sign * sign) * (cc * cc')
        conv_lhs => arg 2; ext π; rw [mul_mul_mul_comm]
        rw [← Finset.mul_sum]
        -- Use h : lam.card ≤ mu.card so inner_sum_eq matches goal's Fin type
        have h_inner := inner_sum_eq h (α τ) (β σ')
          ((sum_comp_pad vm τ hτ hsum_mu).trans hn_eq)
          ((sum_comp_pad vl σ' hσ hsum_lam).trans hm_eq)
        -- Align factorial and exponent to match m.factorial and Q
        rw [show (lam.card).factorial = m.factorial from by rw [hm_eq]]
          at h_inner
        rw [show mu.card - lam.card = r from by omega] at h_inner
        -- Fold (∑ l, X l) ^ r to Q so it matches goal syntactically
        rw [show (∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ r = Q from rfl]
          at h_inner
        -- h_inner: S = m! * C  (with Q, matching goal)
        -- goal: a * S = m! * (a * C)  where a = sign * sign
        exact (congr_arg
          (((Equiv.Perm.sign σ' : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) * ·)
          h_inner).trans (by ring)
      · -- guard_mu fails
        have hτ_exp : ¬ ∀ i : Fin k,
            (0 : ℤ) ≤ ↑(mu.rowLen ↑i) + ↑↑(τ i) - ↑↑i := hτ
        simp_rw [ite_eq_left hσ_exp, ite_eq_right hτ_exp]
        rw [ite_eq_right (fun ⟨_, h⟩ => hτ h)]
        simp only [mul_zero, Finset.sum_const_zero]
    · -- guard_lam fails
      have hσ_exp : ¬ ∀ i : Fin k,
          (0 : ℤ) ≤ ↑(lam.rowLen ↑i) + ↑↑(σ' i) - ↑↑i := hσ
      simp_rw [ite_eq_right hσ_exp]
      rw [ite_eq_right (fun ⟨h, _⟩ => hσ h)]
      simp only [mul_zero, zero_mul, Finset.sum_const_zero]
  -- ═══════ ASSEMBLY ═══════
  rw [lhs_chain]
  congr 1
  rw [rhs_chain]
  -- Swap sum order: ∑ σ' τ = ∑ τ σ'
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  refine Finset.sum_congr rfl fun σ' _ => ?_
  -- Match: sign order and guard order are commutative
  rw [show ((Equiv.Perm.sign σ' : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) =
    ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign σ' : ℤ) : ℂ) from mul_comm
      _ _]
  congr 1
  exact if_congr And.comm rfl rfl

open scoped Classical in
/-- **The restriction pairing is nonzero** whenever one diagram
contains the other, by the Pieri chain's positivity. -/
theorem restrPairing_ne_zero
    (Hpad : ∀ (μ : YoungDiagram) {k : ℕ}
      (_hk : μ.rowLens.length ≤ k) (π : Equiv.Perm (Fin μ.card)),
      jtChar μ π =
        ∑ σ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (if ∀ i : Fin k,
                0 ≤ (μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
              then (colourChar
                (fun i : Fin k =>
                  ((μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) -
                    (i : ℕ)).toNat) π : ℂ)
              else 0))
    (lam mu : YoungDiagram) (hle : lam ≤ mu)
    (h : lam.card ≤ mu.card) :
    restrPairing lam mu h ≠ 0 := by
  classical
  set k := mu.rowLens.length with hk_def
  set m := lam.card with hm_def
  set n := mu.card with hn_def
  set r := n - m with hr_def
  set vl : Fin k → ℕ := fun i => lam.rowLen (i : ℕ) with hvl_def
  set vm : Fin k → ℕ := fun i => mu.rowLen (i : ℕ) with hvm_def
  have hcol_mono : lam.colLen 0 ≤ mu.colLen 0 := by
    by_contra hc
    push Not at hc
    have hmem : (mu.colLen 0, 0) ∈ lam := by
      rw [YoungDiagram.mem_iff_lt_colLen]; omega
    have := hle hmem
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this) (by omega)
  have hkl : lam.rowLens.length ≤ k := by
    rw [hk_def, YoungDiagram.length_rowLens, YoungDiagram.length_rowLens]
    exact hcol_mono
  have hkm : mu.rowLens.length ≤ k := le_refl _
  have hk_col_lam : lam.colLen 0 ≤ k := by
    rw [hk_def, YoungDiagram.length_rowLens]; exact hcol_mono
  have hk_col_mu : mu.colLen 0 ≤ k := by
    rw [hk_def, YoungDiagram.length_rowLens]
  have hsum_lam : ∑ i : Fin k, vl i = m := sum_rowLen_fin lam hk_col_lam
  have hsum_mu : ∑ i : Fin k, vm i = n := sum_rowLen_fin mu hk_col_mu
  suffices key : ∃ N : ℕ, 0 < N ∧
      restrPairing lam mu h = (m.factorial : ℂ) * (N : ℂ) by
    obtain ⟨N, hN_pos, hN_eq⟩ := key
    rw [hN_eq]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
      (Nat.cast_ne_zero.mpr (by omega))
  have hchain := coeff_chain_pos lam mu hle r (by omega) hk_col_mu
  obtain ⟨N, hN_pos, hN_eq⟩ := hchain
  refine ⟨N, hN_pos, ?_⟩
  rw [pairing_eq_factorial_coeff Hpad lam mu hle h
    hk_def hm_def hn_def hr_def hkl hkm
    hk_col_lam hk_col_mu hsum_lam hsum_mu, hN_eq]

end RS
