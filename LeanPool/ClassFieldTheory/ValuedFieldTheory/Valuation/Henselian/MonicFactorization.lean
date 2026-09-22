/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.PrimitiveFactorization
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Polynomial.Vieta
/-!
# Monic Hensel factor lifting

This file isolates the algebraic condition used in the factor-lifting criterion.
The condition is the exact condition: a monic polynomial whose
reduction is a product of relatively prime monic polynomials has monic factors
with exactly those reductions.
-/

noncomputable section

open Polynomial

namespace DiscreteValuationField
open ValuationTheory.DiscreteValuationField

universe u

/-- Multiplicative nonarchimedean Vieta bound.  If every entry of `s` has
valuation at most `B`, with `B ≥ 1`, every coefficient of the corresponding
monic product is bounded by `B ^ |s|`. -/
theorem valuation_coeff_prod_X_sub_C_le_pow_card
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (B : Γ) (hB : 1 ≤ B) (s : Multiset L)
    (hs : ∀ α ∈ s, w α ≤ B) (i : ℕ) :
    w (((s.map (fun α => Polynomial.X - Polynomial.C α)).prod).coeff i) ≤
      B ^ s.card := by
  induction s using Multiset.induction_on generalizing i with
  | empty =>
      cases i <;> simp [Polynomial.coeff_one]
  | @cons α s ih =>
      have hα : w α ≤ B := hs α (by simp)
      have hs' : ∀ β ∈ s, w β ≤ B := by
        intro β hβ
        exact hs β (by simp [hβ])
      have hpow_step : B ^ s.card ≤ B ^ (s.card + 1) := by
        rw [pow_succ]
        calc
          B ^ s.card = B ^ s.card * 1 := (mul_one _).symm
          _ ≤ B ^ s.card * B := by
            simpa [mul_comm] using mul_le_mul_right hB (B ^ s.card)
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
      cases i with
      | zero =>
          have hq := ih hs' 0
          calc
            w (((Polynomial.X - Polynomial.C α) *
                (s.map (fun β => Polynomial.X - Polynomial.C β)).prod).coeff 0) =
                w α *
                  w (((s.map (fun β =>
                    Polynomial.X - Polynomial.C β)).prod).coeff 0) := by
              simp [Polynomial.coeff_zero_eq_eval_zero]
            _ ≤ B * B ^ s.card := mul_le_mul' hα hq
            _ = B ^ (s.card + 1) := by
              rw [pow_succ]
              ac_rfl
      | succ j =>
          rw [Polynomial.coeff_X_sub_C_mul]
          have hqj := ih hs' j
          have hqsucc := ih hs' (j + 1)
          have hterm :
              w (α * ((s.map (fun β =>
                Polynomial.X - Polynomial.C β)).prod).coeff (j + 1)) ≤
                B ^ (s.card + 1) := by
            rw [w.map_mul]
            calc
              w α * w (((s.map (fun β =>
                  Polynomial.X - Polynomial.C β)).prod).coeff (j + 1)) ≤
                  B * B ^ s.card := mul_le_mul' hα hqsucc
              _ = B ^ (s.card + 1) := by
                rw [pow_succ]
                ac_rfl
          calc
            w (((s.map (fun β => Polynomial.X - Polynomial.C β)).prod).coeff j -
                α * ((s.map (fun β =>
                  Polynomial.X - Polynomial.C β)).prod).coeff (j + 1)) ≤
                max
                  (w (((s.map (fun β =>
                    Polynomial.X - Polynomial.C β)).prod).coeff j))
                  (w (α * ((s.map (fun β =>
                    Polynomial.X - Polynomial.C β)).prod).coeff (j + 1))) := by
              exact
                w.map_sub
                  (((s.map (fun β =>
                    Polynomial.X - Polynomial.C β)).prod).coeff j)
                  (α * ((s.map (fun β =>
                    Polynomial.X - Polynomial.C β)).prod).coeff (j + 1))
            _ ≤ B ^ (s.card + 1) :=
              max_le (hqj.trans hpow_step) hterm

/-- If all elements of a multiset have valuation `t`, the valuation of their
product is `t` to the cardinality. -/
theorem valuation_multiset_prod_eq_pow_card_of_eq
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (t : Γ) (s : Multiset L)
    (hs : ∀ α ∈ s, w α = t) :
    w s.prod = t ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons α s ih =>
      have hα : w α = t := hs α (by simp)
      have hs' : ∀ β ∈ s, w β = t := by
        intro β hβ
        exact hs β (by simp [hβ])
      simp only [Multiset.prod_cons, Multiset.card_cons, w.map_mul,
        hα, ih hs', pow_succ]
      ac_rfl

/-- The elementary-symmetric recursion in a form convenient for valuation
estimates. -/
theorem esymm_cons_succ
    {R : Type*} [CommRing R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons,
    Multiset.map_add, Multiset.sum_add, Multiset.map_map,
    Function.comp_apply, Multiset.prod_cons, Multiset.sum_map_mul_left]

/-- A nonarchimedean bound for elementary symmetric functions. -/
theorem valuation_esymm_le_pow
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (t : Γ) (s : Multiset L)
    (hs : ∀ a ∈ s, w a ≤ t) (n : ℕ) :
    w (s.esymm n) ≤ t ^ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
      cases n with
      | zero =>
          rw [Multiset.esymm, Multiset.powersetCard_zero_left,
            Multiset.map_singleton, Multiset.prod_zero, Multiset.sum_singleton,
            w.map_one, pow_zero]
      | succ n =>
          rw [Multiset.esymm, Multiset.powersetCard_zero_right,
            Multiset.map_zero, Multiset.sum_zero, w.map_zero]
          exact zero_le
  | @cons a s ih =>
      cases n with
      | zero => simp [Multiset.esymm]
      | succ n =>
          rw [show n + 1 = n.succ by rfl, esymm_cons_succ]
          apply le_trans (w.map_add _ _) (max_le ?_ ?_)
          · exact ih (fun b hb => hs b (by simp [hb])) (n + 1)
          · rw [w.map_mul, pow_succ]
            simpa [mul_comm] using
              (mul_le_mul' (hs a (by simp))
                (ih (fun b hb => hs b (by simp [hb])) n))

/-- Strict elementary-symmetric bound when every entry is strictly below
the target value. -/
theorem valuation_esymm_lt_pow
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (t : Γ) (ht : t ≠ 0) (s : Multiset L)
    (hs : ∀ a ∈ s, w a < t) {n : ℕ} (hn : 0 < n) :
    w (s.esymm n) < t ^ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [Multiset.esymm, Multiset.powersetCard_zero_right,
        Multiset.map_zero, Multiset.sum_zero, w.map_zero]
      exact (zero_lt_iff).2 (pow_ne_zero (n + 1) ht)
  | @cons a s ih =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      change w ((a ::ₘ s).esymm (n + 1)) < t ^ (n + 1)
      rw [esymm_cons_succ]
      apply w.map_add_lt
      · exact ih (fun b hb => hs b (by simp [hb])) (Nat.succ_pos n)
      · rw [w.map_mul, pow_succ]
        simpa [mul_comm] using
          (mul_lt_mul_of_nonneg_of_pos (hs a (by simp))
            (valuation_esymm_le_pow w t s
              (fun b hb => (hs b (by simp [hb])).le) n)
            (zero_le : 0 ≤ w a) ((zero_lt_iff).2 (pow_ne_zero n ht)))

/-- If every entry has value at most one and one entry has value below one,
then the product has value below one. -/
theorem valuation_multiset_prod_lt_one_of_mem_lt_one
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (s : Multiset L) {a : L}
    (ha : a ∈ s) (halt : w a < 1)
    (hs : ∀ b ∈ s, w b ≤ 1) :
    w s.prod < 1 := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.prod_cons, w.map_mul]
  have hprodle : ∀ u : Multiset L,
      (∀ b ∈ u, w b ≤ 1) → w u.prod ≤ 1 := by
    intro u hu
    induction u using Multiset.induction_on with
    | empty => simp
    | @cons b u ih =>
        rw [Multiset.prod_cons, w.map_mul]
        simpa using mul_le_mul' (hu b (by simp))
          (ih (fun c hc => hu c (by simp [hc])))
  have htprod : w t.prod ≤ 1 :=
    hprodle t (fun b hb => hs b (by simp [hb]))
  exact mul_lt_one_of_lt_of_le halt htprod

/-- The boundary elementary symmetric function is dominated by the unique
term using all roots of maximal value.  This is the valuation-theoretic
coefficient calculation in Artin's Nart transform. -/
theorem valuation_esymm_eq_pow_card_add_of_eq_of_lt
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (t : Γ) (ht : t ≠ 0)
    (seq slt : Multiset L)
    (hseq : ∀ a ∈ seq, w a = t)
    (hslt : ∀ a ∈ slt, w a < t) :
    w ((seq + slt).esymm seq.card) = t ^ seq.card := by
  have hstrong : ∀ seq : Multiset L,
      (∀ a ∈ seq, w a = t) →
        (w ((seq + slt).esymm seq.card) = t ^ seq.card ∧
          ∀ n, seq.card < n →
            w ((seq + slt).esymm n) < t ^ n) := by
    intro seq
    induction seq using Multiset.induction_on with
    | empty =>
        intro _
        constructor
        · simp [Multiset.esymm]
        · intro n hn
          simpa using valuation_esymm_lt_pow w t ht slt hslt hn
    | @cons a s ih =>
        intro hs
        have ha : w a = t := hs a (by simp)
        have hs' : ∀ b ∈ s, w b = t := by
          intro b hb
          exact hs b (by simp [hb])
        rcases ih hs' with ⟨heq, hlt⟩
        constructor
        · simp only [Multiset.card_cons]
          rw [show (a ::ₘ s) + slt = a ::ₘ (s + slt) by simp,
            esymm_cons_succ]
          have hfirst : w ((s + slt).esymm (s.card + 1)) <
              t ^ (s.card + 1) := hlt _ (Nat.lt_succ_self _)
          have hsecond : w (a * (s + slt).esymm s.card) =
              t ^ (s.card + 1) := by
            rw [w.map_mul, ha, heq, pow_succ]
            ac_rfl
          rw [w.map_add_of_distinct_val (ne_of_lt (hfirst.trans_eq hsecond.symm)),
            hsecond]
          simp [hfirst.le]
        · intro n hn
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
          simp only [Multiset.card_cons, Nat.succ_eq_add_one] at hn
          change w (((a ::ₘ s) + slt).esymm (m + 1)) < t ^ (m + 1)
          rw [show (a ::ₘ s) + slt = a ::ₘ (s + slt) by simp,
            esymm_cons_succ]
          apply w.map_add_lt
          · exact hlt _ (Nat.lt_trans (Nat.lt_succ_self _) hn)
          · rw [w.map_mul, ha, pow_succ]
            conv_rhs => rw [mul_comm]
            exact mul_lt_mul_of_pos_of_nonneg le_rfl (hlt m (by omega))
              ((zero_lt_iff).2 ht) (zero_le : 0 ≤ t ^ m)
  exact (hstrong seq hseq).1

/-- Over a valuation ring, Gauss-primitivity is also detected by nonzero
reduction.  The finite set of nonzero coefficients has a divisibility-minimal
coefficient; if every coefficient reduced to zero, that nonunit would divide
the whole polynomial, contradicting primitivity. -/
theorem residue_ne_zero_of_isPrimitive_valuationSubring
    {K : Type u} [Field K] (V : ValuationSubring K)
    {p : Polynomial V} (hp : p.IsPrimitive) :
    p.map (IsLocalRing.residue V) ≠ 0 := by
  intro hzero
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hp0
  have hs :
      (AlgebraicNumberTheory.Valuations.henselFactorizationTwoPolynomialCoeffFinset p
        0).Nonempty := by
    refine ⟨p.coeff n, ?_⟩
    exact
      AlgebraicNumberTheory.Valuations.henselFactorization_mem_twoPolynomialCoeffFinset_left hn
  have hcoeffMax : ∀ i : ℕ, p.coeff i ∈ IsLocalRing.maximalIdeal V := by
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change IsLocalRing.residue V (p.coeff i) = 0
    rw [← Polynomial.coeff_map, hzero]
    simp
  have hzeroCoeff : ∀ i : ℕ, (0 : Polynomial V).coeff i ∈
      IsLocalRing.maximalIdeal V := by
    intro i
    simp
  rcases
      AlgebraicNumberTheory.Valuations.henselFactorization_exists_coeff_mem_ideal_dvd_all_two_polynomials
        (I := IsLocalRing.maximalIdeal V) hcoeffMax hzeroCoeff hs with
    ⟨π, hπmax, _hπcoeff, hπp, _hπzero⟩
  have hC : Polynomial.C π ∣ p :=
    (Polynomial.C_dvd_iff_dvd_coeff π p).2 hπp
  have hπunit : IsUnit π :=
    (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hp) π hC
  exact (IsLocalRing.mem_maximalIdeal π).mp hπmax hπunit

theorem valuation_coeff_prod_X_sub_C_lt_coeff_zero_of_one_lt
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (s : Multiset L)
    (hs : ∀ α ∈ s, 1 < w α) (j : ℕ) (hj : 0 < j) :
    w (((s.map (fun α => Polynomial.X - Polynomial.C α)).prod).coeff j) <
      w (((s.map (fun α => Polynomial.X - Polynomial.C α)).prod).coeff 0) := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
      simp [Polynomial.coeff_one, Nat.ne_of_gt hj]
  | @cons α s ih =>
      have hα : 1 < w α := hs α (by simp)
      have hs' : ∀ β ∈ s, 1 < w β := by
        intro β hβ
        exact hs β (by simp [hβ])
      let q : Polynomial L :=
        (s.map (fun β => Polynomial.X - Polynomial.C β)).prod
      have hqzero : q.coeff 0 ≠ 0 := by
        have hprod : (s.map fun β => -β).prod ≠ 0 := by
          apply Multiset.prod_ne_zero
          intro hzero
          rcases Multiset.mem_map.mp hzero with ⟨β, hβ, hβzero⟩
          have hβne : β ≠ 0 := by
            intro h
            subst β
            simpa using hs' 0 hβ
          exact hβne (neg_eq_zero.mp hβzero)
        dsimp [q]
        rw [Polynomial.coeff_zero_eq_eval_zero,
          Polynomial.eval_multiset_prod]
        simpa using hprod
      have hqzeroPos : 0 < w (q.coeff 0) :=
        (Valuation.pos_iff w).2 hqzero
      cases j with
      | zero => simp at hj
      | succ k =>
          have hfirst :
              w (q.coeff k) < w α * w (q.coeff 0) := by
            cases k with
            | zero => exact lt_mul_of_one_lt_left hqzeroPos hα
            | succ k =>
                exact (ih hs' (k + 1) (Nat.succ_pos k)).trans
                  (lt_mul_of_one_lt_left hqzeroPos hα)
          have hsecond :
              w (α * q.coeff (k + 1)) <
                w α * w (q.coeff 0) := by
            rw [w.map_mul]
            exact mul_lt_mul_of_pos_left
              (ih hs' (k + 1) (Nat.succ_pos k)) (zero_lt_one.trans hα)
          simp only [Multiset.map_cons, Multiset.prod_cons]
          rw [Polynomial.coeff_X_sub_C_mul]
          have hadd := w.map_add (q.coeff k) (-α * q.coeff (k + 1))
          have hneg : w (-α * q.coeff (k + 1)) =
              w (α * q.coeff (k + 1)) := by simp
          have hcoeff :
              w (q.coeff k - α * q.coeff (k + 1)) <
                w α * w (q.coeff 0) := by
            calc
              w (q.coeff k - α * q.coeff (k + 1)) ≤
                  max (w (q.coeff k))
                    (w (-α * q.coeff (k + 1))) := by
                      simpa [sub_eq_add_neg] using hadd
              _ < w α * w (q.coeff 0) :=
                max_lt hfirst (hneg.trans_lt hsecond)
          simpa [q, Polynomial.coeff_zero_eq_eval_zero, w.map_mul] using hcoeff



theorem residue_root_of_integral_root
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (B : ValuationSubring L)
    [V.valuation.HasExtension B.valuation]
    {Q : Polynomial V} {β : L}
    (hβle : B.valuation β ≤ 1)
    (hroot : ((Q.map V.subtype).map (algebraMap K L)).IsRoot β) :
    ∃ ρ : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField B,
      ((Q.map (IsLocalRing.residue V)).map ρ).IsRoot
        (IsLocalRing.residue B
          (⟨β, (B.valuation_le_one_iff β).1 hβle⟩ : B)) := by
  let ι : V →+* B :=
    { toFun := fun x =>
        ⟨algebraMap K L (x : K),
          (B.valuation_le_one_iff _).1
            ((Valuation.HasExtension.val_map_le_one_iff
              V.valuation B.valuation (x : K)).2
                ((V.valuation_le_one_iff (x : K)).2 x.2))⟩
      map_zero' := by ext; simp
      map_one' := by ext; simp
      map_add' := by intro x y; ext; simp
      map_mul' := by intro x y; ext; simp }
  let : Algebra V B := ι.toAlgebra
  have halg : algebraMap V B = ι := rfl
  let : IsLocalHom (algebraMap V B) :=
    IsLocalHom.mk fun x hx => by
      apply (V.valuation_eq_one_iff x).mpr
      apply (Valuation.HasExtension.val_map_eq_one_iff
        V.valuation B.valuation (x : K)).mp
      exact (B.valuation_eq_one_iff (algebraMap V B x)).mp hx
  let βB : B := ⟨β, (B.valuation_le_one_iff β).1 hβle⟩
  have hrootB : Q.eval₂ (algebraMap V B) βB = 0 := by
    apply B.subtype_injective
    simp only [map_zero]
    rw [Polynomial.eval₂_eq_eval_map]
    rw [← Polynomial.eval₂_at_apply]
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ (B.subtype.comp (algebraMap V B)) β Q = 0
    have hcomp : B.subtype.comp (algebraMap V B) =
        (algebraMap K L).comp V.subtype := by
      ext x
      rfl
    rw [hcomp]
    simpa [Polynomial.eval₂_eq_eval_map, Polynomial.map_map] using hroot
  let ρ : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField B :=
    IsLocalRing.ResidueField.map (algebraMap V B)
  refine ⟨ρ, ?_⟩
  change ((Q.map (IsLocalRing.residue V)).map
      ρ).eval
        (IsLocalRing.residue B βB) = 0
  dsimp [ρ]
  rw [Polynomial.eval_map, Polynomial.eval₂_map]
  rw [IsLocalRing.ResidueField.map_comp_residue]
  rw [← Polynomial.eval₂_map]
  rw [Polynomial.eval₂_at_apply]
  rw [← Polynomial.eval₂_eq_eval_map, hrootB, map_zero]

/-- A split monic polynomial with integral roots, including a unit root and a
strictly small root, lifts to a polynomial whose reduction has both zero and nonzero roots. -/
private theorem exists_monic_residue_polynomial_of_mixed_roots
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (B : ValuationSubring L)
    [V.valuation.HasExtension B.valuation]
    (q : Polynomial K) (hqmonic : q.Monic) (hqirr : Irreducible q)
    (hqsplit : (q.map (algebraMap K L)).Splits)
    (z zγ : L) (hzval : B.valuation z = 1) (hzγval : B.valuation zγ < 1)
    (hqz : (q.map (algebraMap K L)).IsRoot z)
    (hqzγ : (q.map (algebraMap K L)).IsRoot zγ)
    (hqrootsBound : ∀ δ ∈ (q.map (algebraMap K L)).roots, B.valuation δ ≤ 1) :
    ∃ Q : Polynomial V,
      Q.Monic ∧ Irreducible (Q.map V.subtype) ∧
        (Q.map (IsLocalRing.residue V)).coeff 0 = 0 ∧
          ∃ (ρ : IsLocalRing.ResidueField V →+*
              IsLocalRing.ResidueField B)
            (b : IsLocalRing.ResidueField B),
            b ≠ 0 ∧ ((Q.map (IsLocalRing.residue V)).map ρ).IsRoot b := by
  classical
  let qroots : Multiset L := (q.map (algebraMap K L)).roots
  have hqmap0 : q.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).2 hqirr.ne_zero
  have hqprod : q.map (algebraMap K L) =
      (qroots.map (fun x => Polynomial.X - Polynomial.C x)).prod := by
    calc
      q.map (algebraMap K L) =
          Polynomial.C (q.map (algebraMap K L)).leadingCoeff *
            (qroots.map (fun x => Polynomial.X - Polynomial.C x)).prod :=
        hqsplit.eq_prod_roots
      _ = (qroots.map (fun x => Polynomial.X - Polynomial.C x)).prod := by
        rw [(hqmonic.map (algebraMap K L))]
        simp
  have hqcoeffTarget : ∀ i : ℕ,
      B.valuation (algebraMap K L (q.coeff i)) ≤ 1 := by
    intro i
    have hbound := valuation_coeff_prod_X_sub_C_le_pow_card
      B.valuation 1 le_rfl qroots hqrootsBound i
    rw [one_pow] at hbound
    calc
      B.valuation (algebraMap K L (q.coeff i)) =
          B.valuation ((q.map (algebraMap K L)).coeff i) := by
        rw [Polynomial.coeff_map]
      _ = B.valuation
          ((qroots.map (fun x => Polynomial.X - Polynomial.C x)).prod.coeff i) := by
        rw [hqprod]
      _ ≤ 1 := hbound
  have hqcoeffBase : ∀ i : ℕ, V.valuation (q.coeff i) ≤ 1 := by
    intro i
    exact (Valuation.HasExtension.val_map_le_one_iff
      V.valuation B.valuation (q.coeff i)).mp (hqcoeffTarget i)
  have hqlifts : q ∈ Polynomial.lifts V.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨q.coeff i,
      (V.valuation_le_one_iff (q.coeff i)).1 (hqcoeffBase i)⟩, rfl⟩
  rcases Polynomial.lifts_and_natDegree_eq_and_monic
      (f := V.subtype) hqlifts hqmonic with
    ⟨Q, hQmap, _hQdegree, hQmonic⟩
  have hQirr : Irreducible (Q.map V.subtype) := by
    rw [hQmap]
    exact hqirr
  have hzmem : z ∈ qroots := (Polynomial.mem_roots hqmap0).2 hqz
  have hzγmem : zγ ∈ qroots := (Polynomial.mem_roots hqmap0).2 hqzγ
  have hqconstTarget : B.valuation (algebraMap K L (q.coeff 0)) < 1 := by
    have hprodlt := valuation_multiset_prod_lt_one_of_mem_lt_one
      B.valuation qroots hzγmem hzγval hqrootsBound
    have hconst := hqsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
    have hlead : (q.map (algebraMap K L)).leadingCoeff = 1 :=
      hqmonic.map (algebraMap K L)
    calc
      B.valuation (algebraMap K L (q.coeff 0)) =
          B.valuation ((q.map (algebraMap K L)).coeff 0) := by
        rw [Polynomial.coeff_map]
      _ = B.valuation
          (((-1) ^ (q.map (algebraMap K L)).natDegree) *
            (q.map (algebraMap K L)).leadingCoeff * qroots.prod) := by
        rw [hconst]
      _ = B.valuation qroots.prod := by
        rw [hlead]
        simp
      _ < 1 := hprodlt
  have hqconstBase : V.valuation (q.coeff 0) < 1 :=
    (Valuation.HasExtension.val_map_lt_one_iff
      V.valuation B.valuation (q.coeff 0)).mp hqconstTarget
  have hQconstMax : Q.coeff 0 ∈ IsLocalRing.maximalIdeal V := by
    apply (V.valuation_lt_one_iff (Q.coeff 0)).mpr
    have hcoeff := congrArg (fun f : Polynomial K => f.coeff 0) hQmap
    change (Q.map V.subtype).coeff 0 = q.coeff 0 at hcoeff
    rw [Polynomial.coeff_map] at hcoeff
    change (Q.coeff 0 : K) = q.coeff 0 at hcoeff
    rw [hcoeff]
    exact hqconstBase
  have hQbarConst : (Q.map (IsLocalRing.residue V)).coeff 0 = 0 := by
    rw [Polynomial.coeff_map]
    exact (IsLocalRing.residue_eq_zero_iff (Q.coeff 0)).2 hQconstMax
  have hzle : B.valuation z ≤ 1 := hzval.le
  have hrootQ : ((Q.map V.subtype).map (algebraMap K L)).IsRoot z := by
    rw [hQmap]
    exact hqz
  obtain ⟨ρ, hrootBar⟩ := residue_root_of_integral_root
    V B hzle hrootQ
  let zB : B := ⟨z, (B.valuation_le_one_iff z).1 hzle⟩
  let zbar : IsLocalRing.ResidueField B := IsLocalRing.residue B zB
  have hzBunit : IsUnit zB := by
    apply (B.valuation_eq_one_iff zB).mpr
    exact hzval
  have hzbar0 : zbar ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit zB).2 hzBunit
  refine ⟨Q, hQmonic, hQirr, hQbarConst, ρ, zbar, hzbar0, ?_⟩
  simpa [zbar, zB] using hrootBar

theorem exists_mixed_residual_minpoly_of_irreducible_roots_unequal
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    (V : ValuationSubring K) (B : ValuationSubring L)
    [V.valuation.HasExtension B.valuation]
    {p : Polynomial K} (hp : Irreducible p)
    (hsplit : (p.map (algebraMap K L)).Splits)
    {α β : L}
    (hα : α ∈ (p.map (algebraMap K L)).roots)
    (hβ : β ∈ (p.map (algebraMap K L)).roots)
    (hαβ : B.valuation α ≠ B.valuation β) :
    ∃ Q : Polynomial V,
      Q.Monic ∧ Irreducible (Q.map V.subtype) ∧
        (Q.map (IsLocalRing.residue V)).coeff 0 = 0 ∧
          ∃ (ρ : IsLocalRing.ResidueField V →+*
              IsLocalRing.ResidueField B)
            (b : IsLocalRing.ResidueField B),
            b ≠ 0 ∧ ((Q.map (IsLocalRing.residue V)).map ρ).IsRoot b := by
  classical
  let F : Polynomial L := p.map (algebraMap K L)
  let roots : Multiset L := F.roots
  have hF0 : F ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).2 hp.ne_zero
  have hrootsCard : roots.card = p.natDegree := by
    calc
      roots.card = F.natDegree := Polynomial.splits_iff_card_roots.mp hsplit
      _ = p.natDegree := Polynomial.natDegree_map_eq_of_injective
        (algebraMap K L).injective p
  have hroots0 : roots ≠ 0 := by
    intro hzero
    have hpdeg : 0 < p.natDegree := hp.natDegree_pos
    rw [hzero] at hrootsCard
    exact (Nat.ne_of_gt hpdeg) hrootsCard.symm
  obtain ⟨amax, hamax, hmax⟩ :=
    roots.exists_max_image B.valuation hroots0
  let t : B.ValueGroup := B.valuation amax
  have hα' : α ∈ roots := hα
  have hβ' : β ∈ roots := hβ
  have hαle : B.valuation α ≤ t := hmax α hα'
  have hβle : B.valuation β ≤ t := hmax β hβ'
  obtain ⟨γ, hγ, hγlt⟩ : ∃ γ ∈ roots, B.valuation γ < t := by
    by_cases hαt : B.valuation α = t
    · refine ⟨β, hβ', lt_of_le_of_ne hβle ?_⟩
      intro hβt
      exact hαβ (hαt.trans hβt.symm)
    · exact ⟨α, hα', lt_of_le_of_ne hαle hαt⟩
  have htpos : 0 < t := (zero_le : 0 ≤ B.valuation γ).trans_lt hγlt
  have ht0 : t ≠ 0 := ne_of_gt htpos
  let seq : Multiset L := roots.filter (fun x => B.valuation x = t)
  let slt : Multiset L := roots.filter (fun x => B.valuation x ≠ t)
  have hpart : seq + slt = roots := by
    simpa [seq, slt] using
      (Multiset.filter_add_not (fun x => B.valuation x = t) roots)
  have hseq : ∀ x ∈ seq, B.valuation x = t := by
    intro x hx
    exact (Multiset.mem_filter.mp hx).2
  have hslt : ∀ x ∈ slt, B.valuation x < t := by
    intro x hx
    have hxdata := Multiset.mem_filter.mp hx
    exact lt_of_le_of_ne (hmax x hxdata.1) hxdata.2
  let r : ℕ := seq.card
  have hrpos : 0 < r := by
    have : amax ∈ seq := by
      simp [seq, t, hamax]
    exact Multiset.card_pos.mpr (by
      intro hzero
      rw [hzero] at this
      simp at this)
  have hrle : r ≤ p.natDegree := by
    rw [← hrootsCard]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have hboundary : B.valuation (roots.esymm r) = t ^ r := by
    rw [← hpart]
    exact valuation_esymm_eq_pow_card_add_of_eq_of_lt
      B.valuation t ht0 seq slt hseq hslt
  let k : ℕ := p.natDegree - r
  have hk : k ≤ F.natDegree := by
    rw [show F.natDegree = p.natDegree from
      Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective p]
    exact Nat.sub_le _ _
  have hsub : F.natDegree - k = r := by
    rw [show F.natDegree = p.natDegree from
      Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective p]
    exact Nat.sub_sub_self hrle
  have hcoeffF : F.coeff k =
      F.leadingCoeff * (-1) ^ r * roots.esymm r := by
    have h := Polynomial.coeff_eq_esymm_roots_of_splits hsplit hk
    change F.coeff k = F.leadingCoeff * (-1) ^ (F.natDegree - k) *
      roots.esymm (F.natDegree - k) at h
    rwa [hsub] at h
  have hleadF : F.leadingCoeff = algebraMap K L p.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_injective (algebraMap K L).injective p
  have hleadF0 : F.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hF0
  let a : K := p.coeff k / p.leadingCoeff
  have hmapa : algebraMap K L a = (-1) ^ r * roots.esymm r := by
    dsimp [a]
    rw [map_div₀ (algebraMap K L)]
    rw [← Polynomial.coeff_map, show p.map (algebraMap K L) = F from rfl]
    rw [hcoeffF, ← hleadF]
    field_simp
  have hmapaVal : B.valuation (algebraMap K L a) = t ^ r := by
    rw [hmapa, B.valuation.map_mul, hboundary]
    simp
  have hmapa0 : algebraMap K L a ≠ 0 := by
    intro hzero
    have := congrArg B.valuation hzero
    rw [hmapaVal] at this
    simp [pow_ne_zero _ ht0] at this
  let z : L := amax ^ r / algebraMap K L a
  let zγ : L := γ ^ r / algebraMap K L a
  have hzval : B.valuation z = 1 := by
    dsimp [z]
    rw [B.valuation.map_div, B.valuation.map_pow, hmapaVal]
    simp [t, pow_ne_zero _ ht0]
  have hγpow : B.valuation γ ^ r < t ^ r :=
    pow_lt_pow_left₀ hγlt zero_le (Nat.ne_of_gt hrpos)
  have hzγval : B.valuation zγ < 1 := by
    dsimp [zγ]
    rw [B.valuation.map_div, B.valuation.map_pow, hmapaVal]
    exact (div_lt_one₀ ((zero_lt_iff).2 (pow_ne_zero r ht0))).2 hγpow
  have hamaxEval : (aeval amax) p = 0 := by
    simpa [aeval_def, F, roots] using (Polynomial.mem_roots hF0).1 hamax
  have hγEval : (aeval γ) p = 0 := by
    simpa [aeval_def, F, roots] using (Polynomial.mem_roots hF0).1 hγ
  have hminRoots : minpoly K amax = minpoly K γ := by
    rw [← minpoly.eq_of_irreducible hp hamaxEval,
      ← minpoly.eq_of_irreducible hp hγEval]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).1 hminRoots
  have hσz : σ zγ = z := by
    have hσγ : σ γ = amax := hσ
    simp [zγ, z, hσγ]
  let q : Polynomial K := minpoly K z
  have hzint : IsIntegral K z :=
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hqmonic : q.Monic := minpoly.monic hzint
  have hqirr : Irreducible q := minpoly.irreducible hzint
  have hqsplit : (q.map (algebraMap K L)).Splits :=
    Normal.splits (inferInstance : Normal K L) z
  have hq0 : q ≠ 0 := hqirr.ne_zero
  have hqmap0 : q.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).2 hq0
  have hqz : (q.map (algebraMap K L)).IsRoot z := by
    simpa [q, aeval_def] using minpoly.aeval K z
  have hqzγ : (q.map (algebraMap K L)).IsRoot zγ := by
    have hminσ : minpoly K (σ zγ) = minpoly K zγ := minpoly.algEquiv_eq σ zγ
    have hminzγ : minpoly K zγ = q := by
      rw [← hminσ, hσz]
    simpa [q, hminzγ, aeval_def] using minpoly.aeval K zγ
  let qroots : Multiset L := (q.map (algebraMap K L)).roots
  have hqrootsBound : ∀ δ ∈ qroots, B.valuation δ ≤ 1 := by
    intro δ hδ
    have hδeval : (aeval δ) q = 0 := by
      simpa [aeval_def, qroots] using (Polynomial.mem_roots hqmap0).1 hδ
    have hminδ : minpoly K δ = minpoly K z := by
      have h := minpoly.eq_of_irreducible hqirr hδeval
      simpa [q, hqmonic] using h.symm
    obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).1 hminδ
    have hτroot : τ amax ∈ roots := by
      apply (Polynomial.mem_roots hF0).2
      change F.eval (τ amax) = 0
      have heval := (Polynomial.aeval_algHom_apply τ amax p).symm
      rw [hamaxEval, map_zero] at heval
      simpa [F, Polynomial.aeval_def] using heval.symm
    have hτle : B.valuation (τ amax) ≤ t := hmax _ hτroot
    have hτz0 : τ z = δ := hτ
    rw [← hτz0]
    have hτz : τ z = (τ amax) ^ r / algebraMap K L a := by
      simp [z]
    rw [hτz, B.valuation.map_div,
      B.valuation.map_pow, hmapaVal]
    apply (div_le_one₀ ((zero_lt_iff).2 (pow_ne_zero r ht0))).2
    exact pow_le_pow_left₀ zero_le hτle r
  exact exists_monic_residue_polynomial_of_mixed_roots V B q hqmonic hqirr hqsplit
    z zγ hzval hzγval hqz hqzγ hqrootsBound



/-- If a primitive polynomial has nonunit leading and constant coefficients,
the roots of its irreducible fraction-field image cannot all have the same
value under an extension valuation.  This is the Vieta estimate at the start
of Artin's proof of the factor-lifting criterion. -/
theorem not_all_roots_same_valuation_of_primitive_irreducible_endpoints_nonunit
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (B : ValuationSubring L)
    [V.valuation.HasExtension B.valuation]
    {p : Polynomial V}
    (hpprim : p.IsPrimitive)
    (hirr : Irreducible (p.map (algebraMap V K)))
    (hsplit :
      ((p.map (algebraMap V K)).map (algebraMap K L)).Splits)
    (hlead : ¬IsUnit p.leadingCoeff)
    (hconst : ¬IsUnit (p.coeff 0))
    {α : L}
    (hα : α ∈ ((p.map (algebraMap V K)).map
      (algebraMap K L)).roots) :
    ¬ ∀ β ∈ ((p.map (algebraMap V K)).map
      (algebraMap K L)).roots, B.valuation β = B.valuation α := by
  let pk : Polynomial K := p.map (algebraMap V K)
  let F : Polynomial L := pk.map (algebraMap K L)
  let roots : Multiset L := F.roots
  change F.Splits at hsplit
  change α ∈ roots at hα
  intro hall
  change ∀ β ∈ roots, B.valuation β = B.valuation α at hall
  have hpbar0 : p.map (IsLocalRing.residue V) ≠ 0 :=
    residue_ne_zero_of_isPrimitive_valuationSubring V hpprim
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hpbar0
  have hcoeffResidue : IsLocalRing.residue V (p.coeff i) ≠ 0 := by
    intro hzero
    exact (Polynomial.mem_support_iff.mp hi) (by
      rw [Polynomial.coeff_map]
      exact hzero)
  have hcoeffUnit : IsUnit (p.coeff i) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (p.coeff i)).mp hcoeffResidue
  have hcoeffBase : V.valuation (p.coeff i : K) = 1 :=
    (V.valuation_eq_one_iff (p.coeff i)).mp hcoeffUnit
  have hcoeffTarget :
      B.valuation (algebraMap K L (p.coeff i : K)) = 1 :=
    (Valuation.HasExtension.val_map_eq_one_iff
      V.valuation B.valuation (p.coeff i : K)).mpr hcoeffBase
  have hleadMax : p.leadingCoeff ∈ IsLocalRing.maximalIdeal V :=
    (IsLocalRing.mem_maximalIdeal p.leadingCoeff).mpr hlead
  have hconstMax : p.coeff 0 ∈ IsLocalRing.maximalIdeal V :=
    (IsLocalRing.mem_maximalIdeal (p.coeff 0)).mpr hconst
  have hleadBase : V.valuation (p.leadingCoeff : K) < 1 :=
    (V.valuation_lt_one_iff p.leadingCoeff).mp hleadMax
  have hconstBase : V.valuation (p.coeff 0 : K) < 1 :=
    (V.valuation_lt_one_iff (p.coeff 0)).mp hconstMax
  have hleadTarget :
      B.valuation (algebraMap K L (p.leadingCoeff : K)) < 1 :=
    (Valuation.HasExtension.val_map_lt_one_iff
      V.valuation B.valuation (p.leadingCoeff : K)).mpr hleadBase
  have hconstTarget :
      B.valuation (algebraMap K L (p.coeff 0 : K)) < 1 :=
    (Valuation.HasExtension.val_map_lt_one_iff
      V.valuation B.valuation (p.coeff 0 : K)).mpr hconstBase
  have hpk0 : pk ≠ 0 := hirr.ne_zero
  have hF0 : F ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hpk0
  have hinjVK : Function.Injective (algebraMap V K) := by
    intro x y hxy
    exact Subtype.ext hxy
  have halgVK (x : V) : algebraMap V K x = (x : K) := rfl
  have hleadF :
      F.leadingCoeff = algebraMap K L (p.leadingCoeff : K) := by
    rw [Polynomial.leadingCoeff_map_of_injective (algebraMap K L).injective]
    rw [Polynomial.leadingCoeff_map_of_injective hinjVK]
    rw [halgVK]
  have hcoeffFactor (j : ℕ) :
      algebraMap K L (p.coeff j : K) =
        algebraMap K L (p.leadingCoeff : K) *
          ((roots.map (fun x =>
            Polynomial.X - Polynomial.C x)).prod).coeff j := by
    have hcoeffSplit := congrArg (fun q : Polynomial L => q.coeff j)
      hsplit.eq_prod_roots
    simp only [Polynomial.coeff_C_mul] at hcoeffSplit
    rw [hleadF] at hcoeffSplit
    simpa [roots, F, pk, Polynomial.coeff_map, halgVK] using hcoeffSplit
  let t : B.ValueGroup := B.valuation α
  have hroots : ∀ β ∈ roots, B.valuation β = t := by
    intro β hβ
    exact hall β (by simpa [roots, F, pk] using hβ)
  have hconstFactor :
      B.valuation (algebraMap K L (p.coeff 0 : K)) =
        B.valuation (algebraMap K L (p.leadingCoeff : K)) *
          t ^ roots.card := by
    calc
      B.valuation (algebraMap K L (p.coeff 0 : K)) =
          B.valuation (F.coeff 0) := by
        simp [F, pk, Polynomial.coeff_map]
      _ = B.valuation
          (((-1) ^ F.natDegree) * F.leadingCoeff * roots.prod) := by
        rw [hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots]
      _ = B.valuation (algebraMap K L (p.leadingCoeff : K)) *
          B.valuation roots.prod := by
        rw [B.valuation.map_mul, B.valuation.map_mul]
        rw [hleadF]
        simp
      _ = B.valuation (algebraMap K L (p.leadingCoeff : K)) *
          t ^ roots.card := by
        rw [valuation_multiset_prod_eq_pow_card_of_eq B.valuation t roots hroots]
  rcases le_total t 1 with ht | ht
  · have hprodCoeff :
        B.valuation
            (((roots.map (fun x =>
              Polynomial.X - Polynomial.C x)).prod).coeff i) ≤ 1 := by
      have := valuation_coeff_prod_X_sub_C_le_pow_card
        B.valuation 1 le_rfl roots
        (fun β hβ => (hroots β hβ).trans_le ht) i
      simpa using this
    have hlt :
        B.valuation
          (algebraMap K L (p.leadingCoeff : K) *
            ((roots.map (fun x =>
              Polynomial.X - Polynomial.C x)).prod).coeff i) < 1 := by
      rw [B.valuation.map_mul]
      exact mul_lt_one_of_lt_of_le hleadTarget hprodCoeff
    have hcoeffLt :
        B.valuation (algebraMap K L (p.coeff i : K)) < 1 := by
      rw [hcoeffFactor i]
      exact hlt
    rw [hcoeffTarget] at hcoeffLt
    exact lt_irrefl 1 hcoeffLt
  · have hprodCoeff :
        B.valuation
            (((roots.map (fun x =>
              Polynomial.X - Polynomial.C x)).prod).coeff i) ≤
          t ^ roots.card :=
      valuation_coeff_prod_X_sub_C_le_pow_card
        B.valuation t ht roots (fun β hβ => (hroots β hβ).le) i
    have hcoeffLe :
        B.valuation (algebraMap K L (p.coeff i : K)) ≤
          B.valuation (algebraMap K L (p.coeff 0 : K)) := by
      rw [hcoeffFactor i, B.valuation.map_mul, hconstFactor]
      simpa [mul_comm] using
        mul_le_mul_right hprodCoeff
          (B.valuation (algebraMap K L (p.leadingCoeff : K)))
    have :
        B.valuation (algebraMap K L (p.coeff i : K)) < 1 :=
      hcoeffLe.trans_lt hconstTarget
    rw [hcoeffTarget] at this
    exact lt_irrefl 1 this

/-- The monic residual coprime-factor lifting property appearing in
the factor-lifting criterion.  Both residual factors and both lifted factors are monic, and
both residual identities are retained. -/
def MonicResidualCoprimeFactorLifting
    {K : Type u} [Field K] (V : ValuationSubring K) : Prop :=
  ∀ {f : Polynomial V}
      {gbar hbar : Polynomial (IsLocalRing.ResidueField V)},
    f.Monic →
      gbar.Monic →
        hbar.Monic →
          f.map (IsLocalRing.residue V) = gbar * hbar →
            IsCoprime gbar hbar →
              ∃ G H : Polynomial V,
                G.Monic ∧ H.Monic ∧ f = G * H ∧
                  G.map (IsLocalRing.residue V) = gbar ∧
                    H.map (IsLocalRing.residue V) = hbar

/-- the primitive factorization definition's primitive factorization property contains, in
particular, the exact monic lifting property of the factor-lifting criterion.  The factors
returned by the primitive factorization definition are normalized by the mutually inverse leading
coefficients; their reductions stay fixed because both leading coefficients
reduce to `1`. -/
theorem monicResidualCoprimeFactorLifting_of_henselFactorization
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hhensel : HenselFactorizationProperty V) :
    MonicResidualCoprimeFactorLifting V := by
  intro f gbar hbar hf hgbar hhbar hfactor hcoprime
  have hprimitive : f.map (IsLocalRing.residue V) ≠ 0 :=
    (hf.map (IsLocalRing.residue V)).ne_zero
  rcases hhensel hprimitive hfactor hcoprime with
    ⟨G, H, hGdegree, _hHdegree, hGH, hGmap, hHmap⟩
  have hG0 : G ≠ 0 := by
    intro hzero
    rw [hzero] at hGmap
    exact hgbar.ne_zero (by simpa using hGmap.symm)
  have hH0 : H ≠ 0 := by
    intro hzero
    rw [hzero] at hHmap
    exact hhbar.ne_zero (by simpa using hHmap.symm)
  have hleadProduct : G.leadingCoeff * H.leadingCoeff = 1 := by
    calc
      G.leadingCoeff * H.leadingCoeff = (G * H).leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul]
      _ = f.leadingCoeff := by rw [← hGH]
      _ = 1 := hf
  have hGleadResidue :
      IsLocalRing.residue V G.leadingCoeff = 1 := by
    change IsLocalRing.residue V (G.coeff G.natDegree) = 1
    rw [hGdegree]
    calc
      IsLocalRing.residue V (G.coeff gbar.natDegree) =
          (G.map (IsLocalRing.residue V)).coeff gbar.natDegree := by
        rw [Polynomial.coeff_map]
      _ = gbar.coeff gbar.natDegree := by rw [hGmap]
      _ = 1 := hgbar
  have hHleadResidue :
      IsLocalRing.residue V H.leadingCoeff = 1 := by
    have h := congrArg (IsLocalRing.residue V) hleadProduct
    simpa [map_mul, hGleadResidue] using h
  let G' : Polynomial V := Polynomial.C H.leadingCoeff * G
  let H' : Polynomial V := Polynomial.C G.leadingCoeff * H
  have hG' : G'.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    simpa [mul_comm] using hleadProduct
  have hH' : H'.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    exact hleadProduct
  have hfactor' : f = G' * H' := by
    have hC :
        Polynomial.C H.leadingCoeff * Polynomial.C G.leadingCoeff =
          (1 : Polynomial V) := by
      rw [← Polynomial.C_mul, mul_comm, hleadProduct]
      simp
    calc
      f = G * H := hGH
      _ = 1 * (G * H) := by simp
      _ = (Polynomial.C H.leadingCoeff * Polynomial.C G.leadingCoeff) *
          (G * H) := by rw [hC]
      _ = G' * H' := by
        dsimp [G', H']
        ring
  refine ⟨G', H', hG', hH', hfactor', ?_, ?_⟩
  · simp [G', Polynomial.map_mul, hGmap, hHleadResidue]
  · simp [H', Polynomial.map_mul, hHmap, hGleadResidue]

/-- A factor of positive degree and degree strictly below the product rules
out irreducibility over a field. -/
theorem not_irreducible_of_factor_natDegree_lt
    {K : Type u} [Field K] {f g h : Polynomial K}
    (hfactor : f = g * h)
    (hgpos : 0 < g.natDegree)
    (hglt : g.natDegree < f.natDegree) :
    ¬ Irreducible f := by
  intro hirr
  rcases hirr.isUnit_or_isUnit hfactor with hgunit | hhunit
  · exact (Nat.ne_of_gt hgpos) (Polynomial.natDegree_eq_zero_of_isUnit hgunit)
  · have hg0 : g ≠ 0 := by
      intro hzero
      simp [hzero] at hgpos
    have hh0 : h ≠ 0 := hhunit.ne_zero
    have hdegree : f.natDegree = g.natDegree := by
      rw [hfactor, Polynomial.natDegree_mul hg0 hh0,
        Polynomial.natDegree_eq_zero_of_isUnit hhunit, Nat.add_zero]
    exact (Nat.ne_of_lt hglt) hdegree.symm

/-- The zero-slope contradiction in Artin's proof of the factor-lifting criterion.
A nonconstant coprime residual splitting of a monic polynomial lifts to a
genuine factor of intermediate degree, so its image in the fraction field is
not irreducible. -/
theorem MonicResidualCoprimeFactorLifting.not_irreducible_map
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hlift : MonicResidualCoprimeFactorLifting V)
    {f : Polynomial V}
    {gbar hbar : Polynomial (IsLocalRing.ResidueField V)}
    (hf : f.Monic) (hgbar : gbar.Monic) (hhbar : hbar.Monic)
    (hfactor : f.map (IsLocalRing.residue V) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar)
    (hgpos : 0 < gbar.natDegree) (hhpos : 0 < hbar.natDegree) :
    ¬ Irreducible (f.map (algebraMap V K)) := by
  rcases hlift hf hgbar hhbar hfactor hcoprime with
    ⟨G, H, hG, _hH, hGH, hGmap, _hHmap⟩
  have hGdegree : G.natDegree = gbar.natDegree := by
    calc
      G.natDegree = (G.map (IsLocalRing.residue V)).natDegree :=
        (hG.natDegree_map (IsLocalRing.residue V)).symm
      _ = gbar.natDegree := by rw [hGmap]
  have hfdegree :
      f.natDegree = gbar.natDegree + hbar.natDegree := by
    calc
      f.natDegree = (f.map (IsLocalRing.residue V)).natDegree :=
        (hf.natDegree_map (IsLocalRing.residue V)).symm
      _ = (gbar * hbar).natDegree := by rw [hfactor]
      _ = gbar.natDegree + hbar.natDegree :=
        Polynomial.natDegree_mul hgbar.ne_zero hhbar.ne_zero
  let Gk : Polynomial K := G.map (algebraMap V K)
  let Hk : Polynomial K := H.map (algebraMap V K)
  have hinj : Function.Injective (algebraMap V K) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hGkdegree : Gk.natDegree = gbar.natDegree := by
    calc
      Gk.natDegree = G.natDegree :=
        Polynomial.natDegree_map_eq_of_injective hinj G
      _ = gbar.natDegree := hGdegree
  have hfkdegree : (f.map (algebraMap V K)).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj f
  have hfieldFactor : f.map (algebraMap V K) = Gk * Hk := by
    rw [hGH, Polynomial.map_mul]
  apply not_irreducible_of_factor_natDegree_lt hfieldFactor
  · simpa [hGkdegree] using hgpos
  · rw [hGkdegree, hfkdegree, hfdegree]
    exact Nat.lt_add_of_pos_right hhpos

/-- A monic polynomial irreducible over the fraction field cannot have a
coprime residual splitting into two positive-degree monic factors. -/
theorem MonicResidualCoprimeFactorLifting.irreducible_monic_reduction_coprime_factor_degree_zero
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hlift : MonicResidualCoprimeFactorLifting V)
    {f : Polynomial V}
    {gbar hbar : Polynomial (IsLocalRing.ResidueField V)}
    (hf : f.Monic)
    (hirr : Irreducible (f.map (algebraMap V K)))
    (hgbar : gbar.Monic) (hhbar : hbar.Monic)
    (hfactor : f.map (IsLocalRing.residue V) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    gbar.natDegree = 0 ∨ hbar.natDegree = 0 := by
  by_contra hdegree
  push Not at hdegree
  exact
    (hlift.not_irreducible_map hf hgbar hhbar hfactor hcoprime
      (Nat.pos_of_ne_zero hdegree.1) (Nat.pos_of_ne_zero hdegree.2)) hirr

theorem MonicResidualCoprimeFactorLifting.false_of_residue_constant_zero_and_nonzero_root
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hlift : MonicResidualCoprimeFactorLifting V)
    {Q : Polynomial V} (hQmonic : Q.Monic)
    (hQirr : Irreducible (Q.map V.subtype))
    (hconst : (Q.map (IsLocalRing.residue V)).coeff 0 = 0)
    {k' : Type*} [Field k']
    (ρ : IsLocalRing.ResidueField V →+* k')
    {b : k'} (hb0 : b ≠ 0)
    (hroot : ((Q.map (IsLocalRing.residue V)).map ρ).IsRoot b) :
    False := by
  let qbar : Polynomial (IsLocalRing.ResidueField V) :=
    Q.map (IsLocalRing.residue V)
  have hqbarMonic : qbar.Monic := hQmonic.map (IsLocalRing.residue V)
  have hqbar0 : qbar ≠ 0 := hqbarMonic.ne_zero
  have hzeroRoot : qbar.IsRoot 0 := by
    simpa [qbar, Polynomial.IsRoot, Polynomial.coeff_zero_eq_eval_zero]
      using hconst
  obtain ⟨R, hfactor, hnotdiv⟩ :=
    qbar.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hqbar0 0
  let r : ℕ := qbar.rootMultiplicity 0
  have hrpos : 0 < r := by
    dsimp [r]
    exact (Polynomial.rootMultiplicity_pos hqbar0).2 hzeroRoot
  have hfactorX : qbar = Polynomial.X ^ r * R := by
    simpa [r] using hfactor
  have hnotX : ¬ Polynomial.X ∣ R := by
    simpa [r] using hnotdiv
  have hXmonic :
      (Polynomial.X ^ r : Polynomial (IsLocalRing.ResidueField V)).Monic :=
    Polynomial.monic_X_pow r
  have hRmonic : R.Monic :=
    hXmonic.of_mul_monic_left (hfactorX ▸ hqbarMonic)
  have hcoprime : IsCoprime (Polynomial.X ^ r) R := by
    have hcopX : IsCoprime
        (Polynomial.X : Polynomial (IsLocalRing.ResidueField V)) R :=
      (Polynomial.prime_X
        (R := IsLocalRing.ResidueField V)).coprime_iff_not_dvd.2 hnotX
    exact hcopX.pow_left
  have hfactorMap : qbar.map ρ =
      Polynomial.X ^ r * R.map ρ := by
    rw [hfactorX, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  have hRroot : (R.map ρ).IsRoot b := by
    have heval : b ^ r * (R.map ρ).eval b = 0 := by
      rw [Polynomial.IsRoot, hfactorMap, Polynomial.eval_mul] at hroot
      simpa using hroot
    rw [Polynomial.IsRoot]
    exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero r hb0)
  have hRpos : 0 < R.natDegree := by
    by_contra hnotpos
    have hRdegree : R.natDegree = 0 := Nat.eq_zero_of_not_pos hnotpos
    have hRone : R = 1 :=
      Polynomial.eq_one_of_monic_natDegree_zero hRmonic hRdegree
    rw [hRone] at hRroot
    simp [Polynomial.IsRoot] at hRroot
  exact
    (hlift.not_irreducible_map hQmonic hXmonic hRmonic
      hfactorX hcoprime (by simpa using hrpos) hRpos) hQirr

/-- Artin's Nart-transform conclusion: under exact monic lifting, the roots
of an irreducible polynomial in any finite normal splitting extension all
have the same value. -/
theorem MonicResidualCoprimeFactorLifting.irreducible_roots_same_valuation
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    {V : ValuationSubring K} (B : ValuationSubring L)
    [V.valuation.HasExtension B.valuation]
    (hlift : MonicResidualCoprimeFactorLifting V)
    {p : Polynomial K} (hp : Irreducible p)
    (hsplit : (p.map (algebraMap K L)).Splits)
    {α β : L}
    (hα : α ∈ (p.map (algebraMap K L)).roots)
    (hβ : β ∈ (p.map (algebraMap K L)).roots) :
    B.valuation α = B.valuation β := by
  by_contra hαβ
  obtain ⟨Q, hQmonic, hQirr, hconst, ρ, b, hb0, hroot⟩ :=
    exists_mixed_residual_minpoly_of_irreducible_roots_unequal
      V B hp hsplit hα hβ hαβ
  exact hlift.false_of_residue_constant_zero_and_nonzero_root
    hQmonic hQirr hconst ρ hb0 hroot



/-- Exact monic coprime-factor lifting supplies the usual simple-root
Henselian structure. This is an intermediate consequence only; the
factor-lifting criterion below continues to the stronger primitive factorization statement of
the primitive factorization definition. -/
theorem henselianRing_of_monicResidualCoprimeFactorLifting
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hlift : MonicResidualCoprimeFactorLifting V) :
    HenselianRing V (IsLocalRing.maximalIdeal V) where
  jac := by
    rw [Ideal.jacobson, le_sInf_iff]
    rintro I ⟨-, hI⟩
    exact (IsLocalRing.eq_maximalIdeal hI).ge
  is_henselian := by
    intro f hf a0 hroot hsimple
    let fbar : Polynomial (IsLocalRing.ResidueField V) :=
      f.map (IsLocalRing.residue V)
    let abar : IsLocalRing.ResidueField V := IsLocalRing.residue V a0
    let lbar : Polynomial (IsLocalRing.ResidueField V) :=
      Polynomial.X - Polynomial.C abar
    let qbar : Polynomial (IsLocalRing.ResidueField V) := fbar /ₘ lbar
    have hlbar : lbar.Monic := Polynomial.monic_X_sub_C abar
    have hresidual : fbar = lbar * qbar := by
      symm
      exact residual_X_sub_C_mul_divByMonic_eq_map_of_eval_mem hroot
    have hfbar : fbar.Monic := hf.map (IsLocalRing.residue V)
    have hqbar : qbar.Monic :=
      hlbar.of_mul_monic_left (hresidual ▸ hfbar)
    have hcoprime : IsCoprime lbar qbar :=
      isCoprime_residual_X_sub_C_divByMonic_of_simpleRoot_mod hsimple
    rcases hlift hf hlbar hqbar hresidual hcoprime with
      ⟨G, H, hG, _hH, hfactor, hGmap, _hHmap⟩
    have hGdegree : G.natDegree = 1 := by
      calc
        G.natDegree = (G.map (IsLocalRing.residue V)).natDegree :=
          (hG.natDegree_map (IsLocalRing.residue V)).symm
        _ = lbar.natDegree := by rw [hGmap]
        _ = 1 := by simp [lbar]
    let a : V := -G.coeff 0
    have hGshape : G = Polynomial.X - Polynomial.C a := by
      rw [hG.eq_X_add_C hGdegree]
      simp [a]
    have haRoot : f.IsRoot a := by
      rw [hfactor, hGshape, Polynomial.IsRoot, Polynomial.eval_mul]
      simp
    have hcoeffmap :
        IsLocalRing.residue V (G.coeff 0) = -abar := by
      have h := congrArg (fun p => p.coeff 0) hGmap
      simpa [lbar, Polynomial.coeff_map] using h
    have haresidue : IsLocalRing.residue V a = abar := by
      dsimp [a]
      rw [map_neg, hcoeffmap]
      simp
    refine ⟨a, haRoot, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change IsLocalRing.residue V (a - a0) = 0
    rw [map_sub, haresidue]
    simp [abar]

end DiscreteValuationField

end
