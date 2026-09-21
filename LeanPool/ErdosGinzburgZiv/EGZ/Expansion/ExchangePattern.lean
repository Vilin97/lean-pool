/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Sampling
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Subweights
import Mathlib.Data.Fintype.Sum

/-!
# Bounded exchange patterns and their independent samples

A pattern prescribes the number of positive and negative positions in each
fibre. Sampling all these positions independently gives exact uniform
marginals; injective samples are the disjoint exchanges used later.
-/

open scoped BigOperators

namespace EGZ.Expansion

structure ExchangePattern (S : Type*) where
  positive : S → ℕ
  negative : S → ℕ

namespace ExchangePattern

variable {S : Type*} [Fintype S] [DecidableEq S]

def Position (P : ExchangePattern S) :=
  (Σ q, Fin (P.positive q)) ⊕ (Σ q, Fin (P.negative q))

instance (P : ExchangePattern S) : Fintype P.Position :=
  inferInstanceAs (Fintype ((Σ q, Fin (P.positive q)) ⊕ (Σ q, Fin (P.negative q))))

instance (P : ExchangePattern S) : DecidableEq P.Position :=
  inferInstanceAs (DecidableEq ((Σ q, Fin (P.positive q)) ⊕ (Σ q, Fin (P.negative q))))

def label (P : ExchangePattern S) : P.Position → S := Sum.elim Sigma.fst Sigma.fst

def sign (P : ExchangePattern S) : P.Position → ℤ := Sum.elim (fun _ ↦ 1) (fun _ ↦ -1)

abbrev Sample (P : ExchangePattern S) (X : S → Type*) := ∀ i : P.Position, X (P.label i)

def size (P : ExchangePattern S) : ℕ := (∑ q, P.positive q) + ∑ q, P.negative q

@[simp] theorem card_position (P : ExchangePattern S) : Fintype.card P.Position = P.size := by
  rw [Fintype.card_congr (show P.Position ≃
      ((Σ q, Fin (P.positive q)) ⊕ (Σ q, Fin (P.negative q))) from Equiv.refl _)]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, size]

@[simp] theorem sign_natAbs (P : ExchangePattern S) (i : P.Position) : (P.sign i).natAbs = 1 := by
  cases i <;> simp [sign]

theorem sum_sign_smul {G : Type*} [AddCommGroup G] (P : ExchangePattern S) (r : S → G) :
    (∑ i : P.Position, P.sign i • r (P.label i)) =
      (∑ q, P.positive q • r q) - ∑ q, P.negative q • r q := by
  change (∑ i : (Σ q, Fin (P.positive q)) ⊕ (Σ q, Fin (P.negative q)),
    Sum.elim (fun _ ↦ (1 : ℤ)) (fun _ ↦ -1) i •
      r (Sum.elim Sigma.fst Sigma.fst i)) = _
  simp [Fintype.sum_sum_type, Fintype.sum_sigma, ← Finset.sum_neg_distrib, sub_eq_add_neg]

noncomputable def sampleSum {G : Type*} [AddCommGroup G]
    (P : ExchangePattern S) {X : S → Type*} (v : ∀ q, X q → G) (x : P.Sample X) : G :=
  ∑ i, P.sign i • v (P.label i) (x i)

def ofRelation (b : S → ℤ) : ExchangePattern S := ⟨fun q ↦ (b q).toNat, fun q ↦ (-b q).toNat⟩

theorem ofRelation_sum {G : Type*} [AddCommGroup G] (b : S → ℤ) (r : S → G) :
    (∑ i : (ofRelation b).Position, (ofRelation b).sign i • r ((ofRelation b).label i)) =
      ∑ q, b q • r q := by
  rw [sum_sign_smul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  change (b q).toNat • r q - (-b q).toNat • r q = b q • r q
  rcases Int.le_total 0 (b q) with h | h
  · rw [Int.toNat_eq_zero.mpr (neg_nonpos.mpr h), zero_smul, sub_zero]
    rw [← natCast_zsmul, Int.toNat_of_nonneg h]
  · rw [Int.toNat_eq_zero.mpr h, zero_smul, zero_sub]
    rw [← natCast_zsmul, Int.toNat_of_nonneg (neg_nonneg.mpr h), neg_smul, neg_neg]

theorem ofRelation_size (b : S → ℤ) : (ofRelation b).size = ∑ q, (b q).natAbs := by
  rw [size, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  change (b q).toNat + (-b q).toNat = (b q).natAbs
  omega

/-- Product-sample concentration yields a deterministic bound for the
corresponding sum of fibre centres. -/
theorem center_sum_bounded (P : ExchangePattern S)
    {X : S → Type*} [∀ q, Fintype (X q)] [∀ q, Nonempty (X q)]
    {p W : ℕ} (v : ∀ q, X q → ZMod p) (r : S → ZMod p) {η : ℝ}
    (hcoord : ∀ q, finiteProb (fun x ↦ ¬ HasBoundedRepresentative p W (v q x - r q)) ≤ η)
    (hsum : finiteProb (fun x : P.Sample X ↦ ¬ HasBoundedRepresentative p W (P.sampleSum v x)) ≤ η)
    (hsmall : ((P.size : ℝ) + 1) * η < 1) :
    HasBoundedRepresentative p ((1 + P.size) * W)
      ((∑ q, P.positive q • r q) - ∑ q, P.negative q • r q) := by
  have h := bounded_center_sum_of_concentration (fun i : P.Position ↦ X (P.label i))
    (fun i ↦ v (P.label i)) (fun i ↦ r (P.label i)) P.sign
    (fun i ↦ hcoord (P.label i))
    (by simpa only [sampleSum, zsmul_eq_mul] using hsum)
    (by simpa only [card_position] using hsmall)
  simpa only [sign_natAbs, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one, card_position, ← zsmul_eq_mul, sum_sign_smul] using h

end ExchangePattern

end EGZ.Expansion
