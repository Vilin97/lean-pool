/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.AffineRelations
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Sampling
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangePattern

/-!
# Reconstructing relative thinness from concentrated exchanges

Concentration of the individual exchange components gives centres in each
fibre. Integer affine relations turn these centres into one affine slab.
-/

open scoped BigOperators Matrix

namespace EGZ.Expansion

theorem finiteProb_sigma_le {I : Type*} [Fintype I] [Nonempty I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (P : (Σ i, A i) → Prop) {η : ℝ}
    (h : ∀ i, finiteProb (fun a ↦ P ⟨i, a⟩) ≤ η) : finiteProb P ≤ η := by
  classical
  let i₀ : I := Classical.choice inferInstance
  let : Nonempty (Σ i, A i) := ⟨⟨i₀, Classical.choice inferInstance⟩⟩
  have hcard : 0 < (Fintype.card (Σ i, A i) : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [finiteProb, Fintype.expect_eq_sum_div_card]
  apply (div_le_iff₀ hcard).mpr
  rw [Fintype.sum_sigma, Fintype.card_sigma, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := h i
  rw [finiteProb, Fintype.expect_eq_sum_div_card] at hi
  exact (div_le_iff₀ (by exact_mod_cast (Fintype.card_pos (α := A i)))).mp hi

theorem finiteProb_eq_natMassOn {A : Type*} [Fintype A] (P : A → Prop) :
    finiteProb P = (natMassOn (fun _ : A ↦ 1) {a | P a} : ℝ) / Fintype.card A := by
  classical
  rw [finiteProb, Fintype.expect_eq_sum_div_card]
  congr 1
  simp [natMassOn]

theorem isThinAlong_pushWeight_of_finiteProb {A : Type*} [Fintype A] [Nonempty A]
    {p n K : ℕ} [NeZero p] (point : A → FpCoord p n)
    (ξ : FpCoord p n →ᵃ[ZMod p] ZMod p) {η : ℝ}
    (h : finiteProb (fun a ↦ ¬ HasBoundedRepresentative p K (ξ (point a))) ≤ η) :
    IsThinAlong (pushWeight point (fun _ ↦ 1)) ξ K η := by
  have hgood : 1 - η ≤ finiteProb (fun a ↦ HasBoundedRepresentative p K (ξ (point a))) := by
    rw [finiteProb_not] at h
    linarith
  rw [finiteProb_eq_natMassOn] at hgood
  have hcard : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmass := (le_div_iff₀ hcard).mp hgood
  rw [isThinAlong_iff_natMass, natMass_pushWeight, natMassOn_pushWeight]
  simpa only [natMass, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    slab, Set.preimage_ofPred_eq] using hmass

/-- Grouping the signed slots of a relation by their labels. -/
theorem sum_signed_slots {S I R : Type*} [Fintype S] [DecidableEq S] [Fintype I] [CommRing R]
    (label : I → S) (sign : I → ℤ) (coeff : S → ℤ)
    (hcoeff : ∀ q, (∑ i, if label i = q then sign i else 0) = coeff q)
    (v : S → R) :
    (∑ i, (sign i : R) * v (label i)) = ∑ q, (coeff q : R) * v q := by
  classical
  simp only [← hcoeff, Int.cast_sum, Finset.sum_mul, apply_ite, Int.cast_zero, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- If every diagonal exchange and every chosen affine-relation exchange
is concentrated, all positions lie mostly in one affine slab that varies
in a fibre direction. -/
theorem relative_concentration {p r t N B W : ℕ} [Fact p.Prime]
    (S : Finset (IntCoord r)) [Nonempty S]
    (X : S → Type*) [∀ q, Fintype (X q)] [∀ q, Nonempty (X q)]
    (point : ∀ q, X q → FpCoord p (r + t))
    (hlabel : ∀ q x, Coord.first r t (point q x) = q.val.mod p)
    (M : Matrix S (Option (Fin r)) ℤ) (Q : Matrix S S ℤ)
    (hQ : Q = (N : ℤ) • (1 : Matrix S S ℤ) - M * affineConstraintMatrix S)
    (hsize : ∀ q, (∑ z, (Q z q).natAbs) ≤ B)
    (hN : 0 < N) (hNp : N < p)
    (ξ : FpCoord p t →ₗ[ZMod p] ZMod p) (hξ : ξ ≠ 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : ((B : ℝ) + 1) * η < 1)
    (hpair : ∀ q, finiteProb (fun x : X q × X q ↦
      ¬ HasBoundedRepresentative p W
        (ξ (Coord.last r t (point q x.2)) - ξ (Coord.last r t (point q x.1)))) ≤ η)
    (hsum : ∀ q, finiteProb (fun x : (ExchangePattern.ofRelation (fun z ↦ Q z q)).Sample X ↦
      ¬ HasBoundedRepresentative p W
        ((ExchangePattern.ofRelation (fun z ↦ Q z q)).sampleSum
          (fun z a ↦ ξ (Coord.last r t (point z a))) x)) ≤ η) :
    ∃ ψ : FpCoord p (r + t) →ᵃ[ZMod p] ZMod p,
      NonconstantOnFibers (Coord.first r t) ψ ∧
      finiteProb (fun x : Σ q, X q ↦
        ¬ HasBoundedRepresentative p ((N + B + 1) * W) (ψ (point x.1 x.2))) ≤ η := by
  classical
  have hcenters : ∀ q, ∃ c : ZMod p, finiteProb (fun x : X q ↦
      ¬ HasBoundedRepresentative p W (ξ (Coord.last r t (point q x)) - c)) ≤ η := by
    intro q
    exact exists_center_of_pair_concentration _ (hpair q)
  choose c hc using hcenters
  have hrel : ∀ q, HasBoundedRepresentative p ((1 + B) * W)
      (∑ z, (Q z q : ZMod p) * c z) := by
    intro q
    let P := ExchangePattern.ofRelation (fun z ↦ Q z q)
    have hPsize : P.size ≤ B := by simpa [P, ExchangePattern.ofRelation_size] using hsize q
    have hPs : ((P.size : ℝ) + 1) * η < 1 := by
      have hcast : (P.size : ℝ) ≤ B := by exact_mod_cast hPsize
      exact (mul_le_mul_of_nonneg_right (by linarith) hη).trans_lt hsmall
    have h := P.center_sum_bounded (fun z a ↦ ξ (Coord.last r t (point z a))) c hc (hsum q) hPs
    have heq : (∑ z, P.positive z • c z) - ∑ z, P.negative z • c z =
        ∑ z, (Q z q : ZMod p) * c z := by
      rw [← P.sum_sign_smul, ExchangePattern.ofRelation_sum]
      simp only [zsmul_eq_mul]
    rw [heq] at h
    exact h.mono (Nat.mul_le_mul_right W (Nat.add_le_add_left hPsize 1))
  let a := affineFromCoefficients ((M.map (Int.castRingHom (ZMod p))).transpose *ᵥ c)
  let ψ : FpCoord p (r + t) →ᵃ[ZMod p] ZMod p :=
    (N : ZMod p) • (ξ.comp (Coord.last r t)).toAffineMap -
      a.comp (Coord.first r t).toAffineMap
  refine ⟨ψ, nonconstant_scaled_fibre_residual hN hNp ξ hξ a, ?_⟩
  apply finiteProb_sigma_le X
  intro q
  refine (finiteProb_mono (fun x hbad ↦ ?_)).trans (hc q)
  intro hgood
  apply hbad
  have hh := affine_relation_residual_bounded hQ c ξ q (point q x) (hlabel q x) hgood (hrel q)
  have hwidth : N * W + (1 + B) * W = (N + B + 1) * W := by ring
  simpa only [hwidth] using hh

end EGZ.Expansion
