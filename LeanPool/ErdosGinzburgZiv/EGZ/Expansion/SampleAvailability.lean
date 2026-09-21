/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.RelativeConcentration
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SampleDistribution
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangeResources

/-!
# Thick distributions of available disjoint exchanges

An equal mixture of diagonal and affine-relation samples is thick.
The collision estimate permits restriction to injective samples, which
are actual exchanges on the unused atom positions.
-/

open scoped BigOperators Matrix

namespace EGZ.Expansion

theorem finiteProb_pair_eq {A : Type*} [Fintype A] [Nonempty A] :
    finiteProb (fun x : A × A ↦ x.1 = x.2) = 1 / (Fintype.card A : ℝ) := by
  classical
  rw [finiteProb_prod]
  have h (a : A) : finiteProb (fun b ↦ a = b) = 1 / (Fintype.card A : ℝ) := by
    simpa only [eq_comm] using finiteProb_eq a
  simp only [h, Fintype.expect_const]

theorem exists_thick_exchange_weight {p r t N B W : ℕ} [Fact p.Prime]
    (S : Finset (IntCoord r)) [Nonempty S]
    (X : S → Type*) [∀ q, Fintype (X q)] [∀ q, Nonempty (X q)]
    {A : Type*} [Fintype A] (point : A → FpCoord p (r + t))
    (encode : ∀ q, X q → A) (hinj : ∀ q, Function.Injective (encode q))
    (hlabel : ∀ q x, Coord.first r t (point (encode q x)) = q.val.mod p)
    (U : Finset A) (hU : ∀ q x, encode q x ∉ U)
    (D : Matrix S (Option (Fin r)) ℤ) (Q : Matrix S S ℤ)
    (hQ : Q = (N : ℤ) • (1 : Matrix S S ℤ) - D * affineConstraintMatrix S)
    (hAQ : affineConstraintMatrix S * Q = 0)
    (hsize : ∀ q, (∑ z, (Q z q).natAbs) ≤ B)
    (hB : 2 ≤ B) (hN : 0 < N) (hNp : N < p)
    {η δ m : ℝ} (hη : 0 < η) (hηone : η ≤ 1) (hηδ : η ≤ δ)
    (hsmall : ((B : ℝ) + 1) * η < 1)
    (hm : 0 < m) (hcard : ∀ q, m ≤ Fintype.card (X q))
    (hcollision : (B : ℝ) ^ 2 / m ≤ η / 2)
    (hthick : IsThickRelative
      (pushWeight (fun z : Σ q, X q ↦ point (encode z.1 z.2)) (fun _ ↦ 1))
      (Coord.first r t) ((N + B + 1) * W) δ) :
    ∃ ν : FpCoord p t → ℝ, (∀ v, 0 ≤ ν v) ∧ 0 < ∑ v, ν v ∧
      IsCentrallyThick ν W (η / (4 * S.card)) ∧
      ∀ v, 0 < ν v → ∃ e : Exchange point B, Disjoint e.support U ∧ e.shift = v := by
  classical
  let P : S → ExchangePattern S := fun q ↦ ExchangePattern.ofRelation (fun z ↦ Q z q)
  let C : S ⊕ S → Type _ := Sum.elim (fun q ↦ X q × X q) (fun q ↦ (P q).Sample X)
  let : ∀ i, Fintype (C i) := fun i ↦ by cases i <;> dsimp [C] <;> infer_instance
  let : ∀ i, Nonempty (C i) := fun i ↦ by cases i <;> dsimp [C] <;> infer_instance
  let : Nonempty (Σ q, X q) := ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
  let value : ∀ i, C i → FpCoord p t := fun i ↦
    match i with
    | .inl q => fun x ↦ Coord.last r t (point (encode q x.2) - point (encode q x.1))
    | .inr q => (P q).sampleSum (fun z a ↦ Coord.last r t (point (encode z a)))
  let valid : ∀ i, C i → Prop := fun i ↦
    match i with
    | .inl _ => fun x ↦ x.1 ≠ x.2
    | .inr q => fun x ↦ Function.Injective (fun i : (P q).Position ↦ encode ((P q).label i) (x i))
  have hbad (i : S ⊕ S) : finiteProb (fun x : C i ↦ ¬valid i x) ≤ η / 2 := by
    cases i with
    | inl q =>
      change finiteProb (fun x : X q × X q ↦ ¬x.1 ≠ x.2) ≤ η / 2
      simp only [not_not, finiteProb_pair_eq]
      calc
        1 / (Fintype.card (X q) : ℝ) ≤ 1 / m := one_div_le_one_div_of_le hm (hcard q)
        _ ≤ (B : ℝ) ^ 2 / m := by
          apply div_le_div_of_nonneg_right _ hm.le
          have : (2 : ℝ) ≤ B := by exact_mod_cast hB
          nlinarith
        _ ≤ η / 2 := hcollision
    | inr q =>
      have h := finiteProb_not_injective_le (fun i : (P q).Position ↦ X ((P q).label i))
        (fun i ↦ encode ((P q).label i)) (fun i ↦ hinj ((P q).label i)) hm
        (fun i ↦ hcard ((P q).label i))
      apply h.trans
      apply le_trans _ hcollision
      apply div_le_div_of_nonneg_right _ hm.le
      have hP : (P q).size ≤ B := by
        simpa only [P, ExchangePattern.ofRelation_size] using hsize q
      have hh : ((P q).size : ℝ) ≤ B := by exact_mod_cast hP
      rw [ExchangePattern.card_position]
      nlinarith [show (0 : ℝ) ≤ (P q).size by positivity]
  have hout (ξ : FpCoord p t →ₗ[ZMod p] ZMod p) (hξ : ξ ≠ 0) :
      ∃ i, η ≤ finiteProb (fun x : C i ↦ ¬ HasBoundedRepresentative p W (ξ (value i x))) := by
    by_contra! hn
    have hpair (q : S) : finiteProb (fun x : X q × X q ↦
        ¬ HasBoundedRepresentative p W
          (ξ (Coord.last r t (point (encode q x.2))) -
            ξ (Coord.last r t (point (encode q x.1))))) ≤ η := by
      convert (hn (.inl q)).le using 1 <;> try simp only [value, map_sub]
      all_goals rfl
    have hsum (q : S) : finiteProb (fun x : (P q).Sample X ↦
        ¬ HasBoundedRepresentative p W ((P q).sampleSum
          (fun z a ↦ ξ (Coord.last r t (point (encode z a)))) x)) ≤ η := by
      convert (hn (.inr q)).le using 1 <;>
        try simp only [value, ExchangePattern.sampleSum, map_sum, map_zsmul]
      all_goals rfl
    obtain ⟨ψ, hψ, hprob⟩ := relative_concentration S X (fun q x ↦ point (encode q x))
      hlabel D Q hQ hsize hN hNp ξ hξ hη.le hsmall hpair hsum
    exact hthick ψ hψ ((isThinAlong_pushWeight_of_finiteProb
      (fun z : Σ q, X q ↦ point (encode z.1 z.2)) ψ hprob).mono_error hηδ)
  let ν := sampleWeight C value valid
  have hνthick := sampleWeight_centrallyThick C value valid hη hηone hbad hout
  refine ⟨ν, sampleWeight_nonneg C value valid,
    sampleWeight_mass_pos C value valid hη hηone hbad, ?_, ?_⟩
  · convert hνthick using 1
    simp only [Fintype.card_sum, Fintype.card_coe, Nat.cast_add]
    congr 1
    ring
  · intro v hv
    obtain ⟨i, x, hx, hvx⟩ := sampleWeight_pos_exists C value valid hv
    cases i with
    | inl q =>
      have hxy : encode q x.1 ≠ encode q x.2 := fun h ↦ hx ((hinj q) h)
      have hfirst : Coord.first r t (point (encode q x.2)) =
          Coord.first r t (point (encode q x.1)) := (hlabel q x.2).trans (hlabel q x.1).symm
      refine ⟨Exchange.ofPair point _ _ hxy hfirst hB,
        Exchange.ofPair_support_avoids point _ _ hxy hfirst hB U (hU q x.1) (hU q x.2), ?_⟩
      exact (Exchange.ofPair_shift point _ _ hxy hfirst hB).trans hvx
    | inr q =>
      let atom : (P q).Position → A := fun i ↦ encode ((P q).label i) (x i)
      have hatom (i : (P q).Position) : Coord.first r t (point (atom i)) =
          ((P q).label i).val.mod p := hlabel _ _
      have hmass : (∑ z, (P q).positive z) = ∑ z, (P q).negative z :=
        relation_column_pos_neg_sum hAQ q
      have hlab : (∑ z, (P q).positive z • z.val.mod p) =
          ∑ z, (P q).negative z • z.val.mod p := by
        let f : IntCoord r →+ FpCoord p r :=
          { toFun := IntCoord.mod p
            map_zero' := by ext j; simp
            map_add' := by intro x y; ext j; simp }
        have hh := congrArg f (relation_column_pos_neg_weighted_sum hAQ q)
        simpa only [map_sum, map_nsmul, f, P, ExchangePattern.ofRelation,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hh
      have hPsize : (P q).size ≤ B := by simpa [P, ExchangePattern.ofRelation_size] using hsize q
      refine ⟨Exchange.ofPattern (P q) point atom hx (fun z ↦ z.val.mod p) hatom hmass hlab hPsize,
        Exchange.ofPattern_support_avoids (P q) point atom hx (fun z ↦ z.val.mod p)
          hatom hmass hlab hPsize U (fun i ↦ hU _ _), ?_⟩
      exact (Exchange.ofPattern_shift (P q) point atom hx (fun z ↦ z.val.mod p)
        hatom hmass hlab hPsize).trans hvx

end EGZ.Expansion
