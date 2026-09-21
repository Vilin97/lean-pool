/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangePattern
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SetGrowth
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedCoordinates

/-!
# Finite exchanges and their consumed positions

An exchange uses two disjoint sets of atom positions, with equal sizes and
equal first-coordinate sums.  Its shift lies in the remaining coordinates.
Injective samples of a balanced pattern produce such exchanges.
-/

open scoped BigOperators Classical

namespace EGZ.Expansion

variable {p r t : ℕ} {A : Type*} [Fintype A]

/-- The finite collection of exchanges of bounded size in a fixed atom
family.  Multiplicity is represented by distinct atom positions. -/
def Exchange (point : A → FpCoord p (r + t)) (B : ℕ) :=
  {J : Finset A × Finset A // Disjoint J.1 J.2 ∧ J.1.card = J.2.card ∧
    (∑ x ∈ J.1, Coord.first r t (point x)) = (∑ x ∈ J.2, Coord.first r t (point x)) ∧
    J.1.card + J.2.card ≤ B}

noncomputable instance (point : A → FpCoord p (r + t)) (B : ℕ) : Fintype (Exchange point B) := by
  unfold Exchange
  infer_instance

namespace Exchange

variable {point : A → FpCoord p (r + t)} {B : ℕ}

def left (E : Exchange point B) : Finset A := E.val.1
def right (E : Exchange point B) : Finset A := E.val.2
noncomputable def support (E : Exchange point B) : Finset A := E.left ∪ E.right
noncomputable def difference (E : Exchange point B) : FpCoord p (r + t) :=
  (∑ x ∈ E.left, point x) - ∑ x ∈ E.right, point x
noncomputable def shift (E : Exchange point B) : FpCoord p t := Coord.last r t E.difference

theorem disjoint (E : Exchange point B) : Disjoint E.left E.right := E.property.1
theorem card_eq (E : Exchange point B) : E.left.card = E.right.card := E.property.2.1
theorem first_sum_eq (E : Exchange point B) :
    (∑ x ∈ E.left, Coord.first r t (point x)) = ∑ x ∈ E.right, Coord.first r t (point x) :=
  E.property.2.2.1
theorem size_le (E : Exchange point B) : E.left.card + E.right.card ≤ B := E.property.2.2.2

theorem support_card_le (E : Exchange point B) : E.support.card ≤ B :=
  (Finset.card_union_le _ _).trans E.size_le

theorem first_difference (E : Exchange point B) : Coord.first r t E.difference = 0 := by
  simp only [difference, map_sub, map_sum, E.first_sum_eq, sub_self]

theorem shift_eq_zero_of_support_eq_empty (E : Exchange point B) (h : E.support = ∅) : E.shift = 0 := by
  have hh : E.left = ∅ ∧ E.right = ∅ := Finset.union_eq_empty.mp h
  simp [shift, difference, hh.1, hh.2]

/-- Exchange one atom for a distinct atom in the same first-coordinate
fibre.  The shift has the orientation `point y - point x`. -/
noncomputable def ofPair (point : A → FpCoord p (r + t)) {B : ℕ}
    (x y : A) (hxy : x ≠ y)
    (hfirst : Coord.first r t (point y) = Coord.first r t (point x)) (hB : 2 ≤ B) :
    Exchange point B :=
  ⟨({y}, {x}), by simpa using hxy.symm, by simp, by simpa using hfirst, by simpa using hB⟩

@[simp] theorem ofPair_shift (point : A → FpCoord p (r + t)) {B : ℕ}
    (x y : A) (hxy : x ≠ y)
    (hfirst : Coord.first r t (point y) = Coord.first r t (point x)) (hB : 2 ≤ B) :
    (ofPair point x y hxy hfirst hB).shift = Coord.last r t (point y - point x) := by
  simp [ofPair, shift, difference, left, right]

theorem ofPair_support_avoids (point : A → FpCoord p (r + t)) {B : ℕ}
    (x y : A) (hxy : x ≠ y)
    (hfirst : Coord.first r t (point y) = Coord.first r t (point x)) (hB : 2 ≤ B)
    (U : Finset A) (hx : x ∉ U) (hy : y ∉ U) :
    Disjoint (ofPair point x y hxy hfirst hB).support U := by
  apply Finset.disjoint_left.mpr
  intro a ha hu
  simp only [support, left, right, ofPair, Finset.mem_union, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact hy hu
  · exact hx hu

section Pattern

variable {S : Type*} [Fintype S] [DecidableEq S]
  (P : ExchangePattern S) (point : A → FpCoord p (r + t))
  (atom : P.Position → A) (hinj : Function.Injective atom)

noncomputable def positiveAtoms : Finset A :=
  Finset.univ.image (fun i : Σ q, Fin (P.positive q) ↦ atom (Sum.inl i))

noncomputable def negativeAtoms : Finset A :=
  Finset.univ.image (fun i : Σ q, Fin (P.negative q) ↦ atom (Sum.inr i))

include hinj

theorem positiveAtoms_card : (positiveAtoms P atom).card = ∑ q, P.positive q := by
  calc
    _ = Fintype.card (Σ q, Fin (P.positive q)) :=
      Finset.card_image_of_injective _ (fun i j h ↦ Sum.inl_injective (hinj h))
    _ = _ := by simp

theorem negativeAtoms_card : (negativeAtoms P atom).card = ∑ q, P.negative q := by
  calc
    _ = Fintype.card (Σ q, Fin (P.negative q)) :=
      Finset.card_image_of_injective _ (fun i j h ↦ Sum.inr_injective (hinj h))
    _ = _ := by simp

theorem pattern_atoms_disjoint : Disjoint (positiveAtoms P atom) (negativeAtoms P atom) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
  have hh : (Sum.inl i : (Σ q, Fin (P.positive q)) ⊕ (Σ q, Fin (P.negative q))) =
      Sum.inr j := hinj (hi.trans hj.symm)
  cases hh

theorem positiveAtoms_sum {G : Type*} [AddCommMonoid G] (f : A → G) :
    (∑ a ∈ positiveAtoms P atom, f a) = ∑ i : Σ q, Fin (P.positive q), f (atom (Sum.inl i)) := by
  rw [positiveAtoms, Finset.sum_image]
  exact fun i _ j _ h ↦ Sum.inl_injective (hinj h)

theorem negativeAtoms_sum {G : Type*} [AddCommMonoid G] (f : A → G) :
    (∑ a ∈ negativeAtoms P atom, f a) = ∑ i : Σ q, Fin (P.negative q), f (atom (Sum.inr i)) := by
  rw [negativeAtoms, Finset.sum_image]
  exact fun i _ j _ h ↦ Sum.inr_injective (hinj h)

/-- Every injective balanced pattern is an actual exchange. -/
noncomputable def ofPattern (label : S → FpCoord p r)
    (hatom : ∀ i, Coord.first r t (point (atom i)) = label (P.label i))
    (hmass : (∑ q, P.positive q) = ∑ q, P.negative q)
    (hlabel : (∑ q, P.positive q • label q) = ∑ q, P.negative q • label q)
    {B : ℕ} (hsize : P.size ≤ B) : Exchange point B := by
  refine ⟨(positiveAtoms P atom, negativeAtoms P atom), pattern_atoms_disjoint P atom hinj,
    ?_, ?_, ?_⟩
  · rw [positiveAtoms_card P atom hinj, negativeAtoms_card P atom hinj]
    exact hmass
  · rw [positiveAtoms_sum P atom hinj, negativeAtoms_sum P atom hinj]
    have hpos (i : Σ q, Fin (P.positive q)) :
        Coord.first r t (point (atom (Sum.inl i))) = label i.1 := hatom (Sum.inl i)
    have hneg (i : Σ q, Fin (P.negative q)) :
        Coord.first r t (point (atom (Sum.inr i))) = label i.1 := hatom (Sum.inr i)
    simp_rw [hpos, hneg]
    simpa [ExchangePattern.label, Fintype.sum_sigma] using hlabel
  · rw [positiveAtoms_card P atom hinj, negativeAtoms_card P atom hinj]
    exact hsize

theorem ofPattern_shift (label : S → FpCoord p r)
    (hatom : ∀ i, Coord.first r t (point (atom i)) = label (P.label i))
    (hmass : (∑ q, P.positive q) = ∑ q, P.negative q)
    (hlabel : (∑ q, P.positive q • label q) = ∑ q, P.negative q • label q)
    {B : ℕ} (hsize : P.size ≤ B) :
    (ofPattern P point atom hinj label hatom hmass hlabel hsize).shift =
      ∑ i : P.Position, P.sign i • Coord.last r t (point (atom i)) := by
  simp only [shift, difference, ofPattern, left, right, map_sub, map_sum]
  rw [positiveAtoms_sum P atom hinj, negativeAtoms_sum P atom hinj]
  change _ = ∑ i : (Σ q, Fin (P.positive q)) ⊕ (Σ q, Fin (P.negative q)), _
  simp [Fintype.sum_sum_type, ExchangePattern.sign, sub_eq_add_neg, Finset.sum_neg_distrib]

theorem ofPattern_support_avoids (label : S → FpCoord p r)
    (hatom : ∀ i, Coord.first r t (point (atom i)) = label (P.label i))
    (hmass : (∑ q, P.positive q) = ∑ q, P.negative q)
    (hlabel : (∑ q, P.positive q • label q) = ∑ q, P.negative q • label q)
    {B : ℕ} (hsize : P.size ≤ B) (U : Finset A) (hU : ∀ i, atom i ∉ U) :
    Disjoint (ofPattern P point atom hinj label hatom hmass hlabel hsize).support U := by
  apply Finset.disjoint_left.mpr
  intro a ha hu
  change a ∈ positiveAtoms P atom ∪ negativeAtoms P atom at ha
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hU (Sum.inl i) hu
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hU (Sum.inr i) hu

end Pattern

section Relation

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem relation_mass_eq (b : S → ℤ) (hb : ∑ q, b q = 0) :
    (∑ q, (ExchangePattern.ofRelation b).positive q) =
      ∑ q, (ExchangePattern.ofRelation b).negative q := by
  have hh := ExchangePattern.ofRelation_sum b (fun _ ↦ (1 : ℤ))
  rw [ExchangePattern.sum_sign_smul (ExchangePattern.ofRelation b) (fun _ ↦ (1 : ℤ))] at hh
  simp only [nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_id, hb] at hh
  have heq := sub_eq_zero.mp hh
  exact_mod_cast heq

theorem relation_label_eq {G : Type*} [AddCommGroup G]
    (b : S → ℤ) (label : S → G) (hb : ∑ q, b q • label q = 0) :
    (∑ q, (ExchangePattern.ofRelation b).positive q • label q) =
      ∑ q, (ExchangePattern.ofRelation b).negative q • label q := by
  have hh := ExchangePattern.ofRelation_sum b label
  rw [ExchangePattern.sum_sign_smul, hb] at hh
  exact sub_eq_zero.mp hh

theorem relation_mod_sum (b : S → ℤ) (label : S → IntCoord r)
    (hb : ∑ q, b q • label q = 0) : ∑ q, b q • (label q).mod p = 0 := by
  ext j
  have hh := congrArg (fun z : ℤ ↦ (z : ZMod p)) (congrFun hb j)
  simpa [Finset.sum_apply, Pi.smul_apply, IntCoord.mod, zsmul_eq_mul] using hh

/-- An injective sample of an integer affine relation gives a bounded
exchange in the original atom family. -/
noncomputable def ofRelation (point : A → FpCoord p (r + t))
    (b : S → ℤ) (label : S → IntCoord r)
    (atom : (ExchangePattern.ofRelation b).Position → A)
    (hinj : Function.Injective atom)
    (hb : ∑ q, b q = 0) (hlabel : ∑ q, b q • label q = 0)
    (hatom : ∀ i, Coord.first r t (point (atom i)) =
      (label ((ExchangePattern.ofRelation b).label i)).mod p)
    {B : ℕ} (hsize : (∑ q, (b q).natAbs) ≤ B) : Exchange point B :=
  ofPattern (ExchangePattern.ofRelation b) point atom hinj (fun q ↦ (label q).mod p)
    hatom (relation_mass_eq b hb)
    (relation_label_eq b _ (relation_mod_sum b label hlabel))
    ((ExchangePattern.ofRelation_size b).trans_le hsize)

theorem ofRelation_shift (point : A → FpCoord p (r + t))
    (b : S → ℤ) (label : S → IntCoord r)
    (atom : (ExchangePattern.ofRelation b).Position → A)
    (hinj : Function.Injective atom)
    (hb : ∑ q, b q = 0) (hlabel : ∑ q, b q • label q = 0)
    (hatom : ∀ i, Coord.first r t (point (atom i)) =
      (label ((ExchangePattern.ofRelation b).label i)).mod p)
    {B : ℕ} (hsize : (∑ q, (b q).natAbs) ≤ B) :
    (ofRelation point b label atom hinj hb hlabel hatom hsize).shift =
      ∑ i : (ExchangePattern.ofRelation b).Position,
        (ExchangePattern.ofRelation b).sign i • Coord.last r t (point (atom i)) :=
  ofPattern_shift _ _ _ _ _ _ _ _ _

theorem ofRelation_support_avoids (point : A → FpCoord p (r + t))
    (b : S → ℤ) (label : S → IntCoord r)
    (atom : (ExchangePattern.ofRelation b).Position → A)
    (hinj : Function.Injective atom)
    (hb : ∑ q, b q = 0) (hlabel : ∑ q, b q • label q = 0)
    (hatom : ∀ i, Coord.first r t (point (atom i)) =
      (label ((ExchangePattern.ofRelation b).label i)).mod p)
    {B : ℕ} (hsize : (∑ q, (b q).natAbs) ≤ B)
    (U : Finset A) (hU : ∀ i, atom i ∉ U) :
    Disjoint (ofRelation point b label atom hinj hb hlabel hatom hsize).support U :=
  ofPattern_support_avoids _ _ _ _ _ _ _ _ _ U hU

end Relation

end Exchange
end EGZ.Expansion
