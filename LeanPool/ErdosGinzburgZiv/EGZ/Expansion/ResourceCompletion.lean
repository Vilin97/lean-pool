/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangeResources
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangeCompletion
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.GrowthIteration
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.PrescribedCounts

/-!
# Converting exchange coverage to multiplicity bounds
-/

open scoped BigOperators

namespace EGZ.Expansion

open Classical in
/-- The multiplicity of each point among the atoms of a finite selection. -/
noncomputable def selectionWeight {A G : Type*} [Fintype A]
    (point : A → G) (J : Finset A) : G → ℕ := by
  classical
  exact pushWeight point (fun a ↦ if a ∈ J then 1 else 0)

open Classical in
theorem natMass_selectionWeight {A G : Type*} [Fintype A] [Fintype G]
    (point : A → G) (J : Finset A) : natMass (selectionWeight point J) = J.card := by
  classical
  rw [selectionWeight, natMass_pushWeight]
  simp [natMass]

open Classical in
theorem vectorSum_selectionWeight {A G : Type*} [Fintype A] [Fintype G] [AddCommMonoid G]
    (point : A → G) (J : Finset A) : vectorSum (selectionWeight point J) = ∑ a ∈ J, point a := by
  classical
  rw [selectionWeight, vectorSum, sum_pushWeight]
  simp

open Classical in
theorem exchange_position_capacity {A : Type*} [Finite A]
    {p r t B : ℕ} (point : A → FpCoord p (r + t))
    (F : Finset (Exchange point B))
    (hF : (F : Set (Exchange point B)).Pairwise
      (fun e f ↦ Disjoint e.support f.support)) :
    (∑ e : F, fun a ↦ if a ∈ e.val.left then (1 : ℕ) else 0) +
        (∑ e : F, fun a ↦ if a ∈ e.val.right then (1 : ℕ) else 0) ≤
      fun a ↦ if a ∈ usedAtoms Exchange.support F then 1 else 0 := by
  classical
  let := Fintype.ofFinite A
  classical
  intro a
  simp only [Pi.add_apply, Finset.sum_apply, ← Finset.sum_add_distrib]
  have hterm (e : F) : (if a ∈ e.val.left then (1 : ℕ) else 0) +
      (if a ∈ e.val.right then 1 else 0) = if a ∈ e.val.support then 1 else 0 := by
    have hd := Finset.disjoint_left.mp e.val.disjoint
    by_cases hl : a ∈ e.val.left <;> by_cases hr : a ∈ e.val.right <;>
      simp_all [Exchange.support]
  simp_rw [hterm]
  by_cases ha : a ∈ usedAtoms Exchange.support F
  · rw [ite_eq_left ha]
    apply Finset.sum_le_one_iff.mpr
    intro e f _ _ he hf
    have he' : a ∈ e.val.support := by simpa using he
    have hf' : a ∈ f.val.support := by simpa using hf
    refine ⟨?_, by simp [he']⟩
    apply Subtype.ext
    by_contra hne
    exact Finset.disjoint_left.mp (hF e.property f.property hne) he' hf'
  · rw [ite_eq_right ha]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro e _
    apply ite_eq_right
    intro he
    exact ha (Finset.mem_biUnion.mpr ⟨e.val, e.property, he⟩)

open Classical in
theorem exchange_weight_capacity {A : Type*} [Fintype A]
    {p r t B : ℕ} (point : A → FpCoord p (r + t))
    (F : Finset (Exchange point B))
    (hF : (F : Set (Exchange point B)).Pairwise
      (fun e f ↦ Disjoint e.support f.support)) :
    (∑ e : F, selectionWeight point e.val.left) +
        (∑ e : F, selectionWeight point e.val.right) ≤
      selectionWeight point (usedAtoms Exchange.support F) := by
  classical
  have h := pushWeight_mono point (exchange_position_capacity point F hF)
  simpa only [pushWeight_add, pushWeight_sum, selectionWeight] using h

open Classical in
theorem exchange_difference_coverage {A : Type*} [Fintype A]
    {p r t B : ℕ} [NeZero p] (point : A → FpCoord p (r + t))
    (F : Finset (Exchange point B))
    (hF : binarySums Exchange.shift F = Finset.univ) :
    ∀ v : FpCoord p (r + t), Coord.first r t v = 0 → ∃ c : F → Bool,
      (∑ e : F, if c e then
        vectorSum (selectionWeight point e.val.left) -
          vectorSum (selectionWeight point e.val.right) else 0) = v := by
  classical
  intro v hv
  have hmem : Coord.last r t v ∈ binarySums Exchange.shift F := by rw [hF]; simp
  obtain ⟨J, hJ, hsum⟩ := Finset.mem_image.mp hmem
  have hJF : J ⊆ F := Finset.mem_powerset.mp hJ
  let c : F → Bool := fun e ↦ decide (e.val ∈ J)
  refine ⟨c, ?_⟩
  simp only [vectorSum_selectionWeight]
  change (∑ e : F, if c e then e.val.difference else 0) = v
  have heq : (∑ e : F, if c e then e.val.difference else 0) = ∑ e ∈ J, e.difference := by
    simp only [c, decide_eq_true_eq]
    have hcoe := Finset.sum_coe_sort F
      (fun e : Exchange point B ↦ if e ∈ J then e.difference else 0)
    rw [hcoe]
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h ↦ hJF h)
  rw [heq]
  apply Coord.ext_first_last
  · simp [map_sum, Exchange.first_difference, hv]
  · simpa only [map_sum, Exchange.shift] using hsum

open Classical in
/-- Each quotient fibre contains at most the total mass. -/
theorem pushWeight_le_natMass {X Y : Type*} [Fintype X]
    (f : X → Y) (u : X → ℕ) (y : Y) : pushWeight f u y ≤ natMass u := by
  classical
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> omega

open Classical in
theorem selectionWeight_le_all {A G : Type*} [Fintype A]
    (point : A → G) (J : Finset A) :
    selectionWeight point J ≤ pushWeight point (fun _ ↦ 1) := by
  classical
  rw [selectionWeight]
  apply pushWeight_mono point
  intro a
  dsimp only
  split_ifs <;> norm_num

open Classical in
/-- Full coverage by disjoint exchanges gives a zero-sum submultiset when
the reserved positions fit inside the margins of the prescribed counts. -/
theorem complete_exchange_resources {A : Type*} [Fintype A]
    {p r t B : ℕ} [NeZero p] (point : A → FpCoord p (r + t))
    (w : FpCoord p (r + t) → ℕ) (hpoint : pushWeight point (fun _ ↦ 1) ≤ w)
    (F : Finset (Exchange point B))
    (hF : (F : Set (Exchange point B)).Pairwise (fun e f ↦ Disjoint e.support f.support))
    (hcover : binarySums Exchange.shift F = Finset.univ)
    (a : FpCoord p r → ℕ) (hale : a ≤ pushWeight (Coord.first r t) w)
    (ham : natMass a = p) (haz : vectorSum a = 0)
    {R : ℝ} (hused : ((usedAtoms Exchange.support F).card : ℝ) ≤ R)
    (hmargin : ∀ q, pushWeight (Coord.first r t) w q ≠ 0 →
      R ≤ (a q : ℝ) ∧ (a q : ℝ) + R ≤ pushWeight (Coord.first r t) w q) :
    HasZeroSumMultiplicity w := by
  classical
  let left : F → FpCoord p (r + t) → ℕ := fun e ↦ selectionWeight point e.val.left
  let right : F → FpCoord p (r + t) → ℕ := fun e ↦ selectionWeight point e.val.right
  let L := ∑ e, left e
  let Q := ∑ e, right e
  let used := selectionWeight point (usedAtoms Exchange.support F)
  have hcapacity : L + Q ≤ used := exchange_weight_capacity point F hF
  have husedw : used ≤ w := (selectionWeight_le_all point _).trans hpoint
  have hLused : L ≤ used := fun v ↦ (Nat.le_add_right (L v) (Q v)).trans (hcapacity v)
  have hQused : Q ≤ used := fun v ↦ (Nat.le_add_left (Q v) (L v)).trans (hcapacity v)
  have hLmass : (natMass L : ℝ) ≤ R := by
    have hh := natMass_mono hLused
    rw [natMass_selectionWeight] at hh
    exact (Nat.cast_le.mpr hh).trans hused
  have hQmass : (natMass Q : ℝ) ≤ R := by
    have hh := natMass_mono hQused
    rw [natMass_selectionWeight] at hh
    exact (Nat.cast_le.mpr hh).trans hused
  have hLpush : pushWeight (Coord.first r t) L ≤ pushWeight (Coord.first r t) w :=
    pushWeight_mono _ (hLused.trans husedw)
  have hQpush : pushWeight (Coord.first r t) Q ≤ pushWeight (Coord.first r t) w :=
    pushWeight_mono _ (hQused.trans husedw)
  have hlo : pushWeight (Coord.first r t) L ≤ a := by
    intro q
    by_cases hq : pushWeight (Coord.first r t) w q = 0
    · have hh := hLpush q
      rw [hq] at hh
      exact hh.trans (Nat.zero_le _)
    · have hh : (pushWeight (Coord.first r t) L q : ℝ) ≤ a q :=
        (Nat.cast_le.mpr (pushWeight_le_natMass _ L q)).trans (hLmass.trans (hmargin q hq).1)
      exact_mod_cast hh
  have hhi : a + pushWeight (Coord.first r t) Q ≤ pushWeight (Coord.first r t) w := by
    intro q
    by_cases hq : pushWeight (Coord.first r t) w q = 0
    · have hh := hQpush q
      have ha := hale q
      change a q + pushWeight (Coord.first r t) Q q ≤ pushWeight (Coord.first r t) w q
      rw [hq] at hh ha ⊢
      simpa only [zero_add] using Nat.add_le_add ha hh
    · have hh : (pushWeight (Coord.first r t) Q q : ℝ) ≤ R :=
        (Nat.cast_le.mpr (pushWeight_le_natMass _ Q q)).trans hQmass
      have ha := (hmargin q hq).2
      have h : (a q : ℝ) + pushWeight (Coord.first r t) Q q ≤
          pushWeight (Coord.first r t) w q := by linarith
      exact_mod_cast h
  obtain ⟨u, hu, hum, huz⟩ := complete_exchange_family_of_differences
    (Coord.first r t).toAddMonoidHom w a left right
    (hcapacity.trans husedw)
    (fun e ↦ by simp only [left, right, natMass_selectionWeight]; exact e.val.card_eq)
    (fun e ↦ by
      simp only [left, right, vectorSum_selectionWeight, LinearMap.toAddMonoidHom_coe, map_sum]
      exact e.val.first_sum_eq)
    hlo hhi haz (exchange_difference_coverage point F hcover)
  exact ⟨u, hu, hum.trans ham, huz⟩

open Classical in
/-- The prescribed integer coefficients give quotient multiplicities with
the same real margins on every nonempty quotient fibre. -/
theorem prescribed_quotient_counts_with_margin {p r t : ℕ} [NeZero p]
    (S : Finset (IntCoord r)) (w : FpCoord p (r + t) → ℕ) (α : S → ℤ)
    (hinj : Function.Injective (fun q : S ↦ q.val.mod p))
    (hsupport : ∀ v, w v ≠ 0 → ∃ q ∈ S, Coord.first r t v = q.mod p)
    (hz : (∑ q : S, α q • q.val) = 0) (hm : (∑ q : S, α q) = (p : ℤ))
    {R : ℝ} (hR : 0 ≤ R)
    (hmargin : ∀ q : S, R ≤ (α q : ℝ) ∧
      (α q : ℝ) + R ≤ pushWeight (Coord.first r t) w (q.val.mod p)) :
    ∃ a : FpCoord p r → ℕ, a ≤ pushWeight (Coord.first r t) w ∧
      natMass a = p ∧ vectorSum a = 0 ∧
      ∀ q, pushWeight (Coord.first r t) w q ≠ 0 →
        R ≤ (a q : ℝ) ∧ (a q : ℝ) + R ≤ pushWeight (Coord.first r t) w q := by
  classical
  let b : S → ℕ := fun q ↦ (α q).toNat
  have hbZ (q : S) : (b q : ℤ) = α q := Int.toNat_of_nonneg (by
    have hh := hR.trans (hmargin q).1
    exact_mod_cast hh)
  have hbR (q : S) : (b q : ℝ) = (α q : ℝ) := by exact_mod_cast hbZ q
  let a := pushWeight (fun q : S ↦ q.val.mod p) b
  have hvalue (q : S) : a (q.val.mod p) = b q := by simp [a, pushWeight, hinj.eq_iff]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · apply pushWeight_le_of_injective _ hinj
    intro q
    have hh := (hmargin q).2
    have hb : (b q : ℝ) ≤ pushWeight (Coord.first r t) w (q.val.mod p) := by rw [hbR]; linarith
    exact_mod_cast hb
  · rw [natMass_pushWeight]
    change (∑ q, b q) = p
    have hh : (∑ q, (b q : ℤ)) = (p : ℤ) := by simpa only [hbZ] using hm
    exact_mod_cast hh
  · rw [vectorSum, sum_pushWeight]
    ext i
    have hh := congrFun hz i
    simp only [Finset.sum_apply, zsmul_eq_mul, Pi.zero_apply] at hh
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod p)) hh
    simpa [Finset.sum_apply, IntCoord.mod, nsmul_eq_mul,
      Pi.mul_apply, ← hbZ] using hcast
  · intro q hq
    simp only [pushWeight] at hq
    obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    by_cases hvq : Coord.first r t v = q
    · simp only [hvq, ite_true] at hv
      obtain ⟨z, hzS, hzmod⟩ := hsupport v hv
      let z' : S := ⟨z, hzS⟩
      have heq : z'.val.mod p = q := hzmod.symm.trans hvq
      rw [← heq, hvalue, hbR]
      exact hmargin z'
    · simp only [hvq, ite_false, ne_eq, not_true_eq_false] at hv

end EGZ.Expansion
