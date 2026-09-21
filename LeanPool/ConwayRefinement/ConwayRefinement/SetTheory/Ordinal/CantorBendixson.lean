/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonRank
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.PairBounds
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.SetTheory.Ordinal.Topology

import Mathlib.Topology.Maps.Basic

/-!
# Cantor–Bendixson derivatives of ordinals

A normal function on the ordinals is a closed topological embedding. Consequently the
`a`-th derivative of the ordinal space consists, apart from stage zero, of the positive
multiples of `ω ^ a`.
-/

open Cardinal Filter Order Set Topology

universe u

public noncomputable section

namespace Order.IsNormal

/-- A normal ordinal function is a closed map. -/
theorem isClosedMap {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f) : IsClosedMap f := by
  intro s hs
  rw [Ordinal.isClosed_iff_iSup]
  intro ι hι g hg
  choose x hx hfx using hg
  have hxsup : ⨆ i, x i ∈ s := by
    rw [Ordinal.mem_iff_iSup_of_isClosed hs]
    exact ⟨ι, hι, x, hx, rfl⟩
  refine ⟨⨆ i, x i, hxsup, ?_⟩
  have hbounded : BddAbove (range x) := Ordinal.bddAbove_of_small
  rw [hf.map_iSup hbounded]
  exact iSup_congr hfx

/-- A normal ordinal function is a closed topological embedding. -/
theorem isClosedEmbedding {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f) :
    IsClosedEmbedding f := by
  rw [IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap]
  exact ⟨hf.continuous, hf.strictMono.injective, hf.isClosedMap⟩

end Order.IsNormal

namespace NatOrdinal

private theorem wpow_dvd_val_iff_le_lastExponent {a : NatOrdinal.{u}} (ha : a ≠ 0)
    {β e : NatOrdinal.{u}} (he : leastTerm a = ω^ e) :
    (ω^ β).val ∣ a.val ↔ β ≤ e := by
  rw [wpow_dvd_val_iff_partLT_eq_zero]
  constructor
  · intro hzero
    by_contra hnot
    exact partLT_ne_zero_of_leastTerm_lt ha he (lt_of_not_ge hnot) hzero
  · intro hβe
    apply partLT_eq_zero_of_forall_le
    intro t ht
    calc
      (ω^ β).val ≤ (ω^ e).val :=
        (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).mpr
          (NatOrdinal.val.le_iff_le.mpr hβe)
      _ = (leastTerm a).val := congrArg NatOrdinal.val he.symm
      _ ≤ t := val_leastTerm_le_of_mem ha ht

end NatOrdinal

namespace Ordinal

private theorem derivedSet_univ_eq :
    derivedSet (Set.univ : Set Ordinal.{u}) = {x | IsSuccLimit x} := by
  ext x
  rw [mem_derivedSet, AccPt]
  simp only [principal_univ, inf_top_eq, mem_setOf_eq]
  rw [← not_iff_not, not_neBot, ← isOpen_singleton_iff_punctured_nhds]
  exact SuccOrder.isOpen_singleton_iff

private theorem derivedSet_Ioi_zero_eq :
    derivedSet (Ioi (0 : Ordinal.{u})) = {x | IsSuccLimit x} := by
  have huniv : (Set.univ : Set Ordinal.{u}) = {0} ∪ Ioi 0 := by
    ext x
    simp
  have hsingle : derivedSet ({0} : Set Ordinal.{u}) = ∅ := by
    ext x
    simp only [mem_derivedSet, mem_empty_iff_false, iff_false]
    exact fun h ↦ (finite_singleton (0 : Ordinal.{u})).not_infinite
      (Set.Infinite.of_accPt h)
  rw [← derivedSet_univ_eq, huniv, derivedSet_union, hsingle, empty_union]

def positivePrincipalMultiples (a : Ordinal.{u}) : Set Ordinal.{u} :=
  (fun x ↦ omega0 ^ a * x) '' Ioi 0

/-- Membership in the positive multiples of `ω ^ a`. -/
theorem mem_positivePrincipalMultiples {a x : Ordinal.{u}} :
    x ∈ positivePrincipalMultiples a ↔ ∃ q > 0, omega0 ^ a * q = x := Iff.rfl

private theorem positivePrincipalMultiples_isClosed (a : Ordinal.{u}) :
    IsClosed (positivePrincipalMultiples a) := by
  apply (isNormal_mul_right (opow_pos a omega0_pos)).isClosedMap
  have hset : Ioi (0 : Ordinal.{u}) = Ici 1 := by
    ext x
    change 0 < x ↔ (1 : Ordinal.{u}) ≤ x
    exact one_le_iff_pos.symm
  rw [hset]
  exact isClosed_Ici

private theorem derivedSet_positivePrincipalMultiples (a : Ordinal.{u}) :
    derivedSet (positivePrincipalMultiples a) = positivePrincipalMultiples (a + 1) := by
  let f : Ordinal.{u} → Ordinal.{u} := fun x ↦ omega0 ^ a * x
  have hf : IsNormal f := isNormal_mul_right (opow_pos a omega0_pos)
  have himage : derivedSet (f '' Ioi 0) = f '' derivedSet (Ioi 0) := by
    apply Set.Subset.antisymm
    · exact hf.isClosedMap.derivedSet_image_subset _
    · exact hf.continuous.image_derivedSet hf.strictMono.injective
  rw [positivePrincipalMultiples, himage, derivedSet_Ioi_zero_eq,
    positivePrincipalMultiples]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change IsSuccLimit y at hy
    obtain ⟨z, rfl⟩ := isSuccPrelimit_iff_omega0_dvd.mp hy.isSuccPrelimit
    refine ⟨z, ?_, ?_⟩
    · change 0 < z
      exact pos_iff_ne_zero.mpr fun hz ↦ hy.ne_bot (by simp [hz])
    · symm
      change omega0 ^ a * (omega0 * z) = omega0 ^ (a + 1) * z
      rw [show a + 1 = Order.succ a by simp, opow_succ, mul_assoc]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨omega0 * z, ?_, ?_⟩
    · change IsSuccLimit (omega0 * z)
      refine ⟨?_,
        isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _)⟩
      rw [isMin_iff_eq_bot, Ordinal.bot_eq_zero]
      exact mul_ne_zero omega0_ne_zero hz.ne'
    · change omega0 ^ a * (omega0 * z) = omega0 ^ (a + 1) * z
      rw [show a + 1 = Order.succ a by simp, opow_succ, mul_assoc]

private theorem iInter_positivePrincipalMultiples {a : Ordinal.{u}} (ha : IsSuccLimit a) :
    (⋂ i : Iio a, positivePrincipalMultiples i.1) = positivePrincipalMultiples a := by
  ext x
  constructor
  · intro hx
    have hxi (i : Iio a) : x ∈ positivePrincipalMultiples i.1 := mem_iInter.mp hx i
    have hx0 : x ≠ 0 := by
      let i : Iio a := ⟨0, ha.bot_lt⟩
      obtain ⟨y, hy, hxy⟩ := hxi i
      rw [← hxy]
      exact mul_ne_zero (opow_ne_zero _ omega0_ne_zero) hy.ne'
    let n : NatOrdinal.{u} := NatOrdinal.of x
    have hn0 : n ≠ 0 := by
      intro hn
      apply hx0
      have := congrArg NatOrdinal.val hn
      simpa [n] using this
    obtain ⟨e, he⟩ := NatOrdinal.exists_leastTerm_eq_wpow
      (a := n) hn0
    have hie : ∀ i < a, NatOrdinal.of i ≤ e := by
      intro i hi
      obtain ⟨y, hy, hxy⟩ := hxi ⟨i, hi⟩
      apply (NatOrdinal.wpow_dvd_val_iff_le_lastExponent
        (a := n) hn0 he).mp
      change omega0 ^ i ∣ x
      exact ⟨y, hxy.symm⟩
    have hae : a ≤ e.val := by
      by_contra hnot
      have hea : e.val < a := lt_of_not_ge hnot
      have hsucc : e.val + 1 < a := ha.succ_lt hea
      have := NatOrdinal.val.le_iff_le.mpr (hie (e.val + 1) hsucc)
      simpa using (not_le_of_gt (Order.lt_succ e.val)) this
    obtain ⟨q, hq⟩ := (NatOrdinal.wpow_dvd_val_iff_le_lastExponent
      (a := n) (β := NatOrdinal.of a) hn0 he).mpr
        (NatOrdinal.val.le_iff_le.mp hae)
    refine ⟨q, ?_, ?_⟩
    · change 0 < q
      apply pos_iff_ne_zero.mpr
      intro hq0
      apply hx0
      calc
        x = (ω^ (NatOrdinal.of a)).val * q := by simpa only [n, NatOrdinal.val_of] using hq
        _ = 0 := by rw [hq0, mul_zero]
    · change omega0 ^ a * q = x
      simpa only [n, NatOrdinal.val_wpow, NatOrdinal.val_of] using hq.symm
  · intro hx
    apply mem_iInter.mpr
    intro i
    obtain ⟨y, hy, hxy⟩ := hx
    refine ⟨(omega0 ^ (a - i.1)) * y, ?_, ?_⟩
    · exact mul_pos (opow_pos _ omega0_pos) hy
    · change omega0 ^ i.1 * (omega0 ^ (a - i.1) * y) = x
      rw [← mul_assoc, ← opow_add, Ordinal.add_sub_cancel_of_le i.2.le]
      exact hxy

private theorem positivePrincipalMultiples_zero :
    positivePrincipalMultiples (0 : Ordinal.{u}) = Ioi 0 := by
  ext x
  simp [positivePrincipalMultiples]

/-- The `a`-th derivative of the ordinal space is the set of positive multiples of `ω ^ a`,
except that stage zero is the whole space. -/
theorem cantorBendixson_top_eq (a : Ordinal.{u}) :
    ((⊤ : TopologicalSpace.Closeds Ordinal.{u}).cantorBendixson a : Set Ordinal.{u}) =
      if a = 0 then Set.univ else positivePrincipalMultiples a := by
  induction a using Ordinal.limitRecOn with
  | zero => simp
  | add_one a ih =>
      rw [TopologicalSpace.Closeds.cantorBendixson_add_one]
      rw [TopologicalSpace.Closeds.coe_derived]
      rw [ih]
      by_cases ha : a = 0
      · subst a
        simp only [zero_add, if_true, ite_eq_right one_ne_zero]
        rw [derivedSet_univ_eq, ← derivedSet_Ioi_zero_eq,
          ← positivePrincipalMultiples_zero,
          derivedSet_positivePrincipalMultiples]
        simp
      · simp only [ite_eq_right ha]
        rw [derivedSet_positivePrincipalMultiples]
        simp [ha]
  | limit a ha ih =>
      rw [TopologicalSpace.Closeds.cantorBendixson_limit _ _ ha]
      simp only [TopologicalSpace.Closeds.coe_iInf]
      ext x
      simp only [mem_iInter]
      simp only [ite_eq_right (show a ≠ 0 from ha.ne_bot)]
      constructor
      · intro hx
        apply (Set.ext_iff.mp (iInter_positivePrincipalMultiples ha) x).mp
        apply mem_iInter.mpr
        intro i
        by_cases hi : i.1 = 0
        · rw [hi, positivePrincipalMultiples_zero]
          have h1a : (1 : Ordinal.{u}) < a := by
            simpa using ha.succ_lt ha.bot_lt
          have hstage := hx ⟨(1 : Ordinal.{u}), h1a⟩
          rw [ih (1 : Ordinal.{u}) h1a, ite_eq_right one_ne_zero] at hstage
          obtain ⟨y, hy, hxy⟩ := hstage
          change 0 < x
          exact pos_iff_ne_zero.mpr fun hx0 ↦ by
            rw [hx0] at hxy
            exact (mul_ne_zero (opow_ne_zero _ omega0_ne_zero) hy.ne') hxy
        · simpa only [ih i.1 i.2, ite_eq_right hi] using hx i
      · intro hx i
        rw [ih i.1 i.2]
        by_cases hi : i.1 = 0
        · simp [hi]
        · rw [ite_eq_right hi]
          have hall := (Set.ext_iff.mp (iInter_positivePrincipalMultiples ha) x).mpr hx
          exact mem_iInter.mp hall i

end Ordinal
