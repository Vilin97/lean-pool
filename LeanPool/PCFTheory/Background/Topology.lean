/-
Copyright (c) 2026 YnirPaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YnirPaz
-/

import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.DerivedSet
import LeanPool.PCFTheory.Background.Ordinal

/-!
# Topological results on ordinals

A handful of order-topological facts used to set up the theory of clubs.
-/

open Set Order Cardinal

universe u v

namespace Ordinal

-- Small.{u} → Small.{max u v} isn't properly synthed, so this instance is required.
instance {o : Ordinal.{u}} : Small.{max u v} (Iio o) := small_lift (Iio o)

/-- If `o` is a successor limit, `Iio o` has no maximal element. -/
theorem instNoMaxOrderIio {o : Ordinal} (h : IsSuccLimit o) : NoMaxOrder (Iio o) := by
  constructor
  rintro ⟨a, ha⟩
  refine ⟨⟨Order.succ a, h.succ_lt ha⟩, ?_⟩
  exact Subtype.mk_lt_mk.mpr (lt_succ a)

namespace IsAcc

theorem inter_Ioi {o p : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) (hp : p < o) :
    o.IsAcc (S ∩ Ioi p) := by
  rw [isAcc_iff]
  refine ⟨h.pos.ne.symm, fun q hq ↦ ?_⟩
  obtain ⟨x, xmem⟩ := h.forall_lt (max p q) (max_lt hp hq)
  use x
  exact ⟨⟨xmem.1, (max_lt_iff.mp xmem.2.1).1⟩, ⟨(max_lt_iff.mp xmem.2.1).2, xmem.2.2⟩⟩

end IsAcc

theorem isAcc_iSup {o : Ordinal.{u}} {α : Iio o} (ho : IsSuccLimit o) (f : Iio o → Ordinal.{v})
    [Small.{v} (Iio o)] (hf : ∀ α β, α < β → f α < f β) {S : Set Ordinal}
    (hp : ∀ β, α < β → f β ∈ S) :
    (iSup f).IsAcc S := by
  have hone : (1 : Ordinal) < o := one_lt_of_isSuccLimit ho
  have : NoMaxOrder ↑(Iio o) := instNoMaxOrderIio ho
  have : Nonempty (Iio o) := ⟨⟨0, ho.bot_lt⟩⟩
  rw [isAcc_iff]
  constructor
  · have flt := hf ⟨0, ho.bot_lt⟩ ⟨1, hone⟩ (Subtype.mk_lt_mk.mpr zero_lt_one)
    have lesup := le_ciSup (f := f) bddAbove_of_small ⟨1, hone⟩
    intro h
    have := h ▸ bot_lt_of_lt (flt.trans_le lesup)
    exact not_lt_bot this
  · intro β hβ
    obtain ⟨γ, hγ⟩ := (lt_ciSup_iff bddAbove_of_small).mp hβ
    use f (succ (max α γ))
    constructor
    · exact hp (succ (max α γ)) <| (le_max_left α γ).trans_lt (lt_succ (max α γ))
    · constructor
      · exact hγ.trans <| hf _ _ <| (le_max_right α γ).trans_lt (lt_succ (max α γ))
      · apply (lt_ciSup_iff bddAbove_of_small).mpr
        use succ (succ (max α γ))
        exact hf _ _ (lt_succ _)

open Classical in
theorem mk_derivedSet_le (S : Set Ordinal) : #(derivedSet S) ≤ #S := by
  by_cases hS : S.Finite
  · exact mk_le_mk_of_subset <| (isClosed_iff_derivedSet_subset _).mp hS.isClosed
  /- `f` sends each accumulation point of `S` to the smallest element of `S` above it,
  if it exists. This is an injection from the accumulation points to `Option S`. -/
  let f : derivedSet S → Option S := fun δ ↦ if h : (S ∩ Ioi δ).Nonempty then
    some ⟨sInf (S ∩ Ioi δ.1), inter_subset_left (csInf_mem h)⟩
    else none
  suffices hf : Function.Injective f by
    convert mk_le_of_injective hf using 1
    rw [mk_option]
    refine (add_one_of_aleph0_le ?_).symm
    exact infinite_iff.mp (infinite_coe_iff.mpr hS)
  intro a b hab
  apply Subtype.ext
  -- Helper: derive a contradiction when `a.1 < b.1` (in any LT instance) and `f a = f b`.
  suffices aux : ∀ (a b : derivedSet S),
      (a.1 < b.1 : Prop) → f a = f b → a.1 = b.1 by
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · exact aux a b h hab
    · exact h
    · exact (aux b a h hab.symm).symm
  clear hab a b
  intro a b altb hab
  exfalso
  by_cases ha : (S ∩ Ioi a.1).Nonempty
  · by_cases hb : (S ∩ Ioi b.1).Nonempty
    · unfold f at hab
      rw [dif_pos ha, dif_pos hb, Option.some_inj] at hab
      have heq : sInf (S ∩ Ioi a.1) = sInf (S ∩ Ioi b.1) := congrArg Subtype.val hab
      have blt : b.1 ≤ sInf (S ∩ Ioi b.1) := le_csInf hb fun _ ⟨_, h⟩ ↦ h.le
      obtain ⟨x, hx⟩ := IsAcc.forall_lt b.2 a.1 altb
      have hkey : sInf (S ∩ Ioi a.1) < b.1 :=
        csInf_lt_of_lt (a := x) (OrderBot.bddBelow _) ⟨hx.1, hx.2.1⟩ hx.2.2
      have hcontra : sInf (S ∩ Ioi b.1) < b.1 := heq ▸ hkey
      exact lt_irrefl _ (lt_of_lt_of_le hcontra blt)
    · unfold f at hab
      rw [dif_pos ha, dif_neg hb] at hab
      cases hab
  · obtain ⟨x, hx⟩ := IsAcc.forall_lt b.2 a.1 altb
    exact ha ⟨x, ⟨hx.1, hx.2.1⟩⟩


theorem isClosedBelow_derivedSet {S : Set Ordinal} :
    ∀ o, IsClosedBelow (S ∪ (derivedSet S)) o := fun o ↦ by
  rw [isClosedBelow_iff]
  intro p plto pacc
  right
  apply (isAcc_iff _ _).mpr
  refine ⟨(IsAcc.pos pacc).ne.symm, ?_⟩
  intro q qltp
  obtain ⟨x, hx⟩ := IsAcc.forall_lt pacc q qltp
  rcases hx.1 with xs | xds
  · exact ⟨x, ⟨xs, hx.2⟩⟩
  obtain ⟨y, hy⟩ := IsAcc.forall_lt xds q hx.2.1
  exact ⟨y, ⟨hy.1, ⟨hy.2.1, hy.2.2.trans hx.2.2⟩⟩⟩

end Ordinal
