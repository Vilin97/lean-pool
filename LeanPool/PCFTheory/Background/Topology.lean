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

open Set Order Cardinal Filter Set.Notation

universe u v

namespace Ordinal

/-!
### Accumulation points and closed-below sets

`Mathlib`'s `Ordinal.IsAcc`/`Ordinal.IsClosedBelow` were deprecated in favour of the generic
topological `AccPt`/`IsClosed`. We keep working with the ordinal-specific phrasing through these
local replacements, defined exactly as the former `Mathlib` declarations together with the small
API the rest of the development relies on.
-/

/-- An ordinal is an accumulation point of a set of ordinals if it is positive and there
are elements in the set arbitrarily close to the ordinal from below. -/
def IsAccPt (o : Ordinal) (S : Set Ordinal) : Prop :=
  AccPt o (𝓟 S)

/-- A set of ordinals is closed below an ordinal if it contains all of
its accumulation points below the ordinal. -/
def IsClosedBelowPt (S : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosed (Iio o ↓∩ S)

theorem isAccPt_iff (o : Ordinal) (S : Set Ordinal) : o.IsAccPt S ↔
    o ≠ 0 ∧ ∀ p < o, (S ∩ Ioo p o).Nonempty := by
  refine SuccOrder.accPt_principal.trans ?_
  simp [isMin_iff_eq_bot]

theorem IsAccPt.forall_lt {o : Ordinal} {S : Set Ordinal} (h : o.IsAccPt S) :
    ∀ p < o, (S ∩ Ioo p o).Nonempty := ((isAccPt_iff _ _).mp h).2

theorem IsAccPt.pos {o : Ordinal} {S : Set Ordinal} (h : o.IsAccPt S) :
    0 < o := pos_iff_ne_zero.mpr ((isAccPt_iff _ _).mp h).1

theorem IsAccPt.isSuccLimit {o : Ordinal} {S : Set Ordinal} (h : o.IsAccPt S) :
    IsSuccLimit o := AccPt.isSuccLimit h

theorem IsAccPt.mono {o : Ordinal} {S T : Set Ordinal} (h : S ⊆ T) (ho : o.IsAccPt S) :
    o.IsAccPt T := AccPt.mono ho (monotone_principal h)

theorem IsAccPt.inter_Ioo_nonempty {o : Ordinal} {S : Set Ordinal} (hS : o.IsAccPt S)
    {p : Ordinal} (hp : p < o) : (S ∩ Ioo p o).Nonempty := hS.forall_lt p hp

theorem isClosedBelowPt_iff {S : Set Ordinal} {o : Ordinal} : IsClosedBelowPt S o ↔
    ∀ p < o, IsAccPt p S → p ∈ S := by
  simp [IsClosedBelowPt, IsAccPt, isClosed_iff_accPt, ← comap_principal,
    isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

theorem IsClosedBelowPt.forall_lt {S : Set Ordinal} {o : Ordinal} (h : IsClosedBelowPt S o) :
    ∀ p < o, IsAccPt p S → p ∈ S := isClosedBelowPt_iff.mp h

theorem IsClosedBelowPt.sInter {o : Ordinal} {S : Set (Set Ordinal)}
    (h : ∀ C ∈ S, IsClosedBelowPt C o) : IsClosedBelowPt (⋂₀ S) o := by
  rw [isClosedBelowPt_iff]
  exact fun p plto pAcc C CmemS ↦ (h C CmemS).forall_lt p plto <|
    AccPt.mono pAcc (monotone_principal (sInter_subset_of_mem CmemS))

-- Small.{u} → Small.{max u v} isn't properly synthed, so this instance is required.
instance {o : Ordinal.{u}} : Small.{max u v} (Iio o) := small_lift (Iio o)

/-- If `o` is a successor limit, `Iio o` has no maximal element. -/
theorem instNoMaxOrderIio {o : Ordinal} (h : IsSuccLimit o) : NoMaxOrder (Iio o) := by
  constructor
  rintro ⟨a, ha⟩
  refine ⟨⟨Order.succ a, h.succ_lt ha⟩, ?_⟩
  exact Subtype.mk_lt_mk.mpr (lt_succ a)

namespace IsAccPt

theorem inter_Ioi {o p : Ordinal} {S : Set Ordinal} (h : o.IsAccPt S) (hp : p < o) :
    o.IsAccPt (S ∩ Ioi p) := by
  rw [isAccPt_iff]
  refine ⟨h.pos.ne.symm, fun q hq ↦ ?_⟩
  obtain ⟨x, xmem⟩ := h.forall_lt (max p q) (max_lt hp hq)
  use x
  exact ⟨⟨xmem.1, (max_lt_iff.mp xmem.2.1).1⟩, ⟨(max_lt_iff.mp xmem.2.1).2, xmem.2.2⟩⟩

end IsAccPt

theorem isAccPt_iSup {o : Ordinal.{u}} {α : Iio o} (ho : IsSuccLimit o) (f : Iio o → Ordinal.{v})
    [Small.{v} (Iio o)] (hf : ∀ α β, α < β → f α < f β) {S : Set Ordinal}
    (hp : ∀ β, α < β → f β ∈ S) :
    (iSup f).IsAccPt S := by
  have hone : (1 : Ordinal) < o := one_lt_of_isSuccLimit ho
  have : NoMaxOrder ↑(Iio o) := instNoMaxOrderIio ho
  have : Nonempty (Iio o) := ⟨⟨0, ho.bot_lt⟩⟩
  rw [isAccPt_iff]
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
      obtain ⟨x, hx⟩ := IsAccPt.forall_lt b.2 a.1 altb
      have hkey : sInf (S ∩ Ioi a.1) < b.1 :=
        csInf_lt_of_lt (a := x) (OrderBot.bddBelow _) ⟨hx.1, hx.2.1⟩ hx.2.2
      have hcontra : sInf (S ∩ Ioi b.1) < b.1 := heq ▸ hkey
      exact lt_irrefl _ (lt_of_lt_of_le hcontra blt)
    · unfold f at hab
      rw [dif_pos ha, dif_neg hb] at hab
      cases hab
  · obtain ⟨x, hx⟩ := IsAccPt.forall_lt b.2 a.1 altb
    exact ha ⟨x, ⟨hx.1, hx.2.1⟩⟩


theorem isClosedBelowPt_derivedSet {S : Set Ordinal} :
    ∀ o, IsClosedBelowPt (S ∪ (derivedSet S)) o := fun o ↦ by
  rw [isClosedBelowPt_iff]
  intro p plto pacc
  right
  apply (isAccPt_iff _ _).mpr
  refine ⟨(IsAccPt.pos pacc).ne.symm, ?_⟩
  intro q qltp
  obtain ⟨x, hx⟩ := IsAccPt.forall_lt pacc q qltp
  rcases hx.1 with xs | xds
  · exact ⟨x, ⟨xs, hx.2⟩⟩
  obtain ⟨y, hy⟩ := IsAccPt.forall_lt xds q hx.2.1
  exact ⟨y, ⟨hy.1, ⟨hy.2.1, hy.2.2.trans hx.2.2⟩⟩⟩

end Ordinal
