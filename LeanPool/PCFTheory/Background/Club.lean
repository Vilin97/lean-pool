/-
Copyright (c) 2026 YnirPaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YnirPaz
-/

import LeanPool.PCFTheory.Background.Cofinality
import LeanPool.PCFTheory.Background.Topology

/-!
# Club and stationary sets

This file sets up the basic theory of clubs (closed and unbounded sets) and stationary sets.

## Main definitions

* `Ordinal.IsClosed`: A set of ordinals `S` is closed in `o` if `S ⊆ Iio o`
  and `S` contains every `x < o` such that `x.IsAcc S`.
* `Ordinal.IsClub`: A set of ordinals `S` is a club in `o` if
  it is closed in `o` and unbounded in `o`.

## Main results

* `isClub_sInter`: The intersection of fewer than `o.cof` clubs in `o` is a club in `o`.
-/

noncomputable section

open Cardinal Set Order Filter

universe u v

namespace Ordinal

/-- A set of ordinals is a club below an ordinal if it is closed and unbounded in it. -/
def IsClub (C : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosedBelowPt C o ∧ IsAccPt o C

/-- A club below an ordinal `α` is a bundled `IsClub` set: closed and unbounded. -/
structure Club (α : Ordinal) where
  /-- The underlying set of ordinals. -/
  carrier : Set Ordinal
  /-- The proof that the carrier is a club below `α`. -/
  isClub : IsClub carrier α

instance {α : Ordinal} : SetLike (Club α) Ordinal where
  coe := Club.carrier
  coe_injective s t h := by cases s; cases t; congr

instance {α : Ordinal} : HasSubset (Club α) where
  Subset := fun C D ↦ C.carrier ⊆ D.carrier

instance {α : Ordinal} : HasSSubset (Club α) where
  SSubset := fun C D ↦ C.carrier ⊂ D.carrier

instance {α : Ordinal} : IsNonstrictStrictOrder (Club α) (· ⊆ ·) (· ⊂ ·) where
  right_iff_left_not_left _ _ := Iff.rfl

instance {α : Ordinal} : Std.Antisymm ((· ⊆ ·) : Club α → Club α → Prop) where
  antisymm _ _ h h' := SetLike.coe_injective (Subset.antisymm h h')


theorem isClub_iff {C : Set Ordinal} {o : Ordinal} : IsClub C o
    ↔ ((∀ p < o, IsAccPt p C → p ∈ C) ∧ (o ≠ 0 ∧ ∀ p < o, (C ∩ Ioo p o).Nonempty)) :=
  and_congr isClosedBelowPt_iff (isAccPt_iff _ _)

namespace IsClub

theorem isClosedBelowPt {C : Set Ordinal} {o : Ordinal} (h : IsClub C o) :
    IsClosedBelowPt C o := h.1

theorem isAcc {C : Set Ordinal} {o : Ordinal} (h : IsClub C o) : IsAccPt o C := h.2

theorem pos {C : Set Ordinal} {o : Ordinal} (h : IsClub C o) : 0 < o :=
  h.isAcc.pos

theorem ne_zero {C : Set Ordinal} {o : Ordinal} {h : IsClub C o} : o ≠ 0 :=
  h.pos.ne.symm

theorem mem_of_isAcc {C : Set Ordinal} {o p : Ordinal} (h : IsClub C o) (hp : p < o) :
    IsAccPt p C → p ∈ C := (isClub_iff.mp h).1 _ hp

theorem forall_lt {o : Ordinal} {S : Set Ordinal} (h : o.IsClub S) :
    ∀ p < o, (S ∩ Ioo p o).Nonempty := ((isAccPt_iff _ _).mp h.isAcc).2

theorem inter_Iio {C : Set Ordinal} {o : Ordinal} (h : IsClub C o) :
    IsClub (C ∩ Iio o) o := by
  apply isClub_iff.mpr
  constructor
  · exact fun p hpo hp ↦ ⟨h.mem_of_isAcc hpo (hp.mono inter_subset_left), hpo⟩
  · refine ⟨h.pos.ne.symm, fun p hpo ↦ ?_⟩
    convert h.isAcc.inter_Ioo_nonempty hpo using 1
    ext; simp_all

end IsClub

theorem isClub_univ {α : Ordinal} (h : IsSuccLimit α) : IsClub Set.univ α := by
  refine isClub_iff.mpr ⟨?_, ?_, ?_⟩
  · exact fun _ _ _ ↦ mem_univ _
  · exact h.bot_lt.ne.symm
  · exact fun p plt ↦ ⟨succ p, ⟨mem_univ _, ⟨lt_succ _, h.succ_lt plt⟩⟩⟩

/-- The trivial club consisting of every ordinal below a successor-limit `α`. -/
def univClub {α : Ordinal} (h : IsSuccLimit α) : Club α := ⟨Set.univ, isClub_univ h⟩

namespace IsClub

theorem isClub_of_isAcc {α β : Ordinal} {C : Set Ordinal} (h : β < α) (hC : IsClub C α)
    (hacc : IsAccPt β C) : IsClub C β := by
  refine isClub_iff.mpr ⟨?_, ?_, ?_⟩
  · exact fun p plt hp ↦ hC.mem_of_isAcc (plt.trans h) hp
  · exact hacc.isSuccLimit.bot_lt.ne.symm
  · exact fun p hp ↦ hacc.forall_lt p hp

end IsClub



variable {o : Ordinal.{u}} {S : Set (Set Ordinal)}
variable {ι : Type u} {f : ι → Set Ordinal}

/-- Given less than `o.cof` unbounded sets in `o` and some `q < o`, there is a `q < p < o`
  such that `Ioo q p` contains an element of every unbounded set. -/
theorem exists_above_of_lt_cof {p : Ordinal} (h : p < o) (hSemp : Nonempty S)
    (hSacc : ∀ U ∈ S, o.IsAccPt U) (hScard : #S < Cardinal.lift.{u + 1, u} o.cof) :
    ∃ q < o, p < q ∧ ∀ U ∈ S, (U ∩ Ioo p q).Nonempty := by
  rw [lift_cof] at hScard
  have oLim : IsSuccLimit o := hSemp.casesOn fun ⟨T, hT⟩ ↦ (hSacc T hT).isSuccLimit
  let f : ↑S → Ordinal := fun U ↦ lift.{u + 1, u} (sInf (U ∩ (Ioo p o)))
  have infMem : ∀ U : S, sInf (↑U ∩ Ioo p o) ∈ ↑U ∩ Ioo p o := fun U ↦
    csInf_mem ((hSacc U.1 U.2).inter_Ioo_nonempty h : (↑U ∩ Ioo p o).Nonempty)
  have flto : ∀ U : S, f U < lift.{u + 1, u} o := fun U ↦ by
    simp_all only [mem_inter_iff, mem_Ioo, lift_lt, f]
  set q := (iSup f) + 1 with qdef
  have qlto : q < lift.{u + 1, u} o :=
    (isSuccLimit_lift.{u + 1, u}.mpr oLim).succ_lt (iSup_lt_of_lt_cof hScard flto)
  rcases mem_range_lift_of_le qlto.le with ⟨q', hq'⟩
  use q', lift_lt.mp (hq' ▸ qlto)
  have fltq : ∀ U, f U < q := fun U ↦ by
    convert lt_of_le_of_lt (le_ciSup (by apply bddAbove_of_small) U) (qdef ▸ lt_add_one (iSup f))
  constructor <;> try constructor
  · rcases hSemp with ⟨U, hU⟩
    have pltf : lift.{u + 1, u} p < f ⟨U, hU⟩ :=
      lift_lt.mpr (mem_of_mem_inter_right (infMem ⟨U, hU⟩)).1
    have := lt_of_lt_of_le pltf (fltq ⟨U, hU⟩).le
    rwa [← hq', lift_lt] at this
  intro U hU
  specialize infMem ⟨U, hU⟩
  specialize fltq ⟨U, hU⟩
  have : f ⟨U, hU⟩ ∈ Ioo (lift.{u + 1, u} p) q := ⟨lift_lt.mpr infMem.2.1, fltq⟩
  rw [← hq'] at fltq
  rcases mem_range_lift_of_le fltq.le with ⟨fUdown, fUlift⟩
  use fUdown
  constructor
  · simp_all only [lift_inj, mem_inter_iff, f]
  · exact ⟨lift_lt.mp <| fUlift ▸ (this.1), lift_lt.mp (hq'.symm ▸ (fUlift ▸ this).2)⟩

/--
Given a limit ordinal `o` and a property on pairs of ordinals `P`, such that
for any `p < o` there is a `q < o` above `p` so that `P p q`, we can construct
an increasing `ω`-sequence below `o` that satisfies `P` between every 2 consecutive elements.
Additionaly, the sequence can begin arbitrarily high in `o`. That is, above any `r < o`.
-/
theorem exists_omega0_seq_succ_prop (opos : 0 < o) {P : Ordinal → Ordinal → Prop}
    (hP : ∀ p : Iio o, ∃ q, (p < q ∧ P p q)) (r : Iio o) : ∃ f : (Iio ω) → Iio o,
    (∀ i, P (f i) (f (succ i))) ∧ (∀ i j, (i < j) → f i < f j)
    ∧ r < f ⟨0, omega0_pos⟩ := by
  have oLim : IsSuccLimit o := isSuccLimit_iff'.mpr <|
      ⟨opos.ne.symm, fun a alto ↦ (hP ⟨a, alto⟩).casesOn fun r hr ↦
    lt_of_le_of_lt (succ_le_of_lt hr.1) r.2⟩
  classical
  let H₂ : (p : Iio ω) → (Iio o) → (Iio o) := fun _ fp ↦ Classical.choose (hP fp)
  let H₃ : (w : Iio ω) → IsSuccLimit w.1 → ((o' : Iio ω) → o' < w → (Iio o)) → (Iio o) :=
    fun _ _ _ ↦ ⟨0, oLim.bot_lt⟩
  let f : Iio ω → Iio o := fun x ↦ @boundedLimitRec' ω isSuccLimit_omega0 (fun _ ↦ Iio o) x
    (succ r) H₂ H₃
  -- Key relation: f at successor equals chosen witness
  have f_succ_eq : ∀ n : Iio ω,
      f ⟨Order.succ n.1, isSuccLimit_omega0.succ_lt n.2⟩ = Classical.choose (hP (f n)) := by
    intro n
    change boundedLimitRec' isSuccLimit_omega0 ⟨Order.succ n.1, _⟩ (succ r) H₂ H₃ =
      Classical.choose (hP (f n))
    rw [@boundedLimitRec'_succ ω isSuccLimit_omega0 (fun _ ↦ Iio o) n (succ r) H₂ H₃]
  -- The successor in Iio ω
  have succ_eq : ∀ n : Iio ω,
      (succ n : Iio ω) = ⟨Order.succ n.1, isSuccLimit_omega0.succ_lt n.2⟩ := fun n ↦
    succ_Iio isSuccLimit_omega0.isSuccPrelimit
  have f_succ : ∀ n : Iio ω, f (succ n) = Classical.choose (hP (f n)) := fun n ↦ by
    rw [succ_eq n, f_succ_eq n]
  use f
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [f_succ n]
    exact (Classical.choose_spec (hP (f n))).2
  · have aux : ∀ i, f i < f (succ i) := fun i ↦ by
      rw [f_succ i]
      exact (Classical.choose_spec (hP (f i))).1
    exact strictMono_of_succ_lt_omega0 f aux
  · have hf0 : f ⟨0, omega0_pos⟩ = succ r :=
      @boundedLimitRec'_zero ω isSuccLimit_omega0 ((fun _ ↦ Iio o)) (succ r) H₂ H₃
    rw [hf0]
    change r.1 < (Order.succ r : Iio o).1
    rw [coe_succ_Iio oLim.isSuccPrelimit]
    exact lt_succ r.1

/-- If between every 2 consecutive elements of a weakly increasing `δ`-sequence
  there is an element of `C`, and `δ` is a limit ordinal,
  then the supremum of the sequence is an accumulation point of `C`. -/
theorem isAccPt_iSup_of_between {δ : Ordinal.{u}} (C : Set Ordinal) (δLim : IsSuccLimit δ)
    (s : Iio δ → Ordinal.{max u v}) (sInc : ∀ o, s o < s (succ o))
    (h : ∀ o, (C ∩ (Icc (s o) (s (succ o)))).Nonempty) :
    IsAccPt (iSup s) C := by
  rw [isAccPt_iff]
  constructor
  · rw [← pos_iff_ne_zero, Ordinal.lt_iSup_iff]
    use ⟨1, one_lt_of_isSuccLimit δLim⟩
    refine lt_of_le_of_lt (bot_le (a := s ⟨0, δLim.bot_lt⟩)) ?_
    convert sInc ⟨0, δLim.bot_lt⟩
    rw [coe_succ_Iio δLim.isSuccPrelimit]
    exact (zero_add (1 : Ordinal)).symm
  intro p hp
  rw [Ordinal.lt_iSup_iff] at hp
  obtain ⟨r, hr⟩ := hp
  obtain ⟨q, hq⟩ := h r
  use q
  refine ⟨hq.1, ⟨hr.trans_le hq.2.1, ?_⟩⟩
  rw [Ordinal.lt_iSup_iff]
  exact ⟨succ (succ r), hq.2.2.trans_lt (sInc (succ r))⟩

namespace IsClub

/--
The intersection of less than `o.cof` clubs in `o` is a club in `o`.
-/
theorem sInter (hCof : ℵ₀ < o.cof) (hS : ∀ C ∈ S, IsClub C o) (hSemp : S.Nonempty)
    (Scard : #S < Cardinal.lift.{u + 1, u} o.cof) : IsClub (⋂₀ S) o := by
  refine ⟨IsClosedBelowPt.sInter (fun C CmemS ↦ (hS C CmemS).1), (isAccPt_iff _ _).mpr ?_⟩
  have nonemptyS : Nonempty S := hSemp.to_subtype
  have oLim : IsSuccLimit o := one_lt_cof_iff.mp (one_lt_aleph0.trans_le hCof.le)
  use oLim.bot_lt.ne.symm
  intro p plto
  let P : Ordinal → Ordinal → Prop := fun p q ↦ ∀ C ∈ S, (C ∩ Ioo p q).Nonempty
  have auxP : ∀ p : Iio o, ∃ q, p < q ∧ P p q := fun p ↦ by
    rcases exists_above_of_lt_cof p.2 nonemptyS (fun U hU ↦ (hS U hU).2) Scard with ⟨q, hq⟩
    use ⟨q, hq.1⟩, hq.2.1, hq.2.2
  rcases exists_omega0_seq_succ_prop.{u, u} oLim.bot_lt auxP ⟨p, plto⟩ with ⟨f, hf⟩
  let sup := iSup (fun n ↦ (f n).1)
  use sup
  have suplt : sup < o := by
    apply iSup_Iio_lt_ord (fun n ↦ (f n).2)
    rwa [Cardinal.lift_id, Cardinal.lift_id, card_omega0]
  constructor
  · intro s hs
    apply (hS s hs).1.forall_lt sup suplt
    apply isAccPt_iSup_of_between
    · exact isSuccLimit_omega0
    · intro n
      rw [@Subtype.coe_lt_coe]
      convert hf.2.1 n (succ n) ?_
      · apply Subtype.coe_lt_coe.mp
        rw [coe_succ_of_mem]
        · exact lt_succ n.1
        exact isSuccLimit_omega0.succ_lt n.2
    · intro n
      apply (hf.1 n s hs).mono
      exact inter_subset_inter_right _ Ioo_subset_Icc_self
  · constructor
    · rw [Ordinal.lt_iSup_iff]
      exact ⟨⟨0, omega0_pos⟩, hf.2.2⟩
    · exact suplt

theorem iInter_lift {ι : Type v} {f : ι → Set Ordinal.{u}} [Nonempty ι] (hCof : ℵ₀ < o.cof)
    (hf : ∀ i, IsClub (f i) o) (ιCard : Cardinal.lift.{u} #ι < Cardinal.lift.{v} o.cof) :
    IsClub (⋂ i, f i) o := by
  refine IsClub.sInter (S := range f) hCof (fun y ⟨x, hx⟩ ↦ hx ▸ hf x) (range_nonempty f) ?_
  have := mk_range_le_lift (f := f)
  rw [← Cardinal.lift_lt.{_, max v (u + 1)}]
  have aux : Cardinal.lift.{max v (u + 1), u + 1} #↑(range f) =
      Cardinal.lift.{max v, u + 1} #↑(range f) := by
    convert (@lift_umax_eq.{u + 1, u + 1, v} #(range f) #(range f)).mpr rfl
    exact congrFun Cardinal.lift_umax.{u + 1, v}.symm _
  rw [aux]
  apply this.trans_lt
  convert lift_strictMono.{max u v, max (u + 1) v} ιCard
  · rw [Cardinal.lift_lift, Cardinal.lift_umax.{v, u + 1}]
  · rw [Cardinal.lift_lift, Cardinal.lift_lift]

theorem iInter [Nonempty ι] (hCof : ℵ₀ < o.cof) (hf : ∀ i, IsClub (f i) o)
    (ιCard : #ι < o.cof) : IsClub (⋂ i, f i) o :=
  IsClub.iInter_lift hCof hf (Cardinal.lift_lt.mpr ιCard)

theorem inter {Ϟ : Ordinal.{u}} (hCof : ℵ₀ < Ϟ.cof) {C D : Set Ordinal}
    (hC : IsClub C Ϟ) (hD : IsClub D Ϟ) : IsClub (C ∩ D) Ϟ := by
  rw [← sInter_pair C D]
  refine IsClub.sInter hCof ?_ ⟨C, mem_insert C _⟩ ?_
  · intro E hE
    rcases hE with hE | hE
    · exact hE ▸ hC
    · rcases hE with rfl
      exact hD
  · by_cases h : C = D
    · subst h
      simp only [pair_eq_singleton, mk_singleton]
      rw [show (1 : Cardinal.{u + 1}) = Cardinal.lift.{u + 1, u} 1 by simp, Cardinal.lift_lt]
      exact one_lt_aleph0.trans hCof
    · have hne : C ∉ ({D} : Set (Set Ordinal)) := by simp [h]
      rw [show ({C, D} : Set (Set Ordinal)) = insert C {D} from rfl,
        Cardinal.mk_insert hne, mk_singleton]
      rw [show ((1 : Cardinal.{u + 1}) + 1) = Cardinal.lift.{u + 1, u} 2 by simp; norm_num,
        Cardinal.lift_lt]
      exact two_lt_aleph0.trans hCof

theorem iInter_Iio {Ϟ o : Ordinal.{u}} {p : Iio o} {f : Iio p → Set Ordinal}
    (hϞ : ℵ₀ < Ϟ.cof) (h : p.1.card < Ϟ.cof) (hf : ∀ x, IsClub (f x) Ϟ) :
    IsClub (⋂ α, f α) Ϟ := by
  by_cases h : 0 < p.1
  · have : Nonempty (Iio p) := ⟨⟨0, h.trans p.2⟩, h⟩
    apply IsClub.iInter_lift hϞ hf
    · rwa [mk_Iio_subtype, Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, Cardinal.lift_lt]
  · have hp0 : p.1 = 0 := (eq_zero_or_pos p.1).resolve_right h
    have : IsEmpty (Iio p) := isEmpty_iff.mpr fun ⟨x, h'⟩ ↦ by
      have h'' : x.1 < p.1 := h'
      rw [hp0] at h''
      exact (bot_le (a := x.1)).not_gt h''
    rw [iInter_of_empty]
    convert isClub_univ <| one_lt_cof_iff.mp (one_lt_aleph0.trans_le hϞ.le)

end IsClub


namespace IsClub

/-- Accumulation points of a club form a club. -/
theorem derivedSet {α : Ordinal.{u}} {C : Set Ordinal} (hcof : ℵ₀ < α.cof) (h : IsClub C α) :
    IsClub (derivedSet C) α := by
  rw [isClub_iff]
  refine ⟨?_, h.ne_zero, ?_⟩
  · intro p pltα pacc
    change IsAccPt _ _
    rw [isAccPt_iff]
    refine ⟨pacc.pos.ne.symm, ?_⟩
    intro q qltp
    obtain ⟨x, hx⟩ := pacc.forall_lt q qltp
    exact ⟨x, ⟨h.mem_of_isAcc (hx.2.2.trans pltα) hx.1, hx.2⟩⟩
  · intro p pltα
    obtain ⟨f, hf⟩ := exists_omega0_seq_succ_prop.{_, 0} (bot_lt_of_lt pltα) (P := fun _ x ↦ x ∈ C)
      (fun p ↦ by
        obtain ⟨x, hx⟩ := h.forall_lt p p.2
        exact ⟨⟨x, hx.2.2⟩, ⟨hx.2.1, hx.1⟩⟩)
      ⟨p, pltα⟩
    use iSup (fun x ↦ f x)
    constructor
    · apply isAccPt_iSup (o := ω) (α := ⟨0, omega0_pos⟩) isSuccLimit_omega0
      · exact hf.2.1
      · intro n h
        convert hf.1 ⟨pred n, (pred_le_self n.1).trans_lt n.2⟩
        rw [succ_Iio isSuccLimit_omega0.isSuccPrelimit]
        apply SetCoe.ext
        exact (succ_pred_of_finite (bot_lt_of_lt h) n.2).symm
    · constructor
      · exact (lt_ciSup_iff bddAbove_of_small).mpr ⟨⟨0, omega0_pos⟩, hf.2.2⟩
      · apply iSup_Iio_lt_ord (fun i ↦ (f i).2)
        rwa [card_omega0, lift_aleph0, Cardinal.lift_id']

end IsClub

theorem exists_unbounded_Iio_cof {α : Ordinal} (hlim : IsSuccLimit α) :
    ∃ S, S ⊆ Iio α ∧ IsAccPt α S
    ∧ #S = Cardinal.lift.{u + 1, u} α.cof := by
  obtain ⟨S, hUnb, hCard⟩ :=
    Order.exists_cof_eq ↑(Iio α)
  refine ⟨Subtype.val '' S, ?_, ?_, ?_⟩
  · exact Subtype.coe_image_subset (Iio α) S
  · rw [isAccPt_iff]
    refine ⟨hlim.bot_lt.ne.symm, ?_⟩
    intro β βltα
    obtain ⟨x, hxS, hxle⟩ := hUnb ⟨succ β, hlim.succ_lt βltα⟩
    refine ⟨x.1, ⟨x, hxS, rfl⟩, ?_, x.2⟩
    exact (lt_succ β).trans_le hxle
  · rw [Cardinal.mk_image_eq Subtype.val_injective, hCard, cof_Iio, lift_cof]

theorem exists_club_card {o : Ordinal.{u}} (h : IsSuccLimit o) :
    ∃ C : Club o, #C = Cardinal.lift.{u + 1, u} o.cof := by
  obtain ⟨S, hS⟩ := exists_unbounded_Iio_cof h
  let C := S ∪ (derivedSet S)
  use ⟨C, ⟨isClosedBelowPt_derivedSet o, hS.2.1.mono subset_union_left⟩⟩
  apply (hS.2.2 ▸ mk_le_mk_of_subset subset_union_left).antisymm'
  calc
    #C ≤ #S + #(derivedSet S) := mk_union_le _ _
    _ ≤ #S + #S := by gcongr; exact mk_derivedSet_le S
    _ = max #S #S := add_eq_max <| by
      rw [hS.2.2, ← lift_aleph0.{u + 1, u}, Cardinal.lift_le]
      exact aleph0_le_cof_iff.mpr (one_lt_cof_iff.mpr h)
    _ = #S := max_self _
    _ = Cardinal.lift.{u + 1, u} o.cof := hS.2.2

/-- A set of ordinals is stationary below an ordinal if it intersects every club of it. -/
def IsStationary (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C, IsClub C o → (S ∩ C).Nonempty

namespace IsStationary

theorem inter_Iio {o : Ordinal} {S : Set Ordinal} (hS : IsStationary S o) :
    IsStationary (S ∩ Iio o) o := by
  intro C hC
  convert hS _ hC.inter_Iio using 1
  rw [inter_comm C, inter_assoc]

theorem inter_isClub {o : Ordinal} {S C : Set Ordinal} (hS : IsStationary S o)
    (hC : IsClub C o) : (S ∩ C ∩ (Iio o)).Nonempty := by
  have := hS.inter_Iio C hC
  rwa [inter_assoc, inter_comm C, ← inter_assoc]

end IsStationary

end Ordinal
