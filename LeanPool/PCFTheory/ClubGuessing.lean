/-
Copyright (c) 2026 YnirPaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YnirPaz
-/

import LeanPool.PCFTheory.Background.Club

/-!
# Club guessing

This file formalizes `theorem 2.17` in the chapter "Cardinal Arithmetic" in the "Handbook
of set theory."

For `δ` an ordinal, let `S ⊆ δ`, and `f : (α : S) → Club α` a function assigning a club
to each element of `S`.
Then `f` is said to be "club guessing" if for every club of `δ`, `C : Club δ`, there is some
`α ∈ S` such that `f α ⊆ C`. That is, `f` guesses `C` at `α`.

There are many existence results on club guessing sequences. The one we need is `theorem 2.17`:
  Let `Ϟ` be an ordinal and let `S` be a stationary set below `Ϟ`, such that every
  element of `S` has the same cofinality `κ`. Further assume `succ κ < Ϟ.cof`.
  Then there exists a club guessing sequence on `S`.

## Main definitions

* `Ordinal.IsClubGuessing {S} f γ` says `f : (α : S) → Club α` is a club guessing sequence for `γ`.
  Unlike in the typical definition, we don't assume `S ⊆ Iio γ`. This makes no mathematical
  difference but allows us to have `IsClubGuessing f γ` for many different `γ`.

## Main results

* `Ordinal.exists_isClubGuessing_of_cof_uncountable`: Let `Ϟ` be an ordinal and `S` stationary below
  `Ϟ`, such that `∀ α ∈ S, α.cof = κ`, for a constant `κ` satisfying `succ κ < Ϟ.cof`.
  Assume also that `ℵ₀ < κ`. Then there exists `f : (α : S) → Club α` that is club guessing
  below `Ϟ`.
-/

noncomputable section

open Cardinal Order Set

universe u

namespace Ordinal

/-- `f : (α : S) → Club α` is a *club-guessing sequence for `γ`* when every club of `γ`
contains the carrier of `f α` for some `α ∈ S`. -/
def IsClubGuessing {S : Set Ordinal} (f : (α : S) → Club α) (γ : Ordinal) : Prop :=
  ∀ C : Club γ, ∃ δ, (f δ).carrier ⊆ C.carrier

theorem exists_club_of_not_isClubGuessing {S : Set Ordinal} {γ : Ordinal} (f : (α : S) → Club α)
    (h : ¬ IsClubGuessing f γ) : ∃ C : Club γ, ∀ δ, ¬ (f δ).carrier ⊆ C := by
  dsimp [IsClubGuessing] at h
  push Not at h
  exact h

namespace ClubGuessing

/-- The assumptions of the theorem and `hCont`, which says the result is false. -/
class Assumptions where
  /-- The ambient ordinal `Ϟ` below which we build the club-guessing sequence. -/
  Ϟ : Ordinal.{u}
  /-- The common cofinality `κ` of all elements of the stationary set `S`. -/
  κ : Cardinal.{u}
  /-- Hypothesis: `κ` is uncountable. -/
  hκ : ℵ₀ < κ
  /-- Hypothesis: `succ κ < Ϟ.cof`. -/
  hcof : succ κ < Ϟ.cof
  /-- The stationary set on which we build the club-guessing sequence. -/
  S : Set Ordinal.{u}
  /-- Hypothesis: `S` is stationary below `Ϟ`. -/
  hStat : IsStationary S Ϟ
  /-- Hypothesis: `S` is a subset of `Iio Ϟ`. -/
  hSub : S ⊆ Iio Ϟ
  /-- Hypothesis: every element of `S` has cofinality `κ`. -/
  hS : ∀ α ∈ S, α.cof = κ
  /-- Contradictory hypothesis used for the proof by contradiction: there is no
  club-guessing sequence. -/
  hCont : ∀ f : (α : S) → Club.{u} α, ¬ IsClubGuessing f Ϟ

namespace Assumptions
variable [assumptions : Assumptions.{u}]

instance : Nonempty (Iio (succ κ).ord) := ⟨0,
  ord_zero ▸ (ord_lt_ord.mpr <| (aleph0_pos.trans hκ).trans (lt_succ κ))⟩

theorem isSuccLimit_of_mem_S {α : S} : IsSuccLimit α.1 :=
  one_lt_cof_iff.mp (one_lt_aleph0.trans_le (hS α α.2 ▸ hκ).le)

theorem aleph0_lt_cof_Ϟ : ℵ₀ < Ϟ.cof :=
  hκ.trans ((lt_succ κ).trans hcof)

/-- A first attempt at a club-guessing sequence: pick an arbitrary club of cardinality `κ`
below each element of `S`. -/
def f : (α : S) → Club α := fun _ ↦ Classical.choose <| exists_club_card isSuccLimit_of_mem_S

/-- Given a club `E` of `Ϟ` not guessed by `f`, we "force" `f` to guess `E` at every
point in `S` that is an accumulation point of `E` by intersecting every `f α` with `E`. -/
def restrict (E : Club Ϟ) : (α : S) → Club α := fun α ↦
  open Classical in
  if h : IsAccPt α.1 E then
    ⟨(f α).1 ∩ E,
      IsClub.inter (hS α α.2 ▸ hκ) (f α).2 <| IsClub.isClub_of_isAcc (hSub α.2) E.2 h⟩
  else univClub isSuccLimit_of_mem_S

/-- The sequence of clubs `E_α` obtained by repeatedly choosing a club not guessed by the
current restriction of `f`. -/
def F : Iio (succ κ).ord → Club Ϟ := by
  refine @boundedRec (succ κ).ord (fun _ ↦ Club Ϟ) fun o ih ↦
    Classical.choose <| exists_club_of_not_isClubGuessing _
      ((hCont <| restrict ⟨⋂ α, ih α, ?_⟩))
  apply IsClub.iInter_Iio aleph0_lt_cof_Ϟ
  · exact (lt_ord.mp o.2).trans hcof
  · exact fun x ↦ (ih x).isClub

/-- Prefix intersections of `F`. -/
def F' : Iio (succ κ).ord → Club Ϟ := fun δ ↦ ⟨⋂ α : Iio δ, F α,
  IsClub.iInter_Iio aleph0_lt_cof_Ϟ ((lt_ord.mp δ.2).trans hcof) fun x ↦ (F x).2⟩

/-- The intersection of all clubs `F α` for `α < succ κ`. -/
def E : Club Ϟ := ⟨⋂ α : Iio (succ κ).ord, F α, by
  apply IsClub.iInter_lift aleph0_lt_cof_Ϟ fun i ↦ (F i).2
  rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, Cardinal.lift_lt, card_ord]
  exact hcof⟩

/-- Since `E` is a club and `S` is stationary, there is some `α ∈ S ∩ E'`; this is one
such witness. -/
def α : assumptions.S := by
  have : Set.Nonempty _ := hStat.inter_isClub (E.2.derivedSet aleph0_lt_cof_Ϟ)
  exact ⟨Classical.choose this, (Classical.choose_spec this).1.1⟩

theorem isAcc_α : IsAccPt α E := by
  unfold α
  generalize_proofs pf
  exact (Classical.choose_spec pf).1.2

theorem isAcc_α_F' (β : Iio (succ κ).ord) : IsAccPt α (F' β) :=
  isAcc_α.mono (by exact fun x hx y ⟨z, hz⟩ ↦ hx y ⟨z, hz⟩)

theorem restrict_subset_α (β : Iio (succ κ).ord) : restrict (F' β) α ⊆ f α := by
  rw [restrict, dif_pos (isAcc_α_F' _)]
  exact inter_subset_left

theorem restrict_subset_restrict {C D : Club Ϟ} (h : C ⊆ D) (ha : IsAccPt α C) :
    restrict C α ⊆ restrict D α := by
  unfold restrict
  rw [dif_pos ha, dif_pos (by exact ha.mono h)]
  exact inter_subset_inter (fun _ H ↦ H) h

theorem restrict_not_subset (β : Iio (succ κ).ord) :
    ¬ (restrict (F' β) α).carrier ⊆ (F β).carrier := by
  rw [F, boundedRec_eq]
  generalize_proofs _ _ _ pf
  exact Classical.choose_spec pf α

theorem restrict_subset {β γ : Iio (succ κ).ord} (h : β < γ) :
    (restrict (F' γ) α).carrier ⊆ (F β).carrier := by
  rw [restrict, dif_pos (isAcc_α_F' γ)]
  refine inter_subset_right.trans ?_
  intro x xmem
  exact xmem (F β).carrier ⟨⟨β, h⟩, rfl⟩

/- At each of the `succ κ` steps, when we chose a club `C` that is not guessed so far,
we shrunk the club we started with below `α`, `f α`.
In fact we shrunk the club below every element of `S ∩ C'`, because no club guessed `C`.
 -/
theorem restrict_ssubset_restrict {β γ : Iio (succ κ).ord} (h : β < γ) :
    restrict (F' γ) α ⊂ restrict (F' β) α := by
  rw [ssubset_iff_subset_ne]
  constructor
  · apply restrict_subset_restrict
    · exact fun x hx s ⟨z, hz⟩ ↦ hx s ⟨⟨z.1, z.2.trans h⟩, hz⟩
    · exact isAcc_α_F' _
  · exact fun heq ↦ restrict_not_subset β (heq ▸ (restrict_subset h))

/- `f α` has cardinality `κ`, but we removed elements from it `succ κ` many times. -/
theorem contradiction : False := by
  have : Cardinal.lift.{u, u + 1} #(f α).carrier
      < Cardinal.lift.{u + 1, u} (succ κ).ord.card := by
    have : #↑(f α).carrier = Cardinal.lift.{u + 1, u} κ := by
      unfold f
      generalize_proofs pf
      exact (hS α α.2) ▸ Classical.choose_spec pf
    rw [card_ord, this, Cardinal.lift_lift, Cardinal.lift_lt]
    exact lt_succ κ
  apply not_exists_ssubset_chain_lift (isSuccLimit_ord (hκ.trans (lt_succ κ)).le) this
  use fun x ↦ restrict (F' x) α
  constructor
  · exact restrict_subset_α
  · exact fun β γ ↦ restrict_ssubset_restrict

end Assumptions
end ClubGuessing

theorem exists_isClubGuessing_of_cof_uncountable {Ϟ : Ordinal} {κ : Cardinal} (hκ : ℵ₀ < κ)
    (hcof : succ κ < Ϟ.cof) {S : Set Ordinal} (hStat : IsStationary S Ϟ)
    (hS : ∀ α ∈ S, α.cof = κ) : ∃ f : (α : S) → Club α, IsClubGuessing f Ϟ := by
  by_contra! h
  have : ClubGuessing.Assumptions := ⟨Ϟ, κ, hκ, hcof, S ∩ Iio Ϟ, hStat.inter_Iio,
    inter_subset_right, (fun _ ⟨h, _⟩ ↦ hS _ h), ?_⟩
  · exact ClubGuessing.Assumptions.contradiction
  · intro f hf
    let g : (α : S) → (Club α) := fun α ↦ if hα : α.1 ∈ (Iio Ϟ) then (f ⟨α.1, ⟨α.2, hα⟩⟩) else
      univClub (one_lt_cof_iff.mp (one_lt_aleph0.trans_le (hS α α.2 ▸ hκ).le))
    refine h g fun C ↦ ?_
    obtain ⟨δ, hδ⟩ := hf ⟨C.1 ∩ Iio Ϟ, C.2.inter_Iio⟩
    use ⟨δ.1, δ.2.1⟩
    unfold g
    rw [dif_pos δ.2.2]
    exact hδ.trans inter_subset_left

end Ordinal
