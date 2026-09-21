/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.RecursionCardinal

/-!
# Delayed injective bookkeeping

Every pair `(α, ξ)` receives a distinct later recursion index.  The
construction follows the manuscript: well-order all requirements in initial
order type and recursively choose a fresh point in the full-size tail above
`α`.
-/

namespace ScottishBook155

noncomputable section

private abbrev RI := RecursionIndex.{0}

private structure Requirement where
  stage : RI
  point : RI

private def requirementEquiv :
    Requirement ≃ RI × RI where
  toFun p := (p.stage, p.point)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem requirements_mk :
    Cardinal.mk Requirement = recursionCardinal := by
  rw [Cardinal.mk_congr requirementEquiv, Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  rw [mk_recursionIndex,
    Cardinal.mul_eq_self aleph0_lt_recursionCardinal.le]

/-- An injective schedule placing every requirement strictly after the stage
whose point it names. -/
theorem exists_bookkeepingSchedule :
    ∃ s : RI × RI → RI,
      Function.Injective s ∧ ∀ p, p.1 < s p := by
  obtain ⟨orderP, wfP, htype⟩ :=
    Cardinal.exists_ord_eq_type_lt Requirement
  letI : LinearOrder Requirement := orderP
  letI : WellFoundedLT Requirement := wfP
  have hprior (p : Requirement) :
      Cardinal.mk (Set.Iio p) < recursionCardinal := by
    exact (Cardinal.mk_Iio_lt p htype).trans_eq requirements_mk
  have fresh (p : Requirement)
      (rec : ∀ q, q < p → RecursionIndex) :
      ∃ i : RI, p.stage < i ∧
        ∀ q (hq : q < p), rec q hq ≠ i := by
    let g : Set.Iio p → RI := fun q => rec q.1 q.2
    have hused : Cardinal.mk (Set.range g) < recursionCardinal :=
      Cardinal.mk_range_le.trans_lt (hprior p)
    by_contra hnone
    push_neg at hnone
    have hsubset : Set.Ioi p.stage ⊆ Set.range g := by
      intro i hi
      rcases hnone i hi with ⟨q, hq, heq⟩
      exact ⟨⟨q, hq⟩, heq⟩
    have htailUsed : Cardinal.mk (Set.Ioi p.stage) ≤
        Cardinal.mk (Set.range g) := Cardinal.mk_le_mk_of_subset hsubset
    have : recursionCardinal < recursionCardinal := by
      calc
        recursionCardinal = Cardinal.mk (Set.Ioi p.stage) :=
          (tail_mk p.stage).symm
        _ ≤ Cardinal.mk (Set.range g) := htailUsed
        _ < recursionCardinal := hused
    exact this.false
  let F : (p : Requirement) →
      (∀ q, q < p → RI) → RI :=
    fun p rec => Classical.choose (fresh p rec)
  let sR : Requirement → RI :=
    WellFounded.fix wellFounded_lt F
  have hs (p : Requirement) :
      p.stage < sR p ∧ ∀ q (hq : q < p), sR q ≠ sR p := by
    rw [show sR p = F p (fun q _ => sR q) from
      WellFounded.fix_eq wellFounded_lt F p]
    exact Classical.choose_spec (fresh p (fun q _ => sR q))
  have hsR_injective : Function.Injective sR := by
    intro p q hpq
    rcases lt_trichotomy p q with hp | heq | hq
    · exact False.elim ((hs q).2 p hp hpq)
    · exact heq
    · exact False.elim ((hs p).2 q hq hpq.symm)
  let s : RI × RI → RI :=
    fun p => sR ⟨p.1, p.2⟩
  refine ⟨s, ?_, fun p => (hs ⟨p.1, p.2⟩).1⟩
  intro p q hpq
  exact Prod.ext_iff.mpr (Requirement.mk.inj (hsR_injective hpq))

/-- A fixed schedule chosen from `exists_bookkeepingSchedule`. -/
noncomputable def bookkeepingSchedule :
    RI × RI → RI :=
  Classical.choose exists_bookkeepingSchedule

theorem bookkeepingSchedule_injective :
    Function.Injective bookkeepingSchedule :=
  (Classical.choose_spec exists_bookkeepingSchedule).1

theorem bookkeepingSchedule_gt (p : RI × RI) :
    p.1 < bookkeepingSchedule p :=
  (Classical.choose_spec exists_bookkeepingSchedule).2 p

/-- The stage which receives the point named by a bookkeeping requirement.
The schedule names the transition; the point is present at its successor. -/
noncomputable def bookkeepingReceivingStage (p : RI × RI) : RI :=
  Order.succ (bookkeepingSchedule p)

theorem bookkeepingSchedule_lt_receivingStage (p : RI × RI) :
    bookkeepingSchedule p < bookkeepingReceivingStage p :=
  Order.lt_succ_of_not_isMax (not_isMax _)

theorem bookkeepingReceivingStage_gt (p : RI × RI) :
    p.1 < bookkeepingReceivingStage p :=
  (bookkeepingSchedule_gt p).trans (bookkeepingSchedule_lt_receivingStage p)

end

end ScottishBook155
