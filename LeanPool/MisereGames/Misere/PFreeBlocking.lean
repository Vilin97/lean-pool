/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Misere.Blocking

/-!
Misere combinatorial games.
-/

namespace MisereGames

public section

universe u

open Form
open Form.Misere.Outcome
open GameForm
open PFree

namespace GameForm

/-- The P-free subpredicate of the short blocking games. -/
abbrev PFreeBlocking : GameForm → Prop := PFreeSubset ShortBlocking

private theorem misereOutcome_L_of_not_winsGoingFirst_right {g : GameForm}
    (hpf : IsPFree g) (h : ¬ WinsGoingFirst .right g) : MisereOutcome g = .L := by
  rw [misereOutcome_L_iff_winsGoingFirst]
  refine ⟨?_, h⟩
  by_contra hc
  exact misereOutcome_ne_P_of_pfree hpf (misereOutcome_P_iff_winsGoingFirst.mpr ⟨h, hc⟩)

/--
If `G, H ∈ pf(B)` with `o(G) = L` and `H` a Left end, then `o(G + H) = L`.

This is [Davies, Miller, Milley (Lemma 4.1 on p.
24)][davies:SumsPFreeForms:2025]
-/
theorem misereOutcome_L_add_isEnd_left {g h : GameForm}
    (hg : PFreeBlocking g) (hh : PFreeBlocking h)
    (hgL : MisereOutcome g = .L) (hhe : IsEnd .left h) : MisereOutcome (g + h) = .L := by
  have hg_out := misereOutcome_L_iff_winsGoingFirst.mp hgL
  rw [misereOutcome_L_iff_winsGoingFirst]
  constructor
  · rcases (winsGoingFirst_iff g .left).mp hg_out.left with hg_end | ⟨gl, hgl, hgl_not_right⟩
    · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨isEndLike_iff_isEnd.mp hg_end, hhe⟩)
    · have hgl_pfb := Hereditary.of_mem_moves hg hgl
      have hglL := misereOutcome_L_of_not_winsGoingFirst_right hgl_pfb.isPFree hgl_not_right
      have hsum := misereOutcome_L_add_isEnd_left hgl_pfb hh hglL hhe
      exact winsGoingFirst_of_moves
        ⟨gl + h, add_right_mem_moves_add hgl h, (misereOutcome_L_iff_winsGoingFirst.mp hsum).right⟩
  · rw [not_winsGoingFirst_iff]
    refine ⟨fun h_end => ?_, fun gr hgr => ?_⟩
    · absurd hg_out.right
      exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mp (isEndLike_iff_isEnd.mp h_end)).left
    · rw [moves_add, Set.mem_union, Set.mem_image] at hgr
      rw [Player.neg_right]
      rcases hgr with ⟨gr', hgr', rfl⟩ | ⟨hr, hhr, rfl⟩
      · have h_left_gr' : WinsGoingFirst .left gr' := by
          simpa [Player.neg_right] using (not_winsGoingFirst_iff.mp hg_out.right).right gr' hgr'
        have hgr_pfb := Hereditary.of_mem_moves hg hgr'
        rcases (winsGoingFirst_iff gr' .left).mp h_left_gr'
            with hgr_end | ⟨grl, hgrl, hgrl_not_right⟩
        · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨isEndLike_iff_isEnd.mp hgr_end, hhe⟩)
        · apply winsGoingFirst_of_moves
          use grl + h
          constructor
          · exact add_right_mem_moves_add hgrl h
          · have hgrl_pfb := Hereditary.of_mem_moves hgr_pfb hgrl
            have hgrlL :=
                misereOutcome_L_of_not_winsGoingFirst_right hgrl_pfb.isPFree hgrl_not_right
            have hsum := misereOutcome_L_add_isEnd_left hgrl_pfb hh hgrlL hhe
            exact (misereOutcome_L_iff_winsGoingFirst.mp hsum).right
      · have hh_be : IsBlockedEnd .left h := isBlockedEnd_of_isBlocking hh.mem.blocking hhe
        rcases IsBlockedEnd.hereditary_def hh_be hr hhr with hr_be | ⟨hrl, hhrl, hrl_be⟩
        · have hr_pfb := Hereditary.of_mem_moves hh hhr
          have hsum := misereOutcome_L_add_isEnd_left hg hr_pfb hgL (isEnd_of_isBlockedEnd hr_be)
          exact (misereOutcome_L_iff_winsGoingFirst.mp hsum).left
        · apply winsGoingFirst_of_moves
          use g + hrl
          constructor
          · exact add_left_mem_moves_add hhrl g
          · have hrl_pfb := Hereditary.of_mem_moves (Hereditary.of_mem_moves hh hhr) hhrl
            have hsum :=
                misereOutcome_L_add_isEnd_left hg hrl_pfb hgL (isEnd_of_isBlockedEnd hrl_be)
            exact (misereOutcome_L_iff_winsGoingFirst.mp hsum).right
termination_by Form.birthday g + Form.birthday h
decreasing_by
  all_goals
    first
      | exact birthday_add_lt_left (birthday_lt_of_mem_moves (by assumption))
      | exact birthday_add_lt_right (birthday_lt_of_mem_moves (by assumption))
      | exact birthday_add_lt_left
          (lt_trans
            (birthday_lt_of_mem_moves (by assumption))
            (birthday_lt_of_mem_moves (by assumption)))
      | exact birthday_add_lt_right
          (lt_trans
            (birthday_lt_of_mem_moves (by assumption))
            (birthday_lt_of_mem_moves (by assumption)))

/--
This is the mirror of [Davies, Miller, Milley (Lemma 4.1 on p.
24)][davies:SumsPFreeForms:2025].
-/
theorem misereOutcome_R_add_isEnd_right {g h : GameForm}
    (hg : PFreeBlocking g) (hh : PFreeBlocking h)
    (hgR : MisereOutcome g = .R) (hhe : IsEnd .right h) : MisereOutcome (g + h) = .R := by
  rw [← misereOutcome_neg_L_iff_misereOutcome]
  simpa [neg_add_rev, add_comm]
    using misereOutcome_L_add_isEnd_left
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            (misereOutcome_neg_L_iff_misereOutcome.mpr hgR) (IsEnd.neg_iff_neg.mpr hhe)

mutual

private theorem misereOutcome_of_add_LL_blocking {g h : GameForm}
    (hg : PFreeBlocking g) (hh : PFreeBlocking h)
    (hgL : MisereOutcome g = .L) (hhL : MisereOutcome h = .L) : MisereOutcome (g + h) = .L := by
  have hg_out := misereOutcome_L_iff_winsGoingFirst.mp hgL
  have hh_out := misereOutcome_L_iff_winsGoingFirst.mp hhL
  rw [misereOutcome_L_iff_winsGoingFirst]
  constructor
  · rcases (winsGoingFirst_iff g .left).mp hg_out.left with hg_end | ⟨gl, hgl, hgl_not_right⟩
    · rcases (winsGoingFirst_iff h .left).mp hh_out.left with hh_end | ⟨hl, hhl, hhl_not_right⟩
      · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr
          ⟨isEndLike_iff_isEnd.mp hg_end, isEndLike_iff_isEnd.mp hh_end⟩)
      · have hhl_pfb := Hereditary.of_mem_moves hh hhl
        have hhlL := misereOutcome_L_of_not_winsGoingFirst_right hhl_pfb.isPFree hhl_not_right
        have hsumL := misereOutcome_of_add_LL_blocking hg hhl_pfb hgL hhlL
        exact winsGoingFirst_of_moves
          ⟨g + hl, add_left_mem_moves_add hhl g,
            (misereOutcome_L_iff_winsGoingFirst.mp hsumL).right⟩
    · have hgl_pfb := Hereditary.of_mem_moves hg hgl
      have hglL := misereOutcome_L_of_not_winsGoingFirst_right hgl_pfb.isPFree hgl_not_right
      have hsumL := misereOutcome_of_add_LL_blocking hgl_pfb hh hglL hhL
      exact winsGoingFirst_of_moves
        ⟨gl + h, add_right_mem_moves_add hgl h, (misereOutcome_L_iff_winsGoingFirst.mp hsumL).right⟩
  · rw [not_winsGoingFirst_iff]
    refine ⟨fun h_end => ?_, fun gr hgr => ?_⟩
    · exact hg_out.right
        (winsGoingFirst_of_isEnd (IsEnd.add_iff.mp (isEndLike_iff_isEnd.mp h_end)).left)
    · rw [moves_add, Set.mem_union, Set.mem_image] at hgr
      rcases hgr with ⟨gr', hgr', rfl⟩ | ⟨hr, hhr, rfl⟩
      · have h_left_gr' : WinsGoingFirst .left gr' := by
          simpa [Player.neg_right] using (not_winsGoingFirst_iff.mp hg_out.right).right gr' hgr'
        have hgr_pfb := Hereditary.of_mem_moves hg hgr'
        cases hgr'_out : MisereOutcome gr' with
        | L => exact (misereOutcome_L_iff_winsGoingFirst.mp
            (misereOutcome_of_add_LL_blocking hgr_pfb hh hgr'_out hhL)).left
        | N =>
            have hwin : WinsGoingFirst .left (h + gr') :=
              miserePlayerOutcome_eq_iff_winsGoingFirst.mp
                (miserePlayerOutcome_of_add_LN_blocking hh hgr_pfb hhL hgr'_out)
            rwa [add_comm] at hwin
        | P => exact absurd hgr'_out (misereOutcome_ne_P_of_pfree hgr_pfb.isPFree)
        | R => exact absurd h_left_gr' (misereOutcome_R_iff_winsGoingFirst.mp hgr'_out).right
      · have h_left_hr : WinsGoingFirst .left hr := by
          simpa [Player.neg_right] using (not_winsGoingFirst_iff.mp hh_out.right).right hr hhr
        have hhr_pfb := Hereditary.of_mem_moves hh hhr
        cases hhr_out : MisereOutcome hr with
        | L => exact (misereOutcome_L_iff_winsGoingFirst.mp
            (misereOutcome_of_add_LL_blocking hg hhr_pfb hgL hhr_out)).left
        | N =>
            exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp
              (miserePlayerOutcome_of_add_LN_blocking hg hhr_pfb hgL hhr_out)
        | P => exact absurd hhr_out (misereOutcome_ne_P_of_pfree hhr_pfb.isPFree)
        | R => exact absurd h_left_hr (misereOutcome_R_iff_winsGoingFirst.mp hhr_out).right
termination_by Form.birthday g + Form.birthday h
decreasing_by
  · exact add_lt_add_right (birthday_lt_of_mem_moves hhl) _
  · exact add_lt_add_left (birthday_lt_of_mem_moves hgl) _
  · exact add_lt_add_left (birthday_lt_of_mem_moves hgr') _
  · calc
      birthday h + birthday gr' = birthday gr' + birthday h := add_comm _ _
      _ < birthday g + birthday h := add_lt_add_left (birthday_lt_of_mem_moves hgr') _
  · exact add_lt_add_right (birthday_lt_of_mem_moves hhr) _
  · exact add_lt_add_right (birthday_lt_of_mem_moves hhr) _

private theorem miserePlayerOutcome_of_add_LN_blocking {g h : GameForm}
    (hg : PFreeBlocking g) (hh : PFreeBlocking h)
    (hgL : MisereOutcome g = .L) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst]
  by_cases h_end : IsEnd .left h
  · exact
      (misereOutcome_L_iff_winsGoingFirst.mp
        (misereOutcome_L_add_isEnd_left hg hh hgL h_end)).left
  · rcases (winsGoingFirst_iff h .left).mp (misereOutcome_N_iff_winsGoingFirst.mp hhN).left with
        h_le | ⟨hl, hhl, hhl_not_right⟩
    · exact absurd (isEndLike_iff_isEnd.mp h_le) h_end
    · have hhl_pfb := Hereditary.of_mem_moves hh hhl
      have hhlL := misereOutcome_L_of_not_winsGoingFirst_right hhl_pfb.isPFree hhl_not_right
      refine winsGoingFirst_of_moves ⟨g + hl, add_left_mem_moves_add hhl g, ?_⟩
      rw [Player.neg_left]
      exact (misereOutcome_L_iff_winsGoingFirst.mp
        (misereOutcome_of_add_LL_blocking hg hhl_pfb hgL hhlL)).right
termination_by Form.birthday g + Form.birthday h
decreasing_by
  exact add_lt_add_right (birthday_lt_of_mem_moves hhl) _

end

private theorem misereOutcome_of_add_RR_blocking {g h : GameForm}
    (hg : PFreeBlocking g) (hh : PFreeBlocking h)
    (hgR : MisereOutcome g = .R) (hhR : MisereOutcome h = .R) : MisereOutcome (g + h) = .R := by
  rw [← misereOutcome_neg_L_iff_misereOutcome]
  simpa [neg_add_rev, add_comm]
    using misereOutcome_of_add_LL_blocking
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            (misereOutcome_neg_L_iff_misereOutcome.mpr hgR)
            (misereOutcome_neg_L_iff_misereOutcome.mpr hhR)

private theorem miserePlayerOutcome_of_add_RN_blocking {g h : GameForm}
    (hg : PFreeBlocking g) (hh : PFreeBlocking h)
    (hgR : MisereOutcome g = .R) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, ← Player.neg_left, ← winsGoingFirst_neg_iff]
  simpa [neg_add_rev, add_comm]
    using miserePlayerOutcome_eq_iff_winsGoingFirst.mp
          (miserePlayerOutcome_of_add_LN_blocking
            (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
            (misereOutcome_neg_L_iff_misereOutcome.mpr hgR)
            (misereOutcome_neg_N_iff_misereOutcome.mpr hhN))

/--
This is [Davies, Miller, Milley (Lemma 4.2 on p.
25)][davies:SumsPFreeForms:2025].
-/
instance : OutcomeStable (ShortBlocking (G := GameForm)) where
  misereOutcome_of_add_LL := misereOutcome_of_add_LL_blocking
  misereOutcome_of_add_RR := misereOutcome_of_add_RR_blocking
  miserePlayerOutcome_of_add_LN := miserePlayerOutcome_of_add_LN_blocking
  miserePlayerOutcome_of_add_RN := miserePlayerOutcome_of_add_RN_blocking

private theorem misereOutcome_R_of_not_winsGoingFirst_left {g : GameForm}
    (hpf : IsPFree g) (h : ¬ WinsGoingFirst .left g) : MisereOutcome g = .R := by
  rw [misereOutcome_R_iff_winsGoingFirst]
  refine ⟨?_, h⟩
  by_contra hc
  exact misereOutcome_ne_P_of_pfree hpf (misereOutcome_P_iff_winsGoingFirst.mpr ⟨hc, h⟩)

/--
This is [Davies, Miller, Milley (Lemma 4.7 on p.
26)][davies:SumsPFreeForms:2025].
-/
theorem _root_.MisereGames.GameForm.miserePlayerOutcome_right_isEnd_left_NN {g h : GameForm}
    (hg : PFreeBlocking g) (hh : PFreeBlocking h)
    (hge : IsEnd .left g) (hgN : MisereOutcome g = .N) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst]
  by_cases hgr_end : IsEnd .right g
  · have hg0 : g = 0 := both_ends_eq_zero hge hgr_end
    subst hg0
    rw [zero_add]
    exact (misereOutcome_N_iff_winsGoingFirst.mp hhN).right
  · obtain ⟨gr, hgr_mem, hgr_not⟩ : ∃ gr ∈ moves .right g, ¬ WinsGoingFirst .left gr := by
      rcases (winsGoingFirst_iff g .right).mp (misereOutcome_N_iff_winsGoingFirst.mp hgN).right
          with hend | ⟨gr, hgr, hgr_not⟩
      · exact absurd (isEndLike_iff_isEnd.mp hend) hgr_end
      · exact ⟨gr, hgr, by simpa [Player.neg_right] using hgr_not⟩
    have hgrR := misereOutcome_R_of_not_winsGoingFirst_left
        (Hereditary.of_mem_moves hg hgr_mem).isPFree hgr_not
    by_cases hhr_end : IsEnd .right h
    · refine winsGoingFirst_of_moves ⟨gr + h, add_right_mem_moves_add hgr_mem h, ?_⟩
      rw [Player.neg_right]
      exact (misereOutcome_R_iff_winsGoingFirst.mp
        (misereOutcome_R_add_isEnd_right
          (Hereditary.of_mem_moves hg hgr_mem) hh hgrR hhr_end)).right
    · obtain ⟨hr, hhr_mem, hhr_not⟩ : ∃ hr ∈ moves .right h, ¬ WinsGoingFirst .left hr := by
        rcases (winsGoingFirst_iff h .right).mp (misereOutcome_N_iff_winsGoingFirst.mp hhN).right
            with hend | ⟨hr, hhr, hhr_not⟩
        · exact absurd (isEndLike_iff_isEnd.mp hend) hhr_end
        · exact ⟨hr, hhr, by simpa [Player.neg_right] using hhr_not⟩
      have hhr_pfb := Hereditary.of_mem_moves hh hhr_mem
      have hhrR : MisereOutcome hr = .R :=
        misereOutcome_R_of_not_winsGoingFirst_left hhr_pfb.isPFree hhr_not
      have hhr_not_lend : ¬ IsEnd .left hr := by
        intro he
        exact hhr_not (winsGoingFirst_of_isEnd he)
      refine winsGoingFirst_of_moves ⟨g + hr, add_left_mem_moves_add hhr_mem g, ?_⟩
      rw [Player.neg_right, not_winsGoingFirst_iff]
      refine ⟨?_, fun g' hg' => ?_⟩
      · rw [GameForm.isEndLike_iff_isEnd, IsEnd.add_iff]
        exact fun hc => hhr_not_lend hc.right
      · rw [Player.neg_left]
        rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at hg'
        rcases hg' with ⟨gl, hgl, rfl⟩ | ⟨hrl, hhrl, rfl⟩
        · have hg0 : moves .left g = ∅ := by rw [← isEnd_def]; exact hge
          rw [hg0] at hgl
          exact (Set.notMem_empty gl hgl).elim
        · have hhrl_pfb := Hereditary.of_mem_moves hhr_pfb hhrl
          have hhrl_winsR : WinsGoingFirst .right hrl := by
            have := (not_winsGoingFirst_iff.mp
                      (misereOutcome_R_iff_winsGoingFirst.mp hhrR).right).right hrl hhrl
            rwa [Player.neg_left] at this
          rcases hhrl_out : MisereOutcome hrl with _ | _ | _ | _
          · absurd (misereOutcome_L_iff_winsGoingFirst.mp hhrl_out).right
            exact hhrl_winsR
          · exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp
              (miserePlayerOutcome_right_isEnd_left_NN hg hhrl_pfb hge hgN hhrl_out)
          · exact absurd hhrl_out (misereOutcome_ne_P_of_pfree hhrl_pfb.isPFree)
          · have hwin : MiserePlayerOutcome (hrl + g) .right = .right :=
              OutcomeStable.miserePlayerOutcome_of_add_RN hhrl_pfb hg hhrl_out hgN
            have := miserePlayerOutcome_eq_iff_winsGoingFirst.mp hwin
            rwa [add_comm] at this
termination_by Form.birthday g + Form.birthday h
decreasing_by
  all_goals
    first
      | exact birthday_add_lt_left (birthday_lt_of_mem_moves (by assumption))
      | exact birthday_add_lt_right (birthday_lt_of_mem_moves (by assumption))
      | exact birthday_add_lt_right
          (lt_trans
            (birthday_lt_of_mem_moves (by assumption))
            (birthday_lt_of_mem_moves (by assumption)))

/--
This is the mirror of [Davies, Miller, Milley (Lemma 4.7 on p.
26)][davies:SumsPFreeForms:2025].
-/
theorem _root_.MisereGames.GameForm.miserePlayerOutcome_left_isEnd_right_NN {g h : GameForm}
    (hg : PFreeBlocking g) (hh : PFreeBlocking h)
    (hge : IsEnd .right g) (hgN : MisereOutcome g = .N) (hhN : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, ← Player.neg_right, ← winsGoingFirst_neg_iff]
  simpa [neg_add_rev, add_comm]
    using miserePlayerOutcome_eq_iff_winsGoingFirst.mp
      (miserePlayerOutcome_right_isEnd_left_NN
        (ClosedUnderNeg.neg_iff.mpr hg) (ClosedUnderNeg.neg_iff.mpr hh)
        (IsEnd.neg_iff_neg.mpr hge) (misereOutcome_neg_N_iff_misereOutcome.mpr hgN)
        (misereOutcome_neg_N_iff_misereOutcome.mpr hhN))

/--
This is [Davies, Miller, Milley (Lemma 4.8 on p.
26)][davies:SumsPFreeForms:2025].
-/
instance : IntegerInvertible.PropertyX ShortBlocking where
  prop_left := by
    intro g h hAg hAh hsg hsh hNg hNh hge hnge hrg hlh
    rw [misereOutcome_N_iff_winsGoingFirst]
    refine ⟨?_, ?_⟩
    · obtain ⟨hl, hhl, hhl_not⟩ : ∃ hl ∈ moves .left h, ¬ WinsGoingFirst .right hl := by
        rcases (winsGoingFirst_iff h .left).mp (misereOutcome_N_iff_winsGoingFirst.mp hNh).left
            with hend | ⟨hl, hhl, hhl_not⟩
        · exact absurd (isEndLike_iff_isEnd.mp hend) hnge
        · exact ⟨hl, hhl, by simpa [Player.neg_left] using hhl_not⟩
      have hhl_pfb := Hereditary.of_mem_moves hAh hhl
      have hhlL := misereOutcome_L_of_not_winsGoingFirst_right hhl_pfb.isPFree hhl_not
      refine winsGoingFirst_of_moves ⟨g + hl, add_left_mem_moves_add hhl g, ?_⟩
      rw [Player.neg_left]
      have hsum : MisereOutcome (g + hl) = .L := by
        rw [add_comm]; exact misereOutcome_L_add_isEnd_left hhl_pfb hAg hhlL hge
      exact (misereOutcome_L_iff_winsGoingFirst.mp hsum).right
    · rw [<-miserePlayerOutcome_eq_iff_winsGoingFirst]
      exact miserePlayerOutcome_right_isEnd_left_NN hAg hAh hge hNg hNh
  prop_right := by
    intro g h hAg hAh hsg hsh hNg hNh hge hnge hlg hrh
    rw [misereOutcome_N_iff_winsGoingFirst]
    refine ⟨?_, ?_⟩
    · have hw := miserePlayerOutcome_eq_iff_winsGoingFirst.mp
        (miserePlayerOutcome_left_isEnd_right_NN hAh hAg hge hNh hNg)
      rwa [add_comm] at hw
    · obtain ⟨gr, hgr, hgr_not⟩ : ∃ gr ∈ moves .right g, ¬ WinsGoingFirst .left gr := by
        rcases (winsGoingFirst_iff g .right).mp (misereOutcome_N_iff_winsGoingFirst.mp hNg).right
            with hend | ⟨gr, hgr, hgr_not⟩
        · exact absurd (isEndLike_iff_isEnd.mp hend) hnge
        · exact ⟨gr, hgr, by simpa [Player.neg_right] using hgr_not⟩
      have hgr_pfb := Hereditary.of_mem_moves hAg hgr
      have hgrR := misereOutcome_R_of_not_winsGoingFirst_left hgr_pfb.isPFree hgr_not
      refine winsGoingFirst_of_moves ⟨gr + h, add_right_mem_moves_add hgr h, ?_⟩
      rw [Player.neg_right]
      exact (misereOutcome_R_iff_winsGoingFirst.mp
              (misereOutcome_R_add_isEnd_right hgr_pfb hAh hgrR hge)).right

/--
This is [Davies, Miller, Milley (Lemma 4.9 on p.
27)][davies:SumsPFreeForms:2025].
-/
instance : ClosedUnderAdd PFreeBlocking where
  has_add g h h_g h_h := by
    apply PFreeSubset.mk
    · exact ClosedUnderAdd.has_add g h h_g.mem h_h.mem
    · exact IntegerInvertible.isPFree_of_propertyX h_g h_h h_g.mem.short h_h.mem.short

end GameForm

end

end MisereGames
