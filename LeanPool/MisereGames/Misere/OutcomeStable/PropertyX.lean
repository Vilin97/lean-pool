/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Misere.IntegerInvertible

/-!
Misere combinatorial games.
-/

namespace MisereGames

open Form
open Form.Misere.Outcome
open GameForm
open OutcomeStable

namespace IntegerInvertible

universe u

public section

/--
A set of games $\mathcal{A}$ has Property X if, for all $G, H \in
\operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \operatorname{o}(H)
= \mathscr{N}$

1. if $\operatorname{r}(G) = \operatorname{l}(H) = 1$, where $G$ is a Left end
but $H$ is not, then $\operatorname{o}(G + H) = N$; and
2. if $\operatorname{l}(G) = \operatorname{r}(H) = 1$, where $H$ is a Right end
but $G$ is not, then $\operatorname{o}(G + H) = N$.

This is [Davies, Miller, Milley (Definition 3.16 on p.
18)][davies:SumsPFreeForms:2025].
-/
class PropertyX (A : GameForm → Prop) : Prop where
  prop_left {g h : GameForm} (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hNg : MisereOutcome g = .N) (hNh : MisereOutcome h = .N)
    (hge : IsEnd .left g) (hnge : ¬ IsEnd .left h)
    (hrg : RTippingPoint hsg = 1) (hlh : LTippingPoint hsh = 1) :
    MisereOutcome (g + h) = .N
  prop_right {g h : GameForm} (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hNg : MisereOutcome g = .N) (hNh : MisereOutcome h = .N)
    (hge : IsEnd .right h) (hnge : ¬ IsEnd .right g)
    (hlg : LTippingPoint hsg = 1) (hrh : RTippingPoint hsh = 1) :
    MisereOutcome (g + h) = .N

/--
The conjunction of the eight implications of Lemma 3.17 for a fixed pair $(G,
H)$. We package them in a structure so that the (mutual) induction can return
all of them at once.
-/
structure Lemma317Claim (g h : GameForm) (hsg : IsShort g) (hsh : IsShort h) : Prop where
  /--
  1(a): if $\operatorname{o}(G) = \mathscr{L}$, $\operatorname{o}(H) =
  \mathscr{N}$, $\operatorname{n}(G) = \operatorname{l}(H)$ then
  $\operatorname{o}(G + H) = \mathscr{L}$.
  -/
  p1a : MisereOutcome g = .L → MisereOutcome h = .N →
    NTippingPoint hsg = LTippingPoint hsh → MisereOutcome (g + h) = .L
  /--
  1(b): if $\operatorname{o}(G) = \mathscr{L}$, $\operatorname{o}(H) =
  \mathscr{N}$, $\operatorname{r}(G) = \operatorname{l}(H)$ then
  $\operatorname{o}(G + H) = \mathscr{N}$.
  -/
  p1b : MisereOutcome g = .L → MisereOutcome h = .N →
    RTippingPoint hsg = LTippingPoint hsh → MisereOutcome (g + h) = .N
  /--
  2(a): if $\operatorname{o}(G) = \mathscr{R}$, $\operatorname{o}(H) =
  \mathscr{N}$, $\operatorname{n}(G) = \operatorname{r}(H)$ then
  $\operatorname{o}(G + H) = \mathscr{R}$.
  -/
  p2a : MisereOutcome g = .R → MisereOutcome h = .N →
    NTippingPoint hsg = RTippingPoint hsh → MisereOutcome (g + h) = .R
  /--
  2(b): if $\operatorname{o}(G) = \mathscr{R}$, $\operatorname{o}(H) =
  \mathscr{N}$, $\operatorname{l}(G) = \operatorname{r}(H)$ then
  $\operatorname{o}(G + H) = \mathscr{N}$.
  -/
  p2b : MisereOutcome g = .R → MisereOutcome h = .N →
    LTippingPoint hsg = RTippingPoint hsh → MisereOutcome (g + h) = .N
  /--
  3: if $\operatorname{o}(G), \operatorname{o}(H) = \mathscr{N}$,
  $\operatorname{r}(G) = \operatorname{l}(H)$ or $\operatorname{l}(G) =
  \operatorname{r}(H)$ then $\operatorname{o}(G + H) = \mathscr{N}$.
  -/
  p3 : MisereOutcome g = .N → MisereOutcome h = .N →
    (RTippingPoint hsg = LTippingPoint hsh ∨ LTippingPoint hsg = RTippingPoint hsh) →
    MisereOutcome (g + h) = .N
  /--
  4(a): if $\operatorname{o}(G) = \mathscr{L}$, $\operatorname{o}(H) =
  \mathscr{R}$, $\operatorname{n}(G) = \operatorname{l}(H)$ then
  $\operatorname{o}(G + H) = \mathscr{L}$.
  -/
  p4a : MisereOutcome g = .L → MisereOutcome h = .R →
    NTippingPoint hsg = LTippingPoint hsh → MisereOutcome (g + h) = .L
  /--
  4(b): if $\operatorname{o}(G) = \mathscr{L}$, $\operatorname{o}(H) =
  \mathscr{R}$, $\operatorname{n}(G) = \operatorname{n}(H)$ or
  $\operatorname{r}(G) = \operatorname{l}(H)$ then $\operatorname{o}(G + H) =
  \mathscr{N}$.
  -/
  p4b : MisereOutcome g = .L → MisereOutcome h = .R →
    (NTippingPoint hsg = NTippingPoint hsh ∨ RTippingPoint hsg = LTippingPoint hsh) →
    MisereOutcome (g + h) = .N
  /--
  4(c): if $\operatorname{o}(G) = \mathscr{L}$, $\operatorname{o}(H) =
  \mathscr{R}$, $\operatorname{r}(G) = \operatorname{n}(H)$ then
  $\operatorname{o}(G + H) = \mathscr{R}$.
  -/
  p4c : MisereOutcome g = .L → MisereOutcome h = .R →
    RTippingPoint hsg = NTippingPoint hsh → MisereOutcome (g + h) = .R

variable {A : GameForm → Prop}

/--
The induction hypothesis available when proving `Lemma317Claim` for `(g, h)`:
the full claim holds for every P-free pair `(g', h')` in $\mathcal{A}$ of
strictly smaller total birthday.
-/
private def Lemma317IH (g h : GameForm) : Prop :=
  ∀ g' h' (hsg' : IsShort g') (hsh' : IsShort h'),
    (PFreeSubset A) g' → (PFreeSubset A) h' →
    birthday g' + birthday h' < birthday g + birthday h →
    Lemma317Claim g' h' hsg' hsh'

section Helpers

variable [OutcomeStable A] [Form.Hereditary A] [ClosedUnderAddNat A]
  [ClosedUnderNeg A] [ClosedUnderAdd A] [IntegerInvertible A] [PropertyX A]

omit [PropertyX A] in
private theorem lemma317_hr_ge_N {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (heq : NTippingPoint hsg = LTippingPoint hsh) :
    ∀ hr ∈ moves .right h, MisereOutcome (g + hr) ≥ .N := by
  intro hr hr_mem
  have hAhr := Hereditary.has_option hAh (isOption_iff_mem_union.2 (Or.inr hr_mem))
  have hpfhr : IsPFree hr := isPFree_of_mem_moves hAh.isPFree hr_mem
  rcases hcase : MisereOutcome hr with _ | _ | _ | _
  · exact misereOutcome_add_ge_N_of_misereOutcome_L_left hAg hAhr hLg (Or.inr hcase)
  · exact misereOutcome_add_ge_N_of_misereOutcome_L_left hAg hAhr hLg (Or.inl hcase)
  · exact absurd hcase (PFree.misereOutcome_ne_P_of_pfree (A := IsPFree) hpfhr)
  · have hle : NTippingPoint (Short.of_mem_moves hsh hr_mem) ≤ LTippingPoint hsh :=
      NTippingPoint_le_LTippingPoint_of_mem_moves_right hAh hsh hr_mem
        (by rw [hcase]; decide)
    by_cases hlt : NTippingPoint (Short.of_mem_moves hsh hr_mem) < NTippingPoint hsg
    · exact pf_misereOutcome_add_ge_N_of_LR hAg hAhr hsg
        (Short.of_mem_moves hsh hr_mem) hLg hcase (Or.inl hlt)
    · have hN := (IH g hr hsg (Short.of_mem_moves hsh hr_mem) hAg hAhr
        (birthday_add_lt_right (birthday_lt_of_mem_moves hr_mem))).p4b hLg hcase
        (Or.inl (le_antisymm (le_of_not_gt hlt) (by rw [heq]; exact hle)))
      exact hN.ge

omit [PropertyX A] in
private theorem lemma317_p1a_gr {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (hNh : MisereOutcome h = .N)
    (heq : NTippingPoint hsg = LTippingPoint hsh) :
    ∀ gr ∈ moves .right g, MisereOutcome (gr + h) ≥ .N := by
  intro gr hgr
  by_cases hgrL : MisereOutcome gr = .L <;> simp_all +decide only [ge_iff_le]
  · exact
      misereOutcome_add_ge_N_of_misereOutcome_L_left
        (Hereditary.has_option hAg (isOption_iff_mem_union.2 (Or.inr hgr)))
        hAh hgrL (Or.inl hNh)
  · by_cases hgrN : MisereOutcome gr = .N
    · have hr' : NTippingPoint hsg ≤ RTippingPoint (Short.of_mem_moves hsg hgr) := by
        apply RTippingPoint_ge_NTippingPoint_of_mem_moves_right hAg hsg hLg hgr
      by_cases hlt : LTippingPoint hsh < RTippingPoint (Short.of_mem_moves hsg hgr)
      · exact pf_misereOutcome_add_ge_N_of_NN
          (Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inr hgr))) hAh
          (Short.of_mem_moves hsg hgr) hsh hgrN hNh (Or.inl hlt) |> le_trans (by decide)
      · have hN := (IH gr h (Short.of_mem_moves hsg hgr) hsh
          (Hereditary.has_option hAg (isOption_iff_mem_union.2 (Or.inr hgr))) hAh
          (birthday_add_lt_left (birthday_lt_of_mem_moves hgr))).p3 hgrN hNh
          (Or.inl (le_antisymm ( le_of_not_gt hlt ) ( heq ▸ hr' )))
        exact hN.ge
    · rcases misereOutcome_right_option_of_L_cases hAg hsg hLg hgr with h | h
      · exact absurd h hgrL
      · exact absurd h hgrN

omit [PropertyX A] in
private theorem lemma317_p1a {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (hNh : MisereOutcome h = .N)
    (heq : NTippingPoint hsg = LTippingPoint hsh) : MisereOutcome (g + h) = .L := by
  have hge : MisereOutcome (g + h) ≥ .N :=
    misereOutcome_add_ge_N_of_misereOutcome_L_left hAg hAh hLg (Or.inl hNh)
  have hnotend : ¬ IsEndLike .right (g + h) := PFree.not_isEndLike_right_add_of_L hAg hLg
  have hopts : ∀ x ∈ moves .right (g + h), MisereOutcome x ≥ .N := by
    intro x hx
    rw [Form.moves_add, Set.mem_union] at hx
    rcases hx with ⟨gr, gr_mem, rfl⟩ | ⟨hr, hr_mem, rfl⟩
    · exact lemma317_p1a_gr hAg hAh hsg hsh IH hLg hNh heq gr gr_mem
    · exact lemma317_hr_ge_N hAg hAh hsg hsh IH hLg heq hr hr_mem
  have hwin : ¬ WinsGoingFirst .right (g + h) :=
    not_winsGoingFirst_iff.2 ⟨hnotend, fun x hx => winsGoingFirst_left_of_ge_N (hopts x hx)⟩
  rcases hc : MisereOutcome (g + h) with _ | _ | _ | _
  · rfl
  · exact absurd (misereOutcome_N_iff_winsGoingFirst.mp hc).2 hwin
  · rw [hc] at hge; exact absurd hge (by decide)
  · rw [hc] at hge; exact absurd hge (by decide)

omit [ClosedUnderAdd A] [IntegerInvertible A] [PropertyX A] in
private theorem lemma317_p1b [HasInt A] {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (hNh : MisereOutcome h = .N)
    (heq : RTippingPoint hsg = LTippingPoint hsh) : MisereOutcome (g + h) = .N := by
  have hrg2 : 2 ≤ RTippingPoint hsg := by
    have ha := one_le_NTippingPoint_of_misereOutcome_L hsg hLg
    have hb := NTippingPoint_lt_RTippingPoint_of_misereOutcome_L hAg hsg hLg
    omega
  have hnotend : ¬ IsEnd .right h := by
    intro hend
    have h1 : LTippingPoint hsh = NTippingPoint hsh + 1 :=
      LTippingPoint_eq_NTippingPoint_add_one_of_isEnd_right hAh hsh hend
    have h2 : NTippingPoint hsh = 0 := NTippingPoint_eq_zero_of_N hsh hNh
    rw [h2] at h1
    omega
  obtain ⟨hr, hr_mem, hRhr, hnhr⟩ :
      ∃ hr, ∃ (hr_mem : hr ∈ moves .right h), MisereOutcome hr = .R ∧
        NTippingPoint (Short.of_mem_moves hsh hr_mem) = LTippingPoint hsh := by
    rcases isEnd_right_or_exists_NTippingPoint_eq_LTippingPoint_of_N
      hAh hsh hNh with ⟨hend, _⟩ | h
    · exact absurd hend hnotend
    · exact h
  have hAhr := Hereditary.has_option hAh (isOption_iff_mem_union.2 (Or.inr hr_mem))
  have hbd : birthday g + birthday hr < birthday g + birthday h :=
    birthday_add_lt_right (birthday_lt_of_mem_moves hr_mem)
  have hghrR : MisereOutcome (g + hr) = .R :=
    (IH g hr hsg (Short.of_mem_moves hsh hr_mem) hAg hAhr hbd).p4c hLg hRhr
      (by rw [heq]; exact hnhr.symm)
  have hwin : WinsGoingFirst .right (g + h) :=
    (winsGoingFirst_iff (g + h) .right).2 (Or.inr ⟨g + hr, add_left_mem_moves_add hr_mem g,
      fun hl => (misereOutcome_R_iff_winsGoingFirst.mp hghrR).2 hl⟩)
  have hge : MisereOutcome (g + h) ≥ .N :=
    misereOutcome_add_ge_N_of_misereOutcome_L_left hAg hAh hLg (Or.inl hNh)
  rcases hc : MisereOutcome (g + h) with _ | _ | _ | _
  · exact absurd hwin (misereOutcome_L_iff_winsGoingFirst.mp hc).2
  · rfl
  · rw [hc] at hge; exact absurd hge (by decide)
  · rw [hc] at hge; exact absurd hge (by decide)

omit [ClosedUnderAdd A] [IntegerInvertible A] in
private theorem lemma317_p3_left [HasInt A] {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hNg : MisereOutcome g = .N) (hNh : MisereOutcome h = .N)
    (heq : RTippingPoint hsg = LTippingPoint hsh) : WinsGoingFirst .left (g + h) := by
  rcases isEnd_left_or_exists_NTippingPoint_eq_RTippingPoint_of_N hAg hsg hNg
      with ⟨hgend, hrg1⟩ | ⟨gl, gl_mem, hglL, hgln⟩
  · have hlh1 : LTippingPoint hsh = 1 := by rw [← heq]; exact hrg1
    by_cases hhend : IsEnd .left h
    · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨hgend, hhend⟩)
    · have hN := PropertyX.prop_left hAg hAh hsg hsh hNg hNh hgend hhend hrg1 hlh1
      exact (misereOutcome_N_iff_winsGoingFirst.mp hN).1
  · have hAgl := Hereditary.has_option hAg (isOption_iff_mem_union.2 (Or.inl gl_mem))
    have hglh : MisereOutcome (gl + h) = .L :=
      (IH gl h (Short.of_mem_moves hsg gl_mem) hsh hAgl hAh
        (birthday_add_lt_left (birthday_lt_of_mem_moves gl_mem))).p1a hglL hNh (hgln.trans heq)
    exact (winsGoingFirst_iff (g + h) .left).2 (Or.inr ⟨gl + h,
      add_right_mem_moves_add gl_mem h,
      fun hr => (misereOutcome_L_iff_winsGoingFirst.mp hglh).2 hr⟩)

omit [ClosedUnderAdd A] [IntegerInvertible A] in
private theorem lemma317_p3 [HasInt A] {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hNg : MisereOutcome g = .N) (hNh : MisereOutcome h = .N)
    (heq : RTippingPoint hsg = LTippingPoint hsh ∨ LTippingPoint hsg = RTippingPoint hsh) :
    MisereOutcome (g + h) = .N := by
  have IHhg : Lemma317IH (A := A) h g := fun a b ha hb hAa hpa hlt =>
    IH a b ha hb hAa hpa (lt_of_lt_of_eq hlt (add_comm _ _))
  have IHngnh : Lemma317IH (A := A) (-g) (-h) := fun a b ha hb hAa hpa hlt =>
    IH a b ha hb hAa hpa (by rw [birthday_neg, birthday_neg] at hlt; exact hlt)
  have IHnhng : Lemma317IH (A := A) (-h) (-g) := fun a b ha hb hAa hpa hlt =>
    IH a b ha hb hAa hpa
      (by rw [birthday_neg, birthday_neg, add_comm (birthday h) (birthday g)] at hlt; exact hlt)
  have hNng : MisereOutcome (-g) = .N := misereOutcome_neg_N_iff_misereOutcome.mpr hNg
  have hNnh : MisereOutcome (-h) = .N := misereOutcome_neg_N_iff_misereOutcome.mpr hNh
  have hAng := ClosedUnderNeg.neg_of hAg
  have hAnh := ClosedUnderNeg.neg_of hAh
  have hL : WinsGoingFirst .left (g + h) := by
    rcases heq with h1 | h2
    · exact lemma317_p3_left hAg hAh hsg hsh IH hNg hNh h1
    · have hw := lemma317_p3_left hAh hAg hsh hsg IHhg hNh hNg h2.symm
      rwa [add_comm] at hw
  have hR : WinsGoingFirst .right (g + h) := by
    rcases heq with h1 | h2
    · have hw := lemma317_p3_left hAnh hAng (Short.neg hsh) (Short.neg hsg) IHnhng
        hNnh hNng (by rw [RTippingPoint_neg, LTippingPoint_neg]; exact h1.symm)
      have heqn : (-h) + (-g) = -(g + h) := by rw [neg_add]; exact add_comm _ _
      rw [heqn] at hw
      exact (winsGoingFirst_neg_iff (g + h) .left).mp hw
    · have hw := lemma317_p3_left hAng hAnh (Short.neg hsg) (Short.neg hsh) IHngnh
        hNng hNnh (by rw [RTippingPoint_neg, LTippingPoint_neg]; exact h2)
      have heqn : (-g) + (-h) = -(g + h) := (neg_add g h).symm
      rw [heqn] at hw
      exact (winsGoingFirst_neg_iff (g + h) .left).mp hw
  exact misereOutcome_N_iff_winsGoingFirst.mpr ⟨hL, hR⟩

omit [PropertyX A] in
private theorem lemma317_p4a_gr {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (hRh : MisereOutcome h = .R)
    (heq : NTippingPoint hsg = LTippingPoint hsh) :
    ∀ gr ∈ moves .right g, MisereOutcome (gr + h) ≥ .N := by
  intro gr hgr
  have hAgr := Hereditary.has_option hAg (isOption_iff_mem_union.2 (Or.inr hgr))
  have hr' : NTippingPoint hsg ≤ RTippingPoint (Short.of_mem_moves hsg hgr) :=
    RTippingPoint_ge_NTippingPoint_of_mem_moves_right hAg hsg hLg hgr
  have hle : LTippingPoint hsh ≤ RTippingPoint (Short.of_mem_moves hsg hgr) := heq ▸ hr'
  rcases misereOutcome_right_option_of_L_cases hAg hsg hLg hgr with hgrL | hgrN
  · rcases lt_or_eq_of_le hle with hlt | he
    · exact pf_misereOutcome_add_ge_N_of_LR hAgr hAh (Short.of_mem_moves hsg hgr) hsh
        hgrL hRh (Or.inr hlt)
    · have hN := (IH gr h (Short.of_mem_moves hsg hgr) hsh hAgr hAh
        (birthday_add_lt_left (birthday_lt_of_mem_moves hgr))).p4b hgrL hRh (Or.inr he.symm)
      exact hN.ge
  · rcases lt_or_eq_of_le hle with hlt | he
    · have hN := pf_misereOutcome_add_N_of_LTippingPoint_lt_RTippingPoint hAh hAgr hsh
        (Short.of_mem_moves hsg hgr) hRh hgrN hlt
      rw [add_comm] at hN; exact hN.ge
    · have hbd : birthday h + birthday gr < birthday g + birthday h := by
        have hlt' := birthday_lt_of_mem_moves hgr
        calc birthday h + birthday gr < birthday h + birthday g := by gcongr
          _ = birthday g + birthday h := add_comm _ _
      have hN := (IH h gr hsh (Short.of_mem_moves hsg hgr) hAh hAgr hbd).p2b
        hRh hgrN he
      rw [add_comm] at hN; exact hN.ge

omit [PropertyX A] in
private theorem lemma317_p4a {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (hRh : MisereOutcome h = .R)
    (heq : NTippingPoint hsg = LTippingPoint hsh) : MisereOutcome (g + h) = .L := by
  have hge : MisereOutcome (g + h) ≥ .N := by
    have hlt : NTippingPoint hsh < NTippingPoint hsg := by
      have := NTippingPoint_lt_RTippingPoint_of_misereOutcome_L
        (ClosedUnderNeg.neg_of hAh) (Short.neg hsh)
        (by rw [misereOutcome_neg_L_iff_misereOutcome]; exact hRh)
      rw [NTippingPoint.neg hsh, RTippingPoint_neg hsh] at this
      omega
    exact pf_misereOutcome_add_ge_N_of_LR hAg hAh hsg hsh hLg hRh (Or.inl hlt)
  have hnotend : ¬ IsEndLike .right (g + h) := PFree.not_isEndLike_right_add_of_L hAg hLg
  have hopts : ∀ x ∈ moves .right (g + h), MisereOutcome x ≥ .N := by
    intro x hx
    rw [Form.moves_add, Set.mem_union] at hx
    rcases hx with ⟨gr, gr_mem, rfl⟩ | ⟨hr, hr_mem, rfl⟩
    · exact lemma317_p4a_gr hAg hAh hsg hsh IH hLg hRh heq gr gr_mem
    · exact lemma317_hr_ge_N hAg hAh hsg hsh IH hLg heq hr hr_mem
  have hwin : ¬ WinsGoingFirst .right (g + h) :=
    not_winsGoingFirst_iff.2 ⟨hnotend, fun x hx => winsGoingFirst_left_of_ge_N (hopts x hx)⟩
  rcases hc : MisereOutcome (g + h) with _ | _ | _ | _
  · rfl
  · exact absurd (misereOutcome_N_iff_winsGoingFirst.mp hc).2 hwin
  · rw [hc] at hge; exact absurd hge (by decide)
  · rw [hc] at hge; exact absurd hge (by decide)

omit [PropertyX A] in
private theorem lemma317_add_left_option_R_eq_L {g h hl : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (hl_mem : hl ∈ moves .left h)
    (hle : LTippingPoint (Short.of_mem_moves hsh hl_mem) ≤ NTippingPoint hsg) :
    MisereOutcome (g + hl) = .L := by
  have hAhl := Hereditary.has_option hAh (isOption_iff_mem_union.2 (Or.inl hl_mem))
  rcases lt_or_eq_of_le hle with hlt | he
  · exact pf_misereOutcome_add_L_of_LTippingPoint_lt_NTippingPoint hAg hAhl hsg
      (Short.of_mem_moves hsh hl_mem) hLg hlt
  · have hbd : birthday g + birthday hl < birthday g + birthday h :=
      birthday_add_lt_right (birthday_lt_of_mem_moves hl_mem)
    rcases hcase : MisereOutcome hl with _ | _ | _ | _
    · exact OutcomeStable.misereOutcome_of_add_LL hAg hAhl hLg hcase
    · exact (IH g hl hsg (Short.of_mem_moves hsh hl_mem) hAg hAhl hbd).p1a hLg hcase
        he.symm
    · exact absurd hcase (PFree.misereOutcome_ne_P_of_pfree (A := IsPFree) hAhl.isPFree)
    · exact (IH g hl hsg (Short.of_mem_moves hsh hl_mem) hAg hAhl hbd).p4a hLg hcase
        he.symm

omit [PropertyX A] in
private theorem lemma317_p4b_left {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (hRh : MisereOutcome h = .R)
    (heq : NTippingPoint hsg = NTippingPoint hsh ∨ RTippingPoint hsg = LTippingPoint hsh) :
    WinsGoingFirst .left (g + h) := by
  have hnl : NTippingPoint hsh < LTippingPoint hsh :=
    NTippingPoint_lt_LTippingPoint_of_misereOutcome_R hAh hsh hRh
  have left_via_hl : ∀ (hl : GameForm) (hl_mem : hl ∈ moves .left h),
      LTippingPoint (Short.of_mem_moves hsh hl_mem) ≤ NTippingPoint hsg →
      WinsGoingFirst .left (g + h) := by
    intro hl hl_mem hle
    have hL := lemma317_add_left_option_R_eq_L hAg hAh hsg hsh IH hLg hl_mem hle
    exact (winsGoingFirst_iff (g + h) .left).2 (Or.inr ⟨g + hl,
      add_left_mem_moves_add hl_mem g,
      fun hr => (misereOutcome_L_iff_winsGoingFirst.mp hL).2 hr⟩)
  rcases heq with hnn | hrl
  · obtain ⟨hl, hl_mem, hlhl⟩ :=
      exists_mem_moves_left_LTippingPoint_eq_NTippingPoint hAh hsh hRh
    exact left_via_hl hl hl_mem (by rw [hlhl, ← hnn])
  · by_cases hcase : NTippingPoint hsg = RTippingPoint hsg - 1
    · obtain ⟨hl, hl_mem, hlhl⟩ :=
        exists_mem_moves_left_LTippingPoint_eq_NTippingPoint hAh hsh hRh
      refine left_via_hl hl hl_mem ?_
      rw [hlhl]
      omega
    · obtain ⟨gl, gl_mem, hglL, hgln⟩ :=
        exists_mem_moves_left_L_NTippingPoint_eq_RTippingPoint hAg hsg
          hLg hcase
      have hAgl := Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl gl_mem))
      have hglh : MisereOutcome (gl + h) = .L :=
        (IH gl h (Short.of_mem_moves hsg gl_mem) hsh hAgl hAh
          (birthday_add_lt_left (birthday_lt_of_mem_moves gl_mem))).p4a hglL hRh (hgln.trans hrl)
      exact (winsGoingFirst_iff (g + h) .left).2 (Or.inr ⟨gl + h,
        add_right_mem_moves_add gl_mem h,
        fun hr => (misereOutcome_L_iff_winsGoingFirst.mp hglh).2 hr⟩)

omit [PropertyX A] in
private theorem lemma317_p4b {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (hRh : MisereOutcome h = .R)
    (heq : NTippingPoint hsg = NTippingPoint hsh ∨ RTippingPoint hsg = LTippingPoint hsh) :
    MisereOutcome (g + h) = .N := by
  have hL : WinsGoingFirst .left (g + h) :=
    lemma317_p4b_left hAg hAh hsg hsh IH hLg hRh heq
  have IHnhng : Lemma317IH (A := A) (-h) (-g) := fun a b ha hb hAa hpa hlt =>
    IH a b ha hb hAa hpa
      (by rw [birthday_neg, birthday_neg, add_comm (birthday h) (birthday g)] at hlt; exact hlt)
  have hcond : NTippingPoint (Short.neg hsh) = NTippingPoint (Short.neg hsg)
      ∨ RTippingPoint (Short.neg hsh) = LTippingPoint (Short.neg hsg) := by
    rcases heq with h1 | h2
    · exact Or.inl (by rw [NTippingPoint.neg, NTippingPoint.neg]; exact h1.symm)
    · exact Or.inr (by rw [RTippingPoint_neg, LTippingPoint_neg]; exact h2.symm)
  have hw := lemma317_p4b_left
    (ClosedUnderNeg.neg_of hAh) (ClosedUnderNeg.neg_of hAg)
    (Short.neg hsh) (Short.neg hsg) IHnhng (misereOutcome_neg_L_iff_misereOutcome.mpr hRh)
    (misereOutcome_neg_R_iff_misereOutcome.mpr hLg) hcond
  have heqn : (-h) + (-g) = -(g + h) := by rw [neg_add]; exact add_comm _ _
  rw [heqn] at hw
  have hR : WinsGoingFirst .right (g + h) := (winsGoingFirst_neg_iff (g + h) .left).mp hw
  exact misereOutcome_N_iff_winsGoingFirst.mpr ⟨hL, hR⟩

omit [PropertyX A] in
private theorem lemma317_p2a {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hRg : MisereOutcome g = .R) (hNh : MisereOutcome h = .N)
    (heq : NTippingPoint hsg = RTippingPoint hsh) : MisereOutcome (g + h) = .R := by
  have IHn : Lemma317IH (A := A) (-g) (-h) := fun g' h' hsg' hsh' hAg' hpfg' hlt =>
    IH g' h' hsg' hsh' hAg' hpfg' (by rwa [birthday_neg, birthday_neg] at hlt)
  have heqn : NTippingPoint (Short.neg hsg) = LTippingPoint (Short.neg hsh) := by
    rw [NTippingPoint.neg, LTippingPoint_neg]; exact heq
  have key := lemma317_p1a
    (ClosedUnderNeg.neg_of hAg) (ClosedUnderNeg.neg_of hAh)
    (Short.neg hsg) (Short.neg hsh) IHn
    (misereOutcome_neg_L_iff_misereOutcome.mpr hRg)
    (misereOutcome_neg_N_iff_misereOutcome.mpr hNh) heqn
  rw [show g + h = -((-g) + (-h)) by rw [neg_add, neg_neg, neg_neg],
    misereOutcome_neg_R_iff_misereOutcome]
  exact key

omit [ClosedUnderAdd A] [IntegerInvertible A] [PropertyX A] in
private theorem lemma317_p2b [HasInt A] {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hRg : MisereOutcome g = .R) (hNh : MisereOutcome h = .N)
    (heq : LTippingPoint hsg = RTippingPoint hsh) : MisereOutcome (g + h) = .N := by
  have IHn : Lemma317IH (A := A) (-g) (-h) := fun g' h' hsg' hsh' hAg' hAh' hlt =>
    IH g' h' hsg' hsh' hAg' hAh' (by rwa [birthday_neg, birthday_neg] at hlt)
  have heqn : RTippingPoint (Short.neg hsg) = LTippingPoint (Short.neg hsh) := by
    rw [RTippingPoint_neg, LTippingPoint_neg]; exact heq
  have key := lemma317_p1b
    (ClosedUnderNeg.neg_of hAg) (ClosedUnderNeg.neg_of hAh)
    (Short.neg hsg) (Short.neg hsh) IHn (misereOutcome_neg_L_iff_misereOutcome.mpr hRg)
    (misereOutcome_neg_N_iff_misereOutcome.mpr hNh) heqn
  rw [show g + h = -((-g) + (-h)) by rw [neg_add, neg_neg, neg_neg],
    misereOutcome_neg_N_iff_misereOutcome]
  exact key

omit [PropertyX A] in
private theorem lemma317_p4c {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) (IH : Lemma317IH (A := A) g h)
    (hLg : MisereOutcome g = .L) (hRh : MisereOutcome h = .R)
    (heq : RTippingPoint hsg = NTippingPoint hsh) : MisereOutcome (g + h) = .R := by
  have IHn : Lemma317IH (A := A) (-h) (-g) := fun g' h' hsg' hsh' hAg' hAh' hlt =>
    IH g' h' hsg' hsh' hAg' hAh'
      (by rw [birthday_neg, birthday_neg, add_comm (birthday h) (birthday g)] at hlt; exact hlt)
  have heqn : NTippingPoint (Short.neg hsh) = LTippingPoint (Short.neg hsg) := by
    rw [NTippingPoint.neg, LTippingPoint_neg]; exact heq.symm
  have key := lemma317_p4a
    (ClosedUnderNeg.neg_of hAh) (ClosedUnderNeg.neg_of hAg)
    (Short.neg hsh) (Short.neg hsg) IHn
    (misereOutcome_neg_L_iff_misereOutcome.mpr hRh)
    (misereOutcome_neg_R_iff_misereOutcome.mpr hLg) heqn
  rw [show g + h = -((-h) + (-g)) by rw [neg_add, neg_neg, neg_neg, add_comm],
    misereOutcome_neg_R_iff_misereOutcome]
  exact key

/--
If $\mathcal{A}$ is an outcome-stable, hereditary, and integer-invertible
monoid that has Property X, and $G, H \in \operatorname{pf}(\mathcal{A})$, then
`Lemma317Claim` holds.

This is [Davies, Miller, Milley (Lemma 3.17 on p.
18)][davies:SumsPFreeForms:2025].
-/
theorem lemma_3_17 {g h : GameForm} (hsg : IsShort g) (hsh : IsShort h)
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h) :
    Lemma317Claim g h hsg hsh := by
  have IH : Lemma317IH (A := A) g h := fun g' h' hsg' hsh' hAg' hAh' hlt =>
    lemma_3_17 hsg' hsh' hAg' hAh'
  exact
    { p1a := fun hL hN heq => lemma317_p1a hAg hAh hsg hsh IH hL hN heq
      p1b := fun hL hN heq => lemma317_p1b hAg hAh hsg hsh IH hL hN heq
      p2a := fun hR hN heq => lemma317_p2a hAg hAh hsg hsh IH hR hN heq
      p2b := fun hR hN heq => lemma317_p2b hAg hAh hsg hsh IH hR hN heq
      p3 := fun hN1 hN2 heq => lemma317_p3 hAg hAh hsg hsh IH hN1 hN2 heq
      p4a := fun hL hR heq => lemma317_p4a hAg hAh hsg hsh IH hL hR heq
      p4b := fun hL hR heq => lemma317_p4b hAg hAh hsg hsh IH hL hR heq
      p4c := fun hL hR heq => lemma317_p4c hAg hAh hsg hsh IH hL hR heq }
termination_by birthday g + birthday h
decreasing_by exact hlt

/--
If $\mathcal{A}$ is an outcome-stable, hereditary, and integer-invertible
monoid with Property X, and $G, H \in \operatorname{pf}(\mathcal{A})$, then
$\operatorname{o}(G + H) \ne \mathscr{P}$.

This is [Davies, Miller, Milley (Lemma 3.18 on p.
22)][davies:SumsPFreeForms:2025].
-/
theorem misereOutcome_ne_P_of_propertyX {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) : MisereOutcome (g + h) ≠ .P := by
  have lr : ∀ (a b : GameForm), (PFreeSubset A) a → (PFreeSubset A) b →
      ∀ (hsa : IsShort a) (hsb : IsShort b), MisereOutcome a = .L → MisereOutcome b = .R →
      MisereOutcome (a + b) ≥ .N ∨ MisereOutcome (a + b) ≤ .N := by
    intro a b hAa hAb hsa hsb haL hbR
    rcases lt_trichotomy (NTippingPoint hsa) (NTippingPoint hsb) with h1 | h1 | h1
    · exact Or.inr (pf_misereOutcome_add_le_N_of_LR hAa hAb hsa hsb haL hbR (Or.inl h1))
    · exact Or.inl (ge_of_eq
        ((lemma_3_17 hsa hsb hAa hAb).p4b haL hbR (Or.inl h1)))
    · exact Or.inl (pf_misereOutcome_add_ge_N_of_LR hAa hAb hsa hsb haL hbR (Or.inl h1))
  have hmain : MisereOutcome (g + h) ≥ .N ∨ MisereOutcome (g + h) ≤ .N := by
    rcases hg : MisereOutcome g with _ | _ | _ | _
    · rcases hh : MisereOutcome h with _ | _ | _ | _
      · exact Or.inl (by rw [OutcomeStable.misereOutcome_of_add_LL hAg hAh hg hh]; decide)
      · exact Or.inl (misereOutcome_add_ge_N_of_misereOutcome_L_left hAg hAh hg (Or.inl hh))
      · exact absurd hh (PFree.misereOutcome_ne_P_of_pfree (A := IsPFree) hAh.isPFree)
      · exact lr g h hAg hAh hsg hsh hg hh
    · rcases hh : MisereOutcome h with _ | _ | _ | _
      · refine Or.inl ?_
        rw [add_comm]
        exact misereOutcome_add_ge_N_of_misereOutcome_L_left hAh hAg hh (Or.inl hg)
      · rcases lt_trichotomy (LTippingPoint hsh) (RTippingPoint hsg) with h1 | h1 | h1
        · exact Or.inl (pf_misereOutcome_add_ge_N_of_NN hAg hAh hsg hsh hg hh (Or.inl h1))
        · exact Or.inl (ge_of_eq
            ((lemma_3_17 hsg hsh hAg hAh).p3 hg hh (Or.inl h1.symm)))
        · exact Or.inr (pf_misereOutcome_add_le_N_of_NN hAg hAh hsg hsh hg hh (Or.inr h1))
      · exact absurd hh (PFree.misereOutcome_ne_P_of_pfree (A := IsPFree) hAh.isPFree)
      · refine Or.inr ?_
        rw [add_comm]
        rcases OutcomeStable.misereOutcome_of_add_RN hAh hAg hh hg with h' | h'
        <;> simp +decide only [h']
    · exact absurd hg (PFree.misereOutcome_ne_P_of_pfree (A := IsPFree) hAg.isPFree)
    · rcases hh : MisereOutcome h with _ | _ | _ | _
      · have := lr h g hAh hAg hsh hsg hh hg
        rwa [add_comm] at this
      · refine Or.inr ?_
        rcases OutcomeStable.misereOutcome_of_add_RN hAg hAh hg hh with h' | h'
        <;> simp +decide only [h']
      · exact absurd hh (PFree.misereOutcome_ne_P_of_pfree (A := IsPFree) hAh.isPFree)
      · exact Or.inr (by rw [OutcomeStable.misereOutcome_of_add_RR hAg hAh hg hh]; decide)
  intro hP
  rcases hmain with h | h <;> rw [hP] at h <;> exact absurd h (by decide)

/--
If $\mathcal{A}$ is an outcome-stable, hereditary, and integer-invertible
monoid with Property X, then $\operatorname{pf}(\mathcal{A})$ is a monoid.

This is [Davies, Miller, Milley (Lemma 3.19 on p.
23)][davies:SumsPFreeForms:2025].
-/
theorem isPFree_of_propertyX {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) : IsPFree (g + h) := by
  unfold IsPFree
  refine ⟨misereOutcome_ne_P_of_propertyX hAg hAh hsg hsh, ?_⟩
  intro p x hx
  rw [moves_add, Set.mem_union] at hx
  rcases hx with ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩
  · exact isPFree_of_propertyX (Hereditary.has_option hAg (IsOption.of_mem_moves hg'))
       hAh (Short.of_mem_moves hsg hg') hsh
  · exact isPFree_of_propertyX hAg (Hereditary.has_option hAh (IsOption.of_mem_moves hh'))
       hsg (Short.of_mem_moves hsh hh')
termination_by birthday g + birthday h
decreasing_by
  · have := birthday_lt_of_mem_moves hg'
    exact birthday_add_lt_left (birthday_lt_of_mem_moves hg')
  · exact birthday_add_lt_right (birthday_lt_of_mem_moves hh')

end Helpers

/--
If $\mathcal{A}$ is a subsemigroup of an outcome-stable, hereditary, and
integer-invertible monoid that has Property X, then either
$\operatorname{pf}(\mathcal{A})$ is a semigroup or else
$\operatorname{pf}(\mathcal{A}) = \emptyset$.

This is [Davies, Miller, Milley (Corollary 3.21 on p.
23)][davies:SumsPFreeForms:2025].
-/
theorem isPFree_of_subset_propertyX {S A : GameForm → Prop}
    [OutcomeStable S] [Form.Hereditary S] [ClosedUnderAddNat S]
    [ClosedUnderNeg S] [ClosedUnderAdd S] [IntegerInvertible S] [PropertyX S]
    (hAS : ∀ {x}, (PFreeSubset A) x → (PFreeSubset S) x) (hAadd : ∀ {x y}, A x → A y → A (x + y))
    {g h : GameForm} (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h) :
    IsPFree (g + h) ∧ A (g + h) :=
  ⟨isPFree_of_propertyX (A := S) (hAS hAg) (hAS hAh) hsg hsh, hAadd hAg.mem hAh.mem⟩

end

end IntegerInvertible

end MisereGames
