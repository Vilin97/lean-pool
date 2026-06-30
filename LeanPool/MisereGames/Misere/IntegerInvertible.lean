/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Misere.OutcomeStable

/-!
Misere combinatorial games.
-/

namespace MisereGames

open Form
open Form.Misere.Outcome
open GameForm
open OutcomeStable

universe u

public section

variable {A : GameForm → Prop}

/--
A set of games $\mathcal{A}$ is *integer-invertible*  if it contains every
integer $n$ and $n + \overline{n} =_{\mathcal{A}} 0$.

This is [Davies, Miller, Milley (Definition 3.12 on p.
15)][davies:SumsPFreeForms:2025].
-/
class IntegerInvertible (A : GameForm → Prop) : Prop extends HasInt A where
  int_add_neg_misereEQ (n : ℤ) :
    ((n : GameForm) + (-(n : GameForm))) =m A 0

/--
If $\mathcal{A}$ is integer-invertible then so is
$\operatorname{pf}(\mathcal{A})$.
-/
instance [IntegerInvertible A] : IntegerInvertible (PFreeSubset A) where
  has_int n := .mk (HasInt.has_int n) (isPFree_intCast n)
  int_add_neg_misereEQ n := fun x hx =>
    IntegerInvertible.int_add_neg_misereEQ (A := A) n x hx.mem

namespace IntegerInvertible

/--
If $0 \in \mathcal{A}$ and $G =_{\mathcal{A}} H$ then $\operatorname{o}(G) =
\operatorname{o}(H)$.
-/
theorem misereOutcome_eq_of_misereEQ [HasZero A] {g h : GameForm}
    (h1 : g =m A h) : MisereOutcome g = MisereOutcome h := by
  have := h1 0 HasZero.has_zero
  rwa [add_zero, add_zero] at this

/--
If $\mathcal{A}$ is integer-invertible, $G, H \in \mathcal{A}$, and $n \in
\mathbb{Z}$ then
$$
G + H =_{\mathcal{A}} (G + n) + (H - n).
$$
-/
theorem misereEQ_shift [ClosedUnderAdd A] [IntegerInvertible A] {g h : GameForm}
    (hg : A g) (hh : A h) (n : ℤ) :
    (g + h) =m A ((g + (n : GameForm)) + (h + (-(n : GameForm)))) := by
  have hrw : (g + (n : GameForm)) + (h + (-(n : GameForm)))
      = (g + h) + ((n : GameForm) + (-(n : GameForm))) := by
    rw [add_assoc, ← add_assoc (n : GameForm) h, add_comm (n : GameForm) h,
        add_assoc h, ← add_assoc g h]
  rw [hrw]
  have hgh : A (g + h) := ClosedUnderAdd.has_add g h hg hh
  have key : ((g + h) + ((n : GameForm) + (-(n : GameForm)))) =m A ((g + h) + 0) :=
    misereEQ_add_left hgh (IntegerInvertible.int_add_neg_misereEQ n)
  rw [add_zero] at key
  exact key.symm

/--
If $\mathcal{A}$ is integer-invertible, $G, H \in \mathcal{A}$, and $n \in \mathbb{Z}$ then
$$
\operatorname{o}(G + H) = \operatorname{o}((G + n) + (H - n)).
$$
-/
theorem misereOutcome_add_shift [ClosedUnderAdd A] [IntegerInvertible A] {g h : GameForm}
    (hg : A g) (hh : A h) (n : ℤ) :
    MisereOutcome (g + h) = MisereOutcome ((g + (n : GameForm)) + (h + (-(n : GameForm)))) :=
  misereOutcome_eq_of_misereEQ (misereEQ_shift hg hh n)

theorem misereOutcome_add_neg_NTippingPoint_N_of_misereOutcome_R {g : GameForm}
    [OutcomeStable A] [PFree A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : A g) (hsg : IsShort g) (hR : MisereOutcome g = .R) :
    MisereOutcome (g + (-(NTippingPoint hsg : GameForm))) = .N := by
  have := NTippingPoint_spec hsg
  contrapose! this
  constructor
  · intro h
    have := PFree.misereOutcome_add_natCast_R_of_misereOutcome_R (NTippingPoint hsg) hA hR
    simp_all +decide
  · exact this

theorem misereOutcome_add_RTippingPoint_pred_N_of_misereOutcome_L {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L) :
    MisereOutcome (g + (((RTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm)) = .N := by
  have hlt := NTippingPoint_lt_RTippingPoint_of_misereOutcome_L hA hsg hL
  -- The shift `r - 1` is `≥ n(G)`, so `o(G + (r-1)) ≤ o(G + n(G)) = N`.
  have h_le_N : MisereOutcome (g + (((RTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm)) ≤ .N := by
    have hle : (NTippingPoint hsg : ℤ) ≤ (RTippingPoint hsg : ℤ) - 1 := by omega
    have hmono := OutcomeStable.misereOutcome_add_int_antitone hA hle
    simp only [Form.intCast_nat] at hmono
    rwa [OutcomeStable.misereOutcome_add_NTippingPoint_N_of_misereOutcome_L hA hsg hL] at hmono
  -- Convert the integer shift `r - 1` to the natural number shift `r - 1`.
  have hcast : (((RTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm)
      = ((RTippingPoint hsg - 1 : ℕ) : GameForm) := by
    have hz : ((RTippingPoint hsg - 1 : ℕ) : ℤ) = (RTippingPoint hsg : ℤ) - 1 := by omega
    rw [← hz, Form.intCast_nat]
  rw [hcast] at h_le_N ⊢
  refine Or.resolve_right (Outcome.le_N_eq_N_or_R h_le_N) ?_
  exact misereOutcome_add_nat_ne_R_of_lt_RTippingPoint hsg (by omega)

theorem misereOutcome_add_NTippingPoint_pred_L_of_misereOutcome_L {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L) :
    MisereOutcome (g + (((NTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm)) = .L := by
  have hn1 := one_le_NTippingPoint_of_misereOutcome_L hsg hL
  have hcast : (((NTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm)
      = ((NTippingPoint hsg - 1 : ℕ) : GameForm) := by
    have hz : ((NTippingPoint hsg - 1 : ℕ) : ℤ) = (NTippingPoint hsg : ℤ) - 1 := by omega
    rw [← hz, Form.intCast_nat]
  rw [hcast]
  exact OutcomeStable.misereOutcome_add_nat_L_of_lt_NTippingPoint hA hsg hL (by omega)

theorem misereOutcome_add_int_neg_LTippingPoint_L {g : GameForm} (hsg : IsShort g) :
    MisereOutcome (g + (((-(LTippingPoint hsg : ℤ)) : ℤ) : GameForm)) = .L := by
  have h := misereOutcome_add_neg_LTippingPoint_L hsg
  simpa only [Form.intCast_neg, Form.intCast_nat] using h

theorem misereOutcome_add_ge_N_of_misereOutcome_L_left {g h : GameForm} [OutcomeStable A]
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h) (hL : MisereOutcome g = .L)
    (hh : MisereOutcome h = .N ∨ MisereOutcome h = .L) :
    MisereOutcome (g + h) ≥ .N := by
  rcases hh with hN | hL'
  · rcases OutcomeStable.misereOutcome_of_add_LN hAg hAh hL hN with h1 | h1
    · rw [h1]
    · rw [h1]; exact Outcome.L_ge _
  · rw [OutcomeStable.misereOutcome_of_add_LL hAg hAh hL hL']; exact Outcome.L_ge _

variable [OutcomeStable A] [ClosedUnderAddNat A] [ClosedUnderNeg A]
         [ClosedUnderAdd A] [IntegerInvertible A]

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{L}$
then if $\operatorname{n}(G) > \operatorname{l}(H)$ then $\operatorname{o}(G +
H) = \mathscr{L}$.

This is (1) in [Davies, Miller, Milley (Lemma 3.13 on p.
16)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_L_of_LTippingPoint_lt_NTippingPoint {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hLg : MisereOutcome g = .L) (hgt : LTippingPoint hsh < NTippingPoint hsg) :
    MisereOutcome (g + h) = .L := by
  set l := LTippingPoint hsh with hl
  have hshift := misereOutcome_add_shift (A := A) hAg.mem hAh.mem (l : ℤ)
  simp only [Form.intCast_nat] at hshift
  have hGL : MisereOutcome (g + (l : GameForm)) = .L :=
    misereOutcome_add_nat_L_of_lt_NTippingPoint hAg hsg hLg hgt
  have hHL : MisereOutcome (h + (-(l : GameForm))) = .L :=
    ((LTippingPoint_iff hsh l).mp hl.symm).1
  have hAgl := ClosedUnderAddNat.has_add hAg l
  have hAhl := ClosedUnderAddNat.has_add_neg hAh l
  rw [hshift]
  exact OutcomeStable.misereOutcome_of_add_LL hAgl hAhl hGL hHL

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{L}$
and $\operatorname{o}(H) = \mathscr{N}$, then if $\operatorname{r}(G) <
\operatorname{l}(H)$ then $\operatorname{o}(G + H) = \mathscr{N}$.

This is (2) in [Davies, Miller, Milley (Lemma 3.13 on p.
16)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_N_of_RTippingPoint_lt_LTippingPoint {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hLg : MisereOutcome g = .L) (hNh : MisereOutcome h = .N)
    (hlt : RTippingPoint hsg < LTippingPoint hsh) :
    MisereOutcome (g + h) = .N := by
  have hAgr := ClosedUnderAddNat.has_add hAg (RTippingPoint hsg)
  have hAhr := ClosedUnderAddNat.has_add_neg hAh (RTippingPoint hsg)
  have hR := misereOutcome_add_RTippingPoint_R hsg
  have hN := misereOutcome_add_neg_nat_N_of_misereOutcome_N hAh hsh hNh hlt
  have hshift := misereOutcome_add_shift (A := A) hAg.mem hAh.mem (RTippingPoint hsg : ℤ)
  simp only [Form.intCast_nat] at hshift
  have h_lower := misereOutcome_add_ge_N_of_misereOutcome_L_left hAg hAh hLg (Or.inl hNh)
  rw [hshift]
  rcases OutcomeStable.misereOutcome_of_add_RN hAgr hAhr hR hN with hc | hc
  · exact hc
  · rw [hshift, hc] at h_lower
    exact absurd h_lower (by decide)

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) =
\operatorname{o}(H) = \mathscr{N}$ then if $\operatorname{r}(G) >
\operatorname{l}(H)$ or $\operatorname{l}(G) < \operatorname{r}(H)$ then
$\operatorname{o}(G + H) \ge \mathscr{N}$.

This is [Davies, Miller, Milley (Lemma 3.14 on p.
16)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_ge_N_of_NN {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hNg : MisereOutcome g = .N) (hNh : MisereOutcome h = .N)
    (hcond : LTippingPoint hsh < RTippingPoint hsg ∨ LTippingPoint hsg < RTippingPoint hsh) :
    MisereOutcome (g + h) ≥ .N := by
  rcases hcond with hlt | hlt
  · have hAgl := ClosedUnderAddNat.has_add hAg (LTippingPoint hsh)
    have hAhl := ClosedUnderAddNat.has_add_neg hAh (LTippingPoint hsh)
    have hgN : MisereOutcome (g + (LTippingPoint hsh : GameForm)) = .N :=
      misereOutcome_add_nat_N_of_misereOutcome_N hAg hsg hNg hlt
    have hhL : MisereOutcome (h + (-(LTippingPoint hsh : GameForm))) = .L :=
      misereOutcome_add_neg_LTippingPoint_L hsh
    have hshift := misereOutcome_add_shift (A := A) hAg.mem hAh.mem (LTippingPoint hsh : ℤ)
    simp only [Form.intCast_nat] at hshift
    rw [hshift, add_comm]
    exact misereOutcome_add_ge_N_of_misereOutcome_L_left hAhl hAgl hhL (Or.inl hgN)
  · have hAgl := ClosedUnderAddNat.has_add_neg hAg (LTippingPoint hsg)
    have hAhl := ClosedUnderAddNat.has_add hAh (LTippingPoint hsg)
    have hgL := misereOutcome_add_neg_LTippingPoint_L hsg
    have hhN := misereOutcome_add_nat_N_of_misereOutcome_N hAh hsh hNh hlt
    have hshift := misereOutcome_add_shift (A := A) hAg.mem hAh.mem (-(LTippingPoint hsg : ℤ))
    simp only [Form.intCast_neg, Form.intCast_nat, neg_neg] at hshift
    rw [hshift]
    exact misereOutcome_add_ge_N_of_misereOutcome_L_left hAgl hAhl hgL (Or.inl hhN)

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{L}$
and $\operatorname{l}(H) < \operatorname{n}(G)$, then $\operatorname{o}(G + H)
= \mathscr{L}$.

This is (1) in [Davies, Miller, Milley (Lemma 3.15 on p.
17)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_L_of_LTippingPoint_lt_NTippingPoint_LR {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hLg : MisereOutcome g = .L) (hlt : LTippingPoint hsh < NTippingPoint hsg) :
    MisereOutcome (g + h) = .L :=
  pf_misereOutcome_add_L_of_LTippingPoint_lt_NTippingPoint hAg hAh hsg hsh hLg hlt

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{L}$,
$\operatorname{o}(H) = \mathscr{R}$ and $\operatorname{n}(G) >
\operatorname{n}(H)$ or $\operatorname{r}(G) > \operatorname{l}(H)$, then
$\operatorname{o}(G + H) \ge \mathscr{N}$.

This is (2) in [Davies, Miller, Milley (Lemma 3.15 on p.
17)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_ge_N_of_LR {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hLg : MisereOutcome g = .L) (hRh : MisereOutcome h = .R)
    (hcond : NTippingPoint hsh < NTippingPoint hsg ∨ LTippingPoint hsh < RTippingPoint hsg) :
    MisereOutcome (g + h) ≥ .N := by
  rcases hcond with hlt | hlt
  · have hgL : MisereOutcome (g + (((NTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm)) = .L :=
      misereOutcome_add_NTippingPoint_pred_L_of_misereOutcome_L hAg hsg hLg
    have hge : MisereOutcome (h + (-(((NTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm))) ≥ .N := by
      have hwitN := misereOutcome_add_neg_NTippingPoint_N_of_misereOutcome_R hAh hsh hRh
      have hle : (-(((NTippingPoint hsg : ℤ) - 1 : ℤ))) ≤ (-(NTippingPoint hsh : ℤ)) := by omega
      have hmono := misereOutcome_add_int_antitone hAh hle
      simp only [Form.intCast_neg, Form.intCast_nat] at hmono
      rwa [hwitN] at hmono
    have hdisj : MisereOutcome (h + (-(((NTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm))) = .N
        ∨ MisereOutcome (h + (-(((NTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm))) = .L := by
      rcases hc : MisereOutcome (h + (-(((NTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm)))
        with _ | _ | _ | _
      · exact Or.inr rfl
      · exact Or.inl rfl
      · rw [hc] at hge; exact absurd hge (by decide)
      · rw [hc] at hge; exact absurd hge (by decide)
    have hAgn := ClosedUnderAddNat.has_add_int hAg (((NTippingPoint hsg : ℤ) - 1 : ℤ))
    have hAhn := ClosedUnderAddNat.has_add_int_neg hAh (((NTippingPoint hsg : ℤ) - 1))
    have hshift := misereOutcome_add_shift (A := A) hAg.mem hAh.mem ((NTippingPoint hsg : ℤ) - 1)
    rw [hshift]
    exact misereOutcome_add_ge_N_of_misereOutcome_L_left hAgn hAhn hgL hdisj
  · have hgN : MisereOutcome (g + (((RTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm)) = .N :=
      misereOutcome_add_RTippingPoint_pred_N_of_misereOutcome_L hAg hsg hLg
    have hhL : MisereOutcome (h + (-(((RTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm))) = .L := by
      have hle : (-(((RTippingPoint hsg : ℤ) - 1 : ℤ))) ≤ (-(LTippingPoint hsh : ℤ)) := by omega
      have hL := misereOutcome_add_int_L_of_le hAh hle
        (misereOutcome_add_int_neg_LTippingPoint_L hsh)
      rwa [Form.intCast_neg] at hL
    have hAgn := ClosedUnderAddNat.has_add_int hAg ((RTippingPoint hsg : ℤ) - 1)
    have hAhn : (PFreeSubset A) (h + (-(((RTippingPoint hsg : ℤ) - 1 : ℤ) : GameForm))) := by
      have :=
          ClosedUnderNeg.neg_of
            (ClosedUnderAddNat.has_add_int (ClosedUnderNeg.neg_of hAh)
              ((((RTippingPoint hsg : ℤ) - 1 : ℤ))))
      simp only [neg_add_rev, neg_neg] at this
      rwa [add_comm] at this
    have hshift := misereOutcome_add_shift hAg.mem hAh.mem ((RTippingPoint hsg : ℤ) - 1)
    rw [hshift, add_comm]
    exact misereOutcome_add_ge_N_of_misereOutcome_L_left hAhn hAgn hhL (Or.inl hgN)

theorem pf_misereOutcome_add_le_N_of_LR {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hLg : MisereOutcome g = .L) (hRh : MisereOutcome h = .R)
    (hcond : NTippingPoint hsg < NTippingPoint hsh ∨ RTippingPoint hsg < LTippingPoint hsh) :
    MisereOutcome (g + h) ≤ .N := by
  have key := pf_misereOutcome_add_ge_N_of_LR
    (ClosedUnderNeg.neg_of hAh) (ClosedUnderNeg.neg_of hAg)
    (Short.neg hsh) (Short.neg hsg)
    (misereOutcome_neg_L_iff_misereOutcome.mpr hRh)
    (misereOutcome_neg_R_iff_misereOutcome.mpr hLg)
    (by rw [NTippingPoint.neg, NTippingPoint.neg, LTippingPoint_neg,
      RTippingPoint_neg]; exact hcond)
  have heqn : (-h) + (-g) = -(g + h) := by rw [neg_add]; exact add_comm _ _
  rw [heqn, ← misereOutcome_conjugate_neg] at key
  have h2 := Outcome.outcome_ge_conjugate_le key
  rwa [Outcome.conjugate_conjugate_eq_self, show (Outcome.N).Conjugate = Outcome.N from rfl] at h2

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{R}$
then if $\operatorname{r}(H) < \operatorname{n}(G)$ then $\operatorname{o}(G +
H) = \mathscr{R}$.

This is mirror of (1) in [Davies, Miller, Milley (Lemma 3.13 on p.
16)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_R_of_RTippingPoint_lt_NTippingPoint {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hRg : MisereOutcome g = .R) (hgt : RTippingPoint hsh < NTippingPoint hsg) :
    MisereOutcome (g + h) = .R := by
  have hng : MisereOutcome (-g) = .L := by rw [← misereOutcome_conjugate_neg, hRg]; rfl
  have hgt' : LTippingPoint (Short.neg hsh) < NTippingPoint (Short.neg hsg) := by
    rw [LTippingPoint_neg, NTippingPoint.neg]; exact hgt
  have hL := pf_misereOutcome_add_L_of_LTippingPoint_lt_NTippingPoint
    (ClosedUnderNeg.neg_of hAg) (ClosedUnderNeg.neg_of hAh)
    (Short.neg hsg) (Short.neg hsh) hng hgt'
  rw [← neg_neg (g + h), neg_add, ← misereOutcome_conjugate_neg, hL]; rfl

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{R}$
and $\operatorname{o}(H) = \mathscr{N}$, then if $\operatorname{l}(G) <
\operatorname{r}(H)$ then $\operatorname{o}(G + H) = \mathscr{N}$.

This is mirror of (2) in [Davies, Miller, Milley (Lemma 3.13 on p.
16)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_N_of_LTippingPoint_lt_RTippingPoint {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hRg : MisereOutcome g = .R) (hNh : MisereOutcome h = .N)
    (hlt : LTippingPoint hsg < RTippingPoint hsh) :
    MisereOutcome (g + h) = .N := by
  have hng : MisereOutcome (-g) = .L := by rw [← misereOutcome_conjugate_neg, hRg]; rfl
  have hnh : MisereOutcome (-h) = .N := by rw [← misereOutcome_conjugate_neg, hNh]; rfl
  have hlt' : RTippingPoint (Short.neg hsg) < LTippingPoint (Short.neg hsh) := by
    rw [RTippingPoint_neg, LTippingPoint_neg]; exact hlt
  have hN := pf_misereOutcome_add_N_of_RTippingPoint_lt_LTippingPoint
    (ClosedUnderNeg.neg_of hAg) (ClosedUnderNeg.neg_of hAh)
    (Short.neg hsg) (Short.neg hsh) hng hnh hlt'
  rw [show g + h = -((-g) + (-h)) by rw [neg_add, neg_neg, neg_neg],
    ← misereOutcome_conjugate_neg, hN]; rfl

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) =
\operatorname{o}(H) = \mathscr{N}$ then if $\operatorname{r}(G) <
\operatorname{l}(H)$ or $\operatorname{l}(G) > \operatorname{r}(H)$ then
$\operatorname{o}(G + H) \le \mathscr{N}$.

This is mirror of [Davies, Miller, Milley (Lemma 3.14 on p.
16)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_le_N_of_NN {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hNg : MisereOutcome g = .N) (hNh : MisereOutcome h = .N)
    (hcond : RTippingPoint hsh < LTippingPoint hsg ∨ RTippingPoint hsg < LTippingPoint hsh) :
    MisereOutcome (g + h) ≤ .N := by
  have hng : MisereOutcome (-g) = .N := by rw [← misereOutcome_conjugate_neg, hNg]; rfl
  have hnh : MisereOutcome (-h) = .N := by rw [← misereOutcome_conjugate_neg, hNh]; rfl
  have hcond' : LTippingPoint (Short.neg hsh) < RTippingPoint (Short.neg hsg)
      ∨ LTippingPoint (Short.neg hsg) < RTippingPoint (Short.neg hsh) := by
    rw [LTippingPoint_neg, RTippingPoint_neg, LTippingPoint_neg, RTippingPoint_neg]
    exact hcond
  have hge := pf_misereOutcome_add_ge_N_of_NN
    (ClosedUnderNeg.neg_of hAg) (ClosedUnderNeg.neg_of hAh)
    (Short.neg hsg) (Short.neg hsh) hng hnh hcond'
  have h_conj : MisereOutcome (g + h) = (MisereOutcome ((-g) + (-h))).Conjugate := by
    rw [show (-g) + (-h) = -(g + h) by rw [neg_add], misereOutcome_conjugate_neg, neg_neg]
  rw [h_conj]
  have h := Outcome.outcome_ge_conjugate_le hge
  rwa [show (Outcome.N).Conjugate = Outcome.N from rfl] at h

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{R}$
and $\operatorname{r}(H) < \operatorname{n}(G)$, then $\operatorname{o}(G + H)
= \mathscr{R}$.

This is mirror of (1) in [Davies, Miller, Milley (Lemma 3.15 on p.
17)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_R_of_RTippingPoint_lt_NTippingPoint_RL {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hRg : MisereOutcome g = .R) (hlt : RTippingPoint hsh < NTippingPoint hsg) :
    MisereOutcome (g + h) = .R :=
  pf_misereOutcome_add_R_of_RTippingPoint_lt_NTippingPoint hAg hAh hsg hsh hRg hlt

/--
If $\mathcal{A}$ is an outcome-stable and integer-invertible monoid, and $G, H
\in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{R}$,
$\operatorname{o}(H) = \mathscr{L}$ and $\operatorname{n}(G) <
\operatorname{n}(H)$ or $\operatorname{r}(H) < \operatorname{l}(G)$, then
$\operatorname{o}(G + H) \le \mathscr{N}$.

This is mirror of (2) in [Davies, Miller, Milley (Lemma 3.15 on p.
17)][davies:SumsPFreeForms:2025].
-/
theorem pf_misereOutcome_add_le_N_of_RL {g h : GameForm}
    (hAg : (PFreeSubset A) g) (hAh : (PFreeSubset A) h)
    (hsg : IsShort g) (hsh : IsShort h)
    (hRg : MisereOutcome g = .R) (hLh : MisereOutcome h = .L)
    (hcond : NTippingPoint hsh < NTippingPoint hsg ∨ RTippingPoint hsh < LTippingPoint hsg) :
    MisereOutcome (g + h) ≤ .N := by
  have hng : MisereOutcome (-g) = .L := by rw [← misereOutcome_conjugate_neg, hRg]; rfl
  have hnh : MisereOutcome (-h) = .R := by rw [← misereOutcome_conjugate_neg, hLh]; rfl
  have hcond' : NTippingPoint (Short.neg hsh) < NTippingPoint (Short.neg hsg)
      ∨ LTippingPoint (Short.neg hsh) < RTippingPoint (Short.neg hsg) := by
    rw [NTippingPoint.neg, NTippingPoint.neg, LTippingPoint_neg, RTippingPoint_neg]
    exact hcond
  have hge := pf_misereOutcome_add_ge_N_of_LR
    (ClosedUnderNeg.neg_of hAg) (ClosedUnderNeg.neg_of hAh)
    (Short.neg hsg) (Short.neg hsh)
    hng hnh hcond'
  have h_conj : MisereOutcome (g + h) = (MisereOutcome ((-g) + (-h))).Conjugate := by
    rw [show (-g) + (-h) = -(g + h) by rw [neg_add], misereOutcome_conjugate_neg, neg_neg]
  rw [h_conj]
  have h := Outcome.outcome_ge_conjugate_le hge
  rwa [show (Outcome.N).Conjugate = Outcome.N from rfl] at h

end IntegerInvertible

end

end MisereGames
