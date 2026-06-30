/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Misere.PFree
public import LeanPool.MisereGames.Misere.TippingPoints

/-!
Misere combinatorial games.
-/

namespace MisereGames

open Form
open Form.Misere.Outcome
open GameForm
open PFree

universe u

public section

/--
This is [Davies, Miller, Milley (Definition 3.4 on p.
9)][davies:SumsPFreeForms:2025].
-/
class OutcomeStable {G : Type (u + 1)} [Form G] (A : G → Prop) where
  misereOutcome_of_add_LL {g h : G}
      (h1 : (PFreeSubset A) g) (h2 : (PFreeSubset A) h)
      (h3 : MisereOutcome g = .L) (h4 : MisereOutcome h = .L) :
    MisereOutcome (g + h) = .L
  misereOutcome_of_add_RR {g h : G}
      (h1 : (PFreeSubset A) g) (h2 : (PFreeSubset A) h)
      (h3 : MisereOutcome g = .R) (h4 : MisereOutcome h = .R) :
    MisereOutcome (g + h) = .R
  miserePlayerOutcome_of_add_LN {g h : G}
      (h1 : (PFreeSubset A) g) (h2 : (PFreeSubset A) h)
      (h3 : MisereOutcome g = .L) (h4 : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .left = .left
  miserePlayerOutcome_of_add_RN {g h : G}
      (h1 : (PFreeSubset A) g) (h2 : (PFreeSubset A) h)
      (h3 : MisereOutcome g = .R) (h4 : MisereOutcome h = .N) :
    MiserePlayerOutcome (g + h) .right = .right

instance {G : Type (u + 1)} [Form G] (A : G → Prop) [OutcomeStable A] :
    OutcomeStable (PFreeSubset A) where
  misereOutcome_of_add_LL h1 h2 h3 h4 :=
    OutcomeStable.misereOutcome_of_add_LL h1.mem h2.mem h3 h4
  misereOutcome_of_add_RR h1 h2 h3 h4 :=
    OutcomeStable.misereOutcome_of_add_RR h1.mem h2.mem h3 h4
  miserePlayerOutcome_of_add_LN h1 h2 h3 h4 :=
    OutcomeStable.miserePlayerOutcome_of_add_LN h1.mem h2.mem h3 h4
  miserePlayerOutcome_of_add_RN h1 h2 h3 h4 :=
    OutcomeStable.miserePlayerOutcome_of_add_RN h1.mem h2.mem h3 h4

namespace OutcomeStable

theorem misereOutcome_of_add_LN {G : Type (u + 1)} [Form G] {A : G → Prop} [OutcomeStable A]
    {g h : G} (h1 : (PFreeSubset A) g) (h2 : (PFreeSubset A) h)
    (h3 : MisereOutcome g = .L) (h4 : MisereOutcome h = .N) :
    MisereOutcome (g + h) = .N ∨ MisereOutcome (g + h) = .L := by
  have h5 := miserePlayerOutcome_of_add_LN h1 h2 h3 h4
  simp only [MisereOutcome, Outcome.ofPlayers, h5]
  cases MiserePlayerOutcome (g + h) Player.right
  <;> simp only [reduceCtorEq, or_true, or_false]

theorem misereOutcome_of_add_RN {G : Type (u + 1)} [Form G] {A : G → Prop} [OutcomeStable A]
    {g h : G} (h1 : (PFreeSubset A) g) (h2 : (PFreeSubset A) h)
    (h3 : MisereOutcome g = .R) (h4 : MisereOutcome h = .N) :
    MisereOutcome (g + h) = .N ∨ MisereOutcome (g + h) = .R := by
  have h5 := miserePlayerOutcome_of_add_RN h1 h2 h3 h4
  simp only [MisereOutcome, Outcome.ofPlayers, h5]
  cases MiserePlayerOutcome (g + h) Player.left
  <;> simp only [reduceCtorEq, or_true, or_false]

/--
If $\mathcal{A}$ is outcome-stable, $n \in \mathbb{N}$ then $0
\ge_{\operatorname{pf}(\mathcal{A})} 1$.
-/
@[simp]
theorem zero_misereGE_one {A : GameForm → Prop}
    [HasNat A] [OutcomeStable A] :
    0 ≥m (PFreeSubset A) 1 := by
  rw [MisereGE]
  intro x h1
  rw [zero_add]
  cases h2 : MisereOutcome x
  · exact Outcome.L_ge (MisereOutcome (1 + x))
  · have h3 := misereOutcome_of_add_RN HasNat.one h1 one_misereOutcome_R h2
    apply Or.elim h3 <;> intro h3 <;> simp only [h3, ge_iff_le, le_refl, Outcome.ge_R]
  · exact False.elim (misereOutcome_ne_P_of_pfree h1 h2)
  · have h3 := misereOutcome_of_add_RR HasNat.one h1 one_misereOutcome_R h2
    rw [h3]

/--
If $\mathcal{A}$ is outcome-stable, $n \in \mathbb{N}$ then $n
\ge_{\operatorname{pf}(\mathcal{A})} 1 + n$.
-/
theorem nat_misereGE_one_add (A : GameForm → Prop)
    [OutcomeStable A] [ClosedUnderAddNat A] [HasNat A]
    (n : ℕ) : n ≥m (PFreeSubset A) (((1 : ℕ) + n) : ℕ) := by
  by_cases h1 : n > 0
  · rw [MisereGE]
    intro x h2
    simp only [Nat.cast_add, Nat.cast_one]
    rw [add_assoc _ _ x]
    nth_rw 2 [add_comm]
    cases h3 : MisereOutcome x
    · cases h4 : MisereOutcome (↑n + x)
      · simp only [ge_iff_le, Outcome.L_ge]
      · have h_A_nx : A (n + x) := by
          have := (ClosedUnderAddNat.has_add h2 n)
          rw [add_comm] at this
          exact this.mem
        have h_pfree_nx := isPFree_add_natCast h2.isPFree n
        rw [add_comm] at h_pfree_nx
        have h5 := misereOutcome_of_add_RN (A := A)
          HasNat.one (PFreeSubset.mk h_A_nx h_pfree_nx)
          one_misereOutcome_R h4
        rw [add_comm]
        apply Or.elim h5 <;> intro h5 <;> simp only [ge_iff_le, Outcome.ge_R, le_refl, h5]
      · exact False.elim (misereOutcome_ne_P_of_pfree ((isPFree_natCast_add (PFree.pfree h2)) n) h4)
      · simp only [ge_iff_le, Outcome.le_R_iff]
        exact misereOutcome_add_one_R_of_misereOutcome_R (isPFree_natCast_add (PFree.pfree h2) n) h4
    · have h4 := misereOutcome_of_add_RN
        (HasNat.has_nat n) h2
        ((misereOutcome_R_natCast_iff _).mpr h1) h3
      apply Or.elim h4 <;> intro h4
      · have h_A_nx : A (n + x) := by
          have := (ClosedUnderAddNat.has_add h2 n)
          rw [add_comm] at this
          exact this.mem
        have h_pfree_nx := isPFree_add_natCast h2.isPFree n
        rw [add_comm] at h_pfree_nx
        have h5 := misereOutcome_of_add_RN
          HasNat.one (PFreeSubset.mk h_A_nx h_pfree_nx)
          (one_misereOutcome_R) h4
        nth_rw 2 [add_comm]
        aesop
      · simp_all only [gt_iff_lt, reduceCtorEq, or_true, ge_iff_le, Outcome.le_R_iff]
        exact misereOutcome_add_one_R_of_misereOutcome_R (isPFree_natCast_add (PFree.pfree h2) n) h4
    · refine False.elim (misereOutcome_ne_P_of_pfree h2 h3)
    · have h4 := misereOutcome_of_add_RR
         (HasNat.has_nat n) h2
         ((misereOutcome_R_natCast_iff _).mpr h1) h3
      simp only [ge_iff_le, Outcome.le_R_iff, h4]
      exact misereOutcome_add_one_R_of_misereOutcome_R (isPFree_natCast_add (PFree.pfree h2) n) h4
  · simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h1
    simp only [h1, Nat.cast_zero, add_zero, Nat.cast_one, zero_misereGE_one]

/--
If $\mathcal{A}$ is outcome-stable, $n, m \in \mathbb{N}$, and $n \le m$ then
$n \ge_{\operatorname{pf}(\mathcal{A})} m$.
-/
theorem misereGE_of_nat_le (A : GameForm → Prop)
    [OutcomeStable A] [ClosedUnderAddNat A] [HasNat A]
    (n m : ℕ) (h1 : n ≤ m) : n ≥m (PFreeSubset A) m := by
  let k := m - n
  have h0 : m = n + k := by omega
  rw [h0]
  induction k with
  | zero => simp only [add_zero, Misere.Outcome.MisereGE.refl]
  | succ k' ih =>
    apply MisereGE.trans ih
    rw [<-add_assoc, add_comm (n + k') 1]
    exact nat_misereGE_one_add A (n + k')

/--
If $\mathcal{A}$ is outcome-stable, $n \in \mathbb{Z}$ then $n
\ge_{\operatorname{pf}(\mathcal{A})} 1 + n$.
-/
theorem int_misereGE_one_add (A : GameForm → Prop)
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (n : ℤ) : n ≥m (PFreeSubset A) (((1 : ℤ) + n) : ℤ) := by
  by_cases h1 : n ≥ 0
  · obtain ⟨n', h_n'⟩ := (CanLift.prf n h1 : ∃ (n' : ℕ), n' = n)
    have h2 := nat_misereGE_one_add A n'
    rwa [<-Form.intCast_nat, h_n',
         <-Form.intCast_nat, Nat.cast_add, h_n', Nat.cast_one] at h2
  · have : ∃ (n' : ℕ), n' = -n := by
      use n.natAbs; exact Int.ofNat_natAbs_of_nonpos (by omega)
    obtain ⟨n', h_n'⟩ := this
    have h2 := nat_misereGE_one_add A (n' - 1)
    have h3 : 1 + (n' - 1) = n' := by omega
    rw [h3] at h2
    rw [<-Form.intCast_nat, Nat.cast_sub (by omega), h_n',
        <-Form.intCast_nat, h_n',
        <-Misere.Outcome.ClosedUnderNeg.neg_ge_neg_iff] at h2
    simp only [Form.intCast_neg, neg_neg, Nat.cast_one] at h2
    rw [<-Form.intCast_neg] at h2
    simp only [neg_sub, sub_neg_eq_add] at h2
    exact h2

/--
If $\mathcal{A}$ is outcome-stable, $n \in \mathbb{N}$, $k \in \mathbb{Z}$ then
$k \ge_{\operatorname{pf}(\mathcal{A})} n + k$.
-/
theorem int_misereGE_nat_add (A : GameForm → Prop)
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (n : ℕ) (k : ℤ) : k ≥m (PFreeSubset A) ((n + k) : ℤ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    have h1 : m + 1 + k = 1 + (m + k) := by omega
    rw [h1]
    exact MisereGE.trans ih (int_misereGE_one_add A (m + k))

/--
If $\mathcal{A}$ is outcome-stable, $n, m \in \mathbb{Z}$, and $n \le m$ then
$n \ge_{\operatorname{pf}(\mathcal{A})} m$.
-/
theorem misereGE_of_int_le (A : GameForm → Prop)
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (n m : ℤ) (h1 : n ≤ m) : n ≥m (PFreeSubset A) m := by
  obtain ⟨k, h_k⟩ := Int.le.dest h1
  rw [<-h_k, add_comm]
  exact int_misereGE_nat_add A k n

variable {A : GameForm → Prop}

/--
If $\mathcal{A}$ is outcome-stable and $G \in \operatorname{pf}(\mathcal{A})$
then $\operatorname{o}(G + 1) \le \operatorname{o}(G)$.
-/
theorem misereOutcome_add_one_le {g : GameForm} [OutcomeStable A] [HasNat A]
    (hA : A g) (hpf : IsPFree g) :
    MisereOutcome (g + 1) ≤ MisereOutcome g := by
  have h_cases : MisereOutcome g = .L ∨ MisereOutcome g = .R ∨ MisereOutcome g = .N := by
    cases h : MisereOutcome g
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact False.elim ((PFree.misereOutcome_ne_P_of_pfree (A := IsPFree) hpf) h)
    · exact Or.inr (Or.inl rfl)
  obtain h | h | h := h_cases <;> simp_all +decide only [ Outcome.L_ge, Outcome.le_R_iff ]
  · convert PFree.misereOutcome_add_one_R_of_misereOutcome_R hpf h using 1
  · have h_add_one : MisereOutcome (1 + g) = .N ∨ MisereOutcome (1 + g) = .R := by
      convert
        misereOutcome_of_add_RN HasNat.one (PFreeSubset.mk hA hpf)
          one_misereOutcome_R h using 1
    rw [add_comm]
    aesop

/--
If $\mathcal{A}$ is outcome-stable and $G \in \operatorname{pf}(\mathcal{A})$
then $\operatorname{o}(G) \le \operatorname{o}(G - 1)$.
-/
theorem misereOutcome_le_add_negOne {g : GameForm} [OutcomeStable A] [HasNat A] [ClosedUnderNeg A]
    (hA : A g) (hpf : IsPFree g) :
    MisereOutcome g ≤ MisereOutcome (g + (-1)) := by
  have h_neg : MisereOutcome (-g + 1) ≤ MisereOutcome (-g) := by
    convert
      misereOutcome_add_one_le (ClosedUnderNeg.neg_iff.mpr hA)
        (ClosedUnderNeg.neg_iff.mpr hpf) using 1
  have h_neg_add : MisereOutcome (-(g + (-1))) = MisereOutcome (-g + 1) := by
    simp +decide only [neg_add_rev, neg_neg, neg_add_eq_sub]
    rfl
  have h_conj :
      MisereOutcome (-(g + (-1))) = (MisereOutcome (g + (-1))).Conjugate ∧
        MisereOutcome (-g) = (MisereOutcome g).Conjugate := by
    exact ⟨ Eq.symm ( misereOutcome_conjugate_neg _ ), Eq.symm ( misereOutcome_conjugate_neg _ ) ⟩
  cases h : MisereOutcome g <;> cases h' :
      MisereOutcome ( g + -1 ) <;> simp_all +decide only [Outcome.Conjugate]
  all_goals rw [ eq_comm ] at h_neg_add; simp_all +decide

/--
If $\mathcal{A}$ is outcome-stable, $G \in \operatorname{pf}(\mathcal{A})$, and
$n \in \mathbb{N}$ then $\operatorname{o}(G + n) \le \operatorname{o}(G)$.
-/
theorem misereOutcome_add_natCast_le {g : GameForm}
    [OutcomeStable A] [HasNat A] [ClosedUnderAdd A]
    (hA : A g) (hpf : IsPFree g) (n : ℕ) :
    MisereOutcome (g + (n : GameForm)) ≤ MisereOutcome g := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hAk : A (g + (k :
        GameForm)) := ClosedUnderAdd.has_add g (k : GameForm) hA (HasNat.has_nat k)
    have hpfk : IsPFree (g + (k : GameForm)) := isPFree_add_natCast hpf k
    have hstep := misereOutcome_add_one_le hAk hpfk
    have hcast : g + ((k + 1 : ℕ) : GameForm) = g + (k : GameForm) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, add_assoc]
    rw [hcast]
    exact le_trans hstep ih

/--
If $\mathcal{A}$ is outcome-stable, $G \in \operatorname{pf}(\mathcal{A})$, and
$k, m \in \mathbb{Z}$ and $k \le m$ then $\operatorname{o}(G + m) \le
\operatorname{o}(G + k)$.
-/
theorem misereOutcome_add_int_antitone {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) {k m : ℤ} (h : k ≤ m) :
    MisereOutcome (g + (m : GameForm)) ≤ MisereOutcome (g + (k : GameForm)) := by
  have hge := OutcomeStable.misereGE_of_int_le A k m h g hA
  rw [add_comm (g : GameForm) (m : GameForm), add_comm (g : GameForm) (k : GameForm)]
  exact hge

/--
If $G$ is $\mathscr{P}$-free and $n$ is an integer then $G + n$ is also
$\mathscr{P}$-free.

This is [Davies, Miller, Milley (Lemma 3.3 on p.
9)][davies:SumsPFreeForms:2025].
-/
theorem misereOutcome_add_int_ne_P {g : GameForm} (hA : (PFreeSubset A) g) (k : ℤ) :
    MisereOutcome (g + (k : GameForm)) ≠ .P := by
  have h := isPFree_add_intCast (PFree.pfree hA) k
  unfold IsPFree at h
  exact h.1

/--
The $\mathscr{L}$-region is downward closed: if $\operatorname{o}(G + m) =
\mathscr{L}$ and $k \le m$, then $\operatorname{o}(G + k) = \mathscr{L}$.
-/
theorem misereOutcome_add_int_L_of_le {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) {k m : ℤ} (h : k ≤ m) (hm : MisereOutcome (g + (m : GameForm)) = .L) :
    MisereOutcome (g + (k : GameForm)) = .L := by
  have hle := misereOutcome_add_int_antitone hA h
  rw [hm] at hle
  exact le_antisymm (Outcome.L_ge _) hle

/--
The $\mathscr{R}$-region is upward closed: if $\operatorname{o}(G + k) =
\mathscr{R}$ and $k \le m$, then $\operatorname{o}(G + m) = \mathscr{R}$.
-/
theorem misereOutcome_add_int_R_of_ge {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) {k m : ℤ} (h : k ≤ m) (hk : MisereOutcome (g + (k : GameForm)) = .R) :
    MisereOutcome (g + (m : GameForm)) = .R := by
  have hle := misereOutcome_add_int_antitone hA h
  rw [hk] at hle
  exact (Outcome.le_R_iff _).mp hle

/--
The outcome of an integer shift is always one of $\mathscr{L}$, $\mathscr{N}$,
$\mathscr{R}$ (never $\mathscr{P}$).
-/
theorem misereOutcome_add_int_cases {g : GameForm} (hA : (PFreeSubset A) g) (k : ℤ) :
    MisereOutcome (g + (k : GameForm)) = .L ∨ MisereOutcome (g + (k : GameForm)) = .N ∨
      MisereOutcome (g + (k : GameForm)) = .R := by
  have h := misereOutcome_add_int_ne_P hA k
  rcases hc : MisereOutcome (g + (k : GameForm)) with _ | _ | _ | _
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd hc h
  · exact Or.inr (Or.inr rfl)

/--
The $\mathscr{N}$-tipping point of a Left-win game lies strictly above $0$, and
its witness is the positive shift: $\operatorname{o}(G + \operatorname{n}(G)) =
\mathscr{N}$.
-/
theorem misereOutcome_add_NTippingPoint_N_of_misereOutcome_L {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L) :
    MisereOutcome (g + (NTippingPoint hsg : GameForm)) = .N := by
  rcases NTippingPoint_spec hsg with h | h
  · exact h
  · have hneg := PFree.misereOutcome_sub_natCast_L_of_misereOutcome_L (NTippingPoint hsg) hA hL
    rw [h] at hneg
    exact absurd hneg (by decide)

theorem misereOutcome_add_nat_L_of_lt_NTippingPoint {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L)
    {k : ℕ} (hk : k < NTippingPoint hsg) :
    MisereOutcome (g + (k : GameForm)) = .L := by
  have hkN : MisereOutcome (g + (k : GameForm)) ≠ .N :=
    fun hc => NTippingPoint_min hsg hk (Or.inl hc)
  have hNwit := misereOutcome_add_NTippingPoint_N_of_misereOutcome_L hA hsg hL
  have hmono := misereOutcome_add_int_antitone (A := A) hA
      (k := (k : ℤ)) (m := (NTippingPoint hsg : ℤ)) (by exact_mod_cast hk.le)
  simp only [Form.intCast_nat] at hmono
  rw [hNwit] at hmono
  have hP : MisereOutcome (g + (k : GameForm)) ≠ .P := by
    have h := misereOutcome_add_int_ne_P (A := A) hA (k : ℤ)
    simpa only [Form.intCast_nat] using h
  rcases hcase : MisereOutcome (g + (k : GameForm)) with _ | _ | _ | _
  · rfl
  · exact absurd hcase hkN
  · exact absurd hcase hP
  · rw [hcase] at hmono
    exact absurd hmono (by decide)

/--
Positive $\mathscr{N}$-region for a next-win game: if $\operatorname{o}(G) =
\mathscr{N}$ and $k < \operatorname{r}(G)$, then $\operatorname{o}(G + k) =
\mathscr{N}$.
-/
theorem misereOutcome_add_nat_N_of_misereOutcome_N {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) (hsg : IsShort g) (hN : MisereOutcome g = .N)
    {k : ℕ} (hk : k < RTippingPoint hsg) :
    MisereOutcome (g + (k : GameForm)) = .N := by
  have h_le_N : MisereOutcome (g + (k : GameForm)) ≤ .N := by
    have hmono := OutcomeStable.misereOutcome_add_int_antitone hA
      (show (0 : ℤ) ≤ (k : ℤ) by exact_mod_cast Nat.zero_le k)
    simpa only [Form.intCast_nat, Form.intCast_zero, add_zero, hN] using hmono
  exact Or.resolve_right (Outcome.le_N_eq_N_or_R h_le_N)
    (misereOutcome_add_nat_ne_R_of_lt_RTippingPoint hsg hk)

/--
Negative $\mathscr{N}$-region for a next-win game: if $\operatorname{o}(G) =
\mathscr{N}$ and $k < \operatorname{l}(G)$, then $\operatorname{o}(G - k) =
\mathscr{N}$.
-/
theorem misereOutcome_add_neg_nat_N_of_misereOutcome_N {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) (hsg : IsShort g) (hN : MisereOutcome g = .N)
    {k : ℕ} (hk : k < LTippingPoint hsg) :
    MisereOutcome (g + (-(k : GameForm))) = .N := by
  have hge : MisereOutcome (g + (-(k : GameForm))) ≥ .N := by
    have hmono := OutcomeStable.misereOutcome_add_int_antitone hA
      (show (-(k : ℤ)) ≤ (0 : ℤ) by omega)
    simpa only [Form.intCast_zero, add_zero, Form.intCast_neg, Form.intCast_nat, hN] using hmono
  have hne := misereOutcome_add_neg_nat_ne_L_of_lt_LTippingPoint hsg hk
  rcases h : MisereOutcome (g + (-(k : GameForm))) with _ | _ | _ | _
  · exact absurd h hne
  · rfl
  · rw [h] at hge; exact absurd hge (by decide)
  · rw [h] at hge; exact absurd hge (by decide)

/--
For a Left-win game, the $\mathscr{N}$-tipping point lies strictly below the
$\mathscr{R}$-tipping point.
-/
theorem NTippingPoint_lt_RTippingPoint_of_misereOutcome_L {g : GameForm}
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    (hA : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L) :
    NTippingPoint hsg < RTippingPoint hsg := by
  by_contra h
  have hle : (RTippingPoint hsg : ℤ) ≤ (NTippingPoint hsg : ℤ) := by
    exact_mod_cast Nat.le_of_not_lt h
  have hmono := OutcomeStable.misereOutcome_add_int_antitone hA hle
  simp only [Form.intCast_nat] at hmono
  rw [OutcomeStable.misereOutcome_add_NTippingPoint_N_of_misereOutcome_L hA hsg hL,
      misereOutcome_add_RTippingPoint_R hsg] at hmono
  exact absurd hmono (by decide)

/--
Shifting by a natural translates the $\mathscr{R}$-tipping point:
$\operatorname{r}(G + k) = \operatorname{r}(G) - k$.
-/
theorem RTippingPoint_add_natCast
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (k : ℕ)
    (hsk : IsShort (g + (k : GameForm))) :
    RTippingPoint hsk = RTippingPoint hsg - k := by
  have h_char : ∀ m : ℕ, MisereOutcome (g + (m : GameForm)) = .R ↔ RTippingPoint hsg ≤ m := by
    have := RTippingPoint_iff hsg
    intro n
    constructor <;> intro hn
    · exact ((this (RTippingPoint hsg)).mp rfl).right n hn
    · have h1 :=
        misereOutcome_add_int_R_of_ge hAg
          (show (RTippingPoint hsg : ℤ) ≤ n from by exact_mod_cast hn)
      norm_cast at h1
      apply h1
      exact ((this (RTippingPoint hsg)).mp rfl).left
  have h_char' (j : ℕ) :
      MisereOutcome ((g + (k : GameForm)) + (j : GameForm)) = .R ↔ RTippingPoint hsg ≤ k + j := by
    convert h_char (k + j) using 1
    rw [Nat.cast_add, add_assoc]
  apply (RTippingPoint_iff hsk (RTippingPoint hsg - k)).mpr
  grind only

/--
For a Left-win game, shifting by a natural $k \le \operatorname{n}(G)$
translates the $\mathscr{N}$-tipping point: $\operatorname{n}(G + k) =
\operatorname{n}(G) - k$.
-/
theorem NTippingPoint_add_natCast_of_L
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L) (k : ℕ)
    (hk : k ≤ NTippingPoint hsg) (hsk : IsShort (g + (k : GameForm))) :
    NTippingPoint hsk = NTippingPoint hsg - k := by
  have h_pos (j : ℕ) (hj : j < NTippingPoint hsg - k) :
      MisereOutcome ((g + (k : GameForm)) + (j : GameForm)) = .L := by
    have : k + j < NTippingPoint hsg := by omega
    convert misereOutcome_add_nat_L_of_lt_NTippingPoint hAg hsg hL this using 1
    simp only [add_assoc, Nat.cast_add]
  have h_neg (j : ℕ) (hj : j < NTippingPoint hsg - k) :
      MisereOutcome ((g + (k : GameForm)) + (-(j : GameForm))) = .L := by
    have hAk : (PFreeSubset A) (g + (k : GameForm)) := ClosedUnderAddNat.has_add hAg k
    have hm : MisereOutcome ((g + (k : GameForm)) + (((j : ℤ)) : GameForm)) = .L := by
      rw [Form.intCast_nat]
      exact h_pos j hj
    have hkey := misereOutcome_add_int_L_of_le hAk (show ((-(j : ℤ))) ≤ ((j : ℤ)) by omega) hm
    rwa [Form.intCast_neg, Form.intCast_nat] at hkey
  have h_upper_bound (j : ℕ) (hj : j < NTippingPoint hsg - k) :
      ¬(MisereOutcome ((g + (k : GameForm)) + (j : GameForm)) = .N
        ∨ MisereOutcome ((g + (k : GameForm)) + (-(j : GameForm))) = .N) := by
    simp [h_pos j hj, h_neg j hj]
  refine le_antisymm (Nat.le_of_not_lt ?_) (Nat.le_of_not_lt ?_)
  · intro h
    have := misereOutcome_add_NTippingPoint_N_of_misereOutcome_L hAg hsg hL
    have h1 : g + ↑(NTippingPoint hsg) = (g + ↑k) + ↑ (NTippingPoint hsg - k) := by
      rw [add_assoc, ←Nat.cast_add, Nat.add_sub_of_le hk]
    rw [h1] at this
    apply absurd (NTippingPoint_min hsk h)
    simp only [this, true_or, not_true_eq_false, not_false_eq_true]
  · intro hlt
    exact h_upper_bound _ hlt (NTippingPoint_spec hsk)

/--
If $\mathcal{A}$ is outcome-stable, hereditary monoid containing $1$ and $-1$,
and $G \in \operatorname{pf}(\mathcal{A})$, then $\operatorname{n}(G^L) \le
\operatorname{r}(G)$ for all Left options $G^L$ of $G$ with
$\operatorname{o}(G^L) \ne \mathscr{R}$.

This is [Davies, Miller, Milley (Lemma 3.7 on p.
13)][davies:SumsPFreeForms:2025].
-/
theorem NTippingPoint_le_RTippingPoint_of_mem_moves_left
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g gl : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g)
    (hgl : gl ∈ moves .left g) (hglR : MisereOutcome gl ≠ .R) :
    NTippingPoint (Short.of_mem_moves hsg hgl) ≤ RTippingPoint hsg := by
  by_contra h_contra
  have h_misereOutcome_g_R : MisereOutcome (g + (RTippingPoint hsg : GameForm)) = .R :=
    misereOutcome_add_RTippingPoint_R hsg
  have h_winsGoingFirst_gl_l : ¬WinsGoingFirst .left (g + (RTippingPoint hsg : GameForm)) := by
    intro h
    rw [misereOutcome_R_iff_winsGoingFirst] at h_misereOutcome_g_R
    exact h_misereOutcome_g_R.right h
  have h_winsGoingFirst_gl_r : WinsGoingFirst .right (gl + (RTippingPoint hsg : GameForm)) := by
    rw [not_winsGoingFirst_iff] at h_winsGoingFirst_gl_l
    exact h_winsGoingFirst_gl_l.right _ (add_right_mem_moves_add hgl _)
  have h_misereOutcome_gl_r : MisereOutcome (gl + (RTippingPoint hsg : GameForm)) ≠ .L := by
    intro h
    have := misereOutcome_L_iff_winsGoingFirst.mp h
    exact this.right h_winsGoingFirst_gl_r
  have h_pfree_gl : IsPFree gl :=
    PFree.pfree (Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl)))
  have h_misereOutcome_gl_P : MisereOutcome gl ≠ .P :=
    PFree.misereOutcome_ne_P_of_pfree h_pfree_gl
  have h_misereOutcome_gl_L : MisereOutcome gl = .L := by
    cases h : MisereOutcome gl <;> simp_all +decide only
    apply h_contra
    rw [NTippingPoint_eq_zero_of_N (Short.of_mem_moves hsg hgl) h]
    exact Nat.zero_le _
  apply h_misereOutcome_gl_r
  exact misereOutcome_add_nat_L_of_lt_NTippingPoint
          (Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl)))
          (Short.of_mem_moves hsg hgl)
          h_misereOutcome_gl_L
          (Nat.not_le.mp h_contra)

/--
If $\mathcal{A}$ is outcome-stable, hereditary monoid containing $1$ and $-1$,
and $G \in \operatorname{pf}(\mathcal{A})$, then $\operatorname{n}(G^R) \le
\operatorname{l}(G)$ for all Right options $G^R$ of $G$ with
$\operatorname{o}(G^R) \ne \mathscr{L}$.

This is the mirror of [Davies, Miller, Milley (Lemma 3.7 on p.
13)][davies:SumsPFreeForms:2025].
-/
theorem NTippingPoint_le_LTippingPoint_of_mem_moves_right
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g gr : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g)
    (hgr : gr ∈ moves .right g) (hgrL : MisereOutcome gr ≠ .L) :
    NTippingPoint (Short.of_mem_moves hsg hgr) ≤ LTippingPoint hsg := by
  have := NTippingPoint_le_RTippingPoint_of_mem_moves_left
            (ClosedUnderNeg.neg_of hAg) (gl := -gr)
            (ClosedUnderNeg.neg_of hsg) (by simp [hgr]) (by simp [hgrL])
  convert this using 1
  · exact (NTippingPoint.neg (Short.of_mem_moves hsg hgr)).symm
  · exact (RTippingPoint_neg hsg).symm

-- TODO: Move to TippingPoints
/--
If $G$ is a $\mathscr{P}$-free Left end with $\operatorname{o}(G) =
\mathscr{N}$, then $\operatorname{r}(G) = 1$.

This is [Davies, Miller, Milley (Lemma 3.8 on p.
13)][davies:SumsPFreeForms:2025].
-/
theorem RTippingPoint_eq_one_of_isEnd_left_N {g : GameForm} (hsg : IsShort g)
    (hpf : IsPFree g) (hend : IsEnd .left g) (hN : MisereOutcome g = .N) :
    RTippingPoint hsg = 1 := by
  have hand : MisereOutcome (g + ((1 : ℕ) : GameForm)) = .R := by
    have h_pfree : IsPFree (g + 1) := isPFree_add_one hpf
    have h_not_left : ¬WinsGoingFirst .left (g + 1) := by
      rw [not_winsGoingFirst_iff]
      have := misereOutcome_N_iff_winsGoingFirst.mp hN
      simp_all only [isEndLike_iff_isEnd, winsGoingFirst_of_isEndLike, Player.right_le, true_and,
                     IsEndLike.add_iff, not_isEndLike_left_one, and_false, not_false_eq_true,
                     moves_add, leftMoves_one, Set.image_singleton, add_zero, Set.union_singleton,
                     Set.mem_insert_iff, Set.mem_image, not_mem_moves_of_isEnd, false_and,
                     exists_const, or_false, Player.neg_left, Player.le_right_eq, implies_true]
    cases h : MisereOutcome (g + 1)
    · absurd h_not_left
      exact minsGoingFirst_left_of_misereOutcome_L h
    · rw [misereOutcome_N_iff_winsGoingFirst] at h
      absurd h_not_left
      exact h.left
    · exact False.elim ((PFree.misereOutcome_ne_P_of_pfree h_pfree) h)
    · simpa only [Nat.cast_one] using h
  refine (RTippingPoint_iff hsg 1).mpr ⟨ hand, fun x hx => ?_⟩
  apply Nat.one_le_iff_ne_zero.mpr
  intro hx0
  subst hx0
  simp_all only [Nat.cast_one, Nat.cast_zero, add_zero, reduceCtorEq]

/--
If $\mathcal{A}$ is outcome-stable, hereditary monoid containing $1$ and $-1$,
and $G \in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) =
\mathscr{N}$, then either $G$ is Left end-like with $\operatorname{r}(G) = 1$,
or else there exists a Left option $G^L$ of $G$ with $\operatorname{o}(G^L) =
\mathscr{L}$ such that $\operatorname{n}(G^L) = r(G)$.

This is [Davies, Miller, Milley (Lemma 3.9 on p.
13)][davies:SumsPFreeForms:2025].
-/
theorem isEnd_left_or_exists_NTippingPoint_eq_RTippingPoint_of_N
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hN : MisereOutcome g = .N) :
    (IsEnd .left g ∧ RTippingPoint hsg = 1) ∨
      (∃ gl, ∃ (hgl : gl ∈ moves .left g), MisereOutcome gl = .L ∧
        NTippingPoint (Short.of_mem_moves hsg hgl) = RTippingPoint hsg) := by
  by_cases h : IsEndLike .left ( g + ( RTippingPoint hsg - 1 : ℕ ) )
  · simp only [IsEndLike.add_iff, isEndLike_iff_isEnd, natCast_isEndLike_iff,
    isEnd_left_natCast_iff] at h
    obtain ⟨h1, h2⟩ := h
    apply Or.inl
    exact ⟨h1, RTippingPoint_eq_one_of_isEnd_left_N hsg (PFree.pfree hAg) h1 hN⟩
  · simp only [IsEndLike.add_iff, isEndLike_iff_isEnd, isEnd_left_natCast_iff,
               natCast_isEndLike_iff, not_and, exists_and_left] at h ⊢
    obtain ⟨g', hg', hwin⟩ :
        ∃ g', g' ∈ moves .left (g + (RTippingPoint hsg - 1 : ℕ)) ∧ ¬WinsGoingFirst .right g' := by
      have hwin : WinsGoingFirst .left (g + (RTippingPoint hsg - 1 : ℕ)) := by
        have hwin : MisereOutcome (g + (RTippingPoint hsg - 1 : ℕ)) = .N := by
          apply misereOutcome_add_nat_N_of_misereOutcome_N hAg hsg hN
          refine Nat.pred_lt (ne_bot_of_gt (Nat.pos_of_ne_zero ?_))
          have := misereOutcome_add_RTippingPoint_R hsg
          intro h_contra
          simp_all only [Nat.sub_eq, Nat.sub_zero, Nat.cast_zero, add_zero, reduceCtorEq]
        rw [misereOutcome_N_iff_winsGoingFirst] at hwin
        simp only [hwin]
      have := winsGoingFirst_iff (g + (RTippingPoint hsg - 1 : ℕ)) Player.left
      aesop
    obtain ⟨gl, hgl, rfl⟩ | ⟨m, hm, rfl⟩ :
        (∃ gl ∈ moves .left g, g' = gl + (RTippingPoint hsg - 1 : ℕ))
        ∨ (∃ m ∈ moves .left ((RTippingPoint hsg - 1 : ℕ) : GameForm), g' = g + m) := by
      rw [moves_add] at hg'
      aesop
    · have hglL : MisereOutcome (gl + (RTippingPoint hsg - 1 : ℕ)) = .L := by
        cases h : MisereOutcome (gl + ↑(RTippingPoint hsg - 1))
        · rfl
        · absurd h
          simp [misereOutcome_N_iff_winsGoingFirst, hwin]
        · absurd h
          apply PFree.misereOutcome_ne_P_of_pfree (A := IsPFree)
          have hglL := PFree.pfree (Hereditary.has_option hAg (IsOption.of_mem_moves hgl))
          exact isPFree_add_natCast hglL _
        · simp only [h, winsGoingFirst_right_of_misereOutcome_R, not_true_eq_false] at hwin
      have hglL' : MisereOutcome gl = .L := by
        by_cases hglN : MisereOutcome gl = .N
        · have h_gl := Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl))
          have h_rtip : (0 : ℤ) ≤ (RTippingPoint hsg - 1 : ℕ) := Int.natCast_nonneg _
          have := misereOutcome_add_int_antitone h_gl h_rtip
          simp +decide only [Form.intCast_nat, Form.intCast_ofNat, Nat.cast_zero, add_zero, hglL,
            hglN] at this
        · by_cases hglR : MisereOutcome gl = .R
          · have h_gl := Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl))
            have :=
                PFree.misereOutcome_add_natCast_R_of_misereOutcome_R
                  (RTippingPoint hsg - 1) h_gl hglR
            rw [hglL] at this
            absurd this
            decide
          · cases h : MisereOutcome gl
            · rfl
            · exact False.elim (hglN h)
            · exfalso
              have :=
                  PFree.pfree (Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl)))
              simp only [moves_add, Set.mem_union, Set.mem_image] at hg'
              exact PFree.misereOutcome_ne_P_of_pfree this h
            · exact False.elim (hglR h)
      have hglN : NTippingPoint (Short.of_mem_moves hsg hgl) ≥ RTippingPoint hsg := by
        contrapose! hglL
        have h_mem := (Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl)))
        have h_le : (NTippingPoint (Short.of_mem_moves hsg hgl) : ℤ) ≤ ((RTippingPoint hsg - 1) :
            ℤ) :=
          le_tsub_of_add_le_right (mod_cast hglL)
        have h_outcome_le := misereOutcome_add_int_antitone h_mem h_le
        have h_outcome_N := misereOutcome_add_NTippingPoint_N_of_misereOutcome_L
                              (Hereditary.has_option hAg (isOption_iff_mem_union.2 ( Or.inl hgl)))
                              (Short.of_mem_moves hsg hgl)
                              hglL'
        simp only [Form.intCast_nat, h_outcome_N] at h_outcome_le
        cases h' : RTippingPoint hsg
        · omega
        · cases h : MisereOutcome (gl + ↑‹ℕ›)
          · simp only [h, h', Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Form.intCast_nat]
                      at h_outcome_le
            absurd h_outcome_le
            decide
          · simp only [h, add_tsub_cancel_right, ne_eq, reduceCtorEq, not_false_eq_true]
          · simp only [h, add_tsub_cancel_right, ne_eq, reduceCtorEq, not_false_eq_true]
          · simp only [h, add_tsub_cancel_right, ne_eq, reduceCtorEq, not_false_eq_true]
      refine Or.inr ⟨ gl, hglL', hgl, le_antisymm ?_ hglN ⟩
      apply NTippingPoint_le_RTippingPoint_of_mem_moves_left hAg hsg hgl (by
      aesop)
    · have h_contra : MisereOutcome (g + (RTippingPoint hsg - 2 : ℕ)) = .N := by
        apply misereOutcome_add_nat_N_of_misereOutcome_N hAg hsg hN
        rcases n : RTippingPoint hsg with ( _ | _ | n ) <;> simp_all +decide
      absurd hwin
      rw [misereOutcome_N_iff_winsGoingFirst] at h_contra
      have hm_eq : m = ((RTippingPoint hsg - 2 : ℕ) : GameForm) := by
        rcases n : RTippingPoint hsg with ( _ | _ | n ) <;> simp_all +decide
      simpa [hm_eq] using h_contra.right

/--
If $\mathcal{A}$ is outcome-stable, hereditary monoid containing $1$ and $-1$,
and $G \in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) =
\mathscr{N}$, then either $G$ is Right end-like with $\operatorname{l}(G) = 1$,
or else there exists a Left option $G^R$ of $G$ with $\operatorname{o}(G^R) =
\mathscr{R}$ such that $\operatorname{n}(G^R) = l(G)$.

This is mirror of [Davies, Miller, Milley (Lemma 3.9 on p.
13)][davies:SumsPFreeForms:2025].
-/
theorem isEnd_right_or_exists_NTippingPoint_eq_LTippingPoint_of_N
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hN : MisereOutcome g = .N) :
    (IsEnd .right g ∧ LTippingPoint hsg = 1) ∨
      (∃ gr, ∃ (hgr : gr ∈ moves .right g), MisereOutcome gr = .R ∧
        NTippingPoint (Short.of_mem_moves hsg hgr) = LTippingPoint hsg) := by
  convert
    isEnd_left_or_exists_NTippingPoint_eq_RTippingPoint_of_N
      (ClosedUnderNeg.neg_of hAg) (Short.neg hsg) _ using 1
  · rw [ show IsEnd Player.right g = IsEnd Player.left ( -g ) from ?_ ]
    · rw [ RTippingPoint_neg ]
    · rw [ show IsEnd Player.right g = ( moves Player.right g = ∅ ) from ?_,
      show IsEnd Player.left ( -g ) = ( moves Player.left ( -g ) = ∅ ) from ?_ ]
      · simp +decide [ Set.ext_iff ]
      · exact isEnd_def Player.left (-g)
      · exact isEnd_def Player.right g
  · constructor <;> rintro ⟨ gr, hgr, hgr' ⟩
    · use -gr
      simp_all +decide only [misereOutcome_neg_L_iff_misereOutcome, moves_neg,
        Player.neg_left, Set.mem_neg, neg_neg, exists_and_left]
      refine ⟨trivial, ?_⟩
      refine ⟨trivial, ?_⟩
      convert hgr'.2 using 1
      · convert NTippingPoint.neg _
      · exact RTippingPoint_neg hsg
    · use -gr
      use by
        rw [ Form.moves_neg ] at hgr
        exact Set.mem_neg.mp hgr
      generalize_proofs at *
      have := misereOutcome_conjugate_neg gr
      simp_all +decide only [misereOutcome_neg_R_iff_misereOutcome]
      refine ⟨trivial, ?_⟩
      convert hgr'.2 using 1
      · exact NTippingPoint.neg _
      · exact (RTippingPoint_neg hsg).symm
  · rw [ ← misereOutcome_conjugate_neg, hN, Outcome.Conjugate ]

/--
If $\mathcal{A}$ is outcome-stable, hereditary monoid containing $1$ and $-1$,
and $G \in \operatorname{pf}(\mathcal{A})$ is a Left end then
$\operatorname{r}(G) = \operatorname{n}(G) + 1$.

This is [Davies, Miller, Milley (Lemma 3.10 on p.
13)][davies:SumsPFreeForms:2025].
-/
theorem RTippingPoint_eq_NTippingPoint_add_one_of_isEnd_left
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hend : IsEnd .left g) :
    RTippingPoint hsg = NTippingPoint hsg + 1 := by
  have h_outcome : MisereOutcome g = .N ∨ MisereOutcome g = .L :=
    PFree.misereOutcome_of_isEnd_left hAg hend
  rcases h_outcome with hgN | hgL
  · have h1 := RTippingPoint_eq_one_of_isEnd_left_N hsg (PFree.pfree hAg) hend hgN
    have h2 := NTippingPoint_eq_zero_of_N hsg hgN
    omega
  · have hAgN := ClosedUnderAddNat.has_add hAg (NTippingPoint hsg)
    have hsgN : IsShort (g + (NTippingPoint hsg : GameForm)) :=
      Short.add hsg (Short.natCast (NTippingPoint hsg))
    have hNN : MisereOutcome (g + (NTippingPoint hsg : GameForm)) = .N :=
      misereOutcome_add_NTippingPoint_N_of_misereOutcome_L hAg hsg hgL
    have hn1 : 1 ≤ NTippingPoint hsg := one_le_NTippingPoint_of_misereOutcome_L hsg hgL
    obtain ⟨HL, hHL₁, hHL₂, hHL₃⟩ :
        ∃ HL, ∃ (hHL : HL ∈ moves .left (g + (NTippingPoint hsg : GameForm))),
          MisereOutcome HL = .L ∧
            NTippingPoint (Short.of_mem_moves hsgN hHL) = RTippingPoint hsgN := by
      rcases isEnd_left_or_exists_NTippingPoint_eq_RTippingPoint_of_N hAgN hsgN hNN with
        ⟨hEnd, _⟩ | hex
      · exfalso
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show NTippingPoint hsg ≠ 0 by omega)
        have hmem : g + ((k : ℕ) : GameForm) ∈ moves .left (g + (NTippingPoint hsg :
            GameForm)) := by
          rw [hk]
          exact add_left_mem_moves_add (by rw [leftMoves_natCast_succ']; exact rfl) g
        rw [isEnd_def] at hEnd
        rw [hEnd] at hmem
        exact (Set.mem_empty_iff_false _).mp hmem
      · exact hex
    have hHL_form : HL = g + ((NTippingPoint hsg - 1 : ℕ) : GameForm) := by
      rw [moves_add] at hHL₁
      rcases hHL₁ with h | h
      · rw [show gᴸ = ∅ from isEnd_def Player.left g ▸ hend, Set.image_empty] at h
        exact ((Set.mem_empty_iff_false _).mp h).elim
      · obtain ⟨m, hm, rfl⟩ := h
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show NTippingPoint hsg ≠ 0 by omega)
        rw [hk, leftMoves_natCast_succ', Set.mem_singleton_iff] at hm
        subst hm
        rw [hk, Nat.succ_sub_one]
    subst hHL_form
    have hr : RTippingPoint hsgN = RTippingPoint hsg - NTippingPoint hsg :=
      RTippingPoint_add_natCast hAg hsg (NTippingPoint hsg) hsgN
    have hnsub : NTippingPoint (Short.of_mem_moves hsgN hHL₁)
        = NTippingPoint hsg - (NTippingPoint hsg - 1) :=
      NTippingPoint_add_natCast_of_L hAg hsg hgL (NTippingPoint hsg - 1) (by omega)
        (Short.of_mem_moves hsgN hHL₁)
    omega

/--
If $\mathcal{A}$ is outcome-stable, hereditary monoid containing $1$ and $-1$,
and $G \in \operatorname{pf}(\mathcal{A})$ is a Right end then
$\operatorname{l}(G) = \operatorname{n}(G) + 1$.

This is the mirror of [Davies, Miller, Milley (Lemma 3.10 on p.
13)][davies:SumsPFreeForms:2025].
-/
theorem LTippingPoint_eq_NTippingPoint_add_one_of_isEnd_right
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hend : IsEnd .right g) :
    LTippingPoint hsg = NTippingPoint hsg + 1 := by
  have := RTippingPoint_eq_NTippingPoint_add_one_of_isEnd_left
            (ClosedUnderNeg.neg_of hAg) (Short.neg hsg) (IsEnd.neg_iff_neg.mpr hend)
  rw [<-RTippingPoint_neg hsg]
  rwa [NTippingPoint.neg] at this

/--
If $\mathcal{A}$ is outcome-stable, hereditary, integer-invertible monoid, and
$G \in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{L}$
and $G^R$ is a Right option of $G$, then $\operatorname{r}(G^R) \ge
\operatorname{n}(G)$.
-/
theorem RTippingPoint_ge_NTippingPoint_of_mem_moves_right
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g gr : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L)
    (hgr : gr ∈ moves .right g) :
    NTippingPoint hsg ≤ RTippingPoint (Short.of_mem_moves hsg hgr) := by
  have h_RTippingPoint : ∀ r < NTippingPoint hsg, MisereOutcome (gr + (r : GameForm)) ≠ .R := by
    intros r hr_lt
    have h_not_winsGoingFirst : ¬WinsGoingFirst .right (g + (r : GameForm)) := by
      have h_not_winsGoingFirst := misereOutcome_add_nat_L_of_lt_NTippingPoint hAg hsg hL hr_lt
      rw [misereOutcome_L_iff_winsGoingFirst] at h_not_winsGoingFirst
      exact h_not_winsGoingFirst.right
    have h_winsGoingFirst : WinsGoingFirst .left (gr + (r : GameForm)) :=
      (not_winsGoingFirst_iff.mp h_not_winsGoingFirst).right
        (gr + ↑r) (add_right_mem_moves_add hgr r)
    intro h
    rw [misereOutcome_R_iff_winsGoingFirst] at h
    exact h.right h_winsGoingFirst
  contrapose! h_RTippingPoint
  exact ⟨_, h_RTippingPoint, RTippingPoint_iff _ _ |>.mp rfl |>.left⟩

/--
If $\mathcal{A}$ is outcome-stable, hereditary, integer-invertible monoid, and
$G \in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{L}$
and $G^L$ is a Left option of $G$, then $\operatorname{l}(G^L) \ge
\operatorname{n}(G)$.
-/
theorem LTippingPoint_ge_NTippingPoint_of_mem_moves_left
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g gl : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hR : MisereOutcome g = .R)
    (hgl : gl ∈ moves .left g) :
    NTippingPoint hsg ≤ LTippingPoint (Short.of_mem_moves hsg hgl) := by
  obtain ⟨hAng, hsng⟩ : (PFreeSubset A) (-g) ∧ IsShort (-g) := by
    exact ⟨ ClosedUnderNeg.neg_of hAg, Short.neg hsg ⟩
  have h_neg_gl : -gl ∈ moves .right (-g) := by
    convert moves_neg .right g ▸ Set.mem_neg.mpr ?_ using 1; aesop
  have h_neg_g : MisereOutcome (-g) = .L := by
    rw [ ← misereOutcome_conjugate_neg ]; aesop
  convert RTippingPoint_ge_NTippingPoint_of_mem_moves_right hAng hsng h_neg_g h_neg_gl using 1
  · exact (NTippingPoint.neg hsg).symm
  · exact (RTippingPoint_neg (Short.of_mem_moves hsg hgl)).symm

/--
If $\mathcal{A}$ is outcome-stable, hereditary, integer-invertible monoid, and
$G \in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{L}$
then there exists a Right option $G^R$ of $G$ with $\operatorname{r}(G^R) =
\operatorname{n}(G)$.
-/
theorem exists_mem_moves_right_RTippingPoint_eq_NTippingPoint
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L) :
      ∃ gr, ∃ (hgr : gr ∈ moves .right g),
      RTippingPoint (Short.of_mem_moves hsg hgr) = NTippingPoint hsg := by
  obtain ⟨gr, h_gr_mem, h_gr⟩ : ∃ gr ∈ moves .right g,
    ¬WinsGoingFirst .left (gr + (NTippingPoint hsg : GameForm)) := by
    have h_right_move : WinsGoingFirst .right (g + (NTippingPoint hsg : GameForm)) := by
      have := misereOutcome_add_NTippingPoint_N_of_misereOutcome_L hAg hsg hL
      simp only [misereOutcome_N_iff_winsGoingFirst] at this
      exact this.right
    rw [winsGoingFirst_iff] at h_right_move
    apply Or.elim h_right_move
    · intro h
      simp only [IsEndLike.add_iff, isEndLike_iff_isEnd, natCast_isEndLike_iff,
                 natCast_isEnd_right, and_true] at h
      simp only [misereOutcome_L_iff_winsGoingFirst, winsGoingFirst_of_isEnd h,
                 not_true_eq_false, and_false] at hL
    · simp only [moves_add, rightMoves_natCast, Set.image_empty, Set.union_empty, Set.mem_image,
                 Player.neg_right, exists_exists_and_eq_and, imp_self]
  have h_outcome_R : MisereOutcome (gr + (NTippingPoint hsg : GameForm)) = .R := by
    cases h : MisereOutcome (gr + ↑(NTippingPoint hsg))
    · absurd h
      simp [misereOutcome_L_iff_winsGoingFirst, h_gr]
    · absurd h
      simp [misereOutcome_N_iff_winsGoingFirst, h_gr]
    · absurd h
      have h_gr_mem := Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inr h_gr_mem))
      exact PFree.misereOutcome_ne_P_of_pfree (isPFree_add_natCast (PFree.pfree h_gr_mem) _)
    · rfl
  have h_r_le_n : RTippingPoint (Short.of_mem_moves hsg h_gr_mem) ≤ NTippingPoint hsg := by
    exact ((RTippingPoint_iff (Short.of_mem_moves hsg h_gr_mem) _).mp rfl).2 _ h_outcome_R
  use gr, h_gr_mem
  exact le_antisymm h_r_le_n (RTippingPoint_ge_NTippingPoint_of_mem_moves_right hAg hsg hL h_gr_mem)

/--
If $\mathcal{A}$ is outcome-stable, hereditary, integer-invertible monoid, and
$G \in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) = \mathscr{R}$
then there exists a Left option $G^L$ of $G$ with $\operatorname{l}(G^L) =
\operatorname{n}(G)$.
-/
theorem exists_mem_moves_left_LTippingPoint_eq_NTippingPoint
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hR : MisereOutcome g = .R) :
    ∃ gl, ∃ (hgl : gl ∈ moves .left g),
      LTippingPoint (Short.of_mem_moves hsg hgl) = NTippingPoint hsg := by
  have :=
      exists_mem_moves_right_RTippingPoint_eq_NTippingPoint
        (ClosedUnderNeg.neg_of hAg) (Short.neg hsg) ?_
  · obtain ⟨ gr, hgr, h ⟩ := this
    -- By definition of `moves`, we know that `gr ∈ (-g)ᴿ` implies there exists
    -- `gl ∈ gᴸ` such that `gr = -gl`.
    obtain ⟨gl, hgl, rfl⟩ : ∃ gl ∈ gᴸ, gr = -gl := by
      have hMovesNeg : moves .right (-g) = Set.neg.neg (moves .left g) := by
        simpa only [Player.neg_right] using moves_neg .right g
      rw [hMovesNeg, Set.mem_neg] at hgr
      exact ⟨-gr, hgr, by simp⟩
    grind only [NTippingPoint.neg, RTippingPoint_neg, LTippingPoint_neg]
  · exact misereOutcome_neg_L_iff_misereOutcome.mpr hR

theorem misereOutcome_add_nat_N_of_misereOutcome_L
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L)
    {m : ℕ} (hm1 : NTippingPoint hsg ≤ m) (hm2 : m < RTippingPoint hsg) :
    MisereOutcome (g + (m : GameForm)) = .N := by
  cases h : MisereOutcome (g + (m : GameForm))
  · have h_outcome_N' : MisereOutcome (g + (NTippingPoint hsg : GameForm)) = .N := by
      exact misereOutcome_add_NTippingPoint_N_of_misereOutcome_L hAg hsg hL
    have h_outcome_N : MisereOutcome (g + (m : GameForm)) ≤ MisereOutcome (g + (NTippingPoint hsg :
        GameForm)) := by
      have hle : (NTippingPoint hsg : ℤ) ≤ m := by exact_mod_cast hm1
      have hmono := misereOutcome_add_int_antitone hAg hle
      simpa only [Form.intCast_nat] using hmono
    rw [h_outcome_N', h] at h_outcome_N
    absurd h_outcome_N
    decide
  · rfl
  · absurd h
    have hP := misereOutcome_add_int_ne_P hAg (m : ℤ)
    simpa only [Form.intCast_nat] using hP
  · absurd h
    exact misereOutcome_add_nat_ne_R_of_lt_RTippingPoint hsg hm2

/--
If $\mathcal{A}$ is outcome-stable, hereditary monoid containing $1$ and $-1$,
and $G \in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) =
\mathscr{L}$, then if $\operatorname{n}(G) \ne \operatorname{r}(G) - 1$ then
there exists some option $G^L$ with $\operatorname{o}(G^L) = \mathscr{L}$ such
that $\operatorname{n}(G^L) = \operatorname{r}(G)$.

This is (1) in [Davies, Miller, Milley (Lemma 3.11 on p.
14)][davies:SumsPFreeForms:2025].
-/
theorem exists_mem_moves_left_L_NTippingPoint_eq_RTippingPoint
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hL : MisereOutcome g = .L)
    (hne : NTippingPoint hsg ≠ RTippingPoint hsg - 1) :
    ∃ gl, ∃ (hgl : gl ∈ moves .left g), MisereOutcome gl = .L ∧
      NTippingPoint (Short.of_mem_moves hsg hgl) = RTippingPoint hsg := by
  obtain ⟨w, hw⟩ :
      ∃ w : GameForm,
        w ∈ moves .left (g + ((RTippingPoint hsg - 1 : ℕ))) ∧ ¬WinsGoingFirst .right w := by
    have hwL : MisereOutcome (g + ((RTippingPoint hsg - 1 : ℕ))) = .N := by
      apply misereOutcome_add_nat_N_of_misereOutcome_L hAg hsg hL
      · exact Nat.le_sub_one_of_lt (NTippingPoint_lt_RTippingPoint_of_misereOutcome_L hAg hsg hL)
      · have := NTippingPoint_lt_RTippingPoint_of_misereOutcome_L hAg hsg hL
        omega
    have hwL' : WinsGoingFirst .left (g + ((RTippingPoint hsg - 1 : ℕ) : GameForm)) := by
      convert misereOutcome_N_iff_winsGoingFirst.mp hwL using 1
      simp only [misereOutcome_N_iff_winsGoingFirst] at hwL
      exact iff_of_true hwL.left hwL
    have := winsGoingFirst_iff (g + (RTippingPoint hsg - 1 : ℕ)) .left
    contrapose! this
    aesop
  have h_cases :
      (∃ gl ∈ moves .left g, w = gl + ((RTippingPoint hsg - 1 : ℕ) : GameForm))
      ∨ w = g + ((RTippingPoint hsg - 2 : ℕ) : GameForm) := by
    rcases n : RTippingPoint hsg with ( _ | _ | n )
    · simp only [n, zero_le, Nat.sub_eq_zero_of_le, Nat.cast_zero, add_zero] at hw
      simp only [zero_le, Nat.sub_eq_zero_of_le, Nat.cast_zero, add_zero, exists_eq_right', hw,
                 true_or]
    · simp only [n, zero_add, tsub_self, Nat.cast_zero, add_zero] at hw
      simp only [hw, zero_add, tsub_self, Nat.cast_zero, add_zero, exists_eq_right',
                 Nat.one_le_ofNat, Nat.sub_eq_zero_of_le, true_or]
    · simp [n] at hw hne ⊢
      grind only
  obtain ⟨gl, hgl⟩ :
      ∃ gl : GameForm, gl ∈ moves .left g
        ∧ ¬WinsGoingFirst .right (gl + ((RTippingPoint hsg - 1 : ℕ) : GameForm)) := by
    rcases h_cases with (⟨gl, hgl, rfl⟩ | rfl)
    · exact ⟨gl, hgl, hw.right⟩
    · have h_contra : MisereOutcome (g + ((RTippingPoint hsg - 2 : ℕ) : GameForm)) = .N := by
        apply misereOutcome_add_nat_N_of_misereOutcome_L hAg hsg hL
        · have hN : NTippingPoint hsg < RTippingPoint hsg - 1 :=
            lt_of_le_of_ne
              (Nat.le_sub_one_of_lt (NTippingPoint_lt_RTippingPoint_of_misereOutcome_L hAg hsg hL))
              hne
          exact Nat.le_sub_one_of_lt hN
        · have := NTippingPoint_lt_RTippingPoint_of_misereOutcome_L hAg hsg hL
          have := one_le_NTippingPoint_of_misereOutcome_L hsg hL
          omega
      exact False.elim <| hw.2 <| by rw [ misereOutcome_N_iff_winsGoingFirst ] at h_contra; tauto
  have hglL : MisereOutcome (gl + ((RTippingPoint hsg - 1 : ℕ) : GameForm)) = .L := by
    cases h : MisereOutcome (gl + ↑(RTippingPoint hsg - 1))
    · rfl
    · absurd h
      simp [misereOutcome_N_iff_winsGoingFirst, hgl]
    · absurd h
      have hglPFree : IsPFree (gl + ↑(RTippingPoint hsg - 1)) := by
        have hgl_mem := Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl.left))
        exact isPFree_add_natCast (PFree.pfree hgl_mem) _
      exact PFree.misereOutcome_ne_P_of_pfree (A := IsPFree) hglPFree
    · absurd h
      simp [misereOutcome_R_iff_winsGoingFirst, hgl]
  have hglL' : MisereOutcome gl = .L := by
    by_cases hglR : MisereOutcome gl = .R
    · have hglR' : MisereOutcome (gl + ((RTippingPoint hsg - 1 : ℕ) : GameForm)) = .R :=
        PFree.misereOutcome_add_natCast_R_of_misereOutcome_R _
          (Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl.left))) hglR
      absurd hglR'.symm.trans hglL
      decide
    · by_cases hglN : MisereOutcome gl = .N
      · have hA := (Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl.left)))
        have h_rtip : (0 : ℤ) ≤ (RTippingPoint hsg - 1 : ℕ) := Int.natCast_nonneg _
        have := misereOutcome_add_int_antitone hA h_rtip
        simp +decide only [hglN, hglL,
                           Form.intCast_nat, Form.intCast_ofNat, Nat.cast_zero, add_zero] at this
      · have hA := (Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl.left)))
        have := misereOutcome_add_int_ne_P hA 0
        simp only [Form.intCast_ofNat, Nat.cast_zero, add_zero, ne_eq] at this
        cases h : MisereOutcome gl <;> tauto
  refine ⟨gl, hgl.1, hglL', le_antisymm ?_ ?_⟩
  · apply NTippingPoint_le_RTippingPoint_of_mem_moves_left hAg hsg hgl.left
    simp only [hglL', ne_eq, reduceCtorEq, not_false_eq_true]
  · apply le_of_not_gt
    intro h
    have hA := Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl.left))
    have h_ntip : (NTippingPoint (Short.of_mem_moves hsg hgl.left) :
        ℤ) ≤ RTippingPoint hsg - 1 := by
      omega
    have h_antitone := misereOutcome_add_int_antitone hA h_ntip
    simp_all only [ne_eq, moves_add, Set.mem_union, Set.mem_image, Form.intCast_nat]
    have hA := Hereditary.has_option hAg (isOption_iff_mem_union.mpr (Or.inl hgl.left))
    have h_short := Short.of_mem_moves hsg hgl.left
    have h_ntip_outcome :=
      misereOutcome_add_NTippingPoint_N_of_misereOutcome_L hA h_short hglL'
    match h : RTippingPoint hsg with
    | 0 => omega
    | n + 1 =>
      have h_antitone_n :
          MisereOutcome (gl + ↑n) ≤ MisereOutcome (gl + ↑(NTippingPoint h_short)) := by
        simpa [h] using h_antitone
      have h_le_N : MisereOutcome (gl + ↑n) ≤ Outcome.N := by
        rw [h_ntip_outcome] at h_antitone_n
        exact h_antitone_n
      have hglL_n : MisereOutcome (gl + ↑n) = Outcome.L := by
        simpa [h] using hglL
      rw [hglL_n] at h_le_N
      absurd h_le_N
      decide

/--
If $\mathcal{A}$ is outcome-stable, hereditary monoid containing $1$ and $-1$,
and $G \in \operatorname{pf}(\mathcal{A})$ with $\operatorname{o}(G) =
\mathscr{R}$, then if $\operatorname{n}(G) \ne \operatorname{l}(G) - 1$ then
there exists some option $G^R$ with $\operatorname{o}(G^R) = \mathscr{R}$ such
that $\operatorname{n}(G^R) = \operatorname{l}(G)$.

This is mirror of (1) in [Davies, Miller, Milley (Lemma 3.11 on p.
14)][davies:SumsPFreeForms:2025].
-/
theorem exists_mem_moves_right_R_NTippingPoint_eq_LTippingPoint
    [OutcomeStable A] [ClosedUnderAddNat A] [HasInt A] [ClosedUnderNeg A] [Hereditary A]
    {g : GameForm} (hAg : (PFreeSubset A) g) (hsg : IsShort g) (hR : MisereOutcome g = .R)
    (hne : NTippingPoint hsg ≠ LTippingPoint hsg - 1) :
    ∃ gr, ∃ (hgr : gr ∈ moves .right g), MisereOutcome gr = .R ∧
      NTippingPoint (Short.of_mem_moves hsg hgr) = LTippingPoint hsg := by
  -- Apply the L-side lemma to -g.
  have :=
      exists_mem_moves_left_L_NTippingPoint_eq_RTippingPoint
        (ClosedUnderNeg.neg_of hAg) (Short.neg hsg) (by
  rw [ ← misereOutcome_conjugate_neg ]; aesop) (by
  grind only [NTippingPoint.neg, RTippingPoint_neg, LTippingPoint_neg])
  obtain ⟨ gl, hgl₁, hgl₂, hgl₃ ⟩ := this
  -- By definition of `moves_neg`, we have `gl ∈ (-g)ᴸ` if and only if `-gl ∈
  -- gᴿ`.
  have hgr : ∃ gr ∈ gᴿ, gl = -gr := by
    exact ⟨ -gl, by simpa using hgl₁, by simp +decide ⟩
  obtain ⟨ gr, hgr₁, rfl ⟩ := hgr
  use gr
  simp_all +decide only [exists_and_left, misereOutcome_neg_L_iff_misereOutcome]
  refine ⟨trivial, ?_⟩
  refine ⟨trivial, ?_⟩
  convert hgl₃ using 1
  · exact (NTippingPoint.neg _).symm
  · exact (RTippingPoint_neg hsg).symm

theorem misereOutcome_ne_R_of_mem_moves_right_of_L
    [OutcomeStable A] [ClosedUnderAddNat A] [ClosedUnderNeg A] [HasInt A] [Hereditary A]
    {g gr : GameForm} (hAg : (PFreeSubset A) g)
    (hpfg : IsPFree g) (hsg : IsShort g) (hLg : MisereOutcome g = .L)
    (hgr : gr ∈ moves .right g) : MisereOutcome gr ≠ .R := by
  have h1 : NTippingPoint hsg ≤ RTippingPoint (Short.of_mem_moves hsg hgr) :=
    RTippingPoint_ge_NTippingPoint_of_mem_moves_right
      (A := PFreeSubset A) (.mk hAg hpfg) hsg hLg hgr
  have h2 : 1 ≤ NTippingPoint hsg := one_le_NTippingPoint_of_misereOutcome_L hsg hLg
  have h3 : (0 : ℕ) < RTippingPoint (Short.of_mem_moves hsg hgr) := by omega
  have h4 := misereOutcome_add_nat_ne_R_of_lt_RTippingPoint (Short.of_mem_moves hsg hgr) h3
  simpa using h4

theorem misereOutcome_right_option_of_L_cases
    [OutcomeStable A] [ClosedUnderAddNat A] [ClosedUnderNeg A] [HasInt A] [Hereditary A]
    {g gr : GameForm} (hAg : (PFreeSubset A g))
    (hsg : IsShort g) (hLg : MisereOutcome g = .L) (hgr : gr ∈ moves .right g) :
    MisereOutcome gr = .L ∨ MisereOutcome gr = .N := by
  rcases h : MisereOutcome gr with _ | _ | _ | _
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd h (PFree.misereOutcome_ne_P_of_pfree (isPFree_of_mem_moves hAg.isPFree hgr))
  · exact absurd h (misereOutcome_ne_R_of_mem_moves_right_of_L hAg hAg.isPFree hsg hLg hgr)

theorem NTippingPoint_lt_LTippingPoint_of_misereOutcome_R
    [OutcomeStable A] [ClosedUnderAddNat A] [ClosedUnderNeg A] [HasInt A] [Hereditary A]
    {g : GameForm} (hAg : (PFreeSubset A) g)
    (hsg : IsShort g) (hRg : MisereOutcome g = .R) :
    NTippingPoint hsg < LTippingPoint hsg := by
  have := NTippingPoint_lt_RTippingPoint_of_misereOutcome_L
    (ClosedUnderNeg.neg_of hAg) (Short.neg hsg)
    (by rw [misereOutcome_neg_L_iff_misereOutcome]; exact hRg)
  rwa [NTippingPoint.neg hsg, RTippingPoint_neg hsg] at this

end OutcomeStable

end

end MisereGames
