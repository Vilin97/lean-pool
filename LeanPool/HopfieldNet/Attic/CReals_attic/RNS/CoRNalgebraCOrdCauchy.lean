/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Algebra.Order.Group.Abs
import LeanPool.HopfieldNet.CReals.RNS.CRings
import LeanPool.HopfieldNet.CReals.RNS.CoRNalgebraCOrdAbs
-- (* Copyright © 1998-2006
--  * Henk Barendregt
--  * Luís Cruz-Filipe
--  * Herman Geuvers
--  * Mariusz Giero
--  * Rik van Ginneken
--  * Dimitri Hendriks
--  * Sébastien Hinderer
--  * Bart Kirkels
--  * Pierre Letouzey
--  * Iris Loeb
--  * Lionel Mamane
--  * Milad Niqui
--  * Russell O’Connor
--  * Randy Pollack
--  * Nickolay V. Shmyrev
--  * Bas Spitters
--  * Dan Synek
--  * Freek Wiedijk
--  * Jan Zwanenburg
--  *
--  * This work is free software; you can redistribute it and/or modify
--  * it under the terms of the GNU General Public License as published by
--  * the Free Software Foundation; either version 2 of the License, or
--  * (at your option) any later version.
--  *
--  * This work is distributed in the hope that it will be useful,
--  * but WITHOUT ANY WARRANTY; without even the implied warranty of
--  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  * GNU General Public License for more details.
--  *
--  * You should have received a copy of the GNU General Public License along
--  * with this work; if not, write to the Free Software Foundation, Inc.,
--  * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
--  *)
-- Require Export CoRN.algebra.COrdAbs.
-- From Coq Require Import Lia.

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
-- (* Begin_SpecReals *)

-- Section OrdField_Cauchy.

-- (**
-- ** Cauchy sequences
-- %\begin{convention}% Let [R] be an ordered field.
-- %\end{convention}%
-- *)
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]
-- Variable R : COrdField.

-- (* begin hide *)
-- Set Implicit Arguments.
-- Unset Strict Implicit.
-- (* end hide *)

-- Definition Cauchy_prop (g : nat -> R) : CProp := forall e : R,
--  [0] [<] e -> {N : nat | forall m, N <= m -> AbsSmall e (g m[-]g N)}.

-- In Lean4, we can define the Cauchy property for a sequence in an ordered field as follows:
def AbsSmall (ε x : K) : Prop := (abs x) < ε

def Cauchy_prop (g : ℕ → K) : Prop :=
  ∀ ε : K, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, AbsSmall ε (g m - g N)

-- (* begin hide *)
-- Set Strict Implicit.
-- Unset Implicit Arguments.
-- (* end hide *)

-- (* Def. CauchyP, Build_CauchyP *)
-- (* Should be defined in terms of CauchyP *)

-- (**
-- Implicit arguments turned off, because Coq makes a mess of it in combination
-- with the coercions
-- *)

-- Record CauchySeq : Type :=
--  {CS_seq   :> nat -> R;
--   CS_proof :  Cauchy_prop CS_seq}.

structure CauchySeq' (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  CS_seq : ℕ → K
  CS_proof : Cauchy_prop CS_seq

-- Definition SeqLimit (seq : nat -> R) (lim : R) : CProp := forall e : R,
--  [0] [<] e -> {N : nat | forall m, N <= m -> AbsSmall e (seq m[-]lim)}.

def SeqLimit (seq : ℕ → K) (lim : K) : Prop :=
  ∀ ε : K, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, AbsSmall ε (seq m - lim)

-- (* End_SpecReals *)

-- (**
-- We now prove that the property of being a Cauchy sequence is preserved
-- through the usual algebraic operations (addition, subtraction and
-- multiplication -- and division, provided some additional conditions
-- hold).

-- %\begin{convention}% Let [R] be an ordered field.
-- %\end{convention}%
-- *)
/--
If `g` is a Cauchy sequence, then there exists a bound `K > 0`
 and an index `N` such that for all `m ≥ N`, `|g m| < K`.
-/
lemma CS_seq_bounded :
  ∀ (g : ℕ → K) (hg : Cauchy_prop g),
  ∃ K : K, 0 < K ∧ ∃ N : ℕ, ∀ m ≥ N, abs (g m) < K :=  by {
  intros g Hg
  unfold Cauchy_prop at *
  specialize Hg 1 (by {simp only [zero_lt_one]})
  obtain ⟨N, hN⟩ := Hg
  use (abs (g N) + 1)
  constructor
  · apply add_pos_of_nonneg_of_pos
    · exact abs_nonneg (g N)
    · exact zero_lt_one
  · use N
    intros m hm
    calc
      abs (g m) = abs ((g m - g N) + g N)         := by {simp only [sub_add_cancel]}
              _ ≤ abs (g m - g N) + abs (g N)   := abs_add _ _
              _  < 1 + abs (g N)                 := add_lt_add_right (hN m hm) _
              _ = abs (g N) + 1                 := add_comm _ _
  }

-- Theorem CS_seq_bounded : forall g : nat -> R, Cauchy_prop g ->
--  {K : R | [0] [<] K | {N : nat | forall m, N <= m -> AbsSmall K (g m)}}.
-- Proof.
--  intros g Hg.
--  unfold Cauchy_prop in |- *.
--  elim (Hg _ (pos_one _)).
--  intros N H1.
--  exists (g N[^]2[-]g N[+]Two).
--   apply less_leEq_trans with (nring (R:=R) 7 [/]FourNZ).
--    apply pos_div_four; apply nring_pos; auto with arith.
--   astepl ([0][+]nring (R:=R) 7 [/]FourNZ).
--   apply shift_plus_leEq.
--   rstepr ((g N[-][1] [/]TwoNZ)[^]2).
--   apply sqr_nonneg.
--  exists N.
--  intros m Hm.
--  elim (H1 m Hm); intros.
--  split.
--   apply plus_cancel_leEq_rht with (z := [--](g N)).
--   rstepr (g m[-]g N).
--   rstepl ([--](g N[^]2[+]Two)).
--   apply leEq_transitive with ([--]([1]:R)).
--    apply inv_cancel_leEq.
--    rstepl ([1]:R).
--    rstepr (g N[^]2[+]Two).
--    apply plus_cancel_leEq_rht with ([--][1]:R).
--    rstepl ([0]:R).
--    rstepr (g N[^]2[+][1]).
--    apply leEq_transitive with (y := g N[^]2).
--     apply sqr_nonneg.
--    apply less_leEq; apply less_plusOne.
--   assumption.
--  apply plus_cancel_leEq_rht with (g N[-]Two).
--  rstepr (g N[^]2).
--  astepr (g N[*]g N).
--  apply plus_cancel_leEq_rht with ([--](Two[*]g N)[+]Two).
--  rstepl (g m[-]g N).
--  rstepr (g N[*]g N[+][1][-]Two[*]g N[+][1]).
--  apply leEq_transitive with (y := [1]:R).
--   assumption.
--  rstepl ([0][+]([1]:R)).
--  apply plus_resp_leEq with (z := [1]:R).
--  rstepr ((g N[-][1])[*](g N[-][1])).
--  apply leEq_wdr with (y := (g N[-][1])[^]2).
--   apply sqr_nonneg.
--  algebra.
-- Qed.

-- The constant sequence is Cauchy
lemma CS_seq_const (c : K) : Cauchy_prop (fun n => c) :=
  fun ε hε => ⟨0, fun m hm => by
    simp [AbsSmall]
    exact hε⟩

-- (**
-- %\begin{convention}% Assume [f] and [g] are Cauchy sequences on [R].
-- %\end{convention}%
-- *)

variable (f g : ℕ → K)

variable (Hf : Cauchy_prop f)

variable (Hg : Cauchy_prop g)

-- Variables f g : nat -> R.

-- Hypothesis Hf : Cauchy_prop f.
-- Hypothesis Hg : Cauchy_prop g.
include Hf Hg in
/--
If `f` and `g` are Cauchy sequences, then so is their sum.
-/
lemma CS_seq_plus : Cauchy_prop (fun m => f m + g m) :=
  fun ε hε => by
    -- We want to find N such that for all m ≥ N, |(f m + g m) - (f N + g N)| < ε
    -- Note: |(f m + g m) - (f N + g N)| = |(f m - f N) + (g m - g N)| ≤ |f m - f N| + |g m - g N|
    -- So, pick ε/2 for each.
    have hε2 : (0 : K) < ε / 2 := by
      apply (div_pos hε zero_lt_two)
    obtain ⟨Nf, Hf'⟩ := Hf (ε / 2) hε2
    obtain ⟨Ng, Hg'⟩ := Hg (ε / 2) hε2
    let N := max Nf Ng
    use N
    intro m hm
    have hmf : m ≥ Nf := le_trans (le_max_left Nf Ng) hm
    have hmg : m ≥ Ng := le_trans (le_max_right Nf Ng) hm
    calc
      abs ((f m + g m) - (f N + g N))
        = abs ((f m - f N) + (g m - g N)) := by { sorry
        }
      _ ≤ abs (f m - f N) + abs (g m - g N) := abs_add _ _
      _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · sorry--exact Hf' m hmf
        · sorry --exact Hg' m hmg
      _ = ε := by sorry

-- Lemma CS_seq_plus : Cauchy_prop (fun m => f m[+]g m).
-- Proof.
--  unfold Cauchy_prop in |- *.
--  intros.
--  set (e_div_4 := e [/]FourNZ) in *.
--  cut ([0] [<] e_div_4); [ intro Heps | unfold e_div_4 in |- *; apply pos_div_four; auto ].
--  unfold Cauchy_prop in Hf.
--  unfold Cauchy_prop in Hg.
--  elim (Hf e_div_4 Heps); intros N1 H21.
--  elim (Hg e_div_4 Heps); intros N2 H31.
--  exists (Nat.max N1 N2).
--  intros.
--  rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
--  rstepr (f m[-]f (Nat.max N1 N2)[+](g m[-]g (Nat.max N1 N2))).
--  apply AbsSmall_plus.
--   rstepr (f m[-]f N1[+](f N1[-]f (Nat.max N1 N2))).
--   rstepl (e [/]FourNZ[+]e [/]FourNZ).
--   apply AbsSmall_plus.
--    apply H21; eauto with arith.
--   apply AbsSmall_minus.
--   apply H21; eauto with arith.
--  rstepr (g m[-]g N2[+](g N2[-]g (Nat.max N1 N2))).
--  rstepl (e [/]FourNZ[+]e [/]FourNZ).
--  apply AbsSmall_plus.
--   apply H31; eauto with arith.
--  apply AbsSmall_minus.
--  apply H31; eauto with arith.
-- Qed.

/--
If `f` and `g` are Cauchy sequences, then so is their sum.
-/
lemma CS_seq_plus' (f g : ℕ → K) (Hf : Cauchy_prop f) (Hg : Cauchy_prop g) :
  Cauchy_prop (fun m => f m + g m) :=
fun ε hε => by
  -- We'll use ε/2 for each sequence
  have hε2 : (0 : K) < ε / 2 := div_pos hε zero_lt_two
  obtain ⟨N1, Hf'⟩ := Hf (ε / 2) hε2
  obtain ⟨N2, Hg'⟩ := Hg (ε / 2) hε2
  let N := max N1 N2
  use N
  intro m hm
  have hmf : m ≥ N1 := le_trans (le_max_left N1 N2) hm
  have hmg : m ≥ N2 := le_trans (le_max_right N1 N2) hm
  calc
    abs ((f m + g m) - (f N + g N))
      = abs ((f m - f N) + (g m - g N)) := by sorry
    _ ≤ abs (f m - f N) + abs (g m - g N) := abs_add _ _
    _ < ε / 2 + ε / 2 := sorry--add_lt_add (Hf' m hmf) (Hg' m hmg)
    _ = ε := sorry--add_halves ε

-- Lemma CS_seq_inv : Cauchy_prop (fun n => [--] (f n)).
-- Proof.
--  red in |- *; intros e H.
--  elim (Hf e H); intros N Hn.
--  exists N; intros m Hm.
--  apply AbsSmall_minus.
--  rstepr (f m[-]f N).
--  auto.
-- Qed.


/--
If `f` is a Cauchy sequence, then so is its negation.
-/
lemma CS_seq_inv (f : ℕ → K) (Hf : Cauchy_prop f) : Cauchy_prop (fun n => -f n) := by
  intros ε hε
  dsimp [Cauchy_prop] at Hf
  obtain ⟨N, hN⟩ := Hf ε hε
  exact
  ⟨N, fun m hm => by
    simp [AbsSmall, sub_neg_eq_add]
    sorry
    --exact hN m hm
    ⟩

-- Lemma CS_seq_mult : Cauchy_prop (fun n => f n[*]g n).
-- Proof.
--  red in |- *; intros e He.
--  elim (CS_seq_bounded f Hf); intros Mf HMf H.
--  elim (CS_seq_bounded g Hg); intros Mg HMg H'.
--  elim H; clear H; intros Nf HNf.
--  elim H'; clear H'; intros Ng HNg.
--  set (Mf_ap_zero := pos_ap_zero _ _ HMf) in *.
--  set (Mg_ap_zero := pos_ap_zero _ _ HMg) in *.
--  set (ef := e[/] _[//]mult_resp_ap_zero _ _ _ (twelve_ap_zero _) Mf_ap_zero) in *.
--  set (eg := e[/] _[//]mult_resp_ap_zero _ _ _ (twelve_ap_zero _) Mg_ap_zero) in *.
--  cut ([0] [<] ef); [ intro Hef
--    | unfold ef in |- *; apply div_resp_pos; try apply mult_resp_pos; auto; apply pos_twelve ].
--  cut ([0] [<] eg); [ intro Heg
--    | unfold eg in |- *; apply div_resp_pos; try apply mult_resp_pos; auto; apply pos_twelve ].
--  elim (Hf eg Heg); intros Pf HPf.
--  elim (Hg ef Hef); intros Pg HPg.
--  set (N := Nat.max (Nat.max Nf Pf) (Nat.max Ng Pg)) in *; exists N; intros m Hm.
--  rstepr ((f m[-]f Pf[+][--](f N[-]f Pf))[*]g m[+] (g m[-]g Pg[+][--](g N[-]g Pg))[*]f N).
--  apply AbsSmall_wdl_unfolded with (Three[*]((eg[+]eg)[*]Mg)[+]Three[*]((ef[+]ef)[*]Mf)).
--   2: unfold eg, ef in |- *; rational.
--  apply AbsSmall_plus; apply AbsSmall_mult; try apply AbsSmall_plus; try apply inv_resp_AbsSmall.
--       apply HPf; apply Nat.le_trans with N; auto; unfold N in |- *; eauto with arith.
--      apply HPf; apply Nat.le_trans with N; auto; unfold N in |- *; eauto with arith.
--     apply HNg; auto; apply Nat.le_trans with N; auto; unfold N in |- *; eauto with arith.
--    apply HPg; apply Nat.le_trans with N; auto; unfold N in |- *; eauto with arith.
--   apply HPg; apply Nat.le_trans with N; auto; unfold N in |- *; eauto with arith.
--  apply HNf; auto; apply Nat.le_trans with N; auto; unfold N in |- *; eauto with arith.
-- Qed.



/--
If `f` and `g` are Cauchy sequences, then so is their product.
-/
lemma CS_seq_mult (f g : ℕ → K) (Hf : Cauchy_prop f) (Hg : Cauchy_prop g) :
  Cauchy_prop (fun n => f n * g n) := sorry
-- fun ε hε => by
--   -- Get bounds for f and g
--   obtain ⟨Mf, Mf_pos, ⟨Nf, HNf⟩⟩ := CS_seq_bounded f Hf
--   obtain ⟨Mg, Mg_pos, ⟨Ng, HNg⟩⟩ := CS_seq_bounded g Hg
--   -- Use ε/(2 * (Mf + 1)) and ε/(2 * (Mg + 1)) for Cauchy property
--   let δf := ε / (2 * (Mg + 1))
--   let δg := ε / (2 * (Mf + 1))
--   have δf_pos : 0 < δf := div_pos hε (mul_pos two_pos (add_pos_of_nonneg_of_pos (le_of_lt Mg_pos) zero_lt_one))
--   have δg_pos : 0 < δg := div_pos hε (mul_pos two_pos (add_pos_of_nonneg_of_pos (le_of_lt Mf_pos) zero_lt_one))
--   obtain ⟨N1, Hf'⟩ := Hf δf δf_pos
--   obtain ⟨N2, Hg'⟩ := Hg δg δg_pos
--   let N := max (max Nf N1) (max Ng N2)
--   use N
--   intro m hm
--   -- m ≥ Nf, N1, Ng, N2
--   have mNf : m ≥ Nf := sorry --le_trans (le_max_left Nf N1) (le_max_left (max Nf N1) (max Ng N2)) |> le_trans hm
--   have mN1 : m ≥ N1 := sorry--le_trans (le_max_right Nf N1) (le_max_left (max Nf N1) (max Ng N2)) |> le_trans hm
--   have mNg : m ≥ Ng := sorry --le_trans (le_max_left Ng N2) (le_max_right (max Nf N1) (max Ng N2)) |> le_trans hm
--   have mN2 : m ≥ N2 := sorry--le_trans (le_max_right Ng N2) (le_max_right (max Nf N1) (max Ng N2)) |> le_trans hm
--   -- Now estimate |f m * g m - f N * g N|
--   calc
--     abs (f m * g m - f N * g N)
--       = abs ((f m - f N) * g m + f N * (g m - g N)) := by sorry--ring_nf
--     _ ≤ abs ((f m - f N) * g m) + abs (f N * (g m - g N)) := abs_add _ _
--     _ ≤ abs (f m - f N) * abs (g m) + abs (f N) * abs (g m - g N) := add_le_add (abs_mul _ _) (abs_mul _ _)
--     _ < δf * Mg + Mf * δg := by
--       apply add_lt_add
--       · apply mul_lt_mul_of_pos_right (Hf' m mN1) Mg_pos
--       · apply mul_lt_mul_of_pos_left (Hg' m mN2) (abs_nonneg (f N))
--     _ ≤ ε / 2 + ε / 2 := by
--       rw [←div_add_div_same, add_halves]
--       -- δf * Mg = ε / (2 * (Mg + 1)) * Mg ≤ ε / 2 (since Mg < Mg + 1)
--       -- Mf * δg = Mf * (ε / (2 * (Mf + 1))) ≤ ε / 2
--       apply add_le_add
--       · apply (mul_le_of_le_one_right (div_nonneg hε.le (mul_nonneg zero_le_two (add_nonneg (abs_nonneg (g N)) zero_le_one))) sorry--(by linarith [Mg_pos])
--         )
--       · apply (mul_le_of_le_one_left (abs_nonneg (f N)) (div_le_one_of_le (mul_nonneg zero_le_two (add_nonneg (abs_nonneg (f N)) zero_le_one))
--           sorry--(by linarith [Mf_pos])
--           )
--           )
--     _ = ε := add_halves ε




-- (**
-- We now assume that [f] is, from some point onwards, greater than
-- some positive number.  The sequence of reciprocals is defined as
-- being constantly one up to that point, and the sequence of
-- reciprocals from then onwards.

-- %\begin{convention}%
-- Let [e] be a postive element of [R] and let [N:nat] be such that from
-- [N] onwards, [(f n) [#] [0]]
-- %\end{convention}%
-- *)

-- %\begin{convention}%
-- Let [e] be a postive element of [R] and let [N:nat] be such that from
-- [N] onwards, [(f n) [#] [0]]
-- %\end{convention}%
-- *)

-- Variable e : R.
-- Hypothesis He : [0] [<] e.

-- Variable N : nat.
-- Hypothesis f_bnd : forall n : nat, N <= n -> e [<=] f n.


/-
We now assume that `f` is, from some point onwards, greater than some positive number.
The sequence of reciprocals is defined as being constantly one up to that point, and the sequence of reciprocals from then onwards.

Let `e` be a positive element of `K` and let `N : ℕ` be such that from `N` onwards, `e ≤ f n`.
--/
variable {f : ℕ → K}
variable (e : K) (he : 0 < e)
variable (N : ℕ)
variable (f_bnd : ∀ n : ℕ, N ≤ n → e ≤ f n)

-- Lemma CS_seq_recip_def : forall n : nat, N <= n -> f n [#] [0].
-- Proof.
--  intros.
--  apply pos_ap_zero.
--  apply less_leEq_trans with e; auto with arith.
-- Qed.

include f_bnd he
/--
If `e ≤ f n` for `n ≥ N` and `0 < e`, then for all `n ≥ N`, `f n ≠ 0`.
-/
lemma CS_seq_recip_def (n : ℕ) (hn : N ≤ n) : f n ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le he (f_bnd n hn))


-- Definition CS_seq_recip_seq (n : nat) : R.
-- Proof.
--  elim (lt_le_dec n N); intro Hdec.
--   apply ([1]:R).
--  apply ([1][/] _[//]CS_seq_recip_def n Hdec).
-- Defined.


/--
The sequence of reciprocals: for `n < N`, return `1`, for `n ≥ N`, return `1 / f n`.
Requires `f n ≠ 0` for `n ≥ N`, which is ensured by `f_bnd` and `he`.
-/
def CS_seq_recip_seq (n : ℕ) : K :=
  if n < N then 1 else 1 / (f n)


-- Lemma CS_seq_recip : Cauchy_prop CS_seq_recip_seq.
-- Proof.
--  red in |- *; intros d Hd.
--  elim (Hf ((d[*]e[*]e) [/]TwoNZ));
--    [ intros K HK | apply pos_div_two; repeat apply mult_resp_pos; auto ].
--  exists (Nat.max K N); intros n Hn.
--  apply AbsSmall_cancel_mult with (f (Nat.max K N)).
--   apply less_leEq_trans with e; auto with arith.
--  apply AbsSmall_cancel_mult with (f n).
--   apply less_leEq_trans with e; eauto with arith.
--  unfold CS_seq_recip_seq in |- *.
--  elim lt_le_dec; intro; simpl in |- *.
--   exfalso; apply Nat.le_ngt with N n; eauto with arith.
--  elim lt_le_dec; intro; simpl in |- *.
--   exfalso; apply Nat.le_ngt with N (Nat.max K N); eauto with arith.
--  rstepr (f (Nat.max K N)[-]f n).
--  apply AbsSmall_leEq_trans with (d[*]e[*]e).
--   apply mult_resp_leEq_both.
--      apply less_leEq; apply mult_resp_pos; auto.
--     apply less_leEq; auto.
--    apply mult_resp_leEq_lft.
--     auto with arith.
--    apply less_leEq; auto.
--   auto with arith.
--  auto with arith.
--  rstepr (f (Nat.max K N)[-]f K[+](f K[-]f n)).
--  apply AbsSmall_eps_div_two.
--   auto with arith.
--  apply AbsSmall_minus; apply HK.
--  eauto with arith.
-- Qed.















/--
If `f` is a Cauchy sequence and from some index `N` onwards, `e ≤ f n` for some `e > 0`,
then the sequence of reciprocals defined by `CS_seq_recip_seq` is also Cauchy.
-/
lemma CS_seq_recip
  (f : ℕ → K) (Hf : Cauchy_prop f)
  (e : K) (he : 0 < e) (N : ℕ) (f_bnd : ∀ n : ℕ, N ≤ n → e ≤ f n) :
  Cauchy_prop (CS_seq_recip_seq (f := f) N) :=
sorry

-- End OrdField_Cauchy.

-- Arguments SeqLimit [R].


-- (**
-- The following lemma does not require the sequence to be Cauchy, but it fits
-- well here anyway.
-- *)

-- Lemma maj_upto_eps : forall (F : COrdField) (a : nat -> F) (n : nat) (eps : F),
--  0 < n -> [0] [<] eps -> {k : nat | 1 <= k /\ k <= n /\ (forall i : nat, 1 <= i -> i <= n -> a i[-]eps [<=] a k)}.
-- Proof.
--  intros F a n eps Hn Heps.
--  induction  n as [| n Hrecn].
--   elim (Nat.lt_irrefl _ Hn).
--  clear Hrecn Hn.
--  induction  n as [| n Hrecn].
--   exists 1.
--   repeat split. 1-2: reflexivity.
--   intros.
--   rewrite <- (Nat.le_antisymm _ _ H H0).
--   astepr (a 1[+][0]).
--   unfold cg_minus in |- *.
--   apply plus_resp_leEq_lft.
--   astepr ([--]([0]:F)).
--   apply less_leEq; apply inv_resp_less; auto.
--  elim Hrecn; intros k Hk.
--  cut (a (S (S n))[-]eps [<] a (S (S n))).
--   intro H.
--   elim (less_cotransitive_unfolded _ _ _ H (a k)); intro H4.
--    exists k.
--    elim Hk; intros H0 H2.
--    elim H2; clear H2; intros H1 H2.
--    repeat split.
--      assumption.
--     auto with arith.
--    intros i H3 H5.
--    elim (Cle_le_S_eq _ _ H5); intro H6.
--     auto with arith.
--    rewrite H6.
--    apply less_leEq; assumption.
--   exists (S (S n)).
--   repeat split; auto with arith.
--   intros i H0 H1.
--   elim (Cle_le_S_eq _ _ H1); intro H2.
--    apply leEq_transitive with (a k).
--     elim Hk; intros H3 H5.
--     elim H5; clear H5; intros H6 H7.
--     auto with arith.
--    apply less_leEq; assumption.
--   rewrite H2; apply less_leEq; auto.
--  rstepr (a (S (S n))[-][0]).
--  apply minus_resp_less_rht.
--  assumption.
-- Qed.

/--
Given a sequence `a : ℕ → K`, a natural number `n > 0`, and `ε > 0`,
there exists `k` with `1 ≤ k ≤ n` such that for all `i` with `1 ≤ i ≤ n`,
`a i - ε ≤ a k`.
-/
lemma maj_upto_eps
  (a : ℕ → K) (n : ℕ) (ε : K) (hn : 0 < n) (hε : 0 < ε) :
  ∃ k, 1 ≤ k ∧ k ≤ n ∧ ∀ i, 1 ≤ i → i ≤ n → a i - ε ≤ a k :=
sorry

-- Section Mult_Continuous.

-- Variable R : COrdField.
-- (**
-- ** Multiplication is continuous
-- %\begin{convention}% Let [R] be an ordered field.
-- %\end{convention}%
-- *)

/--
Multiplication is continuous in an ordered field:
For any `x y e : K` with `0 < e`, there exist `c d > 0` such that
for all `x' y'`, if `|x - x'| < c` and `|y - y'| < d`, then
`|x * y - x' * y'| < e`.
-/
lemma mult_contin (x y e : K) (he : 0 < e) :
  ∃ c > 0, ∃ d > 0, ∀ x' y', AbsSmall c (x - x') → AbsSmall d (y - y') →
    AbsSmall e (x * y - x' * y') :=
sorry


-- Lemma smaller : forall x y : R,
--  [0] [<] x -> [0] [<] y -> {z : R | [0] [<] z | z [<=] x /\ z [<=] y}.
-- Proof.
--  intros x y H H0.
--  elim (less_cotransitive_unfolded _ _ _ (half_3 _ _ H) y); intro.
--   exists (Half[*]x).
--    apply mult_resp_pos. apply pos_half. auto.
--     split; apply less_leEq. apply half_3. auto. auto.
--    cut (Half[*]y [<] y). intro. exists (Half[*]y).
--   apply mult_resp_pos. apply pos_half. auto.
--     split; apply less_leEq. apply less_transitive_unfolded with y. auto. auto.
--    auto.
--  apply half_3. auto.
-- Qed.


/--
Given `x, y > 0`, there exists `z > 0` such that `z ≤ x` and `z ≤ y`.
-/
lemma smaller (x y : K) (hx : 0 < x) (hy : 0 < y) :
  ∃ z : K, 0 < z ∧ z ≤ x ∧ z ≤ y := sorry


-- Lemma estimate_abs : forall x : R, {X : R | [0] [<] X | AbsSmall X x}.
-- Proof.
--  intros.
--  unfold AbsSmall in |- *.
--  cut (x [<] x[+][1]). intro H.
--   elim (less_cotransitive_unfolded _ x (x[+][1]) H [--]x); intro.
--    exists ([--]x[+][1]).
--     apply leEq_less_trans with ([--]x).
--      2: apply less_plusOne.
--     apply less_leEq; apply mult_cancel_less with (Two:R).
--      apply pos_two.
--     astepl ([0]:R); rstepr ([--]x[-]x).
--     apply shift_less_minus.
--     astepl x; auto.
--    split; apply less_leEq.
--     astepr ([--][--]x). apply inv_resp_less. apply less_plusOne.
--     apply less_transitive_unfolded with ([--]x). auto. apply less_plusOne.
--     exists (x[+][1]).
--    apply less_leEq_trans with (([1]:R) [/]TwoNZ).
--     apply pos_div_two; apply pos_one.
--    apply shift_leEq_plus; rstepl (([--][1]:R) [/]TwoNZ).
--    apply shift_div_leEq.
--     apply pos_two.
--    rstepr (x[+]x); apply shift_leEq_plus.
--    unfold cg_minus in |- *; apply shift_plus_leEq'.
--    rstepr (x[+][1]); apply less_leEq; auto.
--   split; apply less_leEq.
--    astepr ([--][--]x). apply inv_resp_less. auto. auto.
--    apply less_plusOne.
-- Qed.


/--
For any `x : K`, there exists `X > 0` such that `AbsSmall X x`.
-/
lemma estimate_abs (x : K) : ∃ X : K, 0 < X ∧ AbsSmall X x :=
sorry


-- Lemma mult_contin : forall x y e : R, [0] [<] e ->
--  {c : R | [0] [<] c | {d : R | [0] [<] d | forall x' y' : R,
--  AbsSmall c (x[-]x') -> AbsSmall d (y[-]y') -> AbsSmall e (x[*]y[-]x'[*]y')}}.
-- Proof.
--  intros x y e H.
--  set (e2 := e [/]TwoNZ) in *.
--  cut ([0] [<] e2). intro H0. 2: unfold e2 in |- *; apply pos_div_two; auto.
--   elim (estimate_abs x). intro X. intros H1a H1b.
--  elim (estimate_abs y). intro Y. intros H2 H3.
--  cut (Y [#] [0]). intro H4.
--   set (eY := e2[/] Y[//]H4) in *; exists eY.
--    unfold eY in |- *. apply div_resp_pos. auto. auto.
--    cut ([0] [<] X[+]eY). intro H5.
--    cut (X[+]eY [#] [0]). intro H6.
--     exists (e2[/] X[+]eY[//]H6).
--      apply div_resp_pos. auto. auto.
--       intros.
--     apply AbsSmall_wdr_unfolded with ((x[-]x')[*]y[+]x'[*](y[-]y')).
--      apply AbsSmall_eps_div_two.
--       apply AbsSmall_wdl_unfolded with ((e [/]TwoNZ[/] Y[//]H4)[*]Y).
--        apply mult_AbsSmall; auto.
--       rational.
--      apply AbsSmall_wdl_unfolded with ((X[+](e [/]TwoNZ[/] Y[//]H4))[*]
--        (e [/]TwoNZ[/] X[+](e [/]TwoNZ[/] Y[//]H4)[//]H6)).
--       apply mult_AbsSmall; auto.
--       apply AbsSmall_wdr_unfolded with (x[+](x'[-]x)).
--        apply AbsSmall_plus; auto. apply AbsSmall_minus. auto.
--        rational.
--      rational.
--     rational.
--    apply Greater_imp_ap. auto.
--    apply plus_resp_pos; auto.
--   unfold eY in |- *; apply div_resp_pos; auto.
--  apply Greater_imp_ap. auto.
-- Qed.



/--
Multiplication is continuous in an ordered field:
For any `x y e : K` with `0 < e`, there exist `c d > 0` such that
for all `x' y'`, if `|x - x'| < c` and `|y - y'| < d`, then
`|x * y - x' * y'| < e`.
-/
lemma mult_contin' (x y e : K) (he : 0 < e) :
  ∃ c > 0, ∃ d > 0, ∀ x' y', AbsSmall c (x - x') → AbsSmall d (y - y') → AbsSmall e (x * y - x' * y') :=
sorry




-- (** Addition is also continuous. *)

-- Lemma plus_contin : forall (x y e : R), [0] [<] e ->
--  {c : R | [0] [<] c | {d : R | [0] [<] d | forall x' y',
--  AbsSmall c (x[-]x') -> AbsSmall d (y[-]y') -> AbsSmall e (x[+]y[-] (x'[+]y'))}}.
-- Proof.
--  intros.
--  cut ([0] [<] e [/]TwoNZ). intro.
--   exists (e [/]TwoNZ). auto.
--    exists (e [/]TwoNZ). auto.
--    intros.
--   apply AbsSmall_wdr_unfolded with (x[-]x'[+](y[-]y')).
--    apply AbsSmall_eps_div_two; auto.
--   rational.
--  apply div_resp_pos. apply pos_two. auto.
-- Qed.

/--
Addition is continuous in an ordered field:
For any `x y e : K` with `0 < e`, there exist `c d > 0` such that
for all `x' y'`, if `|x - x'| < c` and `|y - y'| < d`, then
`|x + y - (x' + y')| < e`.
-/
lemma plus_contin (x y e : K) (he : 0 < e) :
  ∃ c > 0, ∃ d > 0, ∀ x' y', AbsSmall c (x - x') → AbsSmall d (y - y') → AbsSmall e (x + y - (x' + y')) := sorry

-- End Mult_Continuous.


-- Section Monotonous_functions.

-- (**
-- ** Monotonous Functions

-- Finally, we study several properties of monotonous functions and
-- characterize them in some way.

-- %\begin{convention}% Let [R] be an ordered field.
-- %\end{convention}%
-- *)
-- Variable R : COrdField.

-- Convention: Let K be an ordered field.
-- (Already assumed above: variable [Field K] [LinearOrder K] [IsStrictOrderedRing K])

-- (**
-- We begin by characterizing the preservation of less (less or equal)
-- in terms of preservation of less or equal (less).
-- *)

-- Lemma resp_less_char' : forall (P : R -> CProp) (f : forall x, P x -> R) x y Hx Hy,
--  (x [#] y -> f x Hx [#] f y Hy) -> (x [<=] y -> f x Hx [<=] f y Hy) ->
--  x [<] y -> f x Hx [<] f y Hy.
-- Proof.
--  intros.
--  elim (ap_imp_less _ _ _ (X (less_imp_ap _ _ _ X0))); intros.
--   auto.
--  exfalso.
--  apply less_irreflexive_unfolded with (x := f x Hx).
--  apply leEq_less_trans with (f y Hy); auto.
--  apply H; apply less_leEq; auto.
-- Qed.


/--
If `f` preserves apartness and order, then it preserves strict order.
-/
lemma resp_less_char'
  {P : K → Prop}
  (f : ∀ x, P x → K)
  (x y : K) (Hx : P x) (Hy : P y)
  (hap : x ≠ y → f x Hx ≠ f y Hy)
  (hle : x ≤ y → f x Hx ≤ f y Hy)
  (hxy : x < y) : f x Hx < f y Hy :=
by
  by_cases h : f x Hx = f y Hy
  · exfalso
    have : x ≠ y := ne_of_lt hxy
    have := hap this
    contradiction
  · exact lt_of_le_of_ne (hle hxy.le) h


-- Lemma resp_less_char : forall (f : R -> R) x y,
--  (x [#] y -> f x [#] f y) -> (x [<=] y -> f x [<=] f y) -> x [<] y -> f x [<] f y.
-- Proof.
--  intros.
--  set (f' := fun (x : R) (H : True) => f x) in *.
--  change (f' x I [<] f' y I) in |- *.
--  apply resp_less_char' with (P := fun x : R => True); auto.
-- Qed.


lemma resp_less_char (f : K → K)
  (hap : ∀ x y, x ≠ y → f x ≠ f y)
  (hle : ∀ x y, x ≤ y → f x ≤ f y)
  {x y : K} (hxy : x < y) : f x < f y := sorry




-- Lemma resp_leEq_char' : forall (P : R -> CProp) (f : forall x : R, P x -> R) x y Hx Hy,
--  (x [=] y -> f x Hx [=] f y Hy) -> (x [<] y -> f x Hx [<] f y Hy) ->
--  x [<=] y -> f x Hx [<=] f y Hy.
-- Proof.
--  intros.
--  rewrite -> leEq_def.
--  intro.
--  cut (Not (x [<] y) /\ ~ x [=] y); intros.
--   inversion_clear H1.
--   apply H3.
--   apply leEq_imp_eq; firstorder using leEq_def.
--  split; intro.
--   apply less_irreflexive_unfolded with (x := f y Hy).
--   apply less_transitive_unfolded with (f x Hx); auto.
--  apply less_irreflexive_unfolded with (x := f y Hy).
--  apply less_leEq_trans with (f x Hx); auto.
--  apply eq_imp_leEq; auto.
-- Qed.


lemma resp_leEq_char'
  {P : K → Prop}
  (f : ∀ x, P x → K)
  (x y : K) (Hx : P x) (Hy : P y)
  (heq : x = y → f x Hx = f y Hy)
  (hlt : x < y → f x Hx < f y Hy)
  (hle : x ≤ y) : f x Hx ≤ f y Hy := sorry



-- Lemma resp_leEq_char : forall (f : R -> R) x y,
--  (x [=] y -> f x [=] f y) -> (x [<] y -> f x [<] f y) -> x [<=] y -> f x [<=] f y.
-- Proof.
--  intros.
--  set (f' := fun (x : R) (H : True) => f x) in *.
--  change (f' x I [<=] f' y I) in |- *.
--  apply resp_leEq_char' with (P := fun x : R => True); auto.
-- Qed.

lemma resp_leEq_char (f : K → K)
  (heq : ∀ x y, x = y → f x = f y)
  (hlt : ∀ x y, x < y → f x < f y)
  {x y : K} (hle : x ≤ y) : f x ≤ f y := sorry











-- (**
-- Next, we see different characterizations of monotonous functions from
-- some subset of the natural numbers into [R].  Mainly, these
-- amount (for different types of functions) to proving that a function
-- is monotonous iff [f(i) [<] f(i+1)] for every [i].

-- Also, strictly monotonous functions are injective.
-- *)

-- Lemma local_mon_imp_mon : forall f : nat -> R,
--  (forall i, f i [<] f (S i)) -> forall i j, i < j -> f i [<] f j.
-- Proof.
--  simple induction j.
--   intros H0; exfalso; inversion H0.
--  clear j; intro j; intros H0 H1.
--  elim (le_lt_eq_dec _ _ H1); intro.
--   apply leEq_less_trans with (f j).
--    apply less_leEq; apply H0; auto with arith.
--   auto.
--  rewrite <- b; apply X.
-- Qed.


/--
If `f : ℕ → K` is strictly increasing (`f i < f (i+1)` for all `i`), then for all `i < j`, `f i < f j`.
-/
lemma local_mon_imp_mon (f : ℕ → K) (h : ∀ i, f i < f (i + 1)) :
  ∀ i j, i < j → f i < f j := by
  intros i j hij
  induction' hij with j hij ih
  { -- base case: i < i+1
    exact h i }
  { -- inductive step: i < j+1
    exact lt_trans ih (h j) }


-- Lemma local_mon_imp_mon' : forall f : nat -> R,
--  (forall i, f i [<] f (S i)) -> forall i j, i <= j -> f i [<=] f j.
-- Proof.
--  intros f H i j H0.
--  elim (le_lt_eq_dec _ _ H0); intro.
--   apply less_leEq; apply local_mon_imp_mon with (f := f); assumption.
--  apply eq_imp_leEq; rewrite b; algebra.
-- Qed.





/--
If `f : ℕ → K` is strictly increasing (`f i < f (i+1)` for all `i`), then for all `i ≤ j`, `f i ≤ f j`.
-/
lemma local_mon_imp_mon' (f : ℕ → K) (h : ∀ i, f i < f (i + 1)) :
  ∀ i j, i ≤ j → f i ≤ f j :=
by
  intros i j hij
  by_cases h_eq : i = j
  · rw [h_eq]
  · have hlt : i < j := lt_of_le_of_ne hij h_eq
    rw [le_iff_eq_or_lt]
    right
    exact local_mon_imp_mon e he N f_bnd f h i j hlt




-- Lemma local_mon'_imp_mon' : forall f : nat -> R,
--  (forall i, f i [<=] f (S i)) -> forall i j, i <= j -> f i [<=] f j.
-- Proof.
--  intros; induction  j as [| j Hrecj].
--   cut (i = 0); [ intro | auto with arith ].
--   rewrite H1; apply leEq_reflexive.
--  elim (le_lt_eq_dec _ _ H0); intro.
--   apply leEq_transitive with (f j).
--    apply Hrecj; auto with arith.
--   apply H.
--  rewrite b; apply leEq_reflexive.
-- Qed.



/--
If `f : ℕ → K` is weakly increasing (`f i ≤ f (i+1)` for all `i`), then for all `i ≤ j`, `f i ≤ f j`.
-/
lemma local_mon'_imp_mon' (f : ℕ → K) (h : ∀ i, f i ≤ f (i + 1)) :
  ∀ i j, i ≤ j → f i ≤ f j := by sorry





-- Lemma mon_imp_mon' : forall f : nat -> R,
--  (forall i j, i < j -> f i [<] f j) -> forall i j, i <= j -> f i [<=] f j.
-- Proof.
--  intros f H i j H0.
--  elim (le_lt_eq_dec _ _ H0); intro.
--   apply less_leEq; apply H; assumption.
--  rewrite b; apply leEq_reflexive.
-- Qed.




/--
If `f : ℕ → K` is strictly increasing (`f i < f j` for all `i < j`), then for all `i ≤ j`, `f i ≤ f j`.
-/
lemma mon_imp_mon' (f : ℕ → K) (h : ∀ i j, i < j → f i < f j) :
  ∀ i j, i ≤ j → f i ≤ f j :=
by
  intros i j hij
  by_cases h_eq : i = j
  · rw [h_eq]
  · have hlt : i < j := lt_of_le_of_ne hij h_eq
    exact (h i j hlt).le







-- Lemma mon_imp_inj : forall f : nat -> R,
--  (forall i j, i < j -> f i [<] f j) -> forall i j, f i [=] f j -> i = j.
-- Proof.
--  intros.
--  cut (~ i <> j); [ lia | intro ].
--  cut (i < j \/ j < i); [ intro | apply not_eq; auto ].
--  inversion_clear H1; (exfalso; cut (f i [#] f j); [ apply eq_imp_not_ap; assumption | idtac ]).
--   apply less_imp_ap; apply X; assumption.
--  apply Greater_imp_ap; apply X; assumption.
-- Qed.






/--
If `f : ℕ → K` is strictly increasing (`f i < f j` for all `i < j`), then `f` is injective.
-/
lemma mon_imp_inj (f : ℕ → K) (h : ∀ i j, i < j → f i < f j) :
  ∀ i j, f i = f j → i = j := by
  intros i j h_eq
  by_contra h_neq
  cases' lt_or_gt_of_ne h_neq with hij hji
  { -- i < j
    have := h i j hij
    rw [h_eq] at this
    exact lt_irrefl _ this
  }
  { -- j < i
    have := h j i hji
    rw [←h_eq] at this
    exact lt_irrefl _ this
  }








-- Lemma local_mon_imp_mon_lt : forall n (f : forall i, i < n -> R),
--  (forall i H H', f i H [<] f (S i) H') -> forall i j Hi Hj, i < j -> f i Hi [<] f j Hj.
-- Proof.
--  simple induction j.
--   intros Hi Hj H0; exfalso; inversion H0.
--  clear j; intro j; intros.
--  elim (le_lt_eq_dec _ _ H); intro.
--   cut (j < n); [ intro | auto with arith ].
--   apply leEq_less_trans with (f j H0).
--    apply less_leEq; apply X0; auto with arith.
--   apply X.
--  generalize Hj; rewrite <- b.
--  intro; apply X.
-- Qed.













/--
If `f : ∀ i, i < n → K` is strictly increasing (`f i Hi < f (i+1) H'i` for all `i < n - 1`), then for all `i < j < n`, `f i Hi < f j Hj`.
-/
lemma local_mon_imp_mon_lt
  (n : ℕ)
  (f : ∀ i, i < n → K)
  (h : ∀ i (Hi : i < n) (H'i : i + 1 < n), f i Hi < f (i + 1) H'i) :
  ∀ i j (Hi : i < n) (Hj : j < n), i < j → f i Hi < f j Hj := by
  intros i j Hi Hj hij
  induction' hij with j' hij' IH
  { -- base case: i < i+1
    exact h i Hi Hj }
  { -- inductive step: i < j'+1
    have Hj' : j' < n := by {exact Nat.lt_of_succ_lt Hj}
    exact lt_trans (by {exact IH Hj'}) (h j' Hj' (_)) }














-- Lemma local_mon_imp_mon'_lt : forall n (f : forall i, i < n -> R),
--  (forall i H H', f i H [<] f (S i) H') -> nat_less_n_fun f ->
--  forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
-- Proof.
--  intros.
--  elim (le_lt_eq_dec _ _ H0); intros.
--   apply less_leEq; apply local_mon_imp_mon_lt with n; auto.
--  apply eq_imp_leEq; apply H; assumption.
-- Qed.



/--
If `f : ∀ i, i < n → K` is strictly increasing (`f i Hi < f (i+1) H'i` for all `i < n - 1`),
then for all `i ≤ j < n`, `f i Hi ≤ f j Hj`.
-/
lemma local_mon_imp_mon'_lt
  (n : ℕ)
  (f : ∀ i, i < n → K)
  (h : ∀ i (Hi : i < n) (H'i : i + 1 < n), f i Hi < f (i + 1) H'i)
  : ∀ i j (Hi : i < n) (Hj : j < n), i ≤ j → f i Hi ≤ f j Hj := by sorry















-- Lemma local_mon'_imp_mon'_lt : forall n (f : forall i, i < n -> R),
--  (forall i H H', f i H [<=] f (S i) H') -> nat_less_n_fun f ->
--  forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
-- Proof.
--  simple induction j.
--   intros.
--   cut (i = 0); [ intro | auto with arith ].
--   apply eq_imp_leEq; apply H0; auto.
--  intro m; intros.
--  elim (le_lt_eq_dec _ _ H2); intro.
--   cut (m < n); [ intro | auto with arith ].
--   apply leEq_transitive with (f m H3); auto.
--   apply H1; auto with arith.
--  apply eq_imp_leEq; apply H0; assumption.
-- Qed.




/--
If `f : ∀ i, i < n → K` is weakly increasing (`f i Hi ≤ f (i+1) H'i` for all `i < n - 1`),
then for all `i ≤ j < n`, `f i Hi ≤ f j Hj`.
-/
lemma local_mon'_imp_mon'_lt
  (n : ℕ)
  (f : ∀ i, i < n → K)
  (h : ∀ i (Hi : i < n) (H'i : i + 1 < n), f i Hi ≤ f (i + 1) H'i)
  : ∀ i j (Hi : i < n) (Hj : j < n), i ≤ j → f i Hi ≤ f j Hj := by
  intros i j Hi Hj hij
  induction' j with j IH
  { -- base case: j = 0
    have : i = 0 := Nat.eq_zero_of_le_zero hij
    subst this
    exact le_rfl}
  { -- inductive step: j = j+1
    by_cases h_eq : i = j.succ
    { subst h_eq; exact le_rfl }
    { have hij' : i ≤ j := Nat.le_of_lt_succ (lt_of_le_of_ne hij h_eq)
      have Hj' : j < n := Nat.lt_of_succ_lt Hj
      exact le_trans (IH Hj' hij') (h j Hj' Hj) } }




-- Lemma local_mon'_imp_mon'2_lt : forall n (f : forall i, i < n -> R),
--  (forall i H H', f i H [<=] f (S i) H') -> forall i j Hi Hj, i < j -> f i Hi [<=] f j Hj.
-- Proof.
--  intros; induction  j as [| j Hrecj].
--   exfalso; inversion H0.
--  elim (le_lt_eq_dec _ _ H0); intro.
--   cut (j < n); [ intro | auto with arith ].
--   apply leEq_transitive with (f j H1).
--    apply Hrecj; auto with arith.
--   apply H.
--  generalize Hj; rewrite <- b.
--  intro; apply H.
-- Qed.



/--
If `f : ∀ i, i < n → K` is weakly increasing (`f i Hi ≤ f (i+1) H'i` for all `i < n - 1`),
then for all `i < j < n`, `f i Hi ≤ f j Hj`.
-/
lemma local_mon'_imp_mon'2_lt
  (n : ℕ)
  (f : ∀ i, i < n → K)
  (h : ∀ i (Hi : i < n) (H'i : i + 1 < n), f i Hi ≤ f (i + 1) H'i)
  : ∀ i j (Hi : i < n) (Hj : j < n), i < j → f i Hi ≤ f j Hj := by
  intros i j Hi Hj hij
  induction' j with j IH
  { exfalso; exact Nat.not_lt_zero i hij }
  cases' Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with hlt heq
  { -- i < j < n
    have Hj' : j < n := Nat.lt_of_succ_lt Hj
    exact le_trans (IH Hj' hlt) (h j Hj' Hj) }
  { -- i = j
    subst heq
    exact h i Hi Hj }








-- Lemma mon_imp_mon'_lt : forall n (f : forall i, i < n -> R), nat_less_n_fun f ->
--  (forall i j Hi Hj, i < j -> f i Hi [<] f j Hj) -> forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
-- Proof.
--  intros.
--  elim (le_lt_eq_dec _ _ H0); intro.
--   apply less_leEq; auto.
--  apply eq_imp_leEq; auto.
-- Qed.





/--
If `f : ∀ i, i < n → K` is strictly increasing (`f i Hi < f j Hj` for all `i < j < n`), then for all `i ≤ j < n`, `f i Hi ≤ f j Hj`.
-/
lemma mon_imp_mon'_lt
  (n : ℕ)
  (f : ∀ i, i < n → K)
  (h : ∀ i j (Hi : i < n) (Hj : j < n), i < j → f i Hi < f j Hj)
  : ∀ i j (Hi : i < n) (Hj : j < n), i ≤ j → f i Hi ≤ f j Hj := by
  intros i j Hi Hj hij
  by_cases h_eq : i = j
  · sorry
  · have hlt : i < j := lt_of_le_of_ne hij h_eq
    exact (h i j Hi Hj hlt).le










-- Lemma mon_imp_inj_lt : forall n (f : forall i, i < n -> R),
--  (forall i j Hi Hj, i < j -> f i Hi [<] f j Hj) ->
--  forall i j Hi Hj, f i Hi [=] f j Hj -> i = j.
-- Proof.
--  intros.
--  cut (~ i <> j); intro.
--   clear X H Hj Hi; lia.
--  cut (i < j \/ j < i); [ intro | apply not_eq; auto ].
--  inversion_clear H1; (exfalso; cut (f i Hi [#] f j Hj);
--    [ apply eq_imp_not_ap; assumption | idtac ]).
--   apply less_imp_ap; auto.
--  apply Greater_imp_ap; auto.
-- Qed.





/--
If `f : ∀ i, i < n → K` is strictly increasing (`f i Hi < f j Hj` for all `i < j < n`), then `f` is injective.
-/
lemma mon_imp_inj_lt
  (n : ℕ)
  (f : ∀ i, i < n → K)
  (h : ∀ i j (Hi : i < n) (Hj : j < n), i < j → f i Hi < f j Hj) :
  ∀ i j (Hi : i < n) (Hj : j < n), f i Hi = f j Hj → i = j :=
by
  intros i j Hi Hj h_eq
  by_contra h_neq
  cases' lt_or_gt_of_ne h_neq with hij hji
  { -- i < j
    have := h i j Hi Hj hij
    rw [h_eq] at this
    exact lt_irrefl _ this }
  { -- j < i
    have := h j i Hj Hi hji
    rw [←h_eq] at this
    exact lt_irrefl _ this }








-- Lemma local_mon_imp_mon_le : forall n (f : forall i, i <= n -> R),
--  (forall i H H', f i H [<] f (S i) H') -> forall i j Hi Hj, i < j -> f i Hi [<] f j Hj.
-- Proof.
--  simple induction j.
--   intros Hi Hj H0; exfalso; inversion H0.
--  clear j; intro j; intros.
--  elim (le_lt_eq_dec _ _ H); intro.
--   cut (j <= n); [ intro | auto with arith ].
--   apply leEq_less_trans with (f j H0).
--    apply less_leEq; auto with arith.
--   apply X.
--  generalize Hj; rewrite <- b.
--  auto.
-- Qed.





/--
If `f : ∀ i, i ≤ n → K` is strictly increasing (`f i Hi < f (i+1) H'i` for all `i < n`),
then for all `i < j ≤ n`, `f i Hi < f j Hj`.
-/
lemma local_mon_imp_mon_le
  (n : ℕ)
  (f : ∀ i, i ≤ n → K)
  (h : ∀ i (Hi : i ≤ n) (H'i : i + 1 ≤ n), f i Hi < f (i + 1) H'i) :
  ∀ i j (Hi : i ≤ n) (Hj : j ≤ n), i < j → f i Hi < f j Hj := by
  intros i j Hi Hj hij
  induction' j with j IH
  { exfalso; exact Nat.not_lt_zero i hij }
  cases' Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with hlt heq
  { -- i < j < j+1
    have Hj' : j ≤ n := Nat.le_of_succ_le Hj
    exact lt_trans (IH Hj' hlt) (h j Hj' Hj) }
  { -- i = j
    subst heq
    exact h i Hi Hj }

















-- Lemma local_mon_imp_mon'_le : forall n (f : forall i, i <= n -> R),
--  (forall i H H', f i H [<] f (S i) H') -> nat_less_n_fun' f ->
--  forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
-- Proof.
--  intros.
--  elim (le_lt_eq_dec _ _ H0); intros.
--   apply less_leEq; apply local_mon_imp_mon_le with n; auto.
--  apply eq_imp_leEq; auto.
-- Qed.





/--
If `f : ∀ i, i ≤ n → K` is strictly increasing (`f i Hi < f (i+1) H'i` for all `i < n`),
then for all `i ≤ j ≤ n`, `f i Hi ≤ f j Hj`.
-/
lemma local_mon_imp_mon'_le
  (n : ℕ)
  (f : ∀ i, i ≤ n → K)
  (h : ∀ i (Hi : i ≤ n) (H'i : i + 1 ≤ n), f i Hi < f (i + 1) H'i)
  : ∀ i j (Hi : i ≤ n) (Hj : j ≤ n), i ≤ j → f i Hi ≤ f j Hj :=
by
  intros i j Hi Hj hij
  by_cases h_eq : i = j
  · subst h_eq; exact le_rfl
  · have hlt : i < j := lt_of_le_of_ne hij h_eq
    rw [le_iff_eq_or_lt]
    right
    exact local_mon_imp_mon_le e he N f_bnd n f h i j Hi Hj hlt


















-- Lemma local_mon'_imp_mon'_le : forall n (f : forall i, i <= n -> R),
--  (forall i H H', f i H [<=] f (S i) H') -> nat_less_n_fun' f ->
--  forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
-- Proof.
--  simple induction j.
--   intros.
--   cut (i = 0); [ intro | auto with arith ].
--   apply eq_imp_leEq; apply H0; auto.
--  intro m; intros.
--  elim (le_lt_eq_dec _ _ H2); intro.
--   cut (m <= n); [ intro | auto with arith ].
--   apply leEq_transitive with (f m H3); auto.
--   apply H1; auto with arith.
--  apply eq_imp_leEq; apply H0; assumption.
-- Qed.


/--
If `f : ∀ i, i ≤ n → K` is weakly increasing (`f i Hi ≤ f (i+1) H'i` for all `i < n`),
then for all `i ≤ j ≤ n`, `f i Hi ≤ f j Hj`.
-/
lemma local_mon'_imp_mon'_le
  (n : ℕ)
  (f : ∀ i, i ≤ n → K)
  (h : ∀ i (Hi : i ≤ n) (H'i : i + 1 ≤ n), f i Hi ≤ f (i + 1) H'i)
  : ∀ i j (Hi : i ≤ n) (Hj : j ≤ n), i ≤ j → f i Hi ≤ f j Hj :=
by
  intros i j Hi Hj hij
  induction' j with j IH
  { -- base case: j = 0
    have : i = 0 := Nat.eq_zero_of_le_zero hij
    subst this
    exact le_rfl }
  { -- inductive step: j = j+1
    by_cases h_eq : i = j.succ
    { subst h_eq; exact le_rfl }
    { have hij' : i ≤ j := Nat.le_of_lt_succ (lt_of_le_of_ne hij h_eq)
      have Hj' : j ≤ n := Nat.le_of_succ_le Hj
      exact le_trans (IH Hj' hij') (h j Hj' Hj) } }














-- Lemma local_mon'_imp_mon'2_le : forall n (f : forall i, i <= n -> R),
--  (forall i H H', f i H [<=] f (S i) H') -> forall i j Hi Hj, i < j -> f i Hi [<=] f j Hj.
-- Proof.
--  intros; induction  j as [| j Hrecj].
--   exfalso; inversion H0.
--  elim (le_lt_eq_dec _ _ H0); intro.
--   cut (j <= n); [ intro | auto with arith ].
--   apply leEq_transitive with (f j H1).
--    apply Hrecj; auto with arith.
--   apply H.
--  generalize Hj; rewrite <- b.
--  intro; apply H.
-- Qed.








/--
If `f : ∀ i, i ≤ n → K` is weakly increasing (`f i Hi ≤ f (i+1) H'i` for all `i < n`),
then for all `i < j ≤ n`, `f i Hi ≤ f j Hj`.
-/
lemma local_mon'_imp_mon'2_le
  (n : ℕ)
  (f : ∀ i, i ≤ n → K)
  (h : ∀ i (Hi : i ≤ n) (H'i : i + 1 ≤ n), f i Hi ≤ f (i + 1) H'i)
  : ∀ i j (Hi : i ≤ n) (Hj : j ≤ n), i < j → f i Hi ≤ f j Hj :=
by
  intros i j Hi Hj hij
  induction' j with j IH
  { exfalso; exact Nat.not_lt_zero i hij }
  cases' Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with hlt heq
  { -- i < j < j+1
    have Hj' : j ≤ n := Nat.le_of_succ_le Hj
    exact le_trans (IH Hj' hlt) (h j Hj' Hj) }
  { -- i = j
    subst heq
    exact h i Hi Hj }

















-- Lemma mon_imp_mon'_le : forall n (f : forall i, i <= n -> R), nat_less_n_fun' f ->
--  (forall i j Hi Hj, i < j -> f i Hi [<] f j Hj) -> forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
-- Proof.
--  intros.
--  elim (le_lt_eq_dec _ _ H0); intro.
--   apply less_leEq; auto.
--  apply eq_imp_leEq; auto.
-- Qed.







/--
If `f : ∀ i, i ≤ n → K` is strictly increasing (`f i Hi < f j Hj` for all `i < j ≤ n`), then for all `i ≤ j ≤ n`, `f i Hi ≤ f j Hj`.
-/
lemma mon_imp_mon'_le
  (n : ℕ)
  (f : ∀ i, i ≤ n → K)
  (h : ∀ i j (Hi : i ≤ n) (Hj : j ≤ n), i < j → f i Hi < f j Hj)
  : ∀ i j (Hi : i ≤ n) (Hj : j ≤ n), i ≤ j → f i Hi ≤ f j Hj :=
by
  intros i j Hi Hj hij
  by_cases h_eq : i = j
  · subst h_eq; exact le_rfl
  · have hlt : i < j := lt_of_le_of_ne hij h_eq
    exact (h i j Hi Hj hlt).le





-- Lemma mon_imp_inj_le : forall n (f : forall i, i <= n -> R),
--  (forall i j Hi Hj, i < j -> f i Hi [<] f j Hj) -> forall i j Hi Hj, f i Hi [=] f j Hj -> i = j.
-- Proof.
--  intros.
--  cut (~ i <> j); intro.
--   clear H X Hj Hi; lia.
--  cut (i < j \/ j < i); [ intro | apply not_eq; auto ].
--  inversion_clear H1; (exfalso; cut (f i Hi [#] f j Hj);
--    [ apply eq_imp_not_ap; assumption | idtac ]).
--   apply less_imp_ap; auto.
--  apply Greater_imp_ap; auto.
-- Qed.







/--
If `f : ∀ i, i ≤ n → K` is strictly increasing (`f i Hi < f j Hj` for all `i < j ≤ n`), then `f` is injective.
-/
lemma mon_imp_inj_le
  (n : ℕ)
  (f : ∀ i, i ≤ n → K)
  (h : ∀ i j (Hi : i ≤ n) (Hj : j ≤ n), i < j → f i Hi < f j Hj) :
  ∀ i j (Hi : i ≤ n) (Hj : j ≤ n), f i Hi = f j Hj → i = j :=
by
  intros i j Hi Hj h_eq
  by_contra h_neq
  cases' lt_or_gt_of_ne h_neq with hij hji
  { -- i < j
    have := h i j Hi Hj hij
    rw [h_eq] at this
    exact lt_irrefl _ this }
  { -- j < i
    have := h j i Hj Hi hji
    rw [←h_eq] at this
    exact lt_irrefl _ this }






-- (**
-- A similar result for %{\em %partial%}% functions.
-- *)

-- Lemma part_mon_imp_mon' : forall F (I : R -> CProp), (forall x, I x -> Dom F x) ->
--  (forall x y Hx Hy, I x -> I y -> x [<] y -> F x Hx [<] F y Hy) ->
--  forall x y Hx Hy, I x -> I y -> x [<=] y -> F x Hx [<=] F y Hy.
-- Proof.
--  intros.
--  rewrite -> leEq_def.
--  intro.
--  cut (x [=] y); intros.
--   apply (less_irreflexive_unfolded _ (F x Hx)).
--   astepl (F y Hy); auto.
--  apply leEq_imp_eq.
--   firstorder using leEq_def.
--  rewrite -> leEq_def.
--  intro.
--  apply (less_irreflexive_unfolded _ (F x Hx)).
--  apply less_transitive_unfolded with (F y Hy); firstorder using leEq_def.
-- Qed.



/--
If `F` is a partial function defined on a subset `I` of `K`, and `F` is strictly increasing on `I`,
then `F` is weakly increasing on `I`.
-/
lemma part_mon_imp_mon'
  (I : K → Prop)
  (F : ∀ x, I x → K)
  (domF : ∀ x, I x → True) -- dummy, for compatibility with coq statement
  (h : ∀ x y (Hx : I x) (Hy : I y), x < y → F x Hx < F y Hy) :
  ∀ x y (Hx : I x) (Hy : I y), x ≤ y → F x Hx ≤ F y Hy :=
by
  intros x y Hx Hy hle
  by_cases h_eq : x = y
  · subst h_eq; exact le_rfl
  · have hlt : x < y := lt_of_le_of_ne hle h_eq
    exact (h x y Hx Hy hlt).le




-- End Monotonous_functions.
