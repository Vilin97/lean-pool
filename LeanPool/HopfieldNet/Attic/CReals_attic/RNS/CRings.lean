/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

-- (* Copyright © 1998-2008
--  * Henk Barendregt
--  * Luís Cruz-Filipe
--  * Herman Geuvers
--  * Mariusz Giero
--  * Rik van Ginneken
--  * Dimitri Hendriks
--  * Sébastien Hinderer
--  * Cezary Kaliszyk
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

-- (** printing [*] %\ensuremath\times% #&times;# *)
-- (** printing [^] %\ensuremath{\hat{\ }}% #^# *)
-- (** printing {*} %\ensuremath\times% #&times;# *)
-- (** printing {**} %\ensuremath\ast% #&lowast;# *)
-- (** printing {^} %\ensuremath{\hat{\ }}% #^# *)
-- (** printing [1] %\ensuremath{\mathbf1}% #1# *)
-- (** printing Two %\ensuremath{\mathbf2}% #2# *)
-- (** printing Three %\ensuremath{\mathbf3}% #3# *)
-- (** printing Four %\ensuremath{\mathbf4}% #4# *)
-- (** printing Six %\ensuremath{\mathbf6}% #6# *)
-- (** printing Eight %\ensuremath{\mathbf8}% #8# *)
-- (** printing Nine %\ensuremath{\mathbf9}% #9# *)
-- (** printing Twelve %\ensuremath{\mathbf{12}}% #12# *)
-- (** printing Sixteen %\ensuremath{\mathbf{16}}% #16# *)
-- (** printing Eighteen %\ensuremath{\mathbf{18}}% #18# *)
-- (** printing TwentyFour %\ensuremath{\mathbf{24}}% #24# *)
-- (** printing FortyEight %\ensuremath{\mathbf{48}}% #48# *)

-- Require Import CoRN.tactics.CornTac.
-- Require Export CoRN.algebra.CSums.
-- Require Import CoRN.algebra.CAbMonoids Coq.Sorting.Permutation CoRN.util.SetoidPermutation Coq.Setoids.Setoid Coq.Classes.Morphisms.
-- From Coq Require Import Lia.

-- Transparent sym_eq.
-- Transparent f_equal.

-- (* Begin_SpecReals *)

-- (* Constructive RINGS *)

-- (**
-- * Rings
-- We actually define commutative rings with identity.
-- ** Definition of the notion of Ring
-- *)
-- Definition distributive S (mult plus : CSetoid_bin_op S) :=
--   forall x y z, mult x (plus y z) [=] plus (mult x y) (mult x z).

-- Arguments distributive [S].

-- Record is_CRing (G : CAbGroup) (One : G) (mult : CSetoid_bin_op G) : CProp :=
--   {ax_mult_assoc : associative mult;
--    ax_mult_mon   : is_CMonoid (Build_CSemiGroup G mult ax_mult_assoc) One;
--    ax_mult_com   : commutes mult;
--    ax_dist       : distributive mult csg_op;
--    ax_non_triv   : One [#] [0]}.

-- Record CRing : Type :=
--   {cr_crr   : CAbGroup;
--    cr_one   :  cr_crr;
--    cr_mult  :  CSetoid_bin_op cr_crr;
--    cr_proof :  is_CRing cr_crr cr_one cr_mult}.

-- Definition cr_plus := @csg_op.
-- Definition cr_inv := @cg_inv.
-- Definition cr_minus := cg_minus.


-- Notation "[1]" := (cr_one _).

-- Module Export coercions.
--   Export CAbGroups.coercions.
--   Coercion cr_crr : CRing >-> CAbGroup.
-- End coercions.

-- (* End_SpecReals *)

-- (* Begin_SpecReals *)

-- (**
-- %\begin{nameconvention}%
-- In the names of lemmas, we will denote [One] with [one],
-- and [[*]] with [mult].
-- %\end{nameconvention}%
-- *)

-- Arguments cr_mult {c}.
-- Infix "[*]" := cr_mult (at level 40, left associativity).

-- Section CRing_axioms.
-- (**
-- ** Ring axioms
-- %\begin{convention}% Let [R] be a ring.
-- %\end{convention}%
-- *)
-- Variable R : CRing.

-- Lemma CRing_is_CRing : is_CRing R [1] cr_mult.
-- Proof.
--  elim R; auto.
-- Qed.

-- Lemma mult_assoc : associative (cr_mult (c:=R)).
-- Proof.
--  elim CRing_is_CRing; auto.
-- Qed.

-- Lemma mult_commutes : commutes (cr_mult (c:=R)).
-- Proof.
--  elim CRing_is_CRing; auto.
-- Qed.

-- Lemma mult_mon : is_CMonoid (Build_CSemiGroup R cr_mult mult_assoc) [1].
-- Proof.
--  elim (cr_proof R).
--  intros H1 H2 H3 H4 H5.
--  apply is_CMonoid_proof_irr with H1.
--  assumption.
-- Qed.

-- (* End_SpecReals *)

-- Lemma dist : distributive (S:=R) cr_mult (cr_plus R).
-- Proof.
--  elim (cr_proof R); auto.
-- Qed.

-- Lemma ring_non_triv : ([1]:R) [#] [0].
-- Proof.
--  elim (cr_proof R); auto.
-- Qed.

-- Lemma mult_wd : forall x1 x2 y1 y2 : R, x1 [=] x2 -> y1 [=] y2 -> x1[*]y1 [=] x2[*]y2.
-- Proof.
--  intros; algebra.
-- Qed.

-- Lemma mult_wdl : forall x1 x2 y : R, x1 [=] x2 -> x1[*]y [=] x2[*]y.
-- Proof.
--  intros; algebra.
-- Qed.

-- Lemma mult_wdr : forall x y1 y2 : R, y1 [=] y2 -> x[*]y1 [=] x[*]y2.
-- Proof.
--  intros; algebra.
-- Qed.

-- (* Begin_SpecReals *)

-- End CRing_axioms.

-- Section Ring_constructions.
-- (**
-- ** Ring constructions
-- %\begin{convention}%
-- Let [R] be a ring.
-- %\end{convention}%
-- *)
-- Variable R : CRing.

-- (**
-- The multiplicative monoid of a ring is defined as follows.
-- *)
-- Definition Build_multCMonoid : CMonoid := Build_CMonoid _ _ (mult_mon R).

-- (** Furthermore, this is an abelian monoid: *)
-- Definition Build_multCAbMonoid: CAbMonoid :=
--   Build_CAbMonoid Build_multCMonoid (mult_commutes R).

-- End Ring_constructions.

-- (* End_SpecReals *)

-- Section Ring_unfolded.
-- (**
-- ** Ring unfolded
-- %\begin{convention}% Let [R] be a ring.
-- %\end{convention}%
-- *)
-- Variable R : CRing.
-- (* begin hide *)
-- Let mmR := Build_multCMonoid R.
-- (* end hide *)

-- Lemma mult_assoc_unfolded : forall x y z : R, x[*] (y[*]z) [=] x[*]y[*]z.
-- Proof mult_assoc R.

-- Lemma mult_commut_unfolded : forall x y : R, x[*]y [=] y[*]x.
-- Proof mult_commutes R.
-- Hint Resolve mult_commut_unfolded: algebra.

-- Lemma mult_one : forall x : R, x[*][1] [=] x.
-- Proof cm_rht_unit mmR.

-- Lemma one_mult : forall x : R, [1][*]x [=] x.
-- Proof cm_lft_unit mmR.

-- Lemma ring_dist_unfolded : forall x y z : R, x[*] (y[+]z) [=] x[*]y[+]x[*]z.
-- Proof dist R.
-- Hint Resolve ring_dist_unfolded: algebra.

-- Lemma ring_distl_unfolded : forall x y z : R, (y[+]z) [*]x [=] y[*]x[+]z[*]x.
-- Proof.
--  intros x y z.
--  astepl (x[*] (y[+]z)).
--  astepl (x[*]y[+]x[*]z).
--  astepl (y[*]x[+]x[*]z).
--  Step_final (y[*]x[+]z[*]x).
-- Qed.

-- End Ring_unfolded.
-- #[global]
-- Hint Resolve mult_assoc_unfolded: algebra.
-- #[global]
-- Hint Resolve ring_non_triv mult_one one_mult mult_commut_unfolded: algebra.
-- #[global]
-- Hint Resolve ring_dist_unfolded ring_distl_unfolded: algebra.


-- Section Ring_basics.
-- (**
-- ** Ring basics
-- %\begin{convention}% Let [R] be a ring.
-- %\end{convention}%
-- *)
-- Variable R : CRing.

-- Lemma one_ap_zero : ([1]:R) [#] [0].
-- Proof ring_non_triv R.

-- Definition is_zero_rht S (op : CSetoid_bin_op S) Zero : Prop := forall x, op x Zero [=] Zero.

-- Definition is_zero_lft S (op : CSetoid_bin_op S) Zero : Prop := forall x, op Zero x [=] Zero.

-- Arguments is_zero_rht [S].
-- Arguments is_zero_lft [S].

-- Lemma cring_mult_zero : forall x : R, x[*][0] [=] [0].
-- Proof.
--  intro x.
--  apply cg_cancel_lft with (x[*][0]).
--  astepr (x[*][0]).
--  Step_final (x[*] ([0][+][0])).
-- Qed.
-- Hint Resolve cring_mult_zero: algebra.

-- Lemma x_mult_zero : forall x y : R, y [=] [0] -> x[*]y [=] [0].
-- Proof.
--  intros x y H; Step_final (x[*][0]).
-- Qed.

-- Lemma cring_mult_zero_op : forall x : R, [0][*]x [=] [0].
-- Proof.
--  intro x; Step_final (x[*][0]).
-- Qed.
-- Hint Resolve cring_mult_zero_op: algebra.

-- Lemma cring_inv_mult_lft : forall x y : R, x[*] [--]y [=] [--] (x[*]y).
-- Proof.
--  intros x y.
--  apply cg_inv_unique.
--  astepl (x[*] (y[+] [--]y)).
--  Step_final (x[*][0]).
-- Qed.
-- Hint Resolve cring_inv_mult_lft: algebra.

-- Lemma cring_inv_mult_rht : forall x y : R, [--]x[*]y [=] [--] (x[*]y).
-- Proof.
--  intros x y.
--  astepl (y[*] [--]x).
--  Step_final ( [--] (y[*]x)).
-- Qed.
-- Hint Resolve cring_inv_mult_rht: algebra.

-- Lemma cring_mult_ap_zero :(forall x y : R, x[*]y [#] [0] -> x [#] [0]):CProp.
-- Proof.
--  intros x y H.
--  elim (cs_bin_op_strext _ cr_mult x [0] y y).
--    auto.
--   intro contra; elim (ap_irreflexive _ _ contra).
--  astepr ([0]:R). auto.
-- Qed.

-- Lemma cring_mult_ap_zero_op : (forall x y : R, x[*]y [#] [0] -> y [#] [0])
--   :CProp.
-- Proof.
--  intros x y H.
--  apply cring_mult_ap_zero with x.
--  astepl (x[*]y). auto.
-- Qed.

-- Lemma inv_mult_invol : forall x y : R, [--]x[*] [--]y [=] x[*]y.
-- Proof.
--  intros x y.
--  astepl ( [--] (x[*] [--]y)).
--  Step_final ( [--][--] (x[*]y)).
-- Qed.

-- Lemma ring_dist_minus : forall x y z : R, x[*] (y[-]z) [=] x[*]y[-]x[*]z.
-- Proof.
--  intros x y z.
--  unfold cg_minus in |- *.
--  Step_final (x[*]y[+]x[*] [--]z).
-- Qed.

-- Hint Resolve ring_dist_minus: algebra.

-- Lemma ring_distl_minus : forall x y z : R, (y[-]z) [*]x [=] y[*]x[-]z[*]x.
-- Proof.
--  intros x y z.
--  unfold cg_minus in |- *.
--  Step_final (y[*]x[+] [--]z[*]x).
-- Qed.

-- Hint Resolve ring_distl_minus: algebra.

-- Lemma mult_minus1 : forall x:R, [--][1] [*] x [=] [--]x.
-- Proof.
--  intro x.
--  apply (cg_cancel_lft R x).
--  astepr ([0]:R).
--  astepl (([1][*]x)[+]([--][1][*]x)).
--  astepl (([1][+][--][1])[*]x).
--  Step_final ([0][*]x).
-- Qed.

-- Lemma ring_distr1 : forall a b1 b2:R,
--                     a [*] (b1[-]b2) [=] a[*]b1 [-] a[*]b2.
-- Proof.
--  intros a b1 b2.
--  astepl (a[*](b1[+][--]b2)).
--  astepl (a[*]b1 [+] a[*][--]b2).
--  Step_final (a[*]b1 [+] [--](a[*]b2)).
-- Qed.

-- Lemma ring_distr2 : forall a1 a2 b:R,
--                     (a1[-]a2) [*] b [=] a1[*]b [-] a2[*]b.
-- Proof.
--  intros a1 a2 b.
--  astepl ((a1[+][--]a2)[*]b).
--  astepl (a1[*]b [+] [--]a2[*]b).
--  Step_final (a1[*]b [+] [--](a2[*]b)).
-- Qed.


-- End Ring_basics.
-- #[global]
-- Hint Resolve cring_mult_zero cring_mult_zero_op: algebra.
-- #[global]
-- Hint Resolve inv_mult_invol: algebra.
-- #[global]
-- Hint Resolve cring_inv_mult_lft cring_inv_mult_rht: algebra.
-- #[global]
-- Hint Resolve ring_dist_minus: algebra.
-- #[global]
-- Hint Resolve ring_distl_minus: algebra.
-- #[global]
-- Hint Resolve mult_minus1 ring_distr1 ring_distr2: algebra.
-- (* Begin_SpecReals *)

-- (**
-- ** Ring Definitions
-- Some auxiliary functions and operations over a ring;
-- especially geared towards CReals.
-- *)

-- Section exponentiation.
-- (**
-- *** Exponentiation
-- %\begin{convention}%
-- Let [R] be a ring.
-- %\end{convention}%
-- *)
-- Variable R : CRing.

-- (* End_SpecReals *)

-- Fixpoint nexp (m : nat) : R -> R :=
--   match m with
--   | O   => fun _ : R => [1]
--   | S n => fun x : R => nexp n x[*]x
--   end.

-- Lemma nexp_well_def : forall n, fun_wd (nexp n).
--  intro n; induction  n as [| n Hrecn]; red in |- *; intros; simpl in |- *; algebra.
-- Qed.

-- Lemma nexp_strong_ext : forall n, fun_strext (nexp n).
--  intro n; red in |- *; induction  n as [| n Hrecn]; simpl in |- *; intros x y H.
-- Proof.
--   elim (ap_irreflexive _ _ H).
--  elim (cs_bin_op_strext _ cr_mult _ _ _ _ H); auto.
-- Qed.

-- Definition nexp_op n := Build_CSetoid_un_op R (nexp n) (nexp_strong_ext n).

-- (* Begin_SpecReals *)

-- End exponentiation.

-- (* End_SpecReals *)

-- Notation "x [^] n" := (nexp_op _ n x) (at level 20).
-- Arguments nexp_op [R].

-- (* Begin_SpecReals *)

-- Section nat_injection.
-- (**
-- *** The injection of natural numbers into a ring
-- %\begin{convention}% Let [R] be a ring.
-- %\end{convention}%
-- *)
-- Variable R : CRing.

-- (**
-- The injection of Coq natural numbers into a ring is called [nring].
-- Note that this need not really be an injection; when it is, the ring is said
-- to have characteristic [0].
-- *)

-- Fixpoint nring (m : nat) : R :=
--   match m with
--   | O   => [0]
--   | S n => nring n[+][1]
--   end.
-- Definition Char0 := forall n : nat, 0 < n -> nring n [#] [0].

-- (* End_SpecReals *)

-- Lemma nring_comm_plus : forall n m, nring (n + m) [=] nring n[+]nring m.
-- Proof.
--  intros n m; induction  n as [| n Hrecn]; simpl in |- *.
--   algebra.
--  astepr (nring n[+] ([1][+]nring m)).
--  astepr (nring n[+] (nring m[+][1])).
--  Step_final (nring n[+]nring m[+][1]).
-- Qed.

-- Lemma nring_comm_mult : forall n m, nring (n * m) [=] nring n[*]nring m.
-- Proof.
--  intros n m; induction  n as [| n Hrecn]; simpl in |- *.
--   algebra.
--  apply eq_transitive_unfolded with (nring m[+]nring (n * m)). apply (nring_comm_plus m (n * m)).
--   astepr (nring n[*]nring m[+][1][*]nring m).
--  astepr (nring n[*]nring m[+]nring m).
--  Step_final (nring m[+]nring n[*]nring m).
-- Qed.

-- End nat_injection.

-- #[global]
-- Hint Resolve nring_comm_plus nring_comm_mult: algebra.

-- Arguments nring [R].

-- Notation Two := (nring 2).
-- Notation Three := (nring 3).
-- Notation Four := (nring 4).

-- Notation Six := (nring 6).
-- Notation Eight := (nring 8).
-- Notation Twelve := (nring 12).
-- Notation Sixteen := (nring 16).

-- Notation Nine := (nring 9).
-- Notation Eighteen := (nring 18).
-- Notation TwentyFour := (nring 24).
-- Notation FortyEight := (nring 48).

-- Lemma one_plus_one : forall R : CRing, [1][+][1] [=] (Two:R).
-- Proof.
--  simpl in |- *; algebra.
-- Qed.

-- Lemma x_plus_x : forall (R : CRing) (x : R), x[+]x [=] Two[*]x.
-- Proof.
--  intros R x.
--  astepl ([1][*]x[+][1][*]x).
--  astepl (([1][+][1]) [*]x).
--  simpl in |- *; algebra.
-- Qed.

-- #[global]
-- Hint Resolve one_plus_one x_plus_x: algebra.

-- (**
-- In a ring of characteristic zero, [nring] is really an injection.
-- *)

-- Lemma nring_different : forall R, Char0 R -> forall i j, i <> j -> nring i [#] (nring j:R).
-- Proof.
--  intros R H i j H0.
--  elim (Cnat_total_order i j); intros.
--    replace j with (i + (j - i)).
--     astepr (nring i[+]nring (j - i):R).
--     astepl (nring i[+][0]:R).
--     apply op_lft_resp_ap.
--     apply ap_symmetric_unfolded.
--     apply H.
--     lia.
--    auto with arith.
--   replace i with (j + (i - j)).
--    astepl (nring j[+]nring (i - j):R).
--    astepr (nring j[+] ([0]:R)).
--    apply op_lft_resp_ap.
--    apply H.
--    lia.
--   auto with arith.
--  auto.
-- Qed.

-- Section int_injection.

-- (**
-- *** The injection of integers into a ring
-- %\begin{convention}%
-- Let [R] be a ring.
-- %\end{convention}%
-- *)

-- Variable R : CRing.

-- (**
-- The injection of Coq integers into a ring is called [zring]. Again,
-- this need not really be an injection.

-- The first definition is now obsolete, having been replaced by a more efficient
-- one. It is kept to avoid having to redo all the proofs.
-- *)

-- Definition zring_old k : R := caseZ_diff k (fun m n => nring m[-]nring n).

-- Lemma zring_old_zero : zring_old 0 [=] [0].
-- Proof.
--  simpl in |- *; algebra.
-- Qed.
-- Hint Resolve zring_old_zero: algebra.

-- Lemma zring_old_diff : forall m n : nat, zring_old (m - n) [=] nring m[-]nring n.
-- Proof.
--  unfold zring_old in |- *.
--  intros m n.
--  apply proper_caseZ_diff_CS with (f := fun m0 n0 : nat => nring (R:=R) m0[-]nring n0).
--  clear m n.
--  intros m n p q H.
--  apply cg_cancel_lft with (nring n:R).
--  unfold cg_minus in |- *.
--  astepl (nring (R:=R) n[+] ( [--] (nring n) [+]nring m)).
--  astepl (nring (R:=R) n[+] [--] (nring n) [+]nring m).
--  astepl ([0][+]nring (R:=R) m).
--  astepl (nring (R:=R) m).
--  apply cg_cancel_rht with (nring q:R).
--  astepr (nring (R:=R) n[+] (nring p[+] [--] (nring q) [+]nring q)).
--  astepr (nring (R:=R) n[+] (nring p[+] ( [--] (nring q) [+]nring q))).
--  astepr (nring (R:=R) n[+] (nring p[+][0])).
--  astepr (nring (R:=R) n[+]nring p).
--  astepr (nring (R:=R) (n + p)).
--  astepl (nring (R:=R) (m + q)).
--  rewrite H.
--  algebra.
-- Qed.

-- Hint Resolve zring_old_diff.

-- Lemma zring_old_plus_nat : forall n : nat, zring_old n [=] nring n.
-- Proof.
--  intro n.
--  replace (n:Z) with (n - 0%nat)%Z.
--   astepl (nring (R:=R) n[-]nring 0).
--   simpl in |- *; algebra.
--  simpl in |- *; auto with zarith.
-- Qed.

-- Hint Resolve zring_old_plus_nat: algebra.

-- Lemma zring_old_inv_nat : forall n : nat, zring_old (- n) [=] [--] (nring n).
-- Proof.
--  intro n.
--  replace (- n)%Z with (0%nat - n)%Z.
--   astepl (nring 0[-]nring (R:=R) n).
--   simpl in |- *; algebra.
--  simpl in |- *; auto.
-- Qed.

-- Hint Resolve zring_old_inv_nat: algebra.

-- Lemma zring_old_plus : forall i j, zring_old (i + j) [=] zring_old i[+]zring_old j.
-- Proof.
--  intros i j.
--  pattern i in |- *.
--  apply diff_Z_ind.
--  intros m n.
--  pattern j in |- *.
--  apply diff_Z_ind.
--  intros m0 n0.
--  Hint Resolve zring_old_diff: algebra.
--  replace (m - n + (m0 - n0))%Z with ((m + m0)%nat - (n + n0)%nat)%Z.
--   astepl (nring (m + m0) [-]nring (n + n0):R).
--   astepl (nring m[+]nring m0[-] (nring n[+]nring n0):R).
--   astepr (nring m[-]nring n[+] (nring m0[-]nring n0):R).
--   unfold cg_minus in |- *.
--   astepl (nring m[+] (nring m0[+] [--] (nring n[+]nring n0)):R).
--   astepr (nring m[+] ( [--] (nring n) [+] (nring m0[+] [--] (nring n0))):R).
--   apply bin_op_wd_unfolded.
--    algebra.
--   astepl (nring m0[+] ( [--] (nring n) [+] [--] (nring n0)):R).
--   astepl (nring m0[+] [--] (nring n) [+] [--] (nring n0):R).
--   Step_final ( [--] (nring n) [+]nring m0[+] [--] (nring n0):R).
--  repeat rewrite Znat.inj_plus.
--  auto with zarith.
-- Qed.

-- Hint Resolve zring_old_plus: algebra.

-- Lemma zring_old_inv : forall i, zring_old (- i) [=] [--] (zring_old i).
-- Proof.
--  intro i.
--  pattern i in |- *.
--  apply diff_Z_ind.
--  intros m n.
--  replace (- (m - n))%Z with (n - m)%Z.
--   astepl (nring (R:=R) n[-]nring m).
--   astepr ( [--] (nring (R:=R) m[-]nring n)).
--   unfold cg_minus in |- *.
--   astepr ( [--] (nring m) [+] [--][--] (nring (R:=R) n)).
--   Step_final ( [--] (nring (R:=R) m) [+]nring n).
--  auto with zarith.
-- Qed.

-- Hint Resolve zring_old_inv: algebra.

-- Lemma zring_old_minus : forall i j, zring_old (i - j) [=] zring_old i[-]zring_old j.
-- Proof.
--  intros i j.
--  unfold cg_minus in |- *.
--  replace (i - j)%Z with (i + - j)%Z.
--   Step_final (zring_old i[+]zring_old (- j)).
--  auto.
-- Qed.

-- Hint Resolve zring_old_minus: algebra.

-- Lemma zring_old_mult : forall i j, zring_old (i * j) [=] zring_old i[*]zring_old j.
-- Proof.
--  intros i j.
--  pattern i in |- *.
--  apply diff_Z_ind.
--  intros m n.
--  pattern j in |- *.
--  apply diff_Z_ind.
--  intros m0 n0.
--  astepr ((nring (R:=R) m[-]nring n) [*] (nring m0[-]nring n0)).
--  replace ((m - n) * (m0 - n0))%Z with ((m * m0 + n * n0)%nat - (n * m0 + m * n0)%nat)%Z.
--   2: repeat rewrite Znat.inj_plus.
--   2: repeat rewrite Znat.inj_mult.
--   2: repeat rewrite BinInt.Zmult_minus_distr_r.
--   2: repeat rewrite CornBasics.Zmult_minus_distr_r.
--   2: auto with zarith.
--  astepl (nring (R:=R) (m * m0 + n * n0) [-]nring (n * m0 + m * n0)).
--  astepl (nring (R:=R) (m * m0) [+]nring (n * n0) [-] (nring (n * m0) [+]nring (m * n0))).
--  astepl (nring (R:=R) m[*]nring m0[+]nring n[*]nring n0[-] (nring n[*]nring m0[+]nring m[*]nring n0)).
--  astepr (nring (R:=R) m[*] (nring m0[-]nring n0) [-]nring n[*] (nring m0[-]nring n0)).
--  astepr (nring (R:=R) m[*]nring m0[-]nring m[*]nring n0[-] (nring n[*]nring m0[-]nring n[*]nring n0)).
--  unfold cg_minus in |- *.
--  astepr (nring (R:=R) m[*]nring m0[+] ( [--] (nring m[*]nring n0) [+]
--    [--] (nring n[*]nring m0[+] [--] (nring n[*]nring n0)))).
--  astepl (nring (R:=R) m[*]nring m0[+]
--    (nring n[*]nring n0[+] [--] (nring n[*]nring m0[+]nring m[*]nring n0))).
--  apply bin_op_wd_unfolded.
--   algebra.
--  astepl (nring (R:=R) n[*]nring n0[+] ( [--] (nring n[*]nring m0) [+] [--] (nring m[*]nring n0))).
--  astepr ( [--] (nring (R:=R) m[*]nring n0) [+]
--    ( [--] (nring n[*]nring m0) [+] [--][--] (nring n[*]nring n0))).
--  astepr ( [--] (nring (R:=R) m[*]nring n0) [+] ( [--] (nring n[*]nring m0) [+]nring n[*]nring n0)).
--  astepr ( [--] (nring (R:=R) m[*]nring n0) [+] (nring n[*]nring n0[+] [--] (nring n[*]nring m0))).
--  astepr ( [--] (nring (R:=R) m[*]nring n0) [+]nring n[*]nring n0[+] [--] (nring n[*]nring m0)).
--  astepr (nring (R:=R) n[*]nring n0[+] [--] (nring m[*]nring n0) [+] [--] (nring n[*]nring m0)).
--  Step_final (nring (R:=R) n[*]nring n0[+] ( [--] (nring m[*]nring n0) [+] [--] (nring n[*]nring m0))).
-- Qed.

-- Hint Resolve zring_old_mult: algebra.

-- Lemma zring_old_one : zring_old 1 [=] [1].
-- Proof.
--  simpl in |- *.
--  Step_final ([1][-][0]:R).
-- Qed.

-- Hint Resolve zring_old_one: algebra.

-- Lemma zring_old_inv_one : forall x, zring_old (-1) [*]x [=] [--]x.
-- Proof.
--  intro x.
--  simpl in |- *.
--  astepl ( [--] ([0][+][1]) [*]x).
--  astepl ( [--][1][*]x).
--  Step_final ( [--] ([1][*]x)).
-- Qed.

-- (*---------------- new def of zring. --------------------*)

-- (** The [zring] function can be defined directly.  This is done here.
-- *)

-- Fixpoint pring_aux (p : positive) (pow2 : R) {struct p} : R :=
--   match p with
--   | xH   => pow2
--   | xO p => pring_aux p (Two[*]pow2)
--   | xI p => pow2[+]pring_aux p (Two[*]pow2)
--   end.

-- Definition pring (p : positive) : R := pring_aux p [1].

-- Definition zring (z : Z) : R :=
--   match z with
--   | Z0     => [0]
--   | Zpos p => pring p
--   | Zneg p => [--] (pring p)
--   end.

-- Lemma pring_aux_lemma : forall p r r', r [=] r' -> pring_aux p r [=] pring_aux p r'.
-- Proof.
--  simple induction p; simpl in |- *; algebra.
-- Qed.

-- Lemma double_nring : forall n, Two[*]nring (R:=R) n [=] nring (R:=R) (n + n).
-- Proof.
--  intros.
--  Step_final (nring (R:=R) n[+]nring n).
-- Qed.

-- Hint Resolve pring_aux_lemma double_nring: algebra.

-- Lemma pring_aux_nring : forall p n, pring_aux p (nring n) [=] nring (Pmult_nat p n).
-- Proof.
--  simple induction p; simpl in |- *; intros.
--    astepl (nring n[+]pring_aux p0 (nring (n + n))).
--    Step_final (nring (R:=R) n[+]nring (R:=R) (Pmult_nat p0 (n + n))).
--   Step_final (pring_aux p0 (nring (n + n))).
--  algebra.
-- Qed.
-- Hint Resolve pring_aux_nring: algebra.

-- Lemma pring_convert : forall p, pring p [=] nring (nat_of_P p).
-- Proof.
--  intros; unfold pring, nat_of_P in |- *; simpl in |- *.
--  astepr (pring_aux p (nring 1)).
--  simpl in |- *; algebra.
-- Qed.
-- Hint Resolve pring_convert: algebra.

-- Lemma zring_zring_old : forall z : Z, zring z [=] zring_old z.
-- Proof.
--  simple induction z; simpl in |- *; intros.
--    algebra.
--   astepr (nring (R:=R) (nat_of_P p)).
--   algebra.
--  astepr ( [--] (nring (R:=R) (nat_of_P p))).
--  algebra.
-- Qed.

-- Hint Resolve zring_zring_old: algebra.

-- Lemma zring_zero : zring 0 [=] [0].
-- Proof.
--  simpl in |- *; algebra.
-- Qed.

-- Lemma zring_diff : forall m n : nat, zring (m - n) [=] nring m[-]nring n.
-- Proof.
--  intros; Step_final (zring_old (m - n)).
-- Qed.

-- Lemma zring_plus_nat : forall n : nat, zring n [=] nring n.
-- Proof.
--  intro n; Step_final (zring_old n).
-- Qed.

-- Lemma zring_inv_nat : forall n : nat, zring (- n) [=] [--] (nring n).
-- Proof.
--  intro n; Step_final (zring_old (- n)).
-- Qed.

-- Lemma zring_plus : forall i j, zring (i + j) [=] zring i[+]zring j.
-- Proof.
--  intros.
--  astepl (zring_old (i + j)).
--  Step_final (zring_old i[+]zring_old j).
-- Qed.

-- Lemma zring_inv : forall i, zring (- i) [=] [--] (zring i).
-- Proof.
--  intro i.
--  astepl (zring_old (- i)).
--  Step_final ( [--] (zring_old i)).
-- Qed.

-- Lemma zring_minus : forall i j, zring (i - j) [=] zring i[-]zring j.
-- Proof.
--  intros i j.
--  astepl (zring_old (i - j)).
--  Step_final (zring_old i[-]zring_old j).
-- Qed.

-- Lemma zring_mult : forall i j, zring (i * j) [=] zring i[*]zring j.
-- Proof.
--  intros i j.
--  astepl (zring_old (i * j)).
--  Step_final (zring_old i[*]zring_old j).
-- Qed.

-- Lemma zring_one : zring 1 [=] [1].
-- Proof.
--  simpl in |- *.
--  unfold pring in |- *.
--  algebra.
-- Qed.

-- Lemma zring_inv_one : forall x, zring (-1) [*]x [=] [--]x.
-- Proof.
--  intro x.
--  simpl in |- *.
--  unfold pring in |- *.
--  simpl in |- *.
--  Step_final ( [--] ([1][*]x)).
-- Qed.

-- End int_injection.

-- Arguments zring [R].

-- #[global]
-- Hint Resolve pring_convert zring_zero zring_diff zring_plus_nat zring_inv_nat
--   zring_plus zring_inv zring_minus zring_mult zring_one zring_inv_one:
--   algebra.


-- Section Ring_sums.

-- (**
-- ** Ring sums
-- %\begin{convention}% Let [R] be a ring.
-- %\end{convention}%
-- *)
-- Variable R : CRing.

-- (**
-- *** Infinite Ring sums
-- *)
-- Section infinite_ring_sums.

-- Fixpoint Sum_upto (f : nat -> R) (n : nat) {struct n} : R :=
--   match n with
--   | O   => [0]
--   | S x => f x[+]Sum_upto f x
--   end.

-- Lemma sum_upto_O : forall f : nat -> R, Sum_upto f 0 [=] [0].
-- Proof.
--  algebra.
-- Qed.

-- Definition Sum_from_upto f m n : R := Sum_upto f n[-]Sum_upto f m.

-- (**
-- Here's an alternative def of [Sum_from_upto], with a lemma that
-- it's equivalent to the original.
-- *)

-- Definition seq_from (f : nat -> R) (n i : nat) : R := f (n + i).

-- Definition Sum_from_upto_alt f m n : R := Sum_upto (seq_from f m) (n - m).

-- End infinite_ring_sums.

-- Section ring_sums_over_lists.
-- (**
-- *** Ring Sums over Lists
-- *)

-- Fixpoint RList_Mem (l : list R) (n : nat) {struct n} : R :=
--   match l, n with
--   | nil,      _   => [0]
--   | cons a _, O   => a
--   | cons _ k, S y => RList_Mem k y
--   end.

-- Fixpoint List_Sum_upto (l : list R) (n : nat) {struct n} : R :=
--   match n with
--   | O   => [0]
--   | S x => RList_Mem l x[+]List_Sum_upto l x
--   end.

-- Lemma list_sum_upto_O : forall l : list R, List_Sum_upto l 0 [=] [0].
-- Proof.
--  algebra.
-- Qed.

-- Definition List_Sum_from_upto l m n := List_Sum_upto l n[-]List_Sum_upto l m.

-- End ring_sums_over_lists.
-- End Ring_sums.

-- (**
-- ** Distribution properties
-- %\begin{convention}%
-- Let [R] be a ring.
-- %\end{convention}%
-- *)
-- Section Dist_properties.
-- Variable R : CRing.

-- Lemma dist_1b : forall x y z : R, (x[+]y) [*]z [=] x[*]z[+]y[*]z.
-- Proof.
--  intros x y z.
--  astepl (z[*] (x[+]y)).
--  Step_final (z[*]x[+]z[*]y).
-- Qed.
-- Hint Resolve dist_1b: algebra.

-- Lemma dist_2a : forall x y z : R, z[*] (x[-]y) [=] z[*]x[-]z[*]y.
-- Proof.
--  intros x y z.
--  astepl (z[*] (x[+] [--]y)).
--  astepl (z[*]x[+]z[*] [--]y).
--  Step_final (z[*]x[+] [--] (z[*]y)).
-- Qed.
-- Hint Resolve dist_2a: algebra.

-- Lemma dist_2b : forall x y z : R, (x[-]y) [*]z [=] x[*]z[-]y[*]z.
-- Proof.
--  intros x y z.
--  astepl (z[*] (x[-]y)).
--  Step_final (z[*]x[-]z[*]y).
-- Qed.
-- Hint Resolve dist_2b: algebra.

-- Lemma mult_distr_sum0_lft :  forall (f : nat -> R) x n,
--  Sum0 n (fun i => x[*]f i) [=] x[*]Sum0 n f.
-- Proof.
--  intros f x n.
--  induction  n as [| n Hrecn].
--   simpl in |- *; algebra.
--  simpl in |- *.
--  Step_final (x[*]Sum0 n f[+]x[*]f n).
-- Qed.
-- Hint Resolve mult_distr_sum0_lft.

-- Lemma mult_distr_sum_lft : forall (f : nat -> R) x m n,
--  Sum m n (fun i => x[*]f i) [=] x[*]Sum m n f.
-- Proof.
--  intros f x m n.
--  unfold Sum in |- *.
--  unfold Sum1 in |- *.
--  Step_final (x[*]Sum0 (S n) f[-]x[*]Sum0 m f).
-- Qed.
-- Hint Resolve mult_distr_sum_lft: algebra.

-- Lemma mult_distr_sum_rht : forall (f : nat -> R) x m n,
--  Sum m n (fun i => f i[*]x) [=] Sum m n f[*]x.
-- Proof.
--  intros f x m n.
--  astepl (Sum m n (fun i : nat => x[*]f i)).
--  Step_final (x[*]Sum m n f).
-- Qed.

-- Lemma sumx_const : forall n (x : R), Sumx (fun i (_ : i < n) => x) [=] nring n[*]x.
-- Proof.
--  intros n x; induction  n as [| n Hrecn].
--   simpl in |- *; algebra.
--  simpl in |- *.
--  astepr (nring n[*]x[+][1][*]x).
--  Step_final (nring n[*]x[+]x).
-- Qed.

-- End Dist_properties.

-- #[global]
-- Hint Resolve dist_1b dist_2a dist_2b mult_distr_sum_lft mult_distr_sum_rht
--   sumx_const: algebra.


-- (**
-- ** Properties of exponentiation (with the exponent in [nat])
-- %\begin{convention}%
-- Let [R] be a ring.
-- %\end{convention}%
-- *)
-- Section NExp_properties.
-- Variable R : CRing.

-- Lemma nexp_wd : forall (x y : R) n, x [=] y -> x[^]n [=] y[^]n.
-- Proof.
--  algebra.
-- Qed.

-- Lemma nexp_strext : forall (x y : R) n, x[^]n [#] y[^]n -> x [#] y.
-- Proof.
--  intros x y n H.
--  exact (un_op_strext_unfolded _ _ _ _ H).
-- Qed.

-- Lemma nexp_Sn : forall (x : R) n, x[*]x[^]n [=] x[^]S n.
-- Proof.
--  intros x n.
--  Step_final (x[^]n[*]x).
-- Qed.

-- Hint Resolve nexp_wd nexp_Sn: algebra.

-- Lemma nexp_plus : forall (x : R) m n, x[^]m[*]x[^]n [=] x[^] (m + n).
-- Proof.
--  intros x m n.
--  induction  m as [| m Hrecm].
--   rewrite plus_O_n.
--   Step_final ([1][*]x[^]n).
--  rewrite plus_Sn_m.
--  astepl (x[^]m[*]x[*]x[^]n).
--  astepl (x[*]x[^]m[*]x[^]n).
--  astepl (x[*] (x[^]m[*]x[^]n)).
--  Step_final (x[*]x[^] (m + n)).
-- Qed.
-- Hint Resolve nexp_plus: algebra.

-- Lemma one_nexp : forall n : nat, ([1]:R) [^]n [=] [1].
-- Proof.
--  intro n.
--  induction  n as [| n Hrecn].
--   algebra.
--  astepl (([1]:R) [*][1][^]n).
--  Step_final (([1]:R) [*][1]).
-- Qed.
-- Hint Resolve one_nexp: algebra.

-- Lemma mult_nexp : forall (x y : R) n, (x[*]y) [^]n [=] x[^]n[*]y[^]n.
-- Proof.
--  intros x y n.
--  induction  n as [| n Hrecn].
--   astepl ([1]:R).
--   Step_final (([1]:R) [*][1]).
--  astepl (x[*]y[*] (x[*]y) [^]n).
--  astepl (x[*]y[*] (x[^]n[*]y[^]n)).
--  astepl (x[*] (y[*] (x[^]n[*]y[^]n))).
--  astepl (x[*] (y[*]x[^]n[*]y[^]n)).
--  astepl (x[*] (x[^]n[*]y[*]y[^]n)).
--  astepl (x[*] (x[^]n[*] (y[*]y[^]n))).
--  Step_final (x[*]x[^]n[*] (y[*]y[^]n)).
-- Qed.
-- Hint Resolve mult_nexp: algebra.

-- Lemma nexp_mult : forall (x : R) m n, (x[^]m) [^]n [=] x[^] (m * n).
-- Proof.
--  intros x m n.
--  induction  m as [| m Hrecm].
--   simpl in |- *.
--   Step_final (([1]:R) [^]n).
--  astepl ((x[*]x[^]m) [^]n).
--  astepl (x[^]n[*] (x[^]m) [^]n).
--  astepl (x[^]n[*]x[^] (m * n)).
--  astepl (x[^] (n + m * n)).
--  replace (n + m * n) with (S m * n); algebra.
-- Qed.
-- Hint Resolve nexp_mult: algebra.

-- Lemma zero_nexp : forall n, 0 < n -> ([0]:R) [^]n [=] [0].
-- Proof.
--  intros n H.
--  induction  n as [| n Hrecn].
--   inversion H.
--  Step_final (([0]:R) [*][0][^]n).
-- Qed.
-- Hint Resolve zero_nexp: algebra.

-- Lemma inv_nexp_even : forall (x : R) n, Nat.Even n -> [--]x[^]n [=] x[^]n.
-- Proof.
--  intros x n [k H].
--  replace (2 * k) with (k + k) in H by lia; rewrite H.
--  astepl ( [--]x[^](k)[*] [--]x[^](k)).
--  astepl (( [--]x[*] [--]x) [^](k)).
--  astepl ((x[*]x) [^](k)).
--  Step_final (x[^](k)[*]x[^](k)).
-- Qed.
-- Hint Resolve inv_nexp_even: algebra.

-- Lemma inv_nexp_two : forall x : R, [--]x[^]2 [=] x[^]2.
-- Proof.
--  intro x.
--  now apply inv_nexp_even; exists 1.
-- Qed.
-- Hint Resolve inv_nexp_two: algebra.

-- Lemma inv_nexp_odd : forall (x : R) n, Nat.Odd n -> [--]x[^]n [=] [--] (x[^]n).
-- Proof.
--  intros x [| n] H; [apply Nat.odd_spec in H; discriminate H |].
--  apply Nat.Odd_succ in H.
--  astepl ( [--]x[*] [--]x[^]n).
--  astepl ( [--]x[*]x[^]n).
--  Step_final ( [--] (x[*]x[^]n)).
-- Qed.
-- Hint Resolve inv_nexp_odd: algebra.

-- Lemma nexp_one : forall x : R, x[^]1 [=] x.
-- Proof.
--  intro x.
--  Step_final ([1][*]x).
-- Qed.
-- Hint Resolve nexp_one: algebra.

-- Lemma nexp_two : forall x : R, x[^]2 [=] x[*]x.
-- Proof.
--  intro x.
--  replace 2 with (1 + 1).
--   Step_final (x[^]1[*]x[^]1).
--  auto with arith.
-- Qed.
-- Hint Resolve nexp_two: algebra.

-- Lemma inv_one_even_nexp : forall n : nat, Nat.Even n -> [--][1][^]n [=] ([1]:R).
-- Proof.
--  intros n H.
--  Step_final (([1]:R) [^]n).
-- Qed.
-- Hint Resolve inv_one_even_nexp: algebra.

-- Lemma inv_one_odd_nexp : forall n : nat, Nat.Odd n -> [--][1][^]n [=] [--] ([1]:R).
-- Proof.
--  intros n H.
--  Step_final ( [--] (([1]:R) [^]n)).
-- Qed.
-- Hint Resolve inv_one_odd_nexp: algebra.

-- Lemma square_plus : forall x y : R, (x[+]y) [^]2 [=] x[^]2[+]y[^]2[+]Two[*]x[*]y.
-- Proof.
--  intros x y.
--  astepl ((x[+]y) [*] (x[+]y)).
--  astepl (x[*] (x[+]y) [+]y[*] (x[+]y)).
--  astepl (x[*]x[+]x[*]y[+] (y[*]x[+]y[*]y)).
--  astepl (x[^]2[+]x[*]y[+] (x[*]y[+]y[^]2)).
--  astepl (x[^]2[+]x[*]y[+]x[*]y[+]y[^]2).
--  astepl (x[^]2[+] (x[*]y[+]x[*]y) [+]y[^]2).
--  astepl (x[^]2[+]Two[*] (x[*]y) [+]y[^]2).
--  astepl (x[^]2[+]Two[*]x[*]y[+]y[^]2).
--  astepl (x[^]2[+] (Two[*]x[*]y[+]y[^]2)).
--  Step_final (x[^]2[+] (y[^]2[+]Two[*]x[*]y)).
-- Qed.

-- Lemma square_minus : forall x y : R, (x[-]y) [^]2 [=] x[^]2[+]y[^]2[-]Two[*]x[*]y.
-- Proof.
--  intros x y.
--  unfold cg_minus in |- *.
--  eapply eq_transitive_unfolded.
--   apply square_plus.
--  algebra.
-- Qed.

-- Lemma nexp_funny : forall x y : R, (x[+]y) [*] (x[-]y) [=] x[^]2[-]y[^]2.
-- Proof.
--  intros x y.
--  astepl (x[*] (x[-]y) [+]y[*] (x[-]y)).
--  astepl (x[*]x[-]x[*]y[+] (y[*]x[-]y[*]y)).
--  astepl (x[*]x[+] [--] (x[*]y) [+] (y[*]x[+] [--] (y[*]y))).
--  astepl (x[*]x[+] [--] (x[*]y) [+]y[*]x[+] [--] (y[*]y)).
--  astepl (x[*]x[+] ( [--] (x[*]y) [+]y[*]x) [+] [--] (y[*]y)).
--  astepl (x[*]x[+] ( [--] (x[*]y) [+]x[*]y) [+] [--] (y[*]y)).
--  astepl (x[*]x[+][0][+] [--] (y[*]y)).
--  astepl (x[*]x[+] [--] (y[*]y)).
--  Step_final (x[*]x[-]y[*]y).
-- Qed.
-- Hint Resolve nexp_funny: algebra.

-- Lemma nexp_funny' : forall x y : R, (x[-]y) [*] (x[+]y) [=] x[^]2[-]y[^]2.
-- Proof.
--  intros x y.
--  Step_final ((x[+]y) [*] (x[-]y)).
-- Qed.
-- Hint Resolve nexp_funny': algebra.

-- End NExp_properties.

-- Add Parametric Morphism c n : (nexp c n) with signature (@cs_eq (cr_crr c)) ==> (@cs_eq c) as nexp_morph_wd.
-- Proof.
--  intros. apply: nexp_wd. assumption. Qed.

-- #[global]
-- Hint Resolve nexp_wd nexp_Sn nexp_plus one_nexp mult_nexp nexp_mult zero_nexp
--   inv_nexp_even inv_nexp_two inv_nexp_odd nexp_one nexp_two nexp_funny
--   inv_one_even_nexp inv_one_odd_nexp nexp_funny' one_nexp square_plus
--   square_minus: algebra.

-- Section CRing_Ops.

-- (**
-- ** Functional Operations

-- Now for partial functions.

-- %\begin{convention}%
-- Let [R] be a ring and let [F,G:(PartFunct R)] with predicates
-- respectively [P] and [Q].
-- %\end{convention}%
-- *)

-- Variable R : CRing.

-- Variables F G : PartFunct R.

-- (* begin hide *)
-- Let P := Dom F.
-- Let Q := Dom G.
-- (* end hide *)

-- Section Part_Function_Mult.

-- Lemma part_function_mult_strext : forall x y (Hx : Conj P Q x) (Hy : Conj P Q y),
--  F x (Prj1 Hx) [*]G x (Prj2 Hx) [#] F y (Prj1 Hy) [*]G y (Prj2 Hy) -> x [#] y.
-- Proof.
--  intros x y Hx Hy H.
--  elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intro H1; exact (pfstrx _ _ _ _ _ _ H1).
-- Qed.

-- Definition Fmult := Build_PartFunct R _ (conj_wd (dom_wd _ F) (dom_wd _ G))
--  (fun x Hx => F x (Prj1 Hx) [*]G x (Prj2 Hx)) part_function_mult_strext.

-- End Part_Function_Mult.

-- Section Part_Function_Nth_Power.

-- Variable n : nat.

-- Lemma part_function_nth_strext : forall x y Hx Hy, F x Hx[^]n [#] F y Hy[^]n -> x [#] y.
-- Proof.
--  intros x y Hx Hy H.
--  apply pfstrx with F Hx Hy.
--  apply nexp_strext with n; assumption.
-- Qed.

-- Definition Fnth := Build_PartFunct R _ (dom_wd R F)
--  (fun x Hx => F x Hx[^]n) part_function_nth_strext.

-- End Part_Function_Nth_Power.

-- (**
-- %\begin{convention}% Let [R':R->CProp].
-- %\end{convention}%
-- *)

-- Variable R':R -> CProp.

-- Lemma included_FMult : included R' P -> included R' Q -> included R' (Dom Fmult).
-- Proof.
--  intros; simpl in |- *; apply included_conj; assumption.
-- Qed.

-- Lemma included_FMult' : included R' (Dom Fmult) -> included R' P.
-- Proof.
--  intro H; simpl in H; eapply included_conj_lft; apply H.
-- Qed.

-- Lemma included_FMult'' : included R' (Dom Fmult) -> included R' Q.
-- Proof.
--  intro H; simpl in H; eapply included_conj_rht; apply H.
-- Qed.

-- Variable n:nat.

-- Lemma included_FNth : included R' P -> forall n, included R' (Dom (Fnth n)).
-- Proof.
--  auto.
-- Qed.

-- Lemma included_FNth' : forall n, included R' (Dom (Fnth n)) -> included R' (Dom F).
-- Proof.
--  auto.
-- Qed.

-- End CRing_Ops.

-- Definition Fscalmult (R:CRing) alpha F := Fmult R [-C-]alpha F.

-- Arguments Fmult [R].
-- Infix "{*}" := Fmult (at level 40, left associativity).

-- Arguments Fscalmult [R].
-- Infix "{**}" := Fscalmult (at level 40, left associativity).

-- Arguments Fnth [R].
-- Infix "{^}" := Fnth (at level 30, right associativity).

-- Section ScalarMultiplication.

-- Variable R : CRing.

-- Variable F : PartFunct R.

-- (* begin hide *)
-- Let P := Dom F.
-- (* end hide *)

-- Variable R':R -> CProp.

-- Lemma included_FScalMult : included R' P -> forall c, included R' (Dom (c{**}F)).
-- Proof.
--  intros; simpl in |- *; apply included_conj.
--   red in |- *; intros; auto.
--  assumption.
-- Qed.

-- Lemma included_FScalMult' : forall c, included R' (Dom (c{**}F)) -> included R' P.
-- Proof.
--  intros c H; simpl in H; eapply included_conj_rht; apply H.
-- Qed.

-- End ScalarMultiplication.

-- Section cr_Product.

--   Context {R: CRing}.

--   Definition cr_Product: list R -> R := @cm_Sum (Build_multCAbMonoid R).

--   Lemma cr_Product_ones (l: list R): (forall x, In x l -> x [=] [1]) ->
--     cr_Product l [=] [1].
--   Proof. apply (@cm_Sum_units (Build_multCMonoid R)). Qed.

--   Lemma cr_Product_0 (z: R) (zE: z [=] [0]): forall l, In z l -> cr_Product l [=] [0].
--   Proof with auto.
--    induction l.
--     simpl.
--     intuition.
--    intros [?|?]; simpl.
--     subst. rewrite zE.
--     apply cring_mult_zero_op.
--    rewrite IHl...
--    apply cring_mult_zero.
--   Qed.

--   Global Instance cr_Product_Proper:
--     Proper (SetoidPermutation (@st_eq R) ==> @st_eq R) cr_Product.
--   Proof.
--    apply ( @cm_Sum_AbMonoid_Proper (Build_multCAbMonoid R)).
--   Qed.

--   (* For convenience, we also make a weaker instance for Permutation: *)

--   Global Instance: Proper (@Permutation R ==> @st_eq R) cr_Product.
--   Proof.
--    repeat intro.
--    apply cr_Product_Proper.
--    apply SetoidPermutation_from_Permutation.
--     apply _.
--    assumption.
--   Qed.

-- End cr_Product.


-- #[global]
-- Hint Resolve included_FMult included_FScalMult included_FNth : included.

-- #[global]
-- Hint Immediate included_FMult' included_FMult'' included_FScalMult'
--     included_FNth' : included.
