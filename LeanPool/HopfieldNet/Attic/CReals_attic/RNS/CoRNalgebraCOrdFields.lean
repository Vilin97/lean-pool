/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib

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

-- (** printing [<] %\ensuremath<% #&lt;# *)
-- (** printing [<=] %\ensuremath{\leq}% #&le;# *)
-- (** printing [>] %\ensuremath>% #&gt;# *)
-- (** printing [1]NZ %\ensuremath{\mathbf1}% #1# *)
-- (** printing TwoNZ %\ensuremath{\mathbf2}% #2# *)
-- (** printing ThreeNZ %\ensuremath{\mathbf3}% #3# *)
-- (** printing FourNZ %\ensuremath{\mathbf4}% #4# *)
-- (** printing SixNZ %\ensuremath{\mathbf6}% #6# *)
-- (** printing EightNZ %\ensuremath{\mathbf8}% #8# *)
-- (** printing NineNZ %\ensuremath{\mathbf9}% #9# *)
-- (** printing TwelveNZ %\ensuremath{\mathbf{12}}% #12# *)
-- (** printing SixteenNZ %\ensuremath{\mathbf{16}}% #16# *)
-- (** printing EighteenNZ %\ensuremath{\mathbf{18}}% #18# *)
-- (** printing TwentyFourNZ %\ensuremath{\mathbf{24}}% #24# *)
-- (** printing FortyEightNZ %\ensuremath{\mathbf{48}}% #48# *)

-- Require Export CoRN.tactics.FieldReflection.
-- Require Export CoRN.tactics.Rational.
-- Require Export CoRN.algebra.CSetoids.
-- From Coq Require Import Lia.

-- (* ORDERED FIELDS *)

-- (**
-- * Ordered Fields
-- ** Definition of the notion of ordered field
-- *)
--variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]

-- (* Begin_SpecReals *)

-- Record strictorder (A : Type)(R : A -> A -> CProp) : CProp :=
--  {so_trans : Ctransitive R;
--   so_asym  : antisymmetric R}.

structure StrictOrder (A : Type) (R : A → A → Prop) : Prop where
  so_trans : ∀ {x y z : A}, R x y → R y z → R x z
  so_asym : ∀ {x y : A}, R x y → ¬R y x

-- Record strictorder (A : Type)(R : A -> A -> CProp) : CProp :=
--  {so_trans : Ctransitive R;
--   so_asym  : antisymmetric R}.

-- Arguments strictorder [A].
-- Arguments Build_strictorder [A R].
-- Arguments so_trans [A R].
-- Arguments so_asym [A R].

-- Record is_COrdField (F : CField)
--   (less : CCSetoid_relation F) (leEq : Relation F)
--   (greater : CCSetoid_relation F) (grEq : Relation F) : CProp :=
--   {ax_less_strorder  : strictorder less;
--    ax_plus_resp_less : forall x y, less x y -> forall z, less (x[+]z) (y[+]z);
--    ax_mult_resp_pos  : forall x y, less [0] x -> less [0] y -> less [0] (x[*]y);
--    ax_less_conf_ap   : forall x y, Iff (x [#] y) (less x y or less y x);
--    def_leEq : forall x y, (leEq x y) <-> (Not (less y x));
--    def_greater : forall x y, Iff (greater x y) (less y x);
--    def_grEq : forall x y, (grEq x y) <-> (leEq y x)}.

structure IsOrderedField (F : Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  (less : F → F → Prop) (leEq : F → F → Prop)
  (greater : F → F → Prop) (grEq : F → F → Prop) : Prop where
  ax_less_strorder : StrictOrder F less
  ax_plus_resp_less : ∀ x y z : F, less x y → less (x + z) (y + z)
  ax_mult_resp_pos : ∀ x y : F, less 0 x → less 0 y → less 0 (x * y)
  ax_less_conf_ap : ∀ x y : F, (x ≠ y) ↔ (less x y ∨ less y x)
  def_leEq : ∀ x y : F, leEq x y ↔ ¬less y x
  def_greater : ∀ x y : F, greater x y ↔ less y x
  def_grEq : ∀ x y : F, grEq x y ↔ leEq y x

-- Record COrdField : Type :=
--   {cof_crr   :> CField;
--    cof_less  :  CCSetoid_relation cof_crr;
--    cof_leEq :  cof_crr -> cof_crr -> Prop;
--    cof_greater :  CCSetoid_relation cof_crr;
--    cof_grEq : cof_crr -> cof_crr -> Prop;
--    cof_proof :  is_COrdField cof_crr cof_less cof_leEq cof_greater cof_grEq}.

structure COrdField where
  cof_crr : Type
  [field_inst : Field cof_crr]
  [order_inst : LinearOrder cof_crr]
  [strict_order_inst : IsStrictOrderedRing cof_crr]
  cof_less : cof_crr → cof_crr → Prop
  cof_leEq : cof_crr → cof_crr → Prop
  cof_greater : cof_crr → cof_crr → Prop
  cof_grEq : cof_crr → cof_crr → Prop
  cof_proof : IsOrderedField cof_crr cof_less cof_leEq cof_greater cof_grEq

-- (**
-- %\begin{nameconvention}%
-- In the names of lemmas, [ [<] ] is written as [less] and "[[0] [<] ]"
-- is written as [pos].
-- %\end{nameconvention}%
-- *)

-- Arguments cof_less {c}.
-- Infix "[<]" := cof_less (at level 70, no associativity).

-- Arguments cof_greater {c}.
-- Infix "[>]" := cof_greater (at level 70, no associativity).

-- Arguments cof_leEq {c}.
-- Infix "[<=]" := cof_leEq (at level 70, no associativity).

-- Arguments cof_grEq {c}.
-- Infix "[>=]" := cof_grEq (at level 70, no associativity).

-- Notations for ordered field relations
notation:70 x:70 " [<] " y:71 => COrdField.cof_less x y
notation:70 x:70 " [>] " y:71 => COrdField.cof_greater x y
notation:70 x:70 " [<=] " y:71 => COrdField.cof_leEq x y
notation:70 x:70 " [>=] " y:71 => COrdField.cof_grEq x y

-- Definition default_greater (X:CField) (lt:CCSetoid_relation X) : CCSetoid_relation X.
-- Proof.
--  intros.
--  exists (fun x y => lt y x).
--  destruct lt.
--  unfold Crel_strext in *.
--  simpl.
--  intros.
--  pose (Ccsr_strext _ y2 _ x2 X0).
--  tauto.
-- Defined.

def default_greater (X : Type) [Field X] (lt : X → X → Prop) : X → X → Prop :=
  fun x y => lt y x

def default_leEq (X : Type) [Field X] (lt : X → X → Prop) : X → X → Prop :=
  fun x y => ¬(lt y x)

-- Definition default_grEq (X:CField) (le:Relation X) : Relation X :=
-- (fun x y => (le y x)).

def default_grEq (X : Type) [Field X] (le : X → X → Prop) : X → X → Prop :=
  fun x y => le y x

-- (**
-- %\begin{nameconvention}%
-- In the names of lemmas, [ [<=] ] is written as [leEq] and
-- [[0] [<=] ] is written as [nonneg].
-- %\end{nameconvention}%
-- *)

-- (**
-- ** Properties of [[<=]] and nonnegative elements
-- In the names of lemmas, [[<=]] is written as [leEq] and
-- [[0] [<=]] is written as [nonneg].
-- *)

-- Section COrdField_axioms.

-- (**
-- ** Ordered field axioms
-- %\begin{convention}%
-- Let [F] be a field.
-- %\end{convention}%
-- *)

-- (**
-- ** Ordered field axioms
-- %\begin{convention}%
-- Let [F] be a field.
-- %\end{convention}%
-- *)

--variable {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

-- Variable F : COrdField.

-- Lemma COrdField_is_COrdField : is_COrdField F cof_less (@cof_leEq F) cof_greater (@cof_grEq F).
-- Proof.
--  elim F; auto.
-- Qed.

-- Lemma less_strorder : strictorder (cof_less (c:=F)).
-- Proof.
--  elim COrdField_is_COrdField; auto.
-- Qed.

lemma less_strorder (F : COrdField) : StrictOrder F.cof_crr F.cof_less :=
  @IsOrderedField.ax_less_strorder F.cof_crr F.field_inst F.order_inst F.strict_order_inst F.cof_less F.cof_leEq F.cof_greater F.cof_grEq F.cof_proof

-- Lemma less_transitive_unfolded : forall x y z : F, x [<] y -> y [<] z -> x [<] z.
-- Proof.
--  elim less_strorder; auto.
-- Qed.

lemma less_transitive_unfolded (F : COrdField) : ∀ x y z : F.cof_crr, F.cof_less x y → F.cof_less y z → F.cof_less x z :=
  fun x y z h1 h2 => (less_strorder F).so_trans h1 h2

-- Lemma less_antisymmetric_unfolded : forall x y : F, x [<] y -> Not (y [<] x).
-- Proof.
--  elim less_strorder.
--  intros H1 H2 x y H.
--  intro H0.
--  elim (H2 _ _ H).
--  assumption.
-- Qed.

lemma less_antisymmetric_unfolded (F : COrdField) : ∀ x y : F.cof_crr, F.cof_less x y → ¬F.cof_less y x :=
  fun x y h1 h2 => (less_strorder F).so_asym h1 h2

-- Lemma less_irreflexive : irreflexive (cof_less (c:=F)).
-- Proof.
--  red in |- *.
--  intro x; intro H.
--  elim (less_antisymmetric_unfolded _ _ H H).
-- Qed.

lemma less_irreflexive (F : COrdField) : ∀ x : F.cof_crr, ¬F.cof_less x x :=
  fun x h => less_antisymmetric_unfolded F x x h h

-- Lemma less_irreflexive_unfolded : forall x : F, Not (x [<] x).
-- Proof less_irreflexive.

lemma less_irreflexive_unfolded (F : COrdField) : ∀ x : F.cof_crr, ¬F.cof_less x x :=
  less_irreflexive F

-- Lemma plus_resp_less_rht : forall x y z : F, x [<] y -> x[+]z [<] y[+]z.
-- Proof.
--  elim COrdField_is_COrdField; auto.
-- Qed.
variable (F : COrdField)

lemma plus_resp_less_rht [Field F.cof_crr] : ∀ x y z : F.cof_crr, F.cof_less x y → F.cof_less (x + z) (y + z) :=
  sorry

-- Lemma mult_resp_pos : forall x y : F, [0] [<] x -> [0] [<] y -> [0] [<] x[*]y.
-- Proof.
--  elim COrdField_is_COrdField; auto.
-- Qed.

instance : OfNat F.cof_crr 0 := sorry
instance : HMul F.cof_crr F.cof_crr F.cof_crr := sorry

lemma mult_resp_pos : ∀ x y : F.cof_crr, F.cof_less 0 x → F.cof_less 0 y → F.cof_less 0 (x * y) :=
  sorry

-- Lemma less_conf_ap : forall x y : F, Iff (x [#] y) (x [<] y or y [<] x).
-- Proof.
--  elim COrdField_is_COrdField; auto.
-- Qed.

lemma less_conf_ap : ∀ x y : F.cof_crr, (x ≠ y) ↔ (F.cof_less x y ∨ F.cof_less y x) :=
  @IsOrderedField.ax_less_conf_ap F.cof_crr F.field_inst F.order_inst F.strict_order_inst F.cof_less F.cof_leEq F.cof_greater F.cof_grEq F.cof_proof

-- Lemma leEq_def : forall x y : F, (x [<=] y) <-> (Not (y [<] x)).
-- Proof.
--  elim COrdField_is_COrdField; auto.
-- Qed.

lemma leEq_def : ∀ x y : F.cof_crr, F.cof_leEq x y ↔ ¬F.cof_less y x :=
  @IsOrderedField.def_leEq F.cof_crr F.field_inst F.order_inst F.strict_order_inst F.cof_less F.cof_leEq F.cof_greater F.cof_grEq F.cof_proof

-- Lemma greater_def : forall x y : F, Iff (x [>] y) (y [<] x).
-- Proof.
--  elim COrdField_is_COrdField; auto.
-- Qed.

lemma greater_def : ∀ x y : F.cof_crr, F.cof_greater x y ↔ F.cof_less y x :=
  @IsOrderedField.def_greater F.cof_crr F.field_inst F.order_inst F.strict_order_inst F.cof_less F.cof_leEq F.cof_greater F.cof_grEq F.cof_proof

-- Lemma grEq_def : forall x y : F, (x [>=] y) <-> (y [<=] x).
-- Proof.
--  elim COrdField_is_COrdField; auto.
-- Qed.

lemma grEq_def : ∀ x y : F.cof_crr, F.cof_grEq x y ↔ F.cof_leEq y x :=
  @IsOrderedField.def_grEq F.cof_crr F.field_inst F.order_inst F.strict_order_inst F.cof_less F.cof_leEq F.cof_greater F.cof_grEq F.cof_proof

-- Lemma less_wdr : forall x y z : F, x [<] y -> y [=] z -> x [<] z.
-- Proof Ccsr_wdr F cof_less.

lemma less_wdr : ∀ x y z : F.cof_crr, F.cof_less x y → y = z → F.cof_less x z :=
  fun x y z h_lt h_eq => by rw [←h_eq]; exact h_lt

-- Lemma less_wdl : forall x y z : F, x [<] y -> x [=] z -> z [<] y.
-- Proof Ccsr_wdl F cof_less.

lemma less_wdl : ∀ x y z : F.cof_crr, F.cof_less x y → x = z → F.cof_less z y :=
  fun x y z h_lt h_eq => by rw [h_eq] at h_lt; exact h_lt

-- End COrdField_axioms.

-- Declare Left Step less_wdl.
-- Declare Right Step less_wdr.

-- Section OrdField_basics.

-- (**
-- ** Basics
-- *)

-- (**
-- %\begin{convention}%
-- Let in the rest of this section (and all subsections)
-- [R] be an ordered field
-- %\end{convention}%
-- *)
-- Variable R : COrdField.


-- Lemma less_imp_ap : forall x y : R, x [<] y -> x [#] y.
-- Proof.
--  intros x y H.
--  elim (less_conf_ap _ x y); intros.
--  apply b. left. auto.
-- Qed.

-- Lemma Greater_imp_ap : forall x y : R, y [<] x -> x [#] y.
-- Proof.
--  intros x y H.
--  elim (less_conf_ap _ x y); intros.
--  apply b. right. auto.
-- Qed.

-- Lemma ap_imp_less : forall x y : R, x [#] y -> x [<] y or y [<] x.
-- Proof.
--  intros x y.
--  elim (less_conf_ap _ x y); auto.
-- Qed.

-- (**
-- Now properties which can be derived.
-- *)

-- Lemma less_cotransitive : cotransitive (cof_less (c:=R)).
-- Proof.
--  red in |- *.
--  intros x y H z.
--  generalize (less_imp_ap _ _ H); intro H0.
--  elim (ap_cotransitive_unfolded _ _ _ H0 z); intro H1.
--   elim (ap_imp_less _ _ H1).
--    auto.
--   intro H2.
--   right.
--   apply (less_transitive_unfolded _ _ _ _ H2 H).
--  elim (ap_imp_less _ _ H1).
--   auto.
--  intro H2.
--  left.
--  apply (less_transitive_unfolded _ _ _ _ H H2).
-- Qed.

-- Lemma less_cotransitive_unfolded : forall x y : R, x [<] y -> forall z, x [<] z or z [<] y.
-- Proof less_cotransitive.

-- Lemma pos_ap_zero : forall x : R, [0] [<] x -> x [#] [0].
-- Proof.
--  intros x H.
--  apply Greater_imp_ap.
--  assumption.
-- Defined.

-- (* Main characterization of less *)

-- Lemma leEq_not_eq : forall x y : R, x [<=] y -> x [#] y -> x [<] y.
-- Proof.
--  intros x y H H0.
--  elim (ap_imp_less _ _ H0); intro H1; auto.
--  rewrite -> leEq_def in H.
--  elim (H H1).
-- Qed.

-- End OrdField_basics.

-- (*---------------------------------*)
-- Section Basic_Properties_of_leEq.
-- (*---------------------------------*)

-- (**
-- ** Basic properties of [ [<=] ]
-- *)

-- Variable R : COrdField.

-- Lemma leEq_wdr : forall x y z : R, x [<=] y -> y [=] z -> x [<=] z.
-- Proof.
--  intros x y z H H0.
--  rewrite -> leEq_def in *.
--  intro H1.
--  apply H.
--  astepl z; assumption.
-- Qed.

-- Lemma leEq_wdl : forall x y z : R, x [<=] y -> x [=] z -> z [<=] y.
-- Proof.
--  intros x y z H H0.
--  rewrite -> leEq_def in *.
--  intro H1.
--  apply H.
--  astepr z;auto.
-- Qed.

-- Lemma leEq_reflexive : forall x : R, x [<=] x.
-- Proof.
--  intro x.
--  rewrite -> leEq_def.
--  apply less_irreflexive_unfolded.
-- Qed.

-- Declare Left Step leEq_wdl.
-- Declare Right Step leEq_wdr.

-- Lemma eq_imp_leEq : forall x y : R, x [=] y -> x [<=] y.
-- Proof.
--  intros x y H.
--  astepr x.
--  exact (leEq_reflexive _).
-- Qed.

-- Lemma leEq_imp_eq : forall x y : R, x [<=] y -> y [<=] x -> x [=] y.
-- Proof.
--  intros x y H H0. rewrite -> leEq_def in *|-.
--  apply not_ap_imp_eq. intro H1. apply H0.
--  elim (ap_imp_less _ _ _ H1); intro H2. auto.
--   elim (H H2).
-- Qed.

-- Lemma lt_equiv_imp_eq : forall x x' : R,
--  (forall y, x [<] y -> x' [<] y) -> (forall y, x' [<] y -> x [<] y) -> x [=] x'.
-- Proof.
--  intros x x' H H0.
--  apply leEq_imp_eq; rewrite -> leEq_def in |- *; intro H1.
--   apply (less_irreflexive_unfolded _ x); auto.
--  apply (less_irreflexive_unfolded _ x'); auto.
-- Qed.

-- Lemma less_leEq_trans : forall x y z : R, x [<] y -> y [<=] z -> x [<] z.
-- Proof.
--  intros x y z.
--  intros H H0.
--  elim (less_cotransitive_unfolded _ _ _ H z); intro H1.
--   assumption.
--  destruct (leEq_def _ y z).
--  elim ((H2 H0) H1).
-- Qed.

-- Lemma leEq_less_trans : forall x y z : R, x [<=] y -> y [<] z -> x [<] z.
-- Proof.
--  intros x y z.
--  intros H H0.
--  elim (less_cotransitive_unfolded _ _ _ H0 x); intro H1; try assumption.
--  destruct (leEq_def _ x y) as [H2 H3].
--  elim ((H2 H) H1).
-- Qed.

-- Lemma leEq_transitive : forall x y z : R, x [<=] y -> y [<=] z -> x [<=] z.
-- Proof.
--  intros x y z.
--  repeat rewrite -> leEq_def.
--  intros H H0 H1.
--  apply H.
--  apply leEq_less_trans with (y := z); firstorder using leEq_def.
-- Qed.

-- Lemma less_leEq : forall x y : R, x [<] y -> x [<=] y.
-- Proof.
--  intros.
--  rewrite -> leEq_def.
--  apply less_antisymmetric_unfolded.
--  assumption.
-- Qed.

-- Lemma leEq_or_leEq : forall x y:R, Not (Not (x[<=]y or y[<=]x)).
-- Proof.
--  intros x y H.
--  apply H.
--  right.
--  rewrite -> leEq_def.
--  intros H0.
--  apply H.
--  left.
--  apply less_leEq.
--  assumption.
-- Qed.

-- Lemma leEq_less_or_equal : forall x y:R, x[<=]y -> Not (Not (x[<]y or x[=]y)).
-- Proof.
--  intros x y Hxy H. revert Hxy.
--  rewrite -> leEq_def. intro Hxy. apply H.
--  right.
--  apply (not_ap_imp_eq).
--  intros H0.
--  destruct (ap_imp_less _ _ _ H0).
--   apply H.
--   left.
--   assumption.
--  apply Hxy.
--  assumption.
-- Qed.

-- End Basic_Properties_of_leEq.

-- #[global]
-- Hint Resolve less_leEq : algebra.

-- Declare Left Step leEq_wdl.
-- Declare Right Step leEq_wdr.

-- Section infinity_of_cordfields.
-- (**
-- ** Infinity of ordered fields

-- In an ordered field we have that [[1][+][1]] and
-- [[1][+][1][+][1]] and so on are all apart from zero.
-- We first show this, so that we can define [TwoNZ], [ThreeNZ]
-- and so on. These are elements of [Non[0]s], so that we can write
-- e.g.%\% [x[/]TwoNZ].
-- *)

-- Variable R : COrdField.

-- Lemma pos_one : ([0]:R) [<] [1].
-- Proof.
--  (* 0 [#] 1, so 0<1 (and we are done) or 1<0; so assume 1<0. *)
--  elim (ap_imp_less _ _ _ (ring_non_triv R)).
--   2: auto.
--  intro H.
--  exfalso.
--  apply (less_irreflexive_unfolded R [1]).
--  apply less_transitive_unfolded with ([0]:R).
--   auto.
--  (* By plus_resp_less, 0=(1-1)<(0-1)=-1. *)
--  cut (([0]:R) [<] [--][1]).
--   2: astepl (([1]:R)[+][--][1]).
--   2: astepr (([0]:R)[+][--][1]).
--   2: apply plus_resp_less_rht; auto.
--  intro H0.
--  (* By mult_resp_pos, 0<(-1).(-1)=1. *)
--  rstepr ([--]([1]:R)[*][--][1]).
--  apply (mult_resp_pos _ _ _ H0 H0).
-- Qed.

-- Lemma nring_less_succ : forall m : nat, (nring m:R) [<] nring (S m).
-- Proof.
--  intro m.
--  simpl in |- *.
--  astepr ([1][+]nring (R:=R) m).
--  astepl ([0][+]nring (R:=R) m).
--  apply plus_resp_less_rht.
--  apply pos_one.
-- Qed.

-- Lemma nring_less : forall m n : nat, m < n -> (nring m:R) [<] nring n.
-- Proof.
--  intros m n H.
--  generalize (toCProp_lt _ _ H); intro H0.
--  elim H0.
--   apply nring_less_succ.
--  clear H0 H n; intros n H H0.
--  apply less_transitive_unfolded with (nring (R:=R) n).
--   assumption.
--  apply nring_less_succ.
-- Qed.

-- Lemma nring_leEq : forall m n : nat, m <= n -> (nring m:R) [<=] nring n.
-- Proof.
--  intros m n H.
--  elim (le_lt_eq_dec _ _ H); intro H1.
--   rewrite -> leEq_def in |- *. apply less_antisymmetric_unfolded.
--   apply nring_less. auto.
--   rewrite H1.
--  rewrite -> leEq_def in |- *. apply less_irreflexive_unfolded.
-- Qed.

-- Lemma nring_apart : forall m n : nat, m <> n -> (nring m:R) [#] nring n.
-- Proof.
--  intros m n H.
--  elim (lt_eq_lt_dec m n); intro H0.
--   elim H0; intro H1.
--    apply less_imp_ap.
--    apply nring_less.
--    assumption.
--   elim (H H1).
--  apply Greater_imp_ap.
--  apply nring_less.
--  assumption.
-- Qed.

-- Lemma nring_ap_zero : forall n : nat, n <> 0 -> nring (R:=R) n [#] [0].
-- Proof.
--  intros n H.
--  exact (nring_apart _ _ H).
-- Qed.

-- Lemma nring_ap_zero' : forall n : nat, 0 <> n -> nring (R:=R) n [#] [0].
-- Proof.
--  intros.
--  apply nring_ap_zero; auto.
-- Qed.

-- Lemma nring_ap_zero_imp : forall n : nat, nring (R:=R) n [#] [0] -> 0 <> n.
-- Proof.
--  intros n H.
--  induction  n as [| n Hrecn].
--   simpl in H.
--   elim (ap_irreflexive_unfolded _ _ H).
--  apply O_S.
-- Qed.

-- Definition Snring (n : nat) := nring (R:=R) (S n).

-- Load "Transparent_algebra".

-- Lemma pos_Snring : forall n : nat, ([0]:R) [<] Snring n.
-- Proof.
--  intro n.
--  apply less_leEq_trans with ([1]:R).
--   apply pos_one.
--  stepl (nring (R:=R) 1). 2: simpl in |- *; algebra.
--   unfold Snring in |- *.
--  apply nring_leEq.
--  auto with arith.
-- Qed.

-- Lemma nringS_ap_zero : forall m : nat, nring (R:=R) (S m) [#] [0].
-- Proof.
--  intros.
--  apply pos_ap_zero.
--  exact (pos_Snring m).
-- Qed.

-- Lemma nring_fac_ap_zero : forall n : nat, nring (R:=R) (fact n) [#] [0].
-- Proof.
--  intro n; apply nring_ap_zero. cut (0 < fact n).
--  lia.
--  apply lt_O_fact.
-- Qed.

-- Load "Opaque_algebra".

-- Section up_to_four.

-- (**
-- *** Properties of one up to four
-- %\begin{nameconvention}%
-- In the names of lemmas, we denote the numbers 0,1,2,3,4 and so on, by
-- [zero], [one], [two] etc.
-- %\end{nameconvention}%
-- *)

-- Lemma less_plusOne : forall x : R, x [<] x[+][1].
-- Proof.
--  (* by plus_resp_less_rht and pos_one *)
--  intros x.
--  astepl ([0][+]x); astepr ([1][+]x).
--  apply plus_resp_less_rht.
--  exact pos_one.
-- Qed.

-- Lemma zero_lt_posplus1 : forall x : R, [0] [<=] x -> [0] [<] x[+][1].
-- Proof.
--  intros x zltx.
--  apply leEq_less_trans with x.
--   assumption.
--  exact (less_plusOne x).
-- Qed.

-- Lemma plus_one_ext_less : forall x y : R, x [<] y -> x [<] y[+][1].
-- Proof.
--  (* By transitivity of less and less_plus[1] *)
--  intros x y H.
--  apply less_leEq_trans with y.
--   assumption.
--  apply less_leEq; apply less_plusOne.
-- Qed.

-- Lemma one_less_two : ([1]:R) [<] Two.
-- Proof.
--  simpl in |- *.
--  astepr (([1]:R)[+][1]).
--  apply less_plusOne.
-- Qed.

-- Lemma two_less_three : (Two:R) [<] Three.
-- Proof.
--  simpl in |- *.
--  apply less_plusOne.
-- Qed.

-- Lemma three_less_four : (Three:R) [<] Four.
-- Proof.
--  simpl in |- *.
--  apply less_plusOne.
-- Qed.

-- Lemma pos_two : ([0]:R) [<] Two.
-- Proof.
--  apply less_leEq_trans with ([1]:R).
--   exact pos_one.
--  apply less_leEq; exact one_less_two.
-- Qed.

-- Lemma one_less_three : ([1]:R) [<] Three.
-- Proof.
--  apply less_leEq_trans with (Two:R).
--   exact one_less_two.
--  apply less_leEq; exact two_less_three.
-- Qed.

-- Lemma two_less_four : (Two:R) [<] Four.
-- Proof.
--  apply less_leEq_trans with (Three:R).
--   exact two_less_three.
--  apply less_leEq; exact three_less_four.
-- Qed.

-- Lemma pos_three : ([0]:R) [<] Three.
-- Proof.
--  apply less_leEq_trans with ([1]:R).
--   exact pos_one.
--  apply less_leEq; exact one_less_three.
-- Qed.

-- Lemma one_less_four : ([1]:R) [<] Four.
-- Proof.
--  apply less_leEq_trans with (Three:R).
--   exact one_less_three.
--  apply less_leEq; exact three_less_four.
-- Qed.

-- Lemma pos_four : ([0]:R) [<] Four.
-- Proof.
--  apply less_leEq_trans with ([1]:R).
--   exact pos_one.
--  apply less_leEq; exact one_less_four.
-- Qed.

-- Lemma two_ap_zero : Two [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero.
--  apply pos_two.
-- Qed.

-- Lemma three_ap_zero : Three [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero.
--  apply pos_three.
-- Qed.

-- Lemma four_ap_zero : Four [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero.
--  apply pos_four.
-- Qed.

-- End up_to_four.

-- Section More_than_four.

-- (**
-- *** Properties of some other numbers *)

-- Lemma pos_six : ([0]:R) [<] Six.
-- Proof.
--  exact (pos_Snring 5).
-- Qed.

-- Lemma pos_eight : ([0]:R) [<] Eight.
-- Proof.
--  exact (pos_Snring 7).
-- Qed.

-- Lemma pos_nine : ([0]:R) [<] Nine.
-- Proof.
--  exact (pos_Snring 8).
-- Qed.

-- Lemma pos_twelve : ([0]:R) [<] Twelve.
-- Proof.
--  exact (pos_Snring 11).
-- Qed.

-- Lemma pos_sixteen : ([0]:R) [<] Sixteen.
-- Proof.
--  exact (pos_Snring 15).
-- Qed.

-- Lemma pos_eighteen : ([0]:R) [<] Eighteen.
-- Proof.
--  exact (pos_Snring 17).
-- Qed.

-- Lemma pos_twentyfour : ([0]:R) [<] TwentyFour.
-- Proof.
--  exact (pos_Snring 23).
-- Qed.

-- Lemma pos_fortyeight : ([0]:R) [<] FortyEight.
-- Proof.
--  exact (pos_Snring 47).
-- Qed.

-- Lemma six_ap_zero : Six [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero; apply pos_six.
-- Qed.

-- Lemma eight_ap_zero : Eight [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero; apply pos_eight.
-- Qed.

-- Lemma nine_ap_zero : Nine [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero; apply pos_nine.
-- Qed.

-- Lemma twelve_ap_zero : Twelve [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero; apply pos_twelve.
-- Qed.

-- Lemma sixteen_ap_zero : Sixteen [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero; apply pos_sixteen.
-- Qed.

-- Lemma eighteen_ap_zero : Eighteen [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero; apply pos_eighteen.
-- Qed.

-- Lemma twentyfour_ap_zero : TwentyFour [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero; apply pos_twentyfour.
-- Qed.

-- Lemma fortyeight_ap_zero : FortyEight [#] ([0]:R).
-- Proof.
--  apply pos_ap_zero; apply pos_fortyeight.
-- Qed.

-- End More_than_four.

-- End infinity_of_cordfields.

-- #[global]
-- Hint Resolve pos_one : algebra.

-- Declare Left Step leEq_wdl.
-- Declare Right Step leEq_wdr.

-- Notation " x [/]OneNZ" := (x[/] [1][//]ring_non_triv _) (at level 20).
-- Notation " x [/]TwoNZ" := (x[/] Two[//]two_ap_zero _) (at level 20).
-- Notation " x [/]ThreeNZ" := (x[/] Three[//]three_ap_zero _) (at level 20).
-- Notation " x [/]FourNZ" := (x[/] Four[//]four_ap_zero _) (at level 20).
-- Notation " x [/]SixNZ" := (x[/] Six[//]six_ap_zero _) (at level 20).
-- Notation " x [/]EightNZ" := (x[/] Eight[//]eight_ap_zero _) (at level 20).
-- Notation " x [/]NineNZ" := (x[/] Nine[//]nine_ap_zero _) (at level 20).
-- Notation " x [/]TwelveNZ" := (x[/] Twelve[//]twelve_ap_zero _) (at level 20).
-- Notation " x [/]SixteenNZ" := (x[/] Sixteen[//]sixteen_ap_zero _) (at level 20).
-- Notation " x [/]EighteenNZ" := (x[/] Eighteen[//]eighteen_ap_zero _) (at level 20).
-- Notation " x [/]TwentyFourNZ" := (x[/] TwentyFour[//]twentyfour_ap_zero _) (at level 20).
-- Notation " x [/]FortyEightNZ" := (x[/] FortyEight[//]fortyeight_ap_zero _) (at level 20).

-- Section consequences_of_infinity.

-- (**
-- *** Consequences of infinity
-- *)

-- Variable F : COrdField.

-- Lemma square_eq : forall x a : F, a [#] [0] -> x[^]2 [=] a[^]2 -> {x [=] a} + {x [=] [--]a}.
-- Proof.
--  intros x a a_ H.
--  elim (cond_square_eq F x a); auto.
--  apply two_ap_zero.
-- Qed.

-- (**
-- Ordered fields have characteristic zero.
-- *)

-- Lemma char0_OrdField : Char0 F.
-- Proof.
--  unfold Char0 in |- *.
--  intros.
--  apply nring_ap_zero.
--  lia.
-- Qed.

-- End consequences_of_infinity.

-- (*---------------------------------*)
-- Section Properties_of_Ordering.
-- (*---------------------------------*)

-- (**
-- ** Properties of [[<]]
-- *)

-- Variable R : COrdField.


-- (**
-- We do not use a special predicate for positivity,
-- (e.g.%\% [PosP]), but just write [[0] [<] x].
-- Reasons: it is more natural; in ordinary mathematics we also write [[0] [<] x]
-- (or [x [>] [0]]).

-- *)

-- Section addition.
-- (**
-- *** Addition and subtraction%\label{section:less_plus_minus}%

-- *)

-- Lemma plus_resp_less_lft : forall x y z : R, x [<] y -> z[+]x [<] z[+]y.
-- Proof.
--  intros x y z H.
--  astepl (x[+]z).
--  astepr (y[+]z).
--  apply plus_resp_less_rht.
--  assumption.
-- Qed.

-- Lemma inv_resp_less : forall x y : R, x [<] y -> [--]y [<] [--]x.
-- Proof.
--  intros x y H.
--  rstepl (x[+]([--]x[+][--]y)).
--  rstepr (y[+]([--]x[+][--]y)).
--  apply plus_resp_less_rht.
--  assumption.
-- Qed.

-- Lemma minus_resp_less : forall x y z : R, x [<] y -> x[-]z [<] y[-]z.
-- Proof.
--  Transparent cg_minus.
--  unfold cg_minus in |- *.
--  intros x y z H.
--  apply plus_resp_less_rht.
--  assumption.
-- Qed.

-- Lemma minus_resp_less_rht : forall x y z : R, y [<] x -> z[-]x [<] z[-]y.
-- Proof.
--  intros.
--  Transparent cg_minus.
--  unfold cg_minus in |- *.
--  apply plus_resp_less_lft.
--  apply inv_resp_less.
--  assumption.
-- Qed.

-- Lemma plus_resp_less_both : forall a b c d : R, a [<] b -> c [<] d -> a[+]c [<] b[+]d.
-- Proof.
--  intros.
--  apply less_leEq_trans with (a[+]d).
--   apply plus_resp_less_lft.
--   assumption.
--  apply less_leEq.
--  apply plus_resp_less_rht.
--  assumption.
-- Qed.

-- (**
-- For versions of [plus_resp_less_both] where one [ [<] ] in the
-- assumption is replaced by [ [<=] ]%, see
-- Section~\ref{section:leEq-plus-minus}%.

-- Cancellation laws
-- *)

-- Lemma plus_cancel_less : forall x y z : R, x[+]z [<] y[+]z -> x [<] y.
-- Proof.
--  intros.
--  (* astepl (x[+][0]).
--  astepl (x[+](z[+]([--] z))). *)
--  rstepl (x[+]z[+][--]z).
--  (* astepr (y[+][0]).
--  astepr (y[+](z[+]([--] z))). *)
--  rstepr (y[+]z[+][--]z).
--  apply plus_resp_less_rht.
--  assumption.
-- Qed.

-- Lemma inv_cancel_less : forall x y : R, [--]x [<] [--]y -> y [<] x.
-- Proof.
--  intros.
--  apply plus_cancel_less with ([--]x[-]y).
--  rstepl ([--]x).
--  rstepr ([--]y).
--  assumption.
-- Qed.

-- (**

-- Lemmas where an operation is transformed into the inverse operation on
-- the other side of an inequality are called laws for shifting.
-- %\begin{nameconvention}%
-- The names of laws for shifting start with [shift_], and then come
-- the operation and the inequality, in the order in which they occur in the
-- conclusion.
-- If the shifted operand changes sides w.r.t.%\% the operation and its inverse,
-- the name gets a prime.
-- %\end{nameconvention}%

-- It would be nicer to write the laws for shifting as bi-implications,
-- However, it is impractical to use these in
-- Coq%(see the Coq shortcoming in Section~\ref{section:setoid-basics})%.
-- *)

-- Lemma shift_less_plus : forall x y z : R, x[-]z [<] y -> x [<] y[+]z.
-- Proof.
--  intros.
--  rstepl (x[-]z[+]z).
--  apply plus_resp_less_rht.
--  assumption.
-- Qed.

-- Lemma shift_less_plus' : forall x y z : R, x[-]y [<] z -> x [<] y[+]z.
-- Proof.
--  intros.
--  astepr (z[+]y).
--  apply shift_less_plus.
--  assumption.
-- Qed.

-- Lemma shift_less_minus : forall x y z : R, x[+]z [<] y -> x [<] y[-]z.
-- Proof.
--  intros.
--  rstepl (x[+]z[-]z).
--  apply minus_resp_less.
--  assumption.
-- Qed.

-- Lemma shift_less_minus' : forall x y z : R, z[+]x [<] y -> x [<] y[-]z.
-- Proof.
--  intros.
--  apply shift_less_minus.
--  astepl (z[+]x).
--  assumption.
-- Qed.

-- Lemma shift_plus_less : forall x y z : R, x [<] z[-]y -> x[+]y [<] z.
-- Proof.
--  intros.
--  rstepr (z[-]y[+]y).
--  apply plus_resp_less_rht.
--  assumption.
-- Qed.

-- Lemma shift_plus_less' : forall x y z : R, y [<] z[-]x -> x[+]y [<] z.
-- Proof.
--  intros.
--  astepl (y[+]x).
--  apply shift_plus_less.
--  assumption.
-- Qed.

-- Lemma shift_minus_less : forall x y z : R, x [<] z[+]y -> x[-]y [<] z.
-- Proof.
--  intros.
--  astepr (z[+]y[-]y).
--  apply minus_resp_less.
--  assumption.
-- Qed.

-- Lemma shift_minus_less' : forall x y z : R, x [<] y[+]z -> x[-]y [<] z.
-- Proof.
--  intros.
--  apply shift_minus_less.
--  astepr (y[+]z).
--  assumption.
-- Qed.

-- (**
-- Some special cases of laws for shifting.
-- *)

-- Lemma shift_zero_less_minus : forall x y : R, x [<] y -> [0] [<] y[-]x.
-- Proof.
--  intros.
--  rstepl (x[-]x).
--  apply minus_resp_less.
--  assumption.
-- Qed.

-- Lemma shift_zero_less_minus' : forall x y : R, [0] [<] y[-]x -> x [<] y.
-- Proof.
--  intros.
--  apply plus_cancel_less with ([--]x).
--  rstepl ([0]:R).
--  assumption.
-- Qed.

-- Lemma qltone : forall q : R, q [<] [1] -> q[-][1] [#] [0].
-- Proof.
--  intros.
--  apply less_imp_ap.
--  apply shift_minus_less.
--  astepr ([1]:R).
--  auto.
-- Qed.

-- End addition.

-- Section multiplication.
-- (**
-- *** Multiplication and division
-- By Convention%~\ref{convention:div-form}%
-- in CFields% (Section~\ref{section:fields})%, we often have redundant premises
-- in lemmas. E.g.%\% the informal statement
-- ``for all [x,y : R] with  [[0] [<] x] and [[0] [<] y]
-- we have [[0] [<] y[/]x]''
-- is formalized as follows.
-- [[
-- forall (x y : R) x_, ([0] [<] x) -> ([0] [<] y) -> ([0] [<] y[/]x[//]H)
-- ]]
-- We do this to keep it easy to use such lemmas.

-- *)

-- Lemma mult_resp_less : forall x y z : R, x [<] y -> [0] [<] z -> x[*]z [<] y[*]z.
-- Proof.
--  intros.
--  apply plus_cancel_less with ([--](x[*]z)).
--  astepl ([0]:R).
--  (* astepr ((y[*]z)[-](x[*]z)). *)
--  rstepr ((y[-]x)[*]z).
--  apply mult_resp_pos.
--   astepl (x[-]x).
--   apply minus_resp_less.
--   assumption.
--  assumption.
-- Qed.


-- Lemma recip_resp_pos : forall (y : R) y_, [0] [<] y -> [0] [<] ([1][/] y[//]y_).
-- Proof.
--  intros.
--  cut ([0] [<] ([1][/] y[//]y_) or ([1][/] y[//]y_) [<] [0]).
--   intros H0. elim H0; clear H0; intros H0.
--   auto.
--   exfalso.
--   apply (less_irreflexive_unfolded R [0]).
--   eapply less_transitive_unfolded.
--    2: apply H0.
--   cut ([1] [<] ([0]:R)). intro H1.
--    elim (less_antisymmetric_unfolded _ _ _ (pos_one _) H1).
--   astepl ([--]([--][1]:R)). astepr ([--]([0]:R)).
--   apply inv_resp_less.
--   rstepr (y[*][--]([1][/] y[//]y_)).
--   apply mult_resp_pos. auto.
--    astepl ([--]([0]:R)).
--   apply inv_resp_less. auto.
--   apply ap_imp_less.
--  apply ap_symmetric_unfolded. apply div_resp_ap_zero_rev.
--  apply ring_non_triv.
-- Qed.


-- Lemma div_resp_less_rht : forall (x y z : R) z_, x [<] y -> [0] [<] z -> (x[/] z[//]z_) [<] (y[/] z[//]z_).
-- Proof.
--  intros.
--  rstepl (x[*]([1][/] z[//]z_)).
--  rstepr (y[*]([1][/] z[//]z_)).
--  apply mult_resp_less. auto.
--   apply recip_resp_pos.
--  auto.
-- Qed.


-- Lemma div_resp_pos : forall (x y : R) x_, [0] [<] x -> [0] [<] y -> [0] [<] (y[/] x[//]x_).
-- Proof.
--  intros.
--  astepl ([0][/] x[//]x_).
--  apply div_resp_less_rht; auto.
-- Qed.


-- Lemma mult_resp_less_lft : forall x y z : R, x [<] y -> [0] [<] z -> z[*]x [<] z[*]y.
-- Proof.
--  intros.
--  astepl (x[*]z).
--  astepr (y[*]z).
--  apply mult_resp_less.
--   assumption.
--  assumption.
-- Qed.

-- Lemma mult_resp_less_both : forall x y u v : R,
--  [0] [<=] x -> x [<] y -> [0] [<=] u -> u [<] v -> x[*]u [<] y[*]v.
-- Proof.
--  cut (forall x y z : R, x [<=] y -> [0] [<=] z -> x[*]z [<=] y[*]z).
--   intro resp_leEq.
--   intros.
--   apply leEq_less_trans with (y[*]u).
--    apply resp_leEq; auto.
--    apply less_leEq; auto.
--   apply mult_resp_less_lft; auto.
--   apply leEq_less_trans with x; auto.
--  (* Cut *)
--  intros x y z.
--  repeat rewrite -> leEq_def in |- *.
--  intros H H0 H1.
--  generalize (shift_zero_less_minus _ _ H1); intro H2.
--  cut ([0] [<] (x[-]y)[*]z).
--   intro H3.
--   2: rstepr (x[*]z[-]y[*]z); auto.
--  cut (forall a b : R, [0] [<] a[*]b -> [0] [<] a and [0] [<] b or a [<] [0] and b [<] [0]).
--   intro H4.
--   generalize (H4 _ _ H3); intro H5.
--   elim H5; intro H6; elim H6; intros H7 H8.
--    apply H.
--    astepl ([0][+]y).
--    apply shift_plus_less.
--    assumption.
--   apply H0.
--   assumption.
--  intros a b H4.
--  generalize (Greater_imp_ap _ _ _ H4); intro H5.
--  generalize (mult_cancel_ap_zero_lft _ _ _ H5); intro H6.
--  generalize (mult_cancel_ap_zero_rht _ _ _ H5); intro H7.
--  elim (ap_imp_less _ _ _ H6); intro H8.
--   right.
--   split; auto.
--   elim (ap_imp_less _ _ _ H7); auto.
--   intro H9.
--   exfalso.
--   apply (less_irreflexive_unfolded R [0]).
--   apply less_leEq_trans with (a[*]b); auto.
--   apply less_leEq.
--   apply inv_cancel_less.
--   astepl ([0]:R).
--   astepr ([--]a[*]b).
--   apply mult_resp_pos; auto.
--   astepl ([--]([0]:R)).
--   apply inv_resp_less; auto.
--  left.
--  split; auto.
--  elim (ap_imp_less _ _ _ H7); auto.
--  intro H9.
--  exfalso.
--  apply (less_irreflexive_unfolded R [0]).
--  apply less_leEq_trans with (a[*]b); auto.
--  apply less_leEq.
--  apply inv_cancel_less.
--  astepl ([0]:R).
--  astepr (a[*][--]b).
--  apply mult_resp_pos; auto.
--  astepl ([--]([0]:R)).
--  apply inv_resp_less; auto.
-- Qed.

-- Lemma recip_resp_less : forall (x y : R) x_ y_, [0] [<] x -> x [<] y -> ([1][/] y[//]y_) [<] ([1][/] x[//]x_).
-- Proof.
--  intros.
--  cut ([0] [<] x[*]y). intro.
--   cut (x[*]y [#] [0]). intro H2.
--    rstepl (x[*]([1][/] x[*]y[//]H2)).
--    rstepr (y[*]([1][/] x[*]y[//]H2)).
--    apply mult_resp_less. auto.
--     apply recip_resp_pos. auto.
--    apply Greater_imp_ap. auto.
--   apply mult_resp_pos. auto.
--   apply less_leEq_trans with x; try apply less_leEq; auto.
-- Qed.

-- Lemma div_resp_less : forall (x y z : R) z_, [0] [<] z -> x [<] y -> (x[/] z[//]z_) [<] (y[/] z[//]z_).
-- Proof.
--  intros.
--  rstepl (x[*]([1][/] z[//]z_)).
--  rstepr (y[*]([1][/] z[//]z_)).
--  apply mult_resp_less.
--   assumption.
--  apply recip_resp_pos.
--  auto.
-- Qed.

-- (** Cancellation laws
-- *)

-- Lemma mult_cancel_less : forall x y z : R, [0] [<] z -> x[*]z [<] y[*]z -> x [<] y.
-- Proof.
--  intros x y z H H0.
--  generalize (Greater_imp_ap _ _ _ H); intro H1.
--  rstepl (x[*]z[*]([1][/] z[//]H1)).
--  rstepr (y[*]z[*]([1][/] z[//]H1)).
--  apply mult_resp_less.
--   assumption.
--  rstepl ([0][/] z[//]H1).
--  apply div_resp_less_rht.
--   apply pos_one.
--  assumption.
-- Qed.

-- (**
-- Laws for shifting

-- %For namegiving, see the Section~\ref{section:less_plus_minus}
-- on plus and minus.%
-- *)

-- Lemma shift_div_less : forall (x y z : R) y_, [0] [<] y -> x [<] z[*]y -> (x[/] y[//]y_) [<] z.
-- Proof.
--  intros.
--  apply mult_cancel_less with y. auto.
--   astepl x. auto.
-- Qed.

-- Lemma shift_div_less' : forall (x y z : R) y_, [0] [<] y -> x [<] y[*]z -> (x[/] y[//]y_) [<] z.
-- Proof.
--  intros.
--  apply shift_div_less; auto.
--  astepr (y[*]z). auto.
-- Qed.

-- Lemma shift_less_div : forall (x y z : R) y_, [0] [<] y -> x[*]y [<] z -> x [<] (z[/] y[//]y_).
-- Proof.
--  intros.
--  apply mult_cancel_less with y. auto.
--   astepr z. auto.
-- Qed.

-- Lemma shift_less_mult : forall (x y z : R) z_, [0] [<] z -> (x[/] z[//]z_) [<] y -> x [<] y[*]z.
-- Proof.
--  intros.
--  astepl ((x[/] z[//]z_)[*]z).
--  apply mult_resp_less; auto.
-- Qed.

-- Lemma shift_less_mult' : forall (x y z : R) y_, [0] [<] y -> (x[/] y[//]y_) [<] z -> x [<] y[*]z.
-- Proof.
--  intros.
--  astepl (y[*](x[/] y[//]y_)).
--  apply mult_resp_less_lft; auto.
-- Qed.

-- Lemma shift_mult_less : forall (x y z : R) y_, [0] [<] y -> x [<] (z[/] y[//]y_) -> x[*]y [<] z.
-- Proof.
--  intros.
--  astepr ((z[/] y[//]y_)[*]y).
--  apply mult_resp_less; auto.
-- Qed.

-- (** Other properties of multiplication and division
-- *)

-- Lemma minusOne_less : forall x : R, x[-][1] [<] x.
-- Proof.
--  intros; apply shift_minus_less; apply less_plusOne.
-- Qed.

-- Lemma swap_div : forall (x y z : R) y_ z_, [0] [<] y -> [0] [<] z -> (x[/] z[//]z_) [<] y -> (x[/] y[//]y_) [<] z.
-- Proof.
--  intros.
--  rstepl ((x[/] z[//]z_)[*](z[/] y[//]y_)).
--  astepr (y[*](z[/] y[//]y_)).
--  apply mult_resp_less. auto.
--   apply div_resp_pos; auto.
-- Qed.

-- Lemma eps_div_less_eps : forall (eps d : R) d_, [0] [<] eps -> [1] [<] d -> (eps[/] d[//]d_) [<] eps.
-- Proof.
--  intros.
--  apply shift_div_less'.
--   apply leEq_less_trans with ([1]:R).
--    apply less_leEq; apply pos_one.
--   assumption.
--  astepl ([1][*]eps).
--  apply mult_resp_less.
--   assumption.
--  assumption.
-- Qed.

-- Lemma pos_div_two : forall eps : R, [0] [<] eps -> [0] [<] eps [/]TwoNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_two.
--  astepl ([0]:R).
--  assumption.
-- Qed.

-- Lemma pos_div_two' : forall eps : R, [0] [<] eps -> eps [/]TwoNZ [<] eps.
-- Proof.
--  intros.
--  apply plus_cancel_less with ([--](eps [/]TwoNZ)).
--  astepl ([0]:R).
--  rstepr (eps [/]TwoNZ).
--  apply pos_div_two; assumption.
-- Qed.

-- (*
-- Apply mult_cancel_less with (Two::R).
-- Apply pos_two.
-- rstepl eps[+][0]; rstepr eps[+]eps.
-- Apply plus_resp_less_lft.
-- Auto.
-- Qed.
-- *)

-- Lemma pos_div_three : forall eps : R, [0] [<] eps -> [0] [<] eps [/]ThreeNZ.
-- Proof.
--  intros.
--  apply mult_cancel_less with (Three:R).
--   apply pos_three.
--  astepl ([0]:R); rstepr eps.
--  assumption.
-- Qed.

-- Lemma pos_div_three' : forall eps : R, [0] [<] eps -> eps [/]ThreeNZ [<] eps.
-- Proof.
--  intros.
--  apply mult_cancel_less with (Three:R).
--   apply pos_three.
--  rstepl (eps[+][0]); rstepr (eps[+]Two[*]eps).
--  apply plus_resp_less_lft.
--  apply mult_resp_pos; auto.
--  apply pos_two.
-- Qed.

-- Lemma pos_div_four : forall eps : R, [0] [<] eps -> [0] [<] eps [/]FourNZ.
-- Proof.
--  intros.
--  rstepr ((eps [/]TwoNZ) [/]TwoNZ).
--  apply pos_div_two; apply pos_div_two; assumption.
-- Qed.

-- Lemma pos_div_four' : forall eps : R, [0] [<] eps -> eps [/]FourNZ [<] eps.
-- Proof.
--  intros.
--  rstepl ((eps [/]TwoNZ) [/]TwoNZ).
--  apply leEq_less_trans with (eps [/]TwoNZ).
--   2: apply pos_div_two'; assumption.
--  apply less_leEq.
--  apply pos_div_two'.
--  apply pos_div_two.
--  assumption.
-- Qed.

-- Lemma pos_div_six : forall eps : R, [0] [<] eps -> [0] [<] eps [/]SixNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_six.
--  astepl ([0]:R).
--  assumption.
-- Qed.

-- Lemma pos_div_eight : forall eps : R, [0] [<] eps -> [0] [<] eps [/]EightNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_eight.
--  astepl ([0]:R).
--  assumption.
-- Qed.

-- Lemma pos_div_nine : forall eps : R, [0] [<] eps -> [0] [<] eps [/]NineNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_nine.
--  astepl ([0]:R).
--  assumption.
-- Qed.

-- Lemma pos_div_twelve : forall eps : R, [0] [<] eps -> [0] [<] eps [/]TwelveNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_twelve.
--  astepl ([0]:R).
--  assumption.
-- Qed.

-- Lemma pos_div_sixteen : forall eps : R, [0] [<] eps -> [0] [<] eps [/]SixteenNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_sixteen.
--  astepl ([0]:R).
--  assumption.
-- Qed.

-- Lemma pos_div_eighteen : forall eps : R, [0] [<] eps -> [0] [<] eps [/]EighteenNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_eighteen.
--  astepl ([0]:R).
--  assumption.
-- Qed.

-- Lemma pos_div_twentyfour : forall eps : R, [0] [<] eps -> [0] [<] eps [/]TwentyFourNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_twentyfour.
--  astepl ([0]:R).
--  assumption.
-- Qed.

-- Lemma pos_div_fortyeight : forall eps : R, [0] [<] eps -> [0] [<] eps [/]FortyEightNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_fortyeight.
--  astepl ([0]:R).
--  assumption.
-- Qed.

-- End multiplication.

-- Section misc.

-- (**
-- *** Miscellaneous properties
-- *)

-- Lemma nring_pos : forall m : nat, 0 < m -> [0] [<] nring (R:=R) m.
-- Proof.
--  intro m. elim m.
--  intro; elim (Nat.lt_irrefl 0 H).
--  clear m; intros.
--  apply leEq_less_trans with (nring (R:=R) n).
--   astepl (nring (R:=R) 0).
--   apply nring_leEq; auto with arith.
--  simpl in |- *; apply less_plusOne.
-- Qed.

-- Lemma less_nring : forall n m : nat, nring (R:=R) n [<] nring m -> n < m.
-- Proof.
--  intro n; induction  n as [| n Hrecn].
--   intros m H.
--   induction  m as [| m Hrecm].
--    exfalso; generalize H; apply less_irreflexive_unfolded.
--   auto with arith.
--  intros m H.
--  induction  m as [| m Hrecm].
--   exfalso.
--   cut (nring (R:=R) 0 [<] nring (S n)).
--    apply less_antisymmetric_unfolded; assumption.
--   apply nring_less; auto with arith.
--  cut (n < m).
--   auto with arith.
--  apply Hrecn.
--  rstepr (nring (R:=R) m[+][1][-][1]).
--  apply shift_less_minus.
--  apply H.
-- Qed.

-- Lemma pos_nring_fac : forall n : nat, [0] [<] nring (R:=R) (fact n).
-- Proof.
--  intro.
--  astepl (nring (R:=R) 0).
--  apply nring_less.
--  apply lt_O_fact.
-- Qed.

-- Lemma Smallest_less_Average : forall a b : R, a [<] b -> a [<] (a[+]b) [/]TwoNZ.
-- Proof.
--  intros.
--  apply shift_less_div.
--   apply pos_two.
--  rstepl (a[+]a).
--  apply plus_resp_less_lft.
--  assumption.
-- Qed.

-- Lemma Average_less_Greatest : forall a b : R, a [<] b -> (a[+]b) [/]TwoNZ [<] b.
-- Proof.
--  intros.
--  apply shift_div_less'.
--   apply pos_two.
--  rstepr (b[+]b).
--  apply plus_resp_less_rht.
--  assumption.
-- Qed.

-- Lemma Sum_resp_less : forall (f g : nat -> R) a b, a <= b ->
--  (forall i, a <= i -> i <= b -> f i [<] g i) -> Sum a b f [<] Sum a b g.
-- Proof.
--  intros.
--  induction  b as [| b Hrecb]; intros.
--   replace a with 0.
--    astepl (f 0). astepr (g 0).
--    auto.
--   inversion H. auto.
--   elim (le_lt_eq_dec _ _ H); intro H1.
--   apply less_wdl with (Sum a b f[+]f (S b)).
--    apply less_wdr with (Sum a b g[+]g (S b)).
--     apply plus_resp_less_both.
--      apply Hrecb. auto with arith. auto.
--       apply X; auto.
--    apply eq_symmetric_unfolded. apply Sum_last.
--    apply eq_symmetric_unfolded. apply Sum_last.
--   rewrite H1.
--  astepl (f (S b)).
--  astepr (g (S b)).
--  apply X; auto.
-- Qed.

-- Lemma Sumx_resp_less : forall n, 0 < n -> forall f g : forall i, i < n -> R,
--  (forall i H, f i H [<] g i H) -> Sumx f [<] Sumx g.
-- Proof.
--  simple induction n.
--   intros; simpl in |- *; exfalso; inversion H.
--  simple induction n0.
--   intros.
--   clear H.
--   simpl in |- *; apply plus_resp_less_lft.
--   apply X0.
--  intros.
--  simpl in |- *.
--  apply plus_resp_less_both.
--   astepl (Sumx (fun (i : nat) (l : i < S n1) => f i (Nat.lt_lt_succ_r _ _ l))).
--   astepr (Sumx (fun (i : nat) (l : i < S n1) => g i (Nat.lt_lt_succ_r _ _ l))).
--   apply X0.
--    auto with arith.
--   intros. apply X1.
--   apply X1.
-- Qed.

-- Lemma positive_Sum_two : forall x y : R, [0] [<] x[+]y -> [0] [<] x or [0] [<] y.
-- Proof.
--  intros.
--  cut ([--]x [<] [0] or [0] [<] y).
--   intro; inversion_clear X0.
--    left; astepl ([--]([0]:R)); astepr ([--][--]x); apply inv_resp_less; assumption.
--   right; assumption.
--  apply less_cotransitive_unfolded.
--  astepl ([0][-]x); apply shift_minus_less'; assumption.
-- Qed.

-- Lemma positive_Sumx : forall n (f : forall i, i < n -> R),
--  nat_less_n_fun f -> [0] [<] Sumx f -> {i : nat | {H : i < n | [0] [<] f i H}}.
-- Proof.
--  simple induction n.
--   simpl in |- *.
--   intros; exfalso; generalize X; apply less_irreflexive_unfolded.
--  simple induction n0.
--   simpl in |- *.
--   intros.
--   exists 0.
--   exists (Nat.lt_succ_diag_r 0).
--   eapply less_wdr.
--    apply X0.
--   astepl (f _ (Nat.lt_succ_diag_r 0)).
--   apply H; auto.
--  simpl in |- *; intros.
--  clear X.
--  cut ([0] [<] f _ (Nat.lt_succ_diag_r (S n1)) or [0] [<]
--    Sumx (fun (i : nat) (l : i < n1) => f i (Nat.lt_lt_succ_r i (S n1) (Nat.lt_lt_succ_r i n1 l)))[+]
--      f n1 (Nat.lt_lt_succ_r n1 (S n1) (Nat.lt_succ_diag_r n1))).
--   intro X.  inversion_clear X.
--   exists (S n1).
--    exists (Nat.lt_succ_diag_r (S n1)).
--    eapply less_wdr.
--     apply X2.
--    apply H; auto.
--   set (f' := fun (i : nat) (H : i < S n1) => f i (Nat.lt_lt_succ_r _ _ H)) in *.
--   cut {i : nat | {H : i < S n1 | [0] [<] f' i H}}; intros.
--    elim X; intros i Hi; elim Hi; clear X2 Hi; intros Hi Hi'.
--    exists i.
--    exists (Nat.lt_lt_succ_r _ _ Hi).
--    eapply less_wdr.
--     apply Hi'.
--    unfold f' in |- *; simpl in |- *.
--    apply H; auto.
--   apply X0.
--    red in |- *. intros i j Hij. rewrite Hij. unfold f' in |- *.
--    intros H0 H'.
--    apply H; auto.
--   apply X2; assumption.
--  apply positive_Sum_two.
--  eapply less_wdr.
--   2: apply cag_commutes_unfolded.
--  assumption.
-- Qed.

-- Lemma negative_Sumx : forall n (f : forall i, i < n -> R),
--  nat_less_n_fun f -> Sumx f [<] [0] -> {i : nat | {H : i < n | f i H [<] [0]}}.
-- Proof.
--  intros.
--  cut {i : nat | {H : i < n | [0] [<] [--](f i H)}}.
--   intro H1.
--   elim H1; intros i Hi; elim Hi; clear X Hi; intros Hi Hi'.
--   exists i; exists Hi.
--   astepl ([--][--](f i Hi)); astepr ([--]([0]:R)); apply inv_resp_less; assumption.
--  apply positive_Sumx with (f := fun (i : nat) (H : i < n) => [--](f i H)).
--   red in |- *; intros.
--   apply un_op_wd_unfolded; apply H; assumption.
--  astepl ([--]([0]:R)); apply less_wdr with ([--](Sumx f)).
--   apply inv_resp_less; assumption.
--  generalize f H; clear X H f.
--  induction  n as [| n Hrecn].
--   simpl in |- *.
--   intros; algebra.
--  intros.
--  simpl in |- *.
--  rstepl ([--](Sumx (fun (i : nat) (l : i < n) => f i (Nat.lt_lt_succ_r i n l)))[+] [--](f n (Nat.lt_succ_diag_r n))).
--  apply bin_op_wd_unfolded.
--   2: algebra.
--  apply Hrecn with (f := fun (i : nat) (l : i < n) => f i (Nat.lt_lt_succ_r i n l)).
--  red in |- *; intros; apply H; auto.
-- Qed.

-- End misc.

-- End Properties_of_Ordering.

-- Add Parametric Morphism c : (@cof_leEq c) with signature (@cs_eq (cof_crr c)) ==> (@cs_eq c) ==> iff as cof_leEq_wd.
-- Proof with try assumption.
--  intros x1 x2 Hx y1 y2 Hy.
--  split; intros.
--   stepl x1...
--   stepr y1...
--  symmetry in Hx, Hy.
--  stepl x2...
--  stepr y2...
-- Qed.
