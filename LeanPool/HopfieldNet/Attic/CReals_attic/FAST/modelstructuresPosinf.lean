/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.Core.CornQposMinMax
-- (*
-- Copyright © 2006-2008 Russell O’Connor

-- Permission is hereby granted, free of charge, to any person obtaining a copy of
-- this proof and associated documentation files (the "Proof"), to deal in
-- the Proof without restriction, including without limitation the rights to
-- use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
-- the Proof, and to permit persons to whom the Proof is furnished to do so,
-- subject to the following conditions:

-- The above copyright notice and this permission notice shall be included in all
-- copies or substantial portions of the Proof.

-- THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
-- FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
-- COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
-- IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
-- CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
-- *)

-- From Coq Require Export QArith.
-- Require Import CoRN.model.totalorder.QposMinMax.

-- (** printing QposInf $\mathbb{Q}^{+}_{\infty}$ #Q<SUP>+</SUP><SUB>&infin;</SUB># *)
-- (** printing QposInfinity $\infty$ #&infin;# *)

-- (** The type of positive rational numbers, including positive infinity. *)

-- Set Implicit Arguments.

-- Local Open Scope Q_scope.
-- Local Open Scope Qpos_scope.

-- (**
-- * [Qpos]
-- We choose to define [QposInf] as the disjoint union of [Qpos] and an
-- Infinity token.
-- *)

-- Inductive QposInf : Set :=
-- | Qpos2QposInf : Qpos -> QposInf
-- | QposInfinity : QposInf.

inductive QposInf where
  | Qpos2QposInf : Qpos → QposInf
  | QposInfinity : QposInf

-- Bind Scope QposInf_scope with QposInf.
-- Delimit Scope QposInf_scope with QposInf.

-- (** Qpos2QposInf is an injection from [Qpos] to [QposInf] that we
-- declare as a coercion.
-- *)
-- Coercion Qpos2QposInf : Qpos >-> QposInf.

-- (** This bind operation is useful for lifting operations to work
-- on [QposInf].  It will map [QposInfinity] to [QposInfinity]. *)
-- Definition QposInf_bind (f : Qpos -> QposInf) (x:QposInf) :=
--  match x with
--  | Qpos2QposInf x' => f x'
--  | QposInfinity => QposInfinity
--  end.

-- Lemma QposInf_bind_id : forall x, QposInf_bind (fun e => e) x = x.
-- Proof.
--  intros [x|]; reflexivity.
-- Qed.

-- (** Equality *)
-- Definition QposInfEq (a b:QposInf) :=
--  match a, b with
--  | Qpos2QposInf x, Qpos2QposInf y => Qeq (proj1_sig x) (proj1_sig y)
--  | QposInfinity, QposInfinity => True
--  | _, _ => False
--  end.

-- Lemma QposInfEq_refl x : QposInfEq x x.
-- Proof.
--   destruct x as [x|]. apply Qeq_refl.
--   simpl. trivial.
-- Qed.

-- Lemma QposInfEq_sym x y : QposInfEq x y -> QposInfEq y x.
-- Proof.
--   destruct x as [x|], y as [y|]; simpl; trivial. apply Qeq_sym.
-- Qed.

-- Lemma QposInfEq_trans x y z : QposInfEq x y -> QposInfEq y z -> QposInfEq x z.
-- Proof.
--   destruct x as [x|], y as [y|], z as  [z|]; simpl; try tauto. apply Qeq_trans.
-- Qed.

-- Add Relation QposInf QposInfEq
--  reflexivity proved by QposInfEq_refl
--  symmetry proved by QposInfEq_sym
--  transitivity proved by QposInfEq_trans as QposInfSetoid.

-- #[global]
-- Instance: Proper (QposEq ==> QposInfEq) Qpos2QposInf.
-- Proof.
--   intros x y H. exact H.
-- Qed.

-- #[global]
-- Instance QposInf_bind_wd (f : Qpos -> QposInf) {f_wd : Proper (QposEq ==> QposInfEq) f} :
--   Proper (QposInfEq ==> QposInfEq) (QposInf_bind f).
-- Proof.
--   intros [x|] [y|] E; simpl; auto.
--    destruct E.
--   destruct E.
-- Qed.

-- (** Addition *)
-- Definition QposInf_plus (x y : QposInf) : QposInf :=
-- QposInf_bind (fun x' => QposInf_bind (fun y' => Qpos_plus x' y') y) x.

-- #[global]
-- Instance: Proper (QposInfEq ==> QposInfEq ==> QposInfEq) QposInf_plus.
-- Proof with auto.
--   intros [x1|] [y1|] E1 [x2|] [y2|] E2; simpl...
--   apply Qplus_comp...
-- Qed.

-- (** Multiplication *)
-- Definition QposInf_mult (x y : QposInf) : QposInf :=
-- QposInf_bind (fun x' => QposInf_bind (fun y' => Qpos_mult x' y') y) x.

-- #[global]
-- Instance: Proper (QposInfEq ==> QposInfEq ==> QposInfEq) QposInf_mult.
-- Proof with auto.
--   intros [x1|] [y1|] E1 [x2|] [y2|] E2; simpl...
--   apply Qmult_comp...
-- Qed.

-- (** Order *)
-- Definition QposInf_le (x y: QposInf) : Prop :=
-- match y with
-- | QposInfinity => True
-- | Qpos2QposInf y' =>
--  match x with
--  | QposInfinity => False
--  | Qpos2QposInf x' => proj1_sig x' <= proj1_sig y'
--  end
-- end.

-- (** Minimum *)
-- Definition QposInf_min (x y : QposInf) : QposInf :=
-- match x with
-- | QposInfinity => y
-- | Qpos2QposInf x' =>
--  match y with
--  | QposInfinity => x'
--  | Qpos2QposInf y' => Qpos2QposInf (Qpos_min x' y')
--  end
-- end.

-- #[global]
-- Instance: Proper (QposInfEq ==> QposInfEq ==> QposInfEq) QposInf_min.
-- Proof with intuition.
--   intros [x1|] [y1|] E1 [x2|] [y2|] E2; simpl in *...
--   apply Qpos_min_compat_Proper...
-- Qed.

-- Lemma QposInf_min_lb_l : forall x y, QposInf_le (QposInf_min x y) x.
-- Proof.
--  intros [x|] [y|]; simpl; try auto.
--   apply Qpos_min_lb_l.
--  apply Qle_refl.
-- Qed.

-- Lemma QposInf_min_lb_r : forall x y, QposInf_le (QposInf_min x y) y.
-- Proof.
--  intros [x|] [y|]; simpl; try auto.
--   apply Qpos_min_lb_r.
--  apply Qle_refl.
-- Qed.

-- Infix "+" := QposInf_plus : QposInf_scope.
-- Infix "*" := QposInf_mult : QposInf_scope.
