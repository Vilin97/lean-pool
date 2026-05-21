/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import LeanPool.HopfieldNet.CReals.Core.CoRNmetric2Metric
--import HopfieldNet.CReals.CornQposMinMax
-- (*
-- Copyright © 2008 Russell O’Connor

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
-- Require Import CoRN.model.totalorder.QposMinMax.
-- Require Export CoRN.metric2.Metric.

-- Local Open Scope Q_scope.

-- (**
-- ** Classification of metric spaces

-- A metric space is located if you can choose
-- between ball d x y and ~ball e x y for e < d. Every located metric
-- is a stable metric. This translates the located property of the real
-- numbers e < d -> (e < d(x,y) \/ d(x,y) < d). *)
-- Definition locatedMetric (ms:MetricSpace) :=
--   forall (e d:Q) (x y:ms),
--     e < d -> {ball d x y}+{~ball e x y}.

/--
A metric space is located if for all `e < d`,
you can choose between `ball d x y` and `¬ ball e x y`.
-/
def LocatedMetric (ms : MetricSpace') : Prop :=
  ∀ (e d : ℚ) (x y : ms.carrier), e < d →
    (ms.ball d x y) ∨ ¬ (ms.ball e x y)

-- (** At the top level a metric space is decidable if its ball relation
-- is decidable.  Every decidable metric is a located metric. *)

-- Definition decidableMetric (ms:MetricSpace) :=
--  forall e (x y:ms), {ball e x y}+{~ball e x y}.

/--
A metric space is decidable if its ball relation is decidable.
-/
def DecidableMetric (ms : MetricSpace') : Prop :=
  ∀ (e : ℚ) (x y : ms.carrier), (ms.ball e x y ∨ ¬ ms.ball e x y)

lemma lt_le_weak {α : Type*} [LinearOrder α] {x y : α} (h : x < y) : x ≤ y :=
le_of_lt h

lemma decidable_located :
  ∀ (ms : MetricSpace'), DecidableMetric ms → LocatedMetric ms := by
  intros ms H e d x y Hed
  cases' H e x y with h_ball h_nball
  { left
    apply ball_weak_le ms (e:=e)
    apply lt_le_weak
    exact Hed
    exact h_ball}
  { right; exact h_nball}

-- Lemma decidable_located : forall ms,
--  decidableMetric ms -> locatedMetric ms.
-- Proof.
--  intros ms H e d x y Hed.
--  destruct (H e x y).
--   left.
--   abstract ( apply ball_weak_le with e;
--              try assumption; apply Qlt_le_weak; assumption).
--  right; assumption.
-- Defined.
