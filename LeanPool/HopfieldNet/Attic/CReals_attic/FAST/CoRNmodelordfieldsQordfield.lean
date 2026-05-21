/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
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

-- Require Export CoRN.model.fields.Qfield.
-- Require Import CoRN.algebra.COrdFields.
-- Require Import CoRN.stdlib_omissions.Q.
-- (**
-- ** Example of an ordered field: $\langle$#&lang;#[Q],[[+]],[[*]],[[<]]$\rangle$#&rang;#
--  [Q] is an archemaedian ordered field.
-- *)

-- Definition Qlt_is_strict_order := Build_strictorder
--  Qlt_trans Qlt_is_antisymmetric_unfolded.

-- Definition Qlt_is_strict_order := Build_strictorder
--  Qlt_trans Qlt_is_antisymmetric_unfolded.

-- Definition Q_is_COrdField := Build_is_COrdField Q_as_CField
--  Qlt_is_CSetoid_relation Qle (default_greater Q_as_CField Qlt_is_CSetoid_relation)
--  (default_grEq Q_as_CField Qle) Qlt_is_strict_order (fun x y E z => proj2 (Qplus_lt_l x y z) E)
--  Qmult_lt_0_compat Qlt_gives_apartness Qle_is_not_lt Qgt_is_lt Qge_is_not_gt.

-- Definition Q_as_COrdField := Build_COrdField _ _ _ _ _ Q_is_COrdField.

-- Canonical Structure Q_as_COrdField.

-- Theorem Q_is_archemaedian : forall x : Q_as_COrdField, {n : nat | x [<] nring n}.
-- Proof.
--  intros x. destruct (Q_is_archemaedian0 x) as [n Pn].
--  exists (nat_of_P n). simpl in *.
--  rewrite nring_Q. rewrite <-Zpos_eq_Z_of_nat_o_nat_of_P. assumption.
-- Qed.

theorem rat_is_archimedean (x : ℚ) : ∃ n : ℕ, x < n := by sorry
