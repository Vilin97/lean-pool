/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.RNS.CoRNalgebraCOrdCauchy

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

-- (** printing Lim %\ensuremath{\lim}% *)

-- Require Export CoRN.algebra.COrdCauchy.

-- (**
-- * Definition of the notion of reals
-- The reals are defined as a Cauchy-closed Archimedean constructive
-- ordered field in which we have a maximum function. The maximum
-- function is definable, using countable choice, but in a rather tricky
-- way. Cauchy completeness is stated by assuming a function [lim]
-- that returns a real number for every Cauchy sequence together with a
-- proof that this number is the limit.
-- *)

-- (* Begin_SpecReals *)

-- Record is_CReals (R : COrdField) (lim : CauchySeq R -> R) : CProp :=
--   {ax_Lim  : forall s : CauchySeq R, SeqLimit s (lim s);
--    ax_Arch : forall x : R, {n : nat | x [<=] nring n}}.

-- Record CReals : Type :=
--   {crl_crr   :> COrdField;
--    crl_lim   :  CauchySeq crl_crr -> crl_crr;
--    crl_proof :  is_CReals crl_crr crl_lim}.

-- (* End_SpecReals *)

-- Definition Lim : forall IR : CReals, CauchySeq IR -> IR := crl_lim.

-- Arguments Lim [IR].
