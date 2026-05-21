/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

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

-- Require Export CoRN.model.ordfields.Qordfield.
-- Require Export CoRN.reals.Cauchy_CReals.

-- (**
-- * Cauchy Real Numbers
-- Earlier we defined a construction of a real number structure from an
-- arbitrary archimedian ordered field.  Plugging in [Q] we get the model
-- of the real numbers as Cauchy sequences of rationals.
-- *)

-- Definition Cauchy_IR : CReals := R_as_CReals _ Q_is_archemaedian.

-- (** The term [Cauchy_IR] is of type [CReals]. *)

-- Close Scope Q_scope.
