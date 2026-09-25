/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


-- The minimal tricycle: discrete and metric divisorial gonality really are
-- different (van Dobben de Bruyn--Smit--van der Wegen, JCTA 189 (2022) 105619,
-- arXiv:2106.12568), and Baker's Conjecture 3.14(a) is therefore false.
--
-- This application library imports only `Utilities` and external dependencies.
-- Its declarations use the `Utilities.Tricycle` and `Utilities.Gonality`
-- namespaces.

-- The tricycle core, its explicit potential, and the `IsTricycle` predicate.
public import LeanPool.BrillNoetherGraphs.Tricycle.Core
-- The upper bounds: `dgon(T_m) <= 6` and `dgon(sigma_2 T_m) <= 5`.
public import LeanPool.BrillNoetherGraphs.Tricycle.UpperBounds
-- Lemmas 3.5/3.6 and Corollary 3.7: every subdivision has `dgon >= 5`.
public import LeanPool.BrillNoetherGraphs.Tricycle.HelperLemma
public import LeanPool.BrillNoetherGraphs.Tricycle.Degree5
-- Identifies `regularSubdivision` on the occurrence presentation with slot
-- scaling of a unit-length `Spec`, so the gap can be stated for a bare
-- `CFGraph`.
public import LeanPool.BrillNoetherGraphs.Tricycle.RegularSubdivisionBridge
-- Theorem 3.9 and the assembled counterexample.
public import LeanPool.BrillNoetherGraphs.Tricycle.Gap

-- A one-file public interface: the library's main theorems restated in full
-- and checked by the kernel against the real declarations.
public import LeanPool.BrillNoetherGraphs.Tricycle.Highlights

/-! # Tricycle -/

@[expose] public section
