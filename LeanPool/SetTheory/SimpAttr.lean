/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Lean

/-!
# Simp attributes for the ZF realization machinery

This module registers the custom `simp` attributes used to drive the formula-realization
and elementary-embedding automation in the rest of the development.
-/

/-- Simp set for unfolding `Formula.Realize` of the generated ZF formulas. -/
register_simp_attr realize_simps
/-- Simp set for pushing an elementary embedding through set-theoretic operations. -/
register_simp_attr elementary_simps
/-- Reverse-direction simp set for elementary embeddings. -/
register_simp_attr elementary_simps_rev
/-- Simp set for the `toV` map from a model into the von Neumann universe. -/
register_simp_attr toV_simps
/-- Simp set for the `toZFSet` map from a model into `ZFSet`. -/
register_simp_attr toZFSet_simps
/-- Simp set used while building first-order formulas from set-theoretic predicates. -/
register_simp_attr formula_builder
/-- Pre-processing simp set used before building first-order formulas. -/
register_simp_attr formula_builder_pre
