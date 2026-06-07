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

register_simp_attr realize_simps
register_simp_attr elementary_simps
register_simp_attr elementary_simps_rev
register_simp_attr toV_simps
register_simp_attr toZFSet_simps
register_simp_attr formula_builder
register_simp_attr formula_builder_pre
