/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean
import LeanPool.Lentil.Utils.MetaUtil
import LeanPool.Lentil.Utils.SyntaxUtil
import LeanPool.Lentil.Utils.MiscLemmas

open Lean

/-- Whether to use the custom TLA delaborator when pretty-printing. -/
register_option lentil.pp.useDelab : Bool := {
  defValue := true
  descr := "Use the delaborator from `Lentil.Basic` for delaboration. "
}

/-- Whether to automatically render `satisfies` with the `|=tla=` notation. -/
register_option lentil.pp.autoRenderSatisfies : Bool := {
  defValue := true
  descr := "Automatically render an application `p e` as `e |=tla= p` when `p` is a TLA formula. "
}

/-- Marking the non-temporal parts of TLA. -/
register_simp_attr tla_nontemporal_def

/-- Marking the TLA definitions. -/
register_simp_attr tlasimp_def

/-- Marking the things to simplify when explicitly reasoning about `exec`. -/
register_simp_attr execsimp

/-- Marking the definitions unfolded by `tlaFiniteWindow`. -/
register_simp_attr tla_finite_window_def

/-- Marking the theorems that can be simplify reasoning at the TLA level. -/
register_simp_attr tlasimp

/-- Marking the theorems that are dual to some existing theorems. -/
register_simp_attr tladual

/-- Marking the theorems that are used for normalizing sequents. -/
register_simp_attr tlanormsimp

initialize registerTraceClass `lentil.debug
