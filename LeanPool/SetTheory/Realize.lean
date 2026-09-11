/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
module

public meta import LeanPool.SetTheory.RealizeCore
public import LeanPool.SetTheory.RealizeCore

/-!
# Elaboration of serialized ZF expressions

The implementation is imported at the meta phase so its expression decoders can execute
inside term elaborators while their data definitions and correctness lemmas remain available.
-/

public meta section

open Lean Meta Elab Term

namespace EncodeExpr

elab_rules : term
  | `(headBeta($t:term)) => do
    let result ← elabTerm t none
    return result.headBeta
  | `(expr($e:str)) => do
    let value := ((Json.parse e.getString) >>= fromJson? : Except _ WeakExpr).toOption.get!.toExpr
    let levels := (collectLevelParams {} value).params.toList
    let mvars ← mkFreshLevelMVars levels.length
    return value.instantiateLevelParams levels mvars

end EncodeExpr
