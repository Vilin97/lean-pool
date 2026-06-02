/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Util.Notation3
public import Mathlib.Tactic.Basic

/-!
# LeanPool.ZhangYeungInequality.PFR.ForMathlib.Pair

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.PFR.ForMathlib.Pair`.
-/

public section

/-- The pair of two random variables -/
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)

@[inherit_doc prod] scoped[ZhangYeungPFR] notation3:100 "⟨" X ", " Y "⟩" => prod X Y

open scoped ZhangYeungPFR

@[simp]
lemma prod_eq {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} :
    (⟨ X, Y ⟩ : Ω → S × T) ω = (X ω, Y ω) := rfl
