/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import LeanPool.ErdosTuzaValtr.Config.Default
import LeanPool.ErdosTuzaValtr.Etv.Default

open scoped Classical

noncomputable section

variable {α : Type _} [LinearOrder α] (C : Config α)

def Config.MainGoal (n : ℕ) : Prop :=
  ∀ S : Finset α,
    Nat.choose (n + 2) 2 + 2 ≤ S.card →
      ¬C.HasNCap 4 S → ¬C.HasNCup (n + 3) S → ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s

def Config.MainGoalWlog (n : ℕ) : Prop :=
  ∀ S : Finset α,
    ¬C.HasJoin (n + 2) (n + 1) S →
      Nat.choose (n + 2) 2 + 2 ≤ S.card →
        ¬C.HasNCap 4 S → ¬C.HasNCup (n + 3) S → ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s
