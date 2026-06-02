/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import LeanPool.ErdosTuzaValtr.Lib.List.Default
import LeanPool.ErdosTuzaValtr.Lib.Core.Rel3

/-!
# LeanPool.ErdosTuzaValtr.Config.Defs

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Config.Defs`.
-/


/-- A configuration: a decidable ternary "cup" relation on a linearly ordered type. -/
structure Config (α : Type _) [LinearOrder α] where
  /-- The ternary cup relation of the configuration. -/
  Cup3 : α → α → α → Prop
  /-- The cup relation is decidable. -/
  DecidableCup3 : DecidableRel3 Cup3
namespace Config

variable {α : Type _} [ord : LinearOrder α] (C : Config α)

attribute [instance] Config.DecidableCup3

/-- The 3-cap relation is the negation of the 3-cup relation. -/
def Cap3 (a b c : α) : Prop :=
  ¬C.Cup3 a b c

/-- The 3-cap relation is decidable. -/
@[reducible]
def DecidableCap3 : DecidableRel3 C.Cap3 := fun a b c => @instDecidableNot _ (C.DecidableCup3 a b c)

attribute [instance] DecidableCap3

/-- A cap is a strictly increasing list whose consecutive triples are 3-caps. -/
def Cap (l : List α) : Prop :=
  l.IsChain (· < ·) ∧ l.Chain3' C.Cap3

/-- A cup is a strictly increasing list whose consecutive triples are 3-cups. -/
def Cup (l : List α) : Prop :=
  l.IsChain (· < ·) ∧ l.Chain3' C.Cup3

/-- A gon is a cap and a cup of length at least 2 sharing their first and last endpoints. -/
@[simp]
def Gon (l1 l2 : List α) : Prop :=
  2 ≤ l1.length ∧
    C.Cap l1 ∧ 2 ≤ l2.length ∧ C.Cup l2 ∧ l1.head? = l2.head? ∧ l1.getLast? = l2.getLast?

instance DecidableCup {l : List α} : Decidable (C.Cup l) := by rw [Cup]; infer_instance

/-- An `n`-cap is a cap of length `n`. -/
def NCap (n : ℕ) (l : List α) : Prop :=
  C.Cap l ∧ l.length = n

/-- An `n`-cup is a cup of length `n`. -/
def NCup (n : ℕ) (l : List α) : Prop :=
  C.Cup l ∧ l.length = n

/-- An `n`-gon is a gon whose cap and cup lengths sum to `n + 2`. -/
def NGon (n : ℕ) (l1 l2 : List α) : Prop :=
  C.Gon l1 l2 ∧ l1.length + l2.length = n + 2

/-- A finset has an `n`-cap if some `n`-cap lies inside it. -/
def HasNCap (n : ℕ) (S : Finset α) : Prop :=
  ∃ l : List α, C.NCap n l ∧ l.In S

/-- A finset has an `n`-cup if some `n`-cup lies inside it. -/
def HasNCup (n : ℕ) (S : Finset α) : Prop :=
  ∃ l : List α, C.NCup n l ∧ l.In S

/-- A finset has an `n`-gon if some `n`-gon lies inside it. -/
def HasNGon (n : ℕ) (S : Finset α) : Prop :=
  ∃ l1 l2 : List α, C.NGon n l1 l2 ∧ l1.In S ∧ l2.In S

end Config
