/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import LeanPool.ErdosTuzaValtr.Lib.List.Default
import LeanPool.ErdosTuzaValtr.Lib.Core.Rel3


structure Config (α : Type _) [LinearOrder α] where
  Cup3 : α → α → α → Prop
  DecidableCup3 : DecidableRel3 Cup3
namespace Config

variable {α : Type _} [ord : LinearOrder α] (C : Config α)

attribute [instance] Config.DecidableCup3

-- Notion of 3-caps
def Cap3 (a b c : α) : Prop :=
  ¬C.Cup3 a b c

def DecidableCap3 : DecidableRel3 C.Cap3 := fun a b c => @instDecidableNot _ (C.DecidableCup3 a b c)

attribute [instance] DecidableCap3

-- Notion of caps and cups
def Cap (l : List α) : Prop :=
  l.Chain' (· < ·) ∧ l.Chain3' C.Cap3

def Cup (l : List α) : Prop :=
  l.Chain' (· < ·) ∧ l.Chain3' C.Cup3

@[simp]
def Gon (l1 l2 : List α) : Prop :=
  2 ≤ l1.length ∧
    C.Cap l1 ∧ 2 ≤ l2.length ∧ C.Cup l2 ∧ l1.head? = l2.head? ∧ l1.getLast? = l2.getLast?

instance DecidableCup {l : List α} : Decidable (C.Cup l) := by rw [Cup] <;> infer_instance

def NCap (n : ℕ) (l : List α) : Prop :=
  C.Cap l ∧ l.length = n

def NCup (n : ℕ) (l : List α) : Prop :=
  C.Cup l ∧ l.length = n

def NGon (n : ℕ) (l1 l2 : List α) : Prop :=
  C.Gon l1 l2 ∧ l1.length + l2.length = n + 2

def HasNCap (n : ℕ) (S : Finset α) : Prop :=
  ∃ l : List α, C.NCap n l ∧ l.In S

def HasNCup (n : ℕ) (S : Finset α) : Prop :=
  ∃ l : List α, C.NCup n l ∧ l.In S

def HasNGon (n : ℕ) (S : Finset α) : Prop :=
  ∃ l1 l2 : List α, C.NGon n l1 l2 ∧ l1.In S ∧ l2.In S

end Config
