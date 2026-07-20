/-
Copyright (c) 2026 Tomasz Maciosowski, Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski, Alfie Davies
-/
module

public import LeanPool.MisereGames.AugmentedForm
public import LeanPool.MisereGames.AugmentedForm.Lift
public import LeanPool.MisereGames.AugmentedForm.Short
public import LeanPool.MisereGames.Form
public import LeanPool.MisereGames.Form.Adjoint
public import LeanPool.MisereGames.Form.Birthday
public import LeanPool.MisereGames.Form.Classes
public import LeanPool.MisereGames.Form.Misere.Adjoint
public import LeanPool.MisereGames.Form.Misere.Outcome
public import LeanPool.MisereGames.Form.Short
public import LeanPool.MisereGames.GameForm
public import LeanPool.MisereGames.GameForm.Birthday
public import LeanPool.MisereGames.GameForm.Special
public import LeanPool.MisereGames.GameGraph
public import LeanPool.MisereGames.Literature.OnSumsOfPFreeFormsUnderMiserePlay
public import LeanPool.MisereGames.Mathlib.NatOrdinal
public import LeanPool.MisereGames.Mathlib.SimpleGraph
public import LeanPool.MisereGames.Mathlib.Small
public import LeanPool.MisereGames.Misere.Ambient
public import LeanPool.MisereGames.Misere.Blocking
public import LeanPool.MisereGames.Misere.Closures
public import LeanPool.MisereGames.Misere.Comparison
public import LeanPool.MisereGames.Misere.DeadEnding
public import LeanPool.MisereGames.Misere.Hereditary.MaintenanceProviso
public import LeanPool.MisereGames.Misere.IntegerInvertible
public import LeanPool.MisereGames.Misere.LiftIncomparable
public import LeanPool.MisereGames.Misere.NonInvertible
public import LeanPool.MisereGames.Misere.Normal
public import LeanPool.MisereGames.Misere.OutcomeStable
public import LeanPool.MisereGames.Misere.OutcomeStable.PropertyX
public import LeanPool.MisereGames.Misere.PFree
public import LeanPool.MisereGames.Misere.PFreeBlocking
public import LeanPool.MisereGames.Misere.PFreeDeadEnding
public import LeanPool.MisereGames.Misere.Preservation
public import LeanPool.MisereGames.Misere.Quotients
public import LeanPool.MisereGames.Misere.Separation
public import LeanPool.MisereGames.Misere.ShortIncomparable
public import LeanPool.MisereGames.Misere.Stride
public import LeanPool.MisereGames.Misere.TippingPoints
public import LeanPool.MisereGames.Misere.Universe
public import LeanPool.MisereGames.OfSets
public import LeanPool.MisereGames.Outcome
public import LeanPool.MisereGames.Player
public import LeanPool.MisereGames.Ruleset
public import LeanPool.MisereGames.Ruleset.Hackenbush
public import LeanPool.MisereGames.Ruleset.Push
public import LeanPool.MisereGames.Ruleset.Shove
public import LeanPool.MisereGames.Ruleset.Strip
public import LeanPool.MisereGames.Tactic.DocAlias

/-!
# Misere combinatorial games

Source: url:https://github.com/t4ccer/misere-games
Authors: Tomasz Maciosowski, Alfie Davies
Status: verified
Main declarations: `MisereGames.Form.Promain.of_universe`
Tags: combinatorial-games, misere-play, game-theory
MSC: 91A46, 05C57
-/
