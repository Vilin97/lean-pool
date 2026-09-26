/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2025 Aaron Liu. All rights reserved.
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Aaron Liu, Apurva Nakade, Fox Thomson, František Silváši,
Isabel Longbottom, Junyan Xu, Kim Morrison, Mario Carneiro, Reid Barton, Theodore Hwa,
Violeta Hernández Palacios, Yuyang Zhao
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Multiplication

/-! # Cut-defined omnific integers in the shared surreal-number model

The first-principles indexed-game statement remains in `InlineConwayRefinement`.
Its proof bridges directly to the imported CombinatorialGames implementation.
-/

@[expose] public noncomputable section
universe u
namespace ConwayRefinement.Standalone.InlineSurreal.Surreal

/-- The singleton Conway cut `{x - 1 | x + 1}`. -/
def singletonIntegerCut (x : _root_.Surreal.{u}) : _root_.Surreal.{u} :=
  !{{x - 1} | {x + 1}}' (by
    simp only [Set.mem_singleton_iff]
    rintro _ rfl _ rfl
    simp [sub_eq_add_neg])

/-- Conway's cut equation defining an omnific integer. -/
def IsConwayOmnificInteger (x : _root_.Surreal.{u}) : Prop :=
  x = singletonIntegerCut x

/-- Conway's refinement conjecture for the concretely defined surreal numbers. -/
def ConwayConjecture : Prop :=
  ∀ a b c d : _root_.Surreal.{u},
    IsConwayOmnificInteger a → IsConwayOmnificInteger b →
    IsConwayOmnificInteger c → IsConwayOmnificInteger d → a * b = c * d →
    ∃ e f g h : _root_.Surreal.{u},
      IsConwayOmnificInteger e ∧ IsConwayOmnificInteger f ∧
      IsConwayOmnificInteger g ∧ IsConwayOmnificInteger h ∧
      a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h

end ConwayRefinement.Standalone.InlineSurreal.Surreal
