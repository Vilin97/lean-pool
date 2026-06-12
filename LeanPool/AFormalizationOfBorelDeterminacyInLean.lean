/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Undetermined

/-!
# A formalization of Borel determinacy in Lean

Source: arxiv:2502.03432
Authors: Sven Manthe
Status: verified
Main declarations: `GaleStewartGame.borel_determinacy`, `GaleStewartGame.Games.borel_determinacy`
Tags: descriptive-set-theory, game-theory, determinacy
MSC: 03E15, 54H05, 91A44
-/

/-!
## Mathematical overview

This project formalizes Martin's theorem on Borel determinacy for
Gale-Stewart games. It develops trees of finite positions and infinite
branches, strategies and quasi-strategies, closed determinacy, and the
covering/unravelling machinery used for the inductive proof of Borel
determinacy.

The import also includes applications to Choquet-style and Banach-Mazur-style
games on topological spaces.
-/
