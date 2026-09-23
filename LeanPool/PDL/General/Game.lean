/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.Lean4GlCoalgebras.Pdl.Game

/-! # Shared finite, well-founded game theory

PDL completeness uses the game determinacy library already preserved with the GL
coalgebra development. Its games, strategies, winners and determinacy theorem
coincide with the corresponding upstream PDL infrastructure. The completeness
modules open `Lean4GlCoalgebras` explicitly when using this interface.
-/
