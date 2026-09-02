/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import LeanPool.CommonNeighbourConjecture.Examples.MainTheorems.Internal

/-!
# Proof alias for the public theorem statement

These term macros hide the definitional transport from the internal proof
bundle to the deliberately duplicated reader-facing definitions.
-/

/-- Transport the internal construction to the reader-facing permutation-group bundle. -/
macro "mainTheorem_from_internal" "(" B:term "," degreeBound:term ","
    hB:term ")" : term => do
  let publicGroup := Lean.mkIdent
    `SaxlCounterexamples.MainTheorems.FinitePermutationGroup
  let publicBaseSize := Lean.mkIdent
    `SaxlCounterexamples.MainTheorems.FinitePermutationGroup.baseSize
  let publicIsBase := Lean.mkIdent
    `SaxlCounterexamples.MainTheorems.FinitePermutationGroup.IsBase
  let publicSaxlGraph := Lean.mkIdent
    `SaxlCounterexamples.MainTheorems.FinitePermutationGroup.saxlGraph
  `(by
    obtain ⟨Q, hQ⟩ :=
      SaxlCounterexamples.MainTheorems.Internal.mainTheorem
        $B $degreeBound $hB
    let P : $publicGroup := {
      G := Q.G
      Point := Q.Point
      group := Q.group
      action := Q.action
      finiteGroup := Q.finiteGroup
      finitePoint := Q.finitePoint
      faithful := Q.faithful }
    refine ⟨P, ?_⟩
    simpa only [P,
      $(publicBaseSize):term, $(publicIsBase):term,
      $(publicSaxlGraph):term,
      SaxlCounterexamples.MainTheorems.Core.FinitePermutationGroup.baseSize,
      SaxlCounterexamples.MainTheorems.Core.FinitePermutationGroup.IsBase,
      SaxlCounterexamples.MainTheorems.Core.FinitePermutationGroup.saxlGraph]
      using hQ)
