/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import LeanPool.InflationTermination.TriangleInflation.Defs
public import LeanPool.InflationTermination.TriangleInflation.Finner
public import LeanPool.InflationTermination.TriangleInflation.FinnerMeasure
public import LeanPool.InflationTermination.TriangleInflation.Defect
public import LeanPool.InflationTermination.TriangleInflation.DefectLaw
public import LeanPool.InflationTermination.TriangleInflation.Main
public import LeanPool.InflationTermination.TriangleInflation.Fan
public import LeanPool.InflationTermination.TriangleInflation.Exponent
public import LeanPool.InflationTermination.TriangleInflation.Rate
public import LeanPool.InflationTermination.TriangleInflation.ConvexOrder
public import LeanPool.InflationTermination.TriangleInflation.Graph

/-!
# Inflation for classical pair-source networks

Definitions and theorems for the manuscript *Inflation for Classical Pair-Source Networks:
Termination and Quantitative Obstructions* (included under `paper/`). Every theorem in this
directory is proved; `Audit.lean` checks that the transitive axioms are `propext`,
`Classical.choice` and `Quot.sound` only.

Two developments live here. The triangle modules (`TriangleInflation/*.lean`) carry the
nontermination theorem for the classical triangle and the quantitative work around it, and
`FinnerMeasure.lean` upgrades the Finner inequality, and with it the nontermination theorem,
to arbitrary measurable latent spaces. The graph modules (`TriangleInflation/Graph/*.lean`)
carry the pair-source generalization and the classification theorem: a finite order of the
Navascués–Wolfe hierarchy characterizes compatibility exactly when every connected component
of the observed graph is a double star.

The formalization boundaries are recorded in the header of `TriangleInflation/Defs.lean`, in
the header of `TriangleInflation/Graph/Defs.lean` and in `README.md`.

The two registry statements are `Palomar/TriangleInflation/ClassificationChallenge.lean` and
`Palomar/TriangleInflation/Challenge.lean`, proved in
`PalomarSolutions/TriangleInflationClassification.lean` and
`PalomarSolutions/TriangleInflation.lean`.
-/
