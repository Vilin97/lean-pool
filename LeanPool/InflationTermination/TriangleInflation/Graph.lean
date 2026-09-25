/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import LeanPool.InflationTermination.TriangleInflation.Graph.Defs
public import LeanPool.InflationTermination.TriangleInflation.Graph.Flips
public import LeanPool.InflationTermination.TriangleInflation.Graph.Soundness
public import LeanPool.InflationTermination.TriangleInflation.Graph.RootSink
public import LeanPool.InflationTermination.TriangleInflation.Graph.Triangle
public import LeanPool.InflationTermination.TriangleInflation.Graph.DoubleStar
public import LeanPool.InflationTermination.TriangleInflation.Graph.FivePath
public import LeanPool.InflationTermination.TriangleInflation.Graph.Cycles
public import LeanPool.InflationTermination.TriangleInflation.Graph.Linear
public import LeanPool.InflationTermination.TriangleInflation.Graph.Transport
public import LeanPool.InflationTermination.TriangleInflation.Graph.Classification
public import LeanPool.InflationTermination.TriangleInflation.Graph.DoubleStarForest
public import LeanPool.InflationTermination.TriangleInflation.Graph.CycleWitness
public import LeanPool.InflationTermination.TriangleInflation.Graph.CycleObstruction
public import LeanPool.InflationTermination.TriangleInflation.Graph.FivePathWitness
public import LeanPool.InflationTermination.TriangleInflation.Graph.TriangleWitness
public import LeanPool.InflationTermination.TriangleInflation.Graph.SquareWitness
public import LeanPool.InflationTermination.TriangleInflation.Graph.ClassificationTheorem

/-!
# Inflation for pair-source graphs

The pair-source generalization of `TriangleInflation`: a finite simple graph without
isolated vertices, one binary observed variable per vertex, one independent latent source per
edge. `TriangleInflation/Graph/Defs.lean` carries the definitions (scenarios, copied
observations, the
`NW`, `AI` and recursively expressible tests, compatibility, the named scenarios and the
explicit targets). The other modules carry the proved results of the manuscript's pair-source
sections: local flips, soundness and nesting of the three tests, the root-sink lemma
(`gExpFeasible_iff_gAIFeasible`), the bridge to the triangle module, the double-star
reconstruction (`doubleStar_terminates`), the five-path target with the bilocal inequality,
its distance bound and its witness at every order (`fivePath_witness`), the cycle target with
parity rigidity, its witness at every order (`cycle_witness`), incompatibility and distance
(`cycle_distance`, through the quantitative rigidity `CycleModelAux.quant_rigidity`), the
corrected Fourier density with its positivity and moment table and the triangle witness at
`q = 1/(16t)` (`triangle_linear_witness`), induced-subgraph transport, the exhaustion lemma,
and the classification theorem itself (`classification_NW_lib`, `classification_AI`,
`classification_exp`).

Every module here is proved and is imported by the library root. The one statement of the
pair-source sections that is not yet proved, the square witness at `q = 1/(16t)`
(`square_linear_witness`), is not part of this repository at all: the verification gate
refuses an open proof outside the two Challenges. The Coverage table in `README.md` records
which paper statements each proved declaration covers.
-/
