/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

import LeanPool.Erdos81PaperIIContrib.Chordal

/-!
# Chordal graphs: minimal separators and Dirac's theorem

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/preprints/PAPER_II/05_formalization/lean_v1.2_freeze/Contrib/Submission/Chordal.lean
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `SimpleGraph.IsChordal.comap`,
  `SimpleGraph.IsChordal.minimalSeparator_isClique`,
  `SimpleGraph.IsChordal.exists_isSimplicial`,
  `SimpleGraph.IsChordal.exists_two_nonadj_isSimplicial`
Tags: graph-theory, chordal-graphs, minimal-separators, simplicial-vertices
MSC: 05C75
-/

/-!
## Mathematical overview

This reusable formalization byproduct accompanying *Complete-Split Extremizers for a Fractional
Triangle-Cover Functional on Chordal Graphs* defines chordal graphs using the cycle-and-chord
characterization, proves induced-subgraph heredity and the clique property for minimal vertex
separators, and formalizes both parts of Dirac's theorem on simplicial vertices.
-/
