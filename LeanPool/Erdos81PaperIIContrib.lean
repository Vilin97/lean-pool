/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

import LeanPool.Erdos81PaperIIContrib.Chordal

/-!
# Chordal graphs: minimal separators and simplicial vertices

Source: url:https://github.com/jtraverso/lean-pool/blob/822738f3089d92c5e65a6bfb8c88c992e4699167/LeanPool/Erdos81PaperIIContrib/Chordal.lean
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `SimpleGraph.IsChordal.exists_two_nonadj_isSimplicial`
Tags: graph-theory, chordal-graphs, induced-subgraphs, minimal-separators, simplicial-vertices
MSC: 05C75
-/

/-!
## Mathematical overview

This reusable formalization byproduct accompanying *Complete-Split Extremizers for a Fractional
Triangle-Cover Functional on Chordal Graphs* defines chordal graphs using the cycle-and-chord
characterization, proves induced-subgraph heredity and the clique property for finite minimal
separators of fixed vertex pairs, proves Dirac's simplicial-vertex theorem, and proves the
connected non-complete case of the two-vertex conclusion.
-/
