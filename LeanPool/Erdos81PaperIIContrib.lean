/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

import LeanPool.Erdos81PaperIIContrib.Chordal

/-!
# Chordal graphs and induced-subgraph heredity

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_II
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `SimpleGraph.IsChordal.comap`
Tags: graph-theory, chordal-graphs, induced-subgraphs
MSC: 05C75
-/

/-!
## Mathematical overview

This project defines chordal graphs using the cycle-and-chord characterization and proves that
chordality is inherited along induced graph embeddings and by induced subgraphs.
-/
