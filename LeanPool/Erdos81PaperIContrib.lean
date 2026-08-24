/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

import LeanPool.Erdos81PaperIContrib.FarkasLP
import LeanPool.Erdos81PaperIContrib.FgConeClosed

/-!
# Finitely generated cones and finite LP duality

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_I
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `LeanPool.Erdos81PaperIContrib.fg_cone_isClosed`
Tags: convex-geometry, linear-programming, duality, farkas-lemma
MSC: 52A20, 90C05
-/

/-!
## Mathematical overview

This project proves closedness of finitely generated cones, a finite-dimensional Farkas lemma,
and packing attainment with equality to the covering infimum for finite covering and packing
linear programs. The Farkas and LP statements overlap the pooled Duality project's more general
`inequalityFarkas_neg` and `StandardLP.strongDuality` results; the cone-closedness results supply
a direct, topology-facing API not present there.
-/
