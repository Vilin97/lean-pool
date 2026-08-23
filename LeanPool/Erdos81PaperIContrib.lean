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
Main declarations: `LeanPool.Erdos81PaperIContrib.fg_cone_isClosed`, `LeanPool.Erdos81PaperIContrib.covering_packing_duality`
Tags: convex-geometry, linear-programming, duality, farkas-lemma
MSC: 52A20, 90C05
-/

/-!
## Mathematical overview

This project proves closedness of finitely generated cones, a finite-dimensional Farkas lemma,
and strong duality for finite covering and packing linear programs.
-/
