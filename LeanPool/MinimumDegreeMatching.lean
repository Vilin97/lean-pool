/-
Copyright (c) 2026 Juan Pablo Traverso Gianini and Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import LeanPool.MinimumDegreeMatching.Basic

/-!
# Perfect and near-perfect matchings from minimum degree

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_III/05_formalization/lean_v1.4_freeze/PaperIII/Contrib/Submission
Authors: Juan Pablo Traverso Gianini, Aristotle
Status: verified
Main declarations: `SimpleGraph.exists_isPerfectMatching_of_minDegree`
Tags: graph-theory, perfect-matchings, minimum-degree
MSC: 05C70
-/

/-!
## Mathematical overview

This project derives perfect and near-perfect matchings from sharp minimum-degree hypotheses.
The even case uses Mathlib's formalization of Tutte's theorem. The odd case adjoins a universal
apex, applies the even result, and then deletes the edge incident to the apex.
-/
