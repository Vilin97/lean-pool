/-
Copyright (c) 2026 Juan Pablo Traverso Gianini and Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import LeanPool.MinimumDegreeMatching.Basic
import LeanPool.MinimumDegreeMatching.Spread

/-!
# Minimum-degree and spread matchings

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/6736c816e1f9cd105c2295a8e4716ad55609ccb0/preprints/PAPER_III/05_formalization/lean_v1.4_freeze
Authors: Juan Pablo Traverso Gianini, Aristotle
Status: verified
Main declarations: `SimpleGraph.exists_isPerfectMatching_of_minDegree`, `SimpleGraph.exists_isMatching_compl_singleton_of_minDegree`, `SimpleGraph.exists_involutions_pairwise_ne`, `SimpleGraph.exists_spread_involution`
Tags: graph-theory, perfect-matchings, minimum-degree, edge-disjoint-matchings, weighted-matchings
MSC: 05C70
-/

/-!
## Mathematical overview

This project develops perfect, near-perfect, edge-disjoint, and weighted spread matchings from
sharp minimum-degree hypotheses. One route uses Mathlib's formalization of Tutte's theorem; a
second, constructive finite-set route proves the perfect-matching result directly by augmentation.
The latter route iterates under degree slack to obtain pairwise edge-disjoint perfect matchings and
then averages over them to produce a matching with a quantitative spread bound.
-/
