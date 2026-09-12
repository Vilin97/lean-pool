/-
Copyright (c) 2026 Juan Pablo Traverso Gianini and Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import LeanPool.MinimumDegreeMatching.Basic
import LeanPool.MinimumDegreeMatching.Spread
import LeanPool.MinimumDegreeMatching.BKLO

/-!
# BKLO simultaneous perfect matchings and spread matchings

Source: arxiv:1410.5750, doi:10.1016/j.aim.2015.09.032
Authors: Juan Pablo Traverso Gianini, Aristotle
Status: verified
Main declarations: `BKLOK2.lemma107K2_holds`
Tags: graph-theory, perfect-matchings, edge-disjoint-matchings, pseudorandomness
MSC: 05C70
-/

/-!
## Mathematical overview

The main result is the `r = 2` specialization of the simultaneous factor-selection step in BKLO
Lemma 10.7. It chooses perfect matchings in a linearly sized, overlapping family of neighbourhood
graphs while keeping their edge sets pairwise disjoint. The formal proof replaces the randomized
greedy process in the published argument with a deterministic pessimistic-estimator sweep.

The supporting matching library proves perfect and near-perfect matching results from sharp
minimum-degree hypotheses. Iteration under degree slack produces edge-disjoint perfect matchings,
and averaging gives the weighted spread estimate used by the selector.
-/
