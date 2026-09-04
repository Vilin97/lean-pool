/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.GeneralMain
import LeanPool.Wallace.RealMain
import LeanPool.Wallace.TychonoffWallace

/-!
# The Wallace problem in ZFC

Source: arxiv:2608.17317, doi:10.48550/arXiv.2608.17317, url:https://github.com/vo-rodrigues/wallace-problem-zfc-paper
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
Status: verified
Main declarations: `Wallace.commutativeTychonoffWallaceCounterexampleExists`
Tags: wallace-problem, topological-groups, set-theoretic-topology
MSC: 22A05, 54D30, 20K20
-/

/-!
# Countably compact groups and the Wallace counterexample

This library proves the paper's main theorem for every torsion-free Abelian group of cardinality
continuum.  It also exposes the free, rational, real, and Baer--Specker specializations.  The
nonnegative cone in the free Abelian group gives a commutative Tychonoff countably compact
cancellative topological additive monoid which is not a group.  The internal Section 10
propositions on large closures and suitable sets are included as well.

The public entry point exposes the three principal statements from the paper.
-/
