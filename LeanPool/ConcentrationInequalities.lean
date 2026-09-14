/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import LeanPool.ConcentrationInequalities.BennettBernstein
import LeanPool.ConcentrationInequalities.ConditionalHoeffding
import LeanPool.ConcentrationInequalities.FreedmanBernstein
import LeanPool.ConcentrationInequalities.HoeffdingUpper

/-!
# Bennett--Bernstein, Freedman, and Hoeffding concentration inequalities

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/b3423f3e8c8db7c2d1b279673293ef3079faf903/preprints/PAPER_III/05_formalization/lean_v1.4_freeze/Contrib/FreedmanBernstein.lean
Authors: Juan Pablo Traverso Gianini, Aristotle
Status: verified
Main declarations: `Contrib.Freedman.subgamma_bernstein_tail`
Tags: probability-theory, concentration-inequalities, martingales
MSC: 60E15, 60G42
-/

/-!
# Variance-sensitive and finite concentration inequalities

This project develops Bennett--Bernstein sub-gamma estimates, a Freedman--Bernstein inequality for
adapted sums, and conditional and independent-variable Hoeffding bounds.
-/
