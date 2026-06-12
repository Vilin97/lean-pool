/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/

import LeanPool.LowDimSolvClassification.Classification1
import LeanPool.LowDimSolvClassification.Classification2
import LeanPool.LowDimSolvClassification.Classification3
import LeanPool.LowDimSolvClassification.GeneralResults
import LeanPool.LowDimSolvClassification.InstancesConstructions
import LeanPool.LowDimSolvClassification.InstancesLowDim
import LeanPool.LowDimSolvClassification.LemmasDim3
import LeanPool.LowDimSolvClassification.QuotientSolvable
import LeanPool.LowDimSolvClassification.Semidirect
import LeanPool.LowDimSolvClassification.Tactics

/-!
# Classification of low-dimensional solvable Lie algebras

Source: doi:10.1090/crmm/033, url:https://bookstore.ams.org/crmm-33
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
Status: verified
Main declarations: `LieAlgebra.Dim3.classification`
Tags: lie-algebras, solvable, classification
MSC: 17B30
-/

/-!
## Mathematical overview

Formalization in Lean 4 of the classification of solvable Lie algebras of
dimension zero to three, over arbitrary fields where possible, building on
Mathlib's Lie algebra library.

The development covers:

- General Lie-theoretic infrastructure (`GeneralResults`, `QuotientSolvable`,
  `Semidirect`, `Tactics`).
- Concrete low-dimensional models (`InstancesConstructions`, `InstancesLowDim`).
- Classification theorems for each dimension (`Classification1`,
  `Classification2`, `Classification3`) plus supporting lemmas (`LemmasDim3`).

The main classification theorems are
`LieAlgebra.Dim1.classification`, `LieAlgebra.Dim2.classification`, and
the dimension-three results gathered in `LeanPool.LowDimSolvClassification.Classification3`.
-/
