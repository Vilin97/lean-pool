/-
Copyright (c) 2026 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/

import LeanPool.FoZfc.Basic
import LeanPool.FoZfc.FixedSnoc
import LeanPool.FoZfc.BoundedFormulaOps
import LeanPool.FoZfc.Tostring
import LeanPool.FoZfc.Axioms
import LeanPool.FoZfc.Replacement

/-!
# First Order Language of ZF Set Theory

Source: url:https://doi.org/10.1007/3-540-44761-X
Authors: Tetsuya Ishiu
Status: verified
Main declarations: `FirstOrder.ZFC.ModelZF`, `FirstOrder.ZFC.ext_induction`
Tags: model-theory, set-theory, zf
MSC: 03B10, 03E30
-/

/-!
## Mathematical overview

A formalization of ZF set theory inside Lean 4's `FirstOrder.Language`
framework so that meta-mathematical arguments such as elementary submodels
and embeddings can be carried out.

The language `FirstOrder.Language.LZFC` consists of a single binary
relation `∈'`. Models of the various axioms are organized as type classes
that extend `FirstOrder.ZFC.ModelSets`:

- `ModelEmptyset`, `ModelPairing`, `ModelUnion`, `ModelPowerset`,
  `ModelInfinity`, `ModelRegularity`, `ModelComprehension`,
  `ModelReplacement`,
- their progressive unions (`ModelEPUP`, `ModelEPUPI`, `ModelEPUPIR`,
  `ModelEPUPIC`),
- and the omnibus `ModelZF`.

For each axiom, both an internal form (a `BoundedFormula` in `LZFC`) and
an external form (a `Prop` over a model `V`) are provided, together with
"`realize`" lemmas relating the two. The development closes with the
principle of mathematical induction for ω in both internal and external
forms (`ext_induction`, `int_induction`).
-/
