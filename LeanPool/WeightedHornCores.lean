/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import LeanPool.WeightedHornCores.RealBound
public import LeanPool.WeightedHornCores.UnaryChain

/-!
# Small unsatisfiable cores in weighted Horn formulas

Source: url:https://github.com/lockwo/lean-pool/tree/6b48b5f93366c7528bd1bc679341d9c953d1f412/LeanPool/WeightedHornCores
Authors: Weighted Horn Cores contributors
Status: verified
Main declarations: `WeightedHornCores.exists_positive_core`
Tags: Horn satisfiability, unsatisfiable cores, proof complexity
MSC: 03B05, 68Q25
-/

/-!
## Mathematical overview

The cardinality bound counts distinct original Horn clauses. Its exponent depends on the
weight of positive rules with two premises, rather than on the whole formula weight. See
`WeightedHornCores.exists_positive_core` for the real estimate, or
`WeightedHornCores.exists_core_of_budgets` for a version using integer budgets. The unary
chain shows that the linear dependence on total weight divided by minimum loss is necessary
already without any branching rules.
-/
