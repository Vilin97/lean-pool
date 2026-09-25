/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.SeparatorCertificate
public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.ProjectedZeroSet
public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.Core
public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.IndexedPartition
public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.Iteration
public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.FlexibleCore
public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.FlexibleIteration

/-!
# `NRR.PrimeRefinement` — prime refinement after the Fox--Neuwirth separator

This aggregator exposes the exact separator contract and the fully proved conversion from a
separator certificate to the next nice multivalued function and its canonical partition witness.
-/

@[expose] public section
