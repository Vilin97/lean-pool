/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.SeparatorCertificate
import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.ProjectedZeroSet
import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.Core
import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.IndexedPartition
import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.Iteration
import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.FlexibleCore
import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.FlexibleIteration

/-!
# `NRR.PrimeRefinement` — prime refinement after the Fox--Neuwirth separator

This aggregator exposes the exact separator contract and the fully proved conversion from a
separator certificate to the next nice multivalued function and its canonical partition witness.
-/
