/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.PhaseInterfaces
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ZeroSumAlgebra
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.CoordinateDecomposition
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.PrimeSymmetry
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.Actions
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.FixedVectors
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.EquivariantMap
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.Model
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ModelSites
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ChildEquivariance
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ChildTestMap
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.BoundaryOrthants
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.AugmentedReference

/-!
# Prime configuration-model interface

This public aggregator exposes the algebraic and equivariant layer used by the prime-refinement
argument: the prime symmetry subgroup, zero-sum coordinate decomposition, abstract compact
configuration models, equivariant power-diagram children, child-evaluation test maps, endpoint
orthants, and the bounded augmented reference map.

It does not assert existence of the concrete polyhedral model and does not contain a PL
transversality, orbit-count, or separation theorem.
-/
