/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.PhaseInterfaces
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ZeroSumAlgebra
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.CoordinateDecomposition
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.PrimeSymmetry
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.Actions
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.FixedVectors
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.EquivariantMap
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.Model
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ModelSites
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ChildEquivariance
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ChildTestMap
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.BoundaryOrthants
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.AugmentedReference

/-!
# Prime configuration-model interface

This public aggregator exposes the algebraic and equivariant layer used by the prime-refinement
argument: the prime symmetry subgroup, zero-sum coordinate decomposition, abstract compact
configuration models, equivariant power-diagram children, child-evaluation test maps, endpoint
orthants, and the bounded augmented reference map.

It does not assert existence of the concrete polyhedral model and does not contain a PL
transversality, orbit-count, or separation theorem.
-/

@[expose] public section
