/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import LeanPool.NandakumarRamanaRao.NRR.BodySpace
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody
public import LeanPool.NandakumarRamanaRao.NRR.Multivalued
public import LeanPool.NandakumarRamanaRao.NRR.TestMap.EquivarianceCore

/-!
# Phase interfaces for the prime configuration model

This module collects the stable APIs established before the prime-equivariant layer.  It contains
no new mathematical assertion; later `PrimeModel` modules import this file rather than depending on
implementation details of the hyperspace, variable-body, or multivalued-function developments.
-/

@[expose] public section

namespace NRR

namespace PrimeModel

/-- Site families used to construct the model's power-diagram partitions. -/
abbrev SiteFamily := EMP.VariableBody.SiteFamily

end PrimeModel

end NRR
