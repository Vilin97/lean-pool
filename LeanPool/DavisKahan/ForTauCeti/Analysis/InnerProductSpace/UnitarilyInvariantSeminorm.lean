/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Majorization
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Gauge
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Instances

/-!
# Unitarily invariant seminorms

`UnitarilyInvariantSeminorm 𝕜 E F` extends `Seminorm` on rectangular linear maps.
Ky Fan dominance applies on every such map space. Symmetric gauges, adjoints of
endomorphisms, and operator absolute value use the specialization `E = F`.
-/

@[expose] public section
