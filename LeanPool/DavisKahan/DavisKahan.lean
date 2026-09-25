/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.All
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.All
public import LeanPool.DavisKahan.DavisKahan.Sources.All

/-!
# Davis--Kahan perturbation theory

The deliberate public umbrella: supported bounded-operator and
finite-dimensional theory together with the production source aggregate.
Specialized endpoints, alternative proofs, and experiments require explicit
imports.
-/

@[expose] public section
