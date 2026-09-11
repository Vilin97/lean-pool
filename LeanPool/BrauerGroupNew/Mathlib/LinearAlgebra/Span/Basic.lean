/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Span compatibility imports

The upstream file supplied `Submodule.mem_span_image_finset_iff_exists_fun`;
that declaration is available in current Mathlib from
`Mathlib.LinearAlgebra.Finsupp.LinearCombination`, so this file is kept as an
import-compatible shim.
-/

@[expose] public section
