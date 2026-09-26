/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineThetaSourceInventory
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Theorem61
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Proposition61

/-!
# Trusted-dependency audit for the literal paper sine-theta surface

This file is intentionally excluded from ordinary aggregates because its print
commands produce audit output.  Compile it directly after every successful
build of the exact-paper modules and require only Lean's standard foundational
dependencies in every result.
-/

@[expose] public section
