/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.All
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.AllGap
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.Equation
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.FormBoundedGap
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.IntervalExterior
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.Neumann
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedCutoff
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedEngine
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedEngineDirect
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedFromCutoffs

/-! Supporting modules for Davis–Kahan rotation of eigenvectors. -/
