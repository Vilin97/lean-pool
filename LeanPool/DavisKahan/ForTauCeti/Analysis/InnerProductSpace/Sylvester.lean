/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Basic
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.BlockEstimate
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.BlockIdentity
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Generator
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Group
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Interval
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Operator
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralDistance
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralGap

/-! Supporting modules for Davis–Kahan rotation of eigenvectors. -/
