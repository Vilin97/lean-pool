/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

import LeanPool.DavisKahan.DavisKahan.Sylvester.All
import LeanPool.DavisKahan.DavisKahan.Sylvester.Bounded
import LeanPool.DavisKahan.DavisKahan.Sylvester.ClosedSylvesterEquation
import LeanPool.DavisKahan.DavisKahan.Sylvester.CutoffInterface
import LeanPool.DavisKahan.DavisKahan.Sylvester.FilledTruncation
import LeanPool.DavisKahan.DavisKahan.Sylvester.FiniteBlockReconstruction
import LeanPool.DavisKahan.DavisKahan.Sylvester.FiniteStepCalculus
import LeanPool.DavisKahan.DavisKahan.Sylvester.Gap
import LeanPool.DavisKahan.DavisKahan.Sylvester.HomogeneousUniqueness
import LeanPool.DavisKahan.DavisKahan.Sylvester.OrthogonalIdempotentExp
import LeanPool.DavisKahan.DavisKahan.Sylvester.PairwiseHomogeneousUniqueness
import LeanPool.DavisKahan.DavisKahan.Sylvester.PairwiseSpectrumGap
import LeanPool.DavisKahan.DavisKahan.Sylvester.RealUnbounded
import LeanPool.DavisKahan.DavisKahan.Sylvester.RosenblumExistence
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.DavisKahan.Sylvester.ShiftedInverse
import LeanPool.DavisKahan.DavisKahan.Sylvester.ShiftedInverseGauge
import LeanPool.DavisKahan.DavisKahan.Sylvester.Spectrum
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded

/-! Supporting modules for Davis–Kahan rotation of eigenvectors. -/
