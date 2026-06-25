/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

/-
Examples are kept out of `import LeanPool.HighDimProb` so the stable public import stays
focused on the core API. Import this module explicitly when you want the compact
usage surface.

RandomMatrix examples are intentionally routed through `StatementRoutes` instead
of importing every intermediate bridge file here. Focused lower-level examples
can still be imported directly by contributors who need them.
-/

import LeanPool.HighDimProb.Examples.BasicUsage
import LeanPool.HighDimProb.Examples.EmpiricalProcessNetUsage
import LeanPool.HighDimProb.Examples.NetsUsage
import LeanPool.HighDimProb.Examples.OrliczFeatureUsage
import LeanPool.HighDimProb.Examples.OrliczUsage
import LeanPool.HighDimProb.Examples.RandomMatrixUsage
import LeanPool.HighDimProb.Examples.RandomVariableUsage
import LeanPool.HighDimProb.Examples.RandomVectorUsage
import LeanPool.HighDimProb.Examples.TailUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.StatementRoutes
import LeanPool.HighDimProb.Examples.RandomMatrix.SampleCovarianceUsage
