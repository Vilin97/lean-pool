/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.All

/-!
# Dependency audit for Davis--Kahan 1970 Section 8: internal infrastructure

**This is not the audit of the printed theorems.**  The declarations below are
the conditional bridges and abstract cores that Section 8's analytic layer and
Section 9's continuation layer consume: they take caller-supplied data records
-- a `SpectralContinuationWitness`, a half-gap bridge, an abstract quadratic
block record -- which the paper *proves* rather than assumes.  They are useful
and their trusted-dependency reports are clean, and that is all this
leaf certifies.

The audit of the actual Section 8 capstones is
`DavisKahan/Audits/Section8.lean`, which must live downstream of the analytic
layer because that is where Section 8's analytic content is.  It checks
Theorem 8.1's branch, characterization and uniqueness; parts (i), (ii) and (iii)
for both blocks including the every-symmetric-gauge forms; the eigenvalue/angle
source dictionary; and both Theorem 8.2 alternatives together with the printed
`Theta < pi/4`.

The trusted-dependency reports here should contain only the standard
classical/choice foundations inherited from the spectral calculus, and nothing
project-local.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace Section8

end Section8
end DavisKahan1970
end TauCeti
