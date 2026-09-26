/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedSharpEstimates

/-!
# BoundedRiccatiShift (promoted)

**Promoted 2026-07-30 under lane `EXP-PROMOTE-T2T` slice 2.**  This module held
the shift bridge converting ordered spectral separation into the shifted diagonal form bounds
the estimate assumes.

Those declarations now live in their source-facing home,
`DavisKahan/Riccati/BoundedSharpEstimates.lean`, beside the rest of the sharp
bounded Riccati estimates, and are compiled by `defaultTargets` — which this
module never was.

Nothing is restated here.  Names and namespace (`TauCeti.DavisKahanExt`) are
unchanged, so importing this module still supplies them and no sibling needed an
edit.  This file remains only as that re-export and should be deleted once the
nine `BoundedOffDiagonal*` modules are promoted too.
-/

@[expose] public section
