/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PairingPos
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTPad
import LeanPool.RegtsSevenster.RS.Common.FactorialBound

/-!
# The Schur package, unconditionally

Discharging the padding and branching inputs: the classical
symmetric-group representation theory consumed by the development
is a theorem of this tree.
-/

namespace RS

open scoped Classical in
/-- **The Schur package.** -/
noncomputable def schurPackage : SchurPackage.{u} :=
  schurPackageOf three_pow_mul_factorial_ge
    (fun lam mu hle h =>
      branching_of_pairing lam mu h
        (restrPairing_ne_zero
          (fun μ {_k} hk π => jtChar_pad μ hk π) lam mu hle h))

end RS
