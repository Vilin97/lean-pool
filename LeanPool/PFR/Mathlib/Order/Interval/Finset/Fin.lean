/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Order.Interval.Finset.Fin

/-!
# Order intervals in `Fin`
-/

open Finset

namespace Fin

public
lemma Iio_succ_eq_Iic_castSucc {n : ℕ} (k : Fin n) : Iio k.succ = Iic k.castSucc := rfl

end Fin
