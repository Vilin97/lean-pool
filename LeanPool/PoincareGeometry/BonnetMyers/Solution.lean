/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.BonnetMyers.Complete

/-! # Solution -/

noncomputable section

namespace BonnetMyersEntry

universe u v w

/-- The full independently developed Bonnet--Myers theorem closes the exact
Mathlib-only statement selected in `Challenge.lean`. -/
theorem bonnet_myers : completeStatement.{u,v,w} := by
  exact completeStatement_proved

end BonnetMyersEntry
