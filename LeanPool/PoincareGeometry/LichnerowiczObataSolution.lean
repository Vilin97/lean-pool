/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.StatementEquivalence

/-! # Lichnerowicz Obata Solution -/

@[expose] public noncomputable section

namespace LichnerowiczObataEntry.Geometry

universe u v w

/-- The full theorem follows from the original geometric proof through the
proved definitional equivalence; no hypotheses or conclusions are changed. -/
theorem lichnerowiczObata : completeStatement.{u,v,w} := by
  exact completeStatement_proved

end LichnerowiczObataEntry.Geometry
