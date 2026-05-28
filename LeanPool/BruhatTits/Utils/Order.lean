/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/

import Mathlib.Order.Hom.Basic

variable {α β : Type*} [PartialOrder α] [PartialOrder β] (f : α ≃o β)

lemma OrderIso.map_top_iff [OrderTop α] [OrderTop β] (x : α) :
    f x = ⊤ ↔ x = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ f.map_top⟩
  rw [← f.symm_apply_apply x, h, f.symm.map_top]

lemma OrderIso.map_bot_iff [OrderBot α] [OrderBot β] (x : α) :
    f x = ⊥ ↔ x = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ f.map_bot⟩
  rw [← f.symm_apply_apply x, h, f.symm.map_bot]
