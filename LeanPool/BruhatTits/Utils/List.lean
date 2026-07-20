/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/

import Batteries.Data.List.Basic
import Mathlib.Logic.Function.Basic

/-!
# LeanPool.BruhatTits.Utils.List
-/

theorem List.zipWith₃_map {α α' β β' γ γ' δ : Type*} (f : α' → β' → γ' → δ)
    (fa : α → α') (fb : β → β') (fc : γ → γ')
    (la : List α) (lb : List β) (lc : List γ) :
    List.zipWith₃ f (la.map fa) (lb.map fb) (lc.map fc) =
      List.zipWith₃ (fun a b c ↦ f (fa a) (fb b) (fc c)) la lb lc := by
  match la, lb, lc with
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | (a :: as), (b :: bs), (c :: cs) =>
      exact congrArg (List.cons (f (fa a) (fb b) (fc c)))
        (List.zipWith₃_map f fa fb fc as bs cs)
