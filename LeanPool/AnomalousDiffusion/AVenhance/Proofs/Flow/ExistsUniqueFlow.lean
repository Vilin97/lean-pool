/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.GlobalExistence

/-! # Exists Unique Flow

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization

namespace AVenhance.Proofs

/-- Provider for the globally well-posed flow of a continuous uniformly
globally Lipschitz vector field. -/
theorem existsUnique_flow (b : ℝ → Vec 2 → Vec 2)
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) :
    ∃! X, AVenhance.IsFlow b X :=
  AVenhance.Infra.Flow.existsUnique_flow b hb hL

end AVenhance.Proofs
