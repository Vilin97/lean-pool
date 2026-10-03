/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.ScaleTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Source-scale estimate for the transport term `twistie1`. The §3/§4
spatial L² estimate and the source mean condition remain explicit inputs. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

end AVenhance.Infra.Section5
end
