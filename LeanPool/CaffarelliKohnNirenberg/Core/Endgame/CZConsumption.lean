/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZInputs
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ExtensionNormTransport

/-! # Conditional norm transport to a selected extension representative

An indexed operator's strong bound on compactly supported L^(6/5) inputs
and the selected operator's component bounds imply the vector-valued
gradient bound. The weak-gradient construction in `WeakCZConsumption`
supplies the separate distributional pairing and does not identify a rough
classical representative.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

/-- Transport an indexed extension's L^(6/5) bounds and aggregate the three
output coordinates. -/
theorem hasCZGradientBound_of_extension_component_bounds
    (Ccomp C_CZ : ℝ) (hCcomp : 0 ≤ Ccomp) (hconst : 3 * Ccomp ≤ C_CZ)
    (T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ)
    (hbound : ∀ i j (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      eLpNorm (T i j G) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
        ENNReal.ofReal Ccomp * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    CKN.Foundation.Euclidean.HasCZGradientOperatorBound T C_CZ := by
  apply hCZ_grad_of_component_bounds hCcomp hconst
  intro i j G hG hGc
  exact hbound i j G hG hGc



end CKN.Core.Endgame
