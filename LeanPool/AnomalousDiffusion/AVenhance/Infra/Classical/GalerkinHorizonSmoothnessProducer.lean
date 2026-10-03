/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinHorizonSmoothnessBoundary
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinHorizonConsistency

/-! Joint smoothness of the closed unit-slab Galerkin limit from its spatial word family. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open AVenhance.Infra.Torus

namespace AVenhance.Infra.Classical

theorem GalerkinHorizonSmoothnessProducer.classicalBoundaryClamp_continuous :
    Continuous classicalGalerkinUnitSlabClamp := by
  exact Continuous.subtype_mk
    (continuous_const.max (continuous_const.min continuous_id))
    (fun s => ⟨le_max_left _ _, (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩⟩)

theorem GalerkinHorizonSmoothnessProducer.classicalBoundaryToTorus_continuous : Continuous
    (toUnitTorus 2) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)

/-- The real spatial derivative word of the limiting Galerkin lift, clamped to the unit slab. -/
noncomputable def classicalGalerkinUnitWordFamily
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    List (Fin 2) → ℝ × Vec 2 → ℝ := fun w p =>
  classicalWordDerivative w
    (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
      (classicalGalerkinUnitSlabClamp p.1)) p.2

/-- The spatial word of the physical equation right-hand side on the clamped unit slab. -/
noncomputable def classicalGalerkinUnitWordRhs
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    List (Fin 2) → ℝ × Vec 2 → ℝ := fun w p =>
  classicalWordDerivative w (fun y =>
    F (classicalGalerkinUnitSlabClamp p.1) y +
      κ * AVenhance.spaceLap
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp p.1)) y -
      classicalTransport (AVenhance.streamVel φ (classicalGalerkinUnitSlabClamp p.1))
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp p.1)) y) p.2

theorem classicalGalerkinUnitWordFamily_continuous
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    Continuous (classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w) := by
  let g : Icc (0 : ℝ) 1 × Vec 2 → ℝ := fun p =>
    classicalWordDerivative w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per p.1) p.2
  let m : ℝ × Vec 2 → Icc (0 : ℝ) 1 × Vec 2 := fun p =>
    (classicalGalerkinUnitSlabClamp p.1, p.2)
  have hm : Continuous m :=
    (GalerkinHorizonSmoothnessProducer.classicalBoundaryClamp_continuous.comp
        continuous_fst).prodMk continuous_snd
  have hg : Continuous g := by
    change Continuous (fun p : Icc (0 : ℝ) 1 × Vec 2 =>
      classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per p.1) p.2)
    exact classicalGalerkinWordLift_jointContinuous
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w
  change Continuous (g ∘ m)
  exact hg.comp hm

theorem classicalGalerkinUnitWordRhs_eq_torusPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (p : ℝ × Vec 2) :
    classicalGalerkinUnitWordRhs φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w p =
      (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w
        (classicalGalerkinUnitSlabClamp p.1, toUnitTorus 2 p.2)).re := by
  rw [classicalGalerkinSmoothWordRhsJointPath_apply_toEuclidean]
  simp [classicalGalerkinUnitWordRhs]

theorem classicalGalerkinUnitWordRhs_continuous
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    Continuous (classicalGalerkinUnitWordRhs φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w) := by
  rw [show classicalGalerkinUnitWordRhs φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w =
      fun p => (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w
        (classicalGalerkinUnitSlabClamp p.1, toUnitTorus 2 p.2)).re by
      funext p
      exact classicalGalerkinUnitWordRhs_eq_torusPath
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w p]
  exact (Complex.reCLM.continuous.comp
    ((classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).continuous.comp
        ((GalerkinHorizonSmoothnessProducer.classicalBoundaryClamp_continuous.comp
            continuous_fst).prodMk
          (GalerkinHorizonSmoothnessProducer.classicalBoundaryToTorus_continuous.comp
              continuous_snd))))

end AVenhance.Infra.Classical

end
