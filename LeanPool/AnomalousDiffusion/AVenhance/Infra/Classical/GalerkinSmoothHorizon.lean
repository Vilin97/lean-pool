/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothPDE

/-! Integer-horizon rescaling for the smooth unit-slab Galerkin limit. -/

@[expose] public section

noncomputable section

open Set
open Homogenization

namespace AVenhance.Infra.Classical

/-- Rescale an admissible stream by an integer time horizon, including the chain-rule factor. -/
def classicalGalerkinHorizonStream (N : ℕ) (φ : ℝ → Vec 2 → ℝ) :
    ℝ → Vec 2 → ℝ := fun s x => (N : ℝ) * φ ((N : ℝ) * s) x

/-- Rescale the forcing by the time-chain-rule factor on an integer horizon. -/
def classicalGalerkinHorizonForcing (N : ℕ) (F : ℝ → Vec 2 → ℝ) :
    ℝ → Vec 2 → ℝ := fun s x => (N : ℝ) * F ((N : ℝ) * s) x

theorem classicalGalerkinHorizonStream_admissible (N : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ) :
    AVenhance.IsAdmissibleStream (classicalGalerkinHorizonStream N φ) := by
  constructor
  · have hscale : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => ((N : ℝ) * p.1, p.2)) := by fun_prop
    have hcomp := hφ.1.comp hscale
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => (N : ℝ) * Function.uncurry φ
        ((N : ℝ) * p.1, p.2))
    exact contDiff_const.mul hcomp
  · intro n k s x
    change (N : ℝ) * φ ((N : ℝ) * (s + (n : ℝ)))
      (x + AVenhance.latticeShift k) = (N : ℝ) * φ ((N : ℝ) * s) x
    have hn : (N : ℝ) * (n : ℝ) = ((N : ℤ) * n : ℝ) := by norm_cast
    have hshift : (N : ℝ) * s + (N : ℝ) * (n : ℝ) =
        (N : ℝ) * s + ((N : ℤ) * n : ℝ) := by rw [hn]
    rw [show (N : ℝ) * (s + (n : ℝ)) =
        (N : ℝ) * s + (N : ℝ) * (n : ℝ) by ring, hshift]
    have hperiod := hφ.2 ((N : ℤ) * n) k ((N : ℝ) * s) x
    have hperiod' : φ ((N : ℝ) * s + (N : ℝ) * (n : ℝ))
        (x + AVenhance.latticeShift k) = φ ((N : ℝ) * s) x := by
      push_cast at hperiod
      exact hperiod
    exact congrArg (fun y : ℝ => (N : ℝ) * y) hperiod'

theorem classicalGalerkinHorizonForcing_smooth (N : ℕ)
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry (classicalGalerkinHorizonForcing N F))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  let S : ℝ × Vec 2 → ℝ × Vec 2 := fun p => ((N : ℝ) * p.1, p.2)
  have hS : ContDiff ℝ (⊤ : ℕ∞) S := by fun_prop
  have hmaps : MapsTo S (Set.Ici (0 : ℝ) ×ˢ Set.univ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    rcases Set.mem_prod.mp hp with ⟨ht, hx⟩
    refine ⟨?_, trivial⟩
    change 0 ≤ (N : ℝ) * p.1
    exact mul_nonneg (Nat.cast_nonneg N) ht
  have hcomp := hF.comp hS.contDiffOn hmaps
  change ContDiffOn ℝ (⊤ : ℕ∞)
    (fun p : ℝ × Vec 2 => (N : ℝ) * Function.uncurry F (S p))
    (Set.Ici (0 : ℝ) ×ˢ Set.univ)
  exact contDiffOn_const.mul hcomp

theorem classicalGalerkinHorizonForcing_periodic (N : ℕ)
    (F : ℝ → Vec 2 → ℝ)
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t)) :
    ∀ t, 0 ≤ t →
      AVenhance.IsZ2Periodic (classicalGalerkinHorizonForcing N F t) := by
  intro t ht z x
  change (N : ℝ) * F ((N : ℝ) * t) (x + AVenhance.latticeShift z) = _
  exact congrArg (fun y : ℝ => (N : ℝ) * y)
    (hFper ((N : ℝ) * t) (mul_nonneg (Nat.cast_nonneg N) ht) z x)

theorem classicalGalerkinHorizonStreamVel_eq (N : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (s : ℝ) (x : Vec 2) :
    AVenhance.streamVel (classicalGalerkinHorizonStream N φ) s x =
      (N : ℝ) • AVenhance.streamVel φ ((N : ℝ) * s) x := by
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (φ ((N : ℝ) * s)) := by
    have hpair : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => ((N : ℝ) * s, y)) := contDiff_const.prodMk contDiff_id
    have h := hφ.1.comp hpair
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => Function.uncurry φ ((N : ℝ) * s, y)) at h
    exact h
  have hgrad (i : Fin 2) :
      AVenhance.spaceGrad (fun y => (N : ℝ) * φ ((N : ℝ) * s) y) x i =
        (N : ℝ) * AVenhance.spaceGrad (φ ((N : ℝ) * s)) x i := by
    change fderiv ℝ ((N : ℝ) • φ ((N : ℝ) * s)) x
      (Homogenization.basisVec i) = _
    rw [fderiv_const_smul (hslice.differentiable (by simp) x) (N : ℝ)]
    rfl
  change AVenhance.sigmaMat.mulVec
      (AVenhance.spaceGrad (fun y => (N : ℝ) * φ ((N : ℝ) * s) y) x) = _
  rw [show AVenhance.spaceGrad (fun y => (N : ℝ) * φ ((N : ℝ) * s) y) x =
      (N : ℝ) • AVenhance.spaceGrad (φ ((N : ℝ) * s)) x by
    ext i
    exact hgrad i]
  simp only [Matrix.mulVec_smul]
  rfl

/-- The Galerkin limit on an arbitrary positive integer horizon, obtained by rescaling the
unit-slab construction. -/
noncomputable def classicalGalerkinHorizonLimit
    (N : ℕ) (hN : 0 < N)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) : ℝ → Vec 2 → ℝ := by
  let φN := classicalGalerkinHorizonStream N φ
  let hφN := classicalGalerkinHorizonStream_admissible N φ hφ
  let κN := (N : ℝ) * κ
  have hκN : 0 < κN := mul_pos (Nat.cast_pos.mpr hN) hκ
  let FN := classicalGalerkinHorizonForcing N F
  let hFN := classicalGalerkinHorizonForcing_smooth N F hF
  let hFNper := classicalGalerkinHorizonForcing_periodic N F hFper
  exact fun t x => classicalGalerkinRealSmoothLift φN hφN κN hκN FN hFN hFNper
    θ₀ hθ₀ hθ₀per
      (classicalGalerkinUnitSlabClamp (t / (N : ℝ))) x

theorem classicalGalerkinHorizonLimit_periodic
    (N : ℕ) (hN : 0 < N)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : ℝ) :
    AVenhance.IsZ2Periodic (classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t) := by
  exact classicalGalerkinRealSmoothLift_periodic
    (classicalGalerkinHorizonStream N φ)
    (classicalGalerkinHorizonStream_admissible N φ hφ) ((N : ℝ) * κ)
    (mul_pos (Nat.cast_pos.mpr hN) hκ)
    (classicalGalerkinHorizonForcing N F)
    (classicalGalerkinHorizonForcing_smooth N F hF)
    (classicalGalerkinHorizonForcing_periodic N F hFper)
    θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp (t / (N : ℝ)))

theorem classicalGalerkinHorizonLimit_initial
    (N : ℕ) (hN : 0 < N)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∀ x, classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per 0 x = θ₀ x := by
  have hbase := classicalGalerkinRealSmoothLift_initial
    (classicalGalerkinHorizonStream N φ)
    (classicalGalerkinHorizonStream_admissible N φ hφ) ((N : ℝ) * κ)
    (mul_pos (Nat.cast_pos.mpr hN) hκ)
    (classicalGalerkinHorizonForcing N F)
    (classicalGalerkinHorizonForcing_smooth N F hF)
    (classicalGalerkinHorizonForcing_periodic N F hFper) θ₀ hθ₀ hθ₀per
  have hzero : (0 : ℝ) / (N : ℝ) = 0 := by
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']
    ring
  have hcl0 : classicalGalerkinUnitSlabClamp ((0 : ℝ) / (N : ℝ)) =
      ⟨0, by norm_num, by norm_num⟩ := by
    apply Subtype.ext
    simp [hzero, classicalGalerkinUnitSlabClamp]
  intro x
  simp only [classicalGalerkinHorizonLimit]
  rw [hcl0]
  exact hbase x

theorem classicalGalerkinHorizonLimit_advDiffOp
    (N : ℕ) (hN : 0 < N)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (N : ℝ)) (x : Vec 2) :
    AVenhance.advDiffOp (AVenhance.streamVel φ) κ
      (classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per) t x = F t x := by
  let c : ℝ := (N : ℝ)
  have hc : 0 < c := Nat.cast_pos.mpr hN
  let s : ℝ := t / c
  have hs : s ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos ht.1 hc
    · exact (div_lt_one hc).2 (by simpa [c] using ht.2)
  have hcs : c * s = t := by
    dsimp [s]
    field_simp [hc.ne']
  let φN := classicalGalerkinHorizonStream N φ
  let hφN := classicalGalerkinHorizonStream_admissible N φ hφ
  let κN := c * κ
  have hκN : 0 < κN := mul_pos hc hκ
  let FN := classicalGalerkinHorizonForcing N F
  let hFN := classicalGalerkinHorizonForcing_smooth N F hF
  let hFNper := classicalGalerkinHorizonForcing_periodic N F hFper
  let uS : ℝ → Vec 2 → ℝ := fun r y =>
    classicalGalerkinRealSmoothLift φN hφN κN hκN FN hFN hFNper
      θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp r) y
  have hclS : classicalGalerkinUnitSlabClamp s = ⟨s, le_of_lt hs.1, le_of_lt hs.2⟩ := by
    apply Subtype.ext
    simp [classicalGalerkinUnitSlabClamp, max_eq_right (le_of_lt hs.1),
      min_eq_right (le_of_lt hs.2)]
  have hunit := classicalGalerkinUnitLimit_advDiffOp
    φN hφN κN hκN FN hFN hFNper θ₀ hθ₀ hθ₀per hs x
  have hunitEq : deriv (fun r => uS r x) s - c * κ *
      AVenhance.spaceLap (uS s) x +
        Homogenization.vecDot (AVenhance.streamVel φN s x)
          (AVenhance.spaceGrad (uS s) x) = FN s x := by
    simpa [uS, AVenhance.advDiffOp, κN, hclS,
      classicalGalerkinHorizonStream, classicalGalerkinHorizonForcing] using hunit
  have hunitPoint := classicalGalerkinWordPointwise_hasDerivAt
    φN hφN κN hκN FN hFN hFNper θ₀ hθ₀ hθ₀per [] x hs
  have hpoint : HasDerivAt (fun r => uS r x)
      (FN s x + κN * AVenhance.spaceLap (uS s) x -
        classicalTransport (AVenhance.streamVel φN s) (uS s) x) s := by
    simpa [uS, classicalWordDerivative, hclS] using hunitPoint
  have hscaledVel : AVenhance.streamVel φN s x =
      c • AVenhance.streamVel φ t x := by
    rw [classicalGalerkinHorizonStreamVel_eq N φ hφ s x, hcs]
  have hscaledForce : FN s x = c * F t x := by
    change c * F (c * s) x = c * F t x
    rw [hcs]
  have hdot : Homogenization.vecDot
      (c • AVenhance.streamVel φ t x) (AVenhance.spaceGrad (uS s) x) =
      c * Homogenization.vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (uS s) x) := by
    simp [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul]
    ring
  have hunitValue : deriv (fun r => uS r x) s =
      c * F t x + c * κ * AVenhance.spaceLap (uS s) x -
        c * Homogenization.vecDot (AVenhance.streamVel φ t x)
          (AVenhance.spaceGrad (uS s) x) := by
    have hEq := hunitEq
    rw [hscaledVel, hdot, hscaledForce] at hEq
    linarith
  have harg : HasDerivAt (fun r : ℝ => r / c) c⁻¹ t := by
    simpa [one_div] using (hasDerivAt_id t).div_const c
  have hchain := hpoint.comp t harg
  have hthetaDeriv : deriv
      (fun r => classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per r x) t =
        deriv (fun r => uS r x) s * c⁻¹ := by
    have hfun : (fun r => classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per r x) = (fun r => uS (r / c) x) := by
      funext r
      simp [classicalGalerkinHorizonLimit, uS, φN, κN, FN, c]
    rw [hfun]
    calc
      deriv (fun r => uS (r / c) x) t =
          (FN s x + κN * AVenhance.spaceLap (uS s) x -
            classicalTransport (AVenhance.streamVel φN s) (uS s) x) * c⁻¹ := by
        simpa [Function.comp_def, s] using hchain.deriv
      _ = deriv (fun r => uS r x) s * c⁻¹ := by rw [← hpoint.deriv]
  have hderivValue : deriv
      (fun r => classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per r x) t =
      F t x + κ * AVenhance.spaceLap (uS s) x -
        Homogenization.vecDot (AVenhance.streamVel φ t x)
          (AVenhance.spaceGrad (uS s) x) := by
    rw [hthetaDeriv, hunitValue]
    field_simp [hc.ne']
  have hslice : classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t = uS s := by
    funext y
    simp [classicalGalerkinHorizonLimit, uS, φN, κN, FN, c, s]
  change deriv (fun r => classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per r x) t - κ * AVenhance.spaceLap
        (classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per t) x +
      Homogenization.vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per t) x) = F t x
  rw [hderivValue, hslice]
  ring

end AVenhance.Infra.Classical

end
