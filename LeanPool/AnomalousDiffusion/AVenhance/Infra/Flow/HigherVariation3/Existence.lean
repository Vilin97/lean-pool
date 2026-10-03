/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC2

/-! The third variational affine system along a smooth flow. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

/-- Three spatial directions embedded into the joint time-space domain. -/
def Existence.spatialDirections3 (h k l : Vec 2) : Fin 3 → ℝ × Vec 2 :=
  fun i => if i = 0 then (0, h) else if i = 1 then (0, k) else (0, l)

/-- Two spatial directions embedded into the joint time-space domain. -/
def Existence.spatialDirections2 (h k : Vec 2) : Fin 2 → ℝ × Vec 2 :=
  fun i => Fin.cases (0, h) (fun _ => (0, k)) i

/-- The third derivative of the vector field evaluated in spatial directions. -/
noncomputable def spatialThirdDerivativeEval
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x h k l : Vec 2) : Vec 2 :=
  iteratedFDeriv ℝ 3 (Function.uncurry b) (t, x) (Existence.spatialDirections3 h k l)

/-- Ordered triple of spatial directions for a third derivative evaluation. -/
def Existence.spatialDirections3Vec (h k l : Vec 2) : Fin 3 → Vec 2 :=
  fun i => if i = 0 then h else if i = 1 then k else l

theorem spatialThirdDerivativeEval_eq_slice
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x h k l : Vec 2) :
    spatialThirdDerivativeEval b t x h k l =
      iteratedFDeriv ℝ 3 (fun y => b t y) x (Existence.spatialDirections3Vec h k l) := by
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let incl : Vec 2 →L[ℝ] (ℝ × Vec 2) := ContinuousLinearMap.inr ℝ ℝ (Vec 2)
  let a : ℝ × Vec 2 := (t, 0)
  let Fs : ℝ × Vec 2 → Vec 2 := fun p => F (p + a)
  have hFs : ContDiff ℝ ∞ Fs := by
    dsimp [Fs, F, a]
    exact hb.smooth.comp (by fun_prop)
  have hslice : (fun y : Vec 2 => b t y) = Fs ∘ incl := by
    funext y
    simp [Fs, F, a, incl, ContinuousLinearMap.inr_apply]
  have hright := incl.iteratedFDeriv_comp_right hFs x (i := 3) (by simp)
  have hadd : iteratedFDeriv ℝ 3 Fs (incl x) = iteratedFDeriv ℝ 3 F (incl x + a) := by
    simpa [Fs] using
      (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F) 3 a (incl x))
  have haddEval := congrArg
    (fun D : _root_.ContinuousMultilinearMap ℝ
      (fun _ : Fin 3 => ℝ × Vec 2) (Vec 2) =>
        D (fun i => (0, Existence.spatialDirections3Vec h k l i))) hadd
  rw [spatialThirdDerivativeEval, hslice, hright]
  have hdirs : Existence.spatialDirections3 h k l =
      fun i => (0, Existence.spatialDirections3Vec h k l i) := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3, Existence.spatialDirections3Vec]
  rw [hdirs]
  simpa [a, F, incl, ContinuousLinearMap.inr_apply] using haddEval.symm

theorem spatialThirdDerivativeEval_add_left
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x h₁ h₂ k l : Vec 2) :
    spatialThirdDerivativeEval b t x (h₁ + h₂) k l =
      spatialThirdDerivativeEval b t x h₁ k l +
        spatialThirdDerivativeEval b t x h₂ k l := by
  rw [spatialThirdDerivativeEval_eq_slice hb, spatialThirdDerivativeEval_eq_slice hb,
    spatialThirdDerivativeEval_eq_slice hb]
  have hdirs : Existence.spatialDirections3Vec (h₁ + h₂) k l =
      Function.update (Existence.spatialDirections3Vec h₁ k l) 0 (h₁ + h₂) := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  have hleft : Function.update (Existence.spatialDirections3Vec h₁ k l) 0 h₁ =
      Existence.spatialDirections3Vec h₁ k l := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  have hright : Function.update (Existence.spatialDirections3Vec h₁ k l) 0 h₂ =
      Existence.spatialDirections3Vec h₂ k l := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  rw [hdirs, ContinuousMultilinearMap.map_update_add, hleft, hright]

theorem spatialThirdDerivativeEval_add_middle
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x h k₁ k₂ l : Vec 2) :
    spatialThirdDerivativeEval b t x h (k₁ + k₂) l =
      spatialThirdDerivativeEval b t x h k₁ l +
        spatialThirdDerivativeEval b t x h k₂ l := by
  rw [spatialThirdDerivativeEval_eq_slice hb, spatialThirdDerivativeEval_eq_slice hb,
    spatialThirdDerivativeEval_eq_slice hb]
  have hdirs : Existence.spatialDirections3Vec h (k₁ + k₂) l =
      Function.update (Existence.spatialDirections3Vec h k₁ l) 1 (k₁ + k₂) := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  have hleft : Function.update (Existence.spatialDirections3Vec h k₁ l) 1 k₁ =
      Existence.spatialDirections3Vec h k₁ l := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  have hright : Function.update (Existence.spatialDirections3Vec h k₁ l) 1 k₂ =
      Existence.spatialDirections3Vec h k₂ l := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  rw [hdirs, ContinuousMultilinearMap.map_update_add, hleft, hright]

theorem spatialThirdDerivativeEval_add_right
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x h k l₁ l₂ : Vec 2) :
    spatialThirdDerivativeEval b t x h k (l₁ + l₂) =
      spatialThirdDerivativeEval b t x h k l₁ +
        spatialThirdDerivativeEval b t x h k l₂ := by
  rw [spatialThirdDerivativeEval_eq_slice hb, spatialThirdDerivativeEval_eq_slice hb,
    spatialThirdDerivativeEval_eq_slice hb]
  have hdirs : Existence.spatialDirections3Vec h k (l₁ + l₂) =
      Function.update (Existence.spatialDirections3Vec h k l₁) 2 (l₁ + l₂) := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  have hleft : Function.update (Existence.spatialDirections3Vec h k l₁) 2 l₁ =
      Existence.spatialDirections3Vec h k l₁ := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  have hright : Function.update (Existence.spatialDirections3Vec h k l₁) 2 l₂ =
      Existence.spatialDirections3Vec h k l₂ := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  rw [hdirs, ContinuousMultilinearMap.map_update_add, hleft, hright]

theorem spatialThirdDerivativeEval_smul_left
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x : Vec 2) (c : ℝ) (h k l : Vec 2) :
    spatialThirdDerivativeEval b t x (c • h) k l =
      c • spatialThirdDerivativeEval b t x h k l := by
  rw [spatialThirdDerivativeEval_eq_slice hb, spatialThirdDerivativeEval_eq_slice hb]
  have hdirs : Existence.spatialDirections3Vec (c • h) k l =
      Function.update (Existence.spatialDirections3Vec h k l) 0 (c • h) := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  have hleft : Function.update (Existence.spatialDirections3Vec h k l) 0 h =
      Existence.spatialDirections3Vec h k l := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  rw [hdirs, ContinuousMultilinearMap.map_update_smul, hleft]

theorem spatialThirdDerivativeEval_smul_middle
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x : Vec 2) (c : ℝ) (h k l : Vec 2) :
    spatialThirdDerivativeEval b t x h (c • k) l =
      c • spatialThirdDerivativeEval b t x h k l := by
  rw [spatialThirdDerivativeEval_eq_slice hb, spatialThirdDerivativeEval_eq_slice hb]
  have hdirs : Existence.spatialDirections3Vec h (c • k) l =
      Function.update (Existence.spatialDirections3Vec h k l) 1 (c • k) := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  have hleft : Function.update (Existence.spatialDirections3Vec h k l) 1 k =
      Existence.spatialDirections3Vec h k l := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  rw [hdirs, ContinuousMultilinearMap.map_update_smul, hleft]

theorem spatialThirdDerivativeEval_smul_right
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x : Vec 2) (c : ℝ) (h k l : Vec 2) :
    spatialThirdDerivativeEval b t x h k (c • l) =
      c • spatialThirdDerivativeEval b t x h k l := by
  rw [spatialThirdDerivativeEval_eq_slice hb, spatialThirdDerivativeEval_eq_slice hb]
  have hdirs : Existence.spatialDirections3Vec h k (c • l) =
      Function.update (Existence.spatialDirections3Vec h k l) 2 (c • l) := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  have hleft : Function.update (Existence.spatialDirections3Vec h k l) 2 l =
      Existence.spatialDirections3Vec h k l := by
    funext i
    fin_cases i <;> simp [Existence.spatialDirections3Vec, Function.update]
  rw [hdirs, ContinuousMultilinearMap.map_update_smul, hleft]

/-- Periodicity gives a uniform trilinear bound for the third spatial
derivative of the field. -/
theorem exists_global_spatialThirdDerivativeEval_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x h k l,
      ‖spatialThirdDerivativeEval b t x h k l‖ ≤ C * ‖h‖ * ‖k‖ * ‖l‖ := by
  obtain ⟨C, hC₀, hC⟩ := exists_global_iteratedFDeriv_bound hb 3
  refine ⟨C, hC₀, ?_⟩
  intro t x h k l
  have hprod : (∏ i : Fin 3, ‖Existence.spatialDirections3 h k l i‖) =
      ‖h‖ * ‖k‖ * ‖l‖ := by
    simp [Existence.spatialDirections3, Fin.prod_univ_succ]
    ring
  calc
    ‖spatialThirdDerivativeEval b t x h k l‖ ≤
        ‖iteratedFDeriv ℝ 3 (Function.uncurry b) (t, x)‖ *
          ∏ i : Fin 3, ‖Existence.spatialDirections3 h k l i‖ := by
      exact (iteratedFDeriv ℝ 3 (Function.uncurry b) (t, x)).le_opNorm _
    _ ≤ C * (‖h‖ * ‖k‖ * ‖l‖) := by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right (hC (t, x)) (by positivity)
    _ = C * ‖h‖ * ‖k‖ * ‖l‖ := by ring

/-- The third spatial derivative evaluation is globally Lipschitz in its base
point, with a constant uniform in time and the three directions. -/
theorem exists_global_spatialThirdDerivativeEval_lipschitz
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y h k l,
      ‖spatialThirdDerivativeEval b t x h k l -
        spatialThirdDerivativeEval b t y h k l‖ ≤
          C * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
  obtain ⟨C₄, hC₄₀, hC₄⟩ := exists_global_iteratedFDeriv_bound hb 4
  refine ⟨C₄, hC₄₀, ?_⟩
  intro t x y h k l
  let f : Vec 2 → Vec 2 := fun z => b t z
  let G : Vec 2 → _root_.ContinuousMultilinearMap ℝ
      (fun _ : Fin 3 => Vec 2) (Vec 2) :=
    fun z => iteratedFDeriv ℝ 3 f z
  let m : Fin 3 → Vec 2 := Existence.spatialDirections3Vec h k l
  have hf : ContDiff ℝ ∞ f := by
    exact hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hthree : (3 : ℕ∞ω) < ∞ := by
    change (↑(3 : ℕ∞) : ℕ∞ω) < (↑(⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 3)
  have hG : Differentiable ℝ G := by
    exact hf.differentiable_iteratedFDeriv hthree
  have hGderiv : ∀ z, ‖fderiv ℝ G z‖ ≤ C₄ := by
    intro z
    rw [norm_fderiv_iteratedFDeriv]
    let F : ℝ × Vec 2 → Vec 2 := Function.uncurry b
    let incl : Vec 2 →L[ℝ] (ℝ × Vec 2) := ContinuousLinearMap.inr ℝ ℝ (Vec 2)
    let a : ℝ × Vec 2 := (t, 0)
    let Fs : ℝ × Vec 2 → Vec 2 := fun p => F (p + a)
    have hFs : ContDiff ℝ ∞ Fs := by
      dsimp [Fs, F, a]
      exact hb.smooth.comp (by fun_prop)
    have hright := incl.iteratedFDeriv_comp_right hFs z (i := 4) (by simp)
    have hadd : iteratedFDeriv ℝ 4 Fs (incl z) =
        iteratedFDeriv ℝ 4 F (incl z + a) := by
      simpa [Fs] using
        (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F) 4 a (incl z))
    calc
      ‖iteratedFDeriv ℝ 4 f z‖ =
          ‖(iteratedFDeriv ℝ 4 Fs (incl z)).compContinuousLinearMap
            (fun _ => incl)‖ := by
              rw [show f = Fs ∘ incl by
                funext w
                simp [f, Fs, F, a, incl, ContinuousLinearMap.inr_apply], hright]
      _ ≤ ‖iteratedFDeriv ℝ 4 Fs (incl z)‖ *
          ∏ _i : Fin 4, ‖incl‖ :=
        _root_.ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ 4 F (incl z + a)‖ * 1 := by
        rw [hadd]
        have hincl : ‖incl‖ ≤ 1 := by
          simpa [incl] using
            (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := ℝ) (F := Vec 2))
        have hprod : (∏ _i : Fin 4, ‖incl‖) ≤ 1 := by
          apply Finset.prod_le_one₀
          · intro i hi
            positivity
          · intro i hi
            exact hincl
        exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ ≤ C₄ := by
        simpa [F, a, incl, ContinuousLinearMap.inr_apply] using hC₄ (t, z)
  have hGlip : ‖G x - G y‖ ≤ C₄ * ‖x - y‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hG z) (fun z _ => hGderiv z) (Set.mem_univ _) (Set.mem_univ _)
  have hEval (z : Vec 2) :
      spatialThirdDerivativeEval b t z h k l = G z m := by
    rw [spatialThirdDerivativeEval_eq_slice hb]
  have hprod : (∏ i : Fin 3, ‖m i‖) = ‖h‖ * ‖k‖ * ‖l‖ := by
    simp [m, Existence.spatialDirections3Vec, Fin.prod_univ_succ]
    ring
  calc
    ‖spatialThirdDerivativeEval b t x h k l -
        spatialThirdDerivativeEval b t y h k l‖ = ‖(G x - G y) m‖ := by
          rw [hEval x, hEval y]
          simp
    _ ≤ ‖G x - G y‖ * ∏ i : Fin 3, ‖m i‖ := (G x - G y).le_opNorm m
    _ ≤ (C₄ * ‖x - y‖) * (‖h‖ * ‖k‖ * ‖l‖) := by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right hGlip (by positivity)
    _ = C₄ * ‖x - y‖ * ‖h‖ * ‖k‖ * ‖l‖ := by ring

theorem Existence.continuous_spatialSecondDerivativeEval_along
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s : ℝ) (u v : ℝ → Vec 2)
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun q => spatialSecondDerivativeEval b q (X q x s) (u q) (v q)) := by
  have hcurve : Continuous (fun q : ℝ => (q, X q x s)) :=
    continuous_id.prodMk (flow_continuous_time b hX x s)
  have hD : Continuous (fun q : ℝ =>
      iteratedFDeriv ℝ 2 (Function.uncurry b) (q, X q x s)) :=
    (hb.smooth.continuous_iteratedFDeriv (m := 2) (by simp)).comp hcurve
  have hdirs : Continuous (fun q : ℝ => Existence.spatialDirections2 (u q) (v q)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun q : ℝ => (0, u q))
      exact continuous_const.prodMk hu
    · change Continuous (fun q : ℝ => (0, v q))
      exact continuous_const.prodMk hv
  have hEval : Continuous
      (fun z : _root_.ContinuousMultilinearMap ℝ
        (fun _ : Fin 2 => ℝ × Vec 2) (Vec 2) × (Fin 2 → ℝ × Vec 2) =>
          z.1 z.2) := by fun_prop
  change Continuous (fun q =>
    iteratedFDeriv ℝ 2 (Function.uncurry b) (q, X q x s)
      (Existence.spatialDirections2 (u q) (v q)))
  have hcomp := hEval.comp (hD.prodMk hdirs)
  convert hcomp using 1
  funext q
  rfl

/-- The third variational equation has a unique global solution. Its forcing
is the sum of the third field derivative on three first variations and the
three second-derivative/second-variation terms. -/
theorem existsUnique_flow_thirdVariationCandidate
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k l : Vec 2) :
    ∃! W : ℝ → Vec 2 → ℝ → Vec 2,
      AVenhance.IsFlow (fun t w =>
        jointSpatialFDeriv b t (X t x s) w +
          spatialThirdDerivativeEval b t (X t x s)
            (V t h s) (V t k s) (V t l s) +
          spatialSecondDerivativeEval b t (X t x s)
            (flowSecondVariation hb hX x s hV h k t 0 s) (V t l s) +
          spatialSecondDerivativeEval b t (X t x s)
            (flowSecondVariation hb hX x s hV h l t 0 s) (V t k s) +
          spatialSecondDerivativeEval b t (X t x s)
            (flowSecondVariation hb hX x s hV k l t 0 s) (V t h s)) W := by
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun t => jointSpatialFDeriv b t (X t x s)
  have hA : Continuous A := by
    exact (jointSpatialFDeriv_continuous hb).comp
      (continuous_id.prodMk (flow_continuous_time b hX x s))
  have hVh : Continuous (fun t => V t h s) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hV.2 h s t).continuousAt
  have hVk : Continuous (fun t => V t k s) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hV.2 k s t).continuousAt
  have hVl : Continuous (fun t => V t l s) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hV.2 l s t).continuousAt
  let Whk : ℝ → Vec 2 := fun t => flowSecondVariation hb hX x s hV h k t 0 s
  let Whl : ℝ → Vec 2 := fun t => flowSecondVariation hb hX x s hV h l t 0 s
  let Wkl : ℝ → Vec 2 := fun t => flowSecondVariation hb hX x s hV k l t 0 s
  have hWhk : Continuous Whk := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (flowSecondVariation_isFlow hb hX x s hV h k).2 0 s t |>.continuousAt
  have hWhl : Continuous Whl := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (flowSecondVariation_isFlow hb hX x s hV h l).2 0 s t |>.continuousAt
  have hWkl : Continuous Wkl := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (flowSecondVariation_isFlow hb hX x s hV k l).2 0 s t |>.continuousAt
  let F : ℝ → Vec 2 := fun t =>
    spatialThirdDerivativeEval b t (X t x s) (V t h s) (V t k s) (V t l s) +
      spatialSecondDerivativeEval b t (X t x s) (Whk t) (V t l s) +
      spatialSecondDerivativeEval b t (X t x s) (Whl t) (V t k s) +
      spatialSecondDerivativeEval b t (X t x s) (Wkl t) (V t h s)
  have hF3 : Continuous (fun t =>
      spatialThirdDerivativeEval b t (X t x s) (V t h s) (V t k s) (V t l s)) := by
    have hcurve : Continuous (fun t : ℝ => (t, X t x s)) :=
      continuous_id.prodMk (flow_continuous_time b hX x s)
    have hD : Continuous (fun t : ℝ =>
        iteratedFDeriv ℝ 3 (Function.uncurry b) (t, X t x s)) :=
      (hb.smooth.continuous_iteratedFDeriv (m := 3) (by simp)).comp hcurve
    have hdirs : Continuous (fun t : ℝ =>
        Existence.spatialDirections3 (V t h s) (V t k s) (V t l s)) := by
      apply continuous_pi
      intro i
      fin_cases i
      · change Continuous (fun t : ℝ => (0, V t h s))
        exact continuous_const.prodMk hVh
      · change Continuous (fun t : ℝ => (0, V t k s))
        exact continuous_const.prodMk hVk
      · change Continuous (fun t : ℝ => (0, V t l s))
        exact continuous_const.prodMk hVl
    have hEval : Continuous
        (fun z : _root_.ContinuousMultilinearMap ℝ
          (fun _ : Fin 3 => ℝ × Vec 2) (Vec 2) × (Fin 3 → ℝ × Vec 2) =>
            z.1 z.2) := by fun_prop
    change Continuous (fun t =>
      iteratedFDeriv ℝ 3 (Function.uncurry b) (t, X t x s)
        (Existence.spatialDirections3 (V t h s) (V t k s) (V t l s)))
    have hcomp := hEval.comp (hD.prodMk hdirs)
    convert hcomp using 1
    funext t
    rfl
  have hF : Continuous F := by
    have hhkl := Existence.continuous_spatialSecondDerivativeEval_along hb hX x s
      Whk (fun t => V t l s) hWhk hVl
    have hhlk := Existence.continuous_spatialSecondDerivativeEval_along hb hX x s
      Whl (fun t => V t k s) hWhl hVk
    have hklh := Existence.continuous_spatialSecondDerivativeEval_along hb hX x s
      Wkl (fun t => V t h s) hWkl hVh
    change Continuous (fun t => _ + _ + _ + _)
    exact ((hF3.add hhkl).add hhlk).add hklh
  have hbound : ∀ t, ‖A t‖ ≤ M := fun t => hM t (X t x s)
  simpa [A, F, Whk, Whl, Wkl, add_assoc] using
    existsUnique_forcedLinearSystemFlow A F hA hF M hbound

/-- The selected global third variational flow. -/
noncomputable def flowThirdVariation
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k l : Vec 2) : ℝ → Vec 2 → ℝ → Vec 2 :=
  Classical.choose (existsUnique_flow_thirdVariationCandidate hb hX x s hV h k l)

/-- The selected third variation solves its defining affine system. -/
theorem flowThirdVariation_isFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k l : Vec 2) :
    AVenhance.IsFlow (fun t w =>
      jointSpatialFDeriv b t (X t x s) w +
        spatialThirdDerivativeEval b t (X t x s)
          (V t h s) (V t k s) (V t l s) +
        spatialSecondDerivativeEval b t (X t x s)
          (flowSecondVariation hb hX x s hV h k t 0 s) (V t l s) +
        spatialSecondDerivativeEval b t (X t x s)
          (flowSecondVariation hb hX x s hV h l t 0 s) (V t k s) +
        spatialSecondDerivativeEval b t (X t x s)
          (flowSecondVariation hb hX x s hV k l t 0 s) (V t h s))
      (flowThirdVariation hb hX x s hV h k l) := by
  exact (Classical.choose_spec
    (existsUnique_flow_thirdVariationCandidate hb hX x s hV h k l)).1

end AVenhance.Infra.Flow
