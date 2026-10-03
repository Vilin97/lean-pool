/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Composition
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Characteristic identities for smooth solutions of the transport equation. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff NNReal Topology

noncomputable section

namespace AVenhance.FaaDiBruno

/-- Restrict the derivative of a joint time-space field to its spatial
directions. -/
def spatialDerivativeCLM (F : ℝ × Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) :
    Vec 2 →L[ℝ] Vec 2 :=
  (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Vec 2))

/-- Restricting a smooth joint derivative to the spatial factor agrees with
the derivative of the fixed-time slice. -/
theorem spatialDerivativeCLM_eq_slice
    {f : ℝ → Vec 2 → Vec 2}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) (t : ℝ) (x : Vec 2) :
    spatialDerivativeCLM (Function.uncurry f) t x = fderiv ℝ (f t) x := by
  have hF : Differentiable ℝ (Function.uncurry f) :=
    hf.differentiable (by norm_num)
  have hcomp := (hF (t, x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right t x)
  have hslice : HasFDerivAt (fun y : Vec 2 => f t y)
      (spatialDerivativeCLM (Function.uncurry f) t x) x := by
    simpa [spatialDerivativeCLM, Function.uncurry] using hcomp
  exact hslice.fderiv.symm

/-- A pointwise operator bound for the first derivative bounds the paper's
order-one coordinate seminorm, including vector-valued outputs. -/
theorem derivativeSup_one_le_of_fderiv_norm_le
    {d : ℕ} [Nonempty (Fin d)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (hf : ContDiff ℝ 1 f) {M : ℝ}
    (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ M) :
    derivativeSup 1 f ≤ ENNReal.ofReal M := by
  classical
  apply iSup_le
  intro I
  have hpoint (x : Vec d) : ‖orderedPartial 1 f x I‖ ≤ M := by
    let i : Fin d := I 0
    have hcomp := (hf.differentiable (by norm_num) x).hasFDerivAt.comp
      (WithLp.toLp 1 x) (vecOneEquiv d).hasFDerivAt
    have hLift : fderiv ℝ (liftVecOne f) (WithLp.toLp 1 x) =
        (fderiv ℝ f x).comp (vecOneEquiv d).toContinuousLinearMap := by
      have h := hcomp.fderiv
      simpa [liftVecOne, vecOneEquiv, PiLp.coe_continuousLinearEquiv] using h
    have hbasis : vecOneEquiv d (coordinateVectorOne d i) = coordinateVector d i := by
      ext j
      by_cases hj : j = i <;> simp [vecOneEquiv, coordinateVectorOne,
        coordinateVector, hj]
    have hpartial : orderedPartial 1 f x I =
        fderiv ℝ f x (coordinateVector d i) := by
      simp only [orderedPartial, iteratedFDeriv_one_apply]
      rw [hLift]
      change fderiv ℝ f x (vecOneEquiv d (coordinateVectorOne d (I 0))) = _
      rw [show I 0 = i by rfl, hbasis]
    rw [hpartial]
    have hcoordNorm : ‖coordinateVector d i‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonempty]
      intro j
      by_cases hj : j = i <;> simp [coordinateVector, hj]
    calc
      ‖fderiv ℝ f x (coordinateVector d i)‖ ≤
          ‖fderiv ℝ f x‖ * ‖coordinateVector d i‖ :=
        (fderiv ℝ f x).le_opNorm _
      _ ≤ ‖fderiv ℝ f x‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hcoordNorm
      _ ≤ M := hD x
  have hae : ∀ᵐ x ∂vecVolume d, ‖orderedPartial 1 f x I‖ ≤ M :=
    Filter.Eventually.of_forall hpoint
  simpa [partialSup] using eLpNormEssSup_le_of_ae_bound hae

/-- Convert a pointwise order-one derivative bound into the normalized
order-one seminorm bound, with the paper's factor `4 / R`. -/
theorem snorm_one_le_of_derivativeSup_le
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) {R M : ℝ} (hR : 0 < R)
    (hD : derivativeSup 1 f ≤ ENNReal.ofReal M) :
    snorm f 1 R ≤ ENNReal.ofReal (4 * M / R) := by
  have htarget :
      ENNReal.ofReal M ≤ ENNReal.ofReal
        ((4 * M / R) * R ^ (1 : ℕ) * (Nat.factorial 1 : ℝ) /
          (((1 : ℕ) : ℝ) + 1) ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    have hRne : R ≠ 0 := ne_of_gt hR
    norm_num
    field_simp
    exact le_rfl
  have hD' : derivativeSup 1 f ≤ ENNReal.ofReal
      ((4 * M / R) * R ^ (1 : ℕ) * (Nat.factorial 1 : ℝ) /
        (((1 : ℕ) : ℝ) + 1) ^ 2) := hD.trans htarget
  exact snorm_le_of_derivativeSup_le f hR hD'

/-- A classical solution of `∂ₜY + b·∇Y = g` with zero initial data.
The directional derivative formulation keeps the statement coordinate-free. -/
structure IsClassicalTransportSolution
    (b g Y : ℝ → Vec 2 → Vec 2) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry Y)
  equation : ∀ t x,
    fderiv ℝ (Function.uncurry Y) (t, x) (1, b t x) = g t x
  initial : ∀ x, Y 0 x = 0

/-- Differentiating the transport equation in a spatial direction gives the
linear transport equation for that directional derivative. -/
theorem transportSolution_spatialDerivative_equation
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (t : ℝ) (x v : Vec 2) :
    fderiv ℝ (fun q : ℝ × Vec 2 =>
      fderiv ℝ (Function.uncurry Y) q (0, v)) (t, x) (1, b t x) =
      fderiv ℝ (Function.uncurry g) (t, x) (0, v) -
        fderiv ℝ (Function.uncurry Y) (t, x)
          (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v)) := by
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry Y
  let G : ℝ × Vec 2 → Vec 2 := Function.uncurry g
  let W : ℝ × Vec 2 → ℝ × Vec 2 := fun q => (1, b q.1 q.2)
  let V : ℝ × Vec 2 → ℝ × Vec 2 := fun _ => (0, v)
  let p : ℝ × Vec 2 := (t, x)
  have hW : Differentiable ℝ W := by
    have hW' : ContDiff ℝ ∞ W := by
      simpa [W, Function.uncurry] using contDiff_const.prodMk hb
    exact hW'.differentiable (by simp)
  have hV : Differentiable ℝ V := by fun_prop
  have hcomm := VectorField.fderiv_apply_lieBracket
    (𝕜 := ℝ) (f := F) (W := W) (V := V)
    (x := p) (hY.smooth.contDiffAt) (by simp) (hW p) (hV p)
  have hEq : (fun q => fderiv ℝ F q (W q)) = G := by
    funext q
    exact hY.equation q.1 q.2
  have hbracket : VectorField.lieBracket ℝ V W p = fderiv ℝ W p (V p) := by
    simp [VectorField.lieBracket, V]
  have hcomm' := hcomm
  rw [hbracket, hEq] at hcomm'
  have hcomm'' : fderiv ℝ F p (fderiv ℝ W p (V p)) =
      fderiv ℝ G p (V p) -
        fderiv ℝ (fun q => fderiv ℝ F q (V q)) p (W p) := by
    simpa [V] using hcomm'
  have hresult : fderiv ℝ (fun q => fderiv ℝ F q (V q)) p (W p) =
      fderiv ℝ G p (V p) - fderiv ℝ F p (fderiv ℝ W p (V p)) := by
    rw [hcomm'']
    abel
  have hWdir : fderiv ℝ W p (V p) =
      (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v)) := by
    have hbAt : DifferentiableAt ℝ (Function.uncurry b) (t, x) :=
      hb.differentiable (by simp) (t, x)
    have hWderiv : fderiv ℝ (fun q : ℝ × Vec 2 => (1, b q.1 q.2)) (t, x) =
        (fderiv ℝ (fun _ : ℝ × Vec 2 => (1 : ℝ)) (t, x)).prod
          (fderiv ℝ (Function.uncurry b) (t, x)) :=
      DifferentiableAt.fderiv_prodMk (differentiableAt_const (1 : ℝ)) hbAt
    change fderiv ℝ (fun q : ℝ × Vec 2 => (1, b q.1 q.2)) (t, x) (0, v) = _
    rw [hWderiv]
    simp [fderiv_const_apply]
  rw [hWdir] at hresult
  simpa [p, F, G, Function.uncurry, V, W] using hresult

/-- The joint-space function obtained by differentiating a field in one fixed
spatial direction. -/
def transportDirectionalDerivative (F : ℝ × Vec 2 → Vec 2) (v : Vec 2) :
    ℝ × Vec 2 → Vec 2 := fun p => fderiv ℝ F p (0, v)

/-- Differentiating a classical transport solution once in a fixed spatial
direction again gives a classical transport solution. The differentiated
source includes the commutator with the spatial derivative of the drift. -/
theorem transportSolution_directionalDerivative_isSolution
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g)) (v : Vec 2) :
    IsClassicalTransportSolution b
      (fun t x => transportDirectionalDerivative (Function.uncurry g) v (t, x) -
        fderiv ℝ (Function.uncurry Y) (t, x)
          (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v)))
      (fun t x => transportDirectionalDerivative (Function.uncurry Y) v (t, x)) := by
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry Y
  let G : ℝ × Vec 2 → Vec 2 := Function.uncurry g
  let B : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let Yv : ℝ × Vec 2 → Vec 2 := transportDirectionalDerivative F v
  let Gv : ℝ × Vec 2 → Vec 2 := fun p =>
    transportDirectionalDerivative G v p - fderiv ℝ F p
      (0, fderiv ℝ B p (0, v))
  have hFderiv : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => fderiv ℝ F p) := by
    exact hY.smooth.fderiv_right (by simp)
  have hGderiv : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => fderiv ℝ G p) := by
    exact hg.fderiv_right (by simp)
  have hBderiv : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => fderiv ℝ B p) := by
    exact hb.fderiv_right (by simp)
  have hYv : ContDiff ℝ ∞ Yv := by
    change ContDiff ℝ ∞ (fun p => fderiv ℝ F p (0, v))
    exact hFderiv.clm_apply contDiff_const
  have hGv : ContDiff ℝ ∞ Gv := by
    have hGpart : ContDiff ℝ ∞ (transportDirectionalDerivative G v) := by
      change ContDiff ℝ ∞ (fun p => fderiv ℝ G p (0, v))
      exact hGderiv.clm_apply contDiff_const
    have hBdir : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => ((0 : ℝ), fderiv ℝ B p (0, v))) := by
      have h := hBderiv.clm_apply
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 => ((0 : ℝ), v)))
      have hzero : ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 => (0 : ℝ)) := contDiff_const
      simpa using hzero.prodMk h
    have hYapply : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => fderiv ℝ F p
        (0, fderiv ℝ B p (0, v))) := hFderiv.clm_apply hBdir
    simpa [Gv, transportDirectionalDerivative] using hGpart.sub hYapply
  have hYvUncurry : ContDiff ℝ ∞
      (Function.uncurry fun t x => transportDirectionalDerivative
        (Function.uncurry Y) v (t, x)) := by
    change ContDiff ℝ ∞ (fun p => transportDirectionalDerivative
      (Function.uncurry Y) v p)
    exact hYv
  have hGvUncurry : ContDiff ℝ ∞
      (Function.uncurry fun t x =>
        transportDirectionalDerivative (Function.uncurry g) v (t, x) -
          fderiv ℝ (Function.uncurry Y) (t, x)
            (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v))) := by
    change ContDiff ℝ ∞ (fun p =>
      transportDirectionalDerivative (Function.uncurry g) v p -
        fderiv ℝ (Function.uncurry Y) p
          (0, fderiv ℝ (Function.uncurry b) p (0, v)))
    exact hGv
  refine ⟨hYvUncurry, ?_, ?_⟩
  · intro t x
    change fderiv ℝ (fun p => fderiv ℝ (Function.uncurry Y) p (0, v))
        (t, x) (1, b t x) =
      transportDirectionalDerivative (Function.uncurry g) v (t, x) -
        fderiv ℝ (Function.uncurry Y) (t, x)
          (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v))
    simpa [transportDirectionalDerivative] using
      transportSolution_spatialDerivative_equation hY hb t x v
  · intro x
    have hslice : Y 0 = fun _ => (0 : Vec 2) := by
      funext z
      exact hY.initial z
    have hderiv := spatialDerivativeCLM_eq_slice
      (hY.smooth.of_le (by norm_num : (1 : ℕ) ≤ ∞)) 0 x
    have hzero := congrArg (fun q : Vec 2 →L[ℝ] Vec 2 => q v) hderiv
    have hconst : fderiv ℝ (Y 0) x = 0 := by rw [hslice]; simp
    change spatialDerivativeCLM (Function.uncurry Y) 0 x v = 0
    rw [hzero, hconst]
    simp

/-- A smooth transport solution that also records smoothness of its source.
The source smoothness field lets us iterate spatial differentiation. -/
structure IsSmoothClassicalTransportSolution
    (b g Y : ℝ → Vec 2 → Vec 2) : Prop extends
    IsClassicalTransportSolution b g Y where
  source_smooth : ContDiff ℝ ∞ (Function.uncurry g)

/-- Smoothness of the source obtained by differentiating the transport
equation once in a spatial direction. -/
theorem transportDirectionalSource_contDiff
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g)) (v : Vec 2) :
    ContDiff ℝ ∞ (Function.uncurry fun t x =>
      transportDirectionalDerivative (Function.uncurry g) v (t, x) -
        fderiv ℝ (Function.uncurry Y) (t, x)
          (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v))) := by
  have hYderiv : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => fderiv ℝ (Function.uncurry Y) p) :=
    hY.smooth.fderiv_right (by simp)
  have hGderiv : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => fderiv ℝ (Function.uncurry g) p) :=
    hg.fderiv_right (by simp)
  have hBderiv : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => fderiv ℝ (Function.uncurry b) p) :=
    hb.fderiv_right (by simp)
  have hGpart : ContDiff ℝ ∞
      (transportDirectionalDerivative (Function.uncurry g) v) := by
    change ContDiff ℝ ∞ (fun p => fderiv ℝ (Function.uncurry g) p (0, v))
    exact hGderiv.clm_apply contDiff_const
  have hBpart : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => ((0 : ℝ), fderiv ℝ (Function.uncurry b) p (0, v))) := by
    have h := hBderiv.clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 => ((0 : ℝ), v)))
    have hzero : ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 => (0 : ℝ)) := contDiff_const
    simpa using hzero.prodMk h
  have hYpart : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => fderiv ℝ
      (Function.uncurry Y) p (0, fderiv ℝ (Function.uncurry b) p (0, v))) :=
    hYderiv.clm_apply hBpart
  have hjoint : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      transportDirectionalDerivative (Function.uncurry g) v p -
        fderiv ℝ (Function.uncurry Y) p
          (0, fderiv ℝ (Function.uncurry b) p (0, v))) := hGpart.sub hYpart
  change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
    transportDirectionalDerivative (Function.uncurry g) v p -
      fderiv ℝ (Function.uncurry Y) p
        (0, fderiv ℝ (Function.uncurry b) p (0, v)))
  exact hjoint

/-- The one-step derivative theorem upgraded to preserve smoothness of its new
source, so it can be iterated any finite number of times. -/
theorem transportSolution_directionalDerivative_isSmoothSolution
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsSmoothClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (v : Vec 2) :
    IsSmoothClassicalTransportSolution b
      (fun t x => transportDirectionalDerivative (Function.uncurry g) v (t, x) -
        fderiv ℝ (Function.uncurry Y) (t, x)
          (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v)))
      (fun t x => transportDirectionalDerivative (Function.uncurry Y) v (t, x)) := by
  refine ⟨transportSolution_directionalDerivative_isSolution hY.toIsClassicalTransportSolution
    hb hY.source_smooth v, ?_⟩
  exact transportDirectionalSource_contDiff hY.toIsClassicalTransportSolution
    hb hY.source_smooth v

/-- The joint field of the iterated spatial derivative in a finite ordered
list of fixed directions. -/
def transportSpatialJet (I : List (Vec 2))
    (F : ℝ × Vec 2 → Vec 2) : ℝ × Vec 2 → Vec 2 :=
  match I with
  | [] => F
  | v :: J => transportDirectionalDerivative (transportSpatialJet J F) v

/-- The recursively differentiated source in the transport equation. -/
def transportSourceJet (I : List (Vec 2))
    (b g Y : ℝ → Vec 2 → Vec 2) : ℝ × Vec 2 → Vec 2 :=
  match I with
  | [] => Function.uncurry g
  | v :: J => fun p =>
      transportDirectionalDerivative (transportSourceJet J b g Y) v p -
        fderiv ℝ (transportSpatialJet J (Function.uncurry Y)) p
          (0, fderiv ℝ (Function.uncurry b) p (0, v))

/-- Every finite ordered spatial derivative of a smooth classical transport
solution solves the correspondingly differentiated transport equation. The
source recursion explicitly retains all commutator terms. -/
theorem transportSolution_iteratedDirectionalDerivative_isSmoothSolution
    {b g Y : ℝ → Vec 2 → Vec 2}
    (I : List (Vec 2))
    (hY : IsSmoothClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) :
    IsSmoothClassicalTransportSolution b
      (Function.curry (transportSourceJet I b g Y))
      (Function.curry (transportSpatialJet I (Function.uncurry Y))) := by
  induction I with
  | nil =>
    simpa [transportSourceJet, transportSpatialJet, Function.curry_uncurry] using hY
  | cons v I ih =>
    have hprev := ih
    have hnext := transportSolution_directionalDerivative_isSmoothSolution hprev hb v
    change IsSmoothClassicalTransportSolution b
      (fun t x => transportDirectionalDerivative (transportSourceJet I b g Y) v (t, x) -
        fderiv ℝ (transportSpatialJet I (Function.uncurry Y)) (t, x)
          (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v)))
      (fun t x => transportDirectionalDerivative
        (transportSpatialJet I (Function.uncurry Y)) v (t, x))
    exact hnext

end AVenhance.FaaDiBruno

end
