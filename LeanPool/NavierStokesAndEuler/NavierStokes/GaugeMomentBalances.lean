/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean
public import LeanPool.NavierStokesAndEuler.NavierStokes.DefectIncrementBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedStressPrimitive

/-!
# Measured moment balances in the actual moving pressure gauge

The pressure coefficient is the measured second moment of the normalized
physical density. It varies with the true similarity coordinate. All moment
identities below use the actual state residual and the actual pressure recipe.
-/

section

/-!
# Actual state moment balances

Auxiliary torus averaging, radial integration, and the pressure constructor
connect the literal state residual to its actual slow debt derivatives.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.StateMomentBalances

open Set Filter MeasureTheory CorrectionState
open scoped BigOperators ContDiff Topology

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Mean bar, defined pointwise by `MeanMomentBounds.liftedTorusAverage (f n)`. -/
noncomputable def meanBar (f : ScalarField (Lift S)) : ScalarField (Lift S) :=
  fun n => MeanMomentBounds.liftedTorusAverage (f n)

namespace AuxiliaryAverage

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Coordinates ordered to match the two actual interval integrals. -/
noncomputable def unshuffle : (((ℝ × S) × ℝ) × ℝ) →L[ℝ] Lift S where
  toFun x := (x.1.1.1, (x.1.1.2, (x.2, x.1.2)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.fst.fst.prodMk
    (continuous_fst.fst.snd.prodMk (continuous_snd.prodMk continuous_fst.snd))

/-- Slow projection, bundling `toFun`, `map_add`, `map_smul`, `cont`. -/
noncomputable def slowProjection : Lift S →L[ℝ] (ℝ × S) where
  toFun x := (x.1, x.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.prodMk continuous_snd.fst

theorem pullback_derivative {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : ((ℝ × S) × ℝ) × ℝ) :
    fderiv ℝ (f ∘ unshuffle) x v = fderiv ℝ f (unshuffle x) (unshuffle v) := by
  rw [((hf.differentiable (by simp) _).hasFDerivAt.comp x unshuffle.hasFDerivAt).fderiv]
  rfl

theorem pullback_periodic {f : Lift S → ℝ} (hp : PressureStream.TorusPeriodicLift f) :
    IntegratedMeanBalances.TorusPeriodic (f ∘ unshuffle) := by
  constructor
  · intro x
    simpa [unshuffle, Function.comp_def] using
      hp x.1.1.1 x.1.1.2 (x.2, x.1.2) (1, 0)
  · intro x
    simpa [unshuffle, Function.comp_def] using
      hp x.1.1.1 x.1.1.2 (x.2, x.1.2) (0, 1)

theorem average_slowDerivative {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (v x : ℝ × S) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y (v.1, (v.2, 0))) x =
      fderiv ℝ (PressureStream.torusAverage f) x v := by
  have hF : ContDiff ℝ ∞ (f ∘ unshuffle) := hf.comp (unshuffle (S := S)).contDiff
  have h := IntegratedMeanBalances.torusAverage_fderiv hF x v
  have he : IntegratedMeanBalances.slowPartial v (f ∘ unshuffle) =
      (fun y => fderiv ℝ f (unshuffle y) (v.1, (v.2, 0))) := by
    funext y
    exact pullback_derivative hf y ((v, 0), 0)
  rw [he] at h
  exact h.symm

theorem average_torusDerivative {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (v : PressureStream.Plane) (x : ℝ × S) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y (0, (0, v))) x = 0 := by
  have hF : ContDiff ℝ ∞ (f ∘ unshuffle) := hf.comp (unshuffle (S := S)).contDiff
  have h := IntegratedMeanBalances.torusAverage_torusPartial_zero v hF (pullback_periodic hp) x
  have he : IntegratedMeanBalances.torusPartial v (f ∘ unshuffle) =
      (fun y => fderiv ℝ f (unshuffle y) (0, (0, v))) := by
    funext y
    exact pullback_derivative hf y ((0, v.2), v.1)
  rw [he] at h
  exact h

omit [NormedSpace ℝ S] in
theorem average_add {f g : Lift S → ℝ} (hf : Continuous f) (hg : Continuous g)
    (x : ℝ × S) :
    PressureStream.torusAverage (fun y => f y + g y) x =
      PressureStream.torusAverage f x + PressureStream.torusAverage g x := by
  change FourierAlias.torusMean (fun Y => f (x.1, (x.2, Y)) + g (x.1, (x.2, Y))) =
    FourierAlias.torusMean (fun Y => f (x.1, (x.2, Y))) +
      FourierAlias.torusMean (fun Y => g (x.1, (x.2, Y)))
  exact FourierAlias.torusMean_add
    (hf.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    (hg.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))

/-- The actual torus mean commutes with fixed slow derivatives and removes
the periodic directions. This does not assume a commuting inverse. -/
theorem average_derivative {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (v x : Lift S) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y v) (x.1, x.2.1) =
      fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x v := by
  have hv : v = (v.1, (v.2.1, (0 : PressureStream.Plane))) + (0, (0, v.2.2)) := by simp
  have he : (fun y => fderiv ℝ f y v) =
      (fun y => fderiv ℝ f y (v.1, (v.2.1, (0 : PressureStream.Plane))) +
        fderiv ℝ f y (0, (0, v.2.2))) := by
    funext y
    conv_lhs => rw [hv, map_add]
  rw [he, average_add
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous,
    average_slowDerivative hf (v.1, v.2.1) (x.1, x.2.1),
    average_torusDerivative hf hp v.2.2 (x.1, x.2.1), add_zero]
  have hbar : MeanMomentBounds.liftedTorusAverage f =
      PressureStream.torusAverage f ∘ slowProjection := rfl
  rw [hbar, (((PressureStream.torusAverage_contDiff hf).differentiable (by simp) _).hasFDerivAt.comp
    x slowProjection.hasFDerivAt).fderiv]
  rfl

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem average_const_mul (c : ℝ) (f : Lift S → ℝ) (x : ℝ × S) :
    PressureStream.torusAverage (fun y => c * f y) x = c * PressureStream.torusAverage f x := by
  simp [PressureStream.torusAverage, PressureStream.torusInner,
    intervalIntegral.integral_const_mul]

theorem average_linear {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (v w : Lift S)
    (a b : ℝ × S → ℝ) (x : Lift S) :
    PressureStream.torusAverage (fun y => fderiv ℝ f y v +
      a (y.1, y.2.1) * fderiv ℝ f y w + b (y.1, y.2.1) * f y) (x.1, x.2.1) =
      fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x v +
        a (x.1, x.2.1) * fderiv ℝ (MeanMomentBounds.liftedTorusAverage f) x w +
        b (x.1, x.2.1) * MeanMomentBounds.liftedTorusAverage f x := by
  have hv : Continuous (fun y => fderiv ℝ f y v) :=
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hw : Continuous (fun y => fderiv ℝ f y w) :=
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have he : PressureStream.torusAverage (fun y => fderiv ℝ f y v +
      a (y.1, y.2.1) * fderiv ℝ f y w + b (y.1, y.2.1) * f y) (x.1, x.2.1) =
    PressureStream.torusAverage (fun y => fderiv ℝ f y v +
      a (x.1, x.2.1) * fderiv ℝ f y w + b (x.1, x.2.1) * f y) (x.1, x.2.1) :=
    PressureStream.torusAverage_congr_slice _ (fun _ => rfl)
  rw [he, average_add (hv.fun_add (continuous_const.fun_mul hw)) (continuous_const.fun_mul
      hf.continuous),
    average_add hv (continuous_const.fun_mul hw), average_const_mul, average_const_mul,
    average_derivative hf hp, average_derivative hf hp]
  rfl

theorem meanBar_dz (o : MeanIncrementBounds.Operators (Lift S))
    (f : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    meanBar (o.dz f) = o.dz (meanBar f) := by
  funext n x
  change PressureStream.torusAverage (fun y => o.epsilon n * fderiv ℝ (f n) y o.eZ)
    (x.1, x.2.1) = _
  rw [average_const_mul, average_derivative (hf n) (hp n)]
  rfl

theorem meanBar_radialDiv (o : MeanIncrementBounds.Operators (Lift S))
    (hradius : o.radius = Prod.fst)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (f : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) (c : ℝ) :
    meanBar (o.radialDiv c f) = o.radialDiv c (meanBar f) := by
  funext n x
  have he : o.radialDiv c f n = fun y => fderiv ℝ (f n) y o.eR +
      (o.radialFrequency n * o.radialProfile (y.1, (y.2.1, 0))) * fderiv ℝ (f n) y o.vR +
      (c * y.1⁻¹) * f n y := by
    funext y
    simp only [MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.dr,
      WeightedClasses.graphDerivative, MeanIncrementBounds.Operators.invRadius,
      hradius, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hprofile y.1 y.2.1 y.2.2]
    ring
  change PressureStream.torusAverage (o.radialDiv c f n) (x.1, x.2.1) = _
  rw [he, average_linear (hf n) (hp n) o.eR o.vR
    (fun z => o.radialFrequency n * o.radialProfile (z.1, (z.2, 0))) (fun z => c * z.1⁻¹) x]
  simp only [MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.dr,
    WeightedClasses.graphDerivative, MeanIncrementBounds.Operators.invRadius,
    hradius, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [hprofile x.1 x.2.1 x.2.2]
  have hb : MeanMomentBounds.liftedTorusAverage (f n) = meanBar f n := rfl
  rw [hb]
  ring_nf

theorem meanBar_add (f g : ScalarField (Lift S))
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ∀ n, ContDiff ℝ ∞ (g n)) :
    meanBar (f + g) = meanBar f + meanBar g := by
  funext n x
  exact average_add (hf n).continuous (hg n).continuous _

theorem meanBar_sub (f g : ScalarField (Lift S))
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ∀ n, ContDiff ℝ ∞ (g n)) :
    meanBar (f - g) = meanBar f - meanBar g := by
  funext n x
  exact PressureStream.torusAverage_sub (hf n).continuous (hg n).continuous _

theorem radialDiv_sub (o : MeanIncrementBounds.Operators (Lift S)) (c : ℝ)
    (f g : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) :
    o.radialDiv c (f - g) = o.radialDiv c f - o.radialDiv c g := by
  funext n x
  have hd := fderiv_fun_sub ((hf n).differentiable (by simp) x) ((hg n).differentiable (by simp) x)
  change fderiv ℝ (f n - g n) x = _ at hd
  simp only [MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.dr,
    WeightedClasses.graphDerivative, Pi.add_apply, Pi.sub_apply, hd,
    _root_.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- The torus-mean flux identity used for the initial improved bar estimate. -/
theorem meanBar_fluxBalance {a b : ℝ} (ha : 0 < a)
    (o : MeanIncrementBounds.Operators (Lift S)) (ho : DefectIncrementBounds.PositiveOperators o)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (R A T : ScalarField (Lift S)) (c : ℝ)
    (hR : DefectIncrementBounds.Shell a b R) (hA : DefectIncrementBounds.Shell a b A)
    (hT : DefectIncrementBounds.Shell a b T)
    (hpR : ∀ n, PressureStream.TorusPeriodicLift (R n))
    (hpA : ∀ n, PressureStream.TorusPeriodicLift (A n))
    (hpT : ∀ n, PressureStream.TorusPeriodicLift (T n)) :
    meanBar (o.radialDiv c R + o.dz A - o.radialDiv c T) =
      o.radialDiv c (meanBar R - meanBar T) +
        o.dz (meanBar A) := by
  have hrc := hR.radialDiv ha ho c
  have hac := hA.dz o
  have htc := hT.radialDiv ha ho c
  rw [meanBar_sub (o.radialDiv c R + o.dz A) (o.radialDiv c T)
      (fun n => (hrc.smooth n).add (hac.smooth n)) htc.smooth,
    meanBar_add (o.radialDiv c R) (o.dz A) hrc.smooth hac.smooth,
    meanBar_radialDiv o ho.radius_eq hprofile R hR.smooth hpR c,
    meanBar_radialDiv o ho.radius_eq hprofile T hT.smooth hpT c,
    meanBar_dz o A hA.smooth hpA,
    radialDiv_sub o c (meanBar R) (meanBar T)
      (fun n => MeanMomentBounds.liftedTorusAverage_contDiff (hR.smooth n))
      (fun n => MeanMomentBounds.liftedTorusAverage_contDiff (hT.smooth n))]
  abel

end AuxiliaryAverage

namespace AuxiliaryAverage

theorem periodic_directional {f : Lift S → ℝ}
    (hp : PressureStream.TorusPeriodicLift f) (v : Lift S) :
    PressureStream.TorusPeriodicLift (fun x => fderiv ℝ f x v) := by
  intro R s Y k
  let a : Lift S := (0, (0, ((k.1 : ℝ), (k.2 : ℝ))))
  have he : (fun x : Lift S => f (x + a)) = f := by
    funext x
    simpa [a, Prod.add_def] using hp x.1 x.2.1 x.2.2 k
  have hd := congrArg (fun g : Lift S → ℝ => fderiv ℝ g (R, (s, Y))) he
  rw [fderiv_comp_add_right] at hd
  simpa [a, Prod.add_def] using congrArg (fun L : Lift S →L[ℝ] ℝ => L v) hd

theorem periodic_dr (o : MeanIncrementBounds.Operators (Lift S))
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    {f : ScalarField (Lift S)} (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    ∀ n, PressureStream.TorusPeriodicLift (o.dr f n) := by
  intro n R s Y k
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
    periodic_directional (hp n) o.eR R s Y k,
    periodic_directional (hp n) o.vR R s Y k]
  rw [hprofile R s _, hprofile R s Y]

theorem periodic_dz (o : MeanIncrementBounds.Operators (Lift S))
    {f : ScalarField (Lift S)} (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    ∀ n, PressureStream.TorusPeriodicLift (o.dz f n) := by
  intro n R s Y k
  simp only [MeanIncrementBounds.Operators.dz, periodic_directional (hp n) o.eZ R s Y k]

theorem meanBar_dr (o : MeanIncrementBounds.Operators (Lift S))
    (hradius : o.radius = Prod.fst)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (f : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    meanBar (o.dr f) = o.dr (meanBar f) := by
  simpa only [MeanIncrementBounds.Operators.radialDiv, zero_smul, add_zero] using
    meanBar_radialDiv o hradius hprofile f hf hp 0

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem meanBar_band_mul (c : ℕ → ℝ) (f : ScalarField (Lift S)) :
    meanBar (fun n x => c n * f n x) = fun n x => c n * meanBar f n x := by
  funext n x
  exact average_const_mul (c n) (f n) (x.1, x.2.1)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem average_radial_mul (c : ℝ → ℝ) (f : Lift S → ℝ) (x : ℝ × S) :
    PressureStream.torusAverage (fun y => c y.1 * f y) x =
      c x.1 * PressureStream.torusAverage f x := by
  simp only [PressureStream.torusAverage, PressureStream.torusInner,
    intervalIntegral.integral_const_mul]

theorem meanBar_time (o : MeanIncrementBounds.Operators (Lift S))
    (f : ScalarField (Lift S)) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    meanBar (o.time f) = o.time (meanBar f) := by
  funext n x
  have ht : Continuous (fun y => -(o.epsilon n * fderiv ℝ (f n) y o.eT)) :=
    (continuous_const.mul (((hf n).fderiv_right (m := ∞) (by
        simp)).clm_apply contDiff_const).continuous).neg
  have hv : Continuous (fun y => o.fastCoefficient n * fderiv ℝ (f n) y o.vT) :=
    continuous_const.mul (((hf n).fderiv_right (m := ∞) (by
        simp)).clm_apply contDiff_const).continuous
  change PressureStream.torusAverage (fun y => -(o.epsilon n * fderiv ℝ (f n) y o.eT) +
    o.fastCoefficient n * fderiv ℝ (f n) y o.vT) (x.1, x.2.1) = _
  rw [average_add ht hv]
  simp_rw [← neg_mul]
  rw [average_const_mul, average_const_mul, average_derivative (hf n) (hp n),
    average_derivative (hf n) (hp n)]
  simp only [MeanIncrementBounds.Operators.time, MeanIncrementBounds.Operators.slowTime,
    MeanIncrementBounds.Operators.fastTime, meanBar, Pi.add_apply, neg_mul]

theorem meanBar_viscosity {a b : ℝ} (ha : 0 < a)
    (o : MeanIncrementBounds.Operators (Lift S)) (ho : DefectIncrementBounds.PositiveOperators o)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (f : ScalarField (Lift S)) (hf : DefectIncrementBounds.Shell a b f)
    (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) (c : ℝ) :
    meanBar (o.viscosity c f) = o.viscosity c (meanBar f) := by
  have hrd := hf.dr ha ho
  have hrr := hrd.dr ha ho
  have hri := hrd.inv_mul ha ho
  have hzz := (hf.dz o).dz o
  have hii := ((hf.inv_mul ha ho).inv_mul ha ho).smul c
  have hd := meanBar_dr o ho.radius_eq hprofile f hf.smooth hp
  have hdd := meanBar_dr o ho.radius_eq hprofile (o.dr f) hrd.smooth
    (periodic_dr o hprofile hp)
  rw [hd] at hdd
  have hz := meanBar_dz o f hf.smooth hp
  have hzzbar := meanBar_dz o (o.dz f) (hf.dz o).smooth (periodic_dz o hp)
  rw [hz] at hzzbar
  funext n x
  have hric : Continuous (fun y => o.invRadius n y * o.dr f n y) := (hri.smooth n).continuous
  have hiic : Continuous (fun y => c * (o.invRadius n y * (o.invRadius n y * f n y))) :=
    (hii.smooth n).continuous
  change PressureStream.torusAverage (fun y => o.epsilon n *
      (o.dr (o.dr f) n y + o.invRadius n y * o.dr f n y +
        o.dz (o.dz f) n y - c * (o.invRadius n y * (o.invRadius n y * f n y))))
      (x.1, x.2.1) = _
  rw [average_const_mul,
    PressureStream.torusAverage_sub (((hrr.smooth n).continuous.fun_add hric).fun_add (hzz.smooth
        n).continuous)
      hiic,
    average_add ((hrr.smooth n).continuous.fun_add hric) (hzz.smooth n).continuous,
    average_add (hrr.smooth n).continuous hric]
  simp only [MeanIncrementBounds.Operators.invRadius, ho.radius_eq]
  rw [average_radial_mul, average_const_mul, average_radial_mul, average_radial_mul]
  change o.epsilon n * (meanBar (o.dr (o.dr f)) n x + x.1⁻¹ * meanBar (o.dr f) n x +
    meanBar (o.dz (o.dz f)) n x - c * (x.1⁻¹ * (x.1⁻¹ * meanBar f n x))) = _
  rw [hdd, hd, hzzbar]
  simp only [MeanIncrementBounds.Operators.viscosity, MeanIncrementBounds.Operators.invRadius,
    ho.radius_eq]

end AuxiliaryAverage

/-! ## Explicit graph operators acting on the actual torus means -/

/-- Averaged, defined pointwise by `PressureStream.torusAverage (f n)`. -/
noncomputable def averaged (f : ScalarField (Lift S)) : ℕ → ℝ × S → ℝ :=
  fun n => PressureStream.torusAverage (f n)

/-- Lift slow, defined pointwise by `f n (x.1, x.2.1)`. -/
noncomputable def liftSlow (f : ℕ → ℝ × S → ℝ) : ScalarField (Lift S) :=
  fun n x => f n (x.1, x.2.1)

/-- Native operators, given by `graphOperators r ε fast (z, 0) (t, 0) v`. -/
noncomputable def nativeOperators (r : ReconstructionData) (ε fast : ℕ → ℝ)
    (z t : S) (v : PressureStream.Plane) : MeanIncrementBounds.Operators (Lift S) :=
  graphOperators r ε fast (z, 0) (t, 0) v

theorem nativeOperators_positive (r : ReconstructionData) (ε fast : ℕ → ℝ)
    (z t : S) (v : PressureStream.Plane) :
    DefectIncrementBounds.PositiveOperators (nativeOperators r ε fast z t v) := by
  refine ⟨rfl, ?_⟩
  change ContDiffOn ℝ ∞ (fun x : Lift S => r.exponent * x.1 ^ (r.exponent - 1))
    DefectIncrementBounds.positiveDomain
  exact contDiffOn_const.mul (contDiffOn_fst.rpow_const_of_ne (fun _ hx => (ne_of_gt hx)))

omit [NormedSpace ℝ S] in
theorem nativeOperators_profile (r : ReconstructionData) (ε fast : ℕ → ℝ)
    (z t : S) (v : PressureStream.Plane) (R : ℝ) (s : S) (Y : PressureStream.Plane) :
    (nativeOperators r ε fast z t v).radialProfile (R, (s, Y)) =
      (nativeOperators r ε fast z t v).radialProfile (R, (s, 0)) := rfl

/-- Radial partial, given by `fderiv ℝ F x (1, 0)`. -/
noncomputable def radialPartial (F : ℝ × S → ℝ) (x : ℝ × S) : ℝ :=
  fderiv ℝ F x (1, 0)

theorem radialPartial_smooth {F : ℝ × S → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialPartial F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem radialPartial_eq_deriv {F : ℝ × S → ℝ} (hF : ContDiff ℝ ∞ F) (R : ℝ) (s : S) :
    radialPartial F (R, s) = deriv (fun q => F (q, s)) R := by
  have hd := ((hF.differentiable (by simp)) (R, s)).hasFDerivAt.comp_hasDerivAt R
    ((hasDerivAt_id R).prodMk (hasDerivAt_const R s))
  exact hd.deriv.symm

theorem radialPartial_twice_eq_deriv {F : ℝ × S → ℝ} (hF : ContDiff ℝ ∞ F) (R : ℝ) (s : S) :
    radialPartial (radialPartial F) (R, s) = deriv (deriv (fun q => F (q, s))) R := by
  rw [radialPartial_eq_deriv (radialPartial_smooth hF)]
  congr 1
  funext q
  exact radialPartial_eq_deriv hF q s

theorem fderiv_liftSlow {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (n : ℕ) (x v : Lift S) :
    fderiv ℝ (liftSlow F n) x v = fderiv ℝ (F n) (x.1, x.2.1) (v.1, v.2.1) := by
  have hd := (((hF n).differentiable (by simp)) (x.1, x.2.1)).hasFDerivAt.comp x
    AuxiliaryAverage.slowProjection.hasFDerivAt
  rw [show liftSlow F n = F n ∘ AuxiliaryAverage.slowProjection from rfl, hd.fderiv]
  rfl

theorem native_dr_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n)) :
    (nativeOperators r ε fast z t v).dr (liftSlow F) = liftSlow (fun n => radialPartial (F n)) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
    nativeOperators, graphOperators, fderiv_liftSlow hF]
  simp [liftSlow, radialPartial, show ((0 : ℝ), (0 : S)) = (0 : ℝ × S) from rfl]

theorem native_dz_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n)) :
    (nativeOperators r ε fast z t v).dz (liftSlow F) =
      liftSlow (fun n x => ε n * IntegratedMeanBalances.parameterPartial z (F n) x) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.dz, nativeOperators, graphOperators, fderiv_liftSlow hF]
  rfl

theorem native_time_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n)) :
    (nativeOperators r ε fast z t v).time (liftSlow F) =
      liftSlow (fun n x => -ε n * IntegratedMeanBalances.parameterPartial t (F n) x) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.time, MeanIncrementBounds.Operators.slowTime,
    MeanIncrementBounds.Operators.fastTime, Pi.add_apply, nativeOperators, graphOperators,
    fderiv_liftSlow hF]
  simp [liftSlow, IntegratedMeanBalances.parameterPartial, neg_mul, show ((0 : ℝ), (0 : S)) = (0 :
      ℝ × S) from rfl]

theorem parameterPartial_const_mul {F : ℝ × S → ℝ} (hF : ContDiff ℝ ∞ F)
    (c : ℝ) (v : S) :
    IntegratedMeanBalances.parameterPartial v (fun x => c * F x) =
      fun x => c * IntegratedMeanBalances.parameterPartial v F x := by
  funext x
  unfold IntegratedMeanBalances.parameterPartial
  rw [(((hF.differentiable (by simp)) x).hasFDerivAt.const_mul c).fderiv]
  rfl

theorem native_radialDiv_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (c : ℝ) (n : ℕ) (x : Lift S) :
    (nativeOperators r ε fast z t v).radialDiv c (liftSlow F) n x =
      IntegratedMeanBalances.radialDivergence c (fun q => F n (q, x.2.1)) x.1 := by
  simp only [MeanIncrementBounds.Operators.radialDiv,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  rw [native_dr_lift r ε fast z t v hF]
  simp only [ liftSlow,
    MeanIncrementBounds.Operators.invRadius, nativeOperators, graphOperators]
  rw [radialPartial_eq_deriv (hF n)]
  simp only [IntegratedMeanBalances.radialDivergence, div_eq_mul_inv, mul_assoc]

theorem native_viscosity_lift (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S)
    (v : PressureStream.Plane) {F : ℕ → ℝ × S → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (c : ℝ) (n : ℕ) (x : Lift S) :
    (nativeOperators r ε fast z t v).viscosity c (liftSlow F) n x =
      ε n * (deriv (deriv (fun q => F n (q, x.2.1))) x.1 +
        deriv (fun q => F n (q, x.2.1)) x.1 / x.1 +
        ε n ^ 2 * IntegratedMeanBalances.parameterPartial z
          (IntegratedMeanBalances.parameterPartial z (F n)) (x.1, x.2.1) -
        c * F n (x.1, x.2.1) / x.1 ^ 2) := by
  have hr := native_dr_lift r ε fast z t v hF
  have hrr := native_dr_lift r ε fast z t v (fun n => radialPartial_smooth (hF n))
  have hz := native_dz_lift r ε fast z t v hF
  have hzz := native_dz_lift r ε fast z t v
    (F := fun n x => ε n * IntegratedMeanBalances.parameterPartial z (F n) x)
    (fun n => contDiff_const.mul
    (IntegratedMeanBalances.parameterPartial_smooth z (hF n)))
  simp only [MeanIncrementBounds.Operators.viscosity, hr, hrr, hz, hzz]
  simp only [liftSlow,
    parameterPartial_const_mul (IntegratedMeanBalances.parameterPartial_smooth z (hF n)),
    radialPartial_eq_deriv (hF n), radialPartial_twice_eq_deriv (hF n),
    MeanIncrementBounds.Operators.invRadius, nativeOperators, graphOperators]
  simp only [div_eq_mul_inv]
  ring

/-- Flux residual, given by `o.time u + o.radialDiv d R + o.dz Z - o.viscosity k u - o.radialDiv
d T`. -/
noncomputable def fluxResidual (o : MeanIncrementBounds.Operators (Lift S)) (d k : ℝ)
    (u R Z T : ScalarField (Lift S)) : ScalarField (Lift S) :=
  o.time u + o.radialDiv d R + o.dz Z - o.viscosity k u - o.radialDiv d T

theorem meanBar_fluxResidual {a b : ℝ} (ha : 0 < a)
    (o : MeanIncrementBounds.Operators (Lift S)) (ho : DefectIncrementBounds.PositiveOperators o)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    (d k : ℝ) {u R Z T : ScalarField (Lift S)}
    (hu : DefectIncrementBounds.Shell a b u) (hR : DefectIncrementBounds.Shell a b R)
    (hZ : DefectIncrementBounds.Shell a b Z) (hT : DefectIncrementBounds.Shell a b T)
    (pu : ∀ n, PressureStream.TorusPeriodicLift (u n))
    (pR : ∀ n, PressureStream.TorusPeriodicLift (R n))
    (pZ : ∀ n, PressureStream.TorusPeriodicLift (Z n))
    (pT : ∀ n, PressureStream.TorusPeriodicLift (T n)) :
    meanBar (fluxResidual o d k u R Z T) =
      fluxResidual o d k (meanBar u) (meanBar R) (meanBar Z) (meanBar T) := by
  have hut := hu.time o
  have hRd := hR.radialDiv ha ho d
  have hZd := hZ.dz o
  have huv := hu.viscosity ha ho k
  have hTd := hT.radialDiv ha ho d
  simp only [fluxResidual]
  rw [AuxiliaryAverage.meanBar_sub _ _ (((hut.add hRd).add hZd).sub huv).smooth hTd.smooth,
    AuxiliaryAverage.meanBar_sub _ _ ((hut.add hRd).add hZd).smooth huv.smooth,
    AuxiliaryAverage.meanBar_add _ _ (hut.add hRd).smooth hZd.smooth,
    AuxiliaryAverage.meanBar_add _ _ hut.smooth hRd.smooth,
    AuxiliaryAverage.meanBar_time o u hu.smooth pu,
    AuxiliaryAverage.meanBar_radialDiv o ho.radius_eq hprofile R hR.smooth pR,
    AuxiliaryAverage.meanBar_dz o Z hZ.smooth pZ,
    AuxiliaryAverage.meanBar_viscosity ha o ho hprofile u hu pu,
    AuxiliaryAverage.meanBar_radialDiv o ho.radius_eq hprofile T hT.smooth pT]

/-- Balance as an element of `ℝ`. -/
noncomputable def balance (ε : ℝ) (z t : S) (d k : ℝ)
    (u R Z T : ℝ × S → ℝ) (x : ℝ × S) : ℝ :=
  -ε * IntegratedMeanBalances.parameterPartial t u x +
    IntegratedMeanBalances.radialDivergence d (fun q => R (q, x.2)) x.1 +
    ε * IntegratedMeanBalances.parameterPartial z Z x -
    ε * (deriv (deriv (fun q => u (q, x.2))) x.1 +
      deriv (fun q => u (q, x.2)) x.1 / x.1 +
      ε ^ 2 * IntegratedMeanBalances.parameterPartial z
        (IntegratedMeanBalances.parameterPartial z u) x - k * u x / x.1 ^ 2) -
    IntegratedMeanBalances.radialDivergence d (fun q => T (q, x.2)) x.1

theorem averaged_fluxResidual {a b : ℝ} (ha : 0 < a)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : PressureStream.Plane)
    (d k : ℝ) {u R Z T : ScalarField (Lift S)}
    (hu : DefectIncrementBounds.Shell a b u) (hR : DefectIncrementBounds.Shell a b R)
    (hZ : DefectIncrementBounds.Shell a b Z) (hT : DefectIncrementBounds.Shell a b T)
    (pu : ∀ n, PressureStream.TorusPeriodicLift (u n))
    (pR : ∀ n, PressureStream.TorusPeriodicLift (R n))
    (pZ : ∀ n, PressureStream.TorusPeriodicLift (Z n))
    (pT : ∀ n, PressureStream.TorusPeriodicLift (T n)) (n : ℕ) (x : ℝ × S) :
    averaged (fluxResidual (nativeOperators r ε fast z t v) d k u R Z T) n x =
      balance (ε n) z t d k (averaged u n) (averaged R n) (averaged Z n) (averaged T n) x := by
  have hh := congrFun (congrFun (meanBar_fluxResidual ha _
    (nativeOperators_positive r ε fast z t v) (nativeOperators_profile r ε fast z t v)
    d k hu hR hZ hT pu pR pZ pT) n) (x.1, (x.2, 0))
  have hb (f : ScalarField (Lift S)) : meanBar f = liftSlow (averaged f) := rfl
  simp only [hb, fluxResidual, Pi.add_apply, Pi.sub_apply] at hh
  rw [native_time_lift r ε fast z t v (F := averaged u)
      (fun n => PressureStream.torusAverage_contDiff (hu.smooth n)),
    native_radialDiv_lift r ε fast z t v (F := averaged R)
      (fun n => PressureStream.torusAverage_contDiff (hR.smooth n)),
    native_dz_lift r ε fast z t v (F := averaged Z)
      (fun n => PressureStream.torusAverage_contDiff (hZ.smooth n)),
    native_viscosity_lift r ε fast z t v (F := averaged u)
      (fun n => PressureStream.torusAverage_contDiff (hu.smooth n)),
    native_radialDiv_lift r ε fast z t v (F := averaged T)
      (fun n => PressureStream.torusAverage_contDiff (hT.smooth n))] at hh
  exact hh

/-- Angular balance along as an element of `ℝ`. -/
noncomputable def angularBalanceAlong (ε : ℝ) (z t : S) (u R Z T : ℝ × S → ℝ)
    (x : ℝ × S) : ℝ :=
  -ε * IntegratedMeanBalances.parameterPartial t u x +
    IntegratedMeanBalances.radialDivergence 2 (fun q => R (q, x.2)) x.1 +
    ε * IntegratedMeanBalances.parameterPartial z Z x -
    ε * (IntegratedMeanBalances.angularRadialViscosity (fun q => u (q, x.2)) x.1 +
      ε ^ 2 * IntegratedMeanBalances.parameterPartial z
        (IntegratedMeanBalances.parameterPartial z u) x) -
    IntegratedMeanBalances.radialDivergence 2 (fun q => T (q, x.2)) x.1

/-- Axial balance along as an element of `ℝ`. -/
noncomputable def axialBalanceAlong (ε : ℝ) (z t : S) (u R Z T : ℝ × S → ℝ)
    (x : ℝ × S) : ℝ :=
  -ε * IntegratedMeanBalances.parameterPartial t u x +
    IntegratedMeanBalances.radialDivergence 1 (fun q => R (q, x.2)) x.1 +
    ε * IntegratedMeanBalances.parameterPartial z Z x -
    ε * (IntegratedMeanBalances.axialRadialViscosity (fun q => u (q, x.2)) x.1 +
      ε ^ 2 * IntegratedMeanBalances.parameterPartial z
        (IntegratedMeanBalances.parameterPartial z u) x) -
    IntegratedMeanBalances.radialDivergence 1 (fun q => T (q, x.2)) x.1

theorem balance_angular (ε : ℝ) (z t : S) (u R Z T : ℝ × S → ℝ) :
    balance ε z t 2 1 u R Z T = angularBalanceAlong ε z t u R Z T := by
  funext x
  simp only [balance, angularBalanceAlong, IntegratedMeanBalances.angularRadialViscosity]
  ring

theorem balance_axial (ε : ℝ) (z t : S) (u R Z T : ℝ × S → ℝ) :
    balance ε z t 1 0 u R Z T = axialBalanceAlong ε z t u R Z T := by
  funext x
  simp [balance, axialBalanceAlong, IntegratedMeanBalances.axialRadialViscosity]

theorem angularBalanceAlong_eq_integrated (ε : ℝ) (u R Z T : IntegratedMeanBalances.MeanField) :
    angularBalanceAlong ε (0, 1) (1, 0) u R Z T =
      IntegratedMeanBalances.angularBalance ε u R Z T := rfl

theorem axialBalanceAlong_eq_integrated (ε : ℝ) (u R Z p T : IntegratedMeanBalances.MeanField) :
    axialBalanceAlong ε (0, 1) (1, 0) u R (fun x => Z x + p x) T =
      IntegratedMeanBalances.axialBalance ε u R Z p T := rfl

section MomentIntegration

open IntegratedMeanBalances

/-- Radial shell data, collecting `smooth`, `supported`. -/
structure RadialShell (a b : ℝ) (F : (ℝ × S → ℝ)) : Prop where
  smooth : ContDiff ℝ ∞ F
  supported : RadialAlias.RadiallySupported a b F

theorem RadialShell.parameterDerivative {a b : ℝ} {F : (ℝ × S → ℝ)} (hF : RadialShell a b F)
    (v : S) : RadialShell a b (parameterPartial v F) :=
  ⟨parameterPartial_smooth v hF.smooth, parameterPartial_supported v hF.supported⟩

theorem RadialShell.add {a b : ℝ} {F G : (ℝ × S → ℝ)}
    (hF : RadialShell a b F) (hG : RadialShell a b G) :
    RadialShell a b (fun x => F x + G x) := by
  refine ⟨hF.smooth.add hG.smooth, ?_⟩
  intro x hx
  by_contra hn
  have hFx : F x = 0 := by
    by_contra h
    exact hn (hF.supported h)
  have hGx : G x = 0 := by
    by_contra h
    exact hn (hG.supported h)
  exact hx (by simp [hFx, hGx])

theorem RadialShell.slice_smooth {a b : ℝ} {F : (ℝ × S → ℝ)} (hF : RadialShell a b F)
    (p : S) : ContDiff ℝ ∞ (fun r => F (r, p)) :=
  radial_slice_smooth hF.smooth p

theorem RadialShell.slice_compact {a b : ℝ} {F : (ℝ × S → ℝ)} (hF : RadialShell a b F)
    (p : S) : HasCompactSupport (fun r => F (r, p)) :=
  radial_slice_compact hF.supported p

theorem RadialShell.weighted_integrable {a b : ℝ} {F : (ℝ × S → ℝ)} (hF : RadialShell a b F)
    (n : ℕ) (p : S) : Integrable (fun r => r ^ n * F (r, p)) :=
  IntegratedMeanBalances.weighted_integrable (hF.slice_smooth p).continuous (hF.slice_compact p) n

theorem integrated_angular_along {a b : ℝ} (ε : ℝ) (z t : S)
    {v radialFlux axialFlux virtualFlux : (ℝ × S → ℝ)}
    (hv : RadialShell a b v) (hr : RadialShell a b radialFlux)
    (hz : RadialShell a b axialFlux) (hT : RadialShell a b virtualFlux)
    (hmass : radialMoment 2 v = 0) (p : S) :
    radialMoment 2 (angularBalanceAlong ε z t v radialFlux axialFlux virtualFlux) p =
      ε * fderiv ℝ (radialMoment 2 axialFlux) p z := by
  have halg := moment_balance_algebra 2 (-ε) ε (ε ^ 2)
    (fun r => parameterPartial t v (r, p))
    (radialDivergence 2 (fun r => radialFlux (r, p)))
    (fun r => parameterPartial z axialFlux (r, p))
    (angularRadialViscosity (fun r => v (r, p)))
    (fun r => parameterPartial z (parameterPartial z v) (r, p))
    (radialDivergence 2 (fun r => virtualFlux (r, p)))
    ((hv.parameterDerivative t).weighted_integrable 2 p)
    (angular_divergence_integrable (hr.slice_smooth p) (hr.slice_compact p))
    ((hz.parameterDerivative z).weighted_integrable 2 p)
    (angular_viscosity_integrable (hv.slice_smooth p) (hv.slice_compact p))
    (((hv.parameterDerivative z).parameterDerivative z).weighted_integrable 2 p)
    (angular_divergence_integrable (hT.slice_smooth p) (hT.slice_compact p))
  have ht := zero_mass_parameterPartial hv.smooth hv.supported 2 hmass p t
  have hzz := zero_mass_parameterPartial_twice hv.smooth hv.supported 2 hmass p z z
  have hd := radialMoment_parameterPartial hz.smooth hz.supported 2 p z
  change moment 2 _ = _
  simp only [angularBalanceAlong]
  rw [halg, moment_angular_divergence (hr.slice_smooth p) (hr.slice_compact p),
    moment_angular_divergence (hT.slice_smooth p) (hT.slice_compact p),
    moment_angular_viscosity (hv.slice_smooth p) (hv.slice_compact p)]
  change (-ε) * radialMoment 2 (parameterPartial t v) p + 0 +
    ε * radialMoment 2 (parameterPartial z axialFlux) p -
    ε * (0 + ε ^ 2 * radialMoment 2 (parameterPartial z (parameterPartial z v)) p) - 0 = _
  rw [ht, hzz, ← hd]
  ring

theorem integrated_axial_along {a b : ℝ} (ε : ℝ) (z t : S)
    {γ radialFlux axialFlux virtualFlux : (ℝ × S → ℝ)}
    (hγ : RadialShell a b γ) (hr : RadialShell a b radialFlux)
    (hz : RadialShell a b axialFlux)
    (hT : RadialShell a b virtualFlux)
    (hmass : radialMoment 1 γ = 0) (p : S) :
    radialMoment 1 (axialBalanceAlong ε z t γ radialFlux axialFlux virtualFlux) p =
      ε * fderiv ℝ (radialMoment 1 axialFlux) p z := by
  have halg := moment_balance_algebra 1 (-ε) ε (ε ^ 2)
    (fun r => parameterPartial t γ (r, p))
    (radialDivergence 1 (fun r => radialFlux (r, p)))
    (fun r => parameterPartial z axialFlux (r, p))
    (axialRadialViscosity (fun r => γ (r, p)))
    (fun r => parameterPartial z (parameterPartial z γ) (r, p))
    (radialDivergence 1 (fun r => virtualFlux (r, p)))
    ((hγ.parameterDerivative t).weighted_integrable 1 p)
    (by
        simpa only [pow_one] using axial_divergence_integrable (hr.slice_smooth p)
            (hr.slice_compact p))
    ((hz.parameterDerivative z).weighted_integrable 1 p)
    (by
        simpa only [pow_one] using axial_viscosity_integrable (hγ.slice_smooth p) (hγ.slice_compact
            p))
    (((hγ.parameterDerivative z).parameterDerivative z).weighted_integrable 1 p)
    (by
        simpa only [pow_one] using axial_divergence_integrable (hT.slice_smooth p)
            (hT.slice_compact p))
  have ht := zero_mass_parameterPartial hγ.smooth hγ.supported 1 hmass p t
  have hzz := zero_mass_parameterPartial_twice hγ.smooth hγ.supported 1 hmass p z z
  have hd := radialMoment_parameterPartial hz.smooth hz.supported 1 p z
  change moment 1 _ = _
  simp only [axialBalanceAlong]
  rw [halg, moment_axial_divergence (hr.slice_smooth p) (hr.slice_compact p),
    moment_axial_divergence (hT.slice_smooth p) (hT.slice_compact p),
    moment_axial_viscosity (hγ.slice_smooth p) (hγ.slice_compact p)]
  change (-ε) * radialMoment 1 (parameterPartial t γ) p + 0 +
    ε * radialMoment 1 (parameterPartial z axialFlux) p -
    ε * (0 + ε ^ 2 * radialMoment 1 (parameterPartial z (parameterPartial z γ)) p) - 0 = _
  rw [ht, hzz, ← hd]
  ring

theorem averaged_radialShell {a b : ℝ} {f : ScalarField (Lift S)}
    (hf : DefectIncrementBounds.Shell a b f) (n : ℕ) :
    RadialShell a b (averaged f n) :=
  ⟨PressureStream.torusAverage_contDiff (hf.smooth n),
    PressureStream.torusAverage_supported (hf.supported n)⟩

end MomentIntegration

/-! ## Literal state fluxes and actual debt identities -/

/-- Theta radial flux, given by `MeanIncrementBounds.thetaRadial c.base u.mean + u.covariance 0
1`. -/
noncomputable def thetaRadialFlux (c : Context (Lift S)) (u : State (Lift S)) : ScalarField (Lift
    S) :=
  MeanIncrementBounds.thetaRadial c.base u.mean + u.covariance 0 1

/-- Theta axial flux, given by `MeanIncrementBounds.thetaAxial c.base u.mean + u.covariance 2
1`. -/
noncomputable def thetaAxialFlux (c : Context (Lift S)) (u : State (Lift S)) : ScalarField (Lift S)
    :=
  MeanIncrementBounds.thetaAxial c.base u.mean + u.covariance 2 1

/-- Axial radial flux, given by `MeanIncrementBounds.axialRadial c.base u.mean + u.covariance 0
2`. -/
noncomputable def axialRadialFlux (c : Context (Lift S)) (u : State (Lift S)) : ScalarField (Lift
    S) :=
  MeanIncrementBounds.axialRadial c.base u.mean + u.covariance 0 2

/-- Axial axial flux, given by `MeanIncrementBounds.axialAxial c.base u.mean + u.covariance 2
2`. -/
noncomputable def axialAxialFlux (c : Context (Lift S)) (u : State (Lift S)) : ScalarField (Lift S)
    :=
  MeanIncrementBounds.axialAxial c.base u.mean + u.covariance 2 2

/-- Regularity of the actual pointwise fields; no averaged equation or moment
identity is included among the premises. -/
structure FluxInputs (a b : ℝ) (u R Z T : ScalarField (Lift S)) : Prop where
  velocity : DefectIncrementBounds.Shell a b u
  radial : DefectIncrementBounds.Shell a b R
  axial : DefectIncrementBounds.Shell a b Z
  stress : DefectIncrementBounds.Shell a b T
  velocity_periodic : ∀ n, PressureStream.TorusPeriodicLift (u n)
  radial_periodic : ∀ n, PressureStream.TorusPeriodicLift (R n)
  axial_periodic : ∀ n, PressureStream.TorusPeriodicLift (Z n)
  stress_periodic : ∀ n, PressureStream.TorusPeriodicLift (T n)

/-- Angular inputs: an abbreviation for `FluxInputs a b u.mean.angular (thetaRadialFlux c u)
(thetaAxialFlux c u) c.virtualTheta`. -/
abbrev AngularInputs (a b : ℝ) (c : Context (Lift S)) (u : State (Lift S)) :=
  FluxInputs a b u.mean.angular (thetaRadialFlux c u) (thetaAxialFlux c u) c.virtualTheta

/-- Axial inputs: an abbreviation for `FluxInputs a b u.mean.axial (axialRadialFlux c u)
(axialAxialFlux c u) c.virtualAxial`. -/
abbrev AxialInputs (a b : ℝ) (c : Context (Lift S)) (u : State (Lift S)) :=
  FluxInputs a b u.mean.axial (axialRadialFlux c u) (axialAxialFlux c u) c.virtualAxial

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem state_radialMoment_eq (k : ℕ) (f : ScalarField (Lift S)) (n : ℕ) (s : S) :
    CorrectionState.radialMoment k f n s =
      IntegratedMeanBalances.radialMoment k (averaged f n) s :=
  MeanMomentBounds.pressureMass_radialWeighted k (f n) s

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem periodic_add {f g : Lift S → ℝ} (hf : PressureStream.TorusPeriodicLift f)
    (hg : PressureStream.TorusPeriodicLift g) : PressureStream.TorusPeriodicLift (fun x => f x + g
        x) := by
  intro R s Y k
  exact congrArg₂ (· + ·) (hf R s Y k) (hg R s Y k)

theorem averaged_thetaResidual {a b : ℝ} (ha : 0 < a)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : PressureStream.Plane)
    (c : Context (Lift S)) (u : State (Lift S))
    (ho : c.operators = nativeOperators r ε fast z t v) (H : AngularInputs a b c u)
    (n : ℕ) :
    averaged (u.thetaResidual c) n = angularBalanceAlong (ε n) z t
      (averaged u.mean.angular n) (averaged (thetaRadialFlux c u) n)
      (averaged (thetaAxialFlux c u) n) (averaged c.virtualTheta n) := by
  have he : u.thetaResidual c = fluxResidual (nativeOperators r ε fast z t v) 2 1
      u.mean.angular (thetaRadialFlux c u) (thetaAxialFlux c u) c.virtualTheta := by
    simp only [State.thetaResidual, MeanIncrementBounds.thetaResidual, fluxResidual,
      thetaRadialFlux, thetaAxialFlux, ho]
  rw [he]
  funext x
  rw [averaged_fluxResidual ha r ε fast z t v 2 1 H.velocity H.radial H.axial H.stress
    H.velocity_periodic H.radial_periodic H.axial_periodic H.stress_periodic,
    balance_angular]

theorem state_angular_moment {a b : ℝ} (ha : 0 < a)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : PressureStream.Plane)
    (c : Context (Lift S)) (u : State (Lift S))
    (ho : c.operators = nativeOperators r ε fast z t v) (H : AngularInputs a b c u)
    (hmass : CorrectionState.radialMoment 2 u.mean.angular = 0) (n : ℕ) (s : S) :
    CorrectionState.radialMoment 2 (u.thetaResidual c) n s =
      ε n * fderiv ℝ (CorrectionState.thetaDefect c u n) s z := by
  have hm : IntegratedMeanBalances.radialMoment 2 (averaged u.mean.angular n) = 0 := by
    funext q
    rw [← state_radialMoment_eq, hmass]
    rfl
  have hdebt : CorrectionState.thetaDefect c u n =
      IntegratedMeanBalances.radialMoment 2 (averaged (thetaAxialFlux c u) n) := by
    funext q
    exact state_radialMoment_eq 2 (thetaAxialFlux c u) n q
  rw [state_radialMoment_eq, averaged_thetaResidual ha r ε fast z t v c u ho H n, hdebt]
  exact integrated_angular_along (ε n) z t (averaged_radialShell H.velocity n)
    (averaged_radialShell H.radial n) (averaged_radialShell H.axial n)
    (averaged_radialShell H.stress n) hm s

/-- Pressure recipe, defined pointwise by `PressureStream.meanPressure r.exponent r.inner
r.outer (r.frequency n) r.inner_lt_outer r.radialDirection (u.gr c n)`. -/
noncomputable def pressureRecipe (r : ReconstructionData) (c : Context (Lift S))
    (u : State (Lift S)) : ScalarField (Lift S) :=
  fun n => PressureStream.meanPressure r.exponent r.inner r.outer (r.frequency n)
    r.inner_lt_outer r.radialDirection (u.gr c n)

theorem pressure_recipe_of_fixed (r : ReconstructionData) (c : Context (Lift S))
    (u : State (Lift S)) (h : reconstructPressure r c u = u) : u.pressure = pressureRecipe r c u :=
        by
  exact (congrArg State.pressure h).symm

theorem pressureRecipe_shell (r : ReconstructionData) (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (c : Context (Lift S)) (u : State (Lift S))
    (hg : DefectIncrementBounds.Shell r.inner r.outer (u.gr c)) :
    DefectIncrementBounds.Shell r.inner r.outer (pressureRecipe r c u) :=
  ⟨fun n => PressureStream.meanPressure_contDiff ha r.inner_lt_outer hd r.radialDirection
      (hg.smooth n) (hg.supported n),
    fun n => PressureStream.meanPressure_supported ha r.inner_lt_outer hd r.radialDirection
      (hg.smooth n) (hg.supported n)⟩

/-- Pressure coefficient, given by `IntegratedMeanBalances.moment 2 (PressureStream.rho r.inner
r.outer r.inner_lt_outer) / 2`. -/
noncomputable def pressureCoefficient (r : ReconstructionData) : ℝ :=
  IntegratedMeanBalances.moment 2 (PressureStream.rho r.inner r.outer r.inner_lt_outer) / 2

/-- Axial debt potential, defined pointwise by `CorrectionState.axialDefect c u n s +
pressureCoefficient r * CorrectionState.pressureDefect c u n s`. -/
noncomputable def axialDebtPotential (r : ReconstructionData) (c : Context (Lift S))
    (u : State (Lift S)) : ScalarField S :=
  fun n s => CorrectionState.axialDefect c u n s +
    pressureCoefficient r * CorrectionState.pressureDefect c u n s

theorem pressureRecipe_moment (r : ReconstructionData) (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (c : Context (Lift S)) (u : State (Lift S))
    (hg : DefectIncrementBounds.Shell r.inner r.outer (u.gr c))
    (pg : ∀ n, PressureStream.TorusPeriodicLift (u.gr c n)) (n : ℕ) (s : S) :
    IntegratedMeanBalances.radialMoment 1 (averaged (pressureRecipe r c u) n) s =
      -(1 / 2 : ℝ) * CorrectionState.radialMoment 2 (u.gr c) n s +
        pressureCoefficient r * CorrectionState.pressureDefect c u n s := by
  rw [state_radialMoment_eq]
  simpa only [pressureRecipe, averaged, IntegratedMeanBalances.radialMoment,
    pressureCoefficient, CorrectionState.pressureDefect, CorrectionState.radialMoment,
    pow_zero, one_mul] using
    (IntegratedMeanBalances.constructed_pressure_moment (M := r.frequency n)
      ha r.inner_lt_outer hd r.radialDirection (hg.smooth n) (hg.supported n) (pg n) s)

/-- The exact pressure alias has zero auxiliary mean because the constructed
pressure source has zero total mass. -/
theorem pressureAlias_average_zero (r : ReconstructionData) (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (c : Context (Lift S)) (u : State (Lift S))
    (hg : DefectIncrementBounds.Shell r.inner r.outer (u.gr c))
    (pg : ∀ n, PressureStream.TorusPeriodicLift (u.gr c n)) (n : ℕ) (x : ℝ × S) :
    PressureStream.torusAverage (PressureStream.pressureAlias r.exponent r.inner r.outer
      (r.frequency n) r.inner_lt_outer r.radialDirection (u.gr c n)) x = 0 :=
  PressureStream.pressureAlias_mean_zero ha r.inner_lt_outer hd r.radialDirection
    (hg.smooth n) (hg.supported n) (pg n) x

theorem physicalCompact_periodic (d a b M : ℝ) (v : PressureStream.Plane)
    {f : Lift S → ℝ} (hp : PressureStream.TorusPeriodicLift f) :
    PressureStream.TorusPeriodicLift (RadialPullback.physicalCompact d a b M (0, v) f) := by
  intro R s Y k
  have he : (fun q : ℝ => RadialPullback.normalizeSource d a f
      (TransportPrimitive.shift M ((0 : S), v)
        (RadialPullback.powerChart d a R, (s, Y + ((k.1 : ℝ), (k.2 : ℝ)))) q)) =
      fun q : ℝ => RadialPullback.normalizeSource d a f
      (TransportPrimitive.shift M ((0 : S), v)
        (RadialPullback.powerChart d a R, (s, Y)) q) := by
    funext q
    simp only [RadialPullback.normalizeSource, RadialPullback.liftChart,
      TransportPrimitive.shift, Prod.add_def, Prod.smul_def, smul_zero, add_zero]
    simpa only [Prod.add_def, Prod.smul_def, add_right_comm] using
      congrArg (fun u : ℝ => RadialPullback.sourceMultiplier d a
        (RadialPullback.powerChart d a R + q) • u)
        (hp (RadialPullback.inverseChart d a (RadialPullback.powerChart d a R + q)) s
          (Y + (M * q) • v) k)
  simp only [RadialPullback.physicalCompact, RadialPullback.pullback, RadialPullback.liftChart,
    Function.comp_def,
    TransportPrimitive.compactIntegral, TransportPrimitive.pastIntegral,
        TransportPrimitive.totalIntegral,
    he]

theorem physicalAlias_periodic (d a b M : ℝ) (v : PressureStream.Plane)
    {f : Lift S → ℝ} (hp : PressureStream.TorusPeriodicLift f) :
    PressureStream.TorusPeriodicLift (RadialPullback.physicalAlias d a b M (0, v) f) := by
  intro R s Y k
  have he : (fun q : ℝ => RadialPullback.normalizeSource d a f
      (TransportPrimitive.shift M ((0 : S), v)
        (RadialPullback.powerChart d a R, (s, Y + ((k.1 : ℝ), (k.2 : ℝ)))) q)) =
      fun q : ℝ => RadialPullback.normalizeSource d a f
      (TransportPrimitive.shift M ((0 : S), v)
        (RadialPullback.powerChart d a R, (s, Y)) q) := by
    funext q
    simp only [RadialPullback.normalizeSource, RadialPullback.liftChart,
      TransportPrimitive.shift, Prod.add_def, Prod.smul_def, smul_zero, add_zero]
    simpa only [Prod.add_def, Prod.smul_def, add_right_comm] using
      congrArg (fun u : ℝ => RadialPullback.sourceMultiplier d a
        (RadialPullback.powerChart d a R + q) • u)
        (hp (RadialPullback.inverseChart d a (RadialPullback.powerChart d a R + q)) s
          (Y + (M * q) • v) k)
  simp only [RadialPullback.physicalAlias, RadialPullback.liftChart,
    TransportPrimitive.totalIntegral, he]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem average_neg (f : Lift S → ℝ) (x : ℝ × S) :
    PressureStream.torusAverage (fun y => -f y) x = -PressureStream.torusAverage f x := by
  simp only [PressureStream.torusAverage, PressureStream.torusInner, intervalIntegral.integral_neg]

theorem pressureAlias_state_average_zero (r : ReconstructionData)
    (ha : 0 < r.inner) (hd : 0 < r.exponent) (c : Context (Lift S)) (u : State (Lift S))
    (hg : DefectIncrementBounds.Shell r.inner r.outer (u.gr c))
    (pg : ∀ n, PressureStream.TorusPeriodicLift (u.gr c n)) (n : ℕ) (x : ℝ × S) (i : Fin 3) :
    PressureStream.torusAverage (fun y => CorrectionState.pressureAlias r c u n (y, 0) i) x = 0 :=
        by
  fin_cases i
  · change PressureStream.torusAverage (fun y => -PressureStream.pressureAlias r.exponent r.inner
      r.outer
      (r.frequency n) r.inner_lt_outer r.radialDirection (u.gr c n) y) x = 0
    rw [average_neg, pressureAlias_average_zero r ha hd c u hg pg, neg_zero]
  · simp [CorrectionState.pressureAlias, PressureStream.torusAverage, PressureStream.torusInner]
  · simp [CorrectionState.pressureAlias, PressureStream.torusAverage, PressureStream.torusInner]

theorem axialAlias_periodic (d a b M : ℝ) (v : PressureStream.Plane) (h : ℝ) (n : ℕ)
    (f : Lift S → ℝ) :
    PressureStream.TorusPeriodicLift (TemporalMeanUpdate.axialAlias d a b M v h n f) := by
  have hp := physicalAlias_periodic d a b M v
    (PressureStream.weightedSource_periodic (TemporalMeanUpdate.desiredIncrement_periodic h n f))
  intro R s Y k
  exact congrArg (fun a : ℝ => a / R) (hp R s Y k)

theorem temporalAlias_average_zero [FiniteDimensional ℝ S]
    (r : ReconstructionData) (ha : 0 < r.inner) (hd : 0 < r.exponent) (h : ℝ)
    (c : Context (Lift S)) (u : State (Lift S))
    (hres : DefectIncrementBounds.Shell r.inner r.outer (u.axialResidual c))
    (pres : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (n : ℕ) (x : ℝ × S) (i : Fin 3) :
    PressureStream.torusAverage (fun y => temporalAlias r h c u n (y, 0) i) x = 0 := by
  fin_cases i
  · simp [temporalAlias, PressureStream.torusAverage, PressureStream.torusInner]
  · simp [temporalAlias, PressureStream.torusAverage, PressureStream.torusInner]
  · change PressureStream.torusAverage (fun y => -TemporalMeanUpdate.fastDerivative h n
      (TemporalMeanUpdate.axialAlias r.exponent r.inner r.outer (r.frequency n)
        r.radialDirection h n (u.axialResidual c n)) y) x = 0
    rw [average_neg]
    change -PressureStream.torusAverage (fun y => ChartScales.timeCoefficient h n *
      fderiv ℝ (TemporalMeanUpdate.axialAlias r.exponent r.inner r.outer (r.frequency n)
        r.radialDirection h n (u.axialResidual c n)) y (0, (0, TorusInverse.vector .temporal))) x =
            0
    rw [AuxiliaryAverage.average_const_mul,
      AuxiliaryAverage.average_torusDerivative
        (TemporalMeanUpdate.axialAlias_smooth ha r.inner_lt_outer hd r.radialDirection h n
          (hres.smooth n) (pres n) (hres.supported n))
        (axialAlias_periodic _ _ _ _ _ _ _ _), mul_zero, neg_zero]

theorem pressureRecipe_periodic (r : ReconstructionData) (c : Context (Lift S))
    (u : State (Lift S)) (pg : ∀ n, PressureStream.TorusPeriodicLift (u.gr c n)) :
    ∀ n, PressureStream.TorusPeriodicLift (pressureRecipe r c u n) := by
  intro n
  exact physicalCompact_periodic r.exponent r.inner r.outer (r.frequency n) r.radialDirection
    (PressureStream.pressureSource_periodic r.inner_lt_outer (pg n))

theorem averaged_axialResidual (r : ReconstructionData) (ha : 0 < r.inner)
    (ε fast : ℕ → ℝ) (z t : S) (v : PressureStream.Plane)
    (c : Context (Lift S)) (u : State (Lift S))
    (ho : c.operators = nativeOperators r ε fast z t v) (H : AxialInputs r.inner r.outer c u)
    (hp : DefectIncrementBounds.Shell r.inner r.outer u.pressure)
    (pp : ∀ n, PressureStream.TorusPeriodicLift (u.pressure n)) (n : ℕ) :
    averaged (u.axialResidual c) n = axialBalanceAlong (ε n) z t
      (averaged u.mean.axial n) (averaged (axialRadialFlux c u) n)
      (averaged (axialAxialFlux c u + u.pressure) n) (averaged c.virtualAxial n) := by
  have he : u.axialResidual c = fluxResidual (nativeOperators r ε fast z t v) 1 0
      u.mean.axial (axialRadialFlux c u) (axialAxialFlux c u + u.pressure) c.virtualAxial := by
    simp only [State.axialResidual, MeanIncrementBounds.axialResidual, fluxResidual,
      axialRadialFlux, axialAxialFlux, ho]
  rw [he]
  funext x
  rw [averaged_fluxResidual ha r ε fast z t v 1 0 H.velocity H.radial (H.axial.add hp) H.stress
    H.velocity_periodic H.radial_periodic (fun n => periodic_add (H.axial_periodic n) (pp n))
    H.stress_periodic, balance_axial]

theorem axial_flux_pressure_moment (r : ReconstructionData) (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (c : Context (Lift S)) (u : State (Lift S))
    (hZ : DefectIncrementBounds.Shell r.inner r.outer (axialAxialFlux c u))
    (hg : DefectIncrementBounds.Shell r.inner r.outer (u.gr c))
    (pg : ∀ n, PressureStream.TorusPeriodicLift (u.gr c n))
    (hrecipe : u.pressure = pressureRecipe r c u) :
    CorrectionState.radialMoment 1 (axialAxialFlux c u + u.pressure) = axialDebtPotential r c u :=
        by
  have hp : DefectIncrementBounds.Shell r.inner r.outer u.pressure := by
    rw [hrecipe]
    exact pressureRecipe_shell r ha hd c u hg
  have hsum := DefectIncrementBounds.barMoment_add hZ hp 1
  change CorrectionState.radialMoment 1 (axialAxialFlux c u + u.pressure) =
    CorrectionState.radialMoment 1 (axialAxialFlux c u) + CorrectionState.radialMoment 1 u.pressure
        at hsum
  rw [hsum]
  funext n s
  have hpval : CorrectionState.radialMoment 1 u.pressure n s =
      -(1 / 2 : ℝ) * CorrectionState.radialMoment 2 (u.gr c) n s +
        pressureCoefficient r * CorrectionState.pressureDefect c u n s := by
    rw [state_radialMoment_eq, hrecipe]
    exact pressureRecipe_moment r ha hd c u hg pg n s
  simp only [Pi.add_apply, hpval, axialDebtPotential, CorrectionState.axialDefect,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, axialAxialFlux]
  ring

theorem state_axial_moment (r : ReconstructionData) (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (ε fast : ℕ → ℝ) (z t : S) (v : PressureStream.Plane)
    (c : Context (Lift S)) (u : State (Lift S))
    (ho : c.operators = nativeOperators r ε fast z t v) (H : AxialInputs r.inner r.outer c u)
    (hg : DefectIncrementBounds.Shell r.inner r.outer (u.gr c))
    (pg : ∀ n, PressureStream.TorusPeriodicLift (u.gr c n))
    (hrecipe : u.pressure = pressureRecipe r c u)
    (hmass : CorrectionState.radialMoment 1 u.mean.axial = 0) (n : ℕ) (s : S) :
    CorrectionState.radialMoment 1 (u.axialResidual c) n s =
      ε n * fderiv ℝ (axialDebtPotential r c u n) s z := by
  have hp : DefectIncrementBounds.Shell r.inner r.outer u.pressure := by
    rw [hrecipe]
    exact pressureRecipe_shell r ha hd c u hg
  have pp : ∀ n, PressureStream.TorusPeriodicLift (u.pressure n) := by
    rw [hrecipe]
    exact pressureRecipe_periodic r c u pg
  have hm : IntegratedMeanBalances.radialMoment 1 (averaged u.mean.axial n) = 0 := by
    funext q
    rw [← state_radialMoment_eq, hmass]
    rfl
  have hdebt : IntegratedMeanBalances.radialMoment 1
      (averaged (axialAxialFlux c u + u.pressure) n) = axialDebtPotential r c u n := by
    funext q
    rw [← state_radialMoment_eq, axial_flux_pressure_moment r ha hd c u H.axial hg pg hrecipe]
  rw [state_radialMoment_eq, averaged_axialResidual r ha ε fast z t v c u ho H hp pp n]
  rw [integrated_axial_along (ε n) z t (averaged_radialShell H.velocity n)
    (averaged_radialShell H.radial n) (averaged_radialShell (H.axial.add hp) n)
    (averaged_radialShell H.stress n) hm s, hdebt]

/-! ## Actual all-jet debt bounds yield the improved signed bump order -/

section ClassBounds

open WeightedClasses MeanMomentBounds SignedStressPrimitive

theorem slowClass_smooth {ε slow : ℕ → ℝ}
    {hε : ∀ n, 0 < ε n} {hε1 : ∀ n, ε n ≤ 1} {hslow : ∀ n, 1 ≤ slow n}
    {α : ℝ} {f : ℕ → S → ℝ}
    (hf : UnweightedClass (slowStripData ε slow hε hε1 hslow) α f) (n : ℕ) :
    ContDiff ℝ ∞ (f n) := contDiffOn_univ.mp (hf.smooth n)

theorem slowClass_globalBandJets {ε slow : ℕ → ℝ}
    {hε : ∀ n, 0 < ε n} {hε1 : ∀ n, ε n ≤ 1} {hslow : ∀ n, 1 ≤ slow n}
    {α : ℝ} {f : ℕ → S → ℝ}
    (hf : UnweightedClass (slowStripData ε slow hε hε1 hslow) α f) :
    GlobalBandJets ε slow α f := by
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x j hj
  simpa only [majorant, slowStripData, StripData.growth, inv_one, max_self, mul_one]
    using hb n x (Set.mem_univ x) j hj

/-- Slow projection, given by `(ContinuousLinearMap.fst ℝ S PressureStream.Plane).comp
(ContinuousLinearMap.snd ℝ ℝ (S × PressureStream.Plane))`. -/
noncomputable def slowProjection : Lift S →L[ℝ] S :=
  (ContinuousLinearMap.fst ℝ S PressureStream.Plane).comp
    (ContinuousLinearMap.snd ℝ ℝ (S × PressureStream.Plane))

theorem norm_slowProjection_le : ‖slowProjection (S := S)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.2.1‖ ≤ 1 * ‖x‖
  simp only [one_mul, Prod.norm_def]
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem slowClass_lift (P : Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    {ε slow : ℕ → ℝ} {hε : ∀ n, 0 < ε n} {hε1 : ∀ n, ε n ≤ 1} {hslow : ∀ n, 1 ≤ slow n}
    {α : ℝ} {f : ℕ → S → ℝ}
    (hf : UnweightedClass (slowStripData ε slow hε hε1 hslow) α f) :
    UnweightedClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      α (fun n (x : Lift S) => f n x.2.1) := by
  apply globalBandJets_unweighted_log P.a_pos hcL hcR hε hε1 hslow
    (fun n => (slowClass_smooth hf n).comp contDiff_snd.fst)
  exact (slowClass_globalBandJets hf).compLinear (slowClass_smooth hf)
    slowProjection norm_slowProjection_le

theorem fderiv_parameterLift {f : S → ℝ} (hf : ContDiff ℝ ∞ f)
    (p : S × PressureStream.Plane) (z : S) :
    fderiv ℝ (fun y : S × PressureStream.Plane => f y.1) p (z, 0) = fderiv ℝ f p.1 z := by
  change fderiv ℝ (f ∘ Prod.fst) p (z, 0) = _
  rw [(((hf.differentiable (by simp)) p.1).hasFDerivAt.comp p hasFDerivAt_fst).fderiv]
  rfl

/-- The hypothesis is a bound on the actual slow debt. The residual moment
identity is supplied by the state theorems below, rather than a bump estimate. -/
theorem bump_class_from_actual_debt (P : Patch) (e : ℕ) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR) (ε slow : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)
    (α : ℝ) (F : ScalarField (Lift S)) (D : ScalarField S) (z : S)
    (hD : UnweightedClass (slowStripData ε slow hε hε1 hslow) α D)
    (hidentity : ∀ n s, CorrectionState.radialMoment e F n s = ε n * fderiv ℝ (D n) s z) :
    MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      (α + 1) (fun n => bumpCorrection P e (meanBar F n)) := by
  apply bump_improvedClass_of_moment_identity P e hcL hcR ε slow hε hε1 hslow α
    (meanBar F) (fun n (p : S × PressureStream.Plane) => D n p.1) (z, 0)
    (fun n => (slowClass_smooth hD n).comp contDiff_fst) (slowClass_lift P hcL hcR hD)
  intro n p
  change IntegratedMeanBalances.radialMoment e (averaged F n) p.1 = _
  rw [← state_radialMoment_eq, hidentity, fderiv_parameterLift (slowClass_smooth hD n)]

theorem state_angular_bump_improvedClass (P : Patch) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR) (r : ReconstructionData) (ha : 0 < r.inner)
    (ε fast slow : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hslow : ∀ n, 1 ≤ slow n) (z t : S) (v : PressureStream.Plane)
    (c : Context (Lift S)) (u : State (Lift S)) (α : ℝ)
    (ho : c.operators = nativeOperators r ε fast z t v) (H : AngularInputs r.inner r.outer c u)
    (hmass : ZeroMasses u)
    (hD : UnweightedClass (slowStripData ε slow hε hε1 hslow) α (thetaDefect c u)) :
    MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      (α + 1) (fun n => bumpCorrection P 2 (meanBar (u.thetaResidual c) n)) := by
  apply bump_class_from_actual_debt P 2 hcL hcR ε slow hε hε1 hslow α
    (u.thetaResidual c) (thetaDefect c u) z hD
  exact state_angular_moment ha r ε fast z t v c u ho H hmass.1

theorem state_axial_bump_improvedClass (P : Patch) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR) (r : ReconstructionData)
    (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (ε fast slow : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hslow : ∀ n, 1 ≤ slow n) (z t : S) (v : PressureStream.Plane)
    (c : Context (Lift S)) (u : State (Lift S)) (α : ℝ)
    (ho : c.operators = nativeOperators r ε fast z t v) (H : AxialInputs r.inner r.outer c u)
    (hg : DefectIncrementBounds.Shell r.inner r.outer (u.gr c))
    (pg : ∀ n, PressureStream.TorusPeriodicLift (u.gr c n))
    (hrecipe : u.pressure = pressureRecipe r c u) (hmass : ZeroMasses u)
    (hP : UnweightedClass (slowStripData ε slow hε hε1 hslow) α (pressureDefect c u))
    (hZ : UnweightedClass (slowStripData ε slow hε hε1 hslow) α (axialDefect c u)) :
    MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      (α + 1) (fun n => bumpCorrection P 1 (meanBar (u.axialResidual c) n)) := by
  have hC := hP.map ((ContinuousLinearMap.lsmul ℝ ℝ) (pressureCoefficient r))
  have hD : UnweightedClass (slowStripData ε slow hε hε1 hslow) α (axialDebtPotential r c u) := by
    have h := hZ.add hC
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] at h ⊢
    exact h
  apply bump_class_from_actual_debt P 1 hcL hcR ε slow hε hε1 hslow α
    (u.axialResidual c) (axialDebtPotential r c u) z hD
  exact state_axial_moment r ha hd ε fast z t v c u ho H hg pg hrecipe hmass.2

theorem debt_component_pressure (c : Context (Lift S)) (u : State (Lift S)) :
    (fun n s => debt c u n s 0) = pressureDefect c u := rfl

theorem debt_component_angular (c : Context (Lift S)) (u : State (Lift S)) :
    (fun n s => debt c u n s 1) = thetaDefect c u := rfl

theorem debt_component_axial (c : Context (Lift S)) (u : State (Lift S)) :
    (fun n s => debt c u n s 2) = axialDefect c u := rfl

theorem defectBounds_components {ε slow : ℕ → ℝ}
    {hε : ∀ n, 0 < ε n} {hε1 : ∀ n, ε n ≤ 1} {hslow : ∀ n, 1 ≤ slow n}
    {σ : ℝ} {c : Context (Lift S)} {u : State (Lift S)}
    (hD : DefectBounds (slowStripData ε slow hε hε1 hslow) σ c u) :
    UnweightedClass (slowStripData ε slow hε hε1 hslow) (1 + σ) (pressureDefect c u) ∧
    UnweightedClass (slowStripData ε slow hε hε1 hslow) (1 + σ) (thetaDefect c u) ∧
    UnweightedClass (slowStripData ε slow hε hε1 hslow) (1 + σ) (axialDefect c u) :=
  ⟨hD 0, hD 1, hD 2⟩

end ClassBounds

end NavierStokes.StateMomentBalances

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.GaugeMomentBalances

open Set Filter Function MeasureTheory
open CorrectionState
open scoped ContDiff Topology BigOperators Interval

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane

/-- Base pressure coefficient, given by `IntegratedMeanBalances.moment 2 (PressureStream.rho a b
hab) / 2`. -/
noncomputable def basePressureCoefficient (a b : ℝ) (hab : a < b) : ℝ :=
  IntegratedMeanBalances.moment 2 (PressureStream.rho a b hab) / 2

theorem basePressureCoefficient_lower {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    a ^ 2 / 2 ≤ basePressureCoefficient a b hab := by
  have hm : (∫ r, a ^ 2 * PressureStream.rho a b hab r) ≤
      ∫ r, r ^ 2 * PressureStream.rho a b hab r := by
    apply integral_mono ((PressureStream.rho_integrable a b hab).const_mul (a ^ 2))
      (IntegratedMeanBalances.weighted_integrable (PressureStream.rho_contDiff a b hab).continuous
        (PressureStream.rho_hasCompactSupport a b hab) 2)
    intro r
    by_cases hr : PressureStream.rho a b hab r = 0
    · simp only [hr, mul_zero, le_refl]
    · have har := (PressureStream.rho_support a b hab hr).1
      apply mul_le_mul_of_nonneg_right _ (PressureStream.rho_nonneg a b hab r)
      nlinarith [mul_nonneg (sub_nonneg.mpr har) (add_nonneg (ha.le.trans har) ha.le)]
  rw [integral_const_mul, PressureStream.rho_integral, mul_one] at hm
  exact div_le_div_of_nonneg_right hm (by norm_num)

theorem basePressureCoefficient_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < basePressureCoefficient a b hab :=
  lt_of_lt_of_le (by positivity : 0 < a ^ 2 / 2) (basePressureCoefficient_lower ha hab)

/-- Pressure coefficient, given by `basePressureCoefficient g.radial.inner g.radial.outer
g.radial.inner_lt_outer * g.length n s ^ 2`. -/
noncomputable def pressureCoefficient {S : Type} (g : VariableGaugeMean.GaugeData S)
    (n : ℕ) (s : S) : ℝ :=
  basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer * g.length n s ^ 2

/-- Exact second moment of the scaled, normalized density. -/
theorem rho_second_moment_scale {l a b : ℝ} (hl : 0 < l) (hab : a < b) :
    IntegratedMeanBalances.moment 2
      (PressureStream.rho (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl)) =
      l ^ 2 * IntegratedMeanBalances.moment 2 (PressureStream.rho a b hab) := by
  have he : PressureStream.rho (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) =
      fun r => l⁻¹ * PressureStream.rho a b hab (l⁻¹ * r) := by
    funext r
    have hh := MeanChartCompatibility.rho_scale hl hab (r / l)
    rw [mul_div_cancel₀ _ hl.ne'] at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  rw [he, IntegratedMeanBalances.moment_const_mul]
  change l⁻¹ * (∫ r, r ^ 2 * PressureStream.rho a b hab (l⁻¹ * r)) = _
  rw [SignedStressPrimitive.integral_dilate_weighted 2 _ (inv_pos.mpr hl)]
  unfold IntegratedMeanBalances.moment
  field_simp [hl.ne']; ring_nf; field_simp [hl.ne']

section GeneralGauge

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
/-- This is the coefficient of the pressure debt, measured in the moving
physical radius, rather than in the normalized profile radius. -/
theorem pressureCoefficient_measured (g : VariableGaugeMean.GaugeData S) (n : ℕ) (s : S)
    (hl : 0 < g.length n s) (Y : Plane) :
    (IntegratedMeanBalances.moment 2 (fun R => VariableGaugeMean.density
      g.radial.inner g.radial.outer g.radial.inner_lt_outer (g.length n) (R, (s, Y)))) / 2 =
      pressureCoefficient g n s := by
  have he : (fun R => VariableGaugeMean.density g.radial.inner g.radial.outer
      g.radial.inner_lt_outer (g.length n) (R, (s, Y))) =
      PressureStream.rho (g.length n s * g.radial.inner) (g.length n s * g.radial.outer)
        (mul_lt_mul_of_pos_left g.radial.inner_lt_outer hl) := by
    funext R
    exact VariableGaugeMean.density_eq_scaled g.radial.inner_lt_outer (g.length n) (R, (s, Y)) hl
  rw [he, rho_second_moment_scale hl g.radial.inner_lt_outer]
  unfold pressureCoefficient basePressureCoefficient
  ring

/-- The actual moving-gauge pressure moment. Freezing is used only to apply
a radial integral theorem on one fiber; no slow derivative is frozen. -/
theorem moving_pressure_moment {a b d M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (ell : S → ℝ) (v : Plane) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge a b ell U f)
    (hp : PhysicalMeanDomain.PeriodicOn U f) {s : S} (hsm : s ∈ U) (hl : 0 < ell s) :
    IntegratedMeanBalances.moment 1 (fun R => PressureStream.torusAverage
      (VariableGaugeMean.meanPressure d a b M hab ell v f) (R, s)) =
      -(1 / 2 : ℝ) * IntegratedMeanBalances.moment 2
        (fun R => PressureStream.torusAverage f (R, s)) +
      (basePressureCoefficient a b hab * ell s ^ 2) * PressureStream.pressureMass f s := by
  let F := PhysicalMeanDomain.freezeSlow s f
  have hF : ContDiff ℝ ∞ F := VariableGaugeMean.freezeSlow_contDiff hU hsm hf
  have hFs : RadialAlias.RadiallySupported (ell s * a) (ell s * b) F := by
    intro p hn
    exact hs (p.1, (s, p.2.2)) hsm hn
  have hFp : PressureStream.TorusPeriodicLift F := by
    intro R t Y k
    exact hp R s hsm Y k
  have he (R : ℝ) (Y : Plane) :
      VariableGaugeMean.meanPressure d a b M hab ell v f (R, (s, Y)) =
      PressureStream.meanPressure d (ell s * a) (ell s * b) M (mul_lt_mul_of_pos_left hab hl)
        v F (R, (s, Y)) := by
    rw [VariableGaugeMean.meanPressure_eq_fixed hab d M ell v f _ hl]
    exact PhysicalMeanDomain.meanPressure_fiberLocal d (ell s * a) (ell s * b) M
      (mul_lt_mul_of_pos_left hab hl) v f F s (fun _ _ => rfl) R Y
  have hbar : (fun R => PressureStream.torusAverage
      (VariableGaugeMean.meanPressure d a b M hab ell v f) (R, s)) =
      (fun R => PressureStream.torusAverage
        (PressureStream.meanPressure d (ell s * a) (ell s * b) M
          (mul_lt_mul_of_pos_left hab hl) v F) (R, s)) := by
    funext R
    exact PressureStream.torusAverage_congr_slice (R, s) (he R)
  have hFbar : (fun R => PressureStream.torusAverage F (R, s)) =
      (fun R => PressureStream.torusAverage f (R, s)) := by
    funext R
    exact PressureStream.torusAverage_congr_slice (R, s) (fun _ => rfl)
  have hmass : PressureStream.pressureMass F s = PressureStream.pressureMass f s := by
    change (∫ R, PressureStream.torusAverage F (R, s)) = _
    rw [hFbar]
    rfl
  rw [hbar, IntegratedMeanBalances.constructed_pressure_moment (mul_pos hl ha)
    (mul_lt_mul_of_pos_left hab hl) hd v hF hFs hFp s, hFbar, hmass, rho_second_moment_scale hl hab]
  unfold basePressureCoefficient
  ring

@[simp] theorem reconstructState_gr (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) :
    (VariableGaugeMean.reconstructState g c u).gr c = u.gr c := rfl

@[simp] theorem reconstructState_idempotent (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) :
    VariableGaugeMean.reconstructState g c (VariableGaugeMean.reconstructState g c u) =
      VariableGaugeMean.reconstructState g c u := rfl

end GeneralGauge

section SimilarityCoefficient

theorem similarity_pressureCoefficient {h d a b M : ℝ} (hab : a < b) (index : ℕ → ℕ)
    (hc : 0 < 2 * h) (hc1 : 2 * h < 1) (n : ℕ) {s : Plane} (hs : 0 < s.1) :
    pressureCoefficient (VariableGaugeMean.similarityGauge h d a b M hab index) n s =
      basePressureCoefficient a b hab * SimilarityCoordinates.coordinateQ (2 * h) s := by
  unfold pressureCoefficient VariableGaugeMean.similarityGauge VariableGaugeMean.qLength
  rw [Real.sq_sqrt (SimilarityCoordinates.coordinateQ_spec hc hc1 hs).1.le]

theorem similarity_pressureCoefficient_fderiv {h d a b M : ℝ} (hab : a < b) (index : ℕ → ℕ)
    (hc : 0 < 2 * h) (hc1 : 2 * h < 1) (n : ℕ) {s : Plane} (hs : 0 < s.1) (v : Plane) :
    fderiv ℝ (pressureCoefficient (VariableGaugeMean.similarityGauge h d a b M hab index) n) s v =
      basePressureCoefficient a b hab *
        ((v.1 + 2 * s.2 * SimilarityCoordinates.coordinateQ (2 * h) s ^ (2 * h) * v.2) /
          SimilarityCoordinates.scalarSlope (2 * h) s.2 (SimilarityCoordinates.coordinateQ (2 * h)
              s)) := by
  have he : pressureCoefficient (VariableGaugeMean.similarityGauge h d a b M hab index) n =ᶠ[𝓝 s]
      (fun t => basePressureCoefficient a b hab * SimilarityCoordinates.coordinateQ (2 * h) t) := by
    filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hs)] with t ht
    exact similarity_pressureCoefficient hab index hc hc1 n ht
  rw [he.fderiv_eq]
  have hd := ((SimilarityCoordinates.coordinateQ_smooth hc hc1 hs).differentiableAt (by
      simp)).hasFDerivAt
  rw [(hd.const_mul (basePressureCoefficient a b hab)).fderiv]
  change basePressureCoefficient a b hab * fderiv ℝ (SimilarityCoordinates.coordinateQ (2 * h)) s v
      = _
  rw [SimilarityCoordinates.coordinateQ_fderiv_apply hc hc1 hs]

end SimilarityCoefficient

/-! ## Local integration on a genuine open slow region -/

section LocalIntegration

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

open StateMomentBalances

/-- Local smoothness, compact radial support, and true torus periodicity of a
field. These are regularity hypotheses, not a moment equation. -/
structure LocalField (a b : ℝ) (U : Set S) (f : ScalarField (PressureStream.Lift S)) : Prop where
  smooth : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U)
  supported : ∀ n, PhysicalMeanDomain.SupportedOn a b U (f n)
  periodic : ∀ n, PhysicalMeanDomain.PeriodicOn U (f n)

theorem LocalField.add {a b : ℝ} {U : Set S} {f g : ScalarField (PressureStream.Lift S)}
    (hf : LocalField a b U f) (hg : LocalField a b U g) : LocalField a b U (f + g) := by
  refine ⟨fun n => (hf.smooth n).add (hg.smooth n), ?_, ?_⟩
  · intro n x hx hn
    by_cases h : f n x = 0
    · apply hg.supported n x hx
      simpa only [Pi.add_apply, h, zero_add] using hn
    · exact hf.supported n x hx h
  · intro n R s hs Y k
    exact congrArg₂ (· + ·) (hf.periodic n R s hs Y k) (hg.periodic n R s hs Y k)

/-- Localize family, defined pointwise by `PhysicalMeanDomain.localize χ (f n)`. -/
noncomputable def localizeFamily (χ : S → ℝ) (f : ScalarField (PressureStream.Lift S)) :
    ScalarField (PressureStream.Lift S) := fun n => PhysicalMeanDomain.localize χ (f n)

theorem LocalField.localize {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {f : ScalarField (PressureStream.Lift S)} (hf : LocalField a b U f)
    {χ : S → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ U) :
    DefectIncrementBounds.Shell a b (localizeFamily χ f) :=
  ⟨fun n => PhysicalMeanDomain.localize_smooth hU hχ hs (hf.smooth n),
    fun n => PhysicalMeanDomain.localize_supported hs (hf.supported n)⟩

theorem LocalField.localize_periodic {a b : ℝ} {U : Set S}
    {f : ScalarField (PressureStream.Lift S)} (hf : LocalField a b U f)
    {χ : S → ℝ} (hs : tsupport χ ⊆ U) (n : ℕ) :
    PressureStream.TorusPeriodicLift (localizeFamily χ f n) :=
  PhysicalMeanDomain.localize_periodic hs (hf.periodic n)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem radialMoment_fiber_congr (k : ℕ) {f g : ScalarField (PressureStream.Lift S)}
    (n : ℕ) (s : S) (he : ∀ R Y, f n (R, (s, Y)) = g n (R, (s, Y))) :
    CorrectionState.radialMoment k f n s = CorrectionState.radialMoment k g n s := by
  rw [state_radialMoment_eq, state_radialMoment_eq]
  apply integral_congr_ae
  filter_upwards [] with R
  exact congrArg (fun v => R ^ k * v) (PressureStream.torusAverage_congr_slice (R, s) (he R))

omit [NormedSpace ℝ S] in
theorem radialMoment_fiber_germ (k : ℕ) {f g : ScalarField (PressureStream.Lift S)}
    (n : ℕ) {s : S} (he : PhysicalMeanDomain.FiberGerm s (f n) (g n)) :
    CorrectionState.radialMoment k f n =ᶠ[𝓝 s] CorrectionState.radialMoment k g n := by
  filter_upwards [he] with t ht
  exact radialMoment_fiber_congr k n t ht

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem radialMoment_localize (k : ℕ) (χ : S → ℝ) (f : ScalarField (PressureStream.Lift S))
    (n : ℕ) (s : S) :
    CorrectionState.radialMoment k (localizeFamily χ f) n s =
      χ s * CorrectionState.radialMoment k f n s := by
  have hb (R : ℝ) : PressureStream.torusAverage (localizeFamily χ f n) (R, s) =
      χ s * PressureStream.torusAverage (f n) (R, s) := by
    rw [← AuxiliaryAverage.average_const_mul]
    exact PressureStream.torusAverage_congr_slice (R, s) (fun _ => rfl)
  rw [state_radialMoment_eq, state_radialMoment_eq]
  change IntegratedMeanBalances.moment k (fun R => PressureStream.torusAverage
    (localizeFamily χ f n) (R, s)) = _
  simp only [hb]
  exact IntegratedMeanBalances.moment_const_mul k (χ s) _

theorem dr_eventuallyEq (o : MeanIncrementBounds.Operators (PressureStream.Lift S))
    {f g : ScalarField (PressureStream.Lift S)} {n : ℕ} {x : PressureStream.Lift S}
    (he : f n =ᶠ[𝓝 x] g n) : o.dr f n =ᶠ[𝓝 x] o.dr g n := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative, hy]

theorem dz_eventuallyEq (o : MeanIncrementBounds.Operators (PressureStream.Lift S))
    {f g : ScalarField (PressureStream.Lift S)} {n : ℕ} {x : PressureStream.Lift S}
    (he : f n =ᶠ[𝓝 x] g n) : o.dz f n =ᶠ[𝓝 x] o.dz g n := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
  simp only [MeanIncrementBounds.Operators.dz, hy]

theorem fluxResidual_eventuallyEq (o : MeanIncrementBounds.Operators (PressureStream.Lift S))
    (d k : ℝ) {u R Z T u' R' Z' T' : ScalarField (PressureStream.Lift S)}
    {n : ℕ} {x : PressureStream.Lift S}
    (hu : u n =ᶠ[𝓝 x] u' n) (hR : R n =ᶠ[𝓝 x] R' n)
    (hZ : Z n =ᶠ[𝓝 x] Z' n) (hT : T n =ᶠ[𝓝 x] T' n) :
    fluxResidual o d k u R Z T n =ᶠ[𝓝 x] fluxResidual o d k u' R' Z' T' n := by
  have hdu := dr_eventuallyEq o hu
  have hddu := dr_eventuallyEq o hdu
  have hzzu := dz_eventuallyEq o (dz_eventuallyEq o hu)
  have hdR := dr_eventuallyEq o hR
  have hdT := dr_eventuallyEq o hT
  have hdZ := dz_eventuallyEq o hZ
  filter_upwards [hu, hu.fderiv (𝕜 := ℝ), hR, hT, hdu, hddu, hzzu, hdR, hdT, hdZ]
    with y hy hdy hRy hTy hduy hdduy hzzy hdRy hdTy hdZy
  simp only [fluxResidual, MeanIncrementBounds.Operators.time,
    MeanIncrementBounds.Operators.slowTime, MeanIncrementBounds.Operators.fastTime,
    MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.viscosity,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
    hy, hdy, hRy, hTy, hduy, hdduy, hzzy, hdRy, hdTy, hdZy]

theorem global_angular_moment {a b : ℝ} (ha : 0 < a)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : Plane)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : FluxInputs a b u R Z T)
    (hmass : CorrectionState.radialMoment 2 u = 0) (n : ℕ) (s : S) :
    CorrectionState.radialMoment 2
      (fluxResidual (nativeOperators r ε fast z t v) 2 1 u R Z T) n s =
      ε n * fderiv ℝ (CorrectionState.radialMoment 2 Z n) s z := by
  have hm : IntegratedMeanBalances.radialMoment 2 (averaged u n) = 0 := by
    funext q
    rw [← state_radialMoment_eq, hmass]
    rfl
  have he : averaged (fluxResidual (nativeOperators r ε fast z t v) 2 1 u R Z T) n =
      angularBalanceAlong (ε n) z t (averaged u n) (averaged R n) (averaged Z n) (averaged T n) :=
          by
    funext x
    rw [averaged_fluxResidual ha r ε fast z t v 2 1 H.velocity H.radial H.axial H.stress
      H.velocity_periodic H.radial_periodic H.axial_periodic H.stress_periodic, balance_angular]
  rw [state_radialMoment_eq, he, integrated_angular_along (ε n) z t
    (averaged_radialShell H.velocity n) (averaged_radialShell H.radial n)
    (averaged_radialShell H.axial n) (averaged_radialShell H.stress n) hm s]
  rw [show IntegratedMeanBalances.radialMoment 2 (averaged Z n) =
    CorrectionState.radialMoment 2 Z n from funext fun q => (state_radialMoment_eq 2 Z n q).symm]

theorem global_axial_moment {a b : ℝ} (ha : 0 < a)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : Plane)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : FluxInputs a b u R Z T)
    (hmass : CorrectionState.radialMoment 1 u = 0) (n : ℕ) (s : S) :
    CorrectionState.radialMoment 1
      (fluxResidual (nativeOperators r ε fast z t v) 1 0 u R Z T) n s =
      ε n * fderiv ℝ (CorrectionState.radialMoment 1 Z n) s z := by
  have hm : IntegratedMeanBalances.radialMoment 1 (averaged u n) = 0 := by
    funext q
    rw [← state_radialMoment_eq, hmass]
    rfl
  have he : averaged (fluxResidual (nativeOperators r ε fast z t v) 1 0 u R Z T) n =
      axialBalanceAlong (ε n) z t (averaged u n) (averaged R n) (averaged Z n) (averaged T n) := by
    funext x
    rw [averaged_fluxResidual ha r ε fast z t v 1 0 H.velocity H.radial H.axial H.stress
      H.velocity_periodic H.radial_periodic H.axial_periodic H.stress_periodic, balance_axial]
  rw [state_radialMoment_eq, he, integrated_axial_along (ε n) z t
    (averaged_radialShell H.velocity n) (averaged_radialShell H.radial n)
    (averaged_radialShell H.axial n) (averaged_radialShell H.stress n) hm s]
  rw [show IntegratedMeanBalances.radialMoment 1 (averaged Z n) =
    CorrectionState.radialMoment 1 Z n from funext fun q => (state_radialMoment_eq 1 Z n q).symm]

/-- Local flux inputs data, collecting `velocity`, `radial`, `axial`, `stress`. -/
structure LocalFluxInputs (a b : ℝ) (U : Set S)
    (u R Z T : ScalarField (PressureStream.Lift S)) : Prop where
  velocity : LocalField a b U u
  radial : LocalField a b U R
  axial : LocalField a b U Z
  stress : LocalField a b U T

omit [NormedSpace ℝ S] in
theorem localize_fiber_germ {s : S} {χ : S → ℝ} (hχ : χ =ᶠ[𝓝 s] fun _ => 1)
    (f : ScalarField (PressureStream.Lift S)) (n : ℕ) :
    PhysicalMeanDomain.FiberGerm s (localizeFamily χ f n) (f n) := by
  filter_upwards [hχ] with t ht
  intro R Y
  simp only [localizeFamily, PhysicalMeanDomain.localize, ht, one_smul]

omit [NormedSpace ℝ S] in
theorem localize_zero_moment {U : Set S} {χ : S → ℝ}
    (hχ : tsupport χ ⊆ U) (e : ℕ) {u : ScalarField (PressureStream.Lift S)}
    (hmass : ∀ n s, s ∈ U → CorrectionState.radialMoment e u n s = 0) :
    CorrectionState.radialMoment e (localizeFamily χ u) = 0 := by
  funext n s
  rw [radialMoment_localize]
  by_cases hc : χ s = 0
  · simp [hc]
  · rw [hmass n s (hχ (subset_tsupport χ hc)), mul_zero]
    rfl

variable [FiniteDimensional ℝ S]

theorem exists_slow_cutoff {U : Set S} (hU : IsOpen U) {s : S} (hs : s ∈ U) :
    ∃ χ : S → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧ χ =ᶠ[𝓝 s] fun _ => 1 := by
  obtain ⟨χ, hc, hcs, _, he⟩ := PhysicalMeanDomain.exists_fiber_localization hU hs
    (f := fun _ : PressureStream.Lift S => (1 : ℝ)) contDiffOn_const
  refine ⟨χ, hc, hcs, ?_⟩
  filter_upwards [he] with t ht
  simpa only [PhysicalMeanDomain.localize, smul_eq_mul, mul_one] using ht 0 0

omit [FiniteDimensional ℝ S] in
theorem LocalFluxInputs.localize {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : LocalFluxInputs a b U u R Z T)
    {χ : S → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ U) :
    FluxInputs a b (localizeFamily χ u) (localizeFamily χ R)
      (localizeFamily χ Z) (localizeFamily χ T) :=
  ⟨H.velocity.localize hU hχ hs, H.radial.localize hU hχ hs,
    H.axial.localize hU hχ hs, H.stress.localize hU hχ hs,
    H.velocity.localize_periodic hs, H.radial.localize_periodic hs,
    H.axial.localize_periodic hs, H.stress.localize_periodic hs⟩

omit [FiniteDimensional ℝ S] in
theorem residual_moment_localize (o : MeanIncrementBounds.Operators (PressureStream.Lift S))
    (e : ℕ) (d k : ℝ) {s : S} {χ : S → ℝ} (hχ : χ =ᶠ[𝓝 s] fun _ => 1)
    (u R Z T : ScalarField (PressureStream.Lift S)) (n : ℕ) :
    CorrectionState.radialMoment e (fluxResidual o d k
      (localizeFamily χ u) (localizeFamily χ R) (localizeFamily χ Z) (localizeFamily χ T)) n s =
      CorrectionState.radialMoment e (fluxResidual o d k u R Z T) n s := by
  apply radialMoment_fiber_congr
  intro r Y
  exact (fluxResidual_eventuallyEq o d k
    ((localize_fiber_germ hχ u n).eventuallyEq r Y)
    ((localize_fiber_germ hχ R n).eventuallyEq r Y)
    ((localize_fiber_germ hχ Z n).eventuallyEq r Y)
    ((localize_fiber_germ hχ T n).eventuallyEq r Y)).self_of_nhds

/-- All slow and radial derivatives are taken before integration. A compact
slow cutoff equals one on a whole neighborhood, so no moving-boundary terms
are omitted. -/
theorem local_angular_moment {a b : ℝ} (ha : 0 < a) {U : Set S} (hU : IsOpen U)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : Plane)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : LocalFluxInputs a b U u R Z T)
    (hmass : ∀ n s, s ∈ U → CorrectionState.radialMoment 2 u n s = 0)
    (n : ℕ) {s : S} (hs : s ∈ U) :
    CorrectionState.radialMoment 2
      (fluxResidual (nativeOperators r ε fast z t v) 2 1 u R Z T) n s =
      ε n * fderiv ℝ (CorrectionState.radialMoment 2 Z n) s z := by
  obtain ⟨χ, hc, hcs, he⟩ := exists_slow_cutoff hU hs
  have hh := global_angular_moment ha r ε fast z t v (H.localize hU hc hcs)
    (localize_zero_moment hcs 2 hmass) n s
  rw [residual_moment_localize _ 2 2 1 he u R Z T n,
    (radialMoment_fiber_germ 2 n (localize_fiber_germ he Z n)).fderiv_eq] at hh
  exact hh

theorem local_axial_moment {a b : ℝ} (ha : 0 < a) {U : Set S} (hU : IsOpen U)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : Plane)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : LocalFluxInputs a b U u R Z T)
    (hmass : ∀ n s, s ∈ U → CorrectionState.radialMoment 1 u n s = 0)
    (n : ℕ) {s : S} (hs : s ∈ U) :
    CorrectionState.radialMoment 1
      (fluxResidual (nativeOperators r ε fast z t v) 1 0 u R Z T) n s =
      ε n * fderiv ℝ (CorrectionState.radialMoment 1 Z n) s z := by
  obtain ⟨χ, hc, hcs, he⟩ := exists_slow_cutoff hU hs
  have hh := global_axial_moment ha r ε fast z t v (H.localize hU hc hcs)
    (localize_zero_moment hcs 1 hmass) n s
  rw [residual_moment_localize _ 1 1 0 he u R Z T n,
    (radialMoment_fiber_germ 1 n (localize_fiber_germ he Z n)).fderiv_eq] at hh
  exact hh

theorem LocalField.radialMoment_smooth {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {f : ScalarField (PressureStream.Lift S)} (hf : LocalField a b U f) (e n : ℕ) :
    ContDiffOn ℝ ∞ (CorrectionState.radialMoment e f n) U := by
  have hsm : ContDiffOn ℝ ∞ (fun x : PressureStream.Lift S => x.1 ^ e * f n x)
      (PhysicalMeanDomain.slowDomain U) := (contDiffOn_fst.pow e).mul (hf.smooth n)
  have hsp : PhysicalMeanDomain.SupportedOn a b U
      (fun x : PressureStream.Lift S => x.1 ^ e * f n x) := by
    intro x hx hn
    exact hf.supported n x hx (right_ne_zero_of_mul hn)
  have hm := PhysicalMeanDomain.liftedPressureMass_contDiffOn hU hsm hsp
  have hi : ContDiffOn ℝ ∞ (fun s : S => ((0 : ℝ), (s, (0 : Plane)))) U :=
    contDiffOn_const.prodMk (contDiffOn_id.prodMk contDiffOn_const)
  exact hm.comp hi (fun s hs => hs)

theorem LocalField.radialMoment_add {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {f g : ScalarField (PressureStream.Lift S)} (hf : LocalField a b U f)
    (hg : LocalField a b U g) (e n : ℕ) {s : S} (hs : s ∈ U) :
    CorrectionState.radialMoment e (f + g) n s =
      CorrectionState.radialMoment e f n s + CorrectionState.radialMoment e g n s := by
  obtain ⟨χ, hc, hcs, he⟩ := exists_slow_cutoff hU hs
  have hχ : χ s = 1 := he.self_of_nhds
  have hh := congrFun (congrFun
    (DefectIncrementBounds.barMoment_add (hf.localize hU hc hcs) (hg.localize hU hc hcs) e) n) s
  have heq : localizeFamily χ f + localizeFamily χ g = localizeFamily χ (f + g) := by
    funext n x
    simp [localizeFamily, PhysicalMeanDomain.localize, mul_add]
  change CorrectionState.radialMoment e (localizeFamily χ f + localizeFamily χ g) n s =
    CorrectionState.radialMoment e (localizeFamily χ f) n s +
    CorrectionState.radialMoment e (localizeFamily χ g) n s at hh
  simpa only [heq, radialMoment_localize, hχ, one_mul] using hh

end LocalIntegration

/-! ## The actual reconstructed state in a moving similarity shell -/

section MovingState

open StateMomentBalances LocalSignedRequest

/-- Regularity of an actual field on the moving physical shell. -/
structure MovingField {coord : ℝ} (U : SlowRegion coord) (a b : ℝ)
    (f : ScalarField Point) : Prop where
  smooth : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier)
  supported : ∀ n, VariableGaugeMean.SupportedGauge a b
    (VariableGaugeMean.qLength coord) U.carrier (f n)
  periodic : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n)

theorem MovingField.containing {coord a b c e : ℝ} {U : SlowRegion coord}
    {f : ScalarField Point} (hf : MovingField U a b f)
    (hl : ∀ s ∈ U.carrier, c ≤ VariableGaugeMean.qLength coord s * a)
    (hr : ∀ s ∈ U.carrier, VariableGaugeMean.qLength coord s * b ≤ e) :
    LocalField c e U.carrier f := by
  refine ⟨hf.smooth, ?_, hf.periodic⟩
  intro n x hx hn
  exact ⟨(hl _ hx).trans (hf.supported n x hx hn).1,
    (hf.supported n x hx hn).2.trans (hr _ hx)⟩

theorem MovingField.radialMoment_smooth {coord a b : ℝ} {U : SlowRegion coord}
    (ha : 0 < a) (hab : a < b) {f : ScalarField Point} (hf : MovingField U a b f)
    (e n : ℕ) : ContDiffOn ℝ ∞ (CorrectionState.radialMoment e f n) U.carrier := by
  obtain ⟨c, e', _, _, _, _, _, hl, hr, _⟩ := VariableGaugeMean.qLength_reference_bounds U ha hab
  exact (hf.containing hl hr).radialMoment_smooth U.isOpen e n

/-- Moving flux inputs data, collecting `velocity`, `radial`, `axial`, `stress`. -/
structure MovingFluxInputs {coord : ℝ} (U : SlowRegion coord) (a b : ℝ)
    (u R Z T : ScalarField Point) : Prop where
  velocity : MovingField U a b u
  radial : MovingField U a b R
  axial : MovingField U a b Z
  stress : MovingField U a b T

/-- Moving angular inputs: an abbreviation for `MovingFluxInputs U a b u.mean.angular
(thetaRadialFlux c u) (thetaAxialFlux c u) c.virtualTheta`. -/
abbrev MovingAngularInputs {coord : ℝ} (U : SlowRegion coord) (a b : ℝ)
    (c : Context Point) (u : State Point) :=
  MovingFluxInputs U a b u.mean.angular (thetaRadialFlux c u) (thetaAxialFlux c u) c.virtualTheta

/-- Moving axial inputs: an abbreviation for `MovingFluxInputs U a b u.mean.axial
(axialRadialFlux c u) (axialAxialFlux c u) c.virtualAxial`. -/
abbrev MovingAxialInputs {coord : ℝ} (U : SlowRegion coord) (a b : ℝ)
    (c : Context Point) (u : State Point) :=
  MovingFluxInputs U a b u.mean.axial (axialRadialFlux c u) (axialAxialFlux c u) c.virtualAxial

/-- Pressure recipe, given by `(VariableGaugeMean.reconstructState g c u).pressure`. -/
noncomputable def pressureRecipe (g : VariableGaugeMean.GaugeData Plane)
    (c : Context Point) (u : State Point) : ScalarField Point :=
  (VariableGaugeMean.reconstructState g c u).pressure

/-- Axial debt potential, defined pointwise by `CorrectionState.axialDefect c u n s +
pressureCoefficient g n s * CorrectionState.pressureDefect c u n s`. -/
noncomputable def axialDebtPotential (g : VariableGaugeMean.GaugeData Plane)
    (c : Context Point) (u : State Point) : ScalarField Plane :=
  fun n s => CorrectionState.axialDefect c u n s +
    pressureCoefficient g n s * CorrectionState.pressureDefect c u n s

theorem pressureRecipe_movingField {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c)) :
    MovingField U g.radial.inner g.radial.outer (pressureRecipe g c u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change ContDiffOn ℝ ∞ (VariableGaugeMean.meanPressure g.radial.exponent g.radial.inner
      g.radial.outer (g.radial.frequency n) g.radial.inner_lt_outer (g.length n)
      g.radial.radialDirection (u.gr c n)) _
    rw [hg n]
    exact VariableGaugeMean.meanPressure_q_contDiffOn U ha g.radial.inner_lt_outer hd
      (g.radial.frequency n) g.radial.radialDirection (hf.smooth n) (hf.supported n)
  · intro n
    change VariableGaugeMean.SupportedGauge _ _ _ _
      (VariableGaugeMean.meanPressure g.radial.exponent g.radial.inner g.radial.outer
        (g.radial.frequency n) g.radial.inner_lt_outer (g.length n) g.radial.radialDirection (u.gr
            c n))
    rw [hg n]
    exact VariableGaugeMean.meanPressure_q_supportedGauge U ha g.radial.inner_lt_outer hd
      (g.radial.frequency n) g.radial.radialDirection (hf.smooth n) (hf.supported n)
  · intro n
    exact VariableGaugeMean.meanPressure_periodicOn g.radial.inner_lt_outer
      g.radial.exponent (g.radial.frequency n) (g.length n) g.radial.radialDirection (hf.periodic n)

theorem pressureRecipe_moment {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 (pressureRecipe g c u) n s =
      -(1 / 2 : ℝ) * CorrectionState.radialMoment 2 (u.gr c) n s +
      pressureCoefficient g n s * CorrectionState.pressureDefect c u n s := by
  have hl : 0 < g.length n s := by
    rw [hg n]
    exact VariableGaugeMean.qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)
  have hsp : VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (g.length n)
      U.carrier (u.gr c n) := by rw [hg n]; exact hf.supported n
  have hh := moving_pressure_moment (M := g.radial.frequency n) ha g.radial.inner_lt_outer hd
      (g.length n)
    g.radial.radialDirection U.isOpen (hf.smooth n) hsp (hf.periodic n) hs hl
  rw [state_radialMoment_eq, state_radialMoment_eq]
  simpa only [pressureRecipe, VariableGaugeMean.reconstructState, averaged,
    IntegratedMeanBalances.radialMoment, pressureCoefficient,
    CorrectionState.pressureDefect, CorrectionState.radialMoment, pow_zero, one_mul] using hh

theorem axial_flux_pressure_moment {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hZ : MovingField U g.radial.inner g.radial.outer (axialAxialFlux c u))
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 (axialAxialFlux c u + pressureRecipe g c u) n s =
      axialDebtPotential g c u n s := by
  obtain ⟨a, b, _, _, _, _, _, hl, hr, _⟩ :=
    VariableGaugeMean.qLength_reference_bounds U ha g.radial.inner_lt_outer
  rw [(hZ.containing hl hr).radialMoment_add U.isOpen
    ((pressureRecipe_movingField U g ha hd hg c u hf).containing hl hr) 1 n hs,
    pressureRecipe_moment U g ha hd hg c u hf n hs]
  simp only [axialDebtPotential, CorrectionState.axialDefect, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, axialAxialFlux]
  ring

theorem state_angular_moment {coord a b : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (r : ReconstructionData)
    (ε fast : ℕ → ℝ) (z t v : Plane) (c : Context Point) (u : State Point)
    (ho : c.operators = nativeOperators r ε fast z t v)
    (H : MovingAngularInputs U a b c u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 2 u.mean.angular n s = 0)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 2 (u.thetaResidual c) n s =
      ε n * fderiv ℝ (CorrectionState.thetaDefect c u n) s z := by
  obtain ⟨a', b', _, ha', _, _, _, hl, hr, _⟩ := VariableGaugeMean.qLength_reference_bounds U ha hab
  have he : u.thetaResidual c = fluxResidual (nativeOperators r ε fast z t v) 2 1
      u.mean.angular (thetaRadialFlux c u) (thetaAxialFlux c u) c.virtualTheta := by
    simp only [State.thetaResidual, MeanIncrementBounds.thetaResidual, fluxResidual,
      thetaRadialFlux, thetaAxialFlux, ho]
  rw [he]
  exact local_angular_moment ha' U.isOpen r ε fast z t v
    ⟨H.velocity.containing hl hr, H.radial.containing hl hr,
      H.axial.containing hl hr, H.stress.containing hl hr⟩ hmass n hs

/-- The residual is evaluated on the literal moving-gauge reconstruction.
The differentiated potential contains the full variable measured coefficient. -/
theorem reconstructed_state_axial_moment {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast : ℕ → ℝ) (z t v : Plane) (c : Context Point) (u : State Point)
    (ho : c.operators = nativeOperators g.radial ε fast z t v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 ((VariableGaugeMean.reconstructState g c u).axialResidual c) n s
        =
      ε n * fderiv ℝ (axialDebtPotential g c u n) s z := by
  obtain ⟨a', b', _, ha', _, _, _, hl, hr, _⟩ :=
    VariableGaugeMean.qLength_reference_bounds U ha g.radial.inner_lt_outer
  have hp := (pressureRecipe_movingField U g ha hd hg c u hf).containing hl hr
  have he : (VariableGaugeMean.reconstructState g c u).axialResidual c =
      fluxResidual (nativeOperators g.radial ε fast z t v) 1 0
        u.mean.axial (axialRadialFlux c u) (axialAxialFlux c u + pressureRecipe g c u)
            c.virtualAxial := by
    simp only [VariableGaugeMean.reconstructState, State.axialResidual,
      MeanIncrementBounds.axialResidual, fluxResidual, axialRadialFlux, axialAxialFlux,
      pressureRecipe, ho]
    rfl
  have hh := local_axial_moment ha' U.isOpen g.radial ε fast z t v
    ⟨H.velocity.containing hl hr, H.radial.containing hl hr,
      (H.axial.containing hl hr).add hp, H.stress.containing hl hr⟩ hmass n hs
  have heq : CorrectionState.radialMoment 1 (axialAxialFlux c u + pressureRecipe g c u) n =ᶠ[𝓝 s]
      axialDebtPotential g c u n := by
    filter_upwards [U.isOpen.mem_nhds hs] with q hq
    exact axial_flux_pressure_moment U g ha hd hg c u H.axial hf n hq
  rwa [he, ← heq.fderiv_eq]

theorem state_axial_moment {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast : ℕ → ℝ) (z t v : Plane) (c : Context Point) (u : State Point)
    (ho : c.operators = nativeOperators g.radial ε fast z t v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hfixed : VariableGaugeMean.reconstructState g c u = u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 (u.axialResidual c) n s =
      ε n * fderiv ℝ (axialDebtPotential g c u n) s z := by
  simpa only [hfixed] using
    reconstructed_state_axial_moment U g ha hd hg ε fast z t v c u ho H hf hmass n hs

end MovingState

/-! ## All variable-coefficient terms and the actual debt classes -/

section DebtClasses

open WeightedClasses LocalSignedRequest StateMomentBalances

theorem q_pressureCoefficient {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    pressureCoefficient g n s =
      basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
        SimilarityCoordinates.coordinateQ coord s := by
  unfold pressureCoefficient
  rw [hg n]
  unfold VariableGaugeMean.qLength
  rw [Real.sq_sqrt (SimilarityCoordinates.coordinateQ_spec U.coord_pos U.coord_lt_one
    (U.time_pos s hs)).1.le]

theorem pressureCoefficient_smooth {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord) (n : ℕ) :
    ContDiffOn ℝ ∞ (pressureCoefficient g n) U.carrier := by
  change ContDiffOn ℝ ∞ (fun s =>
    basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer * g.length n s ^
        2) _
  rw [hg n]
  exact contDiffOn_const.mul (((VariableGaugeMean.qLength_contDiffOn U.coord_pos
      U.coord_lt_one).mono
    (fun s hs => U.time_pos s hs)).pow 2)

theorem q_pressureCoefficient_fderiv {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) (v : Plane) :
    fderiv ℝ (pressureCoefficient g n) s v =
      basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
        ((v.1 + 2 * s.2 * SimilarityCoordinates.coordinateQ coord s ^ coord * v.2) /
          SimilarityCoordinates.scalarSlope coord s.2 (SimilarityCoordinates.coordinateQ coord s))
              := by
  have he : pressureCoefficient g n =ᶠ[𝓝 s]
      (fun t => basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
        SimilarityCoordinates.coordinateQ coord t) := by
    filter_upwards [U.isOpen.mem_nhds hs] with t ht
    exact q_pressureCoefficient U g hg n ht
  rw [he.fderiv_eq]
  have hd := ((SimilarityCoordinates.coordinateQ_smooth U.coord_pos U.coord_lt_one
    (U.time_pos s hs)).differentiableAt (by simp)).hasFDerivAt
  rw [(hd.const_mul (basePressureCoefficient g.radial.inner g.radial.outer
    g.radial.inner_lt_outer)).fderiv]
  change basePressureCoefficient _ _ _ * fderiv ℝ (SimilarityCoordinates.coordinateQ coord) s v = _
  rw [SimilarityCoordinates.coordinateQ_fderiv_apply U.coord_pos U.coord_lt_one (U.time_pos s hs)]

/-- On the positive axial half-plane the coefficient has a strictly positive
axial derivative, so replacing it by a constant would change the identity. -/
theorem q_pressureCoefficient_axial_derivative_pos {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) (hz : 0 < s.2) :
    0 < fderiv ℝ (pressureCoefficient g n) s (0, 1) := by
  have hq := SimilarityCoordinates.coordinateQ_spec U.coord_pos U.coord_lt_one (U.time_pos s hs)
  have hforward : 0 < SimilarityCoordinates.forwardScalar coord s.2
      (SimilarityCoordinates.coordinateQ coord s) := by rw [hq.2]; exact U.time_pos s hs
  have hsl := SimilarityCoordinates.scalarSlope_pos U.coord_pos U.coord_lt_one hq.1 hforward
  rw [q_pressureCoefficient_fderiv U g hg n hs]
  simp only [zero_add, mul_one]
  exact mul_pos (basePressureCoefficient_pos ha g.radial.inner_lt_outer)
    (div_pos (mul_pos (mul_pos (by norm_num) hz) (Real.rpow_pos_of_pos hq.1 coord)) hsl)

theorem axialDebtPotential_smooth {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hZ : MovingField U g.radial.inner g.radial.outer (axialAxialFlux c u))
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c)) (n : ℕ) :
    ContDiffOn ℝ ∞ (axialDebtPotential g c u n) U.carrier := by
  exact ((hZ.radialMoment_smooth ha g.radial.inner_lt_outer 1 n).sub
      ((hf.radialMoment_smooth ha g.radial.inner_lt_outer 2 n).const_smul (1 / 2 : ℝ))).add
    ((pressureCoefficient_smooth U g hg n).mul
      (hf.radialMoment_smooth ha g.radial.inner_lt_outer 0 n))

/-- The product rule is applied to the actual measured coefficient. In
particular, the last summand is present even if the unweighted debts are known. -/
theorem axialDebtPotential_fderiv {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hZ : MovingField U g.radial.inner g.radial.outer (axialAxialFlux c u))
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) (v : Plane) :
    fderiv ℝ (axialDebtPotential g c u n) s v =
      fderiv ℝ (CorrectionState.axialDefect c u n) s v +
      pressureCoefficient g n s * fderiv ℝ (CorrectionState.pressureDefect c u n) s v +
      fderiv ℝ (pressureCoefficient g n) s v * CorrectionState.pressureDefect c u n s := by
  have hP : ContDiffOn ℝ ∞ (CorrectionState.pressureDefect c u n) U.carrier :=
    hf.radialMoment_smooth ha g.radial.inner_lt_outer 0 n
  have hJ : ContDiffOn ℝ ∞ (CorrectionState.axialDefect c u n) U.carrier :=
    (hZ.radialMoment_smooth ha g.radial.inner_lt_outer 1 n).sub
      ((hf.radialMoment_smooth ha g.radial.inner_lt_outer 2 n).const_smul (1 / 2 : ℝ))
  have hp := ((hP.contDiffAt (U.isOpen.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
  have hj := ((hJ.contDiffAt (U.isOpen.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
  have hc := (((pressureCoefficient_smooth U g hg n).contDiffAt
    (U.isOpen.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
  change fderiv ℝ (fun s => CorrectionState.axialDefect c u n s +
    pressureCoefficient g n s * CorrectionState.pressureDefect c u n s) s v = _
  rw [(hj.fun_add (hc.fun_mul hp)).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- Explicit native `Z` balance, with the moving-density derivative retained. -/
theorem state_axial_moment_expanded {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast : ℕ → ℝ) (v : Plane) (c : Context Point) (u : State Point)
    (ho : c.operators = nativeOperators g.radial ε fast (0, 1) (1, 0) v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hfixed : VariableGaugeMean.reconstructState g c u = u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 (u.axialResidual c) n s = ε n *
      (fderiv ℝ (CorrectionState.axialDefect c u n) s (0, 1) +
        pressureCoefficient g n s * fderiv ℝ (CorrectionState.pressureDefect c u n) s (0, 1) +
        (basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
          ((2 * s.2 * SimilarityCoordinates.coordinateQ coord s ^ coord) /
            SimilarityCoordinates.scalarSlope coord s.2 (SimilarityCoordinates.coordinateQ coord
                s))) *
          CorrectionState.pressureDefect c u n s) := by
  rw [state_axial_moment U g ha hd hg ε fast (0, 1) (1, 0) v c u ho H hf hfixed hmass n hs,
    axialDebtPotential_fderiv U g ha hg c u H.axial hf n hs,
    q_pressureCoefficient_fderiv U g hg n hs]
  simp only [zero_add, mul_one]

theorem pressureCoefficient_unweighted {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord) :
    UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) 0
      (fun n x => pressureCoefficient g n x.2.1) := by
  have hq := qPower_unweighted U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL 1
  simp only [Real.rpow_one] at hq
  have hc := hq.map ((ContinuousLinearMap.lsmul ℝ ℝ)
    (basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer))
  apply MeanIncrementBounds.class_congr hc
  intro n x hx
  have hs := ((movingStrip_domain U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL x).mp hx).1
  change pressureCoefficient g n x.2.1 =
    basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
      SimilarityCoordinates.coordinateQ coord x.2.1
  exact q_pressureCoefficient U g hg n hs

/-- The combined potential has the same all-jet order as its actual two
debt components. The coefficient estimate uses the same moving strip. -/
theorem axialDebtPotential_unweighted {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point) (α : ℝ)
    (hP : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.pressureDefect c u n x.2.1))
    (hZ : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.axialDefect c u n x.2.1)) :
    UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => axialDebtPotential g c u n x.2.1) := by
  have hc := (pressureCoefficient_unweighted U P hcL hcR ε L hε hεone hL g hg).mul hP
  simp only [one_mul, zero_add] at hc
  exact hZ.add hc

end DebtClasses

/-! ## Removed physical bumps for the same actual residuals -/

section RemovedBumps

open WeightedClasses LocalSignedRequest StateMomentBalances

/-- The literal angular residual, its measured mass, and the removed physical
bump all refer to the same state and moving chart. -/
theorem state_angular_bump_improvedClass {coord a b : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ha : 0 < a) (hab : a < b) (r : ReconstructionData)
    (ε fast L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (z t v : Plane) (c : Context Point) (u : State Point) (α : ℝ)
    (ho : c.operators = nativeOperators r ε fast z t v)
    (H : MovingAngularInputs U a b c u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 2 u.mean.angular n s = 0)
    (hD : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.thetaDefect c u n x.2.1)) :
    MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) (α + 1)
      (fun n x => SignedStressPrimitive.physicalBump P 2 (SimilarityCoordinates.coordinateQ coord)
        (PressureStream.torusAverage (u.thetaResidual c n)) (x.1, x.2.1)) := by
  apply physicalBump_improvedClass_of_moment U P 2 hcL hcR ε L hε hεone hL
    (u.thetaResidual c) (CorrectionState.thetaDefect c u) z α
    (fun n => H.axial.radialMoment_smooth ha hab 2 n) hD
  intro n s hs
  change IntegratedMeanBalances.radialMoment 2 (averaged (u.thetaResidual c) n) s = _
  rw [← state_radialMoment_eq]
  exact state_angular_moment U ha hab r ε fast z t v c u ho H hmass n hs

/-- Direct reconstruction version: the source is the actual axial residual
after applying the moving pressure recipe, with no moment identity as input. -/
theorem reconstructed_state_axial_bump_improvedClass {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (z t v : Plane) (c : Context Point) (u : State Point) (α : ℝ)
    (ho : c.operators = nativeOperators g.radial ε fast z t v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (hP : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.pressureDefect c u n x.2.1))
    (hZ : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.axialDefect c u n x.2.1)) :
    MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) (α + 1)
      (fun n x => SignedStressPrimitive.physicalBump P 1 (SimilarityCoordinates.coordinateQ coord)
        (PressureStream.torusAverage ((VariableGaugeMean.reconstructState g c u).axialResidual c n))
        (x.1, x.2.1)) := by
  apply physicalBump_improvedClass_of_moment U P 1 hcL hcR ε L hε hεone hL
    ((VariableGaugeMean.reconstructState g c u).axialResidual c) (axialDebtPotential g c u) z α
    (axialDebtPotential_smooth U g ha hg c u H.axial hf)
    (axialDebtPotential_unweighted U P hcL hcR ε L hε hεone hL g hg c u α hP hZ)
  intro n s hs
  change IntegratedMeanBalances.radialMoment 1
    (averaged ((VariableGaugeMean.reconstructState g c u).axialResidual c) n) s = _
  rw [← state_radialMoment_eq]
  exact reconstructed_state_axial_moment U g ha hd hg ε fast z t v c u ho H hf hmass n hs

/-- Fixed-point version for the actual output of a temporal or rank stage,
whose constructor finishes with `reconstructState`. -/
theorem state_axial_bump_improvedClass {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (z t v : Plane) (c : Context Point) (u : State Point) (α : ℝ)
    (ho : c.operators = nativeOperators g.radial ε fast z t v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hfixed : VariableGaugeMean.reconstructState g c u = u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (hP : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.pressureDefect c u n x.2.1))
    (hZ : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.axialDefect c u n x.2.1)) :
    MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) (α + 1)
      (fun n x => SignedStressPrimitive.physicalBump P 1 (SimilarityCoordinates.coordinateQ coord)
        (PressureStream.torusAverage (u.axialResidual c n)) (x.1, x.2.1)) := by
  simpa only [hfixed] using reconstructed_state_axial_bump_improvedClass U P hcL hcR g ha hd hg
    ε fast L hε hεone hL z t v c u α ho H hf hmass hP hZ

end RemovedBumps

end NavierStokes.GaugeMomentBalances
