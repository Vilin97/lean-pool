/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketData
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRecursion
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPressure
import LeanPool.NavierStokesAndEuler.Euler.ContinuousForcingTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalSpatialTime
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.MeanConcreteTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPhysical
import LeanPool.NavierStokesAndEuler.Euler.MeanPhysicalTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanSourceSpatialRegularity
import LeanPool.NavierStokesAndEuler.Euler.MeanStrongGevrey
public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import LeanPool.NavierStokesAndEuler.Euler.LpDerivativeBundling
import LeanPool.NavierStokesAndEuler.Euler.LpDominatedDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Admissible raw mean forcing and its actual solved continuous paths

Admissibility consists of literal smooth spatial L² slices and continuity of
their L² spatial jets. All translation regularity below is derived. The
solution paths are obtained by the concrete source inverse in MeanPacketData.
-/

section

/-! Actual spatial derivatives of the forcing supply the time-space translation hypotheses. -/

section

/-! Smooth parameter dependence in actual L² from square-integrable fiberwise jets. -/

@[expose] public section

noncomputable section

namespace EulerLpSmoothFamily

open MeasureTheory Filter EulerLpDerivative
open scoped ContDiff Topology

universe u v w

variable {X : Type u} [MeasurableSpace X] {P : Type v}
  [NormedAddCommGroup P] [NormedSpace ℝ P] {V : Type w}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual parameter jets on almost every fiber, with one L² majorant per derivative order. -/
structure SmoothFamily (μ : Measure X) (P : Type v) (V : Type w)
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- Underlying field of `SmoothFamily`, of type `P → X → V`. -/
  field : P → X → V
  smooth : ∀ᵐ x ∂μ, ContDiff ℝ ∞ (fun a => field a x)
  /-- Jet of `SmoothFamily`, of type `(n : ℕ) → P → Lp (P [×n]→L[ℝ] V) 2 μ`. -/
  jet : (n : ℕ) → P → Lp (P [×n]→L[ℝ] V) 2 μ
  jet_ae : ∀ n a, jet n a =ᵐ[μ] fun x => iteratedFDeriv ℝ n (fun b => field b x) a
  /-- Bound of `SmoothFamily`, of type `ℕ → Lp ℝ 2 μ`. -/
  bound : ℕ → Lp ℝ 2 μ
  bounded : ∀ n, ∀ᵐ x ∂μ, ∀ a, ‖iteratedFDeriv ℝ n (fun b => field b x) a‖ ≤ bound n x

namespace SmoothFamily

variable {μ : Measure X}

/-- Value, given by `(continuousMultilinearCurryFin0 ℝ P
V).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ (A.jet 0 a)`. -/
def value (A : SmoothFamily μ P V) (a : P) : Lp V 2 μ :=
  (continuousMultilinearCurryFin0 ℝ P V).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 μ (A.jet 0 a)

theorem value_ae (A : SmoothFamily μ P V) (a : P) : A.value a =ᵐ[μ] A.field a := by
  filter_upwards [(continuousMultilinearCurryFin0 ℝ P
      V).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
    (A.jet 0 a), A.jet_ae 0 a] with x hx hj
  rw [show A.value a x = continuousMultilinearCurryFin0 ℝ P V (A.jet 0 a x) from hx, hj]
  rw [iteratedFDeriv_zero_eq_comp]
  exact (continuousMultilinearCurryFin0 ℝ P V).apply_symm_apply _

/-- Derivative, bundling `field`, `smooth`, `jet`, `jet_ae` and the required compatibility
proofs. -/
def derivative (A : SmoothFamily μ P V) : SmoothFamily μ P (P →L[ℝ] V) where
  field a x := fderiv ℝ (fun b => A.field b x) a
  smooth := A.smooth.mono (fun _ hx => hx.fderiv_right (m := ∞) (by simp))
  jet n a := (continuousMultilinearCurryRightEquiv' ℝ n P
      V).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 μ (A.jet (n+1) a)
  jet_ae n a := by
    let L : (P [×(n+1)]→L[ℝ] V) →L[ℝ] (P [×n]→L[ℝ] (P →L[ℝ] V)) :=
      (continuousMultilinearCurryRightEquiv' ℝ n P V).toContinuousLinearEquiv.toContinuousLinearMap
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (𝕜 := ℝ) (𝕜' := ℝ)
      (E := P [×(n+1)]→L[ℝ] V) (F := P [×n]→L[ℝ] (P →L[ℝ] V))
      (σ := RingHom.id ℝ) L (A.jet (n+1) a), A.jet_ae (n+1) a] with x hx hj
    rw [hx, hj, iteratedFDeriv_succ_eq_comp_right]
    exact (continuousMultilinearCurryRightEquiv' ℝ n P V).apply_symm_apply _
  bound n := A.bound (n+1)
  bounded n := (A.bounded (n+1)).mono (fun x hx a => by
    simpa only [norm_iteratedFDeriv_fderiv] using hx a)

theorem bound_nonneg (A : SmoothFamily μ P V) (n : ℕ) : ∀ᵐ x ∂μ, 0 ≤ A.bound n x :=
  (A.bounded n).mono (fun _ hx => (norm_nonneg _).trans (hx 0))

theorem hasFDerivAt_value (A : SmoothFamily μ P V) (a : P) :
    HasFDerivAt A.value (derivativeMap μ (A.derivative.value a)) a := by
  have hshift : HasFDerivAt (fun b => A.value (b+a))
      (derivativeMap μ (A.derivative.value a)) 0 := by
    apply EulerLpDerivative.hasFDerivAt_of_dominated μ
      (fun b => A.value (b+a)) (fun b x => A.field (b+a) x)
      (fun b => A.value_ae (b+a)) (A.derivative.value a) _ (A.bound 1)
      (Lp.memLp (A.bound 1)) (A.bound_nonneg 1)
    · apply Eventually.of_forall
      intro b
      filter_upwards [A.smooth, A.bounded 1] with x hx hb
      have hd (c : P) : ‖fderiv ℝ (fun d => A.field d x) c‖ ≤ A.bound 1 x := by
        simpa only [norm_iteratedFDeriv_one] using hb c
      have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ) (f := fun c => A.field c x) (s := Set.univ)
        (fun c _ => hx.differentiable (by simp) c) (fun c _ => hd c)
        (convex_univ : Convex ℝ (Set.univ : Set P)) (Set.mem_univ a) (Set.mem_univ (b+a))
      simpa only [zero_add, add_sub_cancel_right] using hh
    · filter_upwards [A.smooth, A.derivative.value_ae a] with x hx hd
      rw [hd]
      change HasFDerivAt (fun b => A.field (b+a) x)
        (fderiv ℝ (fun b => A.field b x) a) (0 : P)
      apply (hasFDerivAt_comp_add_right (f := fun b => A.field b x) a).mpr
      simpa only [zero_add] using (hx.differentiable (by simp) a).hasFDerivAt
  simpa only [zero_add] using (hasFDerivAt_comp_add_right a).mp hshift

theorem fderiv_value (A : SmoothFamily μ P V) :
    fderiv ℝ A.value = fun a => derivativeBundling μ (A.derivative.value a) :=
  funext (fun a => (A.hasFDerivAt_value a).fderiv)

end SmoothFamily

end EulerLpSmoothFamily

end
end

end

section

/-! All-order L² parameter regularity with the original square-integrable derivative bounds. -/

@[expose] public section

noncomputable section

namespace EulerLpSmoothFamily.SmoothFamily

open MeasureTheory Filter EulerLpDerivative
open scoped ContDiff Topology

universe u w

variable {X : Type u} [MeasurableSpace X] {μ : Measure X} {P : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] {V : Type w}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem contDiff_value_nat_aux (n : ℕ) :
    ∀ (V : Type w) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothFamily μ P V),
      ContDiff ℝ n A.value := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun a => (A.hasFDerivAt_value a).continuousAt))
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.hasFDerivAt_value a).differentiableAt, by simp, ?_⟩
    rw [A.fderiv_value]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : WithTop ℕ∞))
      (E := Lp (P →L[ℝ] V) 2 μ) (F := P →L[ℝ] Lp V 2 μ)
      (derivativeBundling μ)).comp (ih (P →L[ℝ] V) A.derivative)

/-- Genuine smoothness in the full L² norm, not merely pointwise in the measured variable. -/
theorem contDiff_value (A : SmoothFamily μ P V) : ContDiff ℝ ∞ A.value :=
  contDiff_infty.mpr (fun n => contDiff_value_nat_aux n V A)

theorem norm_value_le (A : SmoothFamily μ P V) (a : P) : ‖A.value a‖ ≤ ‖A.bound 0‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [A.value_ae a, A.bounded 0] with x hx hb
  rw [hx]
  have hh : ‖A.field a x‖ ≤ A.bound 0 x := by simpa only [norm_iteratedFDeriv_zero] using hb a
  exact hh.trans (le_abs_self (A.bound 0 x))

private theorem norm_iteratedFDeriv_value_aux (n : ℕ) :
    ∀ (V : Type w) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothFamily μ P V) (a : P),
      ‖iteratedFDeriv ℝ n A.value a‖ ≤ ‖A.bound n‖ := by
  induction n with
  | zero =>
    intro V _ _ A a
    rw [norm_iteratedFDeriv_zero]
    exact A.norm_value_le a
  | succ n ih =>
    intro V _ _ A a
    rw [← norm_iteratedFDeriv_fderiv, A.fderiv_value]
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := P)
      (F := Lp (P →L[ℝ] V) 2 μ) (G := P →L[ℝ] Lp V 2 μ)
      (derivativeBundling μ) (A.derivative.contDiff_value.contDiffAt (x := a)) (n := n) (by simp)
    have hi := ih (P →L[ℝ] V) A.derivative a
    rw [show A.derivative.bound n = A.bound (n+1) from rfl] at hi
    exact h.trans ((mul_le_mul_of_nonneg_right
      (derivativeBundling_norm_le_one (P := P) (V := V) μ) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hi))

/-- Each true L² derivative inherits its original fiberwise L² majorant with constant one. -/
theorem norm_iteratedFDeriv_value_le (A : SmoothFamily μ P V) (n : ℕ) (a : P) :
    ‖iteratedFDeriv ℝ n A.value a‖ ≤ ‖A.bound n‖ := norm_iteratedFDeriv_value_aux n V A a

end EulerLpSmoothFamily.SmoothFamily

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanForcing

open MeasureTheory EulerSmoothLimit EulerLpTranslation EulerLpDerivative
  EulerTimeLp EulerTimeLpBoundedMap EulerLpSmoothFamily Filter
open scoped ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem orbitJet_memLp (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T)) (n : ℕ) (a : Space) :
    MemLp (fun t => iteratedFDeriv ℝ n (fun b : Space => translation b (A t).toLp) a)
      2 (timeMeasure T) := by
  have h := ((hA n).continuousLinearMap_comp (translation (V := Space [×n]→L[ℝ] V)
      a).toContinuousLinearMap).continuousLinearMap_comp
    (multilinearBundling (P := Space) (V := V) volume n)
  exact h.ae_eq (Eventually.of_forall (fun t => (A t).iteratedFDeriv_translation_eq n a |>.symm))

/-- Forcing family, bundling `field`, `smooth`, `jet`, `jet_ae` and the required compatibility
proofs. -/
def forcingFamily (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T)) :
    SmoothFamily (timeMeasure T) Space (L2Space V) where
  field a t := translation a (A t).toLp
  smooth := Eventually.of_forall (fun t => (A t).translation_contDiff)
  jet n a := (orbitJet_memLp T A hA n a).toLp
    (fun t => iteratedFDeriv ℝ n (fun b : Space => translation b (A t).toLp) a)
  jet_ae n a := (orbitJet_memLp T A hA n a).coeFn_toLp
  bound n := (hA n).norm.toLp (fun t => ‖(A t).jetLp n‖)
  bounded n := by
    filter_upwards [(hA n).norm.coeFn_toLp] with t ht
    intro a
    rw [ht]
    exact (A t).norm_iteratedFDeriv_translation_le n a

theorem forcingFamily_value_eq (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T))
    (f : TimeLp T (L2Space V)) (hf : f =ᵐ[timeMeasure T] fun t => (A t).toLp) (a : Space) :
    (forcingFamily T A hA).value a = timeLiftIsometry T (translation a) f := by
  apply Lp.ext
  filter_upwards [(forcingFamily T A hA).value_ae a,
    timeLift_ae T (translation a).toContinuousLinearMap f, hf] with t hv ht he
  change (forcingFamily T A hA).value a t = timeLift T (translation a).toContinuousLinearMap f t
  rw [hv, ht, he]
  rfl

/-- Smooth forcing slices with actual square-integrable spatial jets have a smooth Bochner
translation orbit. -/
theorem forcing_translation_contDiff (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T))
    (f : TimeLp T (L2Space V)) (hf : f =ᵐ[timeMeasure T] fun t => (A t).toLp) :
    ContDiff ℝ ∞ (fun a : Space => timeLiftIsometry T (translation a) f) := by
  have he : (fun a : Space => timeLiftIsometry T (translation a) f) = (forcingFamily T A hA).value
      :=
    funext (fun a => (forcingFamily_value_eq T A hA f hf a).symm)
  rw [he]
  exact (forcingFamily T A hA).contDiff_value

/-- The true time-space derivative norm is bounded by the original ordinary spatial jet norm,
without extra factors. -/
theorem forcing_translation_jet_bound (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T))
    (f : TimeLp T (L2Space V)) (hf : f =ᵐ[timeMeasure T] fun t => (A t).toLp)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => timeLiftIsometry T (translation b) f) a‖ ≤
      ‖(hA n).toLp (fun t => (A t).jetLp n)‖ := by
  have he : (fun b : Space => timeLiftIsometry T (translation b) f) = (forcingFamily T A hA).value
      :=
    funext (fun b => (forcingFamily_value_eq T A hA f hf b).symm)
  have h := (forcingFamily T A hA).norm_iteratedFDeriv_value_le n a
  have hn : ‖(forcingFamily T A hA).bound n‖ = ‖(hA n).toLp (fun t => (A t).jetLp n)‖ := by
    change ‖(hA n).norm.toLp (fun t => ‖(A t).jetLp n‖)‖ = _
    simp only [Lp.norm_toLp, eLpNorm_norm]
  exact (congrArg (fun g : Space → TimeLp T (L2Space V) =>
    ‖iteratedFDeriv ℝ n g a‖) he).trans_le (h.trans_eq hn)

end EulerMeanForcing

end
end

end

section

/-!
# Continuous ordinary forcing jets supply the Bochner hypotheses

On the compact time interval, continuous actual spatial L² jets are
automatically square integrable. The continuous and Bochner orbit theorems
therefore use the same concrete forcing data.
-/

@[expose] public section

noncomputable section

namespace EulerContinuousForcing

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerTimeLp EulerVolterraConvolution

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem spatialJets_memLp (T : ℝ) (hT : 0 ≤ T) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t : Icc (0 : ℝ) T => (A t).jetLp n)) (n : ℕ) :
    MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T) := by
  let J : C(Icc (0 : ℝ) T,L2Space (Space [×n]→L[ℝ] V)) :=
    spatialJetPath (fun t : Icc (0 : ℝ) T => A t) hA n
  apply (path_memLp T hT J).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change (A (projIcc 0 T hT t)).jetLp n = (A t).jetLp n
  rw [projIcc_of_mem hT ht]

theorem forcing_representation (T : ℝ) (hT : 0 ≤ T) (A : ℝ → SmoothL2Field V)
    (fC : C(Icc (0 : ℝ) T, L2Space V)) (hC : ∀ t, fC t = (A t).toLp)
    (f : TimeLp T (L2Space V))
    (hf : (f : ℝ → L2Space V) =ᵐ[timeMeasure T] extendPath T hT fC) :
    (f : ℝ → L2Space V) =ᵐ[timeMeasure T] fun t => (A t).toLp := by
  filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with t ht hmem
  rw [ht]
  change fC (projIcc 0 T hT t) = (A t).toLp
  rw [hC, projIcc_of_mem hT hmem]

end EulerContinuousForcing

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanSourceInverse EulerMeanVariationalInverse
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerTimeLp EulerVolterraConvolution EulerPacketProfileRecursion
open scoped ContDiff

/-- Literal raw-field regularity, with no hypothesis on a solved field. -/
structure Forcing (D : Data) (raw : VectorField) where
  /-- Slices of `Forcing`, of type `ℝ → EulerLpTranslation.SmoothL2Field Space`. -/
  slices : ℝ → EulerLpTranslation.SmoothL2Field Space
  jets_continuous : ∀ n, Continuous (fun t : Icc (0 : ℝ) D.T => (slices t).jetLp n)
  /-- Time-dependent path of `Forcing`, of type `C(Icc (0 : ℝ) D.T,L2)`. -/
  path : C(Icc (0 : ℝ) D.T,L2)
  path_eq : ∀ t, path t = (slices t).toLp
  raw_eq : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(x,θ)) = (slices t).field x

namespace Data

variable (D : Data)

theorem opF_orbit : ContDiff ℝ ∞ (fun a : Space => translatePath D.T a D.opF) := by
  simpa only [opF, translatePath_operatorPath] using operatorPathTranslation_contDiff D.T D.F

theorem opF₁_orbit : ContDiff ℝ ∞ (fun a : Space => translatePath D.T a D.opF₁) := by
  simpa only [opF₁, translatePath_operatorPath] using operatorPathTranslation_contDiff D.T D.F₁

theorem opF_initial : D.opF ⟨0, le_rfl, D.T_pos.le⟩ = ContinuousLinearMap.id ℝ L2 := by
  apply ContinuousLinearMap.ext
  intro v
  have hi := D.opInv_left ⟨0, le_rfl, D.T_pos.le⟩ v
  rw [D.opInv_initial] at hi
  exact hi

end Data

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

/-- The genuine Bochner L² class of the prescribed forcing. -/
def lp : TimeLp D.T L2 := pathLp D.T D.T_pos.le G.path

theorem lp_rep : (G.lp : ℝ → L2) =ᵐ[timeMeasure D.T] extendPath D.T D.T_pos.le G.path :=
  pathLp_ae D.T D.T_pos.le G.path

theorem lp_orbit : ContDiff ℝ ∞ (fun a : Space => timeTranslation D.T a G.lp) :=
  EulerMeanForcing.forcing_translation_contDiff D.T G.slices
    (EulerContinuousForcing.spatialJets_memLp D.T D.T_pos.le G.slices G.jets_continuous) G.lp
    (EulerContinuousForcing.forcing_representation D.T D.T_pos.le G.slices G.path G.path_eq G.lp
        G.lp_rep)

theorem path_orbit : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a G.path) :=
  EulerContinuousForcing.forcing_translation_contDiff
    (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous G.path G.path_eq

/-- Solution: an abbreviation for `D.evolution G.lp`. -/
abbrev solution := D.evolution G.lp

/-- Spatial smoothness of the actually solved coordinate velocity. -/
theorem coordinate_orbit : ContDiff ℝ ∞
    (fun a : Space => timeSolenoidalTranslation D.T a G.solution.velocityLp) :=
  EulerMeanSourceSpatialRegularity.velocity_translation_contDiff
    D.T D.T_pos.le D.ℓ D.ℓ_pos D.F D.F₁ D.H D.M0 D.opInv D.Be D.Bc D.L D.r
    D.Be_nonneg D.Bc_nonneg D.L_lower D.r_nonneg D.r_le_quarter D.exterior_lower D.core_lower
    D.opInv_left D.opF_time D.opInv_right D.K D.K_nonneg D.opInv_initial D.curvature_upper D.small
    G.lp G.solution G.lp_orbit

theorem acceleration_orbit : ContDiff ℝ ∞
    (fun a : Space => timeSolenoidalTranslation D.T a G.solution.acceleration) :=
  G.solution.acceleration_orbit_contDiff D.frameLower D.frameLower_pos D.frame_lower
    D.opF_orbit D.opF₁_orbit G.coordinate_orbit G.lp_orbit

theorem coordinatePath_orbit : ContDiff ℝ ∞
    (fun a : Space => coordinatePathTranslation D.T a G.solution.coordinateVelocityPath) :=
  G.solution.coordinateVelocityPath_translation_contDiff D.T_pos G.coordinate_orbit
      G.acceleration_orbit

/-- Velocity path: an abbreviation for `G.solution.continuousVelocity`. -/
abbrev velocityPath := G.solution.continuousVelocity
/-- Acceleration path: an abbreviation for `G.solution.classicalAcceleration D.frameLower
D.frameLower_pos D.frame_lower G.path`. -/
abbrev accelerationPath := G.solution.classicalAcceleration D.frameLower D.frameLower_pos
    D.frame_lower G.path
/-- Derivative path: an abbreviation for `G.solution.classicalPhysicalDerivative D.frameLower
D.frameLower_pos D.frame_lower G.path`. -/
abbrev derivativePath := G.solution.classicalPhysicalDerivative D.frameLower D.frameLower_pos
    D.frame_lower G.path
/-- Pressure force path: an abbreviation for `G.solution.pressurePath D.frameLower
D.frameLower_pos D.frame_lower G.path`. -/
abbrev pressureForcePath := G.solution.pressurePath D.frameLower D.frameLower_pos D.frame_lower
    G.path

theorem velocityPath_orbit : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a G.velocityPath) :=
  G.solution.continuousVelocity_translation_contDiff
    (G.solution.velocityField_translation_contDiff D.opF_orbit G.coordinate_orbit)
    (G.solution.velocityDerivative_translation_contDiff D.opF_orbit D.opF₁_orbit
      G.coordinate_orbit G.acceleration_orbit)

theorem accelerationPath_orbit : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation D.T a
    G.accelerationPath) :=
  G.solution.classicalAcceleration_translation_contDiff D.frameLower D.frameLower_pos D.frame_lower
      G.path
    D.opF_orbit D.opF₁_orbit G.coordinatePath_orbit G.path_orbit

theorem derivativePath_orbit : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a
    G.derivativePath) :=
  G.solution.classicalPhysicalDerivative_translation_contDiff D.frameLower D.frameLower_pos
      D.frame_lower G.path
    D.opF_orbit D.opF₁_orbit G.coordinatePath_orbit G.path_orbit

theorem pressureForcePath_orbit : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a
    G.pressureForcePath) :=
  G.solution.pressurePath_translation_contDiff D.frameLower D.frameLower_pos D.frame_lower G.path
    D.opF_orbit D.opF₁_orbit G.coordinatePath_orbit G.accelerationPath_orbit G.path_orbit

theorem velocityPath_time : ∀ t : Icc (0 : ℝ) D.T,
    HasDerivWithinAt (extendPath D.T D.T_pos.le G.velocityPath) (G.derivativePath t) (Icc (0 : ℝ)
        D.T) t :=
  G.solution.continuousVelocity_hasDerivWithinAt D.frameLower D.frameLower_pos D.frame_lower G.path
    D.T_pos G.lp_rep D.opF_time

end Forcing

end EulerMeanPacketProvider
