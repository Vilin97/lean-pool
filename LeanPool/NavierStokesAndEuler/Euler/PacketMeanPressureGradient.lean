/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketPressureForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketCylinderFields
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientFrame
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketJets
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialEmbedding
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.PacketScalarPressureGradient
public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAssembly
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPressureLocality
import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketCoordinateResidual
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionSourceData
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionResidualCancellation

/-! Related estimates used together by the same construction modules. -/

section

/-! The actual mean pressure enters the lifted gradient closure.
Only its genuine L² gradient is embedded; its scalar potential need not be L². -/

section

/-! Actual scalar pressures whose lifted gradients are smooth L² fields.
The witnesses below are closed under the literal finite packet assembly. -/

@[expose] public section

noncomputable section

namespace EulerPacketPressure

open Set MeasureTheory ContinuousLinearMap InnerProductSpace Finset EulerSmoothLimit
  EulerPacketPointJets EulerPacketProfileRecursion EulerPacketCylinderField
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderScalarPrimitive
  EulerFiniteGrades
open scoped ContDiff

theorem rawGradient_component (κ : ℝ) (m : Space) (p : ScalarField) (z : Domain)
    (i : Fin 3) :
    rawGradient κ m p z i =
      κ * fderiv ℝ (fun y => p (z.1,y)) z.2 (EuclideanSpace.single i 1,0) +
        fderiv ℝ (fun y => p (z.1,y)) z.2 (0,1) * m i := by
  rw [rawGradient,pressureGradient_eq_spatialDual,pressureJet_angle]
  have h := toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i 1)
    (y := (fderiv ℝ (fun y => p (z.1,y)) z.2).comp (inl ℝ Space ℝ))
  have hi : ((toDual ℝ Space).symm
      ((fderiv ℝ (fun y => p (z.1,y)) z.2).comp (inl ℝ Space ℝ))) i =
      fderiv ℝ (fun y => p (z.1,y)) z.2 (EuclideanSpace.single i 1,0) := by
    simpa only [EuclideanSpace.inner_single_right,conj_trivial,one_mul,comp_apply,inl_apply] using h
  convert! congrArg (fun a : ℝ => κ*a +
    fderiv ℝ (fun y => p (z.1,y)) z.2 (0,1)*m i) hi using 1

theorem rawGradient_zero (κ : ℝ) (m : Space) : rawGradient κ m 0 = 0 := by
  funext z
  simp [rawGradient,pressureGradient,pressureJet_zero]

theorem rawGradient_add (κ : ℝ) (m : Space) (p q : ScalarField) (z : Domain)
    (hp : DifferentiableAt ℝ (fun y => p (z.1, y)) z.2)
    (hq : DifferentiableAt ℝ (fun y => q (z.1, y)) z.2) :
    rawGradient κ m (p+q) z = rawGradient κ m p z + rawGradient κ m q z := by
  ext i
  change rawGradient κ m (p+q) z i = rawGradient κ m p z i + rawGradient κ m q z i
  simp only [rawGradient_component,Pi.add_apply,fderiv_fun_add hp hq,add_apply]
  change κ * (_+_) + (_+_) * m i = (κ*_+_*m i)+(κ*_+_*m i)
  ring

theorem rawGradient_smul (κ : ℝ) (m : Space) (c : ℝ) (p : ScalarField) (z : Domain)
    (hp : DifferentiableAt ℝ (fun y => p (z.1, y)) z.2) :
    rawGradient κ m (c • p) z = c • rawGradient κ m p z := by
  ext i
  change rawGradient κ m (c • p) z i = c * rawGradient κ m p z i
  simp only [rawGradient_component,Pi.smul_apply,fderiv_fun_const_smul hp,smul_apply]
  change κ*(c*_) + (c*_)*m i = c*(κ*_+_*m i)
  ring

theorem rawGradient_sum {ι : Type*} (κ : ℝ) (m : Space) (s : Finset ι)
    (p : ι → ScalarField) (z : Domain)
    (hp : ∀ i ∈ s, DifferentiableAt ℝ (fun y => p i (z.1, y)) z.2) :
    rawGradient κ m (∑ i ∈ s, p i) z = ∑ i ∈ s, rawGradient κ m (p i) z := by
  classical
  ext j
  simp only [WithLp.ofLp_sum,Finset.sum_apply,rawGradient_component,
    fderiv_fun_sum hp,_root_.sum_apply]
  change κ*(∑ i ∈ s, _) + (∑ i ∈ s, _)*m j =
    ∑ i ∈ s, (κ*_+_*m j)
  rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]

/-- Gradient witness data, collecting `smooth`, `field`, `gradient_mem`. -/
structure GradientWitness (P T κ : ℝ) [Fact (0 < P)] (m : Space) (p : ScalarField) where
  smooth : ∀ t : Icc (0 : ℝ) T, ContDiff ℝ ∞ (fun y => p (t,y))
  /-- Underlying field of `GradientWitness`, of type `Field P T (rawGradient κ m p)`. -/
  field : Field P T (rawGradient κ m p)
  gradient_mem : ∀ t : Icc (0 : ℝ) T, field.path t ∈ gradientSpace P κ m

namespace GradientWitness

variable {P T κ : ℝ} [Fact (0 < P)] {m : Space} {p q : ScalarField}

/-- Congr, given by `h ▸ G`. -/
def congr (G : GradientWitness P T κ m p) (h : p = q) : GradientWitness P T κ m q := h ▸ G

/-- Change time, given by `h ▸ G`. -/
def changeTime {T' : ℝ} (G : GradientWitness P T κ m p) (h : T = T') :
    GradientWitness P T' κ m p := h ▸ G

/-- Zero, bundling `smooth`, `field`, `gradient_mem`. -/
def zero (P T κ : ℝ) [Fact (0 < P)] (m : Space) : GradientWitness P T κ m 0 where
  smooth _ := contDiff_const
  field := (Field.zero P T).congr (fun _ _ _ => congrFun (rawGradient_zero κ m) _)
  gradient_mem _ := (gradientSpace P κ m).zero_mem

/-- Add, bundling `smooth`, `field`, `gradient_mem`. -/
def add (G : GradientWitness P T κ m p) (H : GradientWitness P T κ m q) :
    GradientWitness P T κ m (p+q) where
  smooth t := (G.smooth t).add (H.smooth t)
  field := (G.field.add H.field).congr (fun t x θ =>
    rawGradient_add κ m p q (t,(x,θ))
      ((G.smooth t).differentiable (by simp) _) ((H.smooth t).differentiable (by simp) _))
  gradient_mem t := (gradientSpace P κ m).add_mem (G.gradient_mem t) (H.gradient_mem t)

/-- Smul, bundling `smooth`, `field`, `gradient_mem`. -/
def smul (G : GradientWitness P T κ m p) (c : ℝ) : GradientWitness P T κ m (c • p) where
  smooth t := (G.smooth t).const_smul c
  field := (G.field.smul c).congr (fun t x θ =>
    rawGradient_smul κ m c p (t,(x,θ)) ((G.smooth t).differentiable (by simp) _))
  gradient_mem t := (gradientSpace P κ m).smul_mem c (G.gradient_mem t)

/-- Finset sum, bundling `smooth`, `simpa`, `field`, `gradient_mem` and the required
compatibility proofs. -/
def finsetSum {ι : Type*} (s : Finset ι) (p : ι → ScalarField)
    (G : ∀ i, GradientWitness P T κ m (p i)) :
    GradientWitness P T κ m (∑ i ∈ s, p i) where
  smooth t := by
    simpa only [Finset.sum_apply] using ContDiff.sum (fun i (_ : i ∈ s) => (G i).smooth t)
  field := (Field.finsetSum s (fun i => rawGradient κ m (p i)) (fun i => (G i).field)).congr
    (fun t x θ => by
      rw [rawGradient_sum κ m s p (t,(x,θ))
        (fun i _ => ((G i).smooth t).differentiable (by simp) _)]
      exact (Finset.sum_apply _ _ _).symm)
  gradient_mem t := by
    change (∑ i ∈ s, (G i).field.path) t ∈ gradientSpace P κ m
    rw [show (∑ i ∈ s, (G i).field.path) t = ∑ i ∈ s, (G i).field.path t from
      map_sum (ContinuousMap.evalCLM ℝ t) _ s]
    exact (gradientSpace P κ m).sum_mem (fun i _ => (G i).gradient_mem t)

/-- Truncate family as an element of `GradientWitness P T κ m (truncate N p n)`. -/
def truncateFamily (N : ℕ) (p : ℕ → ScalarField)
    (G : ∀ i, i ≤ N → GradientWitness P T κ m (p i)) (n : ℕ) :
    GradientWitness P T κ m (truncate N p n) := by
  by_cases hn : n ≤ N
  · exact (G n hn).congr (truncate_of_le N n p hn).symm
  · exact (zero P T κ m).congr (truncate_of_gt N n p (by omega)).symm

/-- Assemble family used in packet pressure witness. -/
def assembleFamily (N : ℕ) (p q : ℕ → ScalarField)
    (G : ∀ i, i ≤ N → GradientWitness P T κ m (p i))
    (H : ∀ i, i ≤ N → GradientWitness P T κ m (q i)) :
    (n : ℕ) → GradientWitness P T κ m (assemble N p q n)
  | 0 => (truncateFamily N p G 0).congr (by simp only [assemble,shiftUp,add_zero])
  | n+1 => (truncateFamily N p G (n+1)).add (truncateFamily N q H n)

/-- Evaluate family as an element of `GradientWitness P T κ m (fieldSum N r p)`. -/
def evaluateFamily (N : ℕ) (r : ℝ) (p : ℕ → ScalarField)
    (G : ∀ i, GradientWitness P T κ m (p i)) :
    GradientWitness P T κ m (fieldSum N r p) :=
  (finsetSum (range (N+1)) (fun i => r^i • p i) (fun i => (G i).smul (r^i))).congr (by
    funext z
    simp only [fieldSum,evaluate,Finset.sum_apply,Pi.smul_apply])

/-- Compact, bundling `smooth`, `field`, `gradient_mem`. -/
def compact (p : ScalarField) (q : C(Icc (0 : ℝ) T, CylinderL2 P ℝ))
    (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
    (he : ∀ (t : Icc (0 : ℝ) T) x θ,
      p (t,(x,θ)) = scalarPointField P q hq t (x,(θ : AddCircle P)))
    (S : Set Space) (hS : IsCompact S)
    (hz : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ, p (t,(x,θ)) = 0) :
    GradientWitness P T κ m p where
  smooth := scalarRaw_smooth p q hq he
  field := liftedGradientField P p q hq he κ m
  gradient_mem := liftedGradientField_mem P p q hq he κ m S hS hz

end GradientWitness
end EulerPacketPressure

namespace EulerPacketCoordinates

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketPressure
  EulerPacketCylinderField EulerPacketProfileRecursion EulerLiftedGradientSpace
  EulerPacketPointJets

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)
  (k : ℝ) (hk : k ≠ 0) {p : ScalarField}

/-- Pressure field as an element of `Field P D.T (coordinatePressure D k p)`. -/
def pressureField (G : GradientWitness P D.T k⁻¹ D.m₀ p) :
    Field P D.T (coordinatePressure D k p) :=
  (G.field.smul (k^2)).congr (fun t x θ => by
    change k • pressureGradient p (t,(x,θ)) +
      k^2 • ((pressureJet p (t,(x,θ))).2 angleDirection • D.m₀) =
      k^2 • (k⁻¹ • pressureGradient p (t,(x,θ)) +
        (pressureJet p (t,(x,θ))).2 angleDirection • D.m₀)
    simp only [smul_add,smul_smul]
    rw [show k^2*k⁻¹ = k by field_simp [hk]])

theorem pressureField_mem (G : GradientWitness P D.T k⁻¹ D.m₀ p)
    (t : Icc (0 : ℝ) D.T) :
    (pressureField D k hk G).path t ∈ gradientSpace P k⁻¹ D.m₀ :=
  (gradientSpace P k⁻¹ D.m₀).smul_mem (k^2) (G.gradient_mem t)

end EulerPacketCoordinates

end
end

end

section

/-! The actual constant-angle embedding preserves the closed gradient
spaces.  Compact ordinary scalar tests give compact cylinder scalar tests,
and the bounded embedding carries their closures into one another. -/

@[expose] public section

noncomputable section

namespace EulerCylinderSpatialEmbedding

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

/-- Scalar lift, defined pointwise by `φ z.1`. -/
def scalarLift (φ : Space → ℝ) : LiftDomain P → ℝ := fun z => φ z.1

theorem scalarLift_compact (φ : Space → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (scalarLift P φ) := by
  apply HasCompactSupport.intro (hφ.prod (isCompact_univ : IsCompact (univ : Set (AddCircle P))))
  intro z hz
  change φ z.1 = 0
  exact image_eq_zero_of_notMem_tsupport (by simpa only [mem_prod,mem_univ,and_true] using hz)

omit [Fact (0 < P)] in
theorem scalarLift_smooth (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : LiftDomain P) :
    ContDiff ℝ ∞ (localLift P (scalarLift P φ) z) :=
  hφ.comp (contDiff_const.add contDiff_fst)

theorem gradient_component (φ : Space → ℝ) (x : Space) (i : Fin 3) :
    gradient φ x i = fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  have h := toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i 1) (y := fderiv ℝ φ x)
  simpa only [gradient,EuclideanSpace.inner_single_right,conj_trivial,one_mul] using h

omit [Fact (0 < P)] in
theorem scalarLift_gradient (κ : ℝ) (m : Space) (φ : Space → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (z : LiftDomain P) :
    liftedGradient P κ m (scalarLift P φ) z = κ • gradient φ z.1 := by
  have hh : HasFDerivAt (fun y : LiftTangent => z.1+y.1) (fst ℝ Space ℝ) 0 :=
    hasFDerivAt_fst.const_add z.1
  have hf : HasFDerivAt φ (fderiv ℝ φ z.1) (z.1+(0 : LiftTangent).1) := by
    simpa only [Prod.fst_zero,add_zero] using ((hφ.differentiable (by simp)) z.1).hasFDerivAt
  have h := hf.comp (0 : LiftTangent) hh
  have hd : fderiv ℝ (localLift P (scalarLift P φ) z) 0 =
      (fderiv ℝ φ z.1).comp (fst ℝ Space ℝ) := by
    convert! h.fderiv using 1
  ext i
  change κ * (fderiv ℝ (localLift P (scalarLift P φ) z) 0) (EuclideanSpace.single i 1,0) +
    m i * (fderiv ℝ (localLift P (scalarLift P φ) z) 0) (0,1) = κ * gradient φ z.1 i
  rw [hd,gradient_component]
  change κ * fderiv ℝ φ z.1 (EuclideanSpace.single i 1) + m i * fderiv ℝ φ z.1 0 = _
  rw [map_zero,mul_zero,add_zero]

theorem smul_embedding_gradient_mem (κ : ℝ) (m : Space)
    (g : EulerMeanSolenoidal.L2) (hg : g ∈ EulerMeanSolenoidal.gradientSpace) :
    κ • embedding P g ∈ gradientSpace P κ m := by
  let L : EulerMeanSolenoidal.L2 →L[ℝ] LiftL2 P := κ • embedding P
  let K := (gradientSpace P κ m).comap L.toLinearMap
  have hgen : Submodule.span ℝ EulerMeanSolenoidal.gradientGenerators ≤ K := by
    apply Submodule.span_le.mpr
    rintro u ⟨φ,hφc,hφs,hu⟩
    change κ • embedding P u ∈ gradientSpace P κ m
    apply testGradient_mem P κ m
    refine ⟨scalarLift P φ,⟨scalarLift_compact P φ hφc,scalarLift_smooth P φ hφs⟩,?_⟩
    filter_upwards [Lp.coeFn_smul κ (embedding P u),lift_ae P u,
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space))
        (ν := (volume : Measure (AddCircle P)))).ae hu] with z hs hl hz
    change (κ • embedding P u) z = _
    rw [hs]
    change κ • embedding P u z = _
    rw [show embedding P u z = u z.1 from hl,hz,scalarLift_gradient P κ m φ hφs]
  have hclosed : IsClosed (K : Set EulerMeanSolenoidal.L2) :=
    (gradientSpace_closed P κ m).preimage L.continuous
  exact ((Submodule.span ℝ EulerMeanSolenoidal.gradientGenerators).topologicalClosure_minimal
    hgen hclosed) hg

theorem embedding_gradient_mem (κ : ℝ) (hκ : κ ≠ 0) (m : Space)
    (g : EulerMeanSolenoidal.L2) (hg : g ∈ EulerMeanSolenoidal.gradientSpace) :
    embedding P g ∈ gradientSpace P κ m := by
  have h := (gradientSpace P κ m).smul_mem κ⁻¹ (smul_embedding_gradient_mem P κ m g hg)
  simpa only [smul_smul,inv_mul_cancel₀ hκ,one_smul] using h

end EulerCylinderSpatialEmbedding

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanCoefficients EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketCylinderField EulerPacketPressure EulerCylinderSpatialEmbedding
open scoped ContDiff

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem path_ae_raw_zeroAngle (t : Icc (0 : ℝ) D.T) :
    (G.path t : Space → Space) =ᵐ[volume] fun x => raw (t,(x,0)) := by
  rw [G.path_eq]
  filter_upwards [(G.slices t).toLp_ae] with x hx
  exact hx.trans (G.raw_eq t x 0).symm

/-- The classical gradient constructed from the radial potential is the same
ordinary L² element as the projected pressure residual. -/
theorem scalarGradient_path_eq (t : Icc (0 : ℝ) D.T) :
    G.scalarGradientForcing.path t = (D.opF t).adjoint (G.pressureForcePath t) := by
  change G.scalarGradientForcing.path t =
    (EulerMeanCoefficients.multiplier (D.F.field t)).adjoint (G.pressureForcePath t)
  rw [← multiplier_adjointField]
  apply Lp.ext
  filter_upwards [G.scalarGradientForcing.path_ae_raw_zeroAngle t,
    G.pressureForceForcing.path_ae_raw_zeroAngle t,
    multiplier_ae (adjointField (D.F.field t)) (G.pressureForcePath t)] with x hg hp hm
  change G.scalarGradientForcing.path t x =
    (EulerMeanCoefficients.multiplier (adjointField (D.F.field t)) (G.pressureForcePath t)) x
  rw [hg,hm,adjointField_apply]
  change G.scalarGradient (t,(x,0)) = (D.F.field t x).adjoint (G.pressureForceForcing.path t x)
  rw [hp,G.scalarGradient_eq]

theorem scalarGradient_path_mem (t : Icc (0 : ℝ) D.T) :
    G.scalarGradientForcing.path t ∈ EulerMeanSolenoidal.gradientSpace := by
  rw [G.scalarGradient_path_eq]
  exact G.solution.pressurePath_gradient D.frameLower D.frameLower_pos D.frame_lower G.path t

theorem pressureGradient_eq_scalarGradient (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    pressureGradient G.scalar (t,(x,θ)) = G.scalarGradient (t,(x,θ)) := by
  change (toDual ℝ Space).symm ((pressureJet G.scalar (t,(x,θ))).2.comp spatialInjection) = _
  rw [pressureJet_spatial_derivative G.scalar t x θ
    ((G.scalar_spatial_smooth t).differentiable (by simp) (x,θ))]
  rfl

/-- This witness uses the actual projected mean equation to prove membership,
without any compact-support or integrability premise on the scalar potential. -/
def pressureGradientWitness (P κ : ℝ) [Fact (0 < P)] (m : Space) :
    GradientWitness P D.T κ m G.scalar where
  smooth t := G.scalar_spatial_smooth t
  field := ((G.scalarGradientForcing.toCylinderField P).smul κ).congr (fun t x θ => by
    rw [rawGradient,G.scalar_angle_jet,zero_smul,add_zero,
      G.pressureGradient_eq_scalarGradient]
    rfl)
  gradient_mem t :=
    smul_embedding_gradient_mem P κ m (G.scalarGradientForcing.path t) (G.scalarGradient_path_mem t)

end EulerMeanPacketProvider.Forcing

end
end

end

section

/-! The actual coordinate residual identity in every finite Sobolev space.
This discharges the approximation equation, using the source coefficients
and the genuine packet Fields rather than an assumed residual equation. -/

@[expose] public section

noncomputable section

namespace EulerPacketCoordinates

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerPacketPointJets EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketCorrectionCoefficients EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerCylinderSmoothOrbit EulerLpCylinderRectangular EulerSobolevCoefficientPressure
  EulerSobolevTransport EulerCorrectionOperators EulerCorrectionResidualCancellation
  EulerVolterraConvolution EulerMetricTransport EulerLiftedWeakDerivative EulerLpCylinderTranslation
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instPacketCoordinateSobolev1 : NormedAddCommGroup Space := inferInstance
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instPacketCoordinateSobolev2 : NormedSpace ℝ Space := inferInstance

variable {P : ℝ} [Fact (0 < P)]

private theorem coefficient_value_ae {T : ℝ} {a : Domain → Space →L[ℝ] Space}
    (A : MatrixCoefficient T a) (q : ℕ) (t : Icc (0 : ℝ) T)
    (u : SobolevSpace P q) (f : LiftDomain P → Space)
    (hu : (value P u : LiftDomain P → Space) =ᵐ[liftMeasure P] f) :
    (value P (coefficientSobolevOperator P ((A.toCoefficientTower P).jet q t) u) :
      LiftDomain P → Space) =ᵐ[liftMeasure P] fun x => A.path t x.1 (f x) := by
  rw [MatrixCoefficient.toCoefficientTower_sobolev_value P A q t u]
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (A.path t))
    (value P u),hu] with x hA hf
  exact hA.trans (congrArg (A.path t x.1) hf)

private theorem transport_value_ae {T : ℝ} {z : VectorField}
    (Z : Field P T z) (κ : ℝ) (m : Space) (hκ : |κ| ≤ 1) (hm : ‖m‖ ≤ 1)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    (value P (transportBilinear P hq (velocityComponents κ m)
      (velocityComponents_norm κ m hκ hm)
      (Z.toFieldTower.realization (q+1) t) (Z.toFieldTower.realization (q+1) t)) :
        LiftDomain P → Space) =ᵐ[liftMeasure P] fun x =>
      fieldFDeriv P (pointField P Z.path Z.orbit t) x
        (transportDirection κ m (pointField P Z.path Z.orbit t x)) := by
  have h := transportBilinear_ae P hq (velocityComponents κ m)
    (velocityComponents_norm κ m hκ hm) _ _ _ _
    (Z.toFieldTower_value_ae (q+1) t) (Z.toFieldTower_value_ae (q+1) t)
    (pointField_smooth P Z.path Z.orbit t)
  filter_upwards [h] with x hx
  rw [hx,← velocityComponents_direction κ m]
  change (∑ i : Fin 4, velocityComponents κ m i (pointField P Z.path Z.orbit t x) •
      fieldFDeriv P (pointField P Z.path Z.orbit t) x (standardDirection i)) = _
  rw [map_sum]
  simp only [map_smul]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U)

/-- Normalized residual, given by `k • rawInverse D z (slicedMomentumResidual (Icc (0 : ℝ) D.T)
k⁻¹ (rawInverse D z) (D.strain z) (D.normalField z) W p z)`. -/
def normalizedResidual (k : ℝ) (W : VectorField) (p : ScalarField) (z : Domain) : Space :=
  k • rawInverse D z (slicedMomentumResidual (Icc (0 : ℝ) D.T) k⁻¹
    (rawInverse D z) (D.strain z) (D.normalField z) W p z)

private theorem nonlinearity_value_ae (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (R : Field P D.T r)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) D.T) :
    (value P (nonlinearity P ((correctionDataOfFields D P κ hκ Z R).atOrder P q) hq t
      (Z.toFieldTower.realization (q+1) t)) : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => (linearCoefficient D).path t x.1 (pointField P Z.path Z.orbit t x) +
        fieldFDeriv P (pointField P Z.path Z.orbit t) x
          (transportDirection κ D.m₀ (pointField P Z.path Z.orbit t x)) +
        ∑ i : Fin 3, (pointField P Z.path Z.orbit t x) i •
          (quadraticCoefficient D κ i).path t x.1 (pointField P Z.path Z.orbit t x) := by
  let u := Z.toFieldTower.realization (q+1) t
  let a := coefficientSobolevOperator P ((linearTower D P).jet q t) (truncateOperator P q u)
  let b := transportBilinear P hq (velocityComponents κ D.m₀)
    (velocityComponents_norm κ D.m₀ hκ D.m₀_unit.le) u u
  let c := algebraicBilinear P hq
    (fun i => coefficientSobolevOperator P ((quadraticTower D P κ i).jet q t)) u u
  have ha := coefficient_value_ae (linearCoefficient D) q t (truncateOperator P q u)
    (pointField P Z.path Z.orbit t) (by
      simpa only [value_truncateOperator] using Z.toFieldTower_value_ae (q+1) t)
  have hb := transport_value_ae Z κ D.m₀ hκ D.m₀_unit.le q hq t
  have hc := algebraicBilinear_ae P hq (fun i => (quadraticTower D P κ i).coefficient t)
    (fun i => (quadraticTower D P κ i).jet q t) u u _ _
    (Z.toFieldTower_value_ae (q+1) t) (Z.toFieldTower_value_ae (q+1) t)
  change ((valueOperator P q) (a+(b+c)) : LiftDomain P → Space) =ᵐ[liftMeasure P] _
  rw [map_add,map_add]
  filter_upwards [Lp.coeFn_add (value P a) (value P b+value P c),
    Lp.coeFn_add (value P b) (value P c),ha,hb,hc] with x hx hy ha hb hc
  change (value P a + (value P b + value P c)) x = _
  simp only [Pi.add_apply] at hx hy
  change (value P a) x = _ at ha
  change (value P b) x = _ at hb
  change (value P c) x = _ at hc
  rw [hx,hy,ha,hb,hc]
  simp only [add_assoc,quadraticTower,MatrixCoefficient.toCoefficientTower_coefficient]

section Equation

variable (k : ℝ) (hk : k ≠ 0) (hκ : |k⁻¹| ≤ 1)
  {W Wt : VectorField} (G : Field P D.T W) (Gt : Field P D.T Wt)
  (hW : TimeDerivative D.T_pos.le G Gt) (p : ScalarField)
  (R : Field P D.T (normalizedResidual D k W p))
  (Pa : Field P D.T (coordinatePressure D k p))

/-- The data used for cancellation has the literal normalized packet field
and residual. Its coefficients are the original deformation coefficients. -/
def coordinateData : EulerAllOrderCorrectionData.Data P D.T :=
  correctionDataOfFields D P k⁻¹ hκ (coordinateField D G k) R

include hk hW in
theorem sobolev_residual_identity (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) D.T) :
    R.toFieldTower.realization q t =
      (coordinateTimeField D G Gt k).toFieldTower.realization q t +
        nonlinearity P ((coordinateData D k hκ G p R).atOrder P q) hq t
          ((coordinateField D G k).toFieldTower.realization (q+1) t) +
        coefficientSobolevOperator P ((metricTower D P).jet q t)
          (Pa.toFieldTower.realization q t) := by
  let Z := coordinateField D G k
  let Zt := coordinateTimeField D G Gt k
  let A := coordinateData D k hκ G p R
  let N := nonlinearity P (A.atOrder P q) hq t (Z.toFieldTower.realization (q+1) t)
  let Q := coefficientSobolevOperator P ((metricTower D P).jet q t)
    (Pa.toFieldTower.realization q t)
  have hn := nonlinearity_value_ae D k⁻¹ hκ Z R q hq t
  have hp := coefficient_value_ae (metricCoefficient D) q t
    (Pa.toFieldTower.realization q t) (pointField P Pa.path Pa.orbit t)
    (Pa.toFieldTower_value_ae q t)
  apply value_injective P
  change value P (R.toFieldTower.realization q t) =
    (valueOperator P q) (Zt.toFieldTower.realization q t+N+Q)
  rw [map_add,map_add]
  apply Lp.ext
  filter_upwards [R.toFieldTower_value_ae q t,Zt.toFieldTower_value_ae q t,hn,hp,
    Lp.coeFn_add (value P (Zt.toFieldTower.realization q t)) (value P N),
    Lp.coeFn_add (value P (Zt.toFieldTower.realization q t)+value P N) (value P Q)]
    with x hr ht hn hp hs hs'
  change (value P (R.toFieldTower.realization q t)) x =
    (value P (Zt.toFieldTower.realization q t)+value P N+value P Q) x
  simp only [Pi.add_apply] at hs hs'
  change (value P N) x = _ at hn
  change (value P Q) x = _ at hp
  rw [hr,hs',hs,ht,hn,hp]
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective x.2
  have he := normalized_residual D G Gt k hk hW p t x.1 θ
  change normalizedResidual D k W p (t,(x.1,θ)) = _ at he
  rw [R.raw_eq t x.1 θ,Zt.raw_eq t x.1 θ] at he
  simp only [transport,algebraic] at he
  rw [Z.raw_fderiv t x.1 θ,(linearCoefficient D).raw_eq t x.1 θ,
    (metricCoefficient D).raw_eq t x.1 θ,Pa.raw_eq t x.1 θ] at he
  simp only [Z.raw_eq t x.1 θ] at he
  have hquad (i : Fin 3) : rawQuadratic D k⁻¹ i (t,(x.1,θ)) =
      (quadraticCoefficient D k⁻¹ i).path t x.1 :=
    (quadraticCoefficient D k⁻¹ i).raw_eq t x.1 θ
  simp only [hquad,hθ] at he
  simpa only [transportDirection,add_assoc] using he

include hk hW in
/-- The approximation's actual all-order derivative is its literal
residual minus the full nonlinearity and its own actual pressure. -/
theorem approximation_hasDerivWithinAt (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt
      (extendPath D.T D.T_pos.le ((coordinateData D k hκ G p R).approximation.realization q))
      ((coordinateData D k hκ G p R).residual.realization q t -
        nonlinearity P ((coordinateData D k hκ G p R).atOrder P q) hq t
          ((coordinateData D k hκ G p R).approximation.realization (q+1) t) -
        coefficientSobolevOperator P ((coordinateData D k hκ G p R).metric.jet q t)
          (Pa.toFieldTower.realization q t)) (Icc (0 : ℝ) D.T) t := by
  have hd := (coordinateField D G k).toFieldTower_hasDerivWithinAt
    (coordinateTimeField D G Gt k) D.T_pos.le (coordinateField_time D G Gt k hW) q t
  apply hd.congr_deriv
  change (coordinateTimeField D G Gt k).toFieldTower.realization q t =
    R.toFieldTower.realization q t -
      nonlinearity P ((coordinateData D k hκ G p R).atOrder P q) hq t
        ((coordinateField D G k).toFieldTower.realization (q+1) t) -
      coefficientSobolevOperator P ((metricTower D P).jet q t) (Pa.toFieldTower.realization q t)
  rw [sobolev_residual_identity D k hk hκ G Gt hW p R Pa q hq t]
  abel

include hk hW in
theorem approximation_hasDerivAt (q : ℕ) (hq : 6 ≤ q) (t : ℝ) (ht : t ∈ Ioo 0 D.T) :
    HasDerivAt
      (extendPath D.T D.T_pos.le ((coordinateData D k hκ G p R).approximation.realization q))
      ((coordinateData D k hκ G p R).residual.realization q ⟨t,ht.1.le,ht.2.le⟩ -
        nonlinearity P ((coordinateData D k hκ G p R).atOrder P q) hq ⟨t,ht.1.le,ht.2.le⟩
          ((coordinateData D k hκ G p R).approximation.realization (q+1) ⟨t,ht.1.le,ht.2.le⟩) -
        coefficientSobolevOperator P ((coordinateData D k hκ G p R).metric.jet q
            ⟨t,ht.1.le,ht.2.le⟩)
          (Pa.toFieldTower.realization q ⟨t,ht.1.le,ht.2.le⟩)) t :=
  (approximation_hasDerivWithinAt D k hk hκ G Gt hW p R Pa q hq
    ⟨t,ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end Equation

end EulerPacketCoordinates

end
end

end
