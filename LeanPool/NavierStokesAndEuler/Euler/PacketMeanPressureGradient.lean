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
