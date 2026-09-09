/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScalarPressureGradient
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedAssembly

@[expose] public section

/-! Actual scalar pressures whose lifted gradients are smooth L² fields.
The witnesses below are closed under the literal finite packet assembly. -/

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
    (hp : DifferentiableAt ℝ (fun y => p (z.1,y)) z.2)
    (hq : DifferentiableAt ℝ (fun y => q (z.1,y)) z.2) :
    rawGradient κ m (p+q) z = rawGradient κ m p z + rawGradient κ m q z := by
  ext i
  change rawGradient κ m (p+q) z i = rawGradient κ m p z i + rawGradient κ m q z i
  simp only [rawGradient_component,Pi.add_apply,fderiv_fun_add hp hq,add_apply]
  change κ * (_+_) + (_+_) * m i = (κ*_+_*m i)+(κ*_+_*m i)
  ring

theorem rawGradient_smul (κ : ℝ) (m : Space) (c : ℝ) (p : ScalarField) (z : Domain)
    (hp : DifferentiableAt ℝ (fun y => p (z.1,y)) z.2) :
    rawGradient κ m (c • p) z = c • rawGradient κ m p z := by
  ext i
  change rawGradient κ m (c • p) z i = c * rawGradient κ m p z i
  simp only [rawGradient_component,Pi.smul_apply,fderiv_fun_const_smul hp,smul_apply]
  change κ*(c*_) + (c*_)*m i = c*(κ*_+_*m i)
  ring

theorem rawGradient_sum {ι : Type*} (κ : ℝ) (m : Space) (s : Finset ι)
    (p : ι → ScalarField) (z : Domain)
    (hp : ∀ i ∈ s, DifferentiableAt ℝ (fun y => p i (z.1,y)) z.2) :
    rawGradient κ m (∑ i ∈ s, p i) z = ∑ i ∈ s, rawGradient κ m (p i) z := by
  classical
  ext j
  simp only [WithLp.ofLp_sum,Finset.sum_apply,rawGradient_component,
    fderiv_fun_sum hp,_root_.sum_apply]
  change κ*(∑ i ∈ s, _) + (∑ i ∈ s, _)*m j =
    ∑ i ∈ s, (κ*_+_*m j)
  rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]

structure GradientWitness (P T κ : ℝ) [Fact (0 < P)] (m : Space) (p : ScalarField) where
  smooth : ∀ t : Icc (0 : ℝ) T, ContDiff ℝ ∞ (fun y => p (t,y))
  field : Field P T (rawGradient κ m p)
  gradient_mem : ∀ t : Icc (0 : ℝ) T, field.path t ∈ gradientSpace P κ m

namespace GradientWitness

variable {P T κ : ℝ} [Fact (0 < P)] {m : Space} {p q : ScalarField}

def congr (G : GradientWitness P T κ m p) (h : p = q) : GradientWitness P T κ m q := h ▸ G

def changeTime {T' : ℝ} (G : GradientWitness P T κ m p) (h : T = T') :
    GradientWitness P T' κ m p := h ▸ G

def zero (P T κ : ℝ) [Fact (0 < P)] (m : Space) : GradientWitness P T κ m 0 where
  smooth _ := contDiff_const
  field := (Field.zero P T).congr (fun _ _ _ => congrFun (rawGradient_zero κ m) _)
  gradient_mem _ := (gradientSpace P κ m).zero_mem

def add (G : GradientWitness P T κ m p) (H : GradientWitness P T κ m q) :
    GradientWitness P T κ m (p+q) where
  smooth t := (G.smooth t).add (H.smooth t)
  field := (G.field.add H.field).congr (fun t x θ =>
    rawGradient_add κ m p q (t,(x,θ))
      ((G.smooth t).differentiable (by simp) _) ((H.smooth t).differentiable (by simp) _))
  gradient_mem t := (gradientSpace P κ m).add_mem (G.gradient_mem t) (H.gradient_mem t)

def smul (G : GradientWitness P T κ m p) (c : ℝ) : GradientWitness P T κ m (c • p) where
  smooth t := (G.smooth t).const_smul c
  field := (G.field.smul c).congr (fun t x θ =>
    rawGradient_smul κ m c p (t,(x,θ)) ((G.smooth t).differentiable (by simp) _))
  gradient_mem t := (gradientSpace P κ m).smul_mem c (G.gradient_mem t)

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

def truncateFamily (N : ℕ) (p : ℕ → ScalarField)
    (G : ∀ i, i ≤ N → GradientWitness P T κ m (p i)) (n : ℕ) :
    GradientWitness P T κ m (truncate N p n) := by
  by_cases hn : n ≤ N
  · exact (G n hn).congr (truncate_of_le N n p hn).symm
  · exact (zero P T κ m).congr (truncate_of_gt N n p (by omega)).symm

def assembleFamily (N : ℕ) (p q : ℕ → ScalarField)
    (G : ∀ i, i ≤ N → GradientWitness P T κ m (p i))
    (H : ∀ i, i ≤ N → GradientWitness P T κ m (q i)) :
    (n : ℕ) → GradientWitness P T κ m (assemble N p q n)
  | 0 => (truncateFamily N p G 0).congr (by simp only [assemble,shiftUp,add_zero])
  | n+1 => (truncateFamily N p G (n+1)).add (truncateFamily N q H n)

def evaluateFamily (N : ℕ) (r : ℝ) (p : ℕ → ScalarField)
    (G : ∀ i, GradientWitness P T κ m (p i)) :
    GradientWitness P T κ m (fieldSum N r p) :=
  (finsetSum (range (N+1)) (fun i => r^i • p i) (fun i => (G i).smul (r^i))).congr (by
    funext z
    simp only [fieldSum,evaluate,Finset.sum_apply,Pi.smul_apply])

def compact (p : ScalarField) (q : C(Icc (0 : ℝ) T,CylinderL2 P ℝ))
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
