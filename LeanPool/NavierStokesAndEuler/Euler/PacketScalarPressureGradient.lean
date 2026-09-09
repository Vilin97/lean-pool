/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCoordinateResidual
public import LeanPool.NavierStokesAndEuler.Euler.CylinderGradientEmbedding

@[expose] public section

/-! A genuine compact scalar cylinder path supplies the actual lifted
pressure-gradient Field and belongs to the closed lifted gradient space. -/

noncomputable section

namespace EulerPacketPressure

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerPacketPointJets EulerPacketProfileRecursion EulerPacketCylinderField
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderScalarPrimitive
  EulerCylinderSmoothOrbit EulerCylinderConstantMap EulerCylinderSobolev
  EulerLiftedWeakDerivative EulerMetricTransport
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ}

def rawGradient (κ : ℝ) (m : Space) (p : ScalarField) (z : Domain) : Space :=
  κ • pressureGradient p z + (pressureJet p z).2 angleDirection • m

omit [Fact (0 < P)] in
theorem rawGradient_cover (κ : ℝ) (m : Space) (p : ScalarField)
    (φ : LiftDomain P → ℝ) (t : ℝ)
    (he : ∀ x θ, p (t,(x,θ)) = φ (x,(θ : AddCircle P))) (x : Space) (θ : ℝ) :
    rawGradient κ m p (t,(x,θ)) = liftedGradient P κ m φ (x,(θ : AddCircle P)) := by
  have hd : fderiv ℝ (fun y : LiftTangent => p (t,y)) (x,θ) =
      fieldFDeriv P φ (x,(θ : AddCircle P)) := by
    have hh : (fun y : LiftTangent => p (t,y)) =
        fun y => φ (y.1,(y.2 : AddCircle P)) := funext (fun y => he y.1 y.2)
    rw [hh,coverField_fderiv]
  let A := fieldFDeriv P φ (x,(θ : AddCircle P))
  have hi (i : Fin 3) : ((toDual ℝ Space).symm (A.comp (inl ℝ Space ℝ))) i =
      A (EuclideanSpace.single i 1,0) := by
    have h := toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i 1)
      (y := A.comp (inl ℝ Space ℝ))
    simpa only [EuclideanSpace.inner_single_right,conj_trivial,one_mul,comp_apply,inl_apply] using h
  rw [rawGradient,pressureGradient_eq_spatialDual,pressureJet_angle,hd]
  ext i
  change κ*((toDual ℝ Space).symm (A.comp (inl ℝ Space ℝ))) i + A (0,1)*m i =
    κ*A (EuclideanSpace.single i 1,0)+m i*A (0,1)
  rw [hi]
  ring

variable (p : ScalarField) (q : C(Icc (0 : ℝ) T,CylinderL2 P ℝ))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
  (he : ∀ (t : Icc (0 : ℝ) T) x θ, p (t,(x,θ)) = scalarPointField P q hq t (x,(θ : AddCircle P)))

def angularGradientField (m : Space) :
    Field P T (fun z => (pressureJet p z).2 angleDirection • m) :=
  (((scalarEmbeddingField p q hq he).derivative 0).map
    ((toSpanSingleton ℝ m).comp scalarProject)).congr (fun t x θ => by
      have hd : fderiv ℝ (fun y => scalarEmbed (p (t,y))) (x,θ) =
          scalarEmbed.comp (fderiv ℝ (fun y => p (t,y)) (x,θ)) :=
        (scalarEmbed.hasFDerivAt.comp (x,θ)
          (((scalarRaw_smooth p q hq he t).differentiable (by simp)) (x,θ)).hasFDerivAt).fderiv
      simp only [pressureJet_angle,hd,comp_apply,project_embed,toSpanSingleton_apply,
        standardDirection_zero])

def liftedGradientField (κ : ℝ) (m : Space) : Field P T (rawGradient κ m p) :=
  ((scalarGradientField p q hq he).smul κ).add (angularGradientField P p q hq he m)

include he in
theorem scalarPointField_compact (S : Set Space) (hS : IsCompact S)
    (hz : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ, p (t,(x,θ)) = 0)
    (t : Icc (0 : ℝ) T) : HasCompactSupport (scalarPointField P q hq t) := by
  apply HasCompactSupport.intro (hS.prod (isCompact_univ : IsCompact (univ : Set (AddCircle P))))
  intro z hzs
  have hzS : z.1 ∉ S := by simpa only [mem_prod,mem_univ,and_true] using hzs
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective z.2
  have hh := he t z.1 θ
  rw [hθ] at hh
  exact hh.symm.trans (hz t z.1 hzS θ)

theorem liftedGradientField_mem (κ : ℝ) (m : Space) (S : Set Space) (hS : IsCompact S)
    (hz : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ, p (t,(x,θ)) = 0)
    (t : Icc (0 : ℝ) T) :
    (liftedGradientField P p q hq he κ m).path t ∈ gradientSpace P κ m := by
  apply testGradient_mem P κ m
  refine ⟨scalarPointField P q hq t,⟨scalarPointField_compact P p q hq he S hS hz t,
    scalarPointField_smooth P q hq t⟩,?_⟩
  let G := liftedGradientField P p q hq he κ m
  filter_upwards [pointField_ae P G.path G.orbit t] with z hG
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective z.2
  have hraw := G.raw_eq t z.1 θ
  have hgrad := rawGradient_cover P κ m p (scalarPointField P q hq t) t (he t) z.1 θ
  rw [hθ] at hraw hgrad
  exact hG.trans (hraw.symm.trans hgrad)

end EulerPacketPressure

namespace EulerPacketCoordinates

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketPressure
  EulerPacketCylinderField EulerPacketProfileRecursion EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderScalarPrimitive EulerPacketPointJets
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)
  (k : ℝ) (hk : k ≠ 0) (p : ScalarField)
  (q : C(Icc (0 : ℝ) D.T,CylinderL2 P ℝ))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
  (he : ∀ (t : Icc (0 : ℝ) D.T) x θ, p (t,(x,θ)) = scalarPointField P q hq t (x,(θ : AddCircle P)))

def compactPressureField : Field P D.T (coordinatePressure D k p) :=
  ((liftedGradientField P p q hq he k⁻¹ D.m₀).smul (k^2)).congr (fun t x θ => by
    change k • pressureGradient p (t,(x,θ)) +
      k^2 • ((pressureJet p (t,(x,θ))).2 angleDirection • D.m₀) =
      k^2 • (k⁻¹ • pressureGradient p (t,(x,θ)) +
        (pressureJet p (t,(x,θ))).2 angleDirection • D.m₀)
    simp only [smul_add,smul_smul]
    rw [show k^2*k⁻¹ = k by field_simp [hk]])

theorem compactPressureField_mem (S : Set Space) (hS : IsCompact S)
    (hz : ∀ (t : Icc (0 : ℝ) D.T) x, x ∉ S → ∀ θ, p (t,(x,θ)) = 0)
    (t : Icc (0 : ℝ) D.T) :
    (compactPressureField D k hk p q hq he).path t ∈ gradientSpace P k⁻¹ D.m₀ :=
  (gradientSpace P k⁻¹ D.m₀).smul_mem (k^2)
    (liftedGradientField_mem P p q hq he k⁻¹ D.m₀ S hS hz t)

end EulerPacketCoordinates
