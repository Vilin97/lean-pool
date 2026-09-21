/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.SchurMetricDerivative
public import LeanPool.PoincareGeometry.SchurConstancy
public import LeanPool.PoincareGeometry.SchurContractionAlgebra
public import LeanPool.PoincareGeometry.SchurLocalFrame
public import LeanPool.PoincareGeometry.RicciDerivative
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchiBridge
import LeanPool.PoincareGeometry.ContractedBianchiSections

/-!
# Schur's constancy theorem for actual Levi-Civita Ricci curvature

The local trace identification is discharged by
`CovariantDerivative.ricciDerivative_eq_trace_schurFrame`. Double-contracted
Bianchi comes from the imported connection-derived library theorem. The final
`exists_const_of_einstein` theorem assumes actual Levi-Civita curvature, the
Einstein equation, smoothness, connectedness, and dimension at least three.
It has no trace bridge or frame hypothesis.

The explicitly named `_of_trace_bridge` lemmas retain the intermediate assembly
boundary for reuse; the final theorem supplies a proved bridge.
-/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff BigOperators

namespace SchurRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [IsManifold I (minSmoothness ℝ 2) M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The local trace differentiation interface, discharged below. The frame consists
of canonical C³ extensions of the standard orthonormal basis at each point.
No parallel frame, contracted Bianchi identity, or constancy is assumed here. -/
def RicciTraceBridge : Prop :=
  ∀ (x : M) (U V X : Π y : M, TM y),
    ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% U) →
    ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% V) →
    ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% X) →
    bilinearDerivative cov cov.ricciCurvature U V x (X x) =
      ∑ k, inner ℝ
        (cov.secondBianchiAux X
          (CovariantDerivative.schurFrame x (stdOrthonormalBasis ℝ (TM x)).toBasis k)
          U V x)
        (CovariantDerivative.schurFrame x
          (stdOrthonormalBasis ℝ (TM x)).toBasis k x)

/-- Internal pointwise Schur assembly. The only unproved geometric identification
is exposed as `htrace`; double-contracted Bianchi is invoked from the library. -/
theorem mfderiv_eq_zero_of_trace_bridge
    (hLevi : cov.IsLeviCivita)
    (hn : 3 ≤ Module.finrank ℝ E)
    (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hRic : ∀ y u v, cov.ricciCurvature y u v = f y * inner ℝ u v)
    (htrace : RicciTraceBridge cov) (x : M) :
    mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
  let b := stdOrthonormalBasis ℝ (TM x)
  let e := CovariantDerivative.schurFrame x b.toBasis
  have he (i) : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (e i)) :=
    CovariantDerivative.schurFrame_contMDiff_three x b.toBasis i
  have hev (i) : e i x = b i :=
    CovariantDerivative.schurFrame_at x b.toBasis i
  have hformula (U V X : Π y : M, TM y)
      (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% U))
      (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% V))
      (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% X)) :
      (∑ k, inner ℝ (cov.secondBianchiAux X (e k) U V x) (e k x)) =
        mvfderiv (I := I) f x (X x) * inner ℝ (U x) (V x) := by
    calc
      _ = bilinearDerivative cov cov.ricciCurvature U V x (X x) :=
        (htrace x U V X hU hV hX).symm
      _ = _ := bilinearDerivative_eq_of_eq_mul_inner cov hLevi.2
        cov.ricciCurvature f hRic U V x (X x) (hf x)
        ((hU.mdifferentiable (by norm_num)).mdifferentiableAt)
        ((hV.mdifferentiable (by norm_num)).mdifferentiableAt)
  have hd : (mvfderiv (I := I) f x).toLinearMap = 0 := by
    apply differential_eq_zero_of_contraction b _
      (by simpa only [Fintype.card_fin, VectorBundle.finrank_eq ℝ E TM x] using hn)
    intro w
    let W := CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w
    have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W) :=
      CovariantDerivative.smoothExtend_contMDiff_three x w
    have hWx : W x = w := CovariantDerivative.smoothExtend_apply x w
    have hc := cov.curvatureCovariantDerivativeInner_doubleContraction_sections
      x hLevi.1 hLevi.2 e W he hW
    simp_rw [hformula _ _ _ (he _) (he _) hW,
      hformula _ _ _ (he _) hW (he _), hev, hWx] at hc
    exact hc
  ext w
  apply (NormedSpace.fromTangentSpace (f x)).injective
  have hw := LinearMap.congr_fun hd w
  change (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) w) = 0 at hw
  simpa only [zero_apply, map_zero] using hw


/-- Internal global Schur assembly on a connected manifold of dimension at least
three, conditional on the explicitly stated local trace bridge. -/
theorem exists_const_of_trace_bridge [ConnectedSpace M]
    (hLevi : cov.IsLeviCivita)
    (hn : 3 ≤ Module.finrank ℝ E)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hRic : ∀ y u v, cov.ricciCurvature y u v = f y * inner ℝ u v)
    (htrace : RicciTraceBridge cov) :
    ∃ c : ℝ, ∀ x, f x = c := by
  apply SchurConstancy.exists_const_of_contMDiff_mfderiv_eq_zero I hf
  exact mfderiv_eq_zero_of_trace_bridge cov hLevi hn f
    (hf.mdifferentiable (by simp)) hRic htrace

/-- The actual Ricci derivative theorem discharges the trace interface using
canonical C³ extensions. No neighborhood orthonormality or parallelism is assumed. -/
theorem ricciTraceBridge_of_metricCompatible
    (hmetric : cov.IsMetricCompatibleTangent) : RicciTraceBridge cov := by
  intro x U V X hU hV hX
  simpa only [CovariantDerivative.schurFrame_at, OrthonormalBasis.coe_toBasis] using
    cov.ricciDerivative_eq_trace_schurFrame hmetric x
      (stdOrthonormalBasis ℝ (TM x)) X U V
      (hX.of_le (by norm_num)) hU hV

/-- Pointwise Schur theorem: the differential of a differentiable Einstein factor
vanishes in dimension at least three for the actual Levi-Civita Ricci tensor. -/
theorem mfderiv_eq_zero_of_einstein
    (hLevi : cov.IsLeviCivita)
    (hn : 3 ≤ Module.finrank ℝ E)
    (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hRic : ∀ y u v, cov.ricciCurvature y u v = f y * inner ℝ u v)
    (x : M) : mfderiv I 𝓘(ℝ, ℝ) f x = 0 :=
  mfderiv_eq_zero_of_trace_bridge cov hLevi hn f hf hRic
    (ricciTraceBridge_of_metricCompatible cov hLevi.2) x

/-- Schur's theorem: a smooth Einstein factor for actual Levi-Civita Ricci
curvature is globally constant on a connected manifold of dimension at least
three. All trace differentiation and contracted Bianchi identities are proved. -/
theorem exists_const_of_einstein [ConnectedSpace M]
    (hLevi : cov.IsLeviCivita)
    (hn : 3 ≤ Module.finrank ℝ E)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hRic : ∀ y u v, cov.ricciCurvature y u v = f y * inner ℝ u v) :
    ∃ c : ℝ, ∀ x, f x = c :=
  exists_const_of_trace_bridge cov hLevi hn f hf hRic
    (ricciTraceBridge_of_metricCompatible cov hLevi.2)

end SchurRigidity
