/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Bounded.Core
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.Sylvester.Gap

/-! # Core -/

open TauCeti.DavisKahan.Sylvester

/-!
# Unbounded `sin Θ` problem data and residual block identity

The paper-shaped data record for the unbounded residual theorem, the adjoint
residual block identity, and the ideal-gauge transport of that block.  None of
these consumes a Sylvester estimate, so every engine that supplies one shares
them.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

section GenericCore

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Paper-shaped data for the unbounded residual theorem.

The three operators are raw partial maps.  Density, graph closedness and
self-adjointness are **not** fields: every theorem that needs them already takes
the self-adjointness hypotheses, and `IsSelfAdjoint.dense_domain` and
`IsSelfAdjoint.isClosed` give the other two.  Keeping them out is what lets a
caller build this record from nothing but the algebra. -/
structure UnboundedSinThetaData where
  A : E →ₗ.[𝕜] E
  A₀ : F →ₗ.[𝕜] F
  Λ₁ : G →ₗ.[𝕜] G
  X : F →L[𝕜] E
  F₁ : G →L[𝕜] E
  residual : F →L[𝕜] E
  X_maps_domain : ∀ x : A₀.domain, X (x : F) ∈ A.domain
  F₁_maps_domain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  residual_eq : ∀ x : A₀.domain,
    A ⟨X (x : F), X_maps_domain x⟩ - X (A₀ x) = residual (x : F)
  intertwines : ∀ y : Λ₁.domain,
    A ⟨F₁ (y : G), F₁_maps_domain y⟩ = F₁ (Λ₁ y)

/-- The residual identity induces the domain-aware complementary Sylvester
equation.  The right-hand side has a minus sign:
`A₀ X*F₁ - X*F₁ Λ₁ = -R*F₁`. -/
theorem unbounded_adjoint_residual_block_identity
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (_hΛ₁ : _root_.IsSelfAdjoint D.Λ₁) :
    TauCeti.LinearPMap.SylvesterEquation D.A₀ D.Λ₁
      (D.X.adjoint ∘L D.F₁)
      (-(D.residual.adjoint ∘L D.F₁)) := by
  have hA_symm : ∀ x y : D.A.domain,
      ⟪D.A x, (y : E)⟫_𝕜 = ⟪(x : E), D.A y⟫_𝕜 := by
    have hformal := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hA] at hformal
    intro x y
    exact hformal x y
  have hA₀P : D.A₀.adjoint = D.A₀ := LinearPMap.isSelfAdjoint_def.mp hA₀
  have hA₀_symm : ∀ x y : D.A₀.domain,
      ⟪D.A₀ x, (y : F)⟫_𝕜 = ⟪(x : F), D.A₀ y⟫_𝕜 := by
    have hformal := LinearPMap.adjoint_isFormalAdjoint hA₀.dense_domain
    rw [hA₀P] at hformal
    intro x y
    exact hformal x y
  have key : ∀ (y : D.Λ₁.domain) (x : D.A₀.domain),
      ⟪D.X.adjoint (D.F₁ (D.Λ₁ y)) -
          D.residual.adjoint (D.F₁ (y : G)), (x : F)⟫_𝕜 =
        ⟪D.X.adjoint (D.F₁ (y : G)), D.A₀ x⟫_𝕜 := by
    intro y x
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁ y)) -
        D.residual.adjoint (D.F₁ (y : G))
    show ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀ x⟫_𝕜
    let Fx : D.A.domain := ⟨D.X (x : F), D.X_maps_domain x⟩
    let Fy : D.A.domain := ⟨D.F₁ (y : G), D.F₁_maps_domain y⟩
    calc
      ⟪w, (x : F)⟫_𝕜 =
          ⟪D.F₁ (D.Λ₁ y), D.X (x : F)⟫_𝕜 -
            ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
        rw [inner_sub_left,
          D.X.adjoint_inner_left (x : F) (D.F₁ (D.Λ₁ y)),
          D.residual.adjoint_inner_left (x : F) (D.F₁ (y : G))]
      _ = ⟪D.A Fy, D.X (x : F)⟫_𝕜 -
            ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
        rw [← D.intertwines y]
      _ = ⟪D.F₁ (y : G), D.A Fx⟫_𝕜 -
            ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
        have hsymm :
            ⟪D.A Fy, D.X (x : F)⟫_𝕜 =
              ⟪D.F₁ (y : G), D.A Fx⟫_𝕜 := by
          simpa only [Fx, Fy] using hA_symm Fy Fx
        rw [hsymm]
      _ = ⟪D.F₁ (y : G), D.X (D.A₀ x)⟫_𝕜 := by
        rw [← D.residual_eq x, inner_sub_right]
        abel
      _ = ⟪z, D.A₀ x⟫_𝕜 := by
        rw [← D.X.adjoint_inner_left (D.A₀ x) (D.F₁ (y : G))]
  refine ⟨?_, ?_⟩
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁ y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀ x⟫_𝕜 := key y
    have hzAdj : z ∈ D.A₀.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hz : z ∈ D.A₀.domain := by
      rw [← hA₀P]
      exact hzAdj
    simpa only [z, ContinuousLinearMap.comp_apply] using hz
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁ y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀ x⟫_𝕜 := key y
    have hzAdj : z ∈ D.A₀.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hzDom : z ∈ D.A₀.domain := by
      simpa only [hA₀P] using hzAdj
    have hA₀z : D.A₀ ⟨z, hzDom⟩ = w := by
      have hinner :
          (fun x : F => ⟪D.A₀ ⟨z, hzDom⟩, x⟫_𝕜) =
            fun x : F => ⟪w, x⟫_𝕜 := by
        apply Continuous.ext_on hA₀.dense_domain
        · exact continuous_const.inner continuous_id
        · exact continuous_const.inner continuous_id
        · intro x hx
          let xDom : D.A₀.domain := ⟨x, hx⟩
          calc
            ⟪D.A₀ ⟨z, hzDom⟩, x⟫_𝕜 =
                ⟪z, D.A₀ xDom⟫_𝕜 := hA₀_symm ⟨z, hzDom⟩ xDom
            _ = ⟪w, x⟫_𝕜 := (hw xDom).symm
      have hzero :
          ⟪D.A₀ ⟨z, hzDom⟩ - w,
            D.A₀ ⟨z, hzDom⟩ - w⟫_𝕜 = 0 := by
        rw [inner_sub_left,
          congrFun hinner (D.A₀ ⟨z, hzDom⟩ - w), sub_self]
      exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
    change D.A₀ ⟨z, hzDom⟩ - D.X.adjoint (D.F₁ (D.Λ₁ y)) =
      -D.residual.adjoint (D.F₁ (y : G))
    rw [hA₀z]
    unfold w
    abel

/-- The projected residual block remains in the same rectangular ideal and its
 gauge is no larger than the original residual gauge. -/
theorem adjointResidualBlock_mem_and_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hF₁ : IsometricEmbedding D.F₁)
    (hR : N.Mem D.residual) :
    N.Mem (-(D.residual.adjoint ∘L D.F₁)) ∧
      N.gaugeReal (-(D.residual.adjoint ∘L D.F₁)) ≤
        N.gaugeReal D.residual := by
  have hAdj : N.Mem D.residual.adjoint := N.adjoint_mem hR
  have hComp : N.Mem (D.residual.adjoint ∘L D.F₁) :=
    N.comp_right_mem D.F₁ hAdj
  refine ⟨N.neg_mem hComp, ?_⟩
  calc
    N.gaugeReal (-(D.residual.adjoint ∘L D.F₁))
        = N.gaugeReal (D.residual.adjoint ∘L D.F₁) := N.gaugeReal_neg hComp
    _ ≤ N.gaugeReal D.residual.adjoint :=
      N.gaugeReal_comp_right_le D.F₁ hAdj (opNorm_le_one_of_isometry hF₁)
    _ = N.gaugeReal D.residual := N.gaugeReal_adjoint hR

end GenericCore

end ExactSinTheta
end DavisKahan
end TauCeti
