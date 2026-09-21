/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.FilledTruncation
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!

# Direct ordered cutoff Sylvester estimates

This module carries the ordered two-unbounded Sylvester argument through the
direct cutoff and bounded-truncation interfaces, including the two strong-limit
passages and Fan dominance endpoint.
-/

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace Topology
open TauCeti.DavisKahan.ExactSinTheta
open Filter

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]


section ApproximationNumberEndpointAssumptions

variable [HasApproximationNumberStrongCutoff.{u, v, 0} 𝕜]
variable [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]

omit [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜] in
/-- Finite Ky Fan inequalities for all right spectral cutoffs pass to the
original operators.  This is the topological limit step in the two-unbounded
ordered Sylvester argument; the remaining analytic input is the corresponding
inequality for each bounded truncation. -/
theorem kyFanApproximationGauge_le_of_cutoff_le
    {B : F →ₗ.[𝕜] F}
    (hB : IsSelfAdjoint B)
    (PCB : SpectralCutoffInterface B hB)
    {X C : F →L[𝕜] E} {δ : ℝ} (k : ℕ)
    (hcut : ∀ τ : ℝ, 0 ≤ τ →
      δ * kyFanApproximationGauge k
          (X ∘L PCB.cutoff τ) ≤
        kyFanApproximationGauge k
          (C ∘L PCB.cutoff τ)) :
    δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C := by
  have hPproj : ∀ τ : ℝ,
      IsOrthogonalProjectionMap (PCB.cutoff τ) := by
    intro τ
    exact PCB.isOrthogonalProjection τ
  have hPstrong : StronglyTendsto
      (fun τ : ℝ => PCB.cutoff τ) atTop
      (ContinuousLinearMap.id 𝕜 F) := by
    intro x
    simpa using PCB.tendsto_identity x
  have hX := kyFanApproximationGauge_comp_strongProjection_tendsto
    hPproj hPstrong k X
  have hC := kyFanApproximationGauge_comp_strongProjection_tendsto
    hPproj hPstrong k C
  have hcutEventually : ∀ᶠ τ : ℝ in atTop,
      δ * kyFanApproximationGauge k
          (X ∘L PCB.cutoff τ) ≤
        kyFanApproximationGauge k
          (C ∘L PCB.cutoff τ) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact hcut τ hτ
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul hX) hC hcutEventually

omit [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜] in
/-- Finite Ky Fan gauges also converge under strong orthogonal cutoffs on
the target side. -/
theorem kyFanApproximationGauge_left_comp_strongProjection_tendsto_direct
    {ι : Type} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (k : ℕ) (K : F →L[𝕜] E) :
    Tendsto
      (fun i => kyFanApproximationGauge k (P i ∘L K))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  have hright := kyFanApproximationGauge_comp_strongProjection_tendsto
    hPproj hP k K.adjoint
  have hpoint : ∀ i,
      kyFanApproximationGauge k (P i ∘L K) =
        kyFanApproximationGauge k (K.adjoint ∘L P i) :=
    fun i => kyFanApproximationGauge_proj_comp_eq_adjoint_comp (hPproj i) K
  have hlimit : kyFanApproximationGauge k K =
      kyFanApproximationGauge k K.adjoint := by
    symm
    exact kyFanApproximationGauge_adjoint k K
  simpa only [hpoint, hlimit] using hright

omit [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜] in
/-- Left-cutoff finite Ky Fan inequalities pass to the original operators. -/
theorem kyFanApproximationGauge_le_of_leftCutoff_le
    {A : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A)
    (PCA : SpectralCutoffInterface A hA)
    {X C : F →L[𝕜] E} {δ : ℝ} (k : ℕ)
    (hcut : ∀ τ : ℝ, 0 ≤ τ →
      δ * kyFanApproximationGauge k
          (PCA.cutoff τ ∘L X) ≤
        kyFanApproximationGauge k
          (PCA.cutoff τ ∘L C)) :
    δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C := by
  have hPproj : ∀ τ : ℝ,
      IsOrthogonalProjectionMap (PCA.cutoff τ) := by
    intro τ
    exact PCA.isOrthogonalProjection τ
  have hPstrong : StronglyTendsto
      (fun τ : ℝ => PCA.cutoff τ) atTop
      (ContinuousLinearMap.id 𝕜 E) := by
    intro x
    simpa using PCA.tendsto_identity x
  have hX := kyFanApproximationGauge_left_comp_strongProjection_tendsto_direct
    hPproj hPstrong k X
  have hC := kyFanApproximationGauge_left_comp_strongProjection_tendsto_direct
    hPproj hPstrong k C
  have hcutEventually : ∀ᶠ τ : ℝ in atTop,
      δ * kyFanApproximationGauge k
          (PCA.cutoff τ ∘L X) ≤
        kyFanApproximationGauge k
          (PCA.cutoff τ ∘L C) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact hcut τ hτ
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul hX) hC hcutEventually

omit [HasApproximationNumberStrongCutoff 𝕜] [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜] in
/-- Double spectral cutoff turns a domain-aware equation into an ordinary
bounded equation between the filled truncations, parametrically in the cutoff
and truncation interfaces.

`doubleSpectralCutoff_filled_sylvester_equation` is the concrete instantiation at
`spectralCutoff` and `boundedSpectralTruncation`. -/
theorem doubleCutoff_filled_sylvester_equation
    {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (PCA : SpectralCutoffInterface A hA)
    (TCA : BoundedTruncationInterface A hA PCA)
    (PCB : SpectralCutoffInterface B hB)
    (TCB : BoundedTruncationInterface B hB PCB)
    {X C : F →L[𝕜] E}
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (a b τA τB : ℝ) :
    filledTruncation A hA PCA TCA a τA ∘L
        (PCA.cutoff τA ∘L X ∘L PCB.cutoff τB) -
      (PCA.cutoff τA ∘L X ∘L PCB.cutoff τB) ∘L
        filledTruncation B hB PCB TCB b τB =
      PCA.cutoff τA ∘L C ∘L PCB.cutoff τB := by
  let PA : E →L[𝕜] E := PCA.cutoff τA
  let PB : F →L[𝕜] F := PCB.cutoff τB
  let TA : E →L[𝕜] E := TCA.truncation τA
  let TB : F →L[𝕜] F := TCB.truncation τB
  have hPAidem := (PCA.isOrthogonalProjection τA).1
  have hPBidem := (PCB.isOrthogonalProjection τB).1
  have hTAcomm := TCA.commutes_cutoff τA
  have hTBcomm := TCB.commutes_cutoff τB
  ext x
  have hPBdom : PB x ∈ B.domain :=
    PCB.range_le_domain τB ⟨x, rfl⟩
  have hXdom : X (PB x) ∈ A.domain :=
    hEq.mapsTo_domain ⟨PB x, hPBdom⟩
  obtain ⟨hPAxdom, hAcomm⟩ :=
    PCA.commutes_on_domain τA ⟨X (PB x), hXdom⟩
  obtain ⟨_hPAcutdom, hTAcut⟩ :=
    TCA.eq_on_cutoff τA (X (PB x))
  obtain ⟨_hPBcutdom, hTBcut⟩ :=
    TCB.eq_on_cutoff τB x
  have hPAPAx : PA (PA (X (PB x))) = PA (X (PB x)) := by
    have h := congrArg (fun S : E →L[𝕜] E => S (X (PB x))) hPAidem
    simpa only [PA, ContinuousLinearMap.comp_apply] using h
  have hPBPBx : PB (PB x) = PB x := by
    have h := congrArg (fun S : F →L[𝕜] F => S x) hPBidem
    simpa only [PB, ContinuousLinearMap.comp_apply] using h
  have hTAPA : TA (PA (X (PB x))) = TA (X (PB x)) := by
    have h := congrArg (fun S : E →L[𝕜] E => S (X (PB x))) hTAcomm.1
    simpa only [TA, PA, ContinuousLinearMap.comp_apply] using h
  have hPBTB : PB (TB x) = TB x := by
    have h := congrArg (fun S : F →L[𝕜] F => S x) hTBcomm.2
    simpa only [PB, TB, ContinuousLinearMap.comp_apply] using h
  have hPBFilled :
      PB (filledTruncation B hB PCB TCB b τB x) = TB x := by
    change PB (TB x + ((b : ℝ) : 𝕜) • (x - PB x)) = TB x
    simp only [map_add, map_smul, hPBTB, map_sub, hPBPBx, sub_self, smul_zero,
      add_zero]
  have hAFilled :
      filledTruncation A hA PCA TCA a τA (PA (X (PB x))) =
        PA (A ⟨X (PB x), hXdom⟩) := by
    change TA (PA (X (PB x))) +
        ((a : ℝ) : 𝕜) • (PA (X (PB x)) - PA (PA (X (PB x)))) =
      PA (A ⟨X (PB x), hXdom⟩)
    rw [hTAPA, hPAPAx, sub_self, smul_zero, add_zero]
    rw [hTAcut]
    exact hAcomm
  have heq := SylvesterEquation.equation_of_mem hEq ⟨PB x, hPBdom⟩ hXdom
  have heqPA := congrArg PA heq
  change
    filledTruncation A hA PCA TCA a τA (PA (X (PB x))) -
      PA (X (PB (filledTruncation B hB PCB TCB b τB x))) =
        PA (C (PB x))
  rw [hAFilled, hPBFilled]
  rw [show TB x = B ⟨PB x, hPBdom⟩ by
    simpa only [TB, PB] using hTBcut]
  simp only [map_sub] at heqPA
  exact heqPA

omit [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜] in
/-- Pointwise cutoff estimates for every finite Ky Fan gauge imply the full
family of Ky Fan inequalities used by Fan dominance. -/
theorem all_kyFanApproximationGauge_le_of_cutoff_le
    {B : F →ₗ.[𝕜] F}
    (hB : IsSelfAdjoint B)
    (PCB : SpectralCutoffInterface B hB)
    {X C : F →L[𝕜] E} {δ : ℝ}
    (hcut : ∀ τ : ℝ, 0 ≤ τ → ∀ k : ℕ,
      δ * kyFanApproximationGauge k
          (X ∘L PCB.cutoff τ) ≤
        kyFanApproximationGauge k
          (C ∘L PCB.cutoff τ)) :
    ∀ k, δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C := by
  intro k
  exact kyFanApproximationGauge_le_of_cutoff_le hB PCB k
    (fun τ hτ => hcut τ hτ k)

omit [CompleteSpace E] [CompleteSpace F]
  [HasApproximationNumberStrongCutoff 𝕜]
  [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜] in
/-- **Shifting both blocks of a Sylvester equation by the same scalar leaves it
unchanged.**

`(A - m) X - X (B - m) = A X - X B`, because the two `m X` terms cancel.  Both
semibounded-direct bounds below derived this inline. -/
private theorem sylvester_shift_invariant
    (AF : E →L[𝕜] E) (BF : F →L[𝕜] F) (Xc : F →L[𝕜] E) (Cc : F →L[𝕜] E)
    (m : ℝ) (hEqCut : AF ∘L Xc - Xc ∘L BF = Cc) :
    (AF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) ∘L Xc -
        Xc ∘L (BF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F) = Cc := by
  ext x
  have hraw := congrArg (fun T : F →L[𝕜] E => T x) hEqCut
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul] at hraw ⊢
  calc
    AF (Xc x) - ((m : ℝ) : 𝕜) • Xc x -
        (Xc (BF x) - ((m : ℝ) : 𝕜) • Xc x) =
      AF (Xc x) - Xc (BF x) := by module
    _ = Cc x := hraw

/-- Ky Fan estimate obtained from bounded spectral truncations. -/
theorem kyFan_unbounded_sylvester_le_of_semibounded_direct
    {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (PCA : SpectralCutoffInterface A hA)
    (TCA : BoundedTruncationInterface A hA PCA)
    (PCB : SpectralCutoffInterface B hB)
    (TCB : BoundedTruncationInterface B hB PCB)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBc : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C) :
    ∀ k, δ * kyFanApproximationGauge k X
      ≤ kyFanApproximationGauge k C := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  apply kyFanApproximationGauge_le_of_leftCutoff_le hA PCA k
  intro τA hτA
  apply kyFanApproximationGauge_le_of_cutoff_le hB PCB k
  intro τB hτB
  let PA : E →L[𝕜] E := PCA.cutoff τA
  let PB : F →L[𝕜] F := PCB.cutoff τB
  let AF : E →L[𝕜] E := filledTruncation A hA PCA TCA (c + δ) τA
  let BF : F →L[𝕜] F := filledTruncation B hB PCB TCB c τB
  let Xc : F →L[𝕜] E := PA ∘L X ∘L PB
  let Cc : F →L[𝕜] E := PA ∘L C ∘L PB
  have hAFsym : AF.IsSymmetric :=
    filledTruncation_isSymmetric A hA PCA TCA (c + δ) τA
  have hBFsym : BF.IsSymmetric :=
    filledTruncation_isSymmetric B hB PCB TCB c τB
  have hAFlower : ∀ x, (c + δ) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪AF x, x⟫_𝕜 :=
    filledTruncation_lowerBound A hA PCA TCA hτA hAc
  have hBFupper : ∀ x, RCLike.re ⟪BF x, x⟫_𝕜 ≤
      c * ‖x‖ ^ 2 :=
    filledTruncation_upperBound B hB PCB TCB hτB hBc
  have hEqCut : AF ∘L Xc - Xc ∘L BF = Cc := by
    simpa only [AF, BF, Xc, Cc] using
      doubleCutoff_filled_sylvester_equation hA hB PCA TCA PCB TCB hEq
        (c + δ) c τA τB
  let B0 : F →L[𝕜] F :=
    BF - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F
  let ρ : ℝ := ‖B0‖
  let m : ℝ := c - ρ
  let A1 : E →L[𝕜] E :=
    AF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E
  let B1 : F →L[𝕜] F :=
    BF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F
  have hρ : 0 ≤ ρ := norm_nonneg B0
  have hB0sym : B0.IsSymmetric := by
    exact hBFsym.sub (LinearMap.IsSymmetric.smul
      (RCLike.conj_ofReal c) LinearMap.IsSymmetric.id)
  have hB0nonpos : ∀ x, RCLike.re ⟪B0 x, x⟫_𝕜 ≤ 0 := by
    intro x
    have h := hBFupper x
    simp only [B0, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, map_sub, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    linarith
  have hB1eq : B1 = B0 + ((ρ : ℝ) : 𝕜) •
      ContinuousLinearMap.id 𝕜 F := by
    ext x
    simp only [B1, B0, m, sub_apply, add_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    module
  have hB1norm : ‖B1‖ ≤ ρ := by
    rw [hB1eq]
    exact norm_add_opNorm_id_le_of_nonpos_direct hB0sym hB0nonpos
  have hA1coer : ∀ x, (ρ + δ) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪A1 x, x⟫_𝕜 := by
    intro x
    have h := hAFlower x
    have hshift : RCLike.re ⟪A1 x, x⟫_𝕜 =
        RCLike.re ⟪AF x, x⟫_𝕜 - m * ‖x‖ ^ 2 := by
      simp only [A1, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    rw [hshift]
    dsimp [m]
    linarith
  have hρδ : 0 < ρ + δ := by linarith
  obtain ⟨hA1inv, hA1invNorm⟩ :=
    boundedInverseData_of_coercive_direct hρδ hA1coer
  have hEqShift : A1 ∘L Xc - Xc ∘L B1 = Cc :=
    sylvester_shift_invariant AF BF Xc Cc m hEqCut
  have hmain := sylvester_mem_and_gauge_le_of_bound_inverse
    (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk).toSymmetricOperatorIdealFamily
    hA1inv B1 hρ hδ hA1invNorm hB1norm hEqShift
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := 𝕜) k hk Cc)
  simp only [FanDominantIdealFamily.toSymmetric_gaugeReal] at hmain
  rw [KyFanDominantIdealFamily.kyFan_gauge (𝕜 := 𝕜) k hk Xc,
    KyFanDominantIdealFamily.kyFan_gauge (𝕜 := 𝕜) k hk Cc] at hmain
  simpa only [Xc, Cc, PA, PB, ContinuousLinearMap.comp_assoc] using hmain.2

/-- The opposite ordered orientation, obtained by adjointing and swapping the
two closed blocks. -/
theorem kyFan_unbounded_sylvester_le_of_semibounded_direct_swapped
    {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (PCA : SpectralCutoffInterface A hA)
    (TCA : BoundedTruncationInterface A hA PCA)
    (PCB : SpectralCutoffInterface B hB)
    (TCB : BoundedTruncationInterface B hB PCB)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedAbove A c)
    (hBc : TauCeti.LinearPMap.SemiboundedBelow B (c + δ))
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C) :
    ∀ k, δ * kyFanApproximationGauge k X
      ≤ kyFanApproximationGauge k C := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  apply kyFanApproximationGauge_le_of_leftCutoff_le hA PCA k
  intro τA hτA
  apply kyFanApproximationGauge_le_of_cutoff_le hB PCB k
  intro τB hτB
  let PA : E →L[𝕜] E := PCA.cutoff τA
  let PB : F →L[𝕜] F := PCB.cutoff τB
  let AF : E →L[𝕜] E := filledTruncation A hA PCA TCA c τA
  let BF : F →L[𝕜] F := filledTruncation B hB PCB TCB (c + δ) τB
  let Xc : F →L[𝕜] E := PA ∘L X ∘L PB
  let Cc : F →L[𝕜] E := PA ∘L C ∘L PB
  have hAFsym : AF.IsSymmetric :=
    filledTruncation_isSymmetric A hA PCA TCA c τA
  have hBFsym : BF.IsSymmetric :=
    filledTruncation_isSymmetric B hB PCB TCB (c + δ) τB
  have hAFupper : ∀ x, RCLike.re ⟪AF x, x⟫_𝕜 ≤
      c * ‖x‖ ^ 2 :=
    filledTruncation_upperBound A hA PCA TCA hτA hAc
  have hBFlower : ∀ x, (c + δ) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪BF x, x⟫_𝕜 :=
    filledTruncation_lowerBound B hB PCB TCB hτB hBc
  have hEqCut : AF ∘L Xc - Xc ∘L BF = Cc := by
    simpa only [AF, BF, Xc, Cc] using
      doubleCutoff_filled_sylvester_equation hA hB PCA TCA PCB TCB hEq
        c (c + δ) τA τB
  let A0 : E →L[𝕜] E :=
    AF - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E
  let ρ : ℝ := ‖A0‖
  let m : ℝ := c - ρ
  let A1 : E →L[𝕜] E :=
    AF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E
  let B1 : F →L[𝕜] F :=
    BF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F
  have hρ : 0 ≤ ρ := norm_nonneg A0
  have hA0sym : A0.IsSymmetric := by
    exact hAFsym.sub (LinearMap.IsSymmetric.smul
      (RCLike.conj_ofReal c) LinearMap.IsSymmetric.id)
  have hA0nonpos : ∀ x, RCLike.re ⟪A0 x, x⟫_𝕜 ≤ 0 := by
    intro x
    have h := hAFupper x
    simp only [A0, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, map_sub, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    linarith
  have hA1eq : A1 = A0 + ((ρ : ℝ) : 𝕜) •
      ContinuousLinearMap.id 𝕜 E := by
    ext x
    simp only [A1, A0, m, sub_apply, add_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    module
  have hA1norm : ‖A1‖ ≤ ρ := by
    rw [hA1eq]
    exact norm_add_opNorm_id_le_of_nonpos_direct hA0sym hA0nonpos
  have hB1coer : ∀ x, (ρ + δ) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪B1 x, x⟫_𝕜 := by
    intro x
    have h := hBFlower x
    have hshift : RCLike.re ⟪B1 x, x⟫_𝕜 =
        RCLike.re ⟪BF x, x⟫_𝕜 - m * ‖x‖ ^ 2 := by
      simp only [B1, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    rw [hshift]
    dsimp [m]
    linarith
  have hρδ : 0 < ρ + δ := by linarith
  obtain ⟨hB1inv, hB1invNorm⟩ :=
    boundedInverseData_of_coercive_direct hρδ hB1coer
  have hEqShift : A1 ∘L Xc - Xc ∘L B1 = Cc :=
    sylvester_shift_invariant AF BF Xc Cc m hEqCut
  have hmain := sylvester_mem_and_gauge_le_of_bound_inverse_swapped
    (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk).toSymmetricOperatorIdealFamily
    hB1inv A1 hρ hδ hB1invNorm hA1norm hEqShift
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := 𝕜) k hk Cc)
  simp only [FanDominantIdealFamily.toSymmetric_gaugeReal] at hmain
  rw [KyFanDominantIdealFamily.kyFan_gauge (𝕜 := 𝕜) k hk Xc,
    KyFanDominantIdealFamily.kyFan_gauge (𝕜 := 𝕜) k hk Cc] at hmain
  simpa only [Xc, Cc, PA, PB, ContinuousLinearMap.comp_assoc] using hmain.2

/-- Ideal membership of the Sylvester solution from ordered cutoff estimates. -/
theorem unbounded_sylvester_mem_of_semibounded_direct
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (PCA : SpectralCutoffInterface A hA)
    (TCA : BoundedTruncationInterface A hA PCA)
    (PCB : SpectralCutoffInterface B hB)
    (TCB : BoundedTruncationInterface B hB PCB)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBc : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X := by
  exact (mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hδ hC
      (kyFan_unbounded_sylvester_le_of_semibounded_direct
        hA hB PCA TCA PCB TCB hδ hAc hBc hEq)).1

/-- Davis--Kahan Theorem 5.2 in the lower-left/upper-right orientation. -/
theorem unbounded_sylvester_mem_and_gauge_le_direct
    (N : FanDominantIdealFamily (𝕜 := 𝕜))
    {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (PCA : SpectralCutoffInterface A hA)
    (TCA : BoundedTruncationInterface A hA PCA)
    (PCB : SpectralCutoffInterface B hB)
    (TCB : BoundedTruncationInterface B hB PCB)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBc : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  exact mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hδ hC
      (kyFan_unbounded_sylvester_le_of_semibounded_direct
        hA hB PCA TCA PCB TCB hδ hAc hBc hEq)

/-- Davis--Kahan Theorem 5.2 in the upper-left/lower-right orientation. -/
theorem unbounded_sylvester_mem_and_gauge_le_direct_swapped
    (N : FanDominantIdealFamily (𝕜 := 𝕜))
    {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (PCA : SpectralCutoffInterface A hA)
    (TCA : BoundedTruncationInterface A hA PCA)
    (PCB : SpectralCutoffInterface B hB)
    (TCB : BoundedTruncationInterface B hB PCB)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedAbove A c)
    (hBc : TauCeti.LinearPMap.SemiboundedBelow B (c + δ))
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  exact mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hδ hC
      (kyFan_unbounded_sylvester_le_of_semibounded_direct_swapped
        hA hB PCA TCA PCB TCB hδ hAc hBc hEq)


end ApproximationNumberEndpointAssumptions

end Sylvester
end DavisKahan
end TauCeti
