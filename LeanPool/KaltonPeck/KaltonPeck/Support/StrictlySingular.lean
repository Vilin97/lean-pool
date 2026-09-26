/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module

/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Strictly singular operators

This file defines strictly singular bounded operators and proves their basic behavior under
composition, together with strict singularity of compact operators.
-/

@[expose] public section


namespace KaltonPeck.Support.StrictlySingular

open Function Set Filter Topology

/-- A bounded operator is strictly singular when it is not bounded below after precomposition
with any bounded-below embedding of an infinite-dimensional Banach space.
Blueprint label: `def:strictly-singular`. -/
def IsStrictlySingular
    {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) : Prop :=
  ∀ (Z : Type*) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z],
    ¬ FiniteDimensional 𝕜 Z →
      ∀ S : Z →L[𝕜] X, (∃ K, AntilipschitzWith K S) →
        ¬ ∃ K, AntilipschitzWith K (T.comp S)

private theorem antilipschitzWith_of_comp
    {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (R : Y →L[𝕜] Z) (U : X →L[𝕜] Y) {K : NNReal}
    (h : AntilipschitzWith K (R.comp U)) :
    AntilipschitzWith (K * ‖R‖₊) U := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  calc
    dist x y ≤ (K : ℝ) * dist (R (U x)) (R (U y)) := by
      simpa only [ContinuousLinearMap.comp_apply] using h.le_mul_dist x y
    _ ≤ (K : ℝ) * ((‖R‖₊ : ℝ) * dist (U x) (U y)) :=
      mul_le_mul_of_nonneg_left (R.lipschitzWith.dist_le_mul _ _) (NNReal.coe_nonneg K)
    _ = ((K * ‖R‖₊ : NNReal) : ℝ) * dist (U x) (U y) := by
      rw [NNReal.coe_mul]
      ring

universe u𝕜 uX uY uZ uV uW

/-- An upper semi-Fredholm operator on an infinite-dimensional Banach space is not strictly
singular.
Blueprint label: `lem:upper-semi-not-strictly-singular`. -/
theorem not_isStrictlySingular_of_finiteDimensional_ker_of_isClosed_range
    {𝕜 : Type u𝕜} {X : Type uX} {Y : Type uY}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (hX : ¬ FiniteDimensional 𝕜 X) (A : X →L[𝕜] Y)
    (hkerA : FiniteDimensional 𝕜 A.toLinearMap.ker)
    (hrangeA : IsClosed (A.toLinearMap.range : Set Y)) :
    ¬ IsStrictlySingular.{u𝕜, uX, uY, uX} A := by
  let : FiniteDimensional 𝕜 A.toLinearMap.ker := hkerA
  let hker : A.toLinearMap.ker.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional A.toLinearMap.ker
  let Z : Submodule 𝕜 X := hker.complement
  have htop : Submodule.IsTopCompl A.toLinearMap.ker Z :=
    hker.isTopCompl_complement
  have hZclosed : IsClosed (Z : Set X) := hker.isClosed_complement
  let : CompleteSpace Z := hZclosed.completeSpace_coe
  have hZ : ¬ FiniteDimensional 𝕜 Z := by
    intro hZfin
    let : FiniteDimensional 𝕜 Z := hZfin
    have hprod : FiniteDimensional 𝕜 (A.toLinearMap.ker × Z) := inferInstance
    let : FiniteDimensional 𝕜 X :=
      @LinearEquiv.finiteDimensional 𝕜 (A.toLinearMap.ker × Z) _ _ _
        X _ _ (Submodule.prodEquivOfIsCompl _ _ htop.isCompl) hprod
    exact hX inferInstance
  let S : Z →L[𝕜] X := Z.subtypeL
  have hS : ∃ K, AntilipschitzWith K S := by
    exact ⟨1, by
      simpa [S, Submodule.subtypeₗᵢ_toContinuousLinearMap] using
        Z.subtypeₗᵢ.antilipschitz⟩
  have hASinjective : Function.Injective (A.comp S) := by
    intro x y hxy
    apply Subtype.ext
    have hkerxy : (x : X) - (y : X) ∈ A.toLinearMap.ker := by
      change A ((x : X) - (y : X)) = 0
      rw [map_sub, sub_eq_zero]
      simpa [S] using hxy
    have hZxy : (x : X) - (y : X) ∈ Z := Z.sub_mem x.property y.property
    have hzero : (x : X) - (y : X) ∈ (⊥ : Submodule 𝕜 X) :=
      htop.isCompl.disjoint.le_bot ⟨hkerxy, hZxy⟩
    simpa only [Submodule.mem_bot, sub_eq_zero] using hzero
  have hrange : Set.range (A.comp S) = (A.toLinearMap.range : Set Y) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨x, rfl⟩
      have hx : x ∈ A.toLinearMap.ker ⊔ Z := by
        rw [htop.isCompl.sup_eq_top]
        exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hx with ⟨k, hk, z, hz, hkz⟩
      refine ⟨⟨z, hz⟩, ?_⟩
      change A z = A x
      rw [← hkz, map_add, show A k = 0 from hk, zero_add]
  have hASclosed : IsClosed (Set.range (A.comp S)) := by
    rw [hrange]
    exact hrangeA
  have hAS : ∃ K, AntilipschitzWith K (A.comp S) :=
    (A.comp S).antilipschitz_of_injective_of_isClosed_range hASinjective hASclosed
  intro hstrict
  exact hstrict Z hZ S hS hAS

/-- Postcomposition by a bounded operator preserves strict singularity.
Blueprint label: `lem:strictly-singular-comp`. -/
theorem IsStrictlySingular.postcomp
    {𝕜 : Type u𝕜} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {T : X →L[𝕜] Y} (hT : IsStrictlySingular.{u𝕜, uX, uY, uV} T)
    (R : Y →L[𝕜] Z) :
    IsStrictlySingular.{u𝕜, uX, uZ, uV} (R.comp T) := by
  intro W _ _ _ hW S hS hRTS
  apply hT W hW S hS
  rcases hRTS with ⟨K, hK⟩
  exact ⟨K * ‖R‖₊, by
    simpa only [ContinuousLinearMap.comp_apply] using
      antilipschitzWith_of_comp R (T.comp S) hK⟩

/-- Precomposition by a bounded operator preserves strict singularity.
Blueprint label: `lem:strictly-singular-comp`. -/
theorem IsStrictlySingular.precomp
    {𝕜 : Type u𝕜} {W : Type uW} {X : Type uX} {Y : Type uY}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {T : X →L[𝕜] Y} (hT : IsStrictlySingular.{u𝕜, uX, uY, uV} T)
    (R : W →L[𝕜] X) :
    IsStrictlySingular.{u𝕜, uW, uY, uV} (T.comp R) := by
  intro V _ _ _ hV S _ hTRS
  rcases hTRS with ⟨K, hK⟩
  have hRS : ∃ L, AntilipschitzWith L (R.comp S) :=
    ⟨K * ‖T‖₊, by
      simpa only [ContinuousLinearMap.comp_apply] using
        antilipschitzWith_of_comp T (R.comp S) hK⟩
  apply hT V hV (R.comp S) hRS
  rw [ContinuousLinearMap.comp_assoc] at hK
  exact ⟨K, hK⟩

/-- Every compact bounded operator is strictly singular.
Blueprint label: `lem:compact-strictly-singular`. -/
theorem isStrictlySingular_of_isCompactOperator
    {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (hT : IsCompactOperator T) : IsStrictlySingular T := by
  intro Z _ _ _ hZ S _ hTS
  rcases hTS with ⟨K, hanti⟩
  rcases hT.comp_clm S with ⟨C, hC, hC0⟩
  have hemb : IsClosedEmbedding (T.comp S) :=
    hanti.isClosedEmbedding (T.comp S).uniformContinuous
  have hpre : IsCompact ((T.comp S) ⁻¹' C) := hemb.isCompact_preimage hC
  let : LocallyCompactSpace Z :=
    hpre.locallyCompactSpace_of_mem_nhds_of_addGroup hC0
  exact hZ (FiniteDimensional.of_locallyCompactSpace 𝕜)

end KaltonPeck.Support.StrictlySingular

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
