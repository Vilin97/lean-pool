/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Complete singular-value transport for the paper-facing sine operators

Davis--Kahan Theorem 6.1 permits `sin Θ₀` to be any operator with the same
complete singular-value sequence as the canonical cross-projection block.
In infinite dimensions the zero-based approximation numbers are the stable
replacement for the finite singular-value list. This module proves that equal
approximation-number sequences give exactly the same membership and gauge in
every Ky-Fan-dominant unitarily invariant ideal family.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe u vE vF vE1 vF1 vE2 vF2 vE3 vF3 vE0 vF0 vS

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type vE} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Operators between possibly different Hilbert spaces have the same complete
singular-value sequence.  This is the relation used literally in the paper.

It is `ContinuousLinearMap.HasSameApproximationNumbers`, staged in
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/SameSequence.lean`; the abbreviation
keeps the paper's name for the source layer. -/
abbrev SameApproximationSingularSequence
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] 
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] 
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] 
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] 
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₂) : Prop :=
  A.HasSameApproximationNumbers B

namespace SameApproximationSingularSequence

/-- Reflexivity.  This is the cross-space relation -- unlike the same-space version later in
the file, the two operators may live between *different* spaces, which is why the binders are
so long. -/
@[refl]
theorem refl
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] 
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] 
    (A : E →L[𝕜] F) : SameApproximationSingularSequence A A := fun _ => rfl

/-- Symmetry, swapping two independently-typed pairs of spaces. -/
@[symm]
theorem symm
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] 
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] 
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] 
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] 
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    SameApproximationSingularSequence B A := fun n => (h n).symm

/-- Transitivity, across three independently-typed pairs of spaces. -/
@[trans]
theorem trans
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    {E₃ : Type vE3} {F₃ : Type vF3}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] 
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] 
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] 
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] 
    [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃] 
    [NormedAddCommGroup F₃] [InnerProductSpace 𝕜 F₃] 
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂} {C : E₃ →L[𝕜] F₃}
    (hAB : SameApproximationSingularSequence A B)
    (hBC : SameApproximationSingularSequence B C) :
    SameApproximationSingularSequence A C := fun n => (hAB n).trans (hBC n)

/-- Equal complete singular data gives equal operator norms. -/
theorem opNorm_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] 
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] 
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] 
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] 
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) : ‖A‖ = ‖B‖ :=
  ContinuousLinearMap.HasSameApproximationNumbers.norm_eq h

/-- Equal complete singular data gives equal finite Ky Fan sums. -/
theorem kyFanApproximationGauge_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] 
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] 
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] 
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] 
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) (k : ℕ) :
    kyFanApproximationGauge k A = kyFanApproximationGauge k B :=
  ContinuousLinearMap.HasSameApproximationNumbers.kyFanGauge_eq h k

end SameApproximationSingularSequence

/-- Two-sided composition with isometric equivalences never increases an
approximation number.  Only `‖U‖₊ ≤ 1` is used, so no nontriviality
assumption on the coordinate spaces is required. -/
private theorem approximationNumber_comp_isometricEquiv_le
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (U : F₁ ≃ₗᵢ[𝕜] F₂) (V : E₂ ≃ₗᵢ[𝕜] E₁) (A : E₁ →L[𝕜] F₁) (n : ℕ) :
    (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
        V.toContinuousLinearEquiv.toContinuousLinearMap).approximationNumber n
      ≤ A.approximationNumber n := by
  have hU : ‖U.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  have hV : ‖V.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  calc
    (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
          V.toContinuousLinearEquiv.toContinuousLinearMap).approximationNumber n
        ≤ ‖U.toContinuousLinearEquiv.toContinuousLinearMap‖ *
            A.approximationNumber n *
            ‖V.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
      ContinuousLinearMap.approximationNumber_comp_comp_le _ _ _ n
    _ ≤ 1 * A.approximationNumber n * 1 := by
      gcongr <;>
        first
          | assumption
          | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
    _ = A.approximationNumber n := by rw [one_mul, mul_one]

/-- Two-sided composition with isometric equivalences preserves every
approximation number. -/
private theorem approximationNumber_comp_isometricEquiv_eq
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (U : F₁ ≃ₗᵢ[𝕜] F₂) (V : E₂ ≃ₗᵢ[𝕜] E₁) (A : E₁ →L[𝕜] F₁) (n : ℕ) :
    (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
        V.toContinuousLinearEquiv.toContinuousLinearMap).approximationNumber n
      = A.approximationNumber n := by
  refine le_antisymm (approximationNumber_comp_isometricEquiv_le U V A n) ?_
  have hfac :
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
            V.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
          V.symm.toContinuousLinearEquiv.toContinuousLinearMap = A := by
    ext x
    simp
  calc A.approximationNumber n
      = (U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
              V.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
            V.symm.toContinuousLinearEquiv.toContinuousLinearMap).approximationNumber
          n := by rw [hfac]
    _ ≤ _ := approximationNumber_comp_isometricEquiv_le U.symm V.symm _ n

/-- Two rectangular bounded operators have the same complete singular-value
data when all of their approximation singular values agree. -/
def SameApproximationSingularValues (A B : E →L[𝕜] F) : Prop :=
  SameApproximationSingularSequence A B

namespace SameApproximationSingularValues

omit [CompleteSpace E] [CompleteSpace F] in
/-- Two-sided composition by isometric equivalences preserves every
approximation singular value. -/
theorem comp_isometricEquiv
    {A : E →L[𝕜] F}
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    SameApproximationSingularValues
      (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
        V.toContinuousLinearEquiv.toContinuousLinearMap) A := by
  intro n
  exact approximationNumber_comp_isometricEquiv_eq U V A n

omit [CompleteSpace E] [CompleteSpace F] in
/-- If an operator becomes another operator after unitary coordinate changes,
they have the same complete singular sequence. -/
theorem of_isometricEquiv_comp
    {E' : Type vE1} {F' : Type vF1}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] 
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] 
    (U : F ≃ₗᵢ[𝕜] F') (V : E ≃ₗᵢ[𝕜] E')
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'}
    (h : U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
      V.symm.toContinuousLinearEquiv.toContinuousLinearMap = B) :
    SameApproximationSingularSequence A B := by
  intro n
  have hkey := approximationNumber_comp_isometricEquiv_eq U V.symm A n
  rw [h] at hkey
  exact hkey.symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- Reflexivity.  With `symm` and `trans` this makes `SameApproximationSingularValues` an
equivalence usable by `refl`/`symm`/`trans` via the attributes. -/
@[refl]
theorem refl (A : E →L[𝕜] F) : SameApproximationSingularValues A A :=
  fun _ => rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- Symmetry. -/
@[symm]
theorem symm {A B : E →L[𝕜] F}
    (h : SameApproximationSingularValues A B) :
    SameApproximationSingularValues B A :=
  fun n => (h n).symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- Transitivity. -/
@[trans]
theorem trans {A B C : E →L[𝕜] F}
    (hAB : SameApproximationSingularValues A B)
    (hBC : SameApproximationSingularValues B C) :
    SameApproximationSingularValues A C :=
  fun n => (hAB n).trans (hBC n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Equal complete singular-value data gives equal finite Ky Fan gauges. -/
theorem kyFanApproximationGauge_eq {A B : E →L[𝕜] F}
    (h : SameApproximationSingularValues A B) (k : ℕ) :
    kyFanApproximationGauge k A = kyFanApproximationGauge k B := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  exact Finset.sum_congr rfl fun n _ => h n

section IdealGauge

/-! ### Gauge transport

A `KyFanDominantIdealFamily` assigns a gauge to rectangular operators
between Hilbert spaces drawn from a *single* universe: that is how a family
closed under adjoints has to quantify its fields, and it is not an incidental
restriction.  A two-universe variant would be a strictly weaker
object, since a family built for the pair `(v, v)` would no longer apply to the
pair `(v, w)`; there is no single Lean structure carrying one gauge for all
universe pairs at once.

So the results below are stated for a shared universe, which is their natural
generality, while `SameApproximationSingularSequence` and
`SinThetaRepresentativeAcross` above remain genuinely cross-universe:
those are exactly the statements that do not mention a gauge. -/

variable {G H : Type vS}
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Transport ideal membership and exact gauge equality along complete
singular-value equality. -/
theorem mem_and_gauge_eq
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B : G →L[𝕜] H}
    (h : SameApproximationSingularValues A B)
    (hB : N.Mem B) :
    N.Mem A ∧
      N.gauge A =
        N.gauge B := by
  let M := N.toSymmetricOperatorIdealFamily
  have hAB : ∀ k, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B := fun k =>
    le_of_eq (h.kyFanApproximationGauge_eq k)
  obtain ⟨hA, hleAB⟩ := N.majorization_mem_and_gauge_le hB hAB
  have hBA : ∀ k, kyFanApproximationGauge k B ≤
      kyFanApproximationGauge k A := fun k =>
    le_of_eq (h.kyFanApproximationGauge_eq k).symm
  obtain ⟨_, hleBA⟩ := N.majorization_mem_and_gauge_le hA hBA
  exact ⟨hA, le_antisymm hleAB hleBA⟩

/-- Transfer a sharp scalar gauge estimate to any operator with the same
complete singular-value sequence. -/
theorem mem_and_mul_gauge_le
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B C : G →L[𝕜] H} {c : ℝ}
    (h : SameApproximationSingularValues A B)
    (hB : N.Mem B)
    (hbound : c * N.gauge B ≤
      N.gauge C) :
    N.Mem A ∧
      c * N.gauge A ≤
        N.gauge C := by
  obtain ⟨hA, hgauge⟩ := h.mem_and_gauge_eq N hB
  refine ⟨hA, ?_⟩
  rw [hgauge]
  exact hbound

end IdealGauge

end SameApproximationSingularValues

/-- Literal source packaging of the freedom in `sin Theta_0`.  The chosen
representative may act between different Hilbert coordinate spaces, exactly as
in the paper; only its complete singular-value sequence is prescribed. -/
structure SinThetaRepresentativeAcross
    {E₀ : Type vE0} {F₀ : Type vF0}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    (canonical : E →L[𝕜] F) where
  /-- An operator on the representative spaces with the canonical approximation singular
  sequence. -/
  operator : E₀ →L[𝕜] F₀
  same_singular_sequence :
    SameApproximationSingularSequence operator canonical

namespace SinThetaRepresentativeAcross

/-- The canonical operator is an admissible representative. -/
noncomputable def canonical (A : E →L[𝕜] F) :
    SinThetaRepresentativeAcross (E₀ := E) (F₀ := F) A where
  operator := A
  same_singular_sequence := .refl A

end SinThetaRepresentativeAcross

/-- Paper-facing packaging of the freedom in the definition of `sin Θ₀`:
the chosen operator has exactly the complete singular-value sequence of the
canonical directed sine block. -/
structure SinThetaRepresentative (canonical : E →L[𝕜] F) where
  /-- An operator with the same approximation singular values as the canonical directed sine
  block. -/
  operator : E →L[𝕜] F
  same_singular_values : SameApproximationSingularValues operator canonical

namespace SinThetaRepresentative

/-- The canonical block is itself an admissible paper representative. -/
noncomputable def canonical (A : E →L[𝕜] F) :
    SinThetaRepresentative A where
  operator := A
  same_singular_values := .refl A

/-- Every paper representative has exactly the same ideal membership and
gauge as the canonical block.

Stated for a shared universe, for the reason recorded in the gauge-transport
section above: an ideal-family gauge is defined on operators drawn from one
universe. -/
theorem mem_and_gauge_eq
    {G H : Type vS}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {canonical : G →L[𝕜] H}
    (S : SinThetaRepresentative canonical)
    (hcanonical : N.Mem canonical) :
    N.Mem S.operator ∧
      N.gauge S.operator =
        N.gauge canonical :=
  S.same_singular_values.mem_and_gauge_eq N hcanonical

end SinThetaRepresentative

end ExactSinTheta
end DavisKahan
end TauCeti
