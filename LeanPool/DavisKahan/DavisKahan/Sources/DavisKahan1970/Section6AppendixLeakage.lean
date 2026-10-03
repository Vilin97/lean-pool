/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtBasis
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFiniteRank

/-! # Section6Appendix Leakage -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Lemma 6.3

The paper uses the first Ky Fan norm in the conclusion, hence the operator
norm.  The quantitative input is near-saturation of the sum of squares of the
first `v` singular values.

## Source-faithful block hypothesis

An earlier scaffold stated the block hypothesis as `K * P = Q * K`.  That
equation forces `Q * K * (1 - P) = 0` outright, trivializing the leakage
conclusion and *not* representing the paper.  The source hypothesis is the
weaker block-invariance statement

```text
K * P = Q * K * P,
```

which only says that the image of the selected source block lies in the
selected target block.  This module states and proves the corrected result in
both the approximation-number form and the finite-dimensional singular-value
specialization.  The proof was developed ahead of the frontier and is promoted
here.

The proof exposes three ingredients:

1. left compression by a rank-`n` projection cannot increase the first-`n`
   square energy;
2. Hilbert--Schmidt energy splits over the orthogonal domain decomposition
   `P + (1 - P)`;
3. the operator norm is bounded by the Hilbert--Schmidt energy of the off
   block (through the zeroth approximation number, which needs `0 < n`).

The final argument is then a scalar subtraction.

## Scalar scope

Everything except the Pythagorean splitting is scalar generic and is stated
here over `RCLike 𝕜`.  The splitting itself is proved over `ℂ` because the
column-energy bridge `approximationNumberEnergy_eq_basisEnergy` is; the real
splitting, and with it the real Hilbert-space form of the lemma, is obtained by
complexification in
`DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakageReal.lean`.  The
`_of_energySplit` core below is the shared engine of the two scalar cases.
-/

open scoped InnerProductSpace BigOperators ENNReal
open Finset

namespace TauCeti
namespace DavisKahan1970
namespace Section6Appendix

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

universe u v w

variable {𝕜 : Type w} [RCLike 𝕜] {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Sum of squares of the first `n` approximation numbers. -/
noncomputable def approximationEnergy
    (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (approximationSingularValue i T) ^ 2

omit [CompleteSpace E] [CompleteSpace F] in
/-- The prefix square energy is a sum of squares, hence nonnegative. -/
theorem approximationEnergy_nonneg
    (T : E →L[𝕜] F) (n : ℕ) :
    0 ≤ approximationEnergy T n := by
  unfold approximationEnergy
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

omit [CompleteSpace E] [CompleteSpace F] in
/-- The zeroth approximation number is the operator norm, so every nonempty
prefix square energy dominates the squared operator norm. -/
theorem opNorm_sq_le_approximationEnergy
    (T : E →L[𝕜] F) {n : ℕ} (hn : 0 < n) :
    ‖T‖ ^ 2 ≤ approximationEnergy T n := by
  unfold approximationEnergy
  have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
  have hzero :
      (approximationSingularValue 0 T) ^ 2 = ‖T‖ ^ 2 := by
    unfold approximationSingularValue
    rw [T.approximationNumber_index_zero]
  calc
    ‖T‖ ^ 2 = (approximationSingularValue 0 T) ^ 2 := hzero.symm
    _ ≤ ∑ i ∈ Finset.range n,
        (approximationSingularValue i T) ^ 2 := by
      exact Finset.single_le_sum
        (fun i hi => sq_nonneg (approximationSingularValue i T)) hmem

omit [CompleteSpace E] [CompleteSpace F] in
/-- Left composition by an orthogonal projection cannot increase the first
`n` square energy. -/
theorem approximationEnergy_starProjection_comp_le
    (K : E →L[𝕜] F)
    (Q : Submodule 𝕜 F) [Q.HasOrthogonalProjection] (n : ℕ) :
    approximationEnergy (Q.starProjection ∘L K) n ≤
      approximationEnergy K n := by
  unfold approximationEnergy
  apply Finset.sum_le_sum
  intro i hi
  have hcomp :
      approximationSingularValue i (Q.starProjection ∘L K) ≤
        approximationSingularValue i K := by
    unfold approximationSingularValue
    calc
      (Q.starProjection ∘L K).approximationNumber i
          ≤ ‖Q.starProjection‖ * K.approximationNumber i :=
            ContinuousLinearMap.approximationNumber_comp_le_norm_mul
              Q.starProjection K i
      _ ≤ 1 * K.approximationNumber i :=
            mul_le_mul_of_nonneg_right Q.starProjection_norm_le
              (K.approximationNumber_nonneg i)
      _ = K.approximationNumber i := one_mul _
  exact pow_le_pow_left₀
    (approximationSingularValue_nonneg i _)
    hcomp 2

omit [CompleteSpace E] [CompleteSpace F] in
/-- A finite-rank operator's prefix square energy is the real form of its
paper Hilbert--Schmidt energy. -/
theorem approximationEnergy_eq_approximationNumberEnergy_toReal_of_rank_le
    (T : E →L[𝕜] F) {n : ℕ}
    (hrank : T.rank ≤ (n : Cardinal)) :
    approximationEnergy T n =
      (approximationNumberEnergy T).toReal := by
  rw [approximationNumberEnergy_eq_sum_range_of_rank_le hrank]
  unfold approximationEnergy
  rw [ENNReal.toReal_sum]
  · exact Finset.sum_congr rfl fun i hi => by
      rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  · intro i hi
    exact ENNReal.ofReal_ne_top

omit [CompleteSpace E] [CompleteSpace F] in
/-- Rank of a left-compressed operator is bounded by the rank of the
compressing projection. -/
theorem rank_starProjection_comp_le
    (K : E →L[𝕜] F)
    (Q : Submodule 𝕜 F) [Q.HasOrthogonalProjection] :
    (Q.starProjection ∘L K).rank ≤ Q.starProjection.rank := by
  exact LinearMap.rank_comp_le_left
    K.toLinearMap Q.starProjection.toLinearMap

section ComplexPythagoras

variable {E' : Type u} {F' : Type v}
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']

/-- The paper square energy splits over an orthogonal decomposition of the
domain.  This is the basis-free Pythagorean identity used in Lemma 6.3.

Stated over `ℂ` because the column-energy bridge it uses is; the real form is
`hilbertSchmidtEnergy_domain_projection_add_real`, obtained by
complexification. -/
theorem hilbertSchmidtEnergy_domain_projection_add_complex
    (L : E' →L[ℂ] F')
    (P : Submodule ℂ E') [P.HasOrthogonalProjection]
    -- carried for source fidelity: Davis--Kahan Lemma 6.3 states this for
    -- Hilbert--Schmidt `L`, and the proof happens not to need it
    (_hfinite : approximationNumberEnergy L ≠ ⊤) :
    approximationNumberEnergy L =
      approximationNumberEnergy (L ∘L P.starProjection) +
      approximationNumberEnergy
        (L ∘L (1 - P.starProjection)) := by
  classical
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis ℂ F'
  -- Rectangular Hilbert--Schmidt energy of any `M : E' → F'` equals the summed
  -- squared columns of its adjoint over the fixed basis `b` of `F'`.
  have hswap : ∀ M : E' →L[ℂ] F',
      approximationNumberEnergy M =
        hilbertSchmidtBasisEnergy b M.adjoint := by
    intro M
    obtain ⟨κ, bE, -⟩ := exists_hilbertBasis ℂ E'
    rw [approximationNumberEnergy_eq_basisEnergy bE M,
      hilbertSchmidtBasisEnergy_adjoint_swap bE b M]
  -- The adjoints of the two compressed operators are the projected columns.
  have hPadj :
      (L ∘L P.starProjection).adjoint = P.starProjection ∘L L.adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection P).adjoint_eq]
  have hPcadj :
      (L ∘L (1 - P.starProjection)).adjoint =
        (1 - P.starProjection) ∘L L.adjoint := by
    have hsa : (1 - P.starProjection).adjoint = 1 - P.starProjection := by
      rw [← Submodule.starProjection_orthogonal' P]
      exact (isSelfAdjoint_starProjection Pᗮ).adjoint_eq
    rw [ContinuousLinearMap.adjoint_comp, hsa]
  rw [hswap L, hswap (L ∘L P.starProjection),
    hswap (L ∘L (1 - P.starProjection)), hPadj, hPcadj]
  unfold hilbertSchmidtBasisEnergy
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro i
  simp only [ContinuousLinearMap.comp_apply]
  -- Pointwise this is the Pythagorean identity for the orthogonal projection.
  have hpyth := P.norm_sq_eq_add_norm_sq_starProjection (L.adjoint (b i))
  rw [Submodule.starProjection_orthogonal' P] at hpyth
  simp only [← ENNReal.coe_pow, ← ENNReal.coe_add, ENNReal.coe_inj]
  apply NNReal.coe_injective
  push_cast
  exact hpyth

end ComplexPythagoras

omit [CompleteSpace E] [CompleteSpace F] in
/-- Under the paper's block-invariance hypothesis the selected source block
is exactly the source restriction of the left-compressed operator. -/
theorem leftCompressed_comp_source_eq
    (K : E →L[𝕜] F)
    (P : Submodule 𝕜 E) [P.HasOrthogonalProjection]
    (Q : Submodule 𝕜 F) [Q.HasOrthogonalProjection]
    (hKP :
      K ∘L P.starProjection =
        Q.starProjection ∘L K ∘L P.starProjection) :
    (Q.starProjection ∘L K) ∘L P.starProjection =
      K ∘L P.starProjection := by
  simpa only [ContinuousLinearMap.comp_assoc] using hKP.symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The scalar-generic engine of Lemma 6.3.**

Everything in the proof of the lemma except the Pythagorean splitting of the
square energy over `P + (1 - P)` is independent of the scalar field, so the
splitting is taken here as a hypothesis on the one operator that needs it.
Over `ℂ` the hypothesis is discharged by
`hilbertSchmidtEnergy_domain_projection_add_complex`, over `ℝ` by
`hilbertSchmidtEnergy_domain_projection_add_real`. -/
theorem lemma6_3_approximationNumber_leakage_of_energySplit
    (K : E →L[𝕜] F)
    (P : Submodule 𝕜 E) [P.HasOrthogonalProjection]
    (Q : Submodule 𝕜 F) [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hsplit :
      approximationNumberEnergy (Q.starProjection ∘L K) =
        approximationNumberEnergy ((Q.starProjection ∘L K) ∘L P.starProjection) +
          approximationNumberEnergy
            ((Q.starProjection ∘L K) ∘L (1 - P.starProjection)))
    (hnear : approximationEnergy (K ∘L P.starProjection) n >
      approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  let L : E →L[𝕜] F := Q.starProjection ∘L K
  let A : E →L[𝕜] F := K ∘L P.starProjection
  let B : E →L[𝕜] F :=
    Q.starProjection ∘L K ∘L (1 - P.starProjection)
  have hrankL : L.rank ≤ (n : Cardinal) := by
    dsimp [L]
    exact (rank_starProjection_comp_le K Q).trans hrankQ
  have hrankA : A.rank ≤ (n : Cardinal) := by
    have hAeq :
        A = Q.starProjection ∘L (K ∘L P.starProjection) := by
      change K ∘L P.starProjection = Q.starProjection ∘L (K ∘L P.starProjection)
      rw [← ContinuousLinearMap.comp_assoc]
      exact hKP
    rw [hAeq]
    exact
      (rank_starProjection_comp_le
        (K ∘L P.starProjection) Q).trans hrankQ
  have hrankB : B.rank ≤ (n : Cardinal) := by
    have hBeq :
        B = Q.starProjection ∘L (K ∘L (1 - P.starProjection)) := rfl
    rw [hBeq]
    exact
      (rank_starProjection_comp_le
        (K ∘L (1 - P.starProjection)) Q).trans hrankQ
  have hsplitE :
      approximationEnergy L n =
        approximationEnergy A n +
          approximationEnergy B n := by
    have hLP : L ∘L P.starProjection = A := by
      dsimp [L, A]
      exact leftCompressed_comp_source_eq K P Q hKP
    have hLB :
        L ∘L (1 - P.starProjection) = B := rfl
    have hAfinite : approximationNumberEnergy A ≠ ⊤ :=
      approximationNumberEnergy_ne_top_of_rank_le hrankA
    have hBfinite : approximationNumberEnergy B ≠ ⊤ :=
      approximationNumberEnergy_ne_top_of_rank_le hrankB
    have hreal := congrArg ENNReal.toReal hsplit
    rw [hLP, hLB, ENNReal.toReal_add hAfinite hBfinite,
      ← approximationEnergy_eq_approximationNumberEnergy_toReal_of_rank_le L hrankL,
      ← approximationEnergy_eq_approximationNumberEnergy_toReal_of_rank_le A hrankA,
      ← approximationEnergy_eq_approximationNumberEnergy_toReal_of_rank_le B hrankB] at hreal
    exact hreal
  have hLle :
      approximationEnergy L n ≤
        approximationEnergy K n := by
    dsimp [L]
    exact approximationEnergy_starProjection_comp_le K Q n
  have hBenergy : approximationEnergy B n < η ^ 2 := by
    rw [hsplitE] at hLle
    have hnear' :
        approximationEnergy A n >
          approximationEnergy K n - η ^ 2 := hnear
    nlinarith [hLle, hnear']
  have hnormsq : ‖B‖ ^ 2 ≤ approximationEnergy B n :=
    opNorm_sq_le_approximationEnergy B hn
  have hsq : ‖B‖ ^ 2 < η ^ 2 :=
    lt_of_le_of_lt hnormsq hBenergy
  have hnormnonneg : 0 ≤ ‖B‖ := norm_nonneg B
  have hηnonneg : 0 ≤ η := le_of_lt hη
  have hnorm : ‖B‖ < η := by
    nlinarith
  simpa only [B] using hnorm

omit [CompleteSpace E] [CompleteSpace F] in
/-- In finite dimensions, the approximation energy is the sum of the squared
ordinary singular values over the same prefix. -/
theorem approximationEnergy_eq_singularValues
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (T : E →L[𝕜] F) (n : ℕ) :
    approximationEnergy T n =
      ∑ i ∈ Finset.range n,
        ((LinearMap.singularValues T.toLinearMap i : ℝ) ^ 2) := by
  unfold approximationEnergy
  apply Finset.sum_congr rfl
  intro i hi
  have hsv :=
    ContinuousLinearMap.approximationNumber_eq_singularValues T i
  change ((T.approximationNumber i : ℝ) ^ 2) =
    (T.toLinearMap.singularValues i : ℝ) ^ 2
  rw [hsv]
  rfl

section ComplexScalars

variable {E' : Type u} {F' : Type v}
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']

/-- Approximation-number form of Davis--Kahan 1970, Lemma 6.3.

The block hypothesis is the source-faithful `K ∘ P = Q ∘ K ∘ P`, and the
positive-prefix hypothesis `0 < n` is explicit because the proof controls the
operator norm through the zeroth approximation number.  The rank bound on `P`
is retained for source symmetry; only the bound on `Q` is used. -/
theorem lemma6_3_approximationNumber_leakage_complex
    (K : E' →L[ℂ] F')
    (P : Submodule ℂ E') [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F') [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (_hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear : approximationEnergy (K ∘L P.starProjection) n >
      approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  refine lemma6_3_approximationNumber_leakage_of_energySplit
    K P Q n hn η hη hKP hrankQ ?_ hnear
  refine hilbertSchmidtEnergy_domain_projection_add_complex
    (Q.starProjection ∘L K) P ?_
  exact approximationNumberEnergy_ne_top_of_rank_le
    ((rank_starProjection_comp_le K Q).trans hrankQ)

/-- Finite-dimensional singular-value specialization of Lemma 6.3, with the
source-faithful block hypothesis. -/
theorem lemma6_3_singularValue_leakage_complex
    [FiniteDimensional ℂ E'] [FiniteDimensional ℂ F']
    (K : E' →L[ℂ] F')
    (P : Submodule ℂ E') [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F') [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear :
      ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues
            (K ∘L P.starProjection).toLinearMap i : ℝ) ^ 2) >
        ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues K.toLinearMap i : ℝ) ^ 2) - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  apply lemma6_3_approximationNumber_leakage_complex
    K P Q n hn η hη hKP hrankP hrankQ
  simpa only [approximationEnergy_eq_singularValues] using hnear

end ComplexScalars

end Section6Appendix
end DavisKahan1970
end TauCeti
