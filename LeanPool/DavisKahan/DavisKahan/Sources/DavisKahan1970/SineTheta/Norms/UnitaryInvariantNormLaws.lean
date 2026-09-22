/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-!
# Operator laws for the source-defined unitarily invariant norms

`SymmetricNormingFunction` is the literal coherent symmetric-gauge object used
in Davis--Kahan 1970.  This file proves that its canonical prefix-supremum
extension has all of the operator properties used in the paper: normalization,
absolute homogeneity, triangle inequality, adjoint invariance, two-sided
unitary invariance, contraction compatibility, and the ideal property.

Thus the universal theorem quantified over `SymmetricNormingFunction` does not
hide an independently postulated operator ideal.  The ideal and its norm are
constructed from the single source gauge exactly as in the paper.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal

noncomputable section

universe u v

namespace SymmetricNormingFunction

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- Every finite gauge kills the zero vector. -/
theorem finiteGauge_zero (N : SymmetricNormingFunction) (n : ℕ) :
    N.finiteGauge n (0 : Fin n → ℝ) = 0 := by
  have h := N.finiteGauge_smul (n := n) 0 (0 : Fin n → ℝ)
  simpa only [smul_zero, abs_zero, zero_mul] using h

omit [CompleteSpace E] [CompleteSpace F] in
/-- The source norm of the zero operator is zero. -/
@[simp]
theorem extendedGauge_zero (N : SymmetricNormingFunction) :
    N.extendedGauge (0 : E →L[𝕜] F) = 0 := by
  have hzero : ∀ n : ℕ, N.prefixGauge n (0 : E →L[𝕜] F) = 0 := by
    intro n
    have hx : approximationPrefix n (0 : E →L[𝕜] F) = (0 : Fin n → ℝ) := by
      funext i
      simp only [approximationPrefix, approximationSingularValue_zero_map,
        Pi.zero_apply]
    simp only [prefixGauge, hx, N.finiteGauge_zero n]
  simp only [extendedGauge, hzero, ENNReal.ofReal_zero, iSup_const]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Absolute homogeneity of the extended source norm. -/
theorem extendedGauge_smul (N : SymmetricNormingFunction)
    (c : 𝕜) (A : E →L[𝕜] F) :
    N.extendedGauge (c • A) = ENNReal.ofReal ‖c‖ * N.extendedGauge A := by
  by_cases hc : c = 0
  · subst c
    simp
  · unfold extendedGauge
    rw [ENNReal.mul_iSup]
    apply iSup_congr
    intro n
    rw [← ENNReal.ofReal_mul (norm_nonneg c)]
    congr 1
    unfold prefixGauge approximationPrefix
    have hprefix :
        (fun i : Fin n => approximationSingularValue (i : ℕ) (c • A)) =
          ‖c‖ • (fun i : Fin n => approximationSingularValue (i : ℕ) A) := by
      funext i
      rw [approximationSingularValue_smul]
      simp [smul_eq_mul]
    rw [hprefix, N.finiteGauge_smul]
    simp [abs_of_nonneg (norm_nonneg c)]

/-- Triangle inequality for each finite prefix gauge.

The Ky Fan triangle inequality in infinite dimensions is proved from the min--max lower
bound, so what is carried here is the class asserting that bound over the scalar field,
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`, instantiated for `ℝ` and `ℂ`. -/
theorem prefixGauge_add_le
    (N : SymmetricNormingFunction)
    (n : ℕ) (A B : E →L[𝕜] F) :
    N.prefixGauge n (A + B) ≤ N.prefixGauge n A + N.prefixGauge n B := by
  have hmajor :
      N.finiteGauge n (approximationPrefix n (A + B)) ≤
        N.finiteGauge n
          (approximationPrefix n A + approximationPrefix n B) := by
    apply (N.finiteNorm n).gauge_le_gauge_of_prefix_sums_le
      (EuclideanSpace.basisFun (Fin n) ℂ)
    · intro i j hij
      exact approximationSingularValue_antitone (A + B) (Fin.le_def.mp hij)
    · intro i
      exact approximationSingularValue_nonneg _ _
    · intro i
      exact add_nonneg (approximationSingularValue_nonneg _ _)
        (approximationSingularValue_nonneg _ _)
    · intro m
      rcases le_or_gt m n with hm | hm
      · simp only [approximationPrefix, Pi.add_apply]
        rw [sum_filter_lt_eq_sum_fin hm
            (fun k => approximationSingularValue k (A + B)),
          sum_filter_lt_eq_sum_fin hm
            (fun k => approximationSingularValue k A +
              approximationSingularValue k B),
          Fin.sum_univ_eq_sum_range
            (fun k => approximationSingularValue k (A + B)) m,
          Fin.sum_univ_eq_sum_range
            (fun k => approximationSingularValue k A +
              approximationSingularValue k B) m,
          Finset.sum_add_distrib]
        exact kyFanApproximationGauge_add_le m A B
      · have huniv :
          (Finset.univ.filter fun i : Fin n => (i : ℕ) < m) = Finset.univ :=
          Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
        rw [huniv]
        simp only [Pi.add_apply]
        rw [Finset.sum_add_distrib,
          sum_approximationPrefix n (A + B),
          sum_approximationPrefix n A, sum_approximationPrefix n B]
        exact kyFanApproximationGauge_add_le n A B
  exact hmajor.trans (N.finiteGauge_add_le _ _)

/-- Triangle inequality of the canonical infinite-dimensional extension. -/
theorem extendedGauge_add_le
    (N : SymmetricNormingFunction)
    (A B : E →L[𝕜] F) :
    N.extendedGauge (A + B) ≤ N.extendedGauge A + N.extendedGauge B := by
  apply iSup_le
  intro n
  calc
    ENNReal.ofReal (N.prefixGauge n (A + B)) ≤
        ENNReal.ofReal (N.prefixGauge n A + N.prefixGauge n B) :=
      ENNReal.ofReal_le_ofReal (N.prefixGauge_add_le n A B)
    _ = ENNReal.ofReal (N.prefixGauge n A) +
        ENNReal.ofReal (N.prefixGauge n B) :=
      ENNReal.ofReal_add (N.finiteGauge_nonneg _) (N.finiteGauge_nonneg _)
    _ ≤ N.extendedGauge A + N.extendedGauge B :=
      add_le_add
        (le_iSup (fun m => ENNReal.ofReal (N.prefixGauge m A)) n)
        (le_iSup (fun m => ENNReal.ofReal (N.prefixGauge m B)) n)

/-- Adjoint invariance of the source norm.

This is a genuinely *heterogeneous* statement: `A.adjoint : F →L[𝕜] E` while
`A : E →L[𝕜] F`, so it cannot be routed through
`gauge_eq_of_sameApproximationSingularValues`, which compares two operators
between the *same* pair of spaces.  It is proved directly from the equality of
the two approximation singular-value prefixes, which live in the same real
vector space `Fin n → ℝ` regardless of the operators' domains. -/
theorem extendedGauge_adjoint (N : SymmetricNormingFunction)
    (A : E →L[𝕜] F) :
    N.extendedGauge A.adjoint = N.extendedGauge A := by
  simp only [extendedGauge, N.prefixGauge_adjoint]

/-- The canonical ideal of a source norm is adjoint-stable.

Together with `gauge_adjoint` this is what lets a Fan-dominance estimate proved
against one off-diagonal block be read off against its transpose partner, which
lives between the *opposite* pair of spaces. -/
theorem mem_adjoint_iff (N : SymmetricNormingFunction) (A : E →L[𝕜] F) :
    N.Mem A.adjoint ↔ N.Mem A := by
  rw [Mem, Mem, extendedGauge_adjoint]

/-- The real-valued source norm is invariant under adjoint. -/
theorem gauge_adjoint (N : SymmetricNormingFunction) (A : E →L[𝕜] F) :
    N.gauge A.adjoint = N.gauge A := by
  rw [gauge, gauge, extendedGauge_adjoint]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Unitary equivalences on either side preserve the complete source norm. -/
theorem extendedGauge_unitary
    (N : SymmetricNormingFunction)
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) (A : E →L[𝕜] F) :
    N.extendedGauge
      (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
        V.toContinuousLinearEquiv.toContinuousLinearMap) =
      N.extendedGauge A := by
  exact N.gauge_eq_of_sameApproximationSingularValues
    (SameApproximationSingularValues.comp_isometricEquiv (A := A) U V)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Finite Fan dominance between operators with **different codomains**.

`SymmetricNormingFunction.prefixGauge_le_of_all_kyFan_le` compares two
operators between the same pair of spaces.  A two-sided ideal estimate
inherently compares `L ∘L A ∘L R : E →L[𝕜] G` with a rescaling of
`A : E →L[𝕜] F`, so the homogeneous form is not applicable.  Only the real
singular-value prefixes are compared, and those live in `Fin n → ℝ` whatever
the operators' codomains are, so the statement generalizes verbatim. -/
theorem prefixGauge_le_of_all_kyFan_le_hetero (N : SymmetricNormingFunction)
    {A : E →L[𝕜] G} {B : E →L[𝕜] F}
    (h : ∀ k : ℕ, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) (n : ℕ) :
    N.prefixGauge n A ≤ N.prefixGauge n B := by
  change (N.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ)
      (approximationPrefix n A) ≤
    (N.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ)
      (approximationPrefix n B)
  apply (N.finiteNorm n).gauge_le_gauge_of_prefix_sums_le
  · intro i j hij
    exact approximationSingularValue_antitone A (Fin.le_def.mp hij)
  · intro i
    exact approximationSingularValue_nonneg _ _
  · intro i
    exact approximationSingularValue_nonneg _ _
  · intro m
    rcases le_or_gt m n with hm | hm
    · simp only [approximationPrefix]
      rw [sum_filter_lt_eq_sum_fin hm
          (fun k => approximationSingularValue k A),
        sum_filter_lt_eq_sum_fin hm
          (fun k => approximationSingularValue k B),
        Fin.sum_univ_eq_sum_range
          (fun k => approximationSingularValue k A) m,
        Fin.sum_univ_eq_sum_range
          (fun k => approximationSingularValue k B) m]
      exact h m
    · have huniv :
        (Finset.univ.filter fun i : Fin n => (i : ℕ) < m) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
      rw [huniv, sum_approximationPrefix n A, sum_approximationPrefix n B]
      exact h n

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Universal Fan dominance between operators with different codomains. -/
theorem extendedGauge_le_of_all_kyFan_le_hetero
    (N : SymmetricNormingFunction)
    {A : E →L[𝕜] G} {B : E →L[𝕜] F}
    (h : ∀ k : ℕ, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.extendedGauge A ≤ N.extendedGauge B := by
  apply iSup_le
  intro n
  exact le_trans
    (ENNReal.ofReal_le_ofReal
      (N.prefixGauge_le_of_all_kyFan_le_hetero h n))
    (le_iSup (fun m : ℕ => ENNReal.ofReal (N.prefixGauge m B)) n)

omit [CompleteSpace G] in
omit [CompleteSpace E] [CompleteSpace F] in
/-- The two-sided ideal estimate at the extended-value level. -/
theorem extendedGauge_comp_le (N : SymmetricNormingFunction)
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : E →L[𝕜] E) :
    N.extendedGauge (L ∘L A ∘L R) ≤
      ENNReal.ofReal ‖L‖ * N.extendedGauge A * ENNReal.ofReal ‖R‖ := by
  have hLR : (0 : ℝ) ≤ ‖L‖ * ‖R‖ := mul_nonneg (norm_nonneg L) (norm_nonneg R)
  have hcnorm : ‖((‖L‖ * ‖R‖ : ℝ) : 𝕜)‖ = ‖L‖ * ‖R‖ := by
    rw [RCLike.norm_ofReal, abs_of_nonneg hLR]
  have hkey : ∀ k : ℕ,
      kyFanApproximationGauge k (L ∘L A ∘L R) ≤
        kyFanApproximationGauge k (((‖L‖ * ‖R‖ : ℝ) : 𝕜) • A) := by
    intro k
    rw [kyFanApproximationGauge_smul, hcnorm]
    calc
      kyFanApproximationGauge k (L ∘L A ∘L R)
          ≤ ‖L‖ * kyFanApproximationGauge k A * ‖R‖ :=
        kyFanApproximationGauge_comp_le k L A R
      _ = ‖L‖ * ‖R‖ * kyFanApproximationGauge k A := by ring
  have hle := N.extendedGauge_le_of_all_kyFan_le_hetero hkey
  rw [N.extendedGauge_smul, hcnorm,
    ENNReal.ofReal_mul (norm_nonneg L)] at hle
  refine hle.trans_eq ?_
  ring

omit [CompleteSpace G] in
omit [CompleteSpace E] [CompleteSpace F] in
/-- Membership is a two-sided operator ideal. -/
theorem comp_mem (N : SymmetricNormingFunction)
    {A : E →L[𝕜] F} (hA : N.Mem A)
    (L : F →L[𝕜] G) (R : E →L[𝕜] E) :
    N.Mem (L ∘L A ∘L R) := by
  have hle := N.extendedGauge_comp_le L A R
  intro htop
  rw [htop] at hle
  have hfinite :
      ENNReal.ofReal ‖L‖ * N.extendedGauge A * ENNReal.ofReal ‖R‖ ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact hA
    · exact ENNReal.ofReal_ne_top
  exact hfinite (top_le_iff.mp hle)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The real gauge is absolutely homogeneous on its ideal. -/
theorem gauge_smul (N : SymmetricNormingFunction)
    (c : 𝕜) {A : E →L[𝕜] F} (_hA : N.Mem A) :
    N.gauge (c • A) = ‖c‖ * N.gauge A := by
  simp only [gauge]
  rw [N.extendedGauge_smul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (norm_nonneg c)]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The extended gauge does not see a sign.** -/
theorem extendedGauge_neg (N : SymmetricNormingFunction) (A : E →L[𝕜] F) :
    N.extendedGauge (-A) = N.extendedGauge A := by
  have hA : (-A : E →L[𝕜] F) = (-1 : 𝕜) • A := by
    ext x; simp
  rw [hA, N.extendedGauge_smul]
  simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Ideal membership does not see a sign.**

Needed wherever a source theorem is read with the perturbation's sign reversed --
for instance when the ambient estimates are applied along `A + H` with
perturbation `-H` to put the spectral gap on the perturbed blocks, which is where
the source states it. -/
theorem mem_neg (N : SymmetricNormingFunction) {A : E →L[𝕜] F} :
    N.Mem (-A) ↔ N.Mem A := by
  simp only [Mem, N.extendedGauge_neg]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The real gauge does not see a sign.** -/
theorem gauge_neg (N : SymmetricNormingFunction) (A : E →L[𝕜] F) :
    N.gauge (-A) = N.gauge A := by
  simp only [gauge, N.extendedGauge_neg]

/-- The real gauge is subadditive on its canonical ideal. -/
theorem gauge_add_le
    (N : SymmetricNormingFunction)
    {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.gauge (A + B) ≤ N.gauge A + N.gauge B := by
  have hsum : N.extendedGauge A + N.extendedGauge B ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hA, hB⟩
  have hAB : N.Mem (A + B) := by
    intro htop
    have hle := N.extendedGauge_add_le A B
    rw [htop] at hle
    exact hsum (top_le_iff.mp hle)
  have hto := (ENNReal.toReal_le_toReal hAB hsum).mpr
    (N.extendedGauge_add_le A B)
  rw [ENNReal.toReal_add hA hB] at hto
  exact hto

omit [CompleteSpace G] in
omit [CompleteSpace E] [CompleteSpace F] in
/-- Exact ideal inequality for the real-valued source norm. -/
theorem gauge_comp_le (N : SymmetricNormingFunction)
    {A : E →L[𝕜] F} (hA : N.Mem A)
    (L : F →L[𝕜] G) (R : E →L[𝕜] E) :
    N.gauge (L ∘L A ∘L R) ≤ ‖L‖ * N.gauge A * ‖R‖ := by
  have hcomp := N.comp_mem hA L R
  have hle := N.extendedGauge_comp_le L A R
  have hfin :
      ENNReal.ofReal ‖L‖ * N.extendedGauge A * ENNReal.ofReal ‖R‖ ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA) ENNReal.ofReal_ne_top
  have hto := (ENNReal.toReal_le_toReal hcomp hfin).mpr hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (norm_nonneg L),
    ENNReal.toReal_ofReal (norm_nonneg R)] at hto
  exact hto

omit [CompleteSpace G] in
omit [CompleteSpace E] [CompleteSpace F] in
/-- The canonical source norm satisfies the contraction-compatibility law
used in the paper. -/
theorem gauge_comp_le_of_contractions (N : SymmetricNormingFunction)
    {A : E →L[𝕜] F} (hA : N.Mem A)
    (L : F →L[𝕜] G) (R : E →L[𝕜] E)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    N.gauge (L ∘L A ∘L R) ≤ N.gauge A := by
  refine (N.gauge_comp_le hA L R).trans ?_
  have hnonneg : 0 ≤ N.gauge A := ENNReal.toReal_nonneg
  calc ‖L‖ * N.gauge A * ‖R‖ ≤ ‖L‖ * N.gauge A * 1 :=
        mul_le_mul_of_nonneg_left hR (mul_nonneg (norm_nonneg L) hnonneg)
    _ = ‖L‖ * N.gauge A := mul_one _
    _ ≤ 1 * N.gauge A := mul_le_mul_of_nonneg_right hL hnonneg
    _ = N.gauge A := one_mul _

end SymmetricNormingFunction

end

end ExactSinTheta
end DavisKahan
end TauCeti
