/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.KyFanOrthonormal
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Davis--Kahan 1970, Section 1: the Rayleigh--Ritz principle for the `ν`-norms

Equations (1.11)--(1.13).  The `ν`-norm `‖K‖_ν = κ₁ + ⋯ + κ_ν` of (1.11) is carried here by
`kyFanApproximationGauge ν`, the sum of the first `ν` approximation numbers, which agrees
with the sum of the `ν` largest singular values whenever the singular values exist and is
defined for every bounded operator (`kyFanSum_eq_kyFanApproximationGauge`).

The two equations this file supplies are

* **(1.12)** `‖K‖_ν = sup_Ω ‖KΩ‖_ν`, the supremum over projectors `Ω` onto `ν`-dimensional
  subspaces of the domain; and
* **(1.13)** `‖K‖_ν = sup_{Ω,Υ} ‖ΥKΩ‖_ν = sup Re ∑_{k<ν} y_k* K x_k`, the first supremum over
  pairs of `ν`-projectors and the second over pairs of orthonormal `ν`-tuples.

**Both are stated as suprema, not as maxima, and that is the mathematics rather than a
weakness of the proof.**  On an infinite-dimensional space the supremum need not be attained:
take `K` diagonal with entries `1 - 1/n` on an orthonormal basis.  Every approximation number
of that `K` is `1`, so `‖K‖_ν = ν`; but `‖Kx‖ < ‖x‖` for every `x ≠ 0`, so every
`ν`-dimensional compression has `‖KΩ‖_ν < ν` strictly.  An `∃ Ω, ‖KΩ‖_ν = ‖K‖_ν` statement
would therefore be false.  `IsLUB` is the correct reading of the printed `sup`, and the
approximate attaining family it packages is exactly what the Appendix to Section 6 uses when
it invokes (1.13) to produce a `ν`-projector.

**Dimension hypotheses.**  Each statement assumes exactly that the family its supremum ranges
over is nonempty, and nothing more.  (1.12) ranges over `ν`-projectors on the *domain*, so it
assumes only that `E` has room for `ν` orthonormal vectors; the codomain is unconstrained, and
in particular `dim F < ν` is allowed.  (1.13) ranges over pairs, one projector on each side, so
it assumes room on both.  Both hypotheses are vacuously true in the paper's
infinite-dimensional setting, and each is genuinely necessary where it appears: with
`dim F < ν` there is no `ν`-projector `Υ` on `F` at all, which is why (1.13) needs the codomain
hypothesis and (1.12) does not.

**Why (1.12) needs no codomain hypothesis, when its engine does.**  The attaining engine
`exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex` produces an
orthonormal `ν`-tuple in *each* space, so it cannot run at all when `dim F < ν`.  The
conclusion of (1.12) never mentions the codomain, so the fix is to give the engine a codomain
with room: replace `F` by the `L²` sum `F ⊕₂ ℂ^ν` along the contraction `ι` that includes `F`
as the first summand, whose left inverse -- the projection back -- is also a contraction.
`kyFanApproximationGauge_comp_eq_of_leftInverse` says every Ky Fan gauge is blind to that
substitution, so the bound obtained in the padded space is a bound in `F`.  This is why the
`≤` half and the attaining half now have the same hypotheses, namely `hE` alone.

**Scalar field.**  These are stated over `ℂ`, the paper's field.  The reason is not fidelity
alone: the attaining half rests on the min--max localization of approximation numbers, which
this library has for `ℝ` and for `ℂ` but not for an abstract `RCLike` field, since nothing
lets an abstract `RCLike` field be reduced to those two.  The `RCLike`-generic statement,
carrying the localization as the explicit hypothesis
`ContinuousLinearMap.HasMinMaxLowerBound`, is
`TauCeti.ApproximationNumber.exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner`;
everything below is that theorem instantiated and packaged.  The `≤` halves are
`RCLike`-generic already and are cited, not reproved.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.ApproximationNumber

universe u v

section NuNorms

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The span of a finite family is finite-dimensional.

Kept `local`: it exists only so that the `ν`-projector `Ω` of (1.12)--(1.13) can be written
as `(Submodule.span ℂ (Set.range v)).starProjection` inside a set-builder, where there is no
place to introduce the instance by hand. -/
local instance finiteDimensionalSpanRangeFin
    {𝕜 H : Type*} [DivisionRing 𝕜] [AddCommGroup H] [Module 𝕜 H] {ν : ℕ} (v : Fin ν → H) :
    FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range v)) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Davis--Kahan 1970, (1.12), the `≤` half:** compressing the domain by any orthogonal
projector cannot raise the `ν`-norm, `‖KΩ‖_ν ≤ ‖K‖_ν`.

This half needs no hypothesis on `Ω` beyond being an orthogonal projector -- in particular
not that its range is `ν`-dimensional -- because it is only the ideal inequality with
`‖Ω‖ ≤ 1` discharged. -/
theorem equation1_12_gauge_comp_starProjection_le
    (K : E →L[ℂ] F) (ν : ℕ) (Ω : Submodule ℂ E) [Ω.HasOrthogonalProjection] :
    kyFanApproximationGauge ν (K ∘L Ω.starProjection) ≤ kyFanApproximationGauge ν K := by
  simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  refine Finset.sum_le_sum fun n _ => ?_
  calc (K ∘L Ω.starProjection).approximationNumber n
      ≤ K.approximationNumber n * ‖Ω.starProjection‖ :=
        K.approximationNumber_comp_le_mul_norm _ n
    _ ≤ K.approximationNumber n * 1 :=
        mul_le_mul_of_nonneg_left Ω.starProjection_norm_le (K.approximationNumber_nonneg n)
    _ = K.approximationNumber n := mul_one _

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Davis--Kahan 1970, (1.13), the `≤` half for two-sided compressions:**
`‖ΥKΩ‖_ν ≤ ‖K‖_ν` for orthogonal projectors `Ω` on the domain and `Υ` on the codomain. -/
theorem equation1_13_gauge_starProjection_comp_le
    (K : E →L[ℂ] F) (ν : ℕ)
    (Ω : Submodule ℂ E) [Ω.HasOrthogonalProjection]
    (Υ : Submodule ℂ F) [Υ.HasOrthogonalProjection] :
    kyFanApproximationGauge ν (Υ.starProjection ∘L K ∘L Ω.starProjection)
      ≤ kyFanApproximationGauge ν K := by
  simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  refine Finset.sum_le_sum fun n _ => ?_
  have h := ContinuousLinearMap.approximationNumber_comp_comp_le
    Υ.starProjection K Ω.starProjection n
  have h0 := K.approximationNumber_nonneg n
  have hΥ : ‖Υ.starProjection‖ ≤ 1 := Υ.starProjection_norm_le
  have hΩ : ‖Ω.starProjection‖ ≤ 1 := Ω.starProjection_norm_le
  have hA : 0 ≤ ‖Υ.starProjection‖ * K.approximationNumber n :=
    mul_nonneg (norm_nonneg _) h0
  have hstep : ‖Υ.starProjection‖ * K.approximationNumber n * ‖Ω.starProjection‖
      ≤ ‖Υ.starProjection‖ * K.approximationNumber n * 1 :=
    mul_le_mul_of_nonneg_left hΩ hA
  have hstep2 : ‖Υ.starProjection‖ * K.approximationNumber n ≤ 1 * K.approximationNumber n :=
    mul_le_mul_of_nonneg_right hΥ h0
  linarith

/-- **Davis--Kahan 1970, equation (1.12): the Rayleigh--Ritz principle for the `ν`-norms.**

`‖K‖_ν = sup_Ω ‖KΩ‖_ν`, the supremum over projectors `Ω` onto `ν`-dimensional subspaces of
the domain, here indexed by the orthonormal `ν`-tuple spanning the subspace.

A supremum, not a maximum: see the module docstring for the diagonal operator on which it is
not attained.  The single hypothesis says that the domain admits an orthonormal `ν`-tuple,
which is exactly the statement that the printed supremum ranges over a nonempty family; the
codomain carries no hypothesis, so `dim F < ν` is allowed.  The module docstring explains how
the codomain room that the attaining engine needs is supplied by padding. -/
theorem equation1_12 (K : E →L[ℂ] F) {ν : ℕ}
    (hE : ∃ x : Fin ν → E, Orthonormal ℂ x) :
    IsLUB
      {r : ℝ | ∃ v : Fin ν → E, Orthonormal ℂ v ∧
        r = kyFanApproximationGauge ν (K ∘L (Submodule.span ℂ (Set.range v)).starProjection)}
      (kyFanApproximationGauge ν K) := by
  obtain ⟨x, hx⟩ := hE
  -- Pad the codomain with a `ν`-dimensional Euclidean summand so the attaining engine has the
  -- orthonormal `ν`-tuple it wants there.  The inclusion `ι` of `F` as the first summand and
  -- the projection `pr` back onto it are contractions with `pr ∘ ι = id`, so no Ky Fan gauge
  -- can tell the padded operator from the original one.
  set ι : F →L[ℂ] WithLp 2 (F × EuclideanSpace ℂ (Fin ν)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ F
        (EuclideanSpace ℂ (Fin ν))).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.inl ℂ F (EuclideanSpace ℂ (Fin ν))
  set pr : WithLp 2 (F × EuclideanSpace ℂ (Fin ν)) →L[ℂ] F :=
    WithLp.fstL 2 ℂ F (EuclideanSpace ℂ (Fin ν))
  have hleft : Function.LeftInverse pr ι := fun _ => rfl
  have hιnorm : ‖ι‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    have hz : ‖ι z‖ = ‖z‖ := by
      show ‖WithLp.toLp 2 ((z : F), (0 : EuclideanSpace ℂ (Fin ν)))‖ = ‖z‖
      rw [WithLp.prod_norm_eq_of_L2]
      simp
    rw [hz, one_mul]
  have hprnorm : ‖pr‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    calc ‖pr z‖ = ‖WithLp.fst z‖ := rfl
      _ = Real.sqrt (‖WithLp.fst z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖WithLp.fst z‖ ^ 2 + ‖WithLp.snd z‖ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖WithLp.snd z‖])
      _ = ‖z‖ := (WithLp.prod_norm_eq_of_L2 z).symm
      _ = 1 * ‖z‖ := (one_mul _).symm
  have hy : Orthonormal ℂ fun i : Fin ν =>
      (WithLp.toLp 2 ((0 : F), EuclideanSpace.basisFun (Fin ν) ℂ i) :
        WithLp 2 (F × EuclideanSpace ℂ (Fin ν))) := by
    have hb := (EuclideanSpace.basisFun (Fin ν) ℂ).orthonormal
    rw [orthonormal_iff_ite] at hb ⊢
    intro i j
    simpa using hb i j
  have hgauge : ∀ T : E →L[ℂ] F,
      kyFanApproximationGauge ν (ι ∘L T) = kyFanApproximationGauge ν T := fun T =>
    kyFanApproximationGauge_comp_eq_of_leftInverse hleft hιnorm hprnorm ν T
  constructor
  · rintro r ⟨v, -, rfl⟩
    exact equation1_12_gauge_comp_starProjection_le K ν _
  · intro b hb
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨u, v, hu, hv, hlow⟩ :=
      exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex (ι ∘L K) hε hx hy
    have hfix : ∀ i, (Submodule.span ℂ (Set.range v)).starProjection (v i) = v i := fun i =>
      Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span (Set.mem_range_self i))
    have hpair : (∑ i, ⟪u i,
          ((ι ∘L K) ∘L (Submodule.span ℂ (Set.range v)).starProjection) (v i)⟫_ℂ)
        = ∑ i, ⟪u i, (ι ∘L K) (v i)⟫_ℂ :=
      Finset.sum_congr rfl fun i _ => by
        simp only [ContinuousLinearMap.comp_apply, hfix i]
    have hle := DavisKahan.ExactSinTheta.re_sum_inner_map_le_kyFanApproximationGauge
      ((ι ∘L K) ∘L (Submodule.span ℂ (Set.range v)).starProjection) hu hv
    rw [hpair] at hle
    have hcomp : kyFanApproximationGauge ν
          ((ι ∘L K) ∘L (Submodule.span ℂ (Set.range v)).starProjection)
        = kyFanApproximationGauge ν
          (K ∘L (Submodule.span ℂ (Set.range v)).starProjection) := by
      rw [ContinuousLinearMap.comp_assoc]
      exact hgauge _
    rw [hcomp] at hle
    rw [hgauge K] at hlow
    have hub : kyFanApproximationGauge ν
        (K ∘L (Submodule.span ℂ (Set.range v)).starProjection) ≤ b := hb ⟨v, hv, rfl⟩
    linarith

/-- **Davis--Kahan 1970, equation (1.13), first form:**
`‖K‖_ν = sup_{Ω,Υ} ‖ΥKΩ‖_ν`, the supremum over pairs of `ν`-projectors, one on the domain and
one on the codomain.

A supremum, not a maximum; see the module docstring. -/
theorem equation1_13_compressions (K : E →L[ℂ] F) {ν : ℕ}
    (hE : ∃ x : Fin ν → E, Orthonormal ℂ x) (hF : ∃ y : Fin ν → F, Orthonormal ℂ y) :
    IsLUB
      {r : ℝ | ∃ (v : Fin ν → E) (u : Fin ν → F), Orthonormal ℂ v ∧ Orthonormal ℂ u ∧
        r = kyFanApproximationGauge ν
          ((Submodule.span ℂ (Set.range u)).starProjection ∘L K ∘L
            (Submodule.span ℂ (Set.range v)).starProjection)}
      (kyFanApproximationGauge ν K) := by
  obtain ⟨x, hx⟩ := hE
  obtain ⟨y, hy⟩ := hF
  constructor
  · rintro r ⟨v, u, -, -, rfl⟩
    exact equation1_13_gauge_starProjection_comp_le K ν _ _
  · intro b hb
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨u, v, hu, hv, hlow⟩ :=
      exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex K hε hx hy
    have hfix : ∀ i, (Submodule.span ℂ (Set.range v)).starProjection (v i) = v i := fun i =>
      Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span (Set.mem_range_self i))
    have hfixu : ∀ i, (Submodule.span ℂ (Set.range u)).starProjection (u i) = u i := fun i =>
      Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span (Set.mem_range_self i))
    have hpair : (∑ i, ⟪u i,
          ((Submodule.span ℂ (Set.range u)).starProjection ∘L K ∘L
            (Submodule.span ℂ (Set.range v)).starProjection) (v i)⟫_ℂ)
        = ∑ i, ⟪u i, K (v i)⟫_ℂ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ContinuousLinearMap.comp_apply, hfix i]
      rw [← Submodule.inner_starProjection_left_eq_right, hfixu i]
    have hle := DavisKahan.ExactSinTheta.re_sum_inner_map_le_kyFanApproximationGauge
      ((Submodule.span ℂ (Set.range u)).starProjection ∘L K ∘L
        (Submodule.span ℂ (Set.range v)).starProjection) hu hv
    rw [hpair] at hle
    have hub : kyFanApproximationGauge ν
        ((Submodule.span ℂ (Set.range u)).starProjection ∘L K ∘L
          (Submodule.span ℂ (Set.range v)).starProjection) ≤ b := hb ⟨v, u, hv, hu, rfl⟩
    linarith

/-- **Davis--Kahan 1970, equation (1.13), second form:**
`‖K‖_ν = sup Re ∑_{k<ν} y_k* K x_k`, the supremum over all orthonormal `ν`-tuples
`{x₁,…,x_ν}` in the domain and `{y₁,…,y_ν}` in the codomain.

This is the form the Appendix to Section 6 invokes (transcription line 2150) to produce its
`ν`-projector.  A supremum, not a maximum; see the module docstring.  The `≤` half is
`re_sum_inner_map_le_kyFanApproximationGauge`, which is `RCLike`-generic and free of any
dimension hypothesis; only the attaining half needs `ℂ` and the room hypotheses. -/
theorem equation1_13_reSum (K : E →L[ℂ] F) {ν : ℕ}
    (hE : ∃ x : Fin ν → E, Orthonormal ℂ x) (hF : ∃ y : Fin ν → F, Orthonormal ℂ y) :
    IsLUB
      {r : ℝ | ∃ (v : Fin ν → E) (u : Fin ν → F), Orthonormal ℂ v ∧ Orthonormal ℂ u ∧
        r = RCLike.re (∑ i, ⟪u i, K (v i)⟫_ℂ)}
      (kyFanApproximationGauge ν K) := by
  obtain ⟨x, hx⟩ := hE
  obtain ⟨y, hy⟩ := hF
  constructor
  · rintro r ⟨v, u, hv, hu, rfl⟩
    exact DavisKahan.ExactSinTheta.re_sum_inner_map_le_kyFanApproximationGauge
      K hu hv
  · intro b hb
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨u, v, hu, hv, hlow⟩ :=
      exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex K hε hx hy
    have hub : RCLike.re (∑ i, ⟪u i, K (v i)⟫_ℂ) ≤ b := hb ⟨v, u, hv, hu, rfl⟩
    linarith

end NuNorms

end DavisKahan1970
end TauCeti
