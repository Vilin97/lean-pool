/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.KyFan

/-!
# Approximation-number foundation and scalar-specific analytic endpoints

This lower module contains the approximation-number definitions, scalar-generic
algebraic laws, finite-dimensional Ky Fan bridge, and the accepted complex
strong-cutoff and infinite-dimensional Ky Fan arguments. It intentionally does
not import the real localization module, so the real proof can depend on this
foundation without creating an import cycle.

The downstream ideal-family construction is `ForTauCeti.Analysis.OperatorIdeal.Family`;
the paper library's own aggregate is `DavisKahan/OperatorIdeal/ApproximationNumbers/`,
which is a different library and is not what a reader of this module wants.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean`.
* Extraction class: **moved**, not restated.  Statements, proofs and namespace are
  unchanged by the move; what changed is the enclosing library, and with it the
  build options the file is measured against.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c)
  2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports are `ForTauCeti` leaves and Mathlib.
-/

public section

namespace TauCeti
namespace ApproximationNumber

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v vF vG vH vE0 vF0 w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Strong operator convergence expressed pointwise. -/
def StronglyTendsto {ι : Type w} (T : ι → E →L[𝕜] E)
    (l : Filter ι) (S : E →L[𝕜] E) : Prop :=
  ∀ x, Tendsto (fun i => T i x) l (𝓝 (S x))

/-- Orthogonal projection predicate for bounded operators. -/
def IsOrthogonalProjectionMap (P : E →L[𝕜] E) : Prop :=
  P ∘L P = P ∧ P.IsSymmetric

/-- Zero-based approximation singular value, defined as the operator-norm
 distance to maps of rank at most `n`. -/
noncomputable def approximationSingularValue
    (n : ℕ) (K : E →L[𝕜] F) : ℝ :=
  K.approximationNumber n

omit [CompleteSpace E] [CompleteSpace F] in
/-- Approximation singular values are nonnegative. -/
theorem approximationSingularValue_nonneg
    (n : ℕ) (K : E →L[𝕜] F) :
    0 ≤ approximationSingularValue n K := by
  exact_mod_cast K.approximationNumber_nonneg n

omit [CompleteSpace E] [CompleteSpace F] in
/-- Approximation singular values of the zero map vanish. -/
@[simp]
theorem approximationSingularValue_zero_map (n : ℕ) :
    approximationSingularValue n (0 : E →L[𝕜] F) = 0 := by
  exact (ContinuousLinearMap.approximationNumber_zero
      (𝕜 := 𝕜) (E := E) (F := F) n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The zero-based first approximation singular value is the operator norm. -/
@[simp]
theorem approximationSingularValue_zero
    (K : E →L[𝕜] F) :
    approximationSingularValue 0 K = ‖K‖ := by
  exact K.approximationNumber_index_zero

omit [CompleteSpace E] [CompleteSpace F] in
/-- Approximation singular values are absolutely homogeneous. -/
theorem approximationSingularValue_smul
    (n : ℕ) (c : 𝕜) (K : E →L[𝕜] F) :
    approximationSingularValue n (c • K) =
      ‖c‖ * approximationSingularValue n K := by
  exact (ContinuousLinearMap.approximationNumber_smul c K n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Approximation singular values are unchanged by negation. -/
@[simp]
theorem approximationSingularValue_neg
    (n : ℕ) (K : E →L[𝕜] F) :
    approximationSingularValue n (-K) = approximationSingularValue n K := by
  have h := approximationSingularValue_smul n (-1 : 𝕜) K
  simpa using h

omit [CompleteSpace E] [CompleteSpace F] in
/-- Approximation singular values decrease with the index. -/
theorem approximationSingularValue_antitone
    (K : E →L[𝕜] F) :
    Antitone (fun n => approximationSingularValue n K) := by
  intro n m hnm
  exact_mod_cast K.approximationNumber_antitone hnm

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every approximation singular value is controlled by operator norm. -/
theorem approximationSingularValue_le_opNorm
    (n : ℕ) (K : E →L[𝕜] F) :
    approximationSingularValue n K ≤ ‖K‖ := by
  exact_mod_cast K.approximationNumber_le_norm n

omit [CompleteSpace E] [CompleteSpace F] in
/-- Perturbation inequality at a fixed approximation index. -/
theorem approximationSingularValue_add_le
    (n : ℕ) (K L : E →L[𝕜] F) :
    approximationSingularValue n (K + L) ≤
      approximationSingularValue n K + ‖L‖ := by
  exact_mod_cast K.approximationNumber_add_le_add_norm L n

/-- Adjoint invariance of approximation singular values on Hilbert spaces. -/
theorem approximationSingularValue_adjoint
    (n : ℕ) (K : E →L[𝕜] F) :
    approximationSingularValue n K.adjoint =
      approximationSingularValue n K := by
  exact (K.approximationNumber_adjoint n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Ideal inequality for approximation singular values. -/
theorem approximationSingularValue_comp_le
    {G : Type vG} {H : Type vH}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (n : ℕ) (L : F →L[𝕜] G) (K : E →L[𝕜] F)
    (R : H →L[𝕜] E) :
    approximationSingularValue n (L ∘L K ∘L R)
      ≤ ‖L‖ * approximationSingularValue n K * ‖R‖ := by
  have h := ContinuousLinearMap.approximationNumber_comp_comp_le L K R n
  exact_mod_cast h

/-- On finite-dimensional Hilbert spaces, each singular value is bounded by
the corresponding approximation singular value. This is the real-valued
adapter for the lower Eckart--Young theorem. -/
theorem singularValues_le_approximationSingularValue
    {E₀ : Type vE0} {F₀ : Type vF0}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (A : E₀ →ₗ[𝕜] F₀) (n : ℕ) :
    A.singularValues n ≤
      approximationSingularValue n A.toContinuousLinearMap := by
  have h := ContinuousLinearMap.singularValues_le_approximationNumber
    A.toContinuousLinearMap n
  exact_mod_cast h

/-- On finite-dimensional Hilbert spaces, approximation singular values are
exactly the ordinary singular values. -/
theorem approximationSingularValue_eq_singularValues
    {E₀ : Type vE0} {F₀ : Type vF0}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (A : E₀ →ₗ[𝕜] F₀) (n : ℕ) :
    approximationSingularValue n A.toContinuousLinearMap =
      A.singularValues n := by
  have hNN : A.toContinuousLinearMap.approximationNumber n =
      A.singularValues n := by
    simpa only [← ContinuousLinearMap.toLinearMap_singularValues,
      LinearMap.coe_toContinuousLinearMap] using
      (ContinuousLinearMap.approximationNumber_eq_singularValues
        A.toContinuousLinearMap n)
  change (A.toContinuousLinearMap.approximationNumber n : ℝ) =
    A.singularValues n
  exact hNN

omit [CompleteSpace E] in
/-- An orthogonal projection does not increase vector norms. -/
theorem IsOrthogonalProjectionMap.norm_apply_le
    {P : E →L[𝕜] E} (hP : IsOrthogonalProjectionMap P) (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  have hPP : P (P x) = P x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) hP.1
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hPQ : P (x - P x) = 0 := by
    rw [map_sub, hPP, sub_self]
  have horth : ⟪P x, x - P x⟫_𝕜 = 0 := by
    calc
      ⟪P x, x - P x⟫_𝕜 = ⟪x, P (x - P x)⟫_𝕜 :=
        hP.2 x (x - P x)
      _ = 0 := by simp only [hPQ, inner_zero_right]
  have hpyth : ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (P x) (x - P x) horth
    rw [show P x + (x - P x) = x by abel] at h
    rw [sq, sq, sq]
    linarith
  nlinarith [sq_nonneg ‖x - P x‖, norm_nonneg (P x), norm_nonneg x]

omit [CompleteSpace E] in
/-- An orthogonal projection has operator norm at most one. -/
theorem IsOrthogonalProjectionMap.norm_le_one
    {P : E →L[𝕜] E} (hP : IsOrthogonalProjectionMap P) :
    ‖P‖ ≤ 1 := by
  apply P.opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using hP.norm_apply_le x

/-- **A finite-dimensional operator norm is controlled by the values on a basis.**  With
`e` the coordinate isomorphism of `b`, `‖T‖ ≤ ‖e‖ * ∑ⱼ ‖T (b j)‖`.

Extracted from `tendsto_opNorm_zero_of_finiteDimensional`, whose whole content is that
this bound tends to zero: the estimate is a statement about one operator and does not
mention the net, so keeping it inside the limit argument hid a reusable fact behind a
thirty-line `calc`. -/
private theorem opNorm_le_norm_equivFun_mul_sum_basis
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (b : Module.Basis (Module.Basis.ofVectorSpaceIndex 𝕜 V) 𝕜 V)
    (T : V →L[𝕜] G) :
    ‖T‖ ≤ ‖b.equivFunL.toContinuousLinearMap‖ * ∑ j, ‖T (b j)‖ := by
  set e := b.equivFunL.toContinuousLinearMap with he
  refine T.opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)) fun x => ?_
  calc
    ‖T x‖ = ‖T (∑ j, b.repr x j • b j)‖ := by rw [b.sum_repr]
    _ = ‖∑ j, b.repr x j • T (b j)‖ := by rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ j, ‖b.repr x j • T (b j)‖ := norm_sum_le _ _
    _ = ∑ j, ‖b.repr x j‖ * ‖T (b j)‖ :=
      Finset.sum_congr rfl fun j _ => norm_smul _ _
    _ ≤ ∑ j, (‖e‖ * ‖x‖) * ‖T (b j)‖ := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖b.repr x j‖ = ‖e x j‖ := by rfl
        _ ≤ ‖e x‖ := norm_le_pi_norm (e x) j
        _ ≤ ‖e‖ * ‖x‖ := e.le_opNorm x
    _ = (‖e‖ * ‖x‖) * ∑ j, ‖T (b j)‖ := by rw [Finset.mul_sum]
    _ = (‖e‖ * ∑ j, ‖T (b j)‖) * ‖x‖ := by ring

/-- On a finite-dimensional source, pointwise convergence of bounded linear
maps to zero upgrades to convergence in operator norm. -/
theorem tendsto_opNorm_zero_of_finiteDimensional
    {ι : Type w} {l : Filter ι}
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : ι → V →L[𝕜] G)
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 0)) :
    Tendsto (fun i => ‖T i‖) l (𝓝 0) := by
  let b := Module.Basis.ofVectorSpace 𝕜 V
  let e := b.equivFunL.toContinuousLinearMap
  let C : ι → ℝ := fun i =>
    ‖e‖ * ∑ j, ‖T i (b j)‖
  have hsum : Tendsto (fun i => ∑ j, ‖T i (b j)‖) l (𝓝 0) := by
    have hsum' := tendsto_finsetSum Finset.univ
      (fun j _ => (hT (b j)).norm)
    simpa only [norm_zero, Finset.sum_const_zero] using hsum'
  have hC : Tendsto C l (𝓝 0) := by
    simpa only [C, mul_zero] using tendsto_const_nhds.mul hsum
  have hbound : ∀ i, ‖T i‖ ≤ C i := fun i => opNorm_le_norm_equivFun_mul_sum_basis b (T i)
  exact squeeze_zero (fun i => norm_nonneg (T i)) hbound hC

section StrongCutoff

variable {E₀ : Type vE0} {F₀ : Type vF0}
  [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]

omit [CompleteSpace F₀] [CompleteSpace E₀] in
/-- **Post-composing with an orthogonal projection cannot raise an approximation number.**
A projection is a contraction, so this is the ideal inequality with `‖P‖ ≤ 1` discharged.

Extracted from the convergence theorem below, where it was the `hUpper` half: it is a
statement about one projection with no net in sight, and it is the half a reader can check
without reading the localization argument. -/
theorem approximationSingularValue_comp_le_of_isOrthogonalProjection
    {P : E₀ →L[𝕜] E₀} (hP : IsOrthogonalProjectionMap P) (n : ℕ) (K : E₀ →L[𝕜] F₀) :
    approximationSingularValue n (K ∘L P) ≤ approximationSingularValue n K := by
  have hnormNN : ‖P‖ ≤ (1 : ℝ) := by exact_mod_cast hP.norm_le_one
  have hNN : (K ∘L P).approximationNumber n ≤ K.approximationNumber n := by
    calc (K ∘L P).approximationNumber n ≤ K.approximationNumber n * ‖P‖ :=
          K.approximationNumber_comp_le_mul_norm P n
      _ ≤ K.approximationNumber n * 1 :=
          mul_le_mul_of_nonneg_left hnormNN (K.approximationNumber_nonneg n)
      _ = K.approximationNumber n := by rw [mul_one]
  exact_mod_cast hNN

omit [CompleteSpace F₀] [CompleteSpace E₀] in
/-- **Cutoff convergence.**  Along a net of orthogonal projections converging strongly to the
identity, every approximation number of `K ∘L P i` converges to the corresponding
approximation number of `K`.

Upper semicontinuity is free (`P i` is a contraction); the lower bound is where the
generalized Courant--Fischer localization enters, and it is the only step that depends on the
scalar field, so it is taken as the hypothesis
`ContinuousLinearMap.HasMinMaxLowerBound`. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_of_minMax
    (hlb : ContinuousLinearMap.HasMinMaxLowerBound 𝕜 E₀ F₀)
    {ι : Type w} {P : ι → E₀ →L[𝕜] E₀} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E₀))
    (n : ℕ) (K : E₀ →L[𝕜] F₀) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) := by
  -- Two halves, and they are not symmetric.  `hUpper` is the ideal inequality and is now a
  -- lemma of its own; `hLower` is the whole content: pick a coercive subspace `V` witnessing
  -- `r < aₙ(K)`, note `K ∘ P i` agrees with `K` on `V` in the limit because `V` is
  -- finite-dimensional (`tendsto_opNorm_zero_of_finiteDimensional`), and transport the
  -- coercivity.  The min--max hypothesis enters only in producing `V`.
  have hUpper : ∀ i,
      approximationSingularValue n (K ∘L P i) ≤ approximationSingularValue n K :=
    fun i => approximationSingularValue_comp_le_of_isOrthogonalProjection (hPproj i) n K
  have hLower : ∀ r : ℝ,
      r < approximationSingularValue n K →
      ∀ᶠ i in l, r < approximationSingularValue n (K ∘L P i) := by
    intro r hr
    by_cases hr0 : 0 ≤ r
    · obtain ⟨s, hrs, v, hv, hV⟩ := hlb K n hr0 hr
      let c : ℝ := (r + s) / 2
      have hrc : r < c := by dsimp only [c]; linarith
      have hcs : c < s := by dsimp only [c]; linarith
      have hc0 : 0 ≤ c := hr0.trans hrc.le
      let V : Submodule 𝕜 E₀ := Submodule.span 𝕜 (Set.range v)
      let b : Module.Basis (Fin (n + 1)) 𝕜 V := Module.Basis.span hv
      let : FiniteDimensional 𝕜 V := b.finiteDimensional_of_finite
      let D : ι → V →L[𝕜] F₀ := fun i =>
        (K ∘L P i ∘L V.subtypeL) - (K ∘L V.subtypeL)
      have hDpoint : ∀ x : V, Tendsto (fun i => D i x) l (𝓝 0) := by
        intro x
        have hKP : Tendsto (fun i => K (P i (V.subtypeL x))) l
            (𝓝 (K (V.subtypeL x))) :=
          (K.continuous.tendsto (V.subtypeL x)).comp (hP (V.subtypeL x))
        have hconst : Tendsto (fun _ : ι => K (V.subtypeL x)) l
            (𝓝 (K (V.subtypeL x))) := tendsto_const_nhds
        change Tendsto
          (fun i => K (P i (V.subtypeL x)) - K (V.subtypeL x))
          l (𝓝 0)
        simpa only [sub_self] using hKP.sub hconst
      have hDnorm : Tendsto (fun i => ‖D i‖) l (𝓝 0) :=
        tendsto_opNorm_zero_of_finiteDimensional D hDpoint
      have hsmall : ∀ᶠ i in l, ‖D i‖ < s - c :=
        hDnorm.eventually (Iio_mem_nhds (sub_pos.mpr hcs))
      filter_upwards [hsmall] with i hi
      have hcNN : c ≤ (K ∘L P i).approximationNumber n := by
        apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
          (K ∘L P i) n v hv
        intro x hxV hxNorm
        have hDx : ‖D i ⟨x, hxV⟩‖ ≤ ‖D i‖ := by
          have h := (D i).le_opNorm ⟨x, hxV⟩
          change ‖D i ⟨x, hxV⟩‖ ≤ ‖D i‖ * ‖x‖ at h
          rw [hxNorm, mul_one] at h
          exact h
        have hDapply : D i ⟨x, hxV⟩ = K (P i x) - K x := by
          rfl
        have htri : ‖K x‖ ≤ ‖K (P i x)‖ + ‖D i ⟨x, hxV⟩‖ := by
          rw [hDapply]
          have h := norm_sub_le (K (P i x)) (K (P i x) - K x)
          (convert h using 1; abel_nf)
        have hsx : s ≤ ‖K x‖ := by
          have := hV x hxV
          simpa only [hxNorm, mul_one] using this
        change c ≤ ‖K (P i x)‖
        linarith
      have hcReal : c ≤ approximationSingularValue n (K ∘L P i) := hcNN
      exact hrc.trans_le hcReal
    · have hrneg : r < 0 := lt_of_not_ge hr0
      filter_upwards [] with i
      exact hrneg.trans_le
        (approximationSingularValue_nonneg n (K ∘L P i))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlower := hLower
    (approximationSingularValue n K - ε) (by linarith)
  filter_upwards [hlower] with i hi
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · have := hUpper i
    linarith

/-- Cutoff convergence over `ℂ`. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_complex
    {E₀ : Type vE0} {F₀ : Type vF0}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    {ι : Type w} {P : ι → E₀ →L[ℂ] E₀} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℂ E₀))
    (n : ℕ) (K : E₀ →L[ℂ] F₀) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  approximationSingularValue_comp_strongProjection_tendsto_of_minMax
    ContinuousLinearMap.hasMinMaxLowerBound_complex hPproj hP n K

end StrongCutoff

/-- Finite Ky Fan gauge built from approximation singular values.

This is `ContinuousLinearMap.kyFanGauge` with the arguments in the paper's order; the
theory lives in `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean` and
every statement below delegates to it. -/
@[expose]
noncomputable def kyFanApproximationGauge
    (k : ℕ) (K : E →L[𝕜] F) : ℝ :=
  K.kyFanGauge k

omit [CompleteSpace E] [CompleteSpace F] in
/-- The approximation-number Ky Fan gauge agrees definitionally with the Ky Fan gauge. -/
theorem kyFanApproximationGauge_eq_kyFanGauge (k : ℕ) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k K = K.kyFanGauge k := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- Finite Ky Fan gauges are unchanged by negation. -/
@[simp]
theorem kyFanApproximationGauge_neg (k : ℕ) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k (-K) = kyFanApproximationGauge k K :=
  K.kyFanGauge_neg k

section KyFanStrongCutoff

variable {E₀ : Type vE0} {F₀ : Type vF0}
  [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]

omit [CompleteSpace F₀] [CompleteSpace E₀] in
/-- Finite Ky Fan approximation gauges converge under strong orthogonal cutoffs: the
termwise statement summed over `Finset.range k`. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    (hlb : ContinuousLinearMap.HasMinMaxLowerBound 𝕜 E₀ F₀)
    {ι : Type w} {P : ι → E₀ →L[𝕜] E₀} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E₀))
    (k : ℕ) (K : E₀ →L[𝕜] F₀) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  exact tendsto_finsetSum (Finset.range k)
    (fun n hn => approximationSingularValue_comp_strongProjection_tendsto_of_minMax
      hlb hPproj hP n K)

/-- Finite Ky Fan approximation gauges converge under complex strong
orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_complex
    {E₁ : Type vE0} {F₁ : Type vF0}
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {ι : Type w} {P : ι → E₁ →L[ℂ] E₁} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℂ E₁))
    (k : ℕ) (K : E₁ →L[ℂ] F₁) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) :=
  kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    ContinuousLinearMap.hasMinMaxLowerBound_complex hPproj hP k K

end KyFanStrongCutoff

/-- The rectangular Ky Fan sum is bounded by the approximation-number gauge. -/
theorem kyFanSum_le_kyFanApproximationGauge
    {E₀ : Type vE0} {F₀ : Type vF0}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (k : ℕ) (A : E₀ →ₗ[𝕜] F₀) :
    TauCeti.kyFanSum k A ≤
      kyFanApproximationGauge k A.toContinuousLinearMap :=
  (ContinuousLinearMap.kyFanSum_eq_kyFanGauge k A).le

/-- In finite dimensions the two agree: the rectangular Ky Fan sum *is* the
approximation-number gauge. -/
theorem kyFanSum_eq_kyFanApproximationGauge
    {E₀ : Type vE0} {F₀ : Type vF0}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (k : ℕ) (A : E₀ →ₗ[𝕜] F₀) :
    TauCeti.kyFanSum k A =
      kyFanApproximationGauge k A.toContinuousLinearMap :=
  ContinuousLinearMap.kyFanSum_eq_kyFanGauge k A

/-- Subadditivity of the Ky Fan gauge in finite dimensions. -/
theorem kyFanApproximationGauge_add_le_finiteDimensional
    {E₀ : Type vE0} {F₀ : Type vF0}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (k : ℕ) (A B : E₀ →ₗ[𝕜] F₀) :
    kyFanApproximationGauge k (A + B).toContinuousLinearMap ≤
      kyFanApproximationGauge k A.toContinuousLinearMap +
        kyFanApproximationGauge k B.toContinuousLinearMap :=
  ContinuousLinearMap.kyFanGauge_add_le_of_finiteDimensional k A B


section KyFanTriangle

variable {E₀ : Type vE0} {F₀ : Type vF0}
  [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]

omit [CompleteSpace E₀] [CompleteSpace F₀] in
/-- Approximation singular values are monotone in the restricted subspace: enlarging
the domain cannot decrease them. -/
theorem approximationSingularValue_restrict_mono
    (T : E₀ →L[𝕜] F₀) (n : ℕ) {U V : Submodule 𝕜 E₀}
    (hUV : U ≤ V) :
    approximationSingularValue n (T ∘L U.subtypeL) ≤
      approximationSingularValue n (T ∘L V.subtypeL) :=
  T.approximationNumber_restrict_mono n hUV

/-- Composing with the orthogonal projection onto the range leaves every approximation
singular value unchanged. -/
theorem approximationSingularValue_orthogonalProjectionOnto_comp_eq
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (W : Submodule 𝕜 G) [W.HasOrthogonalProjection]
    (A : V →L[𝕜] G) (hA : ∀ x, A x ∈ W) (n : ℕ) :
    approximationSingularValue n (W.orthogonalProjectionOnto ∘L A) =
      approximationSingularValue n A :=
  ContinuousLinearMap.approximationNumber_orthogonalProjectionOnto_comp_eq W A hA n

/-- Composing with the orthogonal projection onto the range leaves the Ky Fan gauge
unchanged. -/
theorem kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (W : Submodule 𝕜 G) [W.HasOrthogonalProjection]
    (A : V →L[𝕜] G) (hA : ∀ x, A x ∈ W) (k : ℕ) :
    kyFanApproximationGauge k (W.orthogonalProjectionOnto ∘L A) =
      kyFanApproximationGauge k A :=
  ContinuousLinearMap.kyFanGauge_orthogonalProjectionOnto_comp_eq W A hA k

/-- Subadditivity of the Ky Fan gauge for finite-source operators. -/
theorem kyFanApproximationGauge_add_le_finiteSource
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (k : ℕ) (A B : V →L[𝕜] G) :
    kyFanApproximationGauge k (A + B) ≤
      kyFanApproximationGauge k A + kyFanApproximationGauge k B :=
  ContinuousLinearMap.kyFanGauge_add_le_of_finiteDimensional_source k A B

omit [CompleteSpace E₀] [CompleteSpace F₀] in
/-- **The Ky Fan triangle inequality**, at whichever field supplies the min--max lower
bound.  The localization argument is `kyFanGauge_add_le_of_exists_finiteRestriction`; the
field enters only through `hlb`. -/
theorem kyFanApproximationGauge_add_le_of_minMax
    (hlb : ContinuousLinearMap.HasMinMaxLowerBound 𝕜 E₀ F₀)
    (k : ℕ) (K L : E₀ →L[𝕜] F₀) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L :=
  ContinuousLinearMap.kyFanGauge_add_le_of_exists_finiteRestriction
    (fun n ε hε => by
      by_cases hsmall : (K + L).approximationNumber n < ε
      · exact ⟨fun _ => 0, hsmall.trans_le
          (le_add_of_nonneg_left
            (ContinuousLinearMap.approximationNumber_nonneg _ n))⟩
      · obtain ⟨v, hv⟩ := hlb.exists_finiteRestrictionApproximationNumber_gt_of_lt (K + L) n
          (sub_nonneg.mpr (le_of_not_gt hsmall)) (sub_lt_self _ hε)
        exact ⟨v, by linarith⟩)
    k

end KyFanTriangle

section ComplexKyFanTriangle

variable {E₀ : Type vE0} {F₀ : Type vF0}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]

/-- Approximation numbers are approached from below by finite restrictions: for every
`ε > 0` some finitely-spanned restriction comes within `ε`. -/
theorem exists_finiteRestrictionApproximationNumber_add_gt
    (T : E₀ →L[ℂ] F₀) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Fin (n + 1) → E₀,
      T.approximationNumber n <
        (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n + ε :=
  T.exists_finiteRestrictionApproximationNumber_add_gt n ε hε

/-- Subadditivity of the Ky Fan gauge over `ℂ`. -/
theorem kyFanApproximationGauge_add_le_complex
    (k : ℕ) (K L : E₀ →L[ℂ] F₀) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L :=
  K.kyFanGauge_add_le_complex L k
end ComplexKyFanTriangle

omit [CompleteSpace E] [CompleteSpace F] in
/-- The zero-term Ky Fan gauge vanishes. -/
@[simp]
theorem kyFanApproximationGauge_zero :
    kyFanApproximationGauge 0 (0 : E →L[𝕜] F) = 0 :=
  (0 : E →L[𝕜] F).kyFanGauge_zero_index

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every finite Ky Fan gauge vanishes on the zero operator. -/
@[simp]
theorem kyFanApproximationGauge_zero_map (k : ℕ) :
    kyFanApproximationGauge k (0 : E →L[𝕜] F) = 0 :=
  ContinuousLinearMap.kyFanGauge_zero k

omit [CompleteSpace E] [CompleteSpace F] in
/-- The first positive Ky Fan gauge is operator norm. -/
@[simp]
theorem kyFanApproximationGauge_one (K : E →L[𝕜] F) :
    kyFanApproximationGauge 1 K = ‖K‖ :=
  K.kyFanGauge_one

omit [CompleteSpace E] [CompleteSpace F] in
/-- Ky Fan approximation gauges are absolutely homogeneous. -/
theorem kyFanApproximationGauge_smul
    (k : ℕ) (c : 𝕜) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k (c • K) =
      ‖c‖ * kyFanApproximationGauge k K :=
  ContinuousLinearMap.kyFanGauge_smul c K k

omit [CompleteSpace E] [CompleteSpace F] in
/-- Ky Fan approximation gauges are nonnegative. -/
theorem kyFanApproximationGauge_nonneg
    (k : ℕ) (K : E →L[𝕜] F) :
    0 ≤ kyFanApproximationGauge k K :=
  K.kyFanGauge_nonneg k

/-- Ky Fan approximation gauges are invariant under adjoint. -/
theorem kyFanApproximationGauge_adjoint
    (k : ℕ) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k K.adjoint =
      kyFanApproximationGauge k K :=
  K.kyFanGauge_adjoint k

omit [CompleteSpace E] [CompleteSpace F] in
/-- Two-sided ideal inequality for finite Ky Fan gauges. -/
theorem kyFanApproximationGauge_comp_le
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (k : ℕ) (L : F →L[𝕜] G) (K : E →L[𝕜] F)
    (R : H →L[𝕜] E) :
    kyFanApproximationGauge k (L ∘L K ∘L R) ≤
      ‖L‖ * kyFanApproximationGauge k K * ‖R‖ :=
  ContinuousLinearMap.kyFanGauge_comp_le L K R k

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Enlarging the codomain leaves the finite Ky Fan gauge unchanged**, for a contraction
`ι : F →L[𝕜] G` admitting a contractive left inverse `π`.  This is what lets an argument
that needs `k` orthonormal vectors in the codomain run even when `F` has too few: pad `F`
to `G`, run the argument there, and read the answer back.  See
`ContinuousLinearMap.kyFanGauge_comp_eq_of_leftInverse`. -/
theorem kyFanApproximationGauge_comp_eq_of_leftInverse
    {G : Type vG}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι : F →L[𝕜] G} {π : G →L[𝕜] F} (hπι : Function.LeftInverse π ι)
    (hι : ‖ι‖ ≤ 1) (hπ : ‖π‖ ≤ 1) (k : ℕ) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k (ι ∘L K) = kyFanApproximationGauge k K :=
  ContinuousLinearMap.kyFanGauge_comp_eq_of_leftInverse hπι hι hπ K k

omit [CompleteSpace E] [CompleteSpace F] in
/-- The operator norm is the first term of every positive finite Ky Fan gauge. -/
theorem opNorm_le_kyFanApproximationGauge
    {k : ℕ} (hk : 0 < k) (K : E →L[𝕜] F) :
    ‖K‖ ≤ kyFanApproximationGauge k K :=
  K.opNorm_le_kyFanGauge hk

omit [CompleteSpace E] [CompleteSpace F] in
/-- A finite Ky Fan gauge is bounded by `k` times operator norm. -/
theorem kyFanApproximationGauge_le_nat_mul_opNorm
    (k : ℕ) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k K ≤ (k : ℝ) * ‖K‖ :=
  K.kyFanGauge_le_nat_mul_opNorm k

omit [CompleteSpace E] in
/-- **The Ky Fan gauge is approached by orthonormal pairings.**

For a bounded `K : E →L[𝕜] F` and any `ε > 0` there are orthonormal `k`-families `v` in `E`
and `u` in `F` with `kyFanApproximationGauge k K - ε ≤ re ∑ᵢ ⟪uᵢ, K vᵢ⟫`.  Together with the
reverse inequality this says the gauge is the *supremum* of those pairings.

Only the approximate form is available at this generality, and that is not a defect of the
proof: for a noncompact `K` the supremum need not be attained.  With `K` diagonal with
entries `1 - 1/n` on an orthonormal basis every approximation number equals `1`, so the gauge
is `k`, while `‖K x‖ < ‖x‖` for every `x ≠ 0` makes each pairing strictly smaller.

The two orthonormal families `x` and `y` are hypotheses, not conclusions: they say only that
`E` and `F` have room for `k` orthonormal vectors, without which no such `u`, `v` can exist.

The min--max lower bound `hlb` is what turns the ambient approximation numbers into
approximation numbers of a *finite-dimensional* restriction; the finite-dimensional
rectangular Ky Fan principle
`exists_orthonormal_re_sum_inner_map_eq_kyFanSum` then attains them exactly, and
the compression is transported back along the inclusion and the projection, which are
isometric on the vectors involved. -/
theorem exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner
    (hlb : ContinuousLinearMap.HasMinMaxLowerBound 𝕜 E F)
    (K : E →L[𝕜] F) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Fin k → E} (hx : Orthonormal 𝕜 x)
    {y : Fin k → F} (hy : Orthonormal 𝕜 y) :
    ∃ (u : Fin k → F) (v : Fin k → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      kyFanApproximationGauge k K - ε ≤ RCLike.re (∑ i, ⟪u i, K (v i)⟫_𝕜) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact ⟨y, x, hy, hx, by simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge,
      hε.le]⟩
  set δ : ℝ := ε / k with hδdef
  have hδ : 0 < δ := div_pos hε (by exact_mod_cast hkpos)
  -- a finite set of vectors whose span nearly attains the `n`-th approximation number
  have hstep : ∀ n : ℕ, ∃ S : Finset E,
      K.approximationNumber n
        < (K ∘L (Submodule.span 𝕜 (S : Set E)).subtypeL).approximationNumber n + δ := by
    intro n
    obtain ⟨w, hw⟩ := hlb.exists_finiteRestrictionApproximationNumber_add_gt K n δ hδ
    refine ⟨Finset.image w Finset.univ, ?_⟩
    have hrange : ((Finset.image w Finset.univ : Finset E) : Set E) = Set.range w := by
      simp
    rw [hrange]
    exact hw
  choose S hS using hstep
  -- the finite-dimensional domain restriction
  set T : Finset E := (Finset.range k).biUnion S ∪ Finset.image x Finset.univ with hTdef
  set W : Submodule 𝕜 E := Submodule.span 𝕜 (T : Set E) with hWdef
  have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 T.finite_toSet
  have : CompleteSpace W := FiniteDimensional.complete 𝕜 W
  have hSW : ∀ n < k, Submodule.span 𝕜 ((S n : Set E)) ≤ W := by
    intro n hn
    refine Submodule.span_mono (Finset.coe_subset.mpr ?_)
    exact (Finset.subset_biUnion_of_mem S (Finset.mem_range.mpr hn)).trans
      Finset.subset_union_left
  have hgaugeW : kyFanApproximationGauge k K - ε
      ≤ kyFanApproximationGauge k (K ∘L W.subtypeL) := by
    have hterm : ∀ n ∈ Finset.range k,
        K.approximationNumber n
          < (K ∘L W.subtypeL).approximationNumber n + δ := by
      intro n hn
      have hmono := ContinuousLinearMap.approximationNumber_restrict_mono K n
        (hSW n (Finset.mem_range.mp hn))
      have hn' := hS n
      linarith
    have hsum : ∑ n ∈ Finset.range k, K.approximationNumber n
        ≤ (∑ n ∈ Finset.range k, (K ∘L W.subtypeL).approximationNumber n)
          + (k : ℝ) * δ := by
      have := Finset.sum_le_sum (fun n hn => (hterm n hn).le)
      simpa [Finset.sum_add_distrib, mul_comm] using this
    have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
    have hkδ : (k : ℝ) * δ = ε := by
      rw [hδdef]
      field_simp
    simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
    rw [hkδ] at hsum
    linarith
  -- both restrictions have room for `k` orthonormal vectors
  have hxW : ∀ i, x i ∈ W := fun i => Submodule.subset_span (by simp [hTdef])
  have hx' : Orthonormal 𝕜 (fun i => (⟨x i, hxW i⟩ : W)) := by
    rw [orthonormal_iff_ite] at hx ⊢
    intro i j
    simpa [Submodule.coe_inner] using hx i j
  have hkW : k ≤ Module.finrank 𝕜 W := by
    simpa using hx'.linearIndependent.fintype_card_le_finrank
  set T' : Finset F := (T.image K) ∪ Finset.image y Finset.univ with hT'def
  set W' : Submodule 𝕜 F := Submodule.span 𝕜 (T' : Set F) with hW'def
  have : FiniteDimensional 𝕜 W' := FiniteDimensional.span_of_finite 𝕜 T'.finite_toSet
  have : CompleteSpace W' := FiniteDimensional.complete 𝕜 W'
  have hyW' : ∀ i, y i ∈ W' := fun i => Submodule.subset_span (by simp [hT'def])
  have hy' : Orthonormal 𝕜 (fun i => (⟨y i, hyW' i⟩ : W')) := by
    rw [orthonormal_iff_ite] at hy ⊢
    intro i j
    simpa [Submodule.coe_inner] using hy i j
  have hkW' : k ≤ Module.finrank 𝕜 W' := by
    simpa using hy'.linearIndependent.fintype_card_le_finrank
  have hKW : ∀ z : W, K (z : E) ∈ W' := by
    intro z
    have hle : W ≤ Submodule.comap (K : E →ₗ[𝕜] F) W' := by
      rw [hWdef]
      refine Submodule.span_le.mpr fun t ht => Submodule.subset_span ?_
      simp only [hT'def, Finset.coe_union, Set.mem_union, Finset.coe_image]
      exact Or.inl ⟨t, ht, rfl⟩
    exact hle z.2
  set K' : W →L[𝕜] W' := W'.orthogonalProjectionOnto ∘L (K ∘L W.subtypeL) with hK'def
  have hgaugeK' : kyFanApproximationGauge k K'
      = kyFanApproximationGauge k (K ∘L W.subtypeL) :=
    kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq W' (K ∘L W.subtypeL) hKW k
  obtain ⟨u', v', hu', hv', heq⟩ :=
    TauCeti.exists_orthonormal_re_sum_inner_map_eq_kyFanSum
      K'.toLinearMap hkW hkW'
  have hbridge : TauCeti.kyFanSum k K'.toLinearMap
      = kyFanApproximationGauge k K' :=
    kyFanSum_eq_kyFanApproximationGauge k K'.toLinearMap
  refine ⟨fun i => (u' i : F), fun i => (v' i : E), ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite] at hu' ⊢
    intro i j
    simpa [Submodule.coe_inner] using hu' i j
  · rw [orthonormal_iff_ite] at hv' ⊢
    intro i j
    simpa [Submodule.coe_inner] using hv' i j
  · have hpair : ∀ i, ⟪u' i, K'.toLinearMap (v' i)⟫_𝕜
        = ⟪((u' i : F)), K ((v' i : E))⟫_𝕜 := by
      intro i
      have hval : ((K'.toLinearMap (v' i) : W') : F) = W'.starProjection (K ((v' i : E))) := rfl
      rw [Submodule.coe_inner, hval, ← W'.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr (u' i).2]
    have hsum : (∑ i, ⟪((u' i : F)), K ((v' i : E))⟫_𝕜)
        = ∑ i, ⟪u' i, K'.toLinearMap (v' i)⟫_𝕜 :=
      Finset.sum_congr rfl fun i _ => (hpair i).symm
    rw [hsum, heq, hbridge, hgaugeK']
    exact hgaugeW

/-- **The Ky Fan gauge is approached by orthonormal pairings**, over `ℂ`.

The min--max lower bound is discharged by `hasMinMaxLowerBound_complex`, so no hypothesis on
the scalar field remains. -/
theorem exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex
    {E₂ : Type vE0} {F₂ : Type vF0}
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (K : E₂ →L[ℂ] F₂) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Fin k → E₂} (hx : Orthonormal ℂ x)
    {y : Fin k → F₂} (hy : Orthonormal ℂ y) :
    ∃ (u : Fin k → F₂) (v : Fin k → E₂), Orthonormal ℂ u ∧ Orthonormal ℂ v ∧
      kyFanApproximationGauge k K - ε ≤ RCLike.re (∑ i, ⟪u i, K (v i)⟫_ℂ) :=
  exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner
    ContinuousLinearMap.hasMinMaxLowerBound_complex K hε hx hy

end ApproximationNumber
end TauCeti
