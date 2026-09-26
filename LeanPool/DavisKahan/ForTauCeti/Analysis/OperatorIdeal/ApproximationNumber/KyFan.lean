/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.KyFan
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction

/-!
# Ky Fan gauges of approximation numbers

The `k`th **Ky Fan gauge** of a bounded operator is the sum of its first `k` approximation
numbers,

```
T.kyFanGauge k = ∑ n ∈ Finset.range k, T.approximationNumber n,
```

so `kyFanGauge 1` is the operator norm and the gauges increase to the nuclear norm.  Each is
a norm on the two-sided ideal it defines, and the family of them determines every
unitarily invariant norm — which is why the Ky Fan gauges, not the individual approximation
numbers, are what an operator-ideal theory is built from.

## The triangle inequality

Everything else here is a one-line consequence of the corresponding statement about
approximation numbers.  The exception, and the reason this module exists, is

```
(S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k,
```

which is *false* term by term — `aₙ` is not subadditive — and is proved in three steps:

1. in finite dimensions it is the Ky Fan norm inequality of
   `ForTauCeti/Analysis/InnerProductSpace/KyFan`, transported
   along `ContinuousLinearMap.approximationNumber_eq_singularValues`;
2. for a finite-dimensional *source* and arbitrary codomain, compress the codomain to the
   (finite-dimensional) range of `S ⊕ T`, which changes no approximation number;
3. in general, localize: `aₙ(S + T)` is approached by the restrictions of `S + T` to
   `(n+1)`-generated subspaces
   (`ContinuousLinearMap.exists_finiteRestrictionApproximationNumber_gt_of_lt`), and `k`
   of those subspaces can be spanned together into a single finite-dimensional `V` on
   which step 2 applies.

Step 3 is where this used to depend on `vendor/Spectra`: the localization statement was
proved there from projection-valued measures.  It is now
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`, so the whole
chain is Mathlib-only.  Steps 2 and 3 are stated over `ℂ` because that is where the
min--max theorem lives.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.ExactSinTheta.{`
  `kyFanApproximationGauge, kyFanApproximationGauge_neg, kyFanApproximationGauge_zero,`
  `kyFanApproximationGauge_zero_map, kyFanApproximationGauge_one,`
  `kyFanApproximationGauge_smul, kyFanApproximationGauge_nonneg,`
  `kyFanApproximationGauge_adjoint, kyFanApproximationGauge_comp_le,`
  `opNorm_le_kyFanApproximationGauge, kyFanApproximationGauge_le_nat_mul_opNorm,`
  `kyFanSum_le_kyFanApproximationGauge,`
  `kyFanSum_eq_kyFanApproximationGauge,`
  `kyFanApproximationGauge_add_le_finiteDimensional,`
  `approximationSingularValue_restrict_mono,`
  `approximationSingularValue_orthogonalProjectionOnto_comp_eq,`
  `kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq,`
  `kyFanApproximationGauge_add_le_finiteSource,`
  `exists_finiteRestrictionApproximationNumber_add_gt,`
  `kyFanApproximationGauge_add_le_complex}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and renamespaced**.  The gauge moves to
  `ContinuousLinearMap.kyFanGauge` with the operator first so dot notation resolves, and
  `approximationSingularValue n K` is spelled `K.approximationNumber n` throughout — it was
  only ever an alias for it.  No proof was changed except for those renamings.
* Spectra influence: **none**, as of the replacement of the min--max bridge on 2026-07-28.
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

noncomputable section

universe u v w x y

variable {𝕜 : Type u} [RCLike 𝕜]

section Basic

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The `k`th **Ky Fan gauge**: the sum of the first `k` approximation numbers. -/
@[expose]
def kyFanGauge (T : E →L[𝕜] F) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range k, T.approximationNumber n

/-- Approximation numbers are unchanged by negation.  Mathlib's staging layer has
`approximationNumber_smul` but not this special case. -/
@[simp] theorem approximationNumber_neg (T : E →L[𝕜] F) (n : ℕ) :
    (-T).approximationNumber n = T.approximationNumber n := by
  rw [← neg_one_smul 𝕜 T, approximationNumber_smul]
  simp

/-- Ky Fan gauges are unchanged by negation. -/
@[simp] theorem kyFanGauge_neg (T : E →L[𝕜] F) (k : ℕ) :
    (-T).kyFanGauge k = T.kyFanGauge k :=
  Finset.sum_congr rfl fun n _ => T.approximationNumber_neg n

/-- The zeroth Ky Fan gauge is the empty sum, hence zero. -/
@[simp] theorem kyFanGauge_zero_index (T : E →L[𝕜] F) : T.kyFanGauge 0 = 0 := by
  simp [kyFanGauge]

/-- The zero operator has zero Ky Fan gauge at every index. -/
@[simp] theorem kyFanGauge_zero (k : ℕ) : (0 : E →L[𝕜] F).kyFanGauge k = 0 := by
  simp [kyFanGauge]

/-- The first Ky Fan gauge is the operator norm. -/
@[simp] theorem kyFanGauge_one (T : E →L[𝕜] F) : T.kyFanGauge 1 = ‖T‖ := by
  simp [kyFanGauge]

/-- Ky Fan gauges are absolutely homogeneous. -/
theorem kyFanGauge_smul (c : 𝕜) (T : E →L[𝕜] F) (k : ℕ) :
    (c • T).kyFanGauge k = ‖c‖ * T.kyFanGauge k := by
  simp only [kyFanGauge, approximationNumber_smul]
  rw [Finset.mul_sum]

/-- Ky Fan gauges are nonnegative. -/
theorem kyFanGauge_nonneg (T : E →L[𝕜] F) (k : ℕ) : 0 ≤ T.kyFanGauge k :=
  Finset.sum_nonneg fun n _ => T.approximationNumber_nonneg n

/-- **The two-sided ideal inequality.** -/
theorem kyFanGauge_comp_le {G : Type x} {H : Type y}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] 
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] 
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) (k : ℕ) :
    (L ∘L T ∘L R).kyFanGauge k ≤ ‖L‖ * T.kyFanGauge k * ‖R‖ := by
  calc
    (L ∘L T ∘L R).kyFanGauge k
        ≤ ∑ n ∈ Finset.range k, (‖L‖ * T.approximationNumber n * ‖R‖) :=
      Finset.sum_le_sum fun n _ => approximationNumber_comp_comp_le L T R n
    _ = ‖L‖ * T.kyFanGauge k * ‖R‖ := by
      simp only [kyFanGauge, Finset.mul_sum, Finset.sum_mul]

/-- **Ky Fan gauges do not see an enlargement of the codomain**, since the approximation
numbers do not: `ι` is a contraction of `F` into `G` and `π` a contractive left inverse,
the model being the inclusion of `F` as one summand of an `ℓ²` direct sum together with
the projection back onto it.  See
`ContinuousLinearMap.approximationNumber_comp_eq_of_leftInverse`. -/
theorem kyFanGauge_comp_eq_of_leftInverse {G : Type x}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι : F →L[𝕜] G} {π : G →L[𝕜] F} (hπι : Function.LeftInverse π ι)
    (hι : ‖ι‖ ≤ 1) (hπ : ‖π‖ ≤ 1) (T : E →L[𝕜] F) (k : ℕ) :
    (ι ∘L T).kyFanGauge k = T.kyFanGauge k :=
  Finset.sum_congr rfl fun n _ =>
    approximationNumber_comp_eq_of_leftInverse hπι hι hπ T n

/-- The operator norm is the first term of every positive Ky Fan gauge. -/
theorem opNorm_le_kyFanGauge (T : E →L[𝕜] F) {k : ℕ} (hk : 0 < k) :
    ‖T‖ ≤ T.kyFanGauge k := by
  rw [← T.approximationNumber_index_zero]
  exact Finset.single_le_sum (fun n _ => T.approximationNumber_nonneg n)
    (Finset.mem_range.mpr hk)

/-- Every Ky Fan gauge is bounded by `k` times the operator norm, so the ideal it defines
contains every bounded operator when `k` is finite. -/
theorem kyFanGauge_le_nat_mul_opNorm (T : E →L[𝕜] F) (k : ℕ) :
    T.kyFanGauge k ≤ (k : ℝ) * ‖T‖ := by
  calc
    T.kyFanGauge k ≤ ∑ _n ∈ Finset.range k, ‖T‖ :=
      Finset.sum_le_sum fun n _ => T.approximationNumber_le_norm n
    _ = (k : ℝ) * ‖T‖ := by simp

end Basic

section Adjoint

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Ky Fan gauges are adjoint-invariant, since the approximation numbers are. -/
theorem kyFanGauge_adjoint (T : E →L[𝕜] F) (k : ℕ) :
    T.adjoint.kyFanGauge k = T.kyFanGauge k := by
  simp only [kyFanGauge, approximationNumber_adjoint]

end Adjoint

section FiniteDimensional

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- In finite dimensions the Ky Fan gauge is the rectangular Ky Fan singular-value sum. -/
theorem kyFanSum_eq_kyFanGauge (k : ℕ) (A : E →ₗ[𝕜] F) :
    TauCeti.kyFanSum k A =
      A.toContinuousLinearMap.kyFanGauge k := by
  unfold TauCeti.kyFanSum
    kyFanGauge
  rw [Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun n _ =>
    (A.toContinuousLinearMap.approximationNumber_eq_singularValues n).symm

/-- **Step 1 of the triangle inequality**: the finite-dimensional case, transported from the
rectangular Ky Fan norm. -/
theorem kyFanGauge_add_le_of_finiteDimensional (k : ℕ) (A B : E →ₗ[𝕜] F) :
    (A + B).toContinuousLinearMap.kyFanGauge k ≤
      A.toContinuousLinearMap.kyFanGauge k + B.toContinuousLinearMap.kyFanGauge k := by
  rw [← kyFanSum_eq_kyFanGauge k (A + B),
    ← kyFanSum_eq_kyFanGauge k A, ← kyFanSum_eq_kyFanGauge k B]
  exact TauCeti.kyFanSum_add_le k A B

end FiniteDimensional

section Compression

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
-- Neither space needs to be complete: completeness is what `HasMinMaxLowerBound` is proved
-- from, not what the passage from it to the triangle inequality uses.
omit [CompleteSpace E] [CompleteSpace F] in
/-- Restricting to a larger source subspace can only increase an approximation number. -/
theorem approximationNumber_restrict_mono (T : E →L[𝕜] F) (n : ℕ) {U V : Submodule 𝕜 E}
    (hUV : U ≤ V) :
    (T ∘L U.subtypeL).approximationNumber n ≤ (T ∘L V.subtypeL).approximationNumber n := by
  let J : U →L[𝕜] V :=
    (Submodule.inclusion hUV).mkContinuous 1 fun x => by
      -- names the application so the norm bound applies to it directly.
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp
  have hJnorm : ‖J‖ ≤ (1 : ℝ) :=
    J.opNorm_le_bound zero_le_one fun x => by
      -- names the application so the norm bound applies to it directly.
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp
  have hcomp : T ∘L U.subtypeL = (T ∘L V.subtypeL) ∘L J := by
    ext x
    rfl
  rw [hcomp]
  calc
    ((T ∘L V.subtypeL) ∘L J).approximationNumber n
        ≤ (T ∘L V.subtypeL).approximationNumber n * ‖J‖ :=
      (T ∘L V.subtypeL).approximationNumber_comp_le_mul_norm J n
    _ ≤ (T ∘L V.subtypeL).approximationNumber n * 1 :=
      mul_le_mul_of_nonneg_left hJnorm (ContinuousLinearMap.approximationNumber_nonneg _ _)
    _ = (T ∘L V.subtypeL).approximationNumber n := by rw [mul_one]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Compressing the codomain to a subspace that already contains the range preserves every
approximation number. -/
theorem approximationNumber_orthogonalProjectionOnto_comp_eq
    (W : Submodule 𝕜 F) [W.HasOrthogonalProjection]
    (A : E →L[𝕜] F) (hA : ∀ x, A x ∈ W) (n : ℕ) :
    (W.orthogonalProjectionOnto ∘L A).approximationNumber n = A.approximationNumber n := by
  set AW : E →L[𝕜] W := W.orthogonalProjectionOnto ∘L A with hAW
  have hfactor : W.subtypeL ∘L AW = A := by
    ext x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change W.starProjection (A x) = A x
    exact W.starProjection_eq_self_iff.mpr (hA x)
  have hproj : ‖W.orthogonalProjectionOnto‖ ≤ (1 : ℝ) := W.orthogonalProjectionOnto_norm_le
  have hsub : ‖W.subtypeL‖ ≤ (1 : ℝ) := W.norm_subtypeL_le
  refine le_antisymm ?_ ?_
  · calc
      AW.approximationNumber n
          ≤ ‖W.orthogonalProjectionOnto‖ * A.approximationNumber n :=
        ContinuousLinearMap.approximationNumber_comp_le_norm_mul
          W.orthogonalProjectionOnto A n
      _ ≤ 1 * A.approximationNumber n :=
        mul_le_mul_of_nonneg_right hproj (ContinuousLinearMap.approximationNumber_nonneg _ _)
      _ = A.approximationNumber n := by rw [one_mul]
  · rw [← hfactor]
    calc
      (W.subtypeL ∘L AW).approximationNumber n
          ≤ ‖W.subtypeL‖ * AW.approximationNumber n :=
        ContinuousLinearMap.approximationNumber_comp_le_norm_mul W.subtypeL AW n
      _ ≤ 1 * AW.approximationNumber n :=
        mul_le_mul_of_nonneg_right hsub (ContinuousLinearMap.approximationNumber_nonneg _ _)
      _ = AW.approximationNumber n := by rw [one_mul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Ky Fan form of `approximationNumber_orthogonalProjectionOnto_comp_eq`. -/
theorem kyFanGauge_orthogonalProjectionOnto_comp_eq
    (W : Submodule 𝕜 F) [W.HasOrthogonalProjection]
    (A : E →L[𝕜] F) (hA : ∀ x, A x ∈ W) (k : ℕ) :
    (W.orthogonalProjectionOnto ∘L A).kyFanGauge k = A.kyFanGauge k :=
  Finset.sum_congr rfl fun n _ =>
    approximationNumber_orthogonalProjectionOnto_comp_eq W A hA n

end Compression

section FiniteSource

variable {V : Type v} {G : Type w}
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- **Step 2 of the triangle inequality**: a finite-dimensional source and an arbitrary
Hilbert codomain.  The codomain is compressed onto the range of `A ⊕ B`, which is
finite-dimensional and changes no approximation number. -/
theorem kyFanGauge_add_le_of_finiteDimensional_source (k : ℕ) (A B : V →L[𝕜] G) :
    (A + B).kyFanGauge k ≤ A.kyFanGauge k + B.kyFanGauge k := by
  let : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  let C : V × V →L[𝕜] G :=
    A ∘L ContinuousLinearMap.fst 𝕜 V V + B ∘L ContinuousLinearMap.snd 𝕜 V V
  let W : Submodule 𝕜 G := C.range
  let : FiniteDimensional 𝕜 W := by
    apply FiniteDimensional.of_surjective C.rangeRestrict.toLinearMap
    intro y
    rcases y.property with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let : CompleteSpace W := FiniteDimensional.complete 𝕜 W
  let : W.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W
  have hA : ∀ x, A x ∈ W := fun x => ⟨(x, 0), by simp [C]⟩
  have hB : ∀ x, B x ∈ W := fun x => ⟨(0, x), by simp [C]⟩
  have hAB : ∀ x, (A + B) x ∈ W := fun x => W.add_mem (hA x) (hB x)
  let AW : V →L[𝕜] W := W.orthogonalProjectionOnto ∘L A
  let BW : V →L[𝕜] W := W.orthogonalProjectionOnto ∘L B
  have hsum : W.orthogonalProjectionOnto ∘L (A + B) = AW + BW := by
    ext x
    simp [AW, BW]
  have hAWcont : AW.toLinearMap.toContinuousLinearMap = AW := by ext x; rfl
  have hBWcont : BW.toLinearMap.toContinuousLinearMap = BW := by ext x; rfl
  have hsumcont : (AW.toLinearMap + BW.toLinearMap).toContinuousLinearMap = AW + BW := by
    ext x
    rfl
  have htri := kyFanGauge_add_le_of_finiteDimensional (𝕜 := 𝕜) k AW.toLinearMap BW.toLinearMap
  rw [hsumcont, hAWcont, hBWcont] at htri
  calc
    (A + B).kyFanGauge k
        = (W.orthogonalProjectionOnto ∘L (A + B)).kyFanGauge k :=
      (kyFanGauge_orthogonalProjectionOnto_comp_eq W (A + B) hAB k).symm
    _ = (AW + BW).kyFanGauge k := by rw [hsum]
    _ ≤ AW.kyFanGauge k + BW.kyFanGauge k := htri
    _ = A.kyFanGauge k + B.kyFanGauge k := by
      rw [kyFanGauge_orthogonalProjectionOnto_comp_eq W A hA k,
        kyFanGauge_orthogonalProjectionOnto_comp_eq W B hB k]

end FiniteSource

section Localization

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Step 3 of the triangle inequality, and the only step that is not field-generic —
so it takes the field-dependent input as a hypothesis.**

Given that every approximation number of `S + T` is approached by its restrictions to
finite-dimensional subspaces of the source, the Ky Fan triangle inequality for `S` and `T`
follows: span the finitely many near-optimal vectors, restrict there, apply the
finite-dimensional-source case, and let the tolerance go to zero.

Nothing else in the argument sees the scalars.  Over `ℂ` the hypothesis is
`exists_finiteRestrictionApproximationNumber_add_gt`, a corollary of the min-max theorem;
over `ℝ`, where Mathlib's continuous functional calculus is not available for operators on
the space itself, it is proved by complexification.  Stating the step this way is what keeps
the two fields from needing two copies of the argument. -/
theorem kyFanGauge_add_le_of_exists_finiteRestriction {S T : E →L[𝕜] F}
    (hfr : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ v : Fin (n + 1) → E,
      (S + T).approximationNumber n <
        ((S + T) ∘L (Submodule.span 𝕜 (Set.range v)).subtypeL).approximationNumber n + ε)
    (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp
  apply le_of_forall_pos_le_add
  intro ε hε
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hδ : 0 < ε / (k : ℝ) := div_pos hε hkreal
  choose v hv using fun n => hfr n (ε / (k : ℝ)) hδ
  let β : Type := Σ n : Fin k, Fin (n.1 + 1)
  let w : β → E := fun p => v p.1.1 p.2
  let V : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range w)
  let : FiniteDimensional 𝕜 V := Module.Finite.span_of_finite 𝕜 (Set.finite_range w)
  let : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  let SV : V →L[𝕜] F := S ∘L V.subtypeL
  let TV : V →L[𝕜] F := T ∘L V.subtypeL
  have hsumRestrict : (S + T) ∘L V.subtypeL = SV + TV := by
    ext x
    rfl
  have hterm : ∀ n ∈ Finset.range k,
      (S + T).approximationNumber n ≤ (SV + TV).approximationNumber n + ε / (k : ℝ) := by
    intro n hn
    let U : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range (v n))
    have hUV : U ≤ V := by
      refine Submodule.span_le.mpr ?_
      rintro x ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(⟨⟨n, Finset.mem_range.mp hn⟩, j⟩ : β), rfl⟩
    calc
      (S + T).approximationNumber n
          ≤ ((S + T) ∘L U.subtypeL).approximationNumber n + ε / (k : ℝ) := (hv n).le
      _ ≤ ((S + T) ∘L V.subtypeL).approximationNumber n + ε / (k : ℝ) :=
        by gcongr; exact (S + T).approximationNumber_restrict_mono n hUV
      _ = (SV + TV).approximationNumber n + ε / (k : ℝ) := by rw [hsumRestrict]
  have hlocal : (S + T).kyFanGauge k ≤ (SV + TV).kyFanGauge k + ε := by
    calc
      (S + T).kyFanGauge k ≤ ∑ n ∈ Finset.range k,
          ((SV + TV).approximationNumber n + ε / (k : ℝ)) := Finset.sum_le_sum hterm
      _ = (SV + TV).kyFanGauge k + (k : ℝ) * (ε / (k : ℝ)) := by
        rw [kyFanGauge, Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
      _ = (SV + TV).kyFanGauge k + ε := by rw [mul_div_cancel₀ ε hkreal.ne']
  have hrestrictS : SV.kyFanGauge k ≤ S.kyFanGauge k :=
    Finset.sum_le_sum fun n _ => S.approximationNumber_comp_subtypeL_le n V
  have hrestrictT : TV.kyFanGauge k ≤ T.kyFanGauge k :=
    Finset.sum_le_sum fun n _ => T.approximationNumber_comp_subtypeL_le n V
  calc
    (S + T).kyFanGauge k ≤ (SV + TV).kyFanGauge k + ε := hlocal
    _ ≤ (SV.kyFanGauge k + TV.kyFanGauge k) + ε := by
      gcongr
      exact kyFanGauge_add_le_of_finiteDimensional_source k SV TV
    _ ≤ (S.kyFanGauge k + T.kyFanGauge k) + ε := by gcongr

end Localization

section Triangle

section AnyField

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

-- Neither space needs to be complete here: completeness is what `HasMinMaxLowerBound` is
-- proved from, not what the passage from it to the triangle inequality uses.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Ky Fan triangle inequality over any scalar field with a min--max lower bound.**

This is the general statement: `kyFanGauge_add_le_of_exists_finiteRestriction` needs a finite
source restriction for every tolerance, and `HasMinMaxLowerBound` is exactly what produces
one.  The two concrete fields are corollaries — `kyFanGauge_add_le_complex` over `ℂ` below and
`TauCeti.ApproximationNumber.kyFanGauge_add_le_real` over `ℝ` — and neither repeats any part
of the argument. -/
theorem kyFanGauge_add_le_of_hasMinMaxLowerBound (h : HasMinMaxLowerBound 𝕜 E F)
    (S T : E →L[𝕜] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k :=
  kyFanGauge_add_le_of_exists_finiteRestriction
    (fun n ε hε => h.exists_finiteRestrictionApproximationNumber_add_gt (S + T) n ε hε) k

end AnyField

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Every positive tolerance admits a finite source restriction whose approximation number
is within that tolerance of the ambient one, over `ℂ`. -/
theorem exists_finiteRestrictionApproximationNumber_add_gt
    (T : E →L[ℂ] F) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Fin (n + 1) → E,
      T.approximationNumber n <
        (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n + ε :=
  hasMinMaxLowerBound_complex.exists_finiteRestrictionApproximationNumber_add_gt T n ε hε

/-- **The Ky Fan triangle inequality**, in full generality: arbitrary bounded operators
between complex Hilbert spaces, no compactness or finite-dimensionality.

This is the inequality that makes every Ky Fan gauge a norm, and hence the one every
symmetric operator ideal built on approximation numbers depends on.  The argument is
`kyFanGauge_add_le_of_exists_finiteRestriction`; what is complex-specific is only the
min-max input it consumes. -/
theorem kyFanGauge_add_le_complex (S T : E →L[ℂ] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k :=
  kyFanGauge_add_le_of_hasMinMaxLowerBound hasMinMaxLowerBound_complex S T k

end Triangle

end

end ContinuousLinearMap
