/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.Core
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.Real
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.KyFan

/-!
# Scalar-generic approximation-number endpoints and ideal families

This public module assembles the lower approximation-number foundation with
its complex and real analytic endpoints. The scalar-generic endpoint wrappers
and the downstream Ky Fan dominant ideal families live here, above both
scalar-specific implementations, avoiding the former real-proof import cycle.

## Main definitions

* `HasApproximationNumberStrongCutoff`:
  the two analytic capabilities, separated from `RCLike` because that class is
  open while these facts are established for `ℝ` and `ℂ`.
* `kyFanSymmetricIdealFamily`: the finite Ky Fan gauge as a **canonical**
  `TauCeti.SymmetricOperatorIdealFamily`, with a completeness instance.
* `KyFanDominantIdealFamily`: a complete symmetric ideal family dominated by
  the finite Ky Fan gauges — the hypothesis of the infinite-dimensional
  Davis--Kahan estimates — together with its two instances, `operatorNorm` and
  `kyFan k`.

## The two gauges

The gauge is *stored* canonically in `ℝ≥0∞`, where the ideal laws are
unconditional, and *read* in `ℝ` through `KyFanDominantIdealFamily.gauge`,
because the Davis--Kahan estimates subtract gauges and finish with `linarith`.
The bridge is `TauCeti.SymmetricOperatorIdealFamily.gaugeReal`; see the
"ideal interface" section below.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open scoped ENNReal
open Filter

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Analytic capability asserting strong-cutoff convergence for approximation
numbers over a scalar field.  This is separated from `RCLike`: the latter is
an open algebraic typeclass, while this property is currently established for
the standard real and complex scalar fields. -/
class HasApproximationNumberStrongCutoff
    (𝕜 : Type u) [RCLike 𝕜] : Prop where
  tendsto_comp_strongProjection :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι},
      (∀ i, IsOrthogonalProjectionMap (P i)) →
      StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E) →
      ∀ (n : ℕ) (K : E →L[𝕜] F),
        Tendsto
          (fun i => approximationSingularValue n (K ∘L P i))
          l (𝓝 (approximationSingularValue n K))

/-- The strong-cutoff convergence holds over `ℝ`.  Supplied as an instance so
the field-generic development can be used at `ℝ` without naming the real proof. -/
instance realHasApproximationNumberStrongCutoff :
    HasApproximationNumberStrongCutoff.{0, v, w} ℝ where
  tendsto_comp_strongProjection :=
    ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real

/-- The strong-cutoff convergence holds over `ℂ`. -/
instance complexHasApproximationNumberStrongCutoff :
    HasApproximationNumberStrongCutoff.{0, v, w} ℂ where
  tendsto_comp_strongProjection :=
    approximationSingularValue_comp_strongProjection_tendsto_complex

/-- Real-Hilbert-space continuity of approximation numbers under strongly
convergent orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_real
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    {ι : Type w} {P : ι → ER →L[ℝ] ER} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ ER))
    (n : ℕ) (K : ER →L[ℝ] FR) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real
    hPproj hP n K

/-- Real-Hilbert-space finite Ky Fan convergence under strongly convergent
orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_real
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    {ι : Type w} {P : ι → ER →L[ℝ] ER} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ ER))
    (k : ℕ) (K : ER →L[ℝ] FR) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) :=
  ApproximationNumbersReal.kyFanApproximationGauge_comp_strongProjection_tendsto_real
    hPproj hP k K

/-- Real-Hilbert-space infinite-dimensional Ky Fan triangle inequality. -/
theorem kyFanApproximationGauge_add_le_real
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    (k : ℕ) (K L : ER →L[ℝ] FR) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L :=
  ApproximationNumbersReal.kyFanApproximationGauge_add_le_real k K L

/-- Continuity of each approximation number under strongly convergent
orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto
    [HasApproximationNumberStrongCutoff.{u, v, w} 𝕜]
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (n : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  HasApproximationNumberStrongCutoff.tendsto_comp_strongProjection
    (𝕜 := 𝕜) hPproj hP n K

/-- Ky Fan's addition inequality for approximation numbers. -/
theorem kyFanApproximationGauge_add_le
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    (k : ℕ) (K L : E →L[𝕜] F) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L :=
  ContinuousLinearMap.kyFanGauge_add_le_of_hasMinMaxLowerBound
    ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.out K L k


/-- Ky Fan gauges converge under strong orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto
    [HasApproximationNumberStrongCutoff.{u, v, w} 𝕜]
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (k : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  exact tendsto_finsetSum (Finset.range k)
    (fun n hn => approximationSingularValue_comp_strongProjection_tendsto
      hPproj hP n K)

/-! ### The finite Ky Fan gauges as a canonical ideal family -/

/-- The finite Ky Fan gauge `∑_{n < k} aₙ` as a **canonical** symmetric operator
ideal family (`TauCeti.SymmetricOperatorIdealFamily`).

The gauge is `ENNReal.ofReal` of `kyFanApproximationGauge k`, so it is finite
everywhere — every bounded operator is a member
(`carrier_kyFanSymmetricIdealFamily`) — and the four ideal laws are the
real-valued ones transported along `ENNReal.ofReal`.  Only one of them,
subadditivity, is mathematics rather than bookkeeping; it arrives through
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`, the `ForTauCeti` class that assumes the
min--max lower bound the Ky Fan triangle inequality is proved from.

`hk : 0 < k` is needed for exactly one law: `enorm_le_gauge`.  At `k = 0` the
gauge is identically `0`, which satisfies the other three but is not a norm.

**Intended destination.**  This belongs beside `TauCeti.operatorNormFamily` in
`ForTauCeti/Analysis/OperatorIdeal/Family/`.  It cannot live there yet, because
both `kyFanApproximationGauge` and the capability class supplying its triangle
inequality are defined in this library; it moves when the approximation-number
layer is extracted. -/
noncomputable def kyFanSymmetricIdealFamily
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k) :
    TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge A := ENNReal.ofReal (kyFanApproximationGauge k A)
  gauge_add_le A B := by
    rw [← ENNReal.ofReal_add (kyFanApproximationGauge_nonneg k A)
      (kyFanApproximationGauge_nonneg k B)]
    exact ENNReal.ofReal_le_ofReal (kyFanApproximationGauge_add_le k A B)
  gauge_smul c A := by
    rw [kyFanApproximationGauge_smul, ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm]
  enorm_le_gauge A := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (opNorm_le_kyFanApproximationGauge hk A)
  gauge_comp_le L A R := by
    rw [← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg L),
      ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (kyFanApproximationGauge_nonneg k A))]
    exact ENNReal.ofReal_le_ofReal (kyFanApproximationGauge_comp_le k L A R)
  gauge_adjoint A := by rw [kyFanApproximationGauge_adjoint]

/-- The gauge of the Ky Fan symmetric family is the `ℝ≥0∞` transport of the Ky
Fan approximation gauge, definitionally. -/
@[simp]
theorem gauge_kyFanSymmetricIdealFamily
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k)
    (A : E →L[𝕜] F) :
    (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).gauge A =
      ENNReal.ofReal (kyFanApproximationGauge k A) := rfl

/-- The Ky Fan gauge is never `∞`: it is `ENNReal.ofReal` of a real number.
This is what makes every bounded operator a member of the finite Ky Fan ideal. -/
theorem gauge_kyFanSymmetricIdealFamily_ne_top
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k)
    (A : E →L[𝕜] F) :
    (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).gauge A ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Every bounded operator lies in the finite Ky Fan ideal: the gauge is a
finite sum of approximation numbers, so it never reaches `∞`. -/
@[simp]
theorem carrier_kyFanSymmetricIdealFamily
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k) :
    (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).toOperatorIdealFamily.carrier
      (E := E) (F := F) = ⊤ := by
  ext A
  simp

/-- This family is the staged `TauCeti.kyFanIdealFamily`, over any field where both are
defined.

**The two capability classes are now the same fact one layer apart.**  This one assumes the
Ky Fan triangle inequality; `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere` assumes the
min--max lower bound the triangle inequality is *proved from*, and since 2026-07-31 that
lower bound holds over `ℝ` as well as `ℂ`.  So the staged family is no longer the
complex-only one of the pair — the sentence this docstring used to end with, that the
capability class *"survives only for the real-scalar case"*, is out of date.  What survives
is the redundancy: two classes stating the same capability at two depths, of which only the
deeper one is now needed. -/
theorem kyFanSymmetricIdealFamily_eq_kyFanIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k) :
    kyFanSymmetricIdealFamily.{u, v} (𝕜 := 𝕜) k hk
      = TauCeti.kyFanIdealFamily.{u, v} 𝕜 k hk :=
  rfl

/-- The real-valued Ky Fan gauge is recovered from the canonical one. -/
theorem toReal_gauge_kyFanSymmetricIdealFamily
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k)
    (A : E →L[𝕜] F) :
    ((kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).gauge A).toReal =
      kyFanApproximationGauge k A :=
  ENNReal.toReal_ofReal (kyFanApproximationGauge_nonneg k A)

/-- The finite Ky Fan ideal is complete.

The ideal is all of `E →L[𝕜] F` and its norm is *equivalent* to the operator
norm — `‖A‖ ≤ ∑_{n<k} aₙ(A) ≤ k‖A‖` — so completeness is inherited from the
bounded operators.  Both inequalities are needed: the first turns an ideal-norm
Cauchy sequence into an operator-norm one, the second turns the operator-norm
limit back into an ideal-norm limit. -/
instance isComplete_kyFanSymmetricIdealFamily
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k) :
    (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).toOperatorIdealFamily.IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    have hnorm : ∀ x : (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).toOperatorIdealFamily.Elem E F,
        ‖x‖ = kyFanApproximationGauge k x.val :=
      fun x => ENNReal.toReal_ofReal (kyFanApproximationGauge_nonneg k _)
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    have hop : CauchySeq fun n => (a n).val := by
      rw [Metric.cauchySeq_iff] at ha ⊢
      intro ε hε
      obtain ⟨M, hM⟩ := ha ε hε
      refine ⟨M, fun m hm n hn => lt_of_le_of_lt ?_ (hM m hm n hn)⟩
      rw [dist_eq_norm, dist_eq_norm, hnorm]
      exact opNorm_le_kyFanApproximationGauge hk _
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hop
    refine ⟨TauCeti.OperatorIdealFamily.Elem.mk
      (gauge_kyFanSymmetricIdealFamily_ne_top k hk L), ?_⟩
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    rw [Metric.tendsto_atTop] at hL ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hL (ε / k) (div_pos hε hkR)
    refine ⟨M, fun n hn => ?_⟩
    rw [dist_eq_norm, hnorm]
    calc kyFanApproximationGauge k ((a n).val - L)
        ≤ (k : ℝ) * ‖(a n).val - L‖ :=
          kyFanApproximationGauge_le_nat_mul_opNorm k _
      _ < (k : ℝ) * (ε / k) := by
          refine mul_lt_mul_of_pos_left ?_ hkR
          simpa [dist_eq_norm] using hM n hn
      _ = ε := by field_simp

/-- A **complete symmetric operator ideal family dominated by the finite Ky Fan
gauges**: the ideal norm decreases whenever every finite Ky Fan gauge does.

This is the hypothesis under which the infinite-dimensional Davis--Kahan
estimates hold for a general unitarily invariant norm.  The gauge is carried by
the canonical `TauCeti.SymmetricOperatorIdealFamily`, so the ideal laws are
inherited rather than restated, and Fan dominance is the single extra field.

Two fields disappeared when the storage moved from the historical record to the
canonical family, and both for the same reason — in `ℝ≥0∞` the laws are
unconditional.  Dominance no longer needs `B` to be a member as a *hypothesis*,
and no longer has to conclude that `A` is one: `gauge A ≤ gauge B` already gives
`gauge B ≠ ∞ → gauge A ≠ ∞`.  The historical two-part form survives as the
theorem `majorization_mem_and_gauge_le`. -/
structure FanDominantIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  /-- The canonical symmetric ideal family supplying the gauge and its laws. -/
  toSymmetricOperatorIdealFamily : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜
  /-- **Fan dominance.**  Majorization of every finite Ky Fan gauge forces the
  ideal gauge to be dominated too. -/
  gauge_le_of_forall_kyFanApproximationGauge_le :
    ∀ {E F E' F' : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
      [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
      {A : E →L[𝕜] F} {B : E' →L[𝕜] F'},
      (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      toSymmetricOperatorIdealFamily.gauge A ≤
        toSymmetricOperatorIdealFamily.gauge B

/-- **The Fan-dominant family together with the ideal's completeness.**

Completeness is a theorem of Gohberg--Krein about the *closed* class, not one of
the properties Davis and Kahan print, and the analytic layer genuinely needs it:
the limiting arguments in the `sin Θ` and `sin 2Θ` development ask for the ideal
to be a Banach space.  It therefore sits here, above the source-facing norm
quantifier, and not in `FanDominantIdealFamily`, which carries exactly the laws
the paper states. -/
structure KyFanDominantIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    extends FanDominantIdealFamily.{u, v} 𝕜 where
  /-- The ideal is complete for its own norm. -/
  isComplete : toSymmetricOperatorIdealFamily.toOperatorIdealFamily.IsComplete

attribute [instance] KyFanDominantIdealFamily.isComplete

/-- A complete Fan-dominant family is in particular a Fan-dominant one; the
coercion is what lets the existing call sites keep passing the stronger
structure to statements that only need the weaker one. -/
instance : CoeOut (KyFanDominantIdealFamily.{u, v} 𝕜) (FanDominantIdealFamily.{u, v} 𝕜) :=
  ⟨KyFanDominantIdealFamily.toFanDominantIdealFamily⟩

namespace FanDominantIdealFamily

/-! ### The ideal interface

The gauge is stored canonically, in `ℝ≥0∞`, but the Davis--Kahan development is
written in `ℝ`: its estimates multiply gauges by gap constants, subtract them,
and finish with `linarith`, none of which survives truncated subtraction.  So
the paper-facing view is a **real-valued** one, obtained by reading the
canonical family: `TauCeti.SymmetricOperatorIdealFamily.gaugeReal`, which reads
the stored `ℝ≥0∞` gauge through `.toReal`, with `Mem` its finiteness.

The canonical family is the source of truth and nothing is duplicated: every law
of the historical record is a theorem about the canonical gauge, proved in
`DavisKahan/OperatorIdeal/CanonicalRealView.lean`.

`Mem` and `gauge` remain the whole public surface the sin-Θ development uses. -/

variable (N : FanDominantIdealFamily.{u, v} 𝕜)

/-! Both accessors below read the **canonical** family directly.  They used to
route through a view onto the historical rectangular record, which made every one
of the ~28 modules that consume a `KyFanDominantIdealFamily` depend on the legacy
structure definitionally, even though none of them mentions it.  That view defined
exactly `Mem A := gauge A ≠ ∞` and `gauge A := (gauge A).toReal`, so going direct
is definitionally the same term — `mem_iff` and `gauge_eq_toReal` below are still
`Iff.rfl` and `rfl` — and no statement or proof downstream changed meaning. -/

/-- Membership in the ideal: the operator has finite ideal gauge. -/
abbrev Mem (A : E →L[𝕜] F) : Prop :=
  N.toSymmetricOperatorIdealFamily.gauge A ≠ ∞

/-- The ideal gauge, real-valued and meaningful only on members
(`FanDominantIdealFamily.Mem`). -/
noncomputable abbrev gauge (A : E →L[𝕜] F) : ℝ :=
  (N.toSymmetricOperatorIdealFamily.gauge A).toReal

/-! The two bridges to the canonical gauge.  Deliberately **not** `@[simp]`: they
rewrite the paper-facing `ℝ` view into the stored `ℝ≥0∞` one, which is the wrong
normal form for this layer — the Davis--Kahan estimates are stated and proved in
`ℝ`.  As `simp` lemmas they also shadow `kyFan_gauge`, whose left-hand side is
the `ℝ` view, and that silently breaks `simpa` calls two libraries away. -/

/-- Membership in the ideal is finiteness of the canonical `ℝ≥0∞` gauge.  The
first of the two bridges described above, and deliberately not `@[simp]`. -/
theorem mem_iff (A : E →L[𝕜] F) :
    N.Mem A ↔ N.toSymmetricOperatorIdealFamily.gauge A ≠ ∞ := Iff.rfl

/-- The real-valued gauge is the `.toReal` of the stored `ℝ≥0∞` one.  The second
of the two bridges described above, and like `mem_iff` deliberately not `@[simp]`. -/
theorem gauge_eq_toReal (A : E →L[𝕜] F) :
    N.gauge A = (N.toSymmetricOperatorIdealFamily.gauge A).toReal := rfl

/-! Both accessors are `abbrev`, so they are reducible and `exact` sees through
them.  `rw` does **not**: it keys on the head symbol, and the accessor form and
the canonical-gauge form have different ones.  A proof whose goal is stated through these accessors but
whose supporting lemmas are stated over the historical record — the block lemmas
in `SinTheta/**` are the usual case — has to reconcile the two.

**Reconcile by normalising the hypothesis upward, not the goal downward.**  The
older idiom was `simp only [KyFanDominantIdealFamily.gauge]`, which unfolded the
*goal* into whatever `gauge` was defined as.  That only ever worked by accident:
it depended on `gauge` being defined through the historical record, so repointing
the accessor at the canonical family broke thirteen proofs across eight files at
once.  The two lemmas below rewrite the *hypothesis* into the accessor form
instead, which is stable under any later change to what `gauge` unfolds to, and
points the same way as the migration. -/



/-- The canonical family's real view is `N.gauge` -- again the same term, again a
different head symbol.  Needed once a provider has been migrated off the historical
record: the result then arrives as `N.toSymmetricOperatorIdealFamily.gaugeReal`, and
`kyFan_gauge` is stated over the accessor. -/
theorem toSymmetric_gaugeReal (A : E →L[𝕜] F) :
    N.toSymmetricOperatorIdealFamily.gaugeReal A = N.gauge A := rfl

/-- The canonical family's membership is `N.Mem`; the companion of
`toSymmetric_gaugeReal`. -/
theorem toSymmetric_mem (A : E →L[𝕜] F) :
    N.toSymmetricOperatorIdealFamily.Mem A = N.Mem A := rfl

/-- Fan dominance in the historical two-part form: majorization of every finite
Ky Fan gauge carries membership *and* the gauge bound.

Both halves now follow from the single canonical inequality — in `ℝ≥0∞`,
`gauge A ≤ gauge B` already implies `A` is a member as soon as `B` is. -/
theorem majorization_mem_and_gauge_le {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'} (hB : N.Mem B)
    (h : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) :
    N.Mem A ∧ N.gauge A ≤ N.gauge B := by
  have hle := N.gauge_le_of_forall_kyFanApproximationGauge_le h
  exact ⟨ne_top_of_le_ne_top hB hle, ENNReal.toReal_mono hB hle⟩

end FanDominantIdealFamily

namespace KyFanDominantIdealFamily

variable (N : KyFanDominantIdealFamily.{u, v} 𝕜)

/-- The ordinary operator norm with its finite-Ky-Fan dominance property. -/
noncomputable def operatorNorm :
    KyFanDominantIdealFamily.{u, v} 𝕜 where
  toSymmetricOperatorIdealFamily := TauCeti.operatorNormFamily 𝕜
  isComplete := inferInstance
  gauge_le_of_forall_kyFanApproximationGauge_le := by
    intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hmajor
    have h : ‖A‖ ≤ ‖B‖ := by simpa using hmajor 1
    simpa [TauCeti.gauge_operatorNormFamily, ← ofReal_norm] using
      ENNReal.ofReal_le_ofReal h

/-- A fixed positive finite Ky Fan gauge with its own dominance property.

Dominance is immediate: the gauge *is* the `k`-th Ky Fan gauge, so majorization
at index `k` is the conclusion. -/
noncomputable def kyFan [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    (k : ℕ) (hk : 0 < k) :
    KyFanDominantIdealFamily.{u, v} 𝕜 where
  toSymmetricOperatorIdealFamily := kyFanSymmetricIdealFamily k hk
  isComplete := inferInstance
  gauge_le_of_forall_kyFanApproximationGauge_le := by
    intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hmajor
    exact ENNReal.ofReal_le_ofReal (hmajor k)

/-! The next two are stated through `Mem`/`gauge`, the accessors.

They used to be stated through the *derived view* instead, for a reason that has
since expired: downstream `simpa only [N, kyFan_gauge]` calls arrived with goals
already unfolded by `simp only [KyFanDominantIdealFamily.gauge]`, so an
accessor-shaped left-hand side would have stopped matching.  Those unfoldings are
gone — the sites now normalise their hypotheses up to the accessor via
`toSymmetric_gaugeReal` rather than unfolding the goal — so the
accessor is the shape that matches, and it is also the shape that survives the
historical record being deleted. -/

/-- Every bounded operator belongs to the fixed finite Ky Fan family. -/
@[simp]
theorem kyFan_mem [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    (k : ℕ) (hk : 0 < k) (K : E →L[𝕜] F) :
    (kyFan (𝕜 := 𝕜) k hk).Mem K :=
  gauge_kyFanSymmetricIdealFamily_ne_top k hk K

/-- The concrete gauge of the fixed finite Ky Fan family. -/
@[simp]
theorem kyFan_gauge [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    (k : ℕ) (hk : 0 < k) (K : E →L[𝕜] F) :
    (kyFan (𝕜 := 𝕜) k hk).gauge K = kyFanApproximationGauge k K :=
  toReal_gauge_kyFanSymmetricIdealFamily k hk K

end KyFanDominantIdealFamily

/-- Infinite-dimensional Fan dominance, exposed from the stronger family. -/
theorem mem_and_gauge_le_of_all_kyFanApproximationGauge_le
    (N : FanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F}
    (hB : N.Mem B)
    (h : ∀ k, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.Mem A ∧
      N.gauge A ≤
        N.gauge B :=
  N.majorization_mem_and_gauge_le hB h

/-- Scaled Fan dominance in the exact form consumed by the Sylvester theorem. -/
theorem mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    (N : FanDominantIdealFamily (𝕜 := 𝕜))
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'} {δ : ℝ}
    (hδ : 0 < δ)
    (hB : N.Mem B)
    (h : ∀ k, δ * kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.Mem A ∧
      δ * N.gauge A ≤
        N.gauge B := by
  let d : 𝕜 := (δ : 𝕜)
  have hd : d ≠ 0 := RCLike.ofReal_ne_zero.mpr hδ.ne'
  have hdnorm : ‖d‖ = δ := by
    simp [d, abs_of_pos hδ]
  have hscaled : ∀ k,
      kyFanApproximationGauge k (d • A) ≤
        kyFanApproximationGauge k B := by
    intro k
    rw [kyFanApproximationGauge_smul, hdnorm]
    exact h k
  obtain ⟨hdA, hgauge⟩ := N.majorization_mem_and_gauge_le hB hscaled
  have hA : N.Mem A := by
    have hinv := N.toSymmetricOperatorIdealFamily.smul_mem d⁻¹ hdA
    rw [← mul_smul, inv_mul_cancel₀ hd, one_smul] at hinv
    exact hinv
  refine ⟨hA, ?_⟩
  -- Ascribed to `N.gauge` rather than left at the canonical accessor.  The two are the
  -- same term, but only the former shares an atom with the goal: `linarith` identifies
  -- atoms up to *reducible* defeq, and `toSymmetricOperatorIdealFamily` is a projection.
  have hhom : N.gauge (d • A) = ‖d‖ * N.gauge A :=
    N.toSymmetricOperatorIdealFamily.gaugeReal_smul d hA
  rw [hdnorm] at hhom
  linarith

/-- **A Ky Fan gauge is unchanged by moving an orthogonal projection across the
adjoint.**

`‖P K‖_(k) = ‖K⋆ P‖_(k)` for an orthogonal projection `P`.  Derived identically
in `Sylvester/Unbounded/OrderedCutoff.lean` and
`Sylvester/Unbounded/OrderedFromCutoffs.lean`, which share no import edge. -/
theorem kyFanApproximationGauge_proj_comp_eq_adjoint_comp
    {k : ℕ} {P : F →L[𝕜] F} (hP : IsOrthogonalProjectionMap P) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k (P ∘L K) =
      kyFanApproximationGauge k (K.adjoint ∘L P) := by
  rw [← kyFanApproximationGauge_adjoint k (P ∘L K)]
  simp only [ContinuousLinearMap.adjoint_comp]
  rw [hP.2.clm_adjoint_eq]

end ExactSinTheta
end DavisKahan
end TauCeti
