/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Normalized symmetric operator ideal families

This module contains two related operator-ideal norm records.

* `NormalizedSymmetricOperatorIdealFamily` is the mathematical base object: a
  symmetric operator ideal family together with rank-one normalization and
  where-defined Fan comparison. The last property is an explicit structure field,
  not a theorem derived here from the other two ingredients.
  Its name describes the data it carries; Davis--Kahan provenance belongs in
  theorem and module documentation rather than in the type name.
* `NormalizedUnitaryInvariantNorm` is the older, stronger implementation record.
  It additionally packages unconditional Fan dominance through
  `FanDominantIdealFamily`.

The distinction matters in infinite dimension.  With an `ℝ≥0∞` gauge, unconditional
Fan dominance also transfers ideal membership: if the right-hand operator has finite
gauge and every Ky Fan gauge of the left-hand operator is smaller, the left-hand
operator must have finite gauge as well.  That domain-solidity assertion is stronger
than the where-defined comparison needed by the source-facing Davis--Kahan
inequalities.  The base record therefore carries only where-defined Fan comparison; it does not
carry the stronger membership-transferring form.

## Mathematical data in the base record

`NormalizedSymmetricOperatorIdealFamily` consists of:

* the domain/ideal and its `ℝ≥0∞` gauge, supplied by
  `TauCeti.SymmetricOperatorIdealFamily`;
* the norm and two-sided ideal laws already carried by that family;
* adjoint/unitary invariance and contraction compatibility, derived from those
  ideal laws; and
* the rank-one normalization `‖u v*‖ = ‖u‖ ‖v‖`, represented by
  `gauge_rankOne_eq_one` after normalizing the vectors; and
* the where-defined comparison law
  `gauge_le_of_forall_kyFanApproximationGauge_le_defined`.

Where-defined Fan comparison is part of the mathematical base record.  Adding the
stronger unconditional property with `NormalizedSymmetricOperatorIdealFamily.withFanDominance` recovers a
`NormalizedUnitaryInvariantNorm`.  Conversely,
`NormalizedUnitaryInvariantNorm.toNormalizedSymmetricOperatorIdealFamily` forgets
that extra property.

The theorem `hasFanDominanceWhereDefined` below exposes that stored law. It does
not establish a representation theorem for every norm satisfying only bare
unitary invariance. Davis--Kahan Section 1 cites Fan comparison as mathematical
background; source audits must record that choice explicitly.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal

noncomputable section

universe u v

/-- A normalized symmetric operator ideal family with unconditional Fan dominance.

This is the stronger implementation record used by existing analytic machinery.
Its Fan-dominance field includes the associated membership-transfer consequence;
source-facing theorem signatures should use the weaker mathematical base record
when that stronger domain assertion is not part of the statement being modeled. -/
structure NormalizedUnitaryInvariantNorm (𝕜 : Type u) [RCLike 𝕜] where
  /-- The Fan-dominant symmetric ideal family supplying the gauge, its domain,
  and all the norm and ideal laws.

  **Completeness is deliberately not here.**  It is a property of the ideal that
  the analytic development needs and that Gohberg--Krein prove about the closed
  class; Davis and Kahan do not print it, so it must not restrict the
  source-facing quantifier.  It lives one layer up, on
  `KyFanDominantIdealFamily`. -/
  toFanDominantIdealFamily : FanDominantIdealFamily.{u, v} 𝕜
  /-- **The source normalization.**  A rank-one operator of norm one has norm
  one -- the Lean spelling of `‖u v*‖ = ‖u‖ ‖v‖` after scaling both vectors to
  norm one. -/
  gauge_rankOne_eq_one : ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {V : E →L[𝕜] F}, ‖V‖ = 1 → V.rank ≤ (1 : Cardinal) →
      toFanDominantIdealFamily.gauge V = 1

namespace NormalizedUnitaryInvariantNorm

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜)

/-- Membership in the norm's ideal: the source's "the norm exists here". -/
abbrev Mem (A : E →L[𝕜] F) : Prop := N.toFanDominantIdealFamily.Mem A

/-- The real-valued norm, meaningful on its ideal. -/
noncomputable abbrev gauge (A : E →L[𝕜] F) : ℝ :=
  N.toFanDominantIdealFamily.gauge A

/-- Membership and the gauge are read off the underlying family; this is the
bridge a façade proof uses. -/
theorem mem_iff_fanDominant (A : E →L[𝕜] F) :
    N.Mem A ↔ N.toFanDominantIdealFamily.Mem A := Iff.rfl

/-- The gauge is the underlying family's gauge. -/
theorem gauge_eq_fanDominant (A : E →L[𝕜] F) :
    N.gauge A = N.toFanDominantIdealFamily.gauge A := rfl

/-! ### The source's listed properties, derived

Each theorem below is one line of Davis--Kahan's Section 1 list.  None is a field
of the structure: they follow from the ideal laws the underlying family already
carries, and proving them here is what makes the structure's data irredundant. -/

/-- **Nonnegativity.** -/
theorem gauge_nonneg {A : E →L[𝕜] F} (hA : N.Mem A) : 0 ≤ N.gauge A :=
  N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_nonneg hA

/-- **Definiteness.**  The norm vanishes only on the zero operator. -/
theorem gauge_eq_zero_iff {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge A = 0 ↔ A = 0 := by
  constructor
  · intro h
    exact N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_eq_zero hA h
  · rintro rfl
    exact N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_zero

/-- **The triangle inequality.** -/
theorem gauge_add_le {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.gauge (A + B) ≤ N.gauge A + N.gauge B :=
  N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_add_le hA hB

/-- **Absolute homogeneity.** -/
theorem gauge_smul (c : 𝕜) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge (c • A) = ‖c‖ * N.gauge A :=
  N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_smul c hA

/-- **Contraction compatibility on the left.**  Composing with an operator of
norm at most one does not increase the norm. -/
theorem gauge_comp_left_le (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : N.Mem A)
    (hL : ‖L‖ ≤ 1) : N.gauge (L ∘L A) ≤ N.gauge A :=
  N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_comp_left_le L hA hL

/-- **Contraction compatibility on the right.** -/
theorem gauge_comp_right_le {A : E →L[𝕜] F} (R : H →L[𝕜] E) (hA : N.Mem A)
    (hR : ‖R‖ ≤ 1) : N.gauge (A ∘L R) ≤ N.gauge A :=
  N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_comp_right_le R hA hR

/-- **The norm dominates the operator norm**, so it is a norm and not a
seminorm on its ideal. -/
theorem opNorm_le_gauge {A : E →L[𝕜] F} (hA : N.Mem A) : ‖A‖ ≤ N.gauge A :=
  N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.opNorm_le_gaugeReal hA

/-- **Adjoint invariance**, which the source uses whenever it transposes a
block. -/
theorem gauge_adjoint {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge A.adjoint = N.gauge A :=
  N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.gaugeReal_adjoint hA

/-- A linear isometric equivalence is a contraction. -/
private theorem norm_isometryEquiv_le_one {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
    (g : X ≃ₗᵢ[𝕜] Y) : ‖(g.toContinuousLinearEquiv : X →L[𝕜] Y)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp

/-- **Equation (1.9): unitary invariance.**  Composing with linear isometric
equivalences on either side leaves the norm unchanged.

Both inequalities come from contraction compatibility: an isometric equivalence
and its inverse are contractions, so neither direction can strictly decrease the
norm.  This is why (1.9) is a theorem here rather than a field. -/
theorem gauge_comp_isometryEquiv (e : F ≃ₗᵢ[𝕜] G) (f : H ≃ₗᵢ[𝕜] E)
    {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge ((e.toContinuousLinearEquiv : F →L[𝕜] G) ∘L A ∘L
      (f.toContinuousLinearEquiv : H →L[𝕜] E)) = N.gauge A := by
  set S := N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily with hS
  set B := (e.toContinuousLinearEquiv : F →L[𝕜] G) ∘L A ∘L
    (f.toContinuousLinearEquiv : H →L[𝕜] E) with hB
  have hBmem : N.Mem B := S.comp_mem _ _ hA
  -- `A` is recovered from `B` by the inverse equivalences.
  have hAeq : A = (e.symm.toContinuousLinearEquiv : G →L[𝕜] F) ∘L B ∘L
      (f.symm.toContinuousLinearEquiv : E →L[𝕜] H) := by
    ext x
    simp [hB]
  refine le_antisymm ?_ ?_
  · calc N.gauge B
        ≤ N.gauge (A ∘L (f.toContinuousLinearEquiv : H →L[𝕜] E)) := by
          rw [hB, ← ContinuousLinearMap.comp_assoc]
          exact S.gaugeReal_comp_left_le _ (S.comp_right_mem _ hA)
            (norm_isometryEquiv_le_one e)
      _ ≤ N.gauge A := S.gaugeReal_comp_right_le _ hA (norm_isometryEquiv_le_one f)
  · calc N.gauge A
        = N.gauge ((e.symm.toContinuousLinearEquiv : G →L[𝕜] F) ∘L B ∘L
            (f.symm.toContinuousLinearEquiv : E →L[𝕜] H)) := by rw [← hAeq]
      _ ≤ N.gauge (B ∘L (f.symm.toContinuousLinearEquiv : E →L[𝕜] H)) := by
          rw [← ContinuousLinearMap.comp_assoc]
          exact S.gaugeReal_comp_left_le _ (S.comp_right_mem _ hBmem)
            (norm_isometryEquiv_le_one e.symm)
      _ ≤ N.gauge B :=
          S.gaugeReal_comp_right_le _ hBmem (norm_isometryEquiv_le_one f.symm)

/-- **A norm-one rank-one operator lies in the ideal.**

This is not a separate assumption: the structure's one normalization field says
the *real* gauge of such an operator is `1`, and the real gauge reads the stored
`ℝ≥0∞` gauge through `toReal`, which sends `∞` to `0`.  A value of `1` therefore
already rules out `∞`.

It is what makes the class usable on the Section 2 equality models, whose
residual and directed sine block are scalar multiples of a norm-one rank-one
coordinate inclusion. -/
theorem mem_rankOne {V : E →L[𝕜] F} (hVnorm : ‖V‖ = 1)
    (hVrank : V.rank ≤ (1 : Cardinal)) : N.Mem V := by
  intro htop
  have h1 : N.gauge V = 1 := N.gauge_rankOne_eq_one hVnorm hVrank
  rw [show N.gauge V
      = (N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge
          V).toReal from rfl, htop] at h1
  simp at h1

/-- Finite sums of members are members. -/
theorem mem_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E →L[𝕜] F}
    (hA : ∀ i ∈ s, N.Mem (A i)) : N.Mem (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.zero_mem
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily.add_mem
        (hA i (Finset.mem_insert_self i s))
        (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

end NormalizedUnitaryInvariantNorm

/-! ## The normalized symmetric ideal-family layer

`NormalizedSymmetricOperatorIdealFamily` is the mathematical record obtained by
adding the rank-one normalization to `TauCeti.SymmetricOperatorIdealFamily`.
It includes only the standard where-defined Ky Fan comparison, not unconditional
Fan dominance of the total extended gauge.

`NormalizedUnitaryInvariantNorm` is the stronger record obtained by adding the
unconditional Fan-dominance property.  The conversions below make that relation
explicit:

```text
NormalizedSymmetricOperatorIdealFamily
        │  withFanDominance
        ▼
NormalizedUnitaryInvariantNorm
        │  toNormalizedSymmetricOperatorIdealFamily
        └───────────────────────────────────────────► base record
```

The exploration in `DavisKahan/Explorations/SourceUnitaryInvariantNormFanDominance`
shows why the distinction is semantic rather than cosmetic: unconditional
`ℝ≥0∞` Fan dominance contains a membership-transfer statement, while a
where-defined Fan comparison does not.  Source correspondence is therefore
recorded in theorem documentation instead of being encoded in this type's name.
-/

/-- A normalized symmetric operator ideal family.

This is a symmetric operator ideal family -- carrying its domain, gauge, norm laws,
adjoint symmetry, and two-sided ideal law -- together with the rank-one
normalization `‖u v*‖ = ‖u‖ ‖v‖`.

The standard Ky Fan comparison is stored only at its where-defined scope.  No
membership-transfer or domain-solidity property is part of this structure. -/
structure NormalizedSymmetricOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  /-- The symmetric ideal family supplying the gauge, its domain, and all the
  norm and ideal laws. -/
  toSymmetricOperatorIdealFamily : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜
  /-- The rank-one normalization `‖u v*‖ = ‖u‖ ‖v‖`, after scaling both vectors
  to norm one. -/
  gauge_rankOne_eq_one : ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {V : E →L[𝕜] F}, ‖V‖ = 1 → V.rank ≤ (1 : Cardinal) →
      (toSymmetricOperatorIdealFamily.gauge V).toReal = 1
  /-- Ky Fan dominance where both displayed ideal norms exist.  This is the
  partial-domain comparison theorem used by Davis--Kahan; unlike unconditional
  dominance of the extended `ℝ≥0∞` gauge, it does not transfer ideal membership. -/
  gauge_le_of_forall_kyFanApproximationGauge_le_defined :
    ∀ {E F E' F' : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
      [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
      {A : E →L[𝕜] F} {B : E' →L[𝕜] F'},
      toSymmetricOperatorIdealFamily.gauge A ≠ ⊤ →
      toSymmetricOperatorIdealFamily.gauge B ≠ ⊤ →
      (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
        toSymmetricOperatorIdealFamily.gauge A ≤
          toSymmetricOperatorIdealFamily.gauge B

namespace NormalizedSymmetricOperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Membership in the normalized symmetric operator ideal family.  This is the
finiteness domain of the underlying symmetric ideal gauge. -/
abbrev Mem
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : Prop :=
  N.toSymmetricOperatorIdealFamily.Mem A

/-- The real-valued ideal gauge, to be read only together with a corresponding
`Mem` hypothesis. -/
noncomputable abbrev gaugeReal
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : ℝ :=
  N.toSymmetricOperatorIdealFamily.gaugeReal A

/-- Ky Fan dominance where both displayed ideal norms exist.  This is the
comparison property of the normalized symmetric ideal family itself; it does not
assert that majorization transfers membership between ideal domains. -/
def HasFanDominanceWhereDefined
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'},
    N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤ →
    N.toSymmetricOperatorIdealFamily.gauge B ≠ ⊤ →
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- Every normalized symmetric operator ideal family carries where-defined Fan dominance. -/
theorem hasFanDominanceWhereDefined (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜) :
    N.HasFanDominanceWhereDefined :=
  N.gauge_le_of_forall_kyFanApproximationGauge_le_defined

/-- A scaled norm comparison with Davis--Kahan's partial-norm convention: when
both displayed norms exist, `c ‖A‖ ≤ ‖B‖`; if either norm does not exist, there
is no numerical obligation. -/
def ScaledGaugeLEWhereDefined
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    (c : ℝ) (A : E →L[𝕜] F) (B : E' →L[𝕜] F') : Prop :=
  N.toSymmetricOperatorIdealFamily.Mem A →
  N.toSymmetricOperatorIdealFamily.Mem B →
    c * N.toSymmetricOperatorIdealFamily.gaugeReal A ≤
      N.toSymmetricOperatorIdealFamily.gaugeReal B

/-- Transport scaled Ky Fan inequalities through the standard where-defined Fan
comparison, without deriving membership of either displayed operator. -/
theorem scaledGaugeLEWhereDefined_of_all_mul_kyFan_le
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    {c : ℝ} {A : E →L[𝕜] F} {B : E' →L[𝕜] F'}
    (hc : 0 < c)
    (hky : ∀ k, c * kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) :
    N.ScaledGaugeLEWhereDefined c A B := by
  intro hA hB
  let S := N.toSymmetricOperatorIdealFamily
  have hscaledMem : S.Mem ((((c : ℝ) : 𝕜)) • A) := S.smul_mem (((c : ℝ) : 𝕜)) hA
  have hscaled : ∀ k, kyFanApproximationGauge k ((((c : ℝ) : 𝕜)) • A) ≤
      kyFanApproximationGauge k B := by
    intro k
    rw [kyFanApproximationGauge_smul, RCLike.norm_ofReal, abs_of_pos hc]
    exact hky k
  have hle : S.gauge ((((c : ℝ) : 𝕜)) • A) ≤ S.gauge B :=
    N.hasFanDominanceWhereDefined hscaledMem hB hscaled
  have hreal : S.gaugeReal ((((c : ℝ) : 𝕜)) • A) ≤ S.gaugeReal B :=
    ENNReal.toReal_mono hB hle
  rw [S.gaugeReal_smul (((c : ℝ) : 𝕜)) hA, RCLike.norm_ofReal, abs_of_pos hc] at hreal
  exact hreal

/-- Unconditional Fan dominance for a normalized symmetric operator ideal family.

Because nonmembership is represented by gauge `⊤`, this property contains both
where-defined Fan monotonicity and the corresponding membership-transfer
consequence. -/
def HasFanDominance (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- Add unconditional Fan dominance to the base normalized symmetric family. -/
def withFanDominance (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜) (h : N.HasFanDominance) :
    NormalizedUnitaryInvariantNorm.{u, v} 𝕜 where
  toFanDominantIdealFamily :=
    { toSymmetricOperatorIdealFamily := N.toSymmetricOperatorIdealFamily
      gauge_le_of_forall_kyFanApproximationGauge_le := h }
  gauge_rankOne_eq_one := fun hV hr => N.gauge_rankOne_eq_one hV hr

end NormalizedSymmetricOperatorIdealFamily

namespace NormalizedUnitaryInvariantNorm

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Forget unconditional Fan dominance, retaining the normalized symmetric ideal family. -/
def toNormalizedSymmetricOperatorIdealFamily (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜) :
    NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toSymmetricOperatorIdealFamily :=
    N.toFanDominantIdealFamily.toSymmetricOperatorIdealFamily
  gauge_rankOne_eq_one := fun hV hr => N.gauge_rankOne_eq_one hV hr
  gauge_le_of_forall_kyFanApproximationGauge_le_defined := by
    intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B _ _ hAB
    exact N.toFanDominantIdealFamily.gauge_le_of_forall_kyFanApproximationGauge_le hAB

/-- The forgotten base family satisfies unconditional Fan dominance by the field carried above it. -/
theorem toNormalizedSymmetricOperatorIdealFamily_hasFanDominance (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜) :
    N.toNormalizedSymmetricOperatorIdealFamily.HasFanDominance :=
  N.toFanDominantIdealFamily.gauge_le_of_forall_kyFanApproximationGauge_le

/-- Forgetting Fan dominance and then adding back the carried property returns the same record. -/
theorem toNormalizedSymmetricOperatorIdealFamily_withFanDominance (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜) :
    N.toNormalizedSymmetricOperatorIdealFamily.withFanDominance N.toNormalizedSymmetricOperatorIdealFamily_hasFanDominance = N := by
  cases N with
  | mk fam _ => cases fam; rfl

end NormalizedUnitaryInvariantNorm

end

end ExactSinTheta
end DavisKahan
end TauCeti
