/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/


/-
# HANDOFF: normalized symmetric ideal families / Fan dominance (2026-09-08)

**2026-09-09 scope note.** The handoff below is historical. In the current base
record, where-defined Fan comparison is already an explicit field. Consequently
its public accessor is not an independent derivation from the norm and ideal
laws. The earlier statement below that the base record contains no Fan dominance
must be read as the pre-field state. Unconditional membership-transferring Fan
dominance is still distinct. Preserve the probes as exploration history; do not
count a field projection as closure of a bare-UI-norm representation obligation.


This file is intentionally a **standalone compile probe**.  Nothing imports it.
The user compiled Probes 1--43 cleanly before the naming cleanup that renamed the
base record from its previous provenance-based name to the
mathematical `NormalizedSymmetricOperatorIdealFamily`. Probes 44--46 were added on
2026-09-09 to test the repaired real/complex/RCLike maintenance boundary for
`sin Θ` and `sin 2Θ`. Probes 44 and 45 compiled on the first run. The original
Probe 46 compiled after this standalone file opened the repository's scoped
`TauCeti.CompleteSubspace` instance.  That successful norm-layer probe was then
replaced by production-conformance Probes 46 and 47 after the scalar-generic
directed residual engine was factored into production; those current probes
still require a compiler run.

Compile this file with:

```text
lake env lean \
  DavisKahan/Explorations/SourceUnitaryInvariantNormFanDominance.lean
```

## Result of the exploration

The base mathematical object is now:

```text
NormalizedSymmetricOperatorIdealFamily
```

It is a `SymmetricOperatorIdealFamily` together with the rank-one normalization.
It does not contain Fan dominance.  `NormalizedUnitaryInvariantNorm` remains the
stronger implementation record whose underlying `FanDominantIdealFamily` carries
unconditional `ENNReal` Fan dominance.

Probes 17--24 construct a finite-rank/operator-norm family with gauge `∞` outside
the finite-rank ideal.  It satisfies the base record and where-defined Fan
monotonicity but refutes unconditional Fan dominance.  The failure is exactly
membership transfer: Ky-Fan domination by an ideal member need not force the
dominated operator into this ideal.

Probes 25--30 separate memberwise symmetric-norming representation from total
ideal-domain representation.  Memberwise representation is enough for
where-defined Fan comparison; total/domain representation additionally gives the
membership-transfer property bundled into unconditional `ENNReal` dominance.

Probes 31--37 express the source's "vacuous when the norm does not exist"
convention directly and show that the Davis--Kahan sine-theta analytic theorem
can be presented at the where-defined boundary.

Probes 38--43 finish the theorem-signature test.  They show that:

* vacuous comparison is exactly the ordinary real-valued inequality conditional
  on both displayed norms existing;
* the finite-rank countermodel is not in the image of
  `NormalizedUnitaryInvariantNorm.toNormalizedSymmetricOperatorIdealFamily`;
* the actual sine-theta theorem still holds for that excluded family at the
  vacuous/where-defined boundary; and
* the candidate public norm quantifier requires no caller-visible membership
  premise and concludes no membership transfer.

The source/literature audit therefore points to where-defined Fan comparison as
the source-facing boundary.  The next production step is separate from this
naming cleanup: put the where-defined comparison at the reusable mathematical
layer and retarget the canonical Davis--Kahan façades to the vacuous conclusion.
Do not attempt to prove unconditional `HasFanDominance` from the base record;
the countermodel proves that implication false.
-/
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.PrescribedSequence
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CompactApproximationEigenvalues
import LeanPool.DavisKahan.DavisKahan.SharedFoundations.Ideal.ModulusTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Majorization
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.System
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SeparableOrthonormal
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.BlockSum
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.KyFanNorm
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.NormalizedUnitaryInvariantNormExamples
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaDirectedAngle
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaDirectedRCLike
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SectionTwo

/-!
# Exploration: Fan dominance at the Davis--Kahan source norm boundary

This file is deliberately standalone.  Nothing imports it, and it does not
change `NormalizedSymmetricOperatorIdealFamily`, `NormalizedUnitaryInvariantNorm`, or any
production theorem signature.

The question being tested is narrower than "formalize Calkin's theorem":

1. Davis--Kahan work on separable Hilbert spaces.
2. Their source norm class is represented by `NormalizedSymmetricOperatorIdealFamily`.
3. The source-facing theorem should not require an extra `HasFanDominance`
   argument if Fan dominance is a theorem of that source class.
4. Existing `ForTauCeti` infrastructure already proves that a gauge obtained
   from a symmetric sequence gauge is Fan dominant.

The compile probes below progressively narrow the missing implication.  Probe 1
checks that a separable symmetric-gauge representation would suffice, but later
probes deliberately avoid assuming that representation: the printed source
class can contain norms with an essential/Calkin contribution invisible to
finite-rank gauge recovery.  The later probes instead isolate what follows from
the raw source ideal laws, what can be reduced to one infinite-dimensional
separable model space, and which genuinely infinite-dimensional obligations
remain.

No `sorry`, `axiom`, or replacement source structure is introduced here.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta
namespace FanDominanceExploration

open scoped ENNReal InnerProductSpace

noncomputable section

universe v

/-- Fan dominance restricted to the separable Hilbert-space scope used by the
Davis--Kahan paper.

This is intentionally a local exploration predicate rather than a field added
to `NormalizedSymmetricOperatorIdealFamily`. -/
def HasFanDominanceSeparable (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [TopologicalSpace.SeparableSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    [TopologicalSpace.SeparableSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- A separable Calkin-style representation statement, stated only as strongly
as this exploration needs it.

The same symmetric sequence gauge must represent the source norm on every
separable source/target pair.  This is the missing mathematical bridge we want
to investigate; it is a proposition here, not an assumption added to the source
norm structure. -/
def HasSymmetricGaugeRepresentationSeparable
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∃ Φ : TauCeti.SymmetricGauge,
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [TopologicalSpace.SeparableSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      [TopologicalSpace.SeparableSpace F]
      (A : E →L[ℂ] F),
      N.toSymmetricOperatorIdealFamily.gauge A =
        Φ.extend (TauCeti.approxSeq A)

/-- The existing unrestricted Fan-dominance property certainly implies the
separable version.  This checks that `HasFanDominanceSeparable` is only a
restriction of the current target, not a different mathematical condition. -/
theorem hasFanDominanceSeparable_of_hasFanDominance
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) (h : N.HasFanDominance) :
    HasFanDominanceSeparable N := by
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
  exact h hAB

/-- **Main reduction probe.**

If a source norm has one symmetric sequence gauge representing it on every
separable Hilbert-space pair, then it has Fan dominance on exactly that
separable scope.

The proof uses only infrastructure already present in `ForTauCeti`:

* `approxSeq_antitone` for approximation-number sequences;
* the definition of the Ky Fan gauge as a finite prefix sum; and
* `SymmetricGauge.extend_le_extend_of_forall_sum_le`, the proved weak-majorization
  monotonicity of the extended symmetric gauge.

Thus a successful compile isolates the remaining gap to the representation
step. -/
theorem hasFanDominanceSeparable_of_symmetricGaugeRepresentation
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hrep : HasSymmetricGaugeRepresentationSeparable N) :
    HasFanDominanceSeparable N := by
  rcases hrep with ⟨Φ, hΦ⟩
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
  rw [hΦ A, hΦ B]
  apply Φ.extend_le_extend_of_forall_sum_le
    (TauCeti.approxSeq_antitone A)
  intro k
  have hk := hAB k
  simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge] at hk
  rw [show (∑ n ∈ Finset.range k, TauCeti.approxSeq A n) =
        ENNReal.ofReal (∑ n ∈ Finset.range k, A.approximationNumber n) by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun i _ => A.approximationNumber_nonneg i)]
      rfl,
    show (∑ n ∈ Finset.range k, TauCeti.approxSeq B n) =
        ENNReal.ofReal (∑ n ∈ Finset.range k, B.approximationNumber n) by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun i _ => B.approximationNumber_nonneg i)]
      rfl]
  exact ENNReal.ofReal_le_ofReal hk

/-!
## Probe 2: recover finite-dimensional Fan dominance directly from the source laws

The symmetric-gauge representation above is deliberately stronger than we
should expect for the entire source class.  In particular, this repository
already records source-like norms with a Calkin-quotient contribution: those
need not equal the maximal extension of their restriction to finite-rank
operators.

The next probe therefore avoids any infinite symmetric-gauge representation.
It asks only whether the source gauge, restricted to finite-dimensional
operator spaces, is already enough to feed the proved finite-dimensional Fan
dominance theorem.

There is one local hypothesis below: every finite-dimensional operator belongs
to the source ideal.  Rank-one normalization plus the ideal laws should imply
that hypothesis; keeping it separate in this probe lets the compiler test the
majorization route independently of the finite-rank decomposition needed to
prove membership.
-/

/-- Every operator between finite-dimensional complex Hilbert spaces belongs to
this source ideal.

This is an exploration predicate, not a new field.  The next probe will try to
derive it from rank-one normalization. -/
def HasFiniteDimensionalMembership
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →L[ℂ] F),
    N.toSymmetricOperatorIdealFamily.Mem A

/-- A linear isometric equivalence is a contraction.  Local copy of the tiny
fact used by the production source-norm façade; kept here so this exploration
does not depend on any Fan-dominant wrapper. -/
private theorem norm_isometryEquiv_le_one_finite
    {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (g : X ≃ₗᵢ[ℂ] Y) :
    ‖(g.toContinuousLinearEquiv : X →L[ℂ] Y)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp

/-- On finite-dimensional members, the source gauge is invariant under
unitaries on both sides.  This is derived from the ideal law in both directions,
not assumed. -/
theorem gaugeReal_comp_isometryEquiv_finite
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hfinite : HasFiniteDimensionalMembership N)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (e : F ≃ₗᵢ[ℂ] F) (f : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] F) :
    N.toSymmetricOperatorIdealFamily.gaugeReal
        ((e.toContinuousLinearEquiv : F →L[ℂ] F) ∘L A ∘L
          (f.toContinuousLinearEquiv : E →L[ℂ] E)) =
      N.toSymmetricOperatorIdealFamily.gaugeReal A := by
  let S := N.toSymmetricOperatorIdealFamily
  set B := (e.toContinuousLinearEquiv : F →L[ℂ] F) ∘L A ∘L
    (f.toContinuousLinearEquiv : E →L[ℂ] E) with hB
  change S.gaugeReal B = S.gaugeReal A
  have hA : S.Mem A := by
    simpa [S] using hfinite A
  have hBmem : S.Mem B := by
    simpa [S] using hfinite B
  have hAeq : A =
      (e.symm.toContinuousLinearEquiv : F →L[ℂ] F) ∘L B ∘L
        (f.symm.toContinuousLinearEquiv : E →L[ℂ] E) := by
    ext x
    simp [hB]
  refine le_antisymm ?_ ?_
  · calc
      S.gaugeReal B
          ≤ S.gaugeReal
              (A ∘L (f.toContinuousLinearEquiv : E →L[ℂ] E)) := by
            rw [hB, ← ContinuousLinearMap.comp_assoc]
            exact S.gaugeReal_comp_left_le _
              (S.comp_right_mem _ hA)
              (norm_isometryEquiv_le_one_finite e)
      _ ≤ S.gaugeReal A :=
          S.gaugeReal_comp_right_le _ hA
            (norm_isometryEquiv_le_one_finite f)
  · calc
      S.gaugeReal A =
          S.gaugeReal
            ((e.symm.toContinuousLinearEquiv : F →L[ℂ] F) ∘L B ∘L
              (f.symm.toContinuousLinearEquiv : E →L[ℂ] E)) := by
            rw [← hAeq]
      _ ≤ S.gaugeReal
              (B ∘L (f.symm.toContinuousLinearEquiv : E →L[ℂ] E)) := by
            rw [← ContinuousLinearMap.comp_assoc]
            exact S.gaugeReal_comp_left_le _
              (S.comp_right_mem _ hBmem)
              (norm_isometryEquiv_le_one_finite e.symm)
      _ ≤ S.gaugeReal B :=
          S.gaugeReal_comp_right_le _ hBmem
            (norm_isometryEquiv_le_one_finite f.symm)

/-- Restrict a source ideal gauge to finite-dimensional linear maps.  Under the
local membership hypothesis it is a rectangular unitarily invariant seminorm,
so the existing T-transform/Fan-dominance engine applies without any symmetric
sequence-gauge representation of the infinite-dimensional ideal. -/
noncomputable def finiteRectangularSeminorm
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hfinite : HasFiniteDimensionalMembership N)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] :
    TauCeti.UnitarilyInvariantSeminorm ℂ E F where
  toSeminorm := Seminorm.of
    (fun A => N.toSymmetricOperatorIdealFamily.gaugeReal A.toContinuousLinearMap)
    (fun A B => by
      let S := N.toSymmetricOperatorIdealFamily
      have hA : S.Mem A.toContinuousLinearMap := by
        simpa [S] using hfinite A.toContinuousLinearMap
      have hB : S.Mem B.toContinuousLinearMap := by
        simpa [S] using hfinite B.toContinuousLinearMap
      change S.gaugeReal (A + B).toContinuousLinearMap ≤
        S.gaugeReal A.toContinuousLinearMap + S.gaugeReal B.toContinuousLinearMap
      rw [map_add]
      exact S.gaugeReal_add_le hA hB)
    (fun c A => by
      let S := N.toSymmetricOperatorIdealFamily
      have hA : S.Mem A.toContinuousLinearMap := by
        simpa [S] using hfinite A.toContinuousLinearMap
      change S.gaugeReal (c • A).toContinuousLinearMap =
        ‖c‖ * S.gaugeReal A.toContinuousLinearMap
      rw [map_smul]
      exact S.gaugeReal_smul c hA)
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry
      (fun U V A => by
        let S := N.toSymmetricOperatorIdealFamily
        have hcomp :
            (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap =
              (U.toContinuousLinearEquiv : F →L[ℂ] F) ∘L
                A.toContinuousLinearMap ∘L
                  (V.toContinuousLinearEquiv : E →L[ℂ] E) := by
          ext x
          simp
        change S.gaugeReal
            (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap =
          S.gaugeReal A.toContinuousLinearMap
        rw [hcomp]
        simpa [S] using
          gaugeReal_comp_isometryEquiv_finite N hfinite U V
            A.toContinuousLinearMap)

/-- **Finite-dimensional reduction.**

Once finite-dimensional membership is known, the source laws already imply
Fan dominance for arbitrary rectangular finite-dimensional operators.  The
proof is exactly the existing rectangular T-transform theorem, with the bridge
from finite singular-value sums to approximation-number Ky Fan gauges. -/
theorem finiteDimensional_fanDominance_real
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hfinite : HasFiniteDimensionalMembership N)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {A B : E →L[ℂ] F}
    (hAB : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) :
    N.toSymmetricOperatorIdealFamily.gaugeReal A ≤
      N.toSymmetricOperatorIdealFamily.gaugeReal B := by
  have hlin : ∀ k,
      TauCeti.kyFanSum k A.toLinearMap ≤
        TauCeti.kyFanSum k B.toLinearMap := by
    intro k
    rw [kyFanSum_eq_kyFanApproximationGauge,
      kyFanSum_eq_kyFanApproximationGauge]
    have hA : A.toLinearMap.toContinuousLinearMap = A := by
      ext x
      rfl
    have hB : B.toLinearMap.toContinuousLinearMap = B := by
      ext x
      rfl
    rw [hA, hB]
    exact hAB k
  change (finiteRectangularSeminorm N hfinite) A.toLinearMap ≤
    (finiteRectangularSeminorm N hfinite) B.toLinearMap
  exact (finiteRectangularSeminorm N hfinite).apply_le_of_kyFanSum_le hlin

/-- The same finite-dimensional result at the canonical `ℝ≥0∞` gauge level,
which is the shape of `NormalizedSymmetricOperatorIdealFamily.HasFanDominance`. -/
theorem finiteDimensional_fanDominance
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hfinite : HasFiniteDimensionalMembership N)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {A B : E →L[ℂ] F}
    (hAB : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) :
    N.toSymmetricOperatorIdealFamily.gauge A ≤
      N.toSymmetricOperatorIdealFamily.gauge B := by
  have hA := hfinite A
  have hB := hfinite B
  apply (ENNReal.toReal_le_toReal hA hB).mp
  exact finiteDimensional_fanDominance_real N hfinite hAB

/-!
## Probe 3: finite-dimensional membership follows from the source laws

Probe 2 isolated one temporary hypothesis: that every operator between finite-
dimensional Hilbert spaces belongs to the source ideal.  This probe attempts to
remove that hypothesis without changing any production structure.

The argument is elementary.  A finite-dimensional operator has a finite
singular-value decomposition into scalar multiples of rank-one operators.  For
each nonzero singular term, both singular vectors have norm one, so the source's
rank-one normalization says the underlying rank-one operator has finite gauge.
The ideal is a submodule, hence it contains scalar multiples and finite sums.
-/

/-- The source normalization itself forces a norm-one rank-at-most-one operator
to be a member of the source ideal: an infinite `ENNReal` gauge would have
`toReal = 0`, contradicting the required value `1`.

This is the source-level analogue of `NormalizedUnitaryInvariantNorm.mem_rankOne`,
proved here without first bundling Fan dominance. -/
theorem source_mem_rankOne_unit
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {V : E →L[ℂ] F}
    (hVnorm : ‖V‖ = 1) (hVrank : V.rank ≤ (1 : Cardinal)) :
    N.toSymmetricOperatorIdealFamily.Mem V := by
  intro htop
  have h1 : (N.toSymmetricOperatorIdealFamily.gauge V).toReal = 1 :=
    N.gauge_rankOne_eq_one hVnorm hVrank
  rw [htop] at h1
  simp at h1

/-- A rank-one operator made from unit vectors has rank at most one.

The proof uses only the fact that its range lies in the span of its left vector;
it does not need a nonzero case split. -/
private theorem rankOne_rank_le_one
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (u : F) (v : E) :
    (InnerProductSpace.rankOne ℂ u v).rank ≤ (1 : Cardinal) := by
  classical
  have hle : LinearMap.range
      (((InnerProductSpace.rankOne ℂ u v : E →L[ℂ] F) : E →ₗ[ℂ] F)) ≤
      Submodule.span ℂ ({u} : Set F) := by
    rintro y ⟨x, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨inner ℂ v x, rfl⟩
  calc
    (InnerProductSpace.rankOne ℂ u v).rank
        ≤ Module.rank ℂ (Submodule.span ℂ ({u} : Set F)) :=
      Submodule.rank_mono hle
    _ ≤ 1 := by simpa using rank_span_le ({u} : Set F)

/-- **Probe 3 main statement.**  Every bounded operator between finite-
dimensional complex Hilbert spaces belongs to a source ideal using only the
source rank-one normalization and the ideal's submodule laws.

The singular-value decomposition already available in `ForTauCeti` supplies the
finite rank-one sum.  No Fan-dominance or symmetric-gauge representation theorem
is used. -/
theorem source_hasFiniteDimensionalMembership
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) :
    HasFiniteDimensionalMembership N := by
  intro E F _ _ _ _ _ _ A
  let S := N.toSymmetricOperatorIdealFamily
  let L := A.toLinearMap
  have hdecompLinear := TauCeti.eq_sum_singularValue_rankOne L
  have hdecomp : A =
      ∑ i : Fin (Module.finrank ℂ E),
        ((L.singularValues i : ℝ) : ℂ) •
          InnerProductSpace.rankOne ℂ
            (TauCeti.leftSingularVector L i)
            (TauCeti.rightSingularBasis L i) := by
    ext x
    have hx := LinearMap.congr_fun hdecompLinear x
    simpa [L] using hx
  change A ∈ S.toOperatorIdealFamily.carrier
  rw [hdecomp]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hσ : L.singularValues i = 0
  · simp [hσ]
  · apply Submodule.smul_mem
    have hu : ‖TauCeti.leftSingularVector L i‖ = 1 :=
      (TauCeti.orthonormal_leftSingularVector_subtype L).norm_eq_one ⟨i, hσ⟩
    have hv : ‖TauCeti.rightSingularBasis L i‖ = 1 :=
      (TauCeti.rightSingularBasis L).orthonormal.norm_eq_one i
    have hnorm : ‖InnerProductSpace.rankOne ℂ
        (TauCeti.leftSingularVector L i)
        (TauCeti.rightSingularBasis L i)‖ = 1 := by
      simp [hu, hv]
    have hrank : (InnerProductSpace.rankOne ℂ
        (TauCeti.leftSingularVector L i)
        (TauCeti.rightSingularBasis L i)).rank ≤ (1 : Cardinal) :=
      rankOne_rank_le_one _ _
    change S.Mem (InnerProductSpace.rankOne ℂ
      (TauCeti.leftSingularVector L i)
      (TauCeti.rightSingularBasis L i))
    simpa [S] using source_mem_rankOne_unit N hnorm hrank

/-- Probe 2's temporary finite-dimensional-membership hypothesis is therefore
unnecessary: finite-dimensional Fan dominance follows directly from the source
laws and the already-formalized rectangular majorization theorem. -/
theorem finiteDimensional_fanDominance_of_sourceLaws
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {A B : E →L[ℂ] F}
    (hAB : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) :
    N.toSymmetricOperatorIdealFamily.gauge A ≤
      N.toSymmetricOperatorIdealFamily.gauge B :=
  finiteDimensional_fanDominance N (source_hasFiniteDimensionalMembership N) hAB

/-!
## What remains after Probe 3

If Probe 3 compiles, the finite-dimensional part of the Fan-dominance boundary
is closed from the current `NormalizedSymmetricOperatorIdealFamily` laws themselves.  The
remaining source-level question is then genuinely infinite-dimensional:

* can finite-dimensional compressions/approximants transfer the source gauge
  inequality to arbitrary operators on the separable Hilbert spaces used by
  Davis--Kahan; or
* does that transfer require an additional regularity property (for example
  lower semicontinuity/order continuity) not encoded by the current source
  abstraction?

The next probe should attack exactly that finite-to-separable passage.  It
should not modify `NormalizedSymmetricOperatorIdealFamily`, and it should not assume a full
symmetric-gauge representation unless the source mathematics forces one.
-/


/-!
## Probe 4: what the source ideal laws already say about infinite-dimensional corners

The finite-dimensional probes above should not be mistaken for the source-level
result we need.  Before introducing any continuity or sequence-space hypothesis,
we can still ask exactly what follows from the source ideal law on an arbitrary
Hilbert space.

Two useful facts do follow with no Fan dominance:

* compression by an orthogonal projection cannot increase the source gauge;
* extension by zero across an orthogonal summand preserves the source gauge
  exactly.

The second fact is especially useful diagnostically.  It says that merely
changing the ambient Hilbert space by adding a zero summand is not the missing
infinite-dimensional step.  The missing step has to concern genuinely different
operators with the same or majorized approximation-number data.
-/

private theorem subtypeL_enorm_le_one
    {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : Submodule ℂ E) :
    ‖W.subtypeL‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal W.norm_subtypeL_le

private theorem orthogonalProjectionOnto_enorm_le_one
    {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] :
    ‖W.orthogonalProjectionOnto‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal W.orthogonalProjectionOnto_norm_le


private theorem isometryEquiv_enorm_le_one
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) :
    ‖(U.toContinuousLinearEquiv : E →L[ℂ] F)‖ₑ ≤ 1 := by
  have hreal : ‖(U.toContinuousLinearEquiv : E →L[ℂ] F)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simp
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The raw source ideal laws already imply exact invariance under unitary
left/right transport at the stored `ENNReal` gauge level.  This does not use
Fan dominance or finite membership. -/
theorem source_gauge_comp_isometryEquiv
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : F ≃ₗᵢ[ℂ] G) (f : H ≃ₗᵢ[ℂ] E)
    (A : E →L[ℂ] F) :
    N.toSymmetricOperatorIdealFamily.gauge
        ((e.toContinuousLinearEquiv : F →L[ℂ] G) ∘L A ∘L
          (f.toContinuousLinearEquiv : H →L[ℂ] E)) =
      N.toSymmetricOperatorIdealFamily.gauge A := by
  let S := N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily
  let B : H →L[ℂ] G :=
    (e.toContinuousLinearEquiv : F →L[ℂ] G) ∘L A ∘L
      (f.toContinuousLinearEquiv : H →L[ℂ] E)
  have hBA : S.gauge B ≤ S.gauge A := by
    exact S.gauge_comp_le_of_norm_le_one
      (isometryEquiv_enorm_le_one e) (isometryEquiv_enorm_le_one f)
  have hfact : A =
      (e.symm.toContinuousLinearEquiv : G →L[ℂ] F) ∘L B ∘L
        (f.symm.toContinuousLinearEquiv : E →L[ℂ] H) := by
    ext x
    simp [B]
  have hAB : S.gauge A ≤ S.gauge B := by
    rw [hfact]
    exact S.gauge_comp_le_of_norm_le_one
      (isometryEquiv_enorm_le_one e.symm)
      (isometryEquiv_enorm_le_one f.symm)
  exact le_antisymm hBA hAB

/-- Source-law invariance under the operator modulus.  The polar partial
isometry and its adjoint are contractions, so the two polar factorizations give
the two gauge inequalities directly. -/
theorem source_gauge_modulus_eq
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) :
    N.toSymmetricOperatorIdealFamily.gauge T.modulus =
      N.toSymmetricOperatorIdealFamily.gauge T := by
  let S := N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily
  have hnorms :=
    TauCeti.DavisKahan.SharedFoundations.Ideal.polarPartial_and_adjoint_norm_le_one T
  have hU : ‖T.polarPartial‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hnorms.1
  have hUa : ‖T.polarPartial.adjoint‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hnorms.2
  apply le_antisymm
  · calc
      S.gauge T.modulus = S.gauge (T.polarPartial.adjoint ∘L T) := by
        rw [T.adjoint_polarPartial_comp_self]
      _ ≤ S.gauge T := S.gauge_comp_left_le_of_norm_le_one hUa T
  · calc
      S.gauge T = S.gauge (T.polarPartial ∘L T.modulus) := by
        rw [T.polarPartial_comp_modulus]
      _ ≤ S.gauge T.modulus :=
        S.gauge_comp_left_le_of_norm_le_one hU T.modulus

/-- Source-law control of a square compression.  No Fan-dominance hypothesis is
used. -/
theorem source_gauge_compression_le
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] [CompleteSpace W]
    (A : E →L[ℂ] E) :
    N.toSymmetricOperatorIdealFamily.gauge
        (W.orthogonalProjectionOnto ∘L A ∘L W.subtypeL) ≤
      N.toSymmetricOperatorIdealFamily.gauge A := by
  let S := N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily
  exact S.gauge_comp_le_of_norm_le_one
    (orthogonalProjectionOnto_enorm_le_one W)
    (subtypeL_enorm_le_one W)

/-- Extension by zero across an orthogonal summand preserves the source gauge
exactly, using only the two-sided ideal law. -/
theorem source_gauge_zeroExtension_eq
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] [CompleteSpace W]
    (A : W →L[ℂ] W) :
    N.toSymmetricOperatorIdealFamily.gauge
        (W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto) =
      N.toSymmetricOperatorIdealFamily.gauge A := by
  let S := N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily
  let Z : E →L[ℂ] E := W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto
  have hsub := subtypeL_enorm_le_one W
  have hproj := orthogonalProjectionOnto_enorm_le_one W
  have hZA : S.gauge Z ≤ S.gauge A := by
    exact S.gauge_comp_le_of_norm_le_one hsub hproj
  have hfact : A = W.orthogonalProjectionOnto ∘L Z ∘L W.subtypeL := by
    refine ContinuousLinearMap.ext fun x => ?_
    have h1 : W.orthogonalProjectionOnto ((x : E)) = x :=
      Subtype.ext (Submodule.starProjection_eq_self_iff.mpr x.2)
    have h2 : W.orthogonalProjectionOnto ((A x : W) : E) = A x :=
      Subtype.ext (Submodule.starProjection_eq_self_iff.mpr (A x).2)
    change A x = W.orthogonalProjectionOnto
      ((A (W.orthogonalProjectionOnto (x : E)) : W) : E)
    rw [h1, h2]
  have hAZ : S.gauge A ≤ S.gauge Z := by
    rw [hfact]
    exact S.gauge_comp_le_of_norm_le_one hproj hsub
  exact le_antisymm hZA hAZ

/-- The same zero extension also preserves every approximation number.  This
packages the pre-existing approximation-number theorem with the source-gauge
calculation above and verifies that this elementary ambient-space transport is
already completely invisible on both sides. -/
theorem source_zeroExtension_sameSequence_and_gauge
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] [CompleteSpace W]
    (A : W →L[ℂ] W) :
    A.HasSameApproximationNumbers
        (W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto) ∧
      N.toSymmetricOperatorIdealFamily.gauge A =
        N.toSymmetricOperatorIdealFamily.gauge
          (W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto) := by
  constructor
  · rw [ContinuousLinearMap.hasSameApproximationNumbers_iff]
    intro n
    exact (TauCeti.ApproximationNumber.approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto
      W A n).symm
  · exact (source_gauge_zeroExtension_eq N W A).symm

/-!
## Probe 5: every approximation-number sequence has a representative on one infinite model

The next reduction is genuinely infinite-dimensional.  On any fixed
infinite-dimensional Hilbert space `H`, the existing prescribed-sequence theorem
realises the complete approximation-number sequence of *any* bounded operator
as the sequence of a square operator on `H`.

This avoids choosing `ℓ²` as a global model (the pinned Mathlib does not expose a
`SeparableSpace` instance for its `lp` model) and keeps the universe of the model
space aligned with the source norm family.
-/

/-- Every bounded operator has a square representative with exactly the same
approximation-number sequence on any chosen infinite-dimensional Hilbert space. -/
theorem exists_sameApproximationNumbers_on_infiniteHilbert
    {E F H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hinf : ¬ FiniteDimensional ℂ H)
    (A : E →L[ℂ] F) :
    ∃ D : H →L[ℂ] H, A.HasSameApproximationNumbers D := by
  obtain ⟨D, hD⟩ :=
    TauCeti.ApproximationNumber.exists_approximationNumber_eq_of_antitone
      (𝕜 := ℂ) hinf
      (fun n => A.approximationNumber n)
      (fun n => A.approximationNumber_nonneg n)
      A.approximationNumber_antitone
  refine ⟨D, ?_⟩
  rw [ContinuousLinearMap.hasSameApproximationNumbers_iff]
  intro n
  exact (hD n).symm

/-!
## Probe 6: isolate approximation-sequence invariance

The source laws certainly make the gauge invariant under explicit unitary
transport and, by Probe 4, under zero extension.  A much stronger statement is
that *any* two separable-space operators with the same complete approximation-
number sequence have the same source gauge.

This property is not assumed below to follow from the source laws.  It is named
as a local proposition so we can determine exactly how much of the full Fan-
dominance theorem would follow from it.
-/

/-- The source gauge factors through the complete approximation-number sequence
on separable Hilbert spaces. -/
def HasApproximationNumberGaugeInvarianceSeparable
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [TopologicalSpace.SeparableSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    [TopologicalSpace.SeparableSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    A.HasSameApproximationNumbers B →
      N.toSymmetricOperatorIdealFamily.gauge A =
        N.toSymmetricOperatorIdealFamily.gauge B

/-- Separable Fan dominance implies approximation-sequence invariance.  This is
a sanity check that the new predicate really is a necessary component of the
target rather than an unrelated extra assumption. -/
theorem hasApproximationNumberGaugeInvarianceSeparable_of_fanDominance
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hfan : HasFanDominanceSeparable N) :
    HasApproximationNumberGaugeInvarianceSeparable N := by
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hsame
  apply le_antisymm
  · apply hfan
    intro k
    change A.kyFanGauge k ≤ B.kyFanGauge k
    exact (hsame.kyFanGauge_eq k).le
  · apply hfan
    intro k
    change B.kyFanGauge k ≤ A.kyFanGauge k
    exact (hsame.kyFanGauge_eq k).ge

/-- The stronger production `HasFanDominance` property therefore also implies
separable sequence invariance. -/
theorem hasApproximationNumberGaugeInvarianceSeparable_of_hasFanDominance
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hfan : N.HasFanDominance) :
    HasApproximationNumberGaugeInvarianceSeparable N :=
  hasApproximationNumberGaugeInvarianceSeparable_of_fanDominance N
    (hasFanDominanceSeparable_of_hasFanDominance N hfan)

/-- A symmetric-gauge representation implies sequence invariance directly.
This reconnects Probe 1 with the weaker intermediate property isolated here. -/
theorem hasApproximationNumberGaugeInvarianceSeparable_of_symmetricGaugeRepresentation
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hrep : HasSymmetricGaugeRepresentationSeparable N) :
    HasApproximationNumberGaugeInvarianceSeparable N := by
  rcases hrep with ⟨Φ, hΦ⟩
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hsame
  rw [hΦ A, hΦ B]
  apply congrArg Φ.extend
  funext n
  apply congrArg ENNReal.ofReal
  exact (ContinuousLinearMap.hasSameApproximationNumbers_iff A B).mp hsame n

/-!
## Probe 6b: a genuinely infinite-dimensional compact subclass

There is already an infinite-dimensional classification theorem in `ForTauCeti`:
compact positive self-adjoint operators with trivial kernel and the same complete
approximation-number sequence are unitarily equivalent.  Combining that theorem
with the source-law unitary invariance from Probe 4 gives sequence invariance on
this compact subclass *without* Fan dominance.

This is useful because it shows that the remaining sequence-invariance problem
is not simply "infinite dimension".  The hard part is extending beyond a class
where the full operator is classified by its discrete singular data, especially
toward noncompact operators carrying essential/Calkin information.
-/

/-- Source-gauge sequence invariance for compact positive self-adjoint square
operators with trivial kernel. -/
theorem source_gauge_eq_of_compactPositive_sameApproximationNumbers
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hA0 : Module.End.eigenspace A.toLinearMap 0 = ⊥)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B)
    (hBpos : ∀ x, 0 ≤ RCLike.re ⟪B x, x⟫_ℂ)
    (hB0 : Module.End.eigenspace B.toLinearMap 0 = ⊥)
    (hsame : A.HasSameApproximationNumbers B) :
    N.toSymmetricOperatorIdealFamily.gauge A =
      N.toSymmetricOperatorIdealFamily.gauge B := by
  have hAB : ∀ n, A.approximationNumber n = B.approximationNumber n :=
    (ContinuousLinearMap.hasSameApproximationNumbers_iff A B).mp hsame
  obtain ⟨W, hW⟩ :=
    TauCeti.exists_linearIsometryEquiv_intertwining_of_approximationNumber_eq
      hAc hAs hApos hA0 hBc hBs hBpos hB0 hAB
  have hBfact : B =
      (W.toContinuousLinearEquiv : E →L[ℂ] F) ∘L A ∘L
        (W.symm.toContinuousLinearEquiv : F →L[ℂ] E) := by
    ext y
    have hy := hW (W.symm y)
    simpa using hy.symm
  rw [hBfact]
  exact (source_gauge_comp_isometryEquiv N W W.symm A).symm

/-- Fan dominance restricted to square operators on one fixed Hilbert space. -/
def HasFanDominanceOnSquare
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ {A B : H →L[ℂ] H},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-!
## Probe 6c: reduce the one-space problem to positive operators

Probe 4 showed that the source gauge itself is unchanged by the operator
modulus.  Approximation numbers are also unchanged by the modulus.  Therefore
Fan dominance for arbitrary square operators on a fixed Hilbert space is
already equivalent to Fan dominance for positive square operators there.

This removes polar decomposition from the remaining hard theorem: after this
probe the one-space obstruction is a comparison theorem for positive operators,
where spectral/diagonal approximation machinery is the natural next target.
-/

/-- Fan dominance restricted to positive square operators on one fixed Hilbert
space. -/
def HasFanDominanceOnPositiveSquare
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ {A B : H →L[ℂ] H},
    0 ≤ A → 0 ≤ B →
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- Positive-square dominance is sufficient for arbitrary square dominance by
passing both operators to their moduli. -/
theorem hasFanDominanceOnSquare_of_positive
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hpos : HasFanDominanceOnPositiveSquare N H) :
    HasFanDominanceOnSquare N H := by
  intro A B hAB
  have hAseq := ContinuousLinearMap.modulus_hasSameApproximationNumbers A
  have hBseq := ContinuousLinearMap.modulus_hasSameApproximationNumbers B
  have hmodAB : ∀ k,
      kyFanApproximationGauge k A.modulus ≤
        kyFanApproximationGauge k B.modulus := by
    intro k
    have hk := hAB k
    change A.kyFanGauge k ≤ B.kyFanGauge k at hk
    change A.modulus.kyFanGauge k ≤ B.modulus.kyFanGauge k
    calc
      A.modulus.kyFanGauge k = A.kyFanGauge k := hAseq.kyFanGauge_eq k
      _ ≤ B.kyFanGauge k := hk
      _ = B.modulus.kyFanGauge k := (hBseq.kyFanGauge_eq k).symm
  have h := hpos A.modulus_nonneg B.modulus_nonneg hmodAB
  rw [source_gauge_modulus_eq N A, source_gauge_modulus_eq N B] at h
  exact h

/-- Arbitrary square dominance obviously implies its positive restriction. -/
theorem hasFanDominanceOnPositiveSquare_of_square
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (h : HasFanDominanceOnSquare N H) :
    HasFanDominanceOnPositiveSquare N H := by
  intro A B _ _ hAB
  exact h hAB

/-- The one-space Fan-dominance problem is exactly the positive one-space
problem; no sequence-invariance assumption is needed for this reduction. -/
theorem fanDominanceOnSquare_iff_positive
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    HasFanDominanceOnSquare N H ↔ HasFanDominanceOnPositiveSquare N H := by
  constructor
  · exact hasFanDominanceOnPositiveSquare_of_square N
  · exact hasFanDominanceOnSquare_of_positive N

/-!
## Probe 7: reduce the entire separable problem to one infinite model space

For a chosen infinite-dimensional separable Hilbert space `H`, define the
remaining dominance problem only for square operators on `H`.  Probe 5 lets us
move the complete approximation-number sequence of arbitrary rectangular
operators onto `H`.  Therefore, if the source gauge is sequence-invariant, Fan
dominance on this one model space is enough for the full heterogeneous separable
statement.

This is the main infinite-dimensional reduction probe.  It does not use the
finite-dimensional result at all.
-/

/-- The full separable target trivially contains the one-model-space target. -/
theorem hasFanDominanceOnSquare_of_fanDominanceSeparable
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hfan : HasFanDominanceSeparable N) :
    HasFanDominanceOnSquare N H := by
  intro A B hAB
  exact hfan hAB

/-- **Main model-space reduction.**

Assume `H` is one infinite-dimensional separable Hilbert space in the relevant
universe.  Then sequence invariance plus Fan dominance for square operators on
`H` implies the complete heterogeneous separable Fan-dominance statement.

No finite-dimensional approximation, density, compactness, or symmetric-gauge
representation is used. -/
theorem hasFanDominanceSeparable_of_sequenceInvariance_and_modelSpace
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hinf : ¬ FiniteDimensional ℂ H)
    (hseq : HasApproximationNumberGaugeInvarianceSeparable N)
    (hH : HasFanDominanceOnSquare N H) :
    HasFanDominanceSeparable N := by
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
  obtain ⟨DA, hAseq⟩ :=
    exists_sameApproximationNumbers_on_infiniteHilbert hinf A
  obtain ⟨DB, hBseq⟩ :=
    exists_sameApproximationNumbers_on_infiniteHilbert hinf B
  have hAgauge : N.toSymmetricOperatorIdealFamily.gauge A =
      N.toSymmetricOperatorIdealFamily.gauge DA := hseq hAseq
  have hBgauge : N.toSymmetricOperatorIdealFamily.gauge B =
      N.toSymmetricOperatorIdealFamily.gauge DB := hseq hBseq
  have hDAB : ∀ k,
      kyFanApproximationGauge k DA ≤ kyFanApproximationGauge k DB := by
    intro k
    have hk := hAB k
    change A.kyFanGauge k ≤ B.kyFanGauge k at hk
    change DA.kyFanGauge k ≤ DB.kyFanGauge k
    calc
      DA.kyFanGauge k = A.kyFanGauge k := (hAseq.kyFanGauge_eq k).symm
      _ ≤ B.kyFanGauge k := hk
      _ = DB.kyFanGauge k := hBseq.kyFanGauge_eq k
  rw [hAgauge, hBgauge]
  exact hH hDAB

/-- On any fixed infinite-dimensional separable model space, the full
separable Fan-dominance problem is equivalent to exactly two obligations:

1. source-gauge invariance under equality of the complete approximation-number
   sequence; and
2. Fan dominance for square operators on that one model space.

This equivalence is the main output of the new probes. -/
theorem fanDominanceSeparable_iff_sequenceInvariance_and_modelSpace
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hinf : ¬ FiniteDimensional ℂ H) :
    HasFanDominanceSeparable N ↔
      HasApproximationNumberGaugeInvarianceSeparable N ∧
        HasFanDominanceOnSquare N H := by
  constructor
  · intro hfan
    exact ⟨hasApproximationNumberGaugeInvarianceSeparable_of_fanDominance N hfan,
      hasFanDominanceOnSquare_of_fanDominanceSeparable N hfan⟩
  · rintro ⟨hseq, hH⟩
    exact hasFanDominanceSeparable_of_sequenceInvariance_and_modelSpace
      N hinf hseq hH

/-- Combining the model-space and modulus reductions gives the sharpest
factorization found by these probes: on any chosen infinite-dimensional
separable model space, full separable Fan dominance is equivalent to sequence
invariance plus Fan dominance only for positive operators on that model. -/
theorem fanDominanceSeparable_iff_sequenceInvariance_and_positiveModel
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hinf : ¬ FiniteDimensional ℂ H) :
    HasFanDominanceSeparable N ↔
      HasApproximationNumberGaugeInvarianceSeparable N ∧
        HasFanDominanceOnPositiveSquare N H := by
  rw [fanDominanceSeparable_iff_sequenceInvariance_and_modelSpace N hinf,
    fanDominanceOnSquare_iff_positive N]

/-!
## Probe 8: a conditional one-space criterion

The previous equivalence suggests a useful next implementation boundary.  If we
can prove sequence invariance from the source UIN laws, the heterogeneous
Davis--Kahan norm problem collapses to a theorem about square operators on one
infinite-dimensional separable Hilbert space.  Conversely, proving only the
one-space theorem is not enough unless sequence invariance is also established.

This final probe records both implications explicitly so later experiments can
attack them independently without changing the source structure.
-/

/-- Once sequence invariance has been established, one-space Fan dominance and
the full separable statement are equivalent. -/
theorem fanDominanceSeparable_iff_modelSpace_of_sequenceInvariance
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hinf : ¬ FiniteDimensional ℂ H)
    (hseq : HasApproximationNumberGaugeInvarianceSeparable N) :
    HasFanDominanceSeparable N ↔ HasFanDominanceOnSquare N H := by
  constructor
  · exact hasFanDominanceOnSquare_of_fanDominanceSeparable N
  · intro hH
    exact hasFanDominanceSeparable_of_sequenceInvariance_and_modelSpace
      N hinf hseq hH

/-!
## What these probes are intended to decide

A clean compile would establish the following reduction map without changing
any production definition:

```
source UIN laws
   │
   ├─ finite-dimensional Fan dominance                         [Probe 3: proved]
   │
   ├─ compression ≤ ambient gauge; zero extension = same gauge [Probe 4]
   │
   └─ arbitrary separable Fan dominance
          ⇕   (for any chosen infinite-dimensional separable H)
      sequence invariance
          +
      Fan dominance on positive square operators H → H         [Probes 5--8]
```

The important point is negative as well as positive: none of Probes 4--8 claims
that finite-dimensional corners recover the value of an arbitrary source UIN.
That recovery would exclude source-class examples with a genuine essential or
Calkin contribution.  The next mathematical attack, after compilation, should
therefore target the two obligations exposed by Probe 7 rather than return to
finite-dimensional density.
-/

/-!
## Probe 9: rectangular operators already reduce to their positive modulus

Probe 6c used the modulus only for square operators.  That leaves an avoidable
artifact in the later model-space reduction, because the Davis--Kahan norm
comparisons themselves are rectangular.  The polar decomposition is already
rectangular: for `T : E → F`, `T = W |T|` and `|T| = W⋆ T`, with both `W` and
`W⋆` contractions.  Hence the raw source ideal laws identify the gauge of `T`
with the gauge of the positive square operator `|T|` on its domain.

This probe is important because it makes the codomain dimension irrelevant to
the remaining Fan-dominance problem.
-/

private theorem norm_polarPartial_le_one_rectangular
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) :
    ‖T.polarPartial‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, T.polarPartial_apply, T.norm_polarInitialMap_apply]
  exact T.polarInitial.norm_orthogonalProjectionOnto_apply_le x

private theorem polarPartial_and_adjoint_enorm_le_one_rectangular
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) :
    ‖T.polarPartial‖ₑ ≤ 1 ∧ ‖T.polarPartial.adjoint‖ₑ ≤ 1 := by
  have hU : ‖T.polarPartial‖ ≤ 1 := norm_polarPartial_le_one_rectangular T
  have hUa : ‖T.polarPartial.adjoint‖ ≤ 1 := by
    calc
      ‖T.polarPartial.adjoint‖ = ‖T.polarPartial‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hU
  constructor <;> rw [← ofReal_norm, ← ENNReal.ofReal_one]
  · exact ENNReal.ofReal_le_ofReal hU
  · exact ENNReal.ofReal_le_ofReal hUa

/-- **Rectangular modulus reduction from the source laws alone.** -/
theorem source_gauge_modulus_eq_rectangular
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) :
    N.toSymmetricOperatorIdealFamily.gauge T.modulus =
      N.toSymmetricOperatorIdealFamily.gauge T := by
  let S := N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily
  have hnorms := polarPartial_and_adjoint_enorm_le_one_rectangular T
  apply le_antisymm
  · calc
      S.gauge T.modulus = S.gauge (T.polarPartial.adjoint ∘L T) := by
        rw [T.adjoint_polarPartial_comp_self]
      _ ≤ S.gauge T :=
        S.gauge_comp_left_le_of_norm_le_one hnorms.2 T
  · calc
      S.gauge T = S.gauge (T.polarPartial ∘L T.modulus) := by
        rw [T.polarPartial_comp_modulus]
      _ ≤ S.gauge T.modulus :=
        S.gauge_comp_left_le_of_norm_le_one hnorms.1 T.modulus

/-!
## Probe 10: exact transport between infinite separable Hilbert spaces

The repository already proves the Hilbert-space classification theorem needed
here: any two infinite-dimensional separable Hilbert spaces over the same field
are linearly isometrically equivalent.  Consequently, on the all-infinite part
of the source scope we do not need the approximation-sequence-invariance
hypothesis from Probe 7 merely to move operators to a common model space.

The two local lemmas below record that a unitary coordinate change preserves
both the source gauge and every approximation number.
-/

private theorem isometryEquiv_norm_le_one
    {E F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) :
    ‖(U.toContinuousLinearEquiv : E →L[ℂ] F)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp

private theorem approximationNumber_comp_isometryEquiv_le
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    (U : F₁ ≃ₗᵢ[ℂ] F₂) (V : E₂ ≃ₗᵢ[ℂ] E₁)
    (A : E₁ →L[ℂ] F₁) (n : ℕ) :
    ((U.toContinuousLinearEquiv : F₁ →L[ℂ] F₂) ∘L A ∘L
        (V.toContinuousLinearEquiv : E₂ →L[ℂ] E₁)).approximationNumber n ≤
      A.approximationNumber n := by
  have hU := isometryEquiv_norm_le_one U
  have hV := isometryEquiv_norm_le_one V
  calc
    ((U.toContinuousLinearEquiv : F₁ →L[ℂ] F₂) ∘L A ∘L
          (V.toContinuousLinearEquiv : E₂ →L[ℂ] E₁)).approximationNumber n
        ≤ ‖(U.toContinuousLinearEquiv : F₁ →L[ℂ] F₂)‖ *
            A.approximationNumber n *
            ‖(V.toContinuousLinearEquiv : E₂ →L[ℂ] E₁)‖ :=
      ContinuousLinearMap.approximationNumber_comp_comp_le _ _ _ n
    _ ≤ 1 * A.approximationNumber n * 1 := by
      gcongr <;>
        first
          | assumption
          | simpa using A.approximationNumber_nonneg n
    _ = A.approximationNumber n := by ring

private theorem approximationNumber_comp_isometryEquiv_eq
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    (U : F₁ ≃ₗᵢ[ℂ] F₂) (V : E₂ ≃ₗᵢ[ℂ] E₁)
    (A : E₁ →L[ℂ] F₁) (n : ℕ) :
    ((U.toContinuousLinearEquiv : F₁ →L[ℂ] F₂) ∘L A ∘L
        (V.toContinuousLinearEquiv : E₂ →L[ℂ] E₁)).approximationNumber n =
      A.approximationNumber n := by
  apply le_antisymm
  · exact approximationNumber_comp_isometryEquiv_le U V A n
  · let B : E₂ →L[ℂ] F₂ :=
      (U.toContinuousLinearEquiv : F₁ →L[ℂ] F₂) ∘L A ∘L
        (V.toContinuousLinearEquiv : E₂ →L[ℂ] E₁)
    have hfac : A =
        (U.symm.toContinuousLinearEquiv : F₂ →L[ℂ] F₁) ∘L B ∘L
          (V.symm.toContinuousLinearEquiv : E₁ →L[ℂ] E₂) := by
      ext x
      simp [B]
    calc
      A.approximationNumber n =
          ((U.symm.toContinuousLinearEquiv : F₂ →L[ℂ] F₁) ∘L B ∘L
            (V.symm.toContinuousLinearEquiv : E₁ →L[ℂ] E₂)).approximationNumber n := by
        rw [hfac]
      _ ≤ B.approximationNumber n :=
        approximationNumber_comp_isometryEquiv_le U.symm V.symm B n

/-- Unitary conjugation of a square operator preserves both the complete
approximation-number sequence and the source gauge. -/
theorem source_conjugation_sameSequence_and_gauge
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : E ≃ₗᵢ[ℂ] H) (A : E →L[ℂ] E) :
    let B : H →L[ℂ] H :=
      (U.toContinuousLinearEquiv : E →L[ℂ] H) ∘L A ∘L
        (U.symm.toContinuousLinearEquiv : H →L[ℂ] E)
    B.HasSameApproximationNumbers A ∧
      N.toSymmetricOperatorIdealFamily.gauge B =
        N.toSymmetricOperatorIdealFamily.gauge A := by
  dsimp
  constructor
  · rw [ContinuousLinearMap.hasSameApproximationNumbers_iff]
    intro n
    exact approximationNumber_comp_isometryEquiv_eq U U.symm A n
  · exact source_gauge_comp_isometryEquiv N U U.symm A

/-!
## Probe 11: the all-infinite source scope needs no sequence-invariance axiom

After the rectangular modulus reduction, only the *domains* of the two compared
operators matter.  If both are infinite-dimensional and separable, Hilbert-space
classification moves their positive moduli to one fixed infinite separable model
space by honest unitary equivalence.  This is stronger than Probe 7: no arbitrary
same-sequence replacement is used.
-/

/-- Fan dominance restricted to comparisons whose two operator domains are
infinite-dimensional separable Hilbert spaces.  The codomains remain arbitrary
separable Hilbert spaces. -/
def HasFanDominanceOnInfiniteSeparableDomains
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [TopologicalSpace.SeparableSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    [TopologicalSpace.SeparableSpace F']
    (_hE : ¬ FiniteDimensional ℂ E)
    (_hE' : ¬ FiniteDimensional ℂ E')
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- Fan dominance on one infinite separable model space implies every
all-infinite separable rectangular comparison, using only rectangular modulus
and unitary equivalence of separable infinite-dimensional Hilbert spaces. -/
theorem hasFanDominanceOnInfiniteSeparableDomains_of_modelSpace
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hHinf : ¬ FiniteDimensional ℂ H)
    (hH : HasFanDominanceOnSquare N H) :
    HasFanDominanceOnInfiniteSeparableDomains N := by
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE hE' A B hAB
  obtain ⟨U⟩ :=
    TauCeti.nonempty_linearIsometryEquiv_of_separable_of_infiniteDimensional
      (𝕜 := ℂ) hE hHinf
  obtain ⟨V⟩ :=
    TauCeti.nonempty_linearIsometryEquiv_of_separable_of_infiniteDimensional
      (𝕜 := ℂ) hE' hHinf
  let DA : H →L[ℂ] H :=
    (U.toContinuousLinearEquiv : E →L[ℂ] H) ∘L A.modulus ∘L
      (U.symm.toContinuousLinearEquiv : H →L[ℂ] E)
  let DB : H →L[ℂ] H :=
    (V.toContinuousLinearEquiv : E' →L[ℂ] H) ∘L B.modulus ∘L
      (V.symm.toContinuousLinearEquiv : H →L[ℂ] E')
  have hDA := source_conjugation_sameSequence_and_gauge N U A.modulus
  have hDB := source_conjugation_sameSequence_and_gauge N V B.modulus
  have hAmod := ContinuousLinearMap.modulus_hasSameApproximationNumbers A
  have hBmod := ContinuousLinearMap.modulus_hasSameApproximationNumbers B
  have hDAB : ∀ k, kyFanApproximationGauge k DA ≤
      kyFanApproximationGauge k DB := by
    intro k
    have hk := hAB k
    change A.kyFanGauge k ≤ B.kyFanGauge k at hk
    change DA.kyFanGauge k ≤ DB.kyFanGauge k
    calc
      DA.kyFanGauge k = A.modulus.kyFanGauge k := hDA.1.kyFanGauge_eq k
      _ = A.kyFanGauge k := hAmod.kyFanGauge_eq k
      _ ≤ B.kyFanGauge k := hk
      _ = B.modulus.kyFanGauge k := (hBmod.kyFanGauge_eq k).symm
      _ = DB.kyFanGauge k := (hDB.1.kyFanGauge_eq k).symm
  have hmodel : N.toSymmetricOperatorIdealFamily.gauge DA ≤
      N.toSymmetricOperatorIdealFamily.gauge DB := hH hDAB
  calc
    N.toSymmetricOperatorIdealFamily.gauge A =
        N.toSymmetricOperatorIdealFamily.gauge A.modulus :=
      (source_gauge_modulus_eq_rectangular N A).symm
    _ = N.toSymmetricOperatorIdealFamily.gauge DA := hDA.2.symm
    _ ≤ N.toSymmetricOperatorIdealFamily.gauge DB := hmodel
    _ = N.toSymmetricOperatorIdealFamily.gauge B.modulus := hDB.2
    _ = N.toSymmetricOperatorIdealFamily.gauge B :=
      source_gauge_modulus_eq_rectangular N B

/-- Conversely, the all-infinite predicate contains the one-model-space square
case. -/
theorem hasFanDominanceOnSquare_of_infiniteSeparableDomains
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hHinf : ¬ FiniteDimensional ℂ H)
    (h : HasFanDominanceOnInfiniteSeparableDomains N) :
    HasFanDominanceOnSquare N H := by
  intro A B hAB
  exact h hHinf hHinf hAB

/-- **Sharp all-infinite reduction.**  On any fixed infinite-dimensional
separable model space, Fan dominance there is equivalent to Fan dominance for
all rectangular comparisons whose two domains are infinite-dimensional and
separable. -/
theorem fanDominanceInfiniteSeparable_iff_modelSpace
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hHinf : ¬ FiniteDimensional ℂ H) :
    HasFanDominanceOnInfiniteSeparableDomains N ↔ HasFanDominanceOnSquare N H := by
  constructor
  · exact hasFanDominanceOnSquare_of_infiniteSeparableDomains N hHinf
  · exact hasFanDominanceOnInfiniteSeparableDomains_of_modelSpace N hHinf

/-- The same all-infinite reduction can be stated using only positive operators
on the fixed model space. -/
theorem fanDominanceInfiniteSeparable_iff_positiveModel
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hHinf : ¬ FiniteDimensional ℂ H) :
    HasFanDominanceOnInfiniteSeparableDomains N ↔
      HasFanDominanceOnPositiveSquare N H := by
  rw [fanDominanceInfiniteSeparable_iff_modelSpace N hHinf,
    fanDominanceOnSquare_iff_positive N]

/-!
## Probe 12: isolate the cross-dimensional comparisons

The previous probe removes sequence invariance from the all-infinite case.  The
full separable source statement still allows the two domains to have different
Hilbert dimensions.  Rather than bury that issue inside a global same-sequence
axiom, this probe splits the target into three disjoint pieces:

* both domains finite-dimensional;
* both domains infinite-dimensional; and
* exactly one domain finite-dimensional.

This is a logical decomposition, but it is useful because only the third class
can no longer be transported to a common model by a unitary equivalence.  Those
mixed comparisons are therefore the next place where an essential/Calkin
contribution or an infinite-completion issue can actually matter.
-/

/-- Fan dominance when both operator domains are finite-dimensional. -/
def HasFanDominanceOnFiniteSeparableDomains
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [TopologicalSpace.SeparableSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    [TopologicalSpace.SeparableSpace F']
    (_hE : FiniteDimensional ℂ E)
    (_hE' : FiniteDimensional ℂ E')
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- Fan dominance in the genuinely cross-dimensional case: exactly one of the
two operator domains is finite-dimensional. -/
def HasFanDominanceOnMixedSeparableDomains
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [TopologicalSpace.SeparableSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    [TopologicalSpace.SeparableSpace F']
    (_hmixed :
      (FiniteDimensional ℂ E ∧ ¬ FiniteDimensional ℂ E') ∨
        (¬ FiniteDimensional ℂ E ∧ FiniteDimensional ℂ E'))
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- The complete separable target is exactly finite/finite + infinite/infinite
+ mixed-domain dominance. -/
theorem fanDominanceSeparable_iff_dimensionSplit
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) :
    HasFanDominanceSeparable N ↔
      HasFanDominanceOnFiniteSeparableDomains N ∧
      HasFanDominanceOnInfiniteSeparableDomains N ∧
      HasFanDominanceOnMixedSeparableDomains N := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
      exact h hAB
    · intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
      exact h hAB
    · intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
      exact h hAB
  · rintro ⟨hfin, hinf, hmixed⟩
    intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
    classical
    by_cases hE : FiniteDimensional ℂ E
    · by_cases hE' : FiniteDimensional ℂ E'
      · exact hfin hE hE' hAB
      · exact hmixed (Or.inl ⟨hE, hE'⟩) hAB
    · by_cases hE' : FiniteDimensional ℂ E'
      · exact hmixed (Or.inr ⟨hE, hE'⟩) hAB
      · exact hinf hE hE' hAB

/-- Combining the dimension split with Probe 11 identifies a smaller remaining
boundary: after choosing one infinite separable model space, the full source
claim consists of the positive-model theorem plus the finite/finite and mixed
cross-dimensional cases. -/
theorem fanDominanceSeparable_iff_finite_mixed_positiveModel
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hHinf : ¬ FiniteDimensional ℂ H) :
    HasFanDominanceSeparable N ↔
      HasFanDominanceOnFiniteSeparableDomains N ∧
      HasFanDominanceOnMixedSeparableDomains N ∧
      HasFanDominanceOnPositiveSquare N H := by
  rw [fanDominanceSeparable_iff_dimensionSplit N,
    fanDominanceInfiniteSeparable_iff_positiveModel N hHinf]
  tauto

/-!
## Updated boundary after Probes 9--12

If these probes compile, the earlier `sequence invariance + one model` factor
is no longer the sharpest reduction.  The source laws themselves give the
rectangular modulus reduction, and separability classifies every
infinite-dimensional domain up to unitary equivalence.  The full problem then
splits as

```
full separable Fan dominance
        ⇕
finite/finite comparisons
    + mixed finite/infinite comparisons
    + positive Fan dominance on one infinite separable H.
```

The mixed case is now exposed explicitly instead of being hidden inside a
blanket approximation-sequence-invariance hypothesis.  A later probe can ask
which mixed orientation follows from finite-rank reduction and which one really
requires an infinite-completion/full-symmetry theorem.
-/


/-!
## Probe 13: stabilization by a zero Hilbert summand is invisible

Probe 12 exposed finite/infinite mixed comparisons only because finite- and
infinite-dimensional domains are not unitarily equivalent.  A cheaper move is
to *stabilize* every square operator by adjoining the same infinite-dimensional
zero summand.  The resulting domains are all infinite-dimensional, while both
the source gauge and every approximation number should remain unchanged.

This probe proves that invisibility directly from the source ideal laws and the
existing approximation-number contraction estimates.  It does not assume Fan
dominance.
-/

private theorem blockInl_enorm_le_one_stabilization
    {E H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]  :
    ‖(blockInl (𝕜 := ℂ) (E₀ := E) (E₁ := H))‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal
    (norm_blockInl_le (𝕜 := ℂ) (E₀ := E) (E₁ := H))

private theorem blockInr_enorm_le_one_stabilization
    {E H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]  :
    ‖(blockInr (𝕜 := ℂ) (E₀ := E) (E₁ := H))‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal
    (norm_blockInr_le (𝕜 := ℂ) (E₀ := E) (E₁ := H))

private theorem fstL_enorm_le_one_stabilization
    {E H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]  :
    ‖(WithLp.fstL 2 ℂ E H)‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal
    (norm_fstL_le (𝕜 := ℂ) (F₀ := E) (F₁ := H))

private theorem sndL_enorm_le_one_stabilization
    {E H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]  :
    ‖(WithLp.sndL 2 ℂ E H)‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal
    (norm_sndL_le (𝕜 := ℂ) (F₀ := E) (F₁ := H))

/-- Adjoining a zero second block preserves the source gauge exactly. -/
theorem source_gauge_blockSum_zero_right_eq
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : E →L[ℂ] E) :
    N.toSymmetricOperatorIdealFamily.gauge
        (continuousOrthogonalBlockSum A (0 : H →L[ℂ] H)) =
      N.toSymmetricOperatorIdealFamily.gauge A := by
  let S := N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily
  let Z : WithLp 2 (E × H) →L[ℂ] WithLp 2 (E × H) :=
    continuousOrthogonalBlockSum A (0 : H →L[ℂ] H)
  have hZfac : Z =
      (blockInl (𝕜 := ℂ) (E₀ := E) (E₁ := H)) ∘L A ∘L
        (WithLp.fstL 2 ℂ E H) := by
    ext x
    simp [Z, continuousOrthogonalBlockSum_apply]
  have hAfac : A =
      (WithLp.fstL 2 ℂ E H) ∘L Z ∘L
        (blockInl (𝕜 := ℂ) (E₀ := E) (E₁ := H)) := by
    ext x
    simp [Z, continuousOrthogonalBlockSum_apply]
  change S.gauge Z = S.gauge A
  apply le_antisymm
  · rw [hZfac]
    exact S.gauge_comp_le_of_norm_le_one
      blockInl_enorm_le_one_stabilization fstL_enorm_le_one_stabilization
  · rw [hAfac]
    exact S.gauge_comp_le_of_norm_le_one
      fstL_enorm_le_one_stabilization blockInl_enorm_le_one_stabilization

/-- Adjoining a zero second block preserves every approximation number and the
source gauge. -/
theorem source_blockSum_zero_right_sameSequence_and_gauge
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : E →L[ℂ] E) :
    let Z : WithLp 2 (E × H) →L[ℂ] WithLp 2 (E × H) :=
      continuousOrthogonalBlockSum A (0 : H →L[ℂ] H)
    A.HasSameApproximationNumbers Z ∧
      N.toSymmetricOperatorIdealFamily.gauge A =
        N.toSymmetricOperatorIdealFamily.gauge Z := by
  dsimp
  let Z : WithLp 2 (E × H) →L[ℂ] WithLp 2 (E × H) :=
    continuousOrthogonalBlockSum A (0 : H →L[ℂ] H)
  have hZfac : Z =
      (blockInl (𝕜 := ℂ) (E₀ := E) (E₁ := H)) ∘L A ∘L
        (WithLp.fstL 2 ℂ E H) := by
    ext x
    simp [Z, continuousOrthogonalBlockSum_apply]
  have hAfac : A =
      (WithLp.fstL 2 ℂ E H) ∘L Z ∘L
        (blockInl (𝕜 := ℂ) (E₀ := E) (E₁ := H)) := by
    ext x
    simp [Z, continuousOrthogonalBlockSum_apply]
  constructor
  · rw [ContinuousLinearMap.hasSameApproximationNumbers_iff]
    intro n
    apply le_antisymm
    · calc
        A.approximationNumber n =
            ((WithLp.fstL 2 ℂ E H) ∘L Z ∘L
              (blockInl (𝕜 := ℂ) (E₀ := E) (E₁ := H))).approximationNumber n := by
                rw [← hAfac]
        _ ≤ Z.approximationNumber n :=
          TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
            (WithLp.fstL 2 ℂ E H)
            (blockInl (𝕜 := ℂ) (E₀ := E) (E₁ := H))
            (norm_fstL_le (𝕜 := ℂ) (F₀ := E) (F₁ := H))
            (norm_blockInl_le (𝕜 := ℂ) (E₀ := E) (E₁ := H)) n
    · calc
        Z.approximationNumber n =
            ((blockInl (𝕜 := ℂ) (E₀ := E) (E₁ := H)) ∘L A ∘L
              (WithLp.fstL 2 ℂ E H)).approximationNumber n := by
                rw [hZfac]
        _ ≤ A.approximationNumber n :=
          TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
            (blockInl (𝕜 := ℂ) (E₀ := E) (E₁ := H))
            (WithLp.fstL 2 ℂ E H)
            (norm_blockInl_le (𝕜 := ℂ) (E₀ := E) (E₁ := H))
            (norm_fstL_le (𝕜 := ℂ) (F₀ := E) (F₁ := H)) n
  · exact (source_gauge_blockSum_zero_right_eq N (H := H) A).symm

/-!
## Probe 14: stabilization forces every domain into the all-infinite lane

If `H` is infinite-dimensional, then `E ⊕₂ H` is infinite-dimensional for every
`E`.  This is the only dimension fact stabilization needs.
-/

private theorem blockInr_injective_stabilization
    {E H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]  :
    Function.Injective
      (blockInr (𝕜 := ℂ) (E₀ := E) (E₁ := H) :
        H → WithLp 2 (E × H)) := by
  intro x y hxy
  have h := congrArg (fun z : WithLp 2 (E × H) => z.snd) hxy
  simpa using h

/-- `E ⊕₂ H` remains infinite-dimensional as soon as the stabilizing summand
`H` is infinite-dimensional. -/
theorem stabilization_infinite_of_right_infinite
    {E H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hHinf : ¬ FiniteDimensional ℂ H) :
    ¬ FiniteDimensional ℂ (WithLp 2 (E × H)) := by
  intro hfin
  apply hHinf
  let _ : FiniteDimensional ℂ (WithLp 2 (E × H)) := hfin
  exact FiniteDimensional.of_injective
    (blockInr (𝕜 := ℂ) (E₀ := E) (E₁ := H)).toLinearMap
    blockInr_injective_stabilization

/-!
## Probe 15: one infinite model controls *all* separable square pairs

Stabilization removes the mixed-dimensional obstruction from Probe 12.  Given
square operators on arbitrary separable `E` and `E'`, append the same infinite
zero summand `H` to both.  Their approximation sequences and source gauges are
unchanged, while both stabilized domains are now infinite-dimensional.  Probe
11 can therefore compare them.
-/

/-- Fan dominance for arbitrary pairs of square operators on separable Hilbert
spaces, with no dimension restriction. -/
def HasFanDominanceOnSeparableSquarePairs
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E E' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [TopologicalSpace.SeparableSpace E']
    {A : E →L[ℂ] E} {B : E' →L[ℂ] E'},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- All-infinite separable dominance implies arbitrary separable square-pair
dominance after stabilization by one fixed infinite separable Hilbert space. -/
theorem hasFanDominanceOnSeparableSquarePairs_of_infiniteDomains
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hHinf : ¬ FiniteDimensional ℂ H)
    (hinf : HasFanDominanceOnInfiniteSeparableDomains N) :
    HasFanDominanceOnSeparableSquarePairs N := by
  intro E E' _ _ _ _ _ _ _ _ A B hAB
  let ZA : WithLp 2 (E × H) →L[ℂ] WithLp 2 (E × H) :=
    continuousOrthogonalBlockSum A (0 : H →L[ℂ] H)
  let ZB : WithLp 2 (E' × H) →L[ℂ] WithLp 2 (E' × H) :=
    continuousOrthogonalBlockSum B (0 : H →L[ℂ] H)
  have hZA := source_blockSum_zero_right_sameSequence_and_gauge N (H := H) A
  have hZB := source_blockSum_zero_right_sameSequence_and_gauge N (H := H) B
  have hZAseq : A.HasSameApproximationNumbers ZA := by simpa [ZA] using hZA.1
  have hZBseq : B.HasSameApproximationNumbers ZB := by simpa [ZB] using hZB.1
  have hZAgauge : N.toSymmetricOperatorIdealFamily.gauge A =
      N.toSymmetricOperatorIdealFamily.gauge ZA := by simpa [ZA] using hZA.2
  have hZBgauge : N.toSymmetricOperatorIdealFamily.gauge B =
      N.toSymmetricOperatorIdealFamily.gauge ZB := by simpa [ZB] using hZB.2
  have hZAinf : ¬ FiniteDimensional ℂ (WithLp 2 (E × H)) :=
    stabilization_infinite_of_right_infinite hHinf
  have hZBinf : ¬ FiniteDimensional ℂ (WithLp 2 (E' × H)) :=
    stabilization_infinite_of_right_infinite hHinf
  have hZAB : ∀ k, kyFanApproximationGauge k ZA ≤
      kyFanApproximationGauge k ZB := by
    intro k
    have hk := hAB k
    change A.kyFanGauge k ≤ B.kyFanGauge k at hk
    change ZA.kyFanGauge k ≤ ZB.kyFanGauge k
    calc
      ZA.kyFanGauge k = A.kyFanGauge k := (hZAseq.kyFanGauge_eq k).symm
      _ ≤ B.kyFanGauge k := hk
      _ = ZB.kyFanGauge k := hZBseq.kyFanGauge_eq k
  have hstab : N.toSymmetricOperatorIdealFamily.gauge ZA ≤
      N.toSymmetricOperatorIdealFamily.gauge ZB :=
    hinf hZAinf hZBinf hZAB
  calc
    N.toSymmetricOperatorIdealFamily.gauge A =
        N.toSymmetricOperatorIdealFamily.gauge ZA := hZAgauge
    _ ≤ N.toSymmetricOperatorIdealFamily.gauge ZB := hstab
    _ = N.toSymmetricOperatorIdealFamily.gauge B := hZBgauge.symm

/-!
## Probe 16: the whole separable Fan theorem reduces to one positive model

Rectangular modulus reduction (Probe 9) turns arbitrary source comparisons into
square positive comparisons on their domains.  Probe 15 then removes every
dimension distinction by stabilization.  Consequently the complete separable
Fan-dominance statement should be equivalent to positive Fan dominance on one
fixed infinite-dimensional separable Hilbert space.
-/

/-- Square-pair dominance is enough for the full rectangular separable source
statement, because both the gauge and approximation numbers are unchanged by
passing to the operator modulus. -/
theorem hasFanDominanceSeparable_of_squarePairs
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hsq : HasFanDominanceOnSeparableSquarePairs N) :
    HasFanDominanceSeparable N := by
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
  have hAmod := ContinuousLinearMap.modulus_hasSameApproximationNumbers A
  have hBmod := ContinuousLinearMap.modulus_hasSameApproximationNumbers B
  have hABmod : ∀ k, kyFanApproximationGauge k A.modulus ≤
      kyFanApproximationGauge k B.modulus := by
    intro k
    have hk := hAB k
    change A.kyFanGauge k ≤ B.kyFanGauge k at hk
    change A.modulus.kyFanGauge k ≤ B.modulus.kyFanGauge k
    calc
      A.modulus.kyFanGauge k = A.kyFanGauge k := hAmod.kyFanGauge_eq k
      _ ≤ B.kyFanGauge k := hk
      _ = B.modulus.kyFanGauge k := (hBmod.kyFanGauge_eq k).symm
  have hmod : N.toSymmetricOperatorIdealFamily.gauge A.modulus ≤
      N.toSymmetricOperatorIdealFamily.gauge B.modulus := hsq hABmod
  calc
    N.toSymmetricOperatorIdealFamily.gauge A =
        N.toSymmetricOperatorIdealFamily.gauge A.modulus :=
      (source_gauge_modulus_eq_rectangular N A).symm
    _ ≤ N.toSymmetricOperatorIdealFamily.gauge B.modulus := hmod
    _ = N.toSymmetricOperatorIdealFamily.gauge B :=
      source_gauge_modulus_eq_rectangular N B

/-- Positive Fan dominance on one fixed infinite separable Hilbert space implies
the complete separable source statement. -/
theorem hasFanDominanceSeparable_of_positiveModel_stabilized
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hHinf : ¬ FiniteDimensional ℂ H)
    (hpos : HasFanDominanceOnPositiveSquare N H) :
    HasFanDominanceSeparable N := by
  have hsqH : HasFanDominanceOnSquare N H :=
    hasFanDominanceOnSquare_of_positive N hpos
  have hinf : HasFanDominanceOnInfiniteSeparableDomains N :=
    hasFanDominanceOnInfiniteSeparableDomains_of_modelSpace N hHinf hsqH
  have hsqPairs : HasFanDominanceOnSeparableSquarePairs N :=
    hasFanDominanceOnSeparableSquarePairs_of_infiniteDomains N (H := H) hHinf hinf
  -- Inline the already-proved square-pair-to-rectangular reduction here.
  -- Calling `hasFanDominanceSeparable_of_squarePairs` at this higher-order
  -- boundary leaves its separability typeclass arguments underconstrained in
  -- Lean's elaborator, even though the theorem itself is valid.  Introducing
  -- the operator spaces first fixes those arguments before `hsqPairs` is used.
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
  have hAmod := ContinuousLinearMap.modulus_hasSameApproximationNumbers A
  have hBmod := ContinuousLinearMap.modulus_hasSameApproximationNumbers B
  have hABmod : ∀ k, kyFanApproximationGauge k A.modulus ≤
      kyFanApproximationGauge k B.modulus := by
    intro k
    have hk := hAB k
    change A.kyFanGauge k ≤ B.kyFanGauge k at hk
    change A.modulus.kyFanGauge k ≤ B.modulus.kyFanGauge k
    calc
      A.modulus.kyFanGauge k = A.kyFanGauge k := hAmod.kyFanGauge_eq k
      _ ≤ B.kyFanGauge k := hk
      _ = B.modulus.kyFanGauge k := (hBmod.kyFanGauge_eq k).symm
  have hmod : N.toSymmetricOperatorIdealFamily.gauge A.modulus ≤
      N.toSymmetricOperatorIdealFamily.gauge B.modulus := hsqPairs hABmod
  calc
    N.toSymmetricOperatorIdealFamily.gauge A =
        N.toSymmetricOperatorIdealFamily.gauge A.modulus :=
      (source_gauge_modulus_eq_rectangular N A).symm
    _ ≤ N.toSymmetricOperatorIdealFamily.gauge B.modulus := hmod
    _ = N.toSymmetricOperatorIdealFamily.gauge B :=
      source_gauge_modulus_eq_rectangular N B

/-- Conversely, the full separable source statement contains the positive
square case on any particular separable model space. -/
theorem hasFanDominanceOnPositiveSquare_of_fanDominanceSeparable
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (h : HasFanDominanceSeparable N) :
    HasFanDominanceOnPositiveSquare N H :=
  hasFanDominanceOnPositiveSquare_of_square N
    (hasFanDominanceOnSquare_of_fanDominanceSeparable N h)

/-- **Sharp stabilized reduction.**  For any fixed infinite-dimensional
separable complex Hilbert space `H`, full source-scope Fan dominance is exactly
positive Fan dominance on `H`. -/
theorem fanDominanceSeparable_iff_positiveModel_stabilized
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (hHinf : ¬ FiniteDimensional ℂ H) :
    HasFanDominanceSeparable N ↔ HasFanDominanceOnPositiveSquare N H := by
  constructor
  · exact hasFanDominanceOnPositiveSquare_of_fanDominanceSeparable N
  · exact hasFanDominanceSeparable_of_positiveModel_stabilized N hHinf

/-!
## Boundary after Probes 13--16

If these compile, the finite/infinite split from Probe 12 is bookkeeping rather
than an essential obstruction.  Zero stabilization moves every separable square
operator into the all-infinite lane without changing either side of the Fan
comparison.  Together with rectangular modulus reduction, the entire source
problem becomes one theorem:

```
positive Fan dominance
on one fixed infinite-dimensional separable Hilbert space.
```

No finite-dimensional membership issue, mixed-dimensional adapter, or blanket
same-approximation-sequence axiom remains in that reduction.  The next probes
should therefore attack this positive infinite-dimensional model theorem itself,
and in particular determine whether the raw source ideal laws imply the needed
infinite limiting/majorization step or whether the current source abstraction is
missing a standard regularity assumption.
-/


/-!
## Probes 17--24: test whether the raw source laws can imply unconditional Fan dominance

Probes 13--16 reduce the separable problem to positive Fan dominance on one fixed
infinite-dimensional separable Hilbert space.  Before attempting the remaining
infinite-dimensional majorization proof, there is a more basic question to
settle: is the current raw `NormalizedSymmetricOperatorIdealFamily` abstraction itself
strong enough for the unconditional `ENNReal`-valued Fan-dominance property?

The source gauge uses `∞` outside its ideal.  Therefore
`HasFanDominanceSeparable` contains two logically different assertions:

1. **where-defined norm monotonicity** -- if both displayed norms exist, Ky Fan
   domination implies the source-norm inequality;
2. **membership transfer** -- if the right-hand operator belongs to the ideal,
   then every operator weakly majorized by it also belongs to the ideal.

A finite-rank ideal equipped with the operator norm is a useful stress test.  It
satisfies the raw symmetric ideal laws and the rank-one normalization, while an
infinite-rank compact diagonal can be weakly majorized by a rank-one operator.
If the following probes compile, the current raw source laws do **not** imply the
unconditional Fan-dominance property.  That would not by itself decide the
correct Davis--Kahan source interpretation; it would identify the exact semantic
boundary that has to be resolved.
-/

/-- Exploration-only finite-rank predicate, expressed with a natural rank bound
so the existing rank-composition and adjoint lemmas apply directly. -/
def ProbeFiniteRank
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : E →L[ℂ] F) : Prop :=
  ∃ n : ℕ, A.rank ≤ (n : Cardinal)

private theorem probeFiniteRank_zero
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    ProbeFiniteRank (0 : E →L[ℂ] F) := by
  refine ⟨0, ?_⟩
  simp [LinearMap.rank_zero]

private theorem probeFiniteRank_add
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {A B : E →L[ℂ] F}
    (hA : ProbeFiniteRank A) (hB : ProbeFiniteRank B) :
    ProbeFiniteRank (A + B) := by
  obtain ⟨m, hm⟩ := hA
  obtain ⟨n, hn⟩ := hB
  refine ⟨m + n, ?_⟩
  calc
    (A + B).rank ≤ A.rank + B.rank := LinearMap.rank_add_le _ _
    _ ≤ (m : Cardinal) + (n : Cardinal) := add_le_add hm hn
    _ = ((m + n : ℕ) : Cardinal) := by norm_cast

/-- Local copy of the elementary rank inequality used privately by the
approximation-number development. -/
private theorem probe_rank_smul_le_rank
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (c : ℂ) (A : E →L[ℂ] F) :
    (c • A).rank ≤ A.rank := by
  refine Submodule.rank_mono ?_
  rintro y ⟨x, rfl⟩
  exact ⟨c • x, by simp⟩

private theorem probeFiniteRank_smul
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (c : ℂ) {A : E →L[ℂ] F} (hA : ProbeFiniteRank A) :
    ProbeFiniteRank (c • A) := by
  obtain ⟨n, hn⟩ := hA
  exact ⟨n, (probe_rank_smul_le_rank c A).trans hn⟩

private theorem probeFiniteRank_smul_iff
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (c : ℂ) (hc : c ≠ 0) (A : E →L[ℂ] F) :
    ProbeFiniteRank (c • A) ↔ ProbeFiniteRank A := by
  constructor
  · intro h
    have h' := probeFiniteRank_smul c⁻¹ h
    simpa [smul_smul, inv_mul_cancel₀ hc] using h'
  · exact probeFiniteRank_smul c

private theorem probeFiniteRank_comp
    {E H F G : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (L : F →L[ℂ] G) {A : E →L[ℂ] F} (hA : ProbeFiniteRank A)
    (R : H →L[ℂ] E) :
    ProbeFiniteRank (L ∘L A ∘L R) := by
  obtain ⟨n, hn⟩ := hA
  have hLA : (L ∘L A).rank ≤ (n : Cardinal) :=
    ContinuousLinearMap.rank_comp_le_natCast_right A L hn
  exact ⟨n, (ContinuousLinearMap.rank_comp_le_left R (L ∘L A)).trans hLA⟩

private theorem probeFiniteRank_adjoint
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →L[ℂ] F} (hA : ProbeFiniteRank A) :
    ProbeFiniteRank A.adjoint := by
  obtain ⟨n, hn⟩ := hA
  exact ⟨n, ContinuousLinearMap.rank_adjoint_le_natCast_of_rank_le A hn⟩

private theorem probeFiniteRank_adjoint_iff
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    ProbeFiniteRank A.adjoint ↔ ProbeFiniteRank A := by
  constructor
  · intro h
    have h' := probeFiniteRank_adjoint h
    simpa using h'
  · exact probeFiniteRank_adjoint

/-! ### Probe 17: a raw source model on the finite-rank ideal -/

/-- Operator norm on finite-rank maps and `∞` elsewhere. -/
noncomputable def finiteRankOperatorNormGauge
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] 
    (A : E →L[ℂ] F) : ℝ≥0∞ := by
  classical
  exact if ProbeFiniteRank A then ‖A‖ₑ else ⊤

/-- The finite-rank ideal with the operator norm, as an exploration-only ideal
family.  The proof deliberately mirrors the existing compact-operator family. -/
noncomputable def finiteRankOperatorNormIdealFamily :
    OperatorIdealFamily.{0, v, v} ℂ where
  gauge A := finiteRankOperatorNormGauge A
  gauge_add_le A B := by
    classical
    by_cases hA : ProbeFiniteRank A
    · by_cases hB : ProbeFiniteRank B
      · have hAB : ProbeFiniteRank (A + B) := probeFiniteRank_add hA hB
        change finiteRankOperatorNormGauge (A + B) ≤
          finiteRankOperatorNormGauge A + finiteRankOperatorNormGauge B
        simp only [finiteRankOperatorNormGauge, ite_eq_left hA,
          ite_eq_left hB, ite_eq_left hAB]
        exact (operatorNormIdealFamily.{0, v, v} ℂ).gauge_add_le A B
      · simp [finiteRankOperatorNormGauge, ite_eq_right hB]
    · simp [finiteRankOperatorNormGauge, ite_eq_right hA]
  gauge_smul c A := by
    classical
    rcases eq_or_ne c 0 with rfl | hc
    · have hz : ProbeFiniteRank ((0 : ℂ) • A) := by
        rw [zero_smul]
        exact probeFiniteRank_zero
      have h1 : ‖((0 : ℂ) • A)‖ₑ = 0 := by
        rw [zero_smul]
        simp [enorm_eq_nnnorm]
      have h2 : ‖(0 : ℂ)‖ₑ = 0 := by
        simp [enorm_eq_nnnorm]
      change finiteRankOperatorNormGauge ((0 : ℂ) • A) =
        ‖(0 : ℂ)‖ₑ * finiteRankOperatorNormGauge A
      rw [finiteRankOperatorNormGauge, ite_eq_left hz, h1, h2, zero_mul]
    · by_cases hA : ProbeFiniteRank A
      · have hcA : ProbeFiniteRank (c • A) := probeFiniteRank_smul c hA
        change finiteRankOperatorNormGauge (c • A) =
          ‖c‖ₑ * finiteRankOperatorNormGauge A
        simp only [finiteRankOperatorNormGauge, ite_eq_left hA,
          ite_eq_left hcA]
        exact (operatorNormIdealFamily.{0, v, v} ℂ).gauge_smul c A
      · have hcA : ¬ ProbeFiniteRank (c • A) := by
          intro h
          exact hA ((probeFiniteRank_smul_iff c hc A).mp h)
        change finiteRankOperatorNormGauge (c • A) =
          ‖c‖ₑ * finiteRankOperatorNormGauge A
        simp only [finiteRankOperatorNormGauge, ite_eq_right hA,
          ite_eq_right hcA]
        simp [ENNReal.mul_top, enorm_ne_zero.mpr hc]
  enorm_le_gauge A := by
    classical
    change ‖A‖ₑ ≤ finiteRankOperatorNormGauge A
    by_cases hA : ProbeFiniteRank A
    · rw [finiteRankOperatorNormGauge, ite_eq_left hA]
    · rw [finiteRankOperatorNormGauge, ite_eq_right hA]
      exact le_top
  gauge_comp_le L A R := by
    classical
    change finiteRankOperatorNormGauge (L ∘L A ∘L R) ≤
      ‖L‖ₑ * finiteRankOperatorNormGauge A * ‖R‖ₑ
    by_cases hA : ProbeFiniteRank A
    · have hcomp : ProbeFiniteRank (L ∘L A ∘L R) :=
        probeFiniteRank_comp L hA R
      simp only [finiteRankOperatorNormGauge, ite_eq_left hA,
        ite_eq_left hcomp]
      exact (operatorNormIdealFamily.{0, v, v} ℂ).gauge_comp_le L A R
    · simp only [finiteRankOperatorNormGauge, ite_eq_right hA]
      by_cases hL : L = 0
      · have hzero : L ∘L A ∘L R = 0 := by
          rw [hL, ContinuousLinearMap.zero_comp]
        have hz : ProbeFiniteRank (L ∘L A ∘L R) := by
          rw [hzero]
          exact probeFiniteRank_zero
        have hz0 : ‖L ∘L A ∘L R‖ₑ = 0 := by
          rw [hzero]
          simp [enorm_eq_nnnorm]
        rw [ite_eq_left hz, hz0]
        exact zero_le
      · by_cases hR : R = 0
        · have hzero : L ∘L A ∘L R = 0 := by
            rw [hR, ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero]
          have hz : ProbeFiniteRank (L ∘L A ∘L R) := by
            rw [hzero]
            exact probeFiniteRank_zero
          have hz0 : ‖L ∘L A ∘L R‖ₑ = 0 := by
            rw [hzero]
            simp [enorm_eq_nnnorm]
          rw [ite_eq_left hz, hz0]
          exact zero_le
        · have hLe : ‖L‖ₑ ≠ 0 := by
            simp only [enorm_eq_nnnorm, ne_eq, ENNReal.coe_eq_zero,
              nnnorm_eq_zero]
            exact hL
          have hRe : ‖R‖ₑ ≠ 0 := by
            simp only [enorm_eq_nnnorm, ne_eq, ENNReal.coe_eq_zero,
              nnnorm_eq_zero]
            exact hR
          rw [ENNReal.mul_top hLe, ENNReal.top_mul hRe]
          exact le_top

/-- Adjoint-invariant refinement of the finite-rank operator-norm family. -/
noncomputable def finiteRankOperatorNormFamily :
    SymmetricOperatorIdealFamily.{0, v} ℂ where
  toOperatorIdealFamily := finiteRankOperatorNormIdealFamily
  gauge_adjoint A := by
    classical
    change finiteRankOperatorNormGauge A.adjoint = finiteRankOperatorNormGauge A
    have hiff := probeFiniteRank_adjoint_iff A
    by_cases hA : ProbeFiniteRank A
    · have hAdj : ProbeFiniteRank A.adjoint := hiff.mpr hA
      rw [finiteRankOperatorNormGauge, finiteRankOperatorNormGauge,
        ite_eq_left hAdj, ite_eq_left hA, ← ofReal_norm, ← ofReal_norm,
        ContinuousLinearMap.adjoint.norm_map]
    · have hAdj : ¬ ProbeFiniteRank A.adjoint := by
        intro h
        exact hA (hiff.mp h)
      rw [finiteRankOperatorNormGauge, finiteRankOperatorNormGauge,
        ite_eq_right hAdj, ite_eq_right hA]

/-- The finite-rank operator-norm family satisfies the current raw source laws,
including rank-one normalization. -/
noncomputable def finiteRankNormalizedSymmetricOperatorIdealFamily :
    NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ where
  toSymmetricOperatorIdealFamily := finiteRankOperatorNormFamily
  gauge_rankOne_eq_one := by
    intro E F _ _ _ _ _ _ V hVnorm hVrank
    have hfin : ProbeFiniteRank V := ⟨1, hVrank⟩
    change (finiteRankOperatorNormGauge V).toReal = 1
    rw [finiteRankOperatorNormGauge, ite_eq_left hfin, toReal_enorm, hVnorm]
  gauge_le_of_forall_kyFanApproximationGauge_le_defined := by
    intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hA hB hAB
    classical
    have hAfin : ProbeFiniteRank A := by
      by_contra hn
      change finiteRankOperatorNormGauge A ≠ ⊤ at hA
      rw [finiteRankOperatorNormGauge, if_neg hn] at hA
      exact hA rfl
    have hBfin : ProbeFiniteRank B := by
      by_contra hn
      change finiteRankOperatorNormGauge B ≠ ⊤ at hB
      rw [finiteRankOperatorNormGauge, if_neg hn] at hB
      exact hB rfl
    change finiteRankOperatorNormGauge A ≤ finiteRankOperatorNormGauge B
    rw [finiteRankOperatorNormGauge, if_pos hAfin,
      finiteRankOperatorNormGauge, if_pos hBfin]
    have h1 := hAB 1
    rw [kyFanApproximationGauge_one, kyFanApproximationGauge_one] at h1
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h1

/-! ### Probe 18: expose the exact carrier/gauge boundary -/

@[simp]
theorem finiteRankOperatorNormGauge_eq_top_iff
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    finiteRankOperatorNormGauge A = ⊤ ↔ ¬ ProbeFiniteRank A := by
  classical
  by_cases hA : ProbeFiniteRank A
  · rw [finiteRankOperatorNormGauge, ite_eq_left hA]
    simp [hA]
  · rw [finiteRankOperatorNormGauge, ite_eq_right hA]
    simp [hA]


theorem finiteRankOperatorNormGauge_ne_top_iff
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    finiteRankOperatorNormGauge A ≠ ⊤ ↔ ProbeFiniteRank A := by
  rw [ne_eq, finiteRankOperatorNormGauge_eq_top_iff]
  tauto

@[simp]
theorem finiteRankOperatorNormGauge_of_finiteRank
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →L[ℂ] F} (hA : ProbeFiniteRank A) :
    finiteRankOperatorNormGauge A = ‖A‖ₑ := by
  rw [finiteRankOperatorNormGauge, ite_eq_left hA]

/-! ### Probes 19--20: an infinite-rank diagonal below a rank-one Ky Fan profile -/

/-- The complex square-summable sequence space supporting the diagonal Fan-profile example. -/
abbrev FanCounterexampleSpace := lp (fun _ : ℕ => ℂ) 2

/-- Positive geometric approximation-number profile with total mass one. -/
def fanCounterexampleRealCoeff (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

/-- The same profile as complex diagonal coefficients. -/
def fanCounterexampleCoeff (n : ℕ) : ℂ := fanCounterexampleRealCoeff n

@[simp]
theorem norm_fanCounterexampleCoeff (n : ℕ) :
    ‖fanCounterexampleCoeff n‖ = fanCounterexampleRealCoeff n := by
  simp [fanCounterexampleCoeff, fanCounterexampleRealCoeff]

private theorem fanCounterexampleCoeff_le_one (n : ℕ) :
    ‖fanCounterexampleCoeff n‖ ≤ 1 := by
  rw [norm_fanCounterexampleCoeff]
  exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem fanCounterexampleCoeff_antitone :
    Antitone (fun n : ℕ => ‖fanCounterexampleCoeff n‖) := by
  rw [show (fun n : ℕ => ‖fanCounterexampleCoeff n‖) = fanCounterexampleRealCoeff by
    funext n
    exact norm_fanCounterexampleCoeff n]
  refine antitone_nat_of_succ_le fun n => ?_
  unfold fanCounterexampleRealCoeff
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := pow_nonneg (by norm_num) _
  rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
  nlinarith

/-- Infinite-rank compact diagonal used to test membership transfer. -/
noncomputable def fanCounterexampleA :
    FanCounterexampleSpace →L[ℂ] FanCounterexampleSpace :=
  diagOpLp fanCounterexampleCoeff (K := 1) (by norm_num) fanCounterexampleCoeff_le_one

@[simp]
theorem approximationNumber_fanCounterexampleA (n : ℕ) :
    fanCounterexampleA.approximationNumber n = fanCounterexampleRealCoeff n := by
  rw [fanCounterexampleA, approximationNumber_diagOpLp
    fanCounterexampleCoeff (K := 1) (by norm_num) fanCounterexampleCoeff_le_one
    fanCounterexampleCoeff_antitone]
  exact norm_fanCounterexampleCoeff n

private theorem fanCounterexampleRealCoeff_pos (n : ℕ) :
    0 < fanCounterexampleRealCoeff n := by
  unfold fanCounterexampleRealCoeff
  positivity

/-- The geometric diagonal cannot have finite rank: every approximation number
is strictly positive. -/
theorem fanCounterexampleA_not_finiteRank :
    ¬ ProbeFiniteRank fanCounterexampleA := by
  rintro ⟨n, hn⟩
  have hz := ContinuousLinearMap.approximationNumber_eq_zero_of_rank_le
    fanCounterexampleA hn
  rw [approximationNumber_fanCounterexampleA] at hz
  exact (ne_of_gt (fanCounterexampleRealCoeff_pos n)) hz

/-- Exact finite geometric-prefix identity. -/
theorem fanCounterexample_prefix_sum (k : ℕ) :
    (∑ n ∈ Finset.range k, fanCounterexampleRealCoeff n) =
      1 - (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      unfold fanCounterexampleRealCoeff
      rw [show k + 1 = Nat.succ k by rfl, pow_succ]
      ring

/-- Every Ky Fan prefix of the infinite-rank diagonal is at most one. -/
theorem fanCounterexampleA_kyFan_le_one (k : ℕ) :
    kyFanApproximationGauge k fanCounterexampleA ≤ 1 := by
  change fanCounterexampleA.kyFanGauge k ≤ 1
  rw [ContinuousLinearMap.kyFanGauge]
  simp_rw [approximationNumber_fanCounterexampleA]
  rw [fanCounterexample_prefix_sum]
  have hp : 0 ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) _
  linarith

/-- Unit vector for the rank-one comparator. -/
noncomputable def fanCounterexampleUnit : FanCounterexampleSpace :=
  lp.single 2 0 (1 : ℂ)

@[simp]
theorem norm_fanCounterexampleUnit : ‖fanCounterexampleUnit‖ = 1 := by
  rw [fanCounterexampleUnit, lp.norm_single (by norm_num), norm_one]

/-- Rank-one comparator with singular-value profile `(1,0,0,...)`. -/
noncomputable def fanCounterexampleB :
    FanCounterexampleSpace →L[ℂ] FanCounterexampleSpace :=
  InnerProductSpace.rankOne ℂ fanCounterexampleUnit fanCounterexampleUnit

@[simp]
theorem norm_fanCounterexampleB : ‖fanCounterexampleB‖ = 1 := by
  simp [fanCounterexampleB]

private theorem fanCounterexampleB_rank_le_one :
    fanCounterexampleB.rank ≤ (1 : Cardinal) := by
  exact rankOne_rank_le_one _ _

/-- Exact approximation-number profile of the rank-one comparator. -/
theorem approximationNumber_fanCounterexampleB (n : ℕ) :
    fanCounterexampleB.approximationNumber n = if n = 0 then 1 else 0 := by
  have h := SymmetricNormingFunction.approximationSingularValue_rankOne
    norm_fanCounterexampleB fanCounterexampleB_rank_le_one n
  exact h

/-- Every positive Ky Fan prefix of the rank-one comparator equals one. -/
theorem fanCounterexampleB_kyFan_succ (k : ℕ) :
    kyFanApproximationGauge (k + 1) fanCounterexampleB = 1 := by
  change fanCounterexampleB.kyFanGauge (k + 1) = 1
  rw [ContinuousLinearMap.kyFanGauge]
  have hval : ∀ n ∈ Finset.range (k + 1),
      fanCounterexampleB.approximationNumber n = if n = 0 then 1 else 0 :=
    fun n _ => approximationNumber_fanCounterexampleB n
  rw [Finset.sum_congr rfl hval,
    Finset.sum_ite_eq' (Finset.range (k + 1)) 0 (fun _ => (1 : ℝ))]
  simp

/-- The infinite-rank diagonal is weakly Ky-Fan-majorized by the rank-one
comparator. -/
theorem fanCounterexample_kyFan_domination :
    ∀ k, kyFanApproximationGauge k fanCounterexampleA ≤
      kyFanApproximationGauge k fanCounterexampleB := by
  intro k
  rcases k with _ | k
  · change fanCounterexampleA.kyFanGauge 0 ≤ fanCounterexampleB.kyFanGauge 0
    simp
  · rw [fanCounterexampleB_kyFan_succ]
    exact fanCounterexampleA_kyFan_le_one (k + 1)

/-! ### Probe 21: the raw source laws do not imply unconditional Fan dominance -/

@[simp]
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_A :
    (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}).toSymmetricOperatorIdealFamily.gauge
      fanCounterexampleA = ⊤ := by
  change finiteRankOperatorNormGauge fanCounterexampleA = ⊤
  rw [finiteRankOperatorNormGauge,
    ite_eq_right fanCounterexampleA_not_finiteRank]

@[simp]
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_B :
    (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}).toSymmetricOperatorIdealFamily.gauge
      fanCounterexampleB = 1 := by
  have hfin : ProbeFiniteRank fanCounterexampleB := ⟨1, fanCounterexampleB_rank_le_one⟩
  change finiteRankOperatorNormGauge fanCounterexampleB = 1
  rw [finiteRankOperatorNormGauge, ite_eq_left hfin, ← ofReal_norm,
    norm_fanCounterexampleB]
  norm_num

/-- **Decisive unrestricted countermodel probe.**  The raw source laws do not
imply the current production `HasFanDominance` property.  This theorem does not
need a separability instance for the concrete `lp` model. -/
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_not_fanDominant :
    ¬ (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}).HasFanDominance := by
  intro hfan
  have hle := hfan (A := fanCounterexampleA) (B := fanCounterexampleB)
    fanCounterexample_kyFan_domination
  rw [finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_A, finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_B] at hle
  have hbad : (⊤ : ℝ≥0∞) = 1 := le_antisymm hle le_top
  simp at hbad

/-- Existential form for the exact current production property. -/
theorem normalizedSymmetricFamilyLaws_do_not_imply_fanDominance :
    ∃ N : NormalizedSymmetricOperatorIdealFamily.{0, 0} ℂ, ¬ N.HasFanDominance :=
  ⟨finiteRankNormalizedSymmetricOperatorIdealFamily.{0},
    finiteRankNormalizedSymmetricOperatorIdealFamily_not_fanDominant⟩

/-- The same countermodel is separable as soon as Lean is supplied the missing
`SeparableSpace` instance for the pinned `lp` model.  Pinned Mathlib does not
currently provide that instance, so the fact is kept explicit rather than
smuggled in as an axiom or local instance. -/
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_not_fanDominantSeparable
    [TopologicalSpace.SeparableSpace FanCounterexampleSpace] :
    ¬ HasFanDominanceSeparable (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}) := by
  intro hfan
  have hle := hfan (A := fanCounterexampleA) (B := fanCounterexampleB)
    fanCounterexample_kyFan_domination
  rw [finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_A, finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_B] at hle
  have hbad : (⊤ : ℝ≥0∞) = 1 := le_antisymm hle le_top
  simp at hbad

/-- Conditional existential form of the separable countermodel. -/
theorem normalizedSymmetricFamilyLaws_do_not_imply_fanDominanceSeparable
    [TopologicalSpace.SeparableSpace FanCounterexampleSpace] :
    ∃ N : NormalizedSymmetricOperatorIdealFamily.{0, 0} ℂ, ¬ HasFanDominanceSeparable N :=
  ⟨finiteRankNormalizedSymmetricOperatorIdealFamily.{0},
    finiteRankNormalizedSymmetricOperatorIdealFamily_not_fanDominantSeparable⟩

/-! ### Probe 22: split the exact current production property -/

/-- Exploration spelling of the now-production where-defined Fan property. -/
abbrev HasFanDominanceWhereDefined
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  N.HasFanDominanceWhereDefined

/-- The membership-solidity component of the current production Fan-dominance
property. -/
def HasKyFanMembershipTransfer
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    N.toSymmetricOperatorIdealFamily.gauge B ≠ ⊤ →
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤

/-- The production property decomposes exactly into where-defined monotonicity
and Ky-Fan membership transfer. -/
theorem fanDominance_iff_whereDefined_and_membershipTransfer
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) :
    N.HasFanDominance ↔
      HasFanDominanceWhereDefined N ∧ HasKyFanMembershipTransfer N := by
  constructor
  · intro h
    constructor
    · intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B _ _ hAB
      exact h hAB
    · intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hB hAB
      exact ne_top_of_le_ne_top hB (h hAB)
  · rintro ⟨hwhere, htransfer⟩
    intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
    by_cases hB : N.toSymmetricOperatorIdealFamily.gauge B = ⊤
    · rw [hB]
      exact le_top
    · have hA : N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤ :=
        htransfer hB hAB
      exact hwhere hA hB hAB

/-- The finite-rank/operator-norm source satisfies the norm inequality whenever
both source gauges are defined. -/
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_fanDominantWhereDefined_unrestricted :
    HasFanDominanceWhereDefined (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}) := by
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hA hB hAB
  have hAfin : ProbeFiniteRank A := by
    change finiteRankOperatorNormGauge A ≠ ⊤ at hA
    exact (finiteRankOperatorNormGauge_ne_top_iff A).mp hA
  have hBfin : ProbeFiniteRank B := by
    change finiteRankOperatorNormGauge B ≠ ⊤ at hB
    exact (finiteRankOperatorNormGauge_ne_top_iff B).mp hB
  change finiteRankOperatorNormGauge A ≤ finiteRankOperatorNormGauge B
  rw [finiteRankOperatorNormGauge_of_finiteRank hAfin,
    finiteRankOperatorNormGauge_of_finiteRank hBfin]
  have h1 := hAB 1
  rw [kyFanApproximationGauge_one, kyFanApproximationGauge_one] at h1
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h1

/-- The concrete diagonal/rank-one pair disproves the membership-transfer half
of the production property. -/
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_not_membershipTransfer_unrestricted :
    ¬ HasKyFanMembershipTransfer (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}) := by
  intro htransfer
  have hB :
      (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}).toSymmetricOperatorIdealFamily.gauge
        fanCounterexampleB ≠ ⊤ := by
    rw [finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_B]
    simp
  have hA := htransfer (A := fanCounterexampleA) (B := fanCounterexampleB)
    hB fanCounterexample_kyFan_domination
  rw [finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_A] at hA
  exact hA rfl

/-! ### Probes 23--24: repeat the split on the separable source scope -/

/-- Fan dominance only where both source norms exist.  This is an exploration
predicate, not a proposed production replacement. -/
def HasFanDominanceSeparableWhereDefined
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [TopologicalSpace.SeparableSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    [TopologicalSpace.SeparableSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤ →
    N.toSymmetricOperatorIdealFamily.gauge B ≠ ⊤ →
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- The extra ideal-solidity statement hidden inside unconditional `ENNReal`
Fan dominance: weak Ky Fan domination by a member forces membership. -/
def HasKyFanMembershipTransferSeparable
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [TopologicalSpace.SeparableSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    [TopologicalSpace.SeparableSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    N.toSymmetricOperatorIdealFamily.gauge B ≠ ⊤ →
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤

/-- Unconditional Fan dominance decomposes exactly into where-defined norm
monotonicity plus membership transfer. -/
theorem fanDominanceSeparable_iff_whereDefined_and_membershipTransfer
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) :
    HasFanDominanceSeparable N ↔
      HasFanDominanceSeparableWhereDefined N ∧
        HasKyFanMembershipTransferSeparable N := by
  constructor
  · intro h
    constructor
    · intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B _ _ hAB
      exact h hAB
    · intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hB hAB
      exact ne_top_of_le_ne_top hB (h hAB)
  · rintro ⟨hwhere, htransfer⟩
    intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
    by_cases hB : N.toSymmetricOperatorIdealFamily.gauge B = ⊤
    · rw [hB]
      exact le_top
    · have hA : N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤ :=
        htransfer hB hAB
      exact hwhere hA hB hAB

/-- The finite-rank operator-norm source passes the *where-defined* inequality:
on its ideal, the source gauge is just the operator norm, which is the first Ky
Fan gauge. -/
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_fanDominantWhereDefined :
    HasFanDominanceSeparableWhereDefined (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}) := by
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hA hB hAB
  have hAfin : ProbeFiniteRank A := by
    change finiteRankOperatorNormGauge A ≠ ⊤ at hA
    exact (finiteRankOperatorNormGauge_ne_top_iff A).mp hA
  have hBfin : ProbeFiniteRank B := by
    change finiteRankOperatorNormGauge B ≠ ⊤ at hB
    exact (finiteRankOperatorNormGauge_ne_top_iff B).mp hB
  change finiteRankOperatorNormGauge A ≤ finiteRankOperatorNormGauge B
  rw [finiteRankOperatorNormGauge_of_finiteRank hAfin,
    finiteRankOperatorNormGauge_of_finiteRank hBfin]
  have h1 := hAB 1
  rw [kyFanApproximationGauge_one, kyFanApproximationGauge_one] at h1
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h1

/-- The same counterexample pinpoints the failed component: membership transfer,
not the norm inequality on the finite-rank ideal. -/
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_not_membershipTransfer
    [TopologicalSpace.SeparableSpace FanCounterexampleSpace] :
    ¬ HasKyFanMembershipTransferSeparable (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}) := by
  intro htransfer
  have hB :
      (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}).toSymmetricOperatorIdealFamily.gauge
        fanCounterexampleB ≠ ⊤ := by
    rw [finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_B]
    simp
  have hA := htransfer (A := fanCounterexampleA) (B := fanCounterexampleB)
    hB fanCounterexample_kyFan_domination
  rw [finiteRankNormalizedSymmetricOperatorIdealFamily_gauge_A] at hA
  exact hA rfl

/-!
## Boundary after Probes 17--24 -- COMPILED

This batch compiled cleanly on 2026-09-08.  It is now machine-checked that the
current raw `NormalizedSymmetricOperatorIdealFamily` fields do **not** imply the current
unconditional `HasFanDominance` property.  The finite-rank/operator-norm source
is a counterexample.  The same source satisfies the norm inequality whenever
both norms are defined; what fails is weak-majorization membership transfer.

That result changes the exploration target.  We no longer ask Lean to prove a
false implication from the raw fields.  The next probes ask what different
formal readings of the source's "symmetric gauge function" sentence buy us and
how that interacts with the paper-wide convention that results are vacuous when
a displayed norm fails to exist.
-/

/-!
## Probes 25--31: separate value representation, domain representation, and vacuity

The source language can be read at two different strengths:

* **memberwise/value representation:** on operators for which a source norm
  exists, its value is given by one coherent symmetric norming function;
* **total/domain representation:** the canonical extended symmetric norming
  function agrees with the source extended gauge on every bounded operator, so
  it determines both values and the ideal domain.

The finite-rank/operator-norm countermodel is designed to distinguish them.  On
finite-rank members its value is exactly the first Ky Fan norm, hence it has the
weak/memberwise representation.  But its extended gauge is `∞` on an
infinite-rank compact diagonal even though the first Ky Fan gauge is finite.

The probes below also spell out a total-gauge formulation of the source's
"vacuous when norms fail to exist" convention.  This is exploration-only
semantics; no production theorem is changed here.
-/

/-- Cross-space finite-prefix dominance for a coherent symmetric norming
function.  The production theorem currently has same source/target types; this
local version records that its proof only compares the two finite singular-value
vectors and therefore works across different Hilbert-space pairs. -/
private theorem symmetricNorming_prefixGauge_le_cross
    (M : SymmetricNormingFunction)
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'}
    (h : ∀ k : ℕ, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) (n : ℕ) :
    M.prefixGauge n A ≤ M.prefixGauge n B := by
  let MN := M.finiteNorm n
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  change MN.gauge b (SymmetricNormingFunction.approximationPrefix n A) ≤
    MN.gauge b (SymmetricNormingFunction.approximationPrefix n B)
  apply MN.gauge_le_gauge_of_prefix_sums_le b
  · intro i j hij
    exact approximationSingularValue_antitone A (Fin.le_def.mp hij)
  · intro i
    exact approximationSingularValue_nonneg _ _
  · intro i
    exact approximationSingularValue_nonneg _ _
  · intro m
    rcases le_or_gt m n with hm | hm
    · simp only [SymmetricNormingFunction.approximationPrefix]
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
          (Finset.univ.filter fun i : Fin n => (i : ℕ) < m) =
            Finset.univ :=
        Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
      rw [huniv, SymmetricNormingFunction.sum_approximationPrefix n A,
        SymmetricNormingFunction.sum_approximationPrefix n B]
      exact h n

/-- Cross-space Fan dominance for the canonical extended gauge of one coherent
symmetric norming function. -/
theorem symmetricNorming_extendedGauge_le_cross
    (M : SymmetricNormingFunction)
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'}
    (h : ∀ k : ℕ, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    M.extendedGauge A ≤ M.extendedGauge B := by
  change (⨆ n : ℕ, ENNReal.ofReal (M.prefixGauge n A)) ≤
    (⨆ n : ℕ, ENNReal.ofReal (M.prefixGauge n B))
  apply iSup_le
  intro n
  exact le_trans
    (ENNReal.ofReal_le_ofReal (symmetricNorming_prefixGauge_le_cross M h n))
    (le_iSup (fun m : ℕ => ENNReal.ofReal (M.prefixGauge m B)) n)

/-! ### Probe 25: a weak/memberwise reading of "obtained as a symmetric gauge" -/

/-- One coherent symmetric norming function gives the source norm value on every
operator where that source norm is actually defined.  No claim is made about the
canonical extension away from the source ideal. -/
def HasMemberwiseSymmetricNormingRepresentation
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∃ M : SymmetricNormingFunction,
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (A : E →L[ℂ] F),
      N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤ →
        N.toSymmetricOperatorIdealFamily.gauge A = M.extendedGauge A

/-- The compiled finite-rank/operator-norm countermodel has a memberwise
symmetric-norming representation: on its domain it is just the first Ky Fan norm.
Thus a value-only reading of the source's symmetric-gauge sentence does not by
itself rule out the countermodel. -/
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_hasMemberwiseSymmetricNormingRepresentation :
    HasMemberwiseSymmetricNormingRepresentation
      (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}) := by
  have h1 : 0 < (1 : ℕ) := by omega
  refine ⟨kyFanNormingFunction 1 h1, ?_⟩
  intro E F _ _ _ _ _ _ A hA
  change finiteRankOperatorNormGauge A ≠ ⊤ at hA
  have hAfin : ProbeFiniteRank A :=
    (finiteRankOperatorNormGauge_ne_top_iff A).mp hA
  change finiteRankOperatorNormGauge A =
    (kyFanNormingFunction 1 h1).extendedGauge A
  rw [finiteRankOperatorNormGauge_of_finiteRank hAfin,
    kyFanNormingFunction_extendedGauge,
    kyFanApproximationGauge_one, ← ofReal_norm]

/-! ### Probe 26: memberwise representation gives exactly the where-defined Fan inequality -/

/-- Once one coherent symmetric norming function represents the values on the
source ideal, ordinary Fan dominance follows whenever both displayed norms
exist.  No membership-transfer conclusion is used. -/
theorem fanDominantWhereDefined_of_memberwiseSymmetricNormingRepresentation
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hrep : HasMemberwiseSymmetricNormingRepresentation N) :
    HasFanDominanceWhereDefined N := by
  rcases hrep with ⟨M, hM⟩
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hA hB hAB
  rw [hM A hA, hM B hB]
  exact symmetricNorming_extendedGauge_le_cross M hAB

/-- The value-only symmetric-norming statement is strictly weaker than the
current production `HasFanDominance`: the compiled finite-rank source satisfies
the former and refutes the latter. -/
theorem memberwiseSymmetricNormingRepresentation_does_not_imply_fanDominance :
    ∃ N : NormalizedSymmetricOperatorIdealFamily.{0, 0} ℂ,
      HasMemberwiseSymmetricNormingRepresentation N ∧ ¬ N.HasFanDominance := by
  refine ⟨finiteRankNormalizedSymmetricOperatorIdealFamily.{0},
    finiteRankNormalizedSymmetricOperatorIdealFamily_hasMemberwiseSymmetricNormingRepresentation,
    finiteRankNormalizedSymmetricOperatorIdealFamily_not_fanDominant⟩

/-! ### Probe 27: formalize the source's paper-wide vacuity convention -/

/-- Total-gauge form of: if one of the displayed source norms does not exist,
the comparison is treated as vacuous; otherwise the Fan inequality must hold.
This is an exploration predicate, not a production proposal. -/
def HasFanDominanceWithVacuity
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      (N.toSymmetricOperatorIdealFamily.gauge A = ⊤ ∨
        N.toSymmetricOperatorIdealFamily.gauge B = ⊤) ∨
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- The explicit-vacuity contract is exactly the earlier where-defined contract.
This theorem is bookkeeping, but it makes the semantic difference from the
current unconditional `ENNReal` inequality visible in the type. -/
theorem fanDominanceWithVacuity_iff_whereDefined
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) :
    HasFanDominanceWithVacuity N ↔ HasFanDominanceWhereDefined N := by
  constructor
  · intro hv E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hA hB hAB
    rcases hv hAB with hmissing | hle
    · rcases hmissing with hAtop | hBtop
      · exact (hA hAtop).elim
      · exact (hB hBtop).elim
    · exact hle
  · intro hwhere E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
    by_cases hA : N.toSymmetricOperatorIdealFamily.gauge A = ⊤
    · exact Or.inl (Or.inl hA)
    · by_cases hB : N.toSymmetricOperatorIdealFamily.gauge B = ⊤
      · exact Or.inl (Or.inr hB)
      · exact Or.inr (hwhere hA hB hAB)

/-- Memberwise symmetric-norming representation is sufficient for the explicit
vacuity reading of the Fan sentence. -/
theorem fanDominanceWithVacuity_of_memberwiseSymmetricNormingRepresentation
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hrep : HasMemberwiseSymmetricNormingRepresentation N) :
    HasFanDominanceWithVacuity N := by
  rw [fanDominanceWithVacuity_iff_whereDefined]
  exact fanDominantWhereDefined_of_memberwiseSymmetricNormingRepresentation N hrep

/-! ### Probe 28: a strong/total reading of "obtained as a symmetric gauge" -/

/-- Strong reading: one canonical symmetric-norming extension agrees with the
source's total `ENNReal` gauge on *every* bounded operator.  Unlike the
memberwise statement, this fixes the ideal domain as well as norm values. -/
def HasTotalSymmetricNormingRepresentation
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∃ M : SymmetricNormingFunction,
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (A : E →L[ℂ] F),
      N.toSymmetricOperatorIdealFamily.gauge A = M.extendedGauge A

/-- A total canonical symmetric-norming representation is strong enough to
recover the current production `HasFanDominance`, including membership
transfer. -/
theorem fanDominance_of_totalSymmetricNormingRepresentation
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hrep : HasTotalSymmetricNormingRepresentation N) :
    N.HasFanDominance := by
  rcases hrep with ⟨M, hM⟩
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
  rw [hM A, hM B]
  exact symmetricNorming_extendedGauge_le_cross M hAB

/-- Total representation trivially restricts to memberwise representation. -/
theorem memberwiseSymmetricNormingRepresentation_of_total
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hrep : HasTotalSymmetricNormingRepresentation N) :
    HasMemberwiseSymmetricNormingRepresentation N := by
  rcases hrep with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro E F _ _ _ _ _ _ A _
  exact hM A

/-! ### Probes 29--30: identify the exact extra content of the production property -/

/-- Once memberwise symmetric-norming representation is granted, the only extra
content of current unconditional Fan dominance is Ky-Fan membership transfer. -/
theorem fanDominance_iff_membershipTransfer_of_memberwiseRepresentation
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hrep : HasMemberwiseSymmetricNormingRepresentation N) :
    N.HasFanDominance ↔ HasKyFanMembershipTransfer N := by
  have hwhere : HasFanDominanceWhereDefined N :=
    fanDominantWhereDefined_of_memberwiseSymmetricNormingRepresentation N hrep
  constructor
  · intro hfan
    exact ((fanDominance_iff_whereDefined_and_membershipTransfer N).mp hfan).2
  · intro htransfer
    exact (fanDominance_iff_whereDefined_and_membershipTransfer N).mpr
      ⟨hwhere, htransfer⟩

/-- A compact witness to the semantic split established by this exploration:
there exists a raw source norm with a coherent symmetric-norming formula on its
entire domain and with the explicit-vacuity Fan property, yet without the
current unconditional production property. -/
theorem exists_memberwise_vacuous_but_not_unconditional_fanDominance :
    ∃ N : NormalizedSymmetricOperatorIdealFamily.{0, 0} ℂ,
      HasMemberwiseSymmetricNormingRepresentation N ∧
      HasFanDominanceWithVacuity N ∧
      ¬ N.HasFanDominance := by
  refine ⟨finiteRankNormalizedSymmetricOperatorIdealFamily.{0},
    finiteRankNormalizedSymmetricOperatorIdealFamily_hasMemberwiseSymmetricNormingRepresentation,
    ?_, finiteRankNormalizedSymmetricOperatorIdealFamily_not_fanDominant⟩
  exact fanDominanceWithVacuity_of_memberwiseSymmetricNormingRepresentation
    finiteRankNormalizedSymmetricOperatorIdealFamily.{0}
    finiteRankNormalizedSymmetricOperatorIdealFamily_hasMemberwiseSymmetricNormingRepresentation

/-!
## Boundary after Probes 25--30

If this batch compiles, the exploration has isolated a precise semantic fork.
The already-compiled countermodel is compatible with all of the following:

* the current raw source ideal/norm laws;
* a single coherent symmetric-norming formula for every value on its domain;
* Ky Fan monotonicity whenever the two displayed norms exist; and
* an explicit formalization of the paper-wide convention that a comparison is
  vacuous when a displayed norm fails to exist.

It still fails current production `HasFanDominance`, solely because that total
`ENNReal` inequality additionally forces weak-majorization closure of the norm's
**domain**.  In contrast, a total/canonical symmetric-norming representation of
the extended gauge *does* imply the production property.

Therefore the next source-exactness decision should be made from the meaning of
Davis--Kahan's Section 1 sentence that every unitary-invariant norm is obtained
as a symmetric gauge function, together with their explicit vacuity convention
and the cited Ky Fan theorem.  The key question is no longer whether Fan
monotonicity is true; it is whether the source imports **domain solidity** as
part of the mathematical notion of its norm ideal.  Do not modify production
structures until that question is settled.
-/


/-! ### Probe 31: state the source's class-level Fan sentence with vacuity -/

/-- Pairwise source-norm comparison with the paper-wide convention made
explicit: if either displayed norm does not exist, the comparison is vacuous;
otherwise the stored extended gauges are ordered. -/
def SourceVacuousGaugeLe
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (A : E →L[ℂ] F) (B : E' →L[ℂ] F') : Prop :=
  (N.toSymmetricOperatorIdealFamily.gauge A = ⊤ ∨
      N.toSymmetricOperatorIdealFamily.gauge B = ⊤) ∨
    N.toSymmetricOperatorIdealFamily.gauge A ≤
      N.toSymmetricOperatorIdealFamily.gauge B

/-- The left side of Davis--Kahan's strong Fan sentence, interpreted with the
paper-wide vacuity convention: the comparison holds for every source norm. -/
def EverySourceVacuousGaugeLe
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    (A : E →L[ℂ] F) (B : E' →L[ℂ] F') : Prop :=
  ∀ N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ, SourceVacuousGaugeLe N A B

/-- If the external Fan theorem supplies where-defined dominance for every raw
source norm, Ky-Fan majorization implies the source's class-level vacuous
comparison. -/
theorem everySourceVacuousGaugeLe_of_kyFan
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'}
    (hclass : ∀ N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
      HasFanDominanceWhereDefined N)
    (hAB : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) :
    EverySourceVacuousGaugeLe A B := by
  intro N
  exact ((fanDominanceWithVacuity_iff_whereDefined N).2 (hclass N)) hAB

/-! ### Probe 32: put the Ky Fan norms themselves into the raw source class -/

/-- The `k`-th Ky Fan norm, projected from the already-constructed normalized
source member down to the raw printed-law structure. -/
noncomputable def kyFanNormalizedSymmetricOperatorIdealFamily (k : ℕ) (hk : 0 < k) :
    NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ :=
  (kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℂ) k hk).toNormalizedSymmetricOperatorIdealFamily

/-- The raw source gauge of the Ky Fan source member is exactly the finite Ky Fan
approximation gauge transported to `ENNReal`. -/
@[simp]
theorem gauge_kyFanNormalizedSymmetricOperatorIdealFamily
    (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    (kyFanNormalizedSymmetricOperatorIdealFamily k hk).toSymmetricOperatorIdealFamily.gauge A =
      ENNReal.ofReal (kyFanApproximationGauge k A) := by
  change (kyFanSymmetricIdealFamily (𝕜 := ℂ) k hk).gauge A =
    ENNReal.ofReal (kyFanApproximationGauge k A)
  exact gauge_kyFanSymmetricIdealFamily k hk A

/-- Every bounded operator lies in the raw source member supplied by a finite Ky
Fan norm. -/
theorem mem_kyFanNormalizedSymmetricOperatorIdealFamily
    (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    (kyFanNormalizedSymmetricOperatorIdealFamily k hk).toSymmetricOperatorIdealFamily.gauge A ≠ ⊤ := by
  rw [gauge_kyFanNormalizedSymmetricOperatorIdealFamily]
  exact ENNReal.ofReal_ne_top

/-! ### Probe 33: recover every Ky Fan inequality from the class-level sentence -/

/-- The converse half of the source's strong Fan sentence needs no dominance
assumption: because the source class itself contains every finite Ky Fan norm,
a comparison valid for every source norm implies every Ky Fan comparison. -/
theorem kyFan_le_of_everySourceVacuousGaugeLe
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'}
    (h : EverySourceVacuousGaugeLe A B) :
    ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge_zero_index]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hpair := h (kyFanNormalizedSymmetricOperatorIdealFamily k hk)
    rcases hpair with hmissing | hle
    · rcases hmissing with hAtop | hBtop
      · exact (mem_kyFanNormalizedSymmetricOperatorIdealFamily k hk A hAtop).elim
      · exact (mem_kyFanNormalizedSymmetricOperatorIdealFamily k hk B hBtop).elim
    · rw [gauge_kyFanNormalizedSymmetricOperatorIdealFamily,
        gauge_kyFanNormalizedSymmetricOperatorIdealFamily] at hle
      exact (ENNReal.ofReal_le_ofReal_iff
        (kyFanApproximationGauge_nonneg k B)).mp hle

/-- Under exactly the missing external theorem -- where-defined Fan dominance
for every source norm -- the paper's class-level "every UIN iff every Ky Fan
norm" sentence becomes a literal Lean equivalence with vacuity explicit. -/
theorem everySourceVacuousGaugeLe_iff_everyKyFan_le
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'}
    (hclass : ∀ N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
      HasFanDominanceWhereDefined N) :
    EverySourceVacuousGaugeLe A B ↔
      ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B := by
  constructor
  · exact kyFan_le_of_everySourceVacuousGaugeLe
  · exact everySourceVacuousGaugeLe_of_kyFan hclass

/-! ### Probe 34: scaled where-defined Fan dominance -/

/-- The scaled form actually consumed by Davis--Kahan estimates.  It follows
from ordinary where-defined Fan dominance by applying that theorem to `c • A`.
No membership transfer is used: membership of `A` is an explicit premise. -/
theorem mul_gaugeReal_le_of_all_mul_kyFan_le_whereDefined
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hfan : HasFanDominanceWhereDefined N)
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'} {c : ℝ}
    (hc : 0 < c)
    (hA : N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤)
    (hB : N.toSymmetricOperatorIdealFamily.gauge B ≠ ⊤)
    (hky : ∀ k, c * kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    c * N.toSymmetricOperatorIdealFamily.gaugeReal A ≤
      N.toSymmetricOperatorIdealFamily.gaugeReal B := by
  let S := N.toSymmetricOperatorIdealFamily
  have hcA : S.Mem (((c : ℂ)) • A) := S.smul_mem (c : ℂ) hA
  have hscaled : ∀ k, kyFanApproximationGauge k (((c : ℂ)) • A) ≤
      kyFanApproximationGauge k B := by
    intro k
    rw [kyFanApproximationGauge_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc.le]
    exact hky k
  have hle : S.gauge (((c : ℂ)) • A) ≤ S.gauge B := hfan hcA hB hscaled
  have hreal : S.gaugeReal (((c : ℂ)) • A) ≤ S.gaugeReal B :=
    (ENNReal.toReal_le_toReal hcA hB).mpr hle
  rw [S.gaugeReal_smul (c : ℂ) hA, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc.le] at hreal
  exact hreal

/-! ### Probe 35: scaled estimates with the paper's vacuity convention -/

/-- A source estimate `c ‖A‖ ≤ ‖B‖` with the paper-wide "norm may fail to
exist" convention made explicit. -/
def ScaledSourceEstimateWithVacuity
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) (c : ℝ)
    (A : E →L[ℂ] F) (B : E' →L[ℂ] F') : Prop :=
  (N.toSymmetricOperatorIdealFamily.gauge A = ⊤ ∨
      N.toSymmetricOperatorIdealFamily.gauge B = ⊤) ∨
    c * N.toSymmetricOperatorIdealFamily.gaugeReal A ≤
      N.toSymmetricOperatorIdealFamily.gaugeReal B

/-- Scaled Ky Fan inequalities imply the corresponding source estimate with
vacuity under only the where-defined form of Fan dominance. -/
theorem scaledSourceEstimateWithVacuity_of_all_mul_kyFan_le
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hfan : HasFanDominanceWhereDefined N)
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'} {c : ℝ}
    (hc : 0 < c)
    (hky : ∀ k, c * kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    ScaledSourceEstimateWithVacuity N c A B := by
  by_cases hA : N.toSymmetricOperatorIdealFamily.gauge A = ⊤
  · exact Or.inl (Or.inl hA)
  · by_cases hB : N.toSymmetricOperatorIdealFamily.gauge B = ⊤
    · exact Or.inl (Or.inr hB)
    · exact Or.inr
        (mul_gaugeReal_le_of_all_mul_kyFan_le_whereDefined
          N hfan hc hA hB hky)

/-! ### Probe 36: the class-wide scaled bridge -/

/-- Once the external Fan theorem is available in its where-defined form for the
source class, a scaled Ky Fan estimate transports to every source norm with the
paper's vacuity semantics and without any membership-transfer theorem. -/
theorem everySource_scaledEstimateWithVacuity_of_all_mul_kyFan_le
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'} {c : ℝ}
    (hclass : ∀ N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
      HasFanDominanceWhereDefined N)
    (hc : 0 < c)
    (hky : ∀ k, c * kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    ∀ N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
      ScaledSourceEstimateWithVacuity N c A B := by
  intro N
  exact scaledSourceEstimateWithVacuity_of_all_mul_kyFan_le
    N (hclass N) hc hky

/-! ### Probe 37: a source-vacuous sine-theta façade -/

/-- Exploration-only Section 2 façade with the source norm represented by the
raw printed-law structure plus the *where-defined* external Fan theorem.

Unlike the current production `..._sourceExact_complex` façade, this prototype
has no residual-membership premise and no membership-transfer conclusion.  The
paper's global convention is instead visible in `ScaledSourceEstimateWithVacuity`:
if either displayed norm does not exist the conclusion is vacuous, and otherwise
it is exactly `δ · N(sin Θ₀) ≤ N(R)`.

The proof deliberately reuses the already-proved analytic sine-theta theorem only
to obtain the Ky Fan inequalities.  Thus this probe tests theorem-boundary
semantics rather than rebuilding the Davis--Kahan argument. -/
theorem sinTheta_unbounded_formGap_sourceVacuous_complex_probe
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hfan : HasFanDominanceWhereDefined N)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E)
    (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : TauCeti.DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : TauCeti.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) :
    ScaledSourceEstimateWithVacuity N δ
      ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) R := by
  let X := (ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀
  have hky : ∀ k, δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k R := by
    intro k
    by_cases hk0 : k = 0
    · subst k
      simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge_zero_index]
    · have hk : 0 < k := Nat.pos_of_ne_zero hk0
      have hmain :=
        TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex
          (kyFanNormingFunction k hk) A A₀ Λ₁ E₀ F₀ F₁ R
          hA hA₀ hΛ₁ htrial hexact hδ hgap
          (kyFanNormingFunction_mem k hk R)
      simpa only [X, kyFanNormingFunction_gauge] using hmain.2
  change ScaledSourceEstimateWithVacuity N δ X R
  exact scaledSourceEstimateWithVacuity_of_all_mul_kyFan_le N hfan hδ hky

/-!
## Boundary after Probes 31--37 -- COMPILED

The user compiled Probes 31--37 cleanly on 2026-09-08.  They mechanically
separate the public Davis--Kahan inequality from the stronger domain-solidity
property currently bundled into production `HasFanDominance`.

The source/literature audit performed after that compile gives a concrete reason
to test the vacuous boundary as the source-facing one:

* Davis--Kahan explicitly say that some results are vacuous when the relevant
  norms fail to exist.
* In Section 1 they cite Gohberg--Krein, Chapter III, Section 3 for the Ky Fan
  theorem.  That section is the symmetric-norming-function section; the
  construction of symmetrically normed ideals generated by a symmetric norming
  function is the following Section 4.
* The historical operator-ideal theory distinguishes the value formula supplied
  by a symmetric norming function from the choice of ideal/domain.  Thus the
  membership-transfer assertion should not be silently inserted into the
  printed theorem merely because it is available for a canonical generated
  domain.

The next probes therefore do not attempt another infinite-dimensional dominance
proof.  They verify that the proposed vacuity proposition is exactly a partial
norm inequality, exhibit the actual sine-theta theorem at that boundary on the
compiled countermodel, prove that this countermodel cannot come from the current
normalized production class, and package the exact class-level source-facing
conclusion.  These are theorem-signature probes, not production changes.
-/

/-! ### Probe 38: vacuity is exactly a partial-norm implication -/

/-- `SourceVacuousGaugeLe` is not an extra inequality.  It is exactly the
ordinary gauge comparison conditional on both displayed source norms existing. -/
theorem sourceVacuousGaugeLe_iff_defined_implication
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'} :
    SourceVacuousGaugeLe N A B ↔
      (N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤ →
        N.toSymmetricOperatorIdealFamily.gauge B ≠ ⊤ →
        N.toSymmetricOperatorIdealFamily.gauge A ≤
          N.toSymmetricOperatorIdealFamily.gauge B) := by
  constructor
  · intro h hA hB
    rcases h with hmissing | hle
    · rcases hmissing with hAtop | hBtop
      · exact (hA hAtop).elim
      · exact (hB hBtop).elim
    · exact hle
  · intro h
    by_cases hA : N.toSymmetricOperatorIdealFamily.gauge A = ⊤
    · exact Or.inl (Or.inl hA)
    · by_cases hB : N.toSymmetricOperatorIdealFamily.gauge B = ⊤
      · exact Or.inl (Or.inr hB)
      · exact Or.inr (h hA hB)

/-- The scaled Davis--Kahan wrapper has the same exact semantics: once both
norms exist it is precisely the printed real-valued inequality, and otherwise
the result is vacuous. -/
theorem scaledSourceEstimateWithVacuity_iff_defined_implication
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'} {c : ℝ} :
    ScaledSourceEstimateWithVacuity N c A B ↔
      (N.toSymmetricOperatorIdealFamily.gauge A ≠ ⊤ →
        N.toSymmetricOperatorIdealFamily.gauge B ≠ ⊤ →
        c * N.toSymmetricOperatorIdealFamily.gaugeReal A ≤
          N.toSymmetricOperatorIdealFamily.gaugeReal B) := by
  constructor
  · intro h hA hB
    rcases h with hmissing | hle
    · rcases hmissing with hAtop | hBtop
      · exact (hA hAtop).elim
      · exact (hB hBtop).elim
    · exact hle
  · intro h
    by_cases hA : N.toSymmetricOperatorIdealFamily.gauge A = ⊤
    · exact Or.inl (Or.inl hA)
    · by_cases hB : N.toSymmetricOperatorIdealFamily.gauge B = ⊤
      · exact Or.inl (Or.inr hB)
      · exact Or.inr (h hA hB)

/-! ### Probe 39: normalized source norms imply only more than we need -/

/-- Any current production normalized norm supplies the where-defined Fan
property after forgetting its stronger membership-transfer field. -/
theorem normalizedUnitaryInvariantNorm_hasFanDominanceWhereDefined
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ) :
    HasFanDominanceWhereDefined N.toNormalizedSymmetricOperatorIdealFamily :=
  ((fanDominance_iff_whereDefined_and_membershipTransfer N.toNormalizedSymmetricOperatorIdealFamily).mp
    N.toNormalizedSymmetricOperatorIdealFamily_hasFanDominance).1

/-- The compiled finite-rank source norm is outside the image of the current
normalized production class.  Thus a theorem quantifying only over normalized
norms genuinely excludes raw source norms that satisfy the printed-law
abstraction and where-defined Fan comparison. -/
theorem finiteRankNormalizedSymmetricOperatorIdealFamily_not_from_normalizedUnitaryInvariantNorm :
    ¬ ∃ N : NormalizedUnitaryInvariantNorm.{0, 0} ℂ,
      N.toNormalizedSymmetricOperatorIdealFamily = finiteRankNormalizedSymmetricOperatorIdealFamily.{0} := by
  rintro ⟨N, hN⟩
  have hfan : N.toNormalizedSymmetricOperatorIdealFamily.HasFanDominance := N.toNormalizedSymmetricOperatorIdealFamily_hasFanDominance
  rw [hN] at hfan
  exact finiteRankNormalizedSymmetricOperatorIdealFamily_not_fanDominant hfan

/-! ### Probe 40: the actual sine theorem survives on the countermodel -/

/-- The Section 2 sine-theta statement, with the paper's vacuity convention,
holds for the finite-rank/operator-norm source countermodel even though that
norm is not a `NormalizedUnitaryInvariantNorm`.

This is deliberately universe-zero only because the concrete countermodel was
constructed there.  It is enough to witness the theorem-signature distinction. -/
theorem sinTheta_unbounded_formGap_finiteRankSourceVacuous_complex_probe
    {E F G H : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E)
    (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : TauCeti.DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : TauCeti.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) :
    ScaledSourceEstimateWithVacuity (finiteRankNormalizedSymmetricOperatorIdealFamily.{0}) δ
      ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) R :=
  sinTheta_unbounded_formGap_sourceVacuous_complex_probe
    (finiteRankNormalizedSymmetricOperatorIdealFamily.{0})
    finiteRankNormalizedSymmetricOperatorIdealFamily_fanDominantWhereDefined_unrestricted
    A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ hgap

/-! ### Probe 41: normalized norms also admit the weaker source boundary -/

/-- Even if the implementation continues to prove the stronger normalized
theorem internally, its source-facing wrapper need not expose residual
membership or a membership-transfer conclusion. -/
theorem sinTheta_unbounded_formGap_normalizedAsSourceVacuous_complex_probe
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E)
    (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : TauCeti.DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : TauCeti.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) :
    ScaledSourceEstimateWithVacuity N.toNormalizedSymmetricOperatorIdealFamily δ
      ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) R :=
  sinTheta_unbounded_formGap_sourceVacuous_complex_probe
    N.toNormalizedSymmetricOperatorIdealFamily (normalizedUnitaryInvariantNorm_hasFanDominanceWhereDefined N)
    A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ hgap

/-! ### Probe 42: package the literal source-facing norm quantifier -/

/-- Exploration-only proposition matching the norm part of the printed sine
theorem: for every source UIN, the displayed inequality holds whenever its two
displayed norms exist, and is otherwise vacuous.

There is intentionally no `N` argument, no residual-membership premise, and no
membership conclusion in this public proposition. -/
def EverySourceSinThetaEstimateWithVacuity
    {E F H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (δ : ℝ) (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E)
    (R : F →L[ℂ] E) : Prop :=
  ∀ N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
    ScaledSourceEstimateWithVacuity N δ
      ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) R

/-- If the historical Ky Fan theorem supplies the still-missing class theorem at
the where-defined scope, the exact public norm quantifier follows with no
membership hypotheses or conclusions.

This theorem isolates the sole remaining mathematical obligation from the
source-facing Davis--Kahan statement. -/
theorem everySourceSinThetaEstimateWithVacuity_of_whereDefinedFanClass
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hclass : ∀ N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
      HasFanDominanceWhereDefined N)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E)
    (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : TauCeti.DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : TauCeti.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) :
    EverySourceSinThetaEstimateWithVacuity δ E₀ F₀ R := by
  intro N
  exact sinTheta_unbounded_formGap_sourceVacuous_complex_probe
    N (hclass N) A A₀ Λ₁ E₀ F₀ F₁ R
    hA hA₀ hΛ₁ htrial hexact hδ hgap

/-! ### Probe 43: the candidate source signature has no hidden membership data -/

/-- Expanded characterization of the candidate class-level conclusion.  This
keeps the exact theorem boundary auditable: the only norm-side hypotheses are
that both displayed partial norms exist, and those hypotheses occur under the
universal norm quantifier rather than as caller-visible theorem premises. -/
theorem everySourceSinThetaEstimateWithVacuity_iff
    {E F H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {δ : ℝ} {E₀ : F →L[ℂ] E} {F₀ : H →L[ℂ] E}
    {R : F →L[ℂ] E} :
    EverySourceSinThetaEstimateWithVacuity δ E₀ F₀ R ↔
      ∀ N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
        N.toSymmetricOperatorIdealFamily.gauge
            ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≠ ⊤ →
        N.toSymmetricOperatorIdealFamily.gauge R ≠ ⊤ →
        δ * N.toSymmetricOperatorIdealFamily.gaugeReal
            ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
          N.toSymmetricOperatorIdealFamily.gaugeReal R := by
  constructor
  · intro h N hSin hR
    exact (scaledSourceEstimateWithVacuity_iff_defined_implication
      (N := N)).mp (h N) hSin hR
  · intro h N
    exact (scaledSourceEstimateWithVacuity_iff_defined_implication
      (N := N)).mpr (h N)

/-! ### Probes 44--46: keep the source norm boundary scalar-generic

These probes were added after a source-review failure mode became visible in the
public API: a repair would land at `ℂ` while the `ℝ` sibling or shared `RCLike`
surface remained on an older statement boundary.  The three surfaces must be
reviewed together.

Probes 44 and 45 compiled on 2026-09-09 and were then promoted to production.
The original Probe 46 also compiled after opening the repository's intentionally scoped
completeness instance for projected subspaces.  The directed residual engine was then
factored over `RCLike`; the current Probes 46 and 47 call that production directed endpoint
and the complete `SectionTwo.sinTwoTheta` endpoint respectively.  They are conformance
probes and have not yet been compiler-validated in this revision.

The theorem names below deliberately do **not** say `sourceExact`.  Fidelity is
metadata owned by the result ledger; these declarations are only compile probes.
-/

open scoped TauCeti.CompleteSubspace

universe u

/-- **Probe 44: the repaired sine-theta norm boundary is available at arbitrary
`RCLike` scalar field.**

This is the scalar-generic counterpart of the fixed-field where-defined wrappers:
no residual-membership premise is needed to invoke the theorem, and no membership
transfer is concluded.  The two `N.Mem` arrows are the source's convention that
the displayed inequality is asserted where both partial norms are defined. -/
theorem sinTheta_unbounded_formGap_whereDefinedUIN_rclike_probe
    {𝕜 : Type u} [RCLike 𝕜]
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : TauCeti.DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : TauCeti.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) →
    N.Mem R →
      δ * N.gaugeReal ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gaugeReal R := by
  exact TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_rclike
    (𝕜 := 𝕜) N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ hgap

/-- **Probe 45: the ambient `sin 2Θ` clause has the same where-defined RCLike
boundary.**

The existing analytic theorem is already scalar-generic.  This probe changes only
the norm boundary, using every Ky Fan norm and then where-defined Fan dominance.
The factor two is handled by proving the equivalent `(δ / 2)` estimate first. -/
theorem sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike_probe
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (Hop : E →L[𝕜] E) (hHop : Hop.IsSymmetric)
    {P Q : Submodule 𝕜 E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) →
    N.Mem Hop →
      δ * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gaugeReal Hop := by
  exact TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike
    (𝕜 := 𝕜) N hA Hop hHop hPred hQred hδ hgap

/-- **Probe 46: the production directed `sin 2Θ₀` theorem is scalar-generic.**

This is now a conformance probe rather than an assumed-core probe.  It exercises the
production reducing-subspace/residual engine all the way through the where-defined UIN
boundary over arbitrary `RCLike`. -/
theorem sinTwoTheta_directed_whereDefinedUIN_rclike_production_probe
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {trial gapCarrier : Submodule 𝕜 E}
    [trial.HasOrthogonalProjection] [gapCarrier.HasOrthogonalProjection]
    {M : trial →L[𝕜] trial} {R : trial →L[𝕜] E}
    (hred : TauCeti.LinearPMap.ReducesSubspace A gapCarrier)
    (htrialDom : ∀ v : trial, (v : E) ∈ A.domain)
    (hres : ∀ v : trial, A ⟨(v : E), htrialDom v⟩ = R v + ((M v : trial) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A gapCarrier hred)
      (TauCeti.LinearPMap.reducingRestriction A gapCarrierᗮ hred.orthogonal) δ) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) →
    N.Mem R →
      δ * N.gaugeReal
          (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ≤
        2 * N.gaugeReal R := by
  exact TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_whereDefinedUIN_rclike
    N hA hred htrialDom hres hδ hgap

/-- **Probe 47: the complete short `SectionTwo.sinTwoTheta` API is scalar-generic.**

This probe exercises both printed clauses under one shared source setup: the unperturbed
reducing subspace, the perturbed reducing subspace, the trial residual of `A + H`, and the
gap on the two perturbed reducing restrictions. -/
theorem sinTwoTheta_complete_whereDefinedUIN_rclike_production_probe
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (Hop : E →L[𝕜] E) (hHop : Hop.IsSymmetric)
    {P Q : Submodule 𝕜 E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {M : P →L[𝕜] P} {R : P →L[𝕜] E}
    (hPdom : ∀ p : P, (p : E) ∈ (TauCeti.LinearPMap.addBounded A Hop).domain)
    (hres : ∀ p : P,
      (TauCeti.LinearPMap.addBounded A Hop) ⟨(p : E), hPdom p⟩ =
        R p + ((M p : P) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    (N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) →
      N.Mem R →
        δ * N.gaugeReal (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal R) ∧
    (N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) →
      N.Mem Hop →
        δ * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal Hop) := by
  constructor
  · exact TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_whereDefinedUIN_rclike
      N (DavisKahan.addBounded_isSelfAdjoint A hA Hop hHop) hQred hPdom hres hδ hgap
  · exact TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike
      N hA Hop hHop hPred hQred hδ hgap

/-!
## Boundary after Probes 44--47

Probes 44 and 45 are conformance checks for the promoted scalar-generic `sin Θ` and ambient
`sin 2Θ` endpoints.  Probe 46 now calls the production scalar-generic directed residual
engine directly; there is no assumed fixed-field core.  Probe 47 calls the complete
`SectionTwo.sinTwoTheta` API carrying both boxed Section 2 conclusions under one shared
setup.  Fidelity remains attested by the result ledger rather than by these probe names.
-/

/-!
## Boundary after Probes 38--43

If this batch compiles, the Lean exploration has finished the theorem-signature
part of the source audit.

* Probe 38 certifies that the proposed vacuity wrappers are exactly partial-norm
  implications, not a weakened numerical estimate hidden behind `ENNReal`.
* Probe 39 proves that the current normalized quantifier is genuinely narrower
  than the raw source quantifier: the finite-rank source countermodel cannot be
  the `toNormalizedSymmetricOperatorIdealFamily` of any `NormalizedUnitaryInvariantNorm`.
* Probe 40 applies the actual Davis--Kahan sine-theta analytic result to that
  excluded raw source norm at the vacuous/where-defined boundary.
* Probe 41 shows that no proof strength is lost internally by presenting a
  normalized theorem through the weaker source boundary.
* Probes 42--43 package and expand the candidate public quantifier.  There is no
  caller-visible `N.Mem R`, no `N.Mem sinTheta` conclusion, and no hidden
  membership transfer.  The remaining foundation theorem is exactly
  `∀ N : NormalizedSymmetricOperatorIdealFamily, HasFanDominanceWhereDefined N`.

The source audit now points to this boundary as the semantically aligned one.
Davis--Kahan's explicit "vacuous when certain norms fail to exist" convention is
represented literally, while their cited Ky Fan result supplies the comparison
of norm values.  A stronger generated/maximal ideal interpretation may still be
useful internally, but its domain-solidity consequence should not appear in the
source-facing theorem type unless a historical source is found that makes that
extra domain assertion part of Davis--Kahan's quantifier.

Do not edit production in the same commit as this probe batch.  First compile
this file.  After a clean compile, the production change should be a separate,
reviewable step: introduce the source partial/vacuous comparison at the
appropriate reusable layer, prove the historical where-defined Fan theorem for
the intended source UIN representation, and retarget the canonical Davis--Kahan
facades to the class-level source proposition above.
-/

end

end FanDominanceExploration
end ExactSinTheta
end DavisKahan
end TauCeti
