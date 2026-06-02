/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.Delta
import LeanPool.ZhangYeungInequality.Prelude
import LeanPool.ZhangYeungInequality.PFR.ForMathlib.ConditionalIndependence

/-!
# The Zhang-Yeung copy lemma

The **copy lemma** of [@zhangyeung1998, §III, eqs. 44-45] is the auxiliary-probability
construction
at the heart of the 1998 proof of Theorem 3. Given four discrete random variables `X, Y,
Z, U` on a
probability space `(Ω, μ)`, it produces an extended space `(Ω', ν)` carrying a second
conditionally-independent copy `(X₁, Y₁)` of `(X, Y)` over the shared variables `(Z,
U)`. The
auxiliary law is the paper's

  `q(x, y, z, u, x₁, y₁) := p(x, y, z, u) p(x₁, y₁, z, u) / p(z, u)`   (eq. 44)

and this module formalizes it via PFR's `ProbabilityTheory.condIndep_copies` applied to
the pair
`⟨X, Y⟩` conditioned on the shared variable `⟨Z, U⟩`. The module then ships Lemma 2 (eq.
45),

  `Δ(Z, U | X, Y) = I(X; Y₁) - I(X; Y₁ | U) - I(X; Y₁ | Z) - I(Z; U | X, Y₁)`,

both as an abstract Shannon identity (under the hypothesis that one conditional mutual
information
vanishes) and as its Zhang-Yeung-flavored specialization to the copy projections. The
three
subtracted conditional mutual informations on the right are each nonnegative, so the
identity
immediately yields the inequality `Δ(Z, U | X, Y) ≤ I(X; Y₁)` (and the `X ↔ X₁`
symmetric variant
`I(Z; U) - 2·I(Z; U | X) ≤ I(X; X₁)`) -- the two inputs to the Shannon chase that proves
Theorem 3
in the next milestone.

## Main statements

- `ZhangYeung.copyLemma`: the main existential, producing `Ω', ν, X', Y', X₁, Y₁, Z',
  U'` together
  with the three structural facts of eq. (44) (two 4-variable `IdentDistrib`s and one
  `CondIndepFun`) and the six measurabilities.
- `ZhangYeung.delta_of_condMI_vanishes_eq`: Lemma 2 in abstract form -- under the
  hypothesis `I[A :
  D | ⟨B, C⟩; ν] = 0`, the delta identity `Δ(B, C | A, D) = I(A; D) - I(A; D | B) - I(A;
  D | C) -
  I(B; C | ⟨A, D⟩)`.
- `ZhangYeung.copyLemma_delta_transport_Y_to_Y₁`,
  `ZhangYeung.copyLemma_delta_transport_X_to_X₁`:
  bridge identities between `Δ` computed under the original law `μ` and `Δ` computed
  under the copy
  law `ν`, with either `(X, Y)` or `(X, X₁)` in the measured slots.
- `ZhangYeung.copyLemma_delta_identity_Y₁`, `ZhangYeung.copyLemma_delta_identity_X_X₁`:
  Lemma 2
  specialized to the copy's projections.
- `ZhangYeung.copyLemma_delta_le_mutualInfo_Y₁`,
  `ZhangYeung.copyLemma_delta_le_mutualInfo_X_X₁`:
  the inequality-form corollaries combining the delta identity with nonnegativity of the
  three
  conditional mutual information terms on the right of eq. (45).

## Implementation notes

The main `copyLemma` is a direct wrapper around `ProbabilityTheory.condIndep_copies`
applied to
`⟨X, Y⟩ : Ω → S₁ × S₂` with shared variable `⟨Z, U⟩ : Ω → S₃ × S₄`.
`condIndep_copies`
returns two
pair-valued copies `W₁, W₂` and a shared pair-valued variable `V`; we project to the six
individual
random variables `X', Y', X₁, Y₁, Z', U'` via `Prod.fst`/`Prod.snd`. The 4-variable
`IdentDistrib`
outputs are recovered from the 2-level `IdentDistrib`s PFR supplies by composition with
a
measurable rearrangement `((s₁, s₂), (s₃, s₄)) ↦ (s₁, s₂, s₃, s₄)`.

The four codomains `S₁, S₂, S₃, S₄` are bound at a common universe `u` because
`condIndep_copies`
binds its two codomains at a single universe. This is a deviation from
`ZhangYeung/Delta.lean`'s
`Type*` convention, made here because `condIndep_copies` itself requires it.

The derived corollaries (delta transports, delta identities, delta ≤ mutualInfo) live in
their own
`section Consequences` with a shared `variable` block packaging the eight relevant
hypotheses (six
measurabilities, two `IdentDistrib`s, one `CondIndepFun`). A caller of `copyLemma`
produces these
eight hypotheses with one `obtain`, then applies the corollaries as black-box Shannon
identities.

`ZhangYeung.condIndepFun_comp` (post-composition of `CondIndepFun` on its two measured
coordinates)
was promoted to `ZhangYeung/Prelude.lean` when M3 became its second consumer.
`IdentDistrib.condMutualInfo_eq` now lives there as well, promoted for M5's tuple-level
delta
transports.

## References

* [@zhangyeung1998, §III, eq. 44-45, Lemma 2] -- see
  `references/transcriptions/zhangyeung1998.md`
  for a verbatim transcription of equations (44) and (45), verified 2026-04-16.

## Tags

Shannon entropy, conditional mutual information, copy lemma, conditional independence,
Zhang-Yeung
-/

namespace ZhangYeung

open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR

universe u

/-! ### The main copy construction -/

/--
**The Zhang-Yeung copy lemma** [@zhangyeung1998, §III, eq. 44]. Given four discrete
random
variables `X, Y, Z, U` on a probability space `(Ω, μ)`, there exists an extended
probability space
`(Ω', ν)` carrying six projected random variables `X', Y', X₁, Y₁, Z', U'` such that
`(X', Y', Z',
U')` and `(X₁, Y₁, Z', U')` each have the original joint law of `(X, Y, Z, U)` under
`μ`, and the
two pairs `(X', Y')` and `(X₁, Y₁)` are conditionally independent given the shared pair
`(Z', U')`.
This is a direct wrapper around `ProbabilityTheory.condIndep_copies` applied to `⟨X, Y⟩`
conditioned on `⟨Z, U⟩`.
-/
theorem copyLemma
    {Ω : Type*} [MeasurableSpace Ω]
    {S₁ S₂ S₃ S₄ : Type u}
    [MeasurableSpace S₁] [MeasurableSpace S₂]
    [MeasurableSpace S₃] [MeasurableSpace S₄]
    [Finite S₃] [Finite S₄]
    [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → S₁) (Y' : Ω' → S₂)
        (X₁ : Ω' → S₁) (Y₁ : Ω' → S₂)
        (Z' : Ω' → S₃) (U' : Ω' → S₄),
      IsProbabilityMeasure ν ∧
      Measurable X' ∧ Measurable Y' ∧
      Measurable X₁ ∧ Measurable Y₁ ∧
      Measurable Z' ∧ Measurable U' ∧
      IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      CondIndepFun (fun ω' => (X' ω', Y' ω'))
                   (fun ω' => (X₁ ω', Y₁ ω'))
                   (fun ω' => (Z' ω', U' ω')) ν := by
  obtain ⟨Ω', mΩ', W₁, W₂, V, ν, hIsProb, hW₁, hW₂, hV, hCond, hIdent₁,
    hIdent₂⟩ :=
    condIndep_copies (⟨X, Y⟩ : Ω → S₁ × S₂) (⟨Z, U⟩ : Ω → S₃ × S₄)
      (hX.prodMk hY) (hZ.prodMk hU) μ
  have hr : Measurable
      (fun p : (S₁ × S₂) × (S₃ × S₄) => (p.1.1, p.1.2, p.2.1, p.2.2)) := by fun_prop
  refine ⟨Ω', mΩ', ν, fun ω => (W₁ ω).1, fun ω => (W₁ ω).2,
      fun ω => (W₂ ω).1, fun ω => (W₂ ω).2,
      fun ω => (V ω).1, fun ω => (V ω).2,
      hIsProb,
      measurable_fst.comp hW₁, measurable_snd.comp hW₁,
      measurable_fst.comp hW₂, measurable_snd.comp hW₂,
      measurable_fst.comp hV, measurable_snd.comp hV,
      hIdent₁.comp hr, hIdent₂.comp hr, hCond⟩

/-! ### Lemma 2 (abstract Shannon identity) -/

/-- **Lemma 2 (abstract form) of [@zhangyeung1998, §III, eq. 45].** For any four
discrete random
variables `A, B, C, D` on a probability space `(Ω, ν)` with `I[A : D | ⟨B, C⟩; ν] = 0`,

  `Δ(B, C | A, D) = I[A : D] - I[A : D | B] - I[A : D | C] - I[B : C | ⟨A, D⟩]`.

This is the paper's eq. (45) abstracted away from the copy construction: the identity
holds
whenever one conditional mutual information vanishes. The three subtracted conditional
mutual
informations on the right are each nonnegative, so this identity immediately implies the
paper's
inequality form `Δ(B, C | A, D) ≤ I[A : D]` via `linarith`. -/
theorem delta_of_condMI_vanishes_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ δ : Type*}
    [Finite α] [Finite β] [Finite γ] [Finite δ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    {A : Ω → α} {B : Ω → β} {C : Ω → γ} {D : Ω → δ}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hVanish : I[A : D|⟨B, C⟩;ν] = 0) :
    delta B C A D ν
      = I[A : D; ν] - I[A : D | B; ν] - I[A : D | C; ν]
        - I[B : C | ⟨A, D⟩; ν] := by
  have hBC : Measurable (fun ω => (B ω, C ω)) := hB.prodMk hC
  have hAD : Measurable (fun ω => (A ω, D ω)) := hA.prodMk hD
  rw [delta_def,
      mutualInfo_def B C ν, mutualInfo_def A D ν,
      condMutualInfo_eq hB hC hA ν,
      condMutualInfo_eq hB hC hD ν,
      condMutualInfo_eq hA hD hB ν,
      condMutualInfo_eq hA hD hC ν,
      condMutualInfo_eq hB hC hAD ν]
  rw [condMutualInfo_eq hA hD hBC ν] at hVanish
  rw [chain_rule'' ν hB hA, chain_rule'' ν hC hA, chain_rule'' ν hBC hA,
      chain_rule'' ν hB hD, chain_rule'' ν hC hD, chain_rule'' ν hBC hD,
      chain_rule'' ν hA hB, chain_rule'' ν hD hB, chain_rule'' ν hAD hB,
      chain_rule'' ν hA hC, chain_rule'' ν hD hC, chain_rule'' ν hAD hC,
      chain_rule'' ν hB hAD, chain_rule'' ν hC hAD, chain_rule'' ν hBC hAD]
  rw [chain_rule'' ν hA hBC, chain_rule'' ν hD hBC, chain_rule'' ν hAD hBC] at hVanish
  have e_BA : H[⟨B, A⟩; ν] = H[⟨A, B⟩; ν] := entropy_comm hB hA ν
  have e_CA : H[⟨C, A⟩; ν] = H[⟨A, C⟩; ν] := entropy_comm hC hA ν
  have e_BD : H[⟨B, D⟩; ν] = H[⟨D, B⟩; ν] := entropy_comm hB hD ν
  have e_CD : H[⟨C, D⟩; ν] = H[⟨D, C⟩; ν] := entropy_comm hC hD ν
  have e_ADB : H[⟨fun ω => (A ω, D ω), B⟩; ν] = H[⟨B, fun ω => (A ω, D ω)⟩; ν] :=
    entropy_comm hAD hB ν
  have e_ADC : H[⟨fun ω => (A ω, D ω), C⟩; ν] = H[⟨C, fun ω => (A ω, D ω)⟩; ν] :=
    entropy_comm hAD hC ν
  have e_ABC : H[⟨A, fun ω => (B ω, C ω)⟩; ν] = H[⟨fun ω => (B ω, C ω), A⟩; ν] :=
    entropy_comm hA hBC ν
  have e_DBC : H[⟨D, fun ω => (B ω, C ω)⟩; ν] = H[⟨fun ω => (B ω, C ω), D⟩; ν] :=
    entropy_comm hD hBC ν
  have e_ADBC : H[⟨fun ω => (A ω, D ω), fun ω => (B ω, C ω)⟩; ν]
      = H[⟨fun ω => (B ω, C ω), fun ω => (A ω, D ω)⟩; ν] := entropy_comm hAD hBC ν
  linarith [e_BA, e_CA, e_BD, e_CD, e_ADB, e_ADC, e_ABC, e_DBC, e_ADBC]

/-! ### Consequences

The lemmas in this section are parametrized on the outputs of `copyLemma`. A caller
destructures
`copyLemma` once via `obtain`, producing the eight structural hypotheses (six
measurabilities, two
4-variable `IdentDistrib`s, one `CondIndepFun`), and applies these lemmas one by one. -/

section Consequences

/-! #### Measurable projection helpers

Measurable repackings of a right-associated 4-tuple `(a, b, c, d) : S₁ × S₂ × S₃ × S₄`
into the
three-variable shapes `IdentDistrib.condMutualInfo_eq` consumes. `projZUA` extracts `(c,
d, a)` --
the `(Z, U, X)` triple; `projZUB` extracts `(c, d, b)` -- the `(Z, U, Y)` triple. -/

/-- Repackage a right-associated 4-tuple `(a, b, c, d)` as `(c, d, a)`. -/
private def projZUA {S₁ S₂ S₃ S₄ : Type*} (p : S₁ × S₂ × S₃ × S₄) :
  S₃ × S₄ × S₁ :=
  (p.2.2.1, p.2.2.2, p.1)

/-- Repackage a right-associated 4-tuple `(a, b, c, d)` as `(c, d, b)`. -/
private def projZUB {S₁ S₂ S₃ S₄ : Type*} (p : S₁ × S₂ × S₃ × S₄) :
  S₃ × S₄ × S₂ :=
  (p.2.2.1, p.2.2.2, p.2.1)

private lemma measurable_projZUA {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (projZUA : S₁ × S₂ × S₃ × S₄ → _) := by
  unfold projZUA; fun_prop

private lemma measurable_projZUB {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (projZUB : S₁ × S₂ × S₃ × S₄ → _) := by
  unfold projZUB; fun_prop

/--
Measurability of the `(a, b, c, d) ↦ (c, d)` projection extracting the `(Z, U)` pair
from a
right-associated 4-tuple. Consumed by the two delta transport lemmas to build the
pair-level
`IdentDistrib ⟨Z, U⟩ ~ ⟨Z', U'⟩` from the 4-variable `hFirst` `IdentDistrib`.
-/
private lemma measurable_pairZU {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (fun p : S₁ × S₂ × S₃ × S₄ => (p.2.2.1, p.2.2.2)) := by fun_prop

/-! #### Triple-level `IdentDistrib` facts

Each of the three triples extracted below feeds directly into
`IdentDistrib.condMutualInfo_eq`. The
`Fintype`/`MeasurableSingletonClass`/`IsProbabilityMeasure` side conditions are only
needed by the
downstream transport lemmas, so these triple facts live above the heavier instance
block. -/

section TripleIdentDistribs

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
  {μ : Measure Ω}
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'}
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}

/--
Triple-level `IdentDistrib ⟨Z, U, X⟩ ~ ⟨Z', U', X'⟩ μ ν` extracted from the first-copy
4-variable
`IdentDistrib`. The triple is packaged in the shape `IdentDistrib.condMutualInfo_eq`
consumes to
transport `I[Z:U|X]` under the first copy.
-/
private lemma copyLemma_triple_XFirst
    (hFirst : IdentDistrib
        (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
        (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    IdentDistrib (fun ω => (Z ω, U ω, X ω))
                 (fun ω' => (Z' ω', U' ω', X' ω')) μ ν :=
  hFirst.symm.comp measurable_projZUA

/--
Triple-level `IdentDistrib ⟨Z, U, Y⟩ ~ ⟨Z', U', Y₁⟩ μ ν` extracted from the second-copy
4-variable
`IdentDistrib`. Used by the Y_to_Y₁ delta transport for the `I[Z:U|Y]` term.
-/
private lemma copyLemma_triple_YSecond
    (hSecond : IdentDistrib
        (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
        (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    IdentDistrib (fun ω => (Z ω, U ω, Y ω))
                 (fun ω' => (Z' ω', U' ω', Y₁ ω')) μ ν :=
  hSecond.symm.comp measurable_projZUB

/--
Triple-level `IdentDistrib ⟨Z, U, X⟩ ~ ⟨Z', U', X₁⟩ μ ν` extracted from the second-copy
4-variable
`IdentDistrib`. Used by the symmetric X_to_X₁ delta transport.
-/
private lemma copyLemma_triple_XSecond
    (hSecond : IdentDistrib
        (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
        (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    IdentDistrib (fun ω => (Z ω, U ω, X ω))
                 (fun ω' => (Z' ω', U' ω', X₁ ω')) μ ν :=
  hSecond.symm.comp measurable_projZUA

end TripleIdentDistribs

/-! #### Finite-alphabet consequences

The lemmas below all require discrete/countable side conditions on the four codomains
plus an
`IsProbabilityMeasure` instance on the copy measure `ν`. -/

section Finite

variable {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}

/--
`I[X' : Y₁ | ⟨Z', U'⟩; ν] = 0`: the conditional-MI vanishing fact the abstract Lemma 2
Form A
consumes. Derived from the main `CondIndepFun` by projecting each measured pair to one
coordinate
(first-copy `X'`, second-copy `Y₁`).
-/
private lemma copyLemma_condMI_X_Y₁_vanishes
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    I[X' : Y₁ | fun ω' => (Z' ω', U' ω'); ν] = 0 :=
  (condMutualInfo_eq_zero hX' hY₁).mpr
    (ZhangYeung.condIndepFun_comp (φ := Prod.fst) (ψ := Prod.snd)
      measurable_fst measurable_snd hCond)

omit [Finite S₂] [MeasurableSingletonClass S₂] in
/--
`I[X' : X₁ | ⟨Z', U'⟩; ν] = 0`: the symmetric companion to
`copyLemma_condMI_X_Y₁_vanishes` used by
the `X ↔ X₁` variant of Lemma 2. Derived by projecting each measured pair to its first
coordinate.
-/
private lemma copyLemma_condMI_X_X₁_vanishes
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    I[X' : X₁ | fun ω' => (Z' ω', U' ω'); ν] = 0 :=
  (condMutualInfo_eq_zero hX' hX₁).mpr
    (ZhangYeung.condIndepFun_comp (φ := Prod.fst) (ψ := Prod.fst)
      measurable_fst measurable_fst hCond)

/-! ##### Lemma 2 Form B (specialized to the copy projections)

`delta_of_condMI_vanishes_eq` applied to the copy's `(X', Y₁, Z', U')` and `(X', X₁, Z',
U')`
projections, with the vanishing-CMI hypothesis supplied by the projected
conditional-independence
facts. -/

/-- **Lemma 2 Form B (primary)** [@zhangyeung1998, §III, eq. 45]. The delta identity of
Lemma 2
instantiated at the copy's `(X', Y₁, Z', U')` projections:

  `Δ(Z', U' | X', Y₁) = I[X' : Y₁] - I[X' : Y₁ | Z'] - I[X' : Y₁ | U'] - I[Z' : U' |
  ⟨X', Y₁⟩]`

under the copy measure `ν`. The vanishing-CMI hypothesis is derived from the main
`CondIndepFun` by
projecting each measured pair to one coordinate. -/
theorem _root_.ZhangYeung.copyLemma_delta_identity_Y₁
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z' U' X' Y₁ ν
      = I[X' : Y₁; ν] - I[X' : Y₁ | Z'; ν] - I[X' : Y₁ | U'; ν]
        - I[Z' : U' | ⟨X', Y₁⟩; ν] :=
  delta_of_condMI_vanishes_eq hX' hZ' hU' hY₁ ν
    (copyLemma_condMI_X_Y₁_vanishes (Y' := Y') hX' hY₁ hCond)

omit [Finite S₂] [MeasurableSingletonClass S₂] in
/-- **Lemma 2 Form B (symmetric)** [@zhangyeung1998, §III, eq. 45]. The delta identity
of Lemma 2
instantiated at the copy's `(X', X₁, Z', U')` projections, the `X ↔ X₁` swap of
`copyLemma_delta_identity_Y₁`:

  `Δ(Z', U' | X', X₁) = I[X' : X₁] - I[X' : X₁ | Z'] - I[X' : X₁ | U'] - I[Z' : U' |
  ⟨X', X₁⟩]`

under the copy measure `ν`. -/
theorem _root_.ZhangYeung.copyLemma_delta_identity_X_X₁
    (hX' : Measurable X') (hX₁ : Measurable X₁) (hZ' : Measurable Z') (hU' : Measurable U')
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z' U' X' X₁ ν
      = I[X' : X₁; ν] - I[X' : X₁ | Z'; ν] - I[X' : X₁ | U'; ν]
        - I[Z' : U' | ⟨X', X₁⟩; ν] :=
  delta_of_condMI_vanishes_eq hX' hZ' hU' hX₁ ν
    (copyLemma_condMI_X_X₁_vanishes (Y' := Y') (Y₁ := Y₁) hX' hX₁ hCond)

end Finite

/-! #### Delta transport and inequality corollaries

The lemmas in this section take both the original-law hypotheses (\`X, Y, Z, U\` on
\`(Ω, μ)\`) and
the copy-law outputs (\`X', Y', X₁, Y₁, Z', U'\` on \`(Ω', ν)\`) plus the structural
facts
\`hFirst, hSecond, hCond\`, and relate the \`Δ\` under \`μ\` to the \`Δ\` under \`ν\`.
-/

section Transport

variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}

/--
Bridge identity: `Δ(Z, U | X, Y) μ = Δ(Z', U' | X', Y₁) ν`. Each side of the delta
expands into
three mutual-information terms. `IdentDistrib.mutualInfo_eq` transports the
unconditional `I[Z :
U]`; `IdentDistrib.condMutualInfo_eq` transports the two conditional terms via the
triple-level
`IdentDistrib`s extracted from `hFirst` and `hSecond`.
-/
theorem _root_.ZhangYeung.copyLemma_delta_transport_Y_to_Y₁
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    delta Z U X Y μ = delta Z' U' X' Y₁ ν := by
  have hZU : IdentDistrib (fun ω => (Z ω, U ω)) (fun ω' => (Z' ω', U' ω')) μ ν :=
    hFirst.symm.comp measurable_pairZU
  rw [delta_def, delta_def, hZU.mutualInfo_eq,
      IdentDistrib.condMutualInfo_eq hZ hU hX hZ' hU' hX' (copyLemma_triple_XFirst hFirst),
      IdentDistrib.condMutualInfo_eq hZ hU hY hZ' hU' hY₁ (copyLemma_triple_YSecond hSecond)]

omit [Finite S₂] [MeasurableSingletonClass S₂] in
/--
Symmetric bridge identity: `Δ(Z, U | X, X) μ = Δ(Z', U' | X', X₁) ν`. Transports both
conditional-MI terms via `copyLemma_triple_XFirst` and `copyLemma_triple_XSecond`. The
μ-side has
`X` in both conditioner slots, so the two transports target the same pattern
syntactically; closing
by `linarith` over the two transport equalities sidesteps the ambiguity `rw` would
otherwise face.
-/
theorem _root_.ZhangYeung.copyLemma_delta_transport_X_to_X₁
    (hX : Measurable X) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    delta Z U X X μ = delta Z' U' X' X₁ ν := by
  have hZU : IdentDistrib (fun ω => (Z ω, U ω)) (fun ω' => (Z' ω', U' ω')) μ ν :=
    hFirst.symm.comp measurable_pairZU
  have e1 : I[Z : U; μ] = I[Z' : U'; ν] := hZU.mutualInfo_eq
  have e2 : I[Z : U | X; μ] = I[Z' : U' | X'; ν] :=
    IdentDistrib.condMutualInfo_eq hZ hU hX hZ' hU' hX' (copyLemma_triple_XFirst hFirst)
  have e3 : I[Z : U | X; μ] = I[Z' : U' | X₁; ν] :=
    IdentDistrib.condMutualInfo_eq hZ hU hX hZ' hU' hX₁ (copyLemma_triple_XSecond hSecond)
  rw [delta_def, delta_def]
  linarith [e1, e2, e3]

/-- **Primary inequality form of Lemma 2** [@zhangyeung1998, §III, eq. 45]. Combining
the Y-to-Y₁
delta transport with Form B and the nonnegativity of the three subtracted conditional
mutual
informations on the right of eq. (45) gives

  `Δ(Z, U | X, Y) μ ≤ I[X' : Y₁; ν]`,

the first of the two inequalities Theorem 3's proof opens with on paper line 683. -/
theorem _root_.ZhangYeung.copyLemma_delta_le_mutualInfo_Y₁
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z U X Y μ ≤ I[X' : Y₁; ν] := by
  rw [copyLemma_delta_transport_Y_to_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond,
      copyLemma_delta_identity_Y₁ hX' hY₁ hZ' hU' hCond]
  have h1 : 0 ≤ I[X' : Y₁ | Z'; ν] := condMutualInfo_nonneg hX' hY₁
  have h2 : 0 ≤ I[X' : Y₁ | U'; ν] := condMutualInfo_nonneg hX' hY₁
  have h3 : 0 ≤ I[Z' : U' | ⟨X', Y₁⟩; ν] := condMutualInfo_nonneg hZ' hU'
  linarith

omit [Finite S₂] [MeasurableSingletonClass S₂] in
/-- **Symmetric inequality form of Lemma 2** [@zhangyeung1998, §III, eq. 45]. The `X ↔
X₁` variant,

  `I[Z : U; μ] - 2·I[Z : U | X; μ] ≤ I[X' : X₁; ν]`,

the second of the two inequalities Theorem 3's proof opens with on paper line 689. -/
theorem _root_.ZhangYeung.copyLemma_delta_le_mutualInfo_X_X₁
    (hX : Measurable X) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    I[Z : U; μ] - 2 * I[Z : U | X; μ] ≤ I[X' : X₁; ν] := by
  rw [← delta_self Z U X μ,
      copyLemma_delta_transport_X_to_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond,
      copyLemma_delta_identity_X_X₁ hX' hX₁ hZ' hU' hCond]
  have h1 : 0 ≤ I[X' : X₁ | Z'; ν] := condMutualInfo_nonneg hX' hX₁
  have h2 : 0 ≤ I[X' : X₁ | U'; ν] := condMutualInfo_nonneg hX' hX₁
  have h3 : 0 ≤ I[Z' : U' | ⟨X', X₁⟩; ν] := condMutualInfo_nonneg hZ' hU'
  linarith

end Transport

end Consequences

end ZhangYeung
