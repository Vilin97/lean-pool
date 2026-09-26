/-
Copyright (c) 2026 Hyeon Seung-Hyeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hyeon Seung-Hyeon
-/

-- Adapted for Lean Pool from 0stellensatz/MassFormula at 7fa41a621f724f110183904d3fd19c6730a932ad.
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Discriminant
public import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# 1. Statement of the result (p.1031): definitions

This file holds the shared definitions of the project—the local-field setting, the residue
cardinality `q`, the ring of integers `integers L` of a subextension, total ramifiedness, the set
`sigma K n`, the discriminant valuation `d`, the wild exponent `c`, the automorphism count `w`, and
the representative-set predicate standing in for the paper's set of representatives. The
main statements are proved in the remaining project modules. Only unfolding lemmas and
short well-formedness facts are proved here.

## Implementation notes

- The local field `K` is Mathlib's `IsNonarchimedeanLocalField K` over a `ValuativeRel` and a
  complete `UniformSpace`; Mathlib's instances then make `𝒪[K]` a complete DVR with finite residue
  field `𝓀[K]`, which is exactly the paper's standing hypothesis, covering mixed and equal
  characteristic alike.
- The residue cardinality is `q K = Nat.card 𝓀[K]`, and the residue characteristic `p` is written
  inline as `ringChar 𝓀[K]`.
- The separable closure is `SeparableClosure K`, and a subextension `L` of `SeparableClosure K` /
  `K` is a term of `IntermediateField K (SeparableClosure K)`.
- The ring of integers of `L` is `integers L`, the integral closure of `𝒪[K]` in `L`; its maximal
  ideal is modeled instance-freely as `maximalIdealAbove L`, the radical of `𝓂[K]` extended to
  `integers L`, and *totally ramified* means `ramificationIdx L = Module.finrank K ↥L`.
- All of this is junk-tolerant: for `L` infinite over `K` (or `n = 0`) the values are junk, and
  membership in `sigma K n` with `0 < n` is what keeps statements honest.
- `d L` is the multiplicity of `𝓂[K]` in the hand-rolled discriminant ideal `discIdeal L` (the span
  of the discriminants of the integral `K`-bases of `L`, following
  [Serre 1979, Chap. III, §3][Serre1979]), avoiding the freeness and Dedekind-domain instances that
  Mathlib's `differentIdeal` route would demand inside a total definition.
- `c L = d L - n + 1` is defined with truncated `ℕ`-subtraction as `d L + 1 - n`; the paper's claim
  that `c L` is a nonnegative integer becomes the goal `sub_one_le_d`.
- Theorems 1 and 2 are stated in `ℝ≥0∞`, where the possibly infinite `∑'` needs no convergence side
  condition and equality with the finite value `n` (resp. `1`) already encodes convergence; the
  convergence claim of Remark 1° is restated separately over `ℝ` as `Summable`.
- The paper's set of representatives is not built as a quotient: Theorem 2 instead quantifies over
  every `R` satisfying `IsRepresentativeSet n R`—the paper's "set of representatives of the
  isomorphism classes" verbatim—which avoids `Quotient.lift` well-definedness obligations for `c`
  and `w`.

## References

* [Serre1978] J-P. Serre, *Une «formule de masse» pour les extensions totalement ramifiées de
  degré donné d'un corps local*, C. R. Acad. Sci. Paris **286** (1978), Série A, 1031–1036.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer, 1979.
-/

public section

open ValuativeRel

namespace MassFormula

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K]

/-- `q K` is the cardinality of the finite residue field `𝓀[K]` of `K`, that is `Nat.card 𝓀[K]`
([Serre 1978, p.1031][Serre1978]). -/
noncomputable def q : ℕ :=
  Nat.card 𝓀[K]

omit [IsUniformAddGroup K] in
/-- The residue field is a finite *field*, so `1 < q K`. -/
lemma one_lt_q : 1 < q K :=
  Finite.one_lt_card

variable {K}

/-- The ring of integers of a subextension `L` of `SeparableClosure K` / `K`: the integral closure
of `𝒪[K]` in `L` ([Serre 1978, §3, p.1032][Serre1978]). (Introduced by the paper only in Section 3,
but needed already here to say what *totally ramified* means.) -/
noncomputable def integers (L : IntermediateField K (SeparableClosure K)) :
    Subalgebra ↥𝒪[K] ↥L :=
  integralClosure ↥𝒪[K] ↥L

/-- The maximal ideal of `integers L`, modeled instance-freely as the radical of the ideal `𝓂[K]`
extended along `algebraMap 𝒪[K] (integers L)`. For `L` / `K` finite this is the unique maximal ideal
of the local ring `integers L`, but the definition itself carries no such obligations, and is junk
for `L` infinite over `K`. -/
@[expose] noncomputable def maximalIdealAbove (L : IntermediateField K (SeparableClosure K)) :
    Ideal (integers L) :=
  (Ideal.map (algebraMap 𝒪[K] (integers L)) 𝓂[K]).radical

/-- The ramification index of `L` / `K`: the exponent of `maximalIdealAbove L` in the extension of
`𝓂[K]` to `integers L`, via Mathlib's junk-tolerant `Ideal.ramificationIdx'`. -/
@[expose] noncomputable def ramificationIdx (L : IntermediateField K (SeparableClosure K)) : ℕ :=
  Ideal.ramificationIdx' 𝓂[K] (maximalIdealAbove L)

/-- `L` / `K` is *totally ramified* when its ramification index equals its degree
`Module.finrank K ↥L` ([Serre 1978, p.1031][Serre1978]). -/
def IsTotallyRamified (L : IntermediateField K (SeparableClosure K)) : Prop :=
  ramificationIdx L = Module.finrank K ↥L

variable (K)

/-- The set of subextensions `L` of `SeparableClosure K` that are totally ramified over `K` and
satisfy `Module.finrank K ↥L = n` ([Serre 1978, p.1031][Serre1978]). For `n = 0` the set is junk
(the paper takes `1 ≤ n`), which is why every main theorem assumes `0 < n`. -/
def sigma (n : ℕ) : Set (IntermediateField K (SeparableClosure K)) :=
  {L | Module.finrank K ↥L = n ∧ IsTotallyRamified L}

variable {K}

omit [IsUniformAddGroup K] in
lemma mem_sigma {n : ℕ} {L : IntermediateField K (SeparableClosure K)} :
    L ∈ sigma K n ↔ Module.finrank K ↥L = n ∧ IsTotallyRamified L :=
  Iff.rfl

/-- The discriminant ideal of a subextension: the ideal of `𝒪[K]` generated by the elements whose
image in `K` is `Algebra.discr K b` for some `K`-basis `b` of `L` with all entries integral over
`𝒪[K]` (cf. [Serre 1979, Chap. III, §3][Serre1979]). When `L` / `K` is finite separable this is the
classical discriminant ideal generated by the discriminants of the `𝒪[K]`-bases of `integers L`: an
integral `K`-basis spans a sublattice of finite index in `integers L`, and the discriminant of that
sublattice is the square of the index times the discriminant of `integers L`. The present form needs
no freeness or Dedekind-domain instances. For `L` infinite over `K` no such basis exists and the
ideal is `⊥`—junk, as usual. -/
noncomputable def discIdeal (L : IntermediateField K (SeparableClosure K)) : Ideal ↥𝒪[K] :=
  Ideal.span {x : ↥𝒪[K] | ∃ b : Module.Basis (Fin (Module.finrank K ↥L)) K ↥L,
    (∀ i, IsIntegral 𝒪[K] (b i)) ∧ algebraMap 𝒪[K] K x = Algebra.discr K ⇑b}

/-- The valuation of the discriminant of `L` over `K`: the multiplicity of the maximal ideal `𝓂[K]`
in `discIdeal L`, in the monoid of ideals of `𝒪[K]` ([Serre 1978, p.1031][Serre1978]). -/
noncomputable def d (L : IntermediateField K (SeparableClosure K)) : ℕ :=
  multiplicity 𝓂[K] (discIdeal L)

/-- `c L` is `d L - n + 1`, where `n` is the degree `Module.finrank K ↥L`, written in the
truncation-safe form `d L + 1 - n` ([Serre 1978, p.1031][Serre1978]). The bound `n - 1 ≤ d L` making
the truncated subtraction faithful is the paper's own claim that `c L` is a nonnegative integer, the
theorem `sub_one_le_d`. -/
@[expose] noncomputable def c (L : IntermediateField K (SeparableClosure K)) : ℕ :=
  d L + 1 - Module.finrank K ↥L

/-- The number of `K`-automorphisms of `L` ([Serre 1978, Remark 3°, p.1031][Serre1978]). -/
noncomputable def w (L : IntermediateField K (SeparableClosure K)) : ℕ :=
  Nat.card (↥L ≃ₐ[K] ↥L)

/-- The paper's set of representatives, as a predicate rather than a quotient: `R` is a *set of
representatives of the isomorphism classes of the elements of* `sigma K n`—it consists of elements
of `sigma K n`, and every element of `sigma K n` is `K`-isomorphic to exactly one member of `R`
([Serre 1978, Remark 3°, p.1031][Serre1978]). -/
def IsRepresentativeSet (n : ℕ) (R : Set (IntermediateField K (SeparableClosure K))) : Prop :=
  R ⊆ sigma K n ∧ ∀ L ∈ sigma K n, ∃! M, M ∈ R ∧ Nonempty (↥L ≃ₐ[K] ↥M)

end MassFormula
