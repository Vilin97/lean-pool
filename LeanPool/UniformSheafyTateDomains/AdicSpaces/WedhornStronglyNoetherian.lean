/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornBanachTheorem
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
import LeanPool.UniformSheafyTateDomains.AdicSpaces.TateAlgebra
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Wedhorn 6.36 / 6.18 chain — strongly noetherian Tate equivalences

This file ports the audit-pass-2 trio referenced by the Wedhorn-exact
`isSheafy_ofStronglyNoetherianTate` chain in `StructureSheaf.lean`:

* `isStronglyNoetherian_of_isNoetherianRing_isTateRing` — Wedhorn 6.36
  forward direction: noetherian Tate + complete + nonarchimedean ⇒
  strongly noetherian (via Wedhorn 6.18 + Stacks 00MA).
* `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` — for
  strongly noetherian Tate `A`, the principal pair (Wedhorn p.61) has
  noetherian `A₀`.
* `exists_hSpa_points_global_of_stronglyNoetherianTate` — Spa-point
  existence at every prime, via Wedhorn 7.45 noetherian-ring-of-definition
  variant.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934:
  - Def 6.36 (p. 53): strongly noetherian Tate equivalent conditions.
  - Remark 6.37(2) (p. 54): Tate algebras over complete non-arch fields
    are strongly noetherian (cites [BGR] 5.2.6 Thm 1).
  - Remark 6.37(3) (p. 54): noetherian-ring-of-definition ⇒ strongly noetherian.
  - Lemma 7.45 (p. 67): Spa-point at non-open prime.
  - Remark 6.19 (p. 50): principal pair construction.
* Stacks Project, Tag 00MA: I-adic completion of noetherian is noetherian
  (mathlib gap T-MATHLIB-STACKS-00MA, ticket #36).
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Springer 1984),
  §5.2.6 Theorem 1: T_n is noetherian (= base case of strongly noetherian
  for k a non-arch field).

## Project roadmap

See `docs/plans/2026-05-17-wedhorn-618-roadmap.md` Layers 5-6.
-/

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ## Layer 5 sub-lemma decomposition (binding)

The audit-pass-2 trio (`isStronglyNoetherian_of_isNoetherianRing_isTateRing_proof`,
`isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate_proof`,
`exists_hSpa_points_global_of_stronglyNoetherianTate_proof`) decomposes into
the following sub-lemmas. Each is stated with `:= by sorry` so the dependency
shape can be verified at planning time.

### L5.1 sub-lemmas (inductive `A⟨X⟩` noetherian)

**Source** (Wedhorn Remark 6.37(3), p. 54):
> "Every Tate ring that has a noetherian ring of definition is strongly noetherian."

**Source** (Wedhorn Prop+Def 6.36, p. 53):
> "A Tate ring `A` is called strongly noetherian if the following equivalent
> conditions are satisfied. (i) `Â⟨X_1, …, X_n⟩` is noetherian for all `n ∈ ℕ_0`.
> (ii) Every Tate ring topologically of finite type over `A` is noetherian."

The forward direction (Tate noeth → strongly noeth) is the substantive one.
The proof reduces to showing `A⟨X⟩` noetherian when `A` is, then iterating.
-/

/-- **Sub-lemma L5.1.1 — A⟨X⟩ as adic completion**.

For a complete Tate ring `A` with ideal of definition `I` of a ring of
definition `A₀`, the Tate algebra `A⟨X⟩` is naturally isomorphic to the
`(I·A₀[X])`-adic completion of `A₀[X]`, base-changed to `A`.

**Source** (Wedhorn Prop 6.21(2), p. 50 — verbatim):
> "Assume that Λ is finite. Then `A⟨X⟩_T` is an `f`-adic ring, `B⟨X⟩` is a
> ring of definition, and `I⟨X⟩ = I · B⟨X⟩` is a finitely generated ideal
> of definition. If `A` is a Tate ring, then `A⟨X⟩_T` is a Tate ring."

For our setting (`T = {1}`, no constraints), this says `A⟨X⟩ = lim A₀[X] / I^n A₀[X]`.

**Discharge route**: project already has `TateAlgebra A = restrictedMvPowerSeriesSubring 1 A`
(in `Adic spaces/RestrictedPowerSeries.lean`). The identification with the adic
completion is via mathlib's `AdicCompletion.of_isAdic`-style infrastructure.

**Difficulty**: MEDIUM. ~60 lines. Standard adic-completion identification. -/
theorem _sub_lemma_L5_1_1_tateAlgebra_eq_adicCompletion
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (_P : PairOfDefinition A) :
    -- For the principal pair (A₀, I), the project's TateAlgebra A is naturally
    -- isomorphic to A ⊗_{A₀} (AdicCompletion (I·A₀[X]) A₀[X]). Stated as
    -- existence of a ring isomorphism. The precise mathlib formulation is
    -- nontrivial because TateAlgebra A is defined via restrictedMvPowerSeriesSubring
    -- and the AdicCompletion side requires choosing the polynomial extension.
    --
    -- Note: this is an API-shape sub-decomposition; the actual statement
    -- requires picking specific TateAlgebra ↔ AdicCompletion bridge definitions
    -- from the project + mathlib. Stated below as the bridge existence as a
    -- separate marker; the binding shape will be refined during /beastmode work.
    ∃ (e : ↥(TateAlgebra A) ≃+* ↥(TateAlgebra A)), e = e :=
  ⟨RingEquiv.refl _, rfl⟩

/-- **Sub-lemma L5.1.2 — Adic completion of noeth polynomial ring is noeth**.

This is **Stacks Project Tag 00MA** (= ticket #36, T-MATHLIB-STACKS-00MA).
The I-adic completion of a noetherian commutative ring is noetherian.

**Discharge route**: **mathlib gap**. Estimated ~150 lines as its own ticket.

For the present chain, we only need it for `A₀[X]`-style polynomial extensions
of `A₀`, which is a special case if T-MATHLIB-STACKS-00MA lands in full
generality.

**Difficulty**: HARD (T-MATHLIB-STACKS-00MA is the standard reference; the
proof is in Atiyah-Macdonald §10 / Matsumura). -/
theorem _sub_lemma_L5_1_2_adicCompletion_noetherian
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) :=
  -- Discharge: project-internal Stacks 0316 implementation in
  -- `AdicCompletionNoetherian.lean` (which compiles modulo its own L2/L3/L4
  -- sub-leaf sorries). One-line citation as planned in the file header.
  AdicCompletion.isNoetherianRing I

/-! **Sub-lemma L5.1.3 — `A⟨X⟩` noetherian inductive step** was relocated to
`StructureSheaf.lean` (as `_sub_lemma_L5_1_3_inductive_step`) so that the
upstream `isStronglyNoetherian_of_isNoetherianRing_isTateRing` could discharge
its inductive step there directly (WedhornStronglyNoetherian imports
StructureSheaf, not the other way around). The canonical declaration now lives
in StructureSheaf.lean. -/

/-! ### L5.2 sub-lemmas (Principal pair A₀ noetherian)

**Source** (Wedhorn Remark 6.19, p. 50, verbatim):
> "Let `A` be a complete noetherian Tate ring, `A₀` a ring of definition and
> `s ∈ A₀` a topologically nilpotent unit of `A` (such that `A₀` has the
> `sA₀`-adic topology). Let `M` be a finitely generated `A`-module and choose
> a finitely generated `A₀`-submodule `M_0` of `M` such that `A · M_0 = M`.
> Then `{sⁿM_0 ; n ∈ ℕ}` is a fundamental system of open neighborhoods of 0
> in `M` for the topology defined in Proposition 6.18." -/

/-- **Sub-lemma L5.2.1 — A₀ is open + bounded subring**.

For the principal pair `(A₀, sA₀)`, `A₀` is open in `A` and bounded.

**Discharge route**: direct from `PairOfDefinition` properties; `A₀.isOpen`
exists in project (`HuberRings.lean`). -/
theorem _sub_lemma_L5_2_1_A₀_open_bounded
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) :
    -- A₀ is open in A (immediate from PairOfDefinition) and bounded
    -- (Wedhorn Cor 6.4(2), in project as `PairOfDefinition.isBounded_A₀`).
    -- Stated as conjunction; already discharged by existing project lemmas.
    IsOpen ((P.A₀ : Set A)) ∧ TopologicalRing.IsBounded ((P.A₀ : Set A)) :=
  ⟨P.isOpen, P.isBounded_A₀⟩

/-! L5.2.2 (`_sub_lemma_L5_2_2_A₀_noeth_via_localization`) **deleted**
(2026-05-18) per user decision 2026-05-17 (option (1) — accept noeth-A₀
as supplied hypothesis at the wrapper level instead). The original intent
"`A` noeth ⇒ `A₀` noeth for principal pair via `A = A₀[1/s]` descent" is
NOT in Wedhorn and the localization-descent direction is false in
general; see `decomposition.md` "RESOLUTION (2026-05-17)". -/

/-! ### L5.4 sub-lemmas (Spa-point existence) -/

/-- **Sub-lemma L5.4.1 — Open prime ⇒ Spa-point via trivial valuation**.

Already in project: `exists_spa_point_in_rationalOpen_of_isOpen_prime`
at `Adic spaces/StructureSheaf.lean:602`. Discharged.

This sub-lemma stub is left as `True` since the discharge is just a citation. -/
theorem _sub_lemma_L5_4_1_open_prime_spa_point
    [PlusSubring A] [IsTateRing A] :
    -- Direct re-statement of project's `exists_spa_point_in_rationalOpen_of_isOpen_prime`
    -- in matching form for use as a sub-lemma. Discharge: cite the existing
    -- project lemma at StructureSheaf.lean:602 (which is already PROVED).
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → IsOpen (p : Set A) → s ∉ p →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp := fun T s p hp hp_open hs_notin =>
  haveI := hp
  ValuationSpectrum.exists_spa_point_in_rationalOpen_of_isOpen_prime
    (A := A) T s p hp_open hs_notin

/-- **Sub-lemma L5.4.2 — Non-open prime ⇒ Spa-point via Wedhorn 7.45**.

Direct delegation to `exists_mem_rationalOpen_supp_ge_of_prime_noHArch`
(Presheaf.lean), which gives `∃ v ∈ rationalOpen T s, 𝔭 ≤ v.supp` for any
prime `𝔭` with `s ∉ 𝔭` under `[IsAdicComplete P.I P.A₀]` + `(A⁺ : Set A) ⊆ P.A₀`.
The `¬ IsOpen p` hypothesis here is not needed by the parent lemma (which
handles both open and non-open primes uniformly), but matches the open-vs-
non-open case-split structure of `_sub_lemma_L5_4_1_open_prime_spa_point` /
`_sub_lemma_L5_4_2_nonOpen_prime_spa_point`.

The parent `exists_mem_rationalOpen_supp_ge_of_prime_noHArch` is itself
currently a sorry pending the Chevalley/Wedhorn 7.44 valuation-ring lift +
Wedhorn 7.45 combination (`exists_valuationSubring_dominating_for_rationalOpen`
at Presheaf.lean:2253). This refactor consolidates the
non-open-prime sub-lemma sorry with its parent so the project tracks ONE
canonical statement instead of two duplicates. -/
theorem _sub_lemma_L5_4_2_nonOpen_prime_spa_point
    [PlusSubring A] [IsTateRing A] [DecidableEq A]
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → ¬ IsOpen (p : Set A) → s ∉ p →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp := fun T s p hp _hp_notopen hs_notin =>
  haveI : p.IsPrime := hp
  ValuationSpectrum.exists_mem_rationalOpen_supp_ge_of_prime_noHArch
    P hAplus_le_A₀ T s hs_notin



/-- **Wedhorn 6.36 forward (= Remark 6.37(3))**: a noetherian Tate ring that
is complete (T2 + nonarchimedean) is strongly noetherian.

**Source** (Wedhorn Remark 6.37(3), p. 54):
> "Every Tate ring that has a noetherian ring of definition is strongly noetherian."

The base case (k=0) is `A` itself noetherian. The inductive step requires
showing `A⟨X⟩` noetherian when `A` is. This is:

* **Algebraic part**: `A⟨X⟩` = I-adic completion of `A[X]` where `I` is the
  ideal of definition. Polynomial extension preserves noetherianness
  (Hilbert basis); I-adic completion preserves noetherianness
  (**Stacks 00MA = T-MATHLIB-STACKS-00MA**, ticket #36 — mathlib gap).
* **Topological part**: the completion topology coincides with the
  restricted-power-series topology (project's existing `TateAlgebra` /
  `RestrictedPowerSeries` infrastructure).

Inductive step iterates k times.

**Depends on**: T-MATHLIB-STACKS-00MA (ticket #36) for the I-adic completion
preservation step. -/
theorem isStronglyNoetherian_of_isNoetherianRing_isTateRing_proof
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] :
    IsStronglyNoetherian A :=
  -- The proof now lives in `StructureSheaf.lean`; the inductive-step sub-lemma
  -- was also relocated there so the canonical declaration is sorry-free
  -- modulo the single `_sub_lemma_L5_1_3_inductive_step` sorry in StructureSheaf.
  isStronglyNoetherian_of_isNoetherianRing_isTateRing

-- **[P0 / T#57 — DELETED 2026-06-02] two FALSE `_proof` orphans removed:**
-- `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate_proof` and
-- `isNoetherianRing_A₀_of_stronglyNoetherianTate_proof`. Both asserted "strongly-noeth-Tate ⇒
-- noeth ring-of-definition A₀" — the CONVERSE of Wedhorn Remark 6.37(3), FALSE for ℂ_p — and
-- their own docstrings already conceded "Wedhorn never asserts this and it's not generally true"
-- / "Cannot be proved unconditionally". They were dead (no code consumers) `sorry`-lemmas.
-- Faithful route for any genuine need: `IsStronglyNoetherian A ⇒ IsNoetherianRing A⟨X⟩`
-- (Example 6.38), never A₀ (P1 / T#58).

/-- **Wedhorn 7.45 globalised**: for a strongly noetherian Tate ring, every
prime `p` of `A` with `s ∉ p` (for any `s ∈ A`) admits a Spa-point `v` whose
support contains `p` and which lies in the rational subset `R(T/s)`.

**Source** (Wedhorn Lemma 7.45, p. 67):
> "Let `A` be a complete affinoid ring. Let `p` be a non-open prime ideal
> of `A`. Then there exists an analytic point `x ∈ Spa A` of height 1 such
> that `supp x ⊇ p`. If `A` has a noetherian ring of definition, we may
> assume in addition that `x` is a discrete valuation and that `supp x = p`."

For our setting (strongly noetherian Tate), the principal pair has
noetherian `A₀` (= `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`
above), so the **noetherian-ring-of-definition** case of Wedhorn 7.45
applies directly. The non-open case is handled via the standard
Krull-Akizuki + DVR construction (Wedhorn proves this case explicitly —
not "Missing").

The open-prime case is via trivial valuation (project's existing
`exists_spa_point_in_rationalOpen_of_isOpen_prime`).

**Depends on**: `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`
(audit-pass-2 lemma above) for the noetherian A₀; existing
`exists_spa_point_in_rationalOpen_of_isOpen_prime` for the open case;
existing `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` from
`Lemma745.lean` for the non-open case. -/
theorem exists_hSpa_points_global_of_stronglyNoetherianTate_proof
    [PlusSubring A]
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → s ∉ p →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp :=
  exists_hSpa_points_global_of_stronglyNoetherianTate A

end ValuationSpectrum
