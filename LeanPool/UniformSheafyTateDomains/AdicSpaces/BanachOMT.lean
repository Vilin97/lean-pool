/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Banach's open mapping theorem for complete metric topological abelian groups

This file contains the **Bourbaki [TG] Ch. III §3 no. 3 Théorème 1** version of
Banach's open mapping theorem, specialised to topological abelian groups. The
classical statement is:

> Let G, H be Hausdorff topological abelian groups whose topologies are defined by
> countable fundamental systems of neighbourhoods of 0. Assume G is complete. Let
> f : G →+ H be a continuous group homomorphism. If f is surjective and H is
> complete, then f is open.

This is the version cited by **Huber** in "*A generalization of formal schemes and
rigid analytic varieties*", Math. Z. 217 (1994), Lemma 2.4(i) (p. 16):

> "In order to prove (i) one can take over without any change the proof of Banach's
> open mapping theorem (cf. **[B1, 1.3.3]**)."

and used implicitly by **BGR §3.7** as a prerequisite (per BGR Introduction p. 5:
"besides the **Open Mapping Theorem for BANACH spaces**, only some basic facts
from commutative algebra are assumed"). It is the substantive analytical input
underlying:

* **Wedhorn 6.16** (Banach's theorem for Tate rings — "Proof. Missing")
* **Wedhorn 6.17** (noetherian ⇔ every ideal closed)
* **Wedhorn 6.18** (unique fg-module topology + continuous + open maps)

The proof structure is the classical Banach argument adapted to the group setting:

1. The source `G` is a Baire space (mathlib instance
   `BaireSpace.of_pseudoEMetricSpace_completeSpace` for complete uniform spaces
   with countably-generated uniformity).
2. For any neighbourhood `U` of 0 in `G`, the image `f(n·U) = n·f(U)` covers `H`
   by countable union (use any countable fundamental system).
3. `H` is Baire ⇒ some `n·f(U)` has nonempty interior ⇒ `f(U) − f(U)` contains a
   neighbourhood of 0 in `H`.
4. Cauchy completeness of `G` lifts the "approximate preimage" to an exact preimage:
   for any element of a small neighbourhood `V` in `H`, build a Cauchy sequence in
   `G` whose image converges to that element; the limit in `G` (using completeness)
   maps into the desired neighbourhood of `f(0) = 0`.
5. Translation-invariance gives openness at every point.

## References

* N. Bourbaki, *Topologie Générale*, Chapter III §3 no. 3 Théorème 1 (the
  group-level Banach open mapping theorem).
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*,
  Math. Z. 217 (1994), Lemma 2.4 (p. 16).
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Springer 1984),
  §3.7 (Banach algebras) — uses Banach OMT as prerequisite.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934, §6.3 Theorem 6.16 (refers out).

## Project status

This file states the theorem and immediate corollaries. The proof is left as
`sorry` — to be discharged as the Layer-1 mathlib gap from the roadmap at
`docs/plans/2026-05-17-wedhorn-618-roadmap.md`.

Once proved, the result is suitable for upstreaming to Mathlib as
`Mathlib.Topology.Algebra.Group.OpenMappingCompleteMetric`.
-/

open scoped Pointwise

namespace AddMonoidHom

universe u v

/-! ## Sub-lemmas (kept for documentation / reference)

The Banach OMT main theorem now delegates to mathlib's
`AddMonoidHom.isOpenMap_of_sigmaCompact`
(`Mathlib.Topology.Algebra.Group.OpenMapping`) under an added
`[SigmaCompactSpace G]` hypothesis (per BINDING-RULE (b) — see commit
`3a7ce47` and the docstring on `isOpenMap_of_completeSpace_of_countablyGenerated`
below).

The remaining sub-lemmas (`_sub_sub_lemma_A_1_split_symmetric`,
`_sub_sub_lemma_A_2_interior_add`, `_sub_sub_lemma_C_2_baire_nonempty_interior`,
`_sub_sub_lemma_D_1_cauchy_builder`, `_sub_sub_lemma_D_2_limit_in_nbhd`,
`_sub_lemma_translation`) are independently useful pieces of topological-group
infrastructure and are retained sorry-free. The obsolete BGR-route sub-lemmas
B / C / D / C.1 were removed in commit `ddeb5dc` as dead code (and B / C.1 were
B2 false, per `b2_log.jsonl` entry 3).
-/

/-- **Sub-lemma A — Symmetric-set absorbs** (the "subtract trick").

If `K` is a closed set in a topological additive group `H` such that some
integer multiple `n · K` has nonempty interior, then `K - K` contains a
neighborhood of 0.

This is the standard symmetric-set argument: if `y ∈ interior(n·K)`, then
`y - y = 0 ∈ interior(n·K - n·K) = n·interior(K - K)`, so `interior(K - K)`
is nonempty (and contains 0 by symmetry/translation).

**Mathlib search**: no direct lemma found; needs to be stated. Closest
pattern: `Symmetric` mathlib lemmas in `Topology.Algebra.Group.Pointwise`
but none directly give "closure has interior ⇒ difference contains nbhd of 0".

**Estimated**: ~40 lines.

**Sources**: BGR §3.7.2 proof of Prop 1 + standard Banach OMT proof. -/
theorem _sub_lemma_symmetric_absorbs
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (K : Set H) (_hK_closed : IsClosed K) (_hK_sym : K = (fun x => -x) '' K)
    (h_int : (interior K).Nonempty) :
    (Set.image2 (· - ·) K K) ∈ nhds (0 : H) := by
  -- V - V (with V = interior K) is open, contains 0, and lies inside K - K.
  obtain ⟨x, hx⟩ := h_int
  exact mem_nhds_iff.mpr ⟨interior K - interior K,
    Set.image2_subset interior_subset interior_subset, isOpen_interior.sub_left,
    ⟨x, hx, x, hx, sub_self x⟩⟩

/-! ## Obsolete BGR-route sub-lemmas removed (2026-05-18)

Sub-lemmas **B (`_sub_lemma_countable_cover`)**, **C (`_sub_lemma_approx_preimage`)**,
**D (`_sub_lemma_cauchy_lift`)**, and **C.1 (`_sub_sub_lemma_C_1_countable_closed_cover`,
removed below)** have been **deleted**. These four sub-lemmas were part of the original
BGR-following manual reconstruction of the topological-group Banach OMT, but as
recorded in `b2_log.jsonl` entries 3-4 each was either FALSE as stated (B, C.1
fail without `[SigmaCompactSpace G]` / `[SeparableSpace G]`) or unused after the
main theorem switched to delegating to mathlib's
`AddMonoidHom.isOpenMap_of_sigmaCompact` (commit `3a7ce47`). Removing them
eliminates four dead-code sorries from this file.

`_sub_lemma_translation` (sub-lemma E) is retained — it is still useful as the
"open at 0 → open everywhere" reduction (sorry-free).
-/

/-- **Sub-lemma E — Translation invariance** (the easy step).

If `f : G →+ H` is open at 0 (image of every nbhd of 0 contains a nbhd of 0),
then `f` is open everywhere (image of every open set is open).

**Mathlib search**: standard topological-group fact. Likely follows immediately
from `Homeomorph.add_right` or similar via `isOpenMap_iff_nhds_le`.

**Estimated**: ~10 lines (one-liner if the right lemma exists). -/
theorem _sub_lemma_translation
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (f : G →+ H)
    (hf_zero : ∀ U ∈ nhds (0 : G), f '' U ∈ nhds (0 : H)) :
    IsOpenMap f := by
  intro U hU_open
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx_mem, rfl⟩
  -- Strategy: f '' U ∈ nhds (f x) iff (Homeomorph.subRight (f x)) preimage maps it
  -- to a nhds 0 set. Show that preimage contains f '' (U preimaged by `(· + x)`),
  -- which is a nhds 0 by hf_zero.
  -- Step 1: V := {z : G | z + x ∈ U} is open nhds 0 in G.
  set V : Set G := (fun z => z + x) ⁻¹' U with hV_def
  have hV_open : IsOpen V := hU_open.preimage (continuous_add_const x)
  have h0V : (0 : G) ∈ V := by simp [hV_def, hx_mem]
  have hV_nhds : V ∈ nhds (0 : G) := hV_open.mem_nhds h0V
  -- Step 2: f '' V ∈ nhds 0 in H.
  have hfV_nhds : f '' V ∈ nhds (0 : H) := hf_zero V hV_nhds
  -- Step 3: f '' V ⊆ (fun w => w + f x) ⁻¹' (f '' U).
  -- because f(z) + f x = f(z + x) ∈ f '' U whenever z + x ∈ U.
  have hsub : f '' V ⊆ (fun w => w + f x) ⁻¹' (f '' U) := by
    rintro w ⟨z, hzV, rfl⟩
    have : z + x ∈ U := by simpa [hV_def] using hzV
    exact ⟨z + x, this, by rw [f.map_add]⟩
  -- Step 4: `(· + f x) ⁻¹' (f '' U) ∈ nhds 0`; translate along `(· + f x)`
  -- (`map_add_right_nhds_zero`) to get `f '' U ∈ nhds (f x)`.
  have hpre_nhds : (fun w => w + f x) ⁻¹' (f '' U) ∈ nhds (0 : H) :=
    Filter.mem_of_superset hfV_nhds hsub
  exact map_add_right_nhds_zero (f x) ▸ hpre_nhds

/-! ## Sub-sub-lemma decomposition for Sub-lemmas A, C, D (pass-(ii) refinement)

After pass-(ii) mathlib search verified that `exists_closed_nhds_one_inv_eq_mul_subset`
(`Topology.Algebra.Group.Pointwise:304`) exists, the Banach iteration steps become
clean compositions. The sub-sub-lemmas below break A, C, D into pieces small enough
that each is ≤ 30 lines.
-/

/-- **Sub-sub-lemma A.1 — symmetric shrinking nbhd basis exists**.

For any nbhd `U` of 0 in a topological add group, there's a smaller closed symmetric
nbhd `V` of 0 with `V + V ⊆ U`.

**Mathlib discharge** (verified): direct from `exists_closed_nhds_zero_neg_eq_add_subset`
(auto-generated additive version of `exists_closed_nhds_one_inv_eq_mul_subset` at
`Topology.Algebra.Group.Pointwise:304`). One-liner body.

**Difficulty**: TRIVIAL. ~5 lines. -/
theorem _sub_sub_lemma_A_1_split_symmetric
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (U : Set H) (hU : U ∈ nhds (0 : H)) :
    ∃ V ∈ nhds (0 : H), IsClosed V ∧ (-V = V) ∧ V + V ⊆ U :=
  exists_closed_nhds_zero_neg_eq_add_subset hU

/-- **Sub-sub-lemma A.2 — interior of sum contains sum of interiors**.

For sets `S, T` in a topological add group, `interior S + interior T ⊆ interior (S + T)`.

**Mathlib discharge** (verified): `IsOpen.add_left` and `IsOpen.add_right`
exist via `Topology.Algebra.Group.Pointwise`. Compose for `interior + interior ⊆ interior(+)`.

**Difficulty**: EASY. ~15 lines. -/
theorem _sub_sub_lemma_A_2_interior_add
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (S T : Set H) :
    interior S + interior T ⊆ interior (S + T) :=
  -- the open set `interior S + interior T` is contained in `S + T`.
  interior_maximal (Set.add_subset_add interior_subset interior_subset) isOpen_interior.add_left

/-- **Sub-sub-lemma C.2 — Baire ⇒ nonempty interior in some closure**.

For a Baire space `H` covered by countably many closed sets, some closed set
has nonempty interior.

**Mathlib discharge** (verified): direct from `nonempty_interior_of_iUnion_of_closed`
in `Topology.Baire.Lemmas`. One-liner body.

**Difficulty**: TRIVIAL. ~5 lines. -/
theorem _sub_sub_lemma_C_2_baire_nonempty_interior
    {H : Type v} [TopologicalSpace H] [BaireSpace H] [Nonempty H]
    (S : ℕ → Set H) (hS_closed : ∀ n, IsClosed (S n))
    (hS_cover : ⋃ n, S n = Set.univ) :
    ∃ n, (interior (S n)).Nonempty :=
  nonempty_interior_of_iUnion_of_closed hS_closed hS_cover

/-- **Sub-sub-lemma D.1 — Inductive Cauchy sequence builder**.

Given approximate-preimage data: for each `n` we know `f(x_n) → y` faster than
the nbhd basis `V_n` shrinks. Builder constructs the Cauchy sequence `x_n`
with `x_{n+1} - x_n ∈ V_n` for the symmetric basis `V_n`.

**Mathlib discharge route**:
- `Nat.rec` for the inductive construction.
- `IsUniformAddGroup.cauchy_iff` for the Cauchy condition.

**Difficulty**: MEDIUM. ~40 lines. The substantive iteration. -/
theorem _sub_sub_lemma_D_1_cauchy_builder
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [(uniformity G).IsCountablyGenerated]
    (basis : ℕ → Set G) (hbasis : ∀ n, basis n ∈ nhds (0 : G))
    (hshrink : ∀ n, basis (n + 1) + basis (n + 1) ⊆ basis n)
    -- BINDING-RULE (b) addition: without cofinality, the conclusion fails
    -- (counterexample: basis n = univ for all n; shrinking holds trivially,
    -- but step n = n in ℝ then satisfies hstep yet step is not Cauchy).
    -- Cofinality matches BGR's implicit assumption (basis is a fundamental
    -- system of nbhds of 0); every consumer of this lemma supplies it via
    -- the IsCountablyGenerated nhds 0 basis.
    (hcofinal : ∀ V ∈ nhds (0 : G), ∃ n, basis n ⊆ V)
    (step : (n : ℕ) → G) (hstep : ∀ n, step (n + 1) - step n ∈ basis n) :
    CauchySeq step := by
  have h0_basis : ∀ n, (0 : G) ∈ basis n := fun n => mem_of_mem_nhds (hbasis n)
  -- Sum lemma: for any indexed family with xs i ∈ basis (n + 1 + i), Σ xs ∈ basis n.
  -- Proved by induction on k via iterated doubling.
  have hsum_lemma : ∀ k : ℕ, ∀ n : ℕ, ∀ xs : Fin k → G,
      (∀ i : Fin k, xs i ∈ basis (n + 1 + i)) → ∑ i, xs i ∈ basis n := by
    intro k
    induction k with
    | zero =>
      intro n xs _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact h0_basis _
    | succ k ih =>
      intro n xs hxs
      rw [Fin.sum_univ_succ]
      have h0 : xs 0 ∈ basis (n + 1) := by simpa using hxs 0
      have hrest : ∑ i, xs (Fin.succ i) ∈ basis (n + 1) := by
        apply ih (n + 1)
        intro i
        have := hxs (Fin.succ i)
        convert this using 2
        simp [Fin.val_succ]; ring
      exact hshrink _ (Set.add_mem_add h0 hrest)
  -- Telescoping: step (n + 1 + k) - step (n + 1) ∈ basis n via Finset.sum_range_sub.
  have htele : ∀ n k : ℕ, step (n + 1 + k) - step (n + 1) ∈ basis n := by
    intro n k
    have hsum_eq : step (n + 1 + k) - step (n + 1)
        = ∑ i ∈ Finset.range k, (step (n + 1 + (i + 1)) - step (n + 1 + i)) := by
      rw [Finset.sum_range_sub (fun i => step (n + 1 + i))]
    rw [hsum_eq, ← Fin.sum_univ_eq_sum_range]
    apply hsum_lemma k n
    intro j
    have h := hstep (n + 1 + (j : ℕ))
    rw [show n + 1 + ((j : ℕ) + 1) = n + 1 + (j : ℕ) + 1 from by omega]
    exact h
  -- basis is a HasBasis for nhds 0.
  have hbasis_basis : (nhds (0 : G)).HasBasis (fun _ : ℕ => True) basis :=
    ⟨fun V => ⟨fun hV => (hcofinal V hV).imp (fun _ h => ⟨trivial, h⟩),
      fun ⟨n, _, hsub⟩ => Filter.mem_of_superset (hbasis n) hsub⟩⟩
  -- Uniformity basis via swapped form: (a, b) ∈ s_n ↔ a - b ∈ basis n.
  have hunif_basis : (uniformity G).HasBasis (fun _ : ℕ => True)
      (fun n => {x | x.1 - x.2 ∈ basis n}) :=
    hbasis_basis.uniformity_of_nhds_zero_swapped
  rw [hunif_basis.cauchySeq_iff']
  intro n _
  refine ⟨n + 1, fun k hk => ?_⟩
  change step k - step (n + 1) ∈ basis n
  obtain ⟨j, rfl⟩ : ∃ j, k = n + 1 + j := ⟨k - (n + 1), by omega⟩
  exact htele n j

/-- **Sub-sub-lemma D.2 — Cauchy limit lives in nbhd**.

If `x_n` is Cauchy with `x_{n+1} - x_n ∈ V_n` (shrinking basis at 0), then
the limit `x = lim x_n` satisfies `x - x_0 ∈ V_0 + V_1 + ... ⊆ 2·V_0`.

**Mathlib discharge route**: `CauchySeq.tendsto_of_completeSpace` + sum-of-nbhds
inclusion. ~25 lines. -/
theorem _sub_sub_lemma_D_2_limit_in_nbhd
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    (step : ℕ → G) (hcauchy : CauchySeq step)
    (V : Set G) (_hV : V ∈ nhds (0 : G))
    (hstep_in_V : ∀ n, step n - step 0 ∈ V) :
    ∃ x : G, Filter.Tendsto step Filter.atTop (nhds x) ∧ x - step 0 ∈ closure V := by
  -- Cauchy + complete ⇒ converges.
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- `step n - step 0 → x - step 0` (continuity of subtraction) and each term lies in `V`,
  -- so the limit lies in `closure V`.
  exact ⟨x, hx, mem_closure_of_tendsto (hx.sub_const (step 0))
    (Filter.Eventually.of_forall hstep_in_V)⟩

/-! ## Main theorem (composes sub-lemmas A-E from sub-sub-lemmas A.1, A.2, C.1, C.2, D.1, D.2)
-/

/-- **Banach's open mapping theorem for complete metric topological abelian groups**
(Bourbaki [TG] Ch. III §3 no. 3 Théorème 1; Huber [Hu3] Lemma 2.4(i)).

Let `G, H` be Hausdorff topological abelian groups with countably-generated
uniformities (i.e. metrizable), both complete. Then every continuous surjective
additive group homomorphism `f : G →+ H` is open.

This is the substantive analytical input for Wedhorn 6.16/6.17/6.18 and for the
audit-pass-2 trio in `StructureSheaf.lean`.

**B2 SCOPE FINDING (2026-05-18, `b2_log.jsonl` entry 3)**: as currently
stated, this theorem is **mathematically false** without an extra
hypothesis such as `[SeparableSpace G]` or `[SigmaCompactSpace G]`.
Counterexample: `G = ℝ` with the **discrete** topology (complete,
countably-generated uniformity, UAG, T2), `H = ℝ` with the Euclidean
topology, `f = id`. Then `f` is continuous + surjective but not open
(`f({0}) = {0}` is not open in Euclidean ℝ). Bourbaki's proof needs
`G` to be σ-compact (Hewitt-Ross [HR] §5.29) OR separable (so `H` can
be covered by countably many translates of `f(U)` via the dense subset
of `G`); `[(uniformity G).IsCountablyGenerated]` alone supplies a
countable nbhd basis at 0 but does not give a countable cover of `G`
itself. Mathlib's normed-space Banach OMT works because normed spaces
are σ-compact via `⋃ n, ball 0 n`.

**Proof sketch** (Bourbaki, requires the missing hypothesis):
1. `G` is BaireSpace via complete + countably-generated uniformity.
2. For any neighbourhood `U` of 0 in `G`, `f(n·U)` covers `H` by countable union
   (uses σ-compactness or separability of `G`).
3. `H` Baire ⇒ some `n·f(U)` has nonempty interior ⇒ `f(U) − f(U)` contains nbhd of 0.
4. Cauchy completeness of `G` lifts approximate preimages to exact ones.
5. Translation invariance ⇒ open everywhere.

**Mathlib lemmas needed**:
- `BaireSpace.of_pseudoEMetricSpace_completeSpace` (Baire from complete + countably-generated)
- `Filter.HasBasis.mem_iff`, `nhds_zero` basis lemmas
- `nonempty_interior_of_iUnion_of_closed` (Baire category for closed sets)
- `CauchySeq.tendsto_of_completeSpace` (completeness ⇒ Cauchy converges) -/
theorem isOpenMap_of_completeSpace_of_countablyGenerated
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    -- BINDING-RULE (b) addition (2026-05-18): without `[SigmaCompactSpace G]`,
    -- the theorem is FALSE. Counterexample: G = ℝ-discrete (UAG, complete, cg,
    -- T2) ↦ H = ℝ-Euclidean via identity; f is continuous + surjective but not
    -- open (`f({0}) = {0}` is not open in Euclidean ℝ). Cf. `b2_log.jsonl`
    -- entry 3 and the docstring above. With `[SigmaCompactSpace G]` added the
    -- result reduces to mathlib's `AddMonoidHom.isOpenMap_of_sigmaCompact`.
    [SigmaCompactSpace G]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [CompleteSpace H] [(uniformity H).IsCountablyGenerated] [T2Space H]
    (f : G →+ H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsOpenMap f :=
  -- `[BaireSpace H]` synthesised from `[CompleteSpace H] +
  -- [(uniformity H).IsCountablyGenerated]` via
  -- `IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable` and
  -- `BaireSpace.of_completelyPseudoMetrizable` (both mathlib instances).
  AddMonoidHom.isOpenMap_of_sigmaCompact f hsurj hf

/-- **Corollary — Banach's theorem for surjections.** A continuous surjective
group homomorphism between complete metric topological abelian groups is a
quotient map (open + surjective).

Discharged trivially from `isOpenMap_of_completeSpace_of_countablyGenerated` +
the `IsOpenMap.isQuotientMap` characterization. -/
theorem isQuotientMap_of_completeSpace_of_countablyGenerated
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    [SigmaCompactSpace G]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [CompleteSpace H] [(uniformity H).IsCountablyGenerated] [T2Space H]
    (f : G →+ H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    Topology.IsQuotientMap f :=
  (AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated f hf hsurj).isQuotientMap
    hf hsurj

/-- **Bourbaki's full any-two-imply-third statement** — the version Wedhorn 6.16
states. Let `G, H` be Hausdorff topological abelian groups with countably-
generated uniformities. Assume `G` is complete. Let `f : G →+ H` be continuous.
Among:
- (a) `H` is complete
- (b) `f` is surjective
- (c) `f` is open

any two imply the third.

(In the project we will mostly use the "(a) ∧ (b) ⇒ (c)" direction, which is
`isOpenMap_of_completeSpace_of_countablyGenerated` above.) -/
theorem banach_two_of_three
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    [SigmaCompactSpace G]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [(uniformity H).IsCountablyGenerated] [T2Space H]
    (f : G →+ H) (hf : Continuous f) :
    ((CompleteSpace H ∧ Function.Surjective f) → IsOpenMap f) ∧
    ((CompleteSpace H ∧ IsOpenMap f) → Function.Surjective f) ∧
    ((Function.Surjective f ∧ IsOpenMap f) → CompleteSpace H) :=
  ⟨fun ⟨hcomp, hsurj⟩ =>
    haveI := hcomp
    isOpenMap_of_completeSpace_of_countablyGenerated f hf hsurj,
   -- (a) ∧ (c) ⇒ (b): **B2 FALSE (2026-05-18)** — see `b2_log.jsonl` entry 4.
   -- Counterexample: G = 2ℤ ↪ H = ℤ (both discrete, addition; G complete,
   -- cg, UAG, SigmaCompact; H complete, cg, UAG, T2). f = inclusion is
   -- continuous + open but NOT surjective (range is 2ℤ ⊊ ℤ).
   sorry,
   -- (b) ∧ (c) ⇒ (a): f surjective + f open ⇒ H complete. Via the AddEquiv
   -- eq : (G ⧸ f.ker) ≃+ H induced by surjectivity, plus completeness of
   -- the quotient (`QuotientAddGroup.completeSpace_right'`).
   fun ⟨hsurj, hopen⟩ => by
     haveI hk_normal : f.ker.Normal := AddSubgroup.normal_of_isAddCommutative _
     haveI : FirstCountableTopology G := UniformSpace.firstCountableTopology G
     letI τQ : UniformSpace (G ⧸ f.ker) :=
       IsTopologicalAddGroup.rightUniformSpace (G ⧸ f.ker)
     haveI hτQ_uag : @IsUniformAddGroup _ τQ _ := isUniformAddGroup_of_addCommGroup
     haveI hτQ_complete : @CompleteSpace _ τQ :=
       QuotientAddGroup.completeSpace_right G f.ker
     -- f is a topological quotient map: open + continuous + surjective.
     have hf_quot : Topology.IsQuotientMap f := hopen.isQuotientMap hf hsurj
     -- The lift eq : G ⧸ f.ker ≃+ H from surjectivity.
     let eq : G ⧸ f.ker ≃+ H := QuotientAddGroup.quotientKerEquivOfSurjective f hsurj
     -- eq is continuous: eq ∘ mk = f (continuous), and mk is a quotient map.
     have heq_cont : @Continuous _ _ τQ.toTopologicalSpace _ eq :=
       (QuotientAddGroup.isQuotientMap_mk f.ker).continuous_iff.mpr hf
     -- eq.symm is continuous: eq.symm ∘ f = mk (continuous), f is a quotient map.
     have heq_symm_cont : Continuous (eq.symm : H → G ⧸ f.ker) := by
       rw [hf_quot.continuous_iff]
       have : ⇑eq.symm ∘ ⇑f = (QuotientAddGroup.mk : G → G ⧸ f.ker) := by
         ext g
         change eq.symm (f g) = QuotientAddGroup.mk g
         have h1 : eq (QuotientAddGroup.mk g) = f g := rfl
         rw [← h1]
         exact eq.symm_apply_apply (QuotientAddGroup.mk g)
       rw [this]
       exact QuotientAddGroup.continuous_mk
     -- UC for both directions via `uniformContinuous_addMonoidHom_of_continuous`.
     have heq_uc : @UniformContinuous _ _ τQ _ eq :=
       @uniformContinuous_addMonoidHom_of_continuous _ _ τQ _ _ _ _ _ _ _ _ _ heq_cont
     have heq_symm_uc : @UniformContinuous _ _ _ τQ eq.symm.toAddMonoidHom :=
       @uniformContinuous_addMonoidHom_of_continuous _ _ _ _ _ _ τQ _ _ _ _ _ heq_symm_cont
     -- IsUniformEmbedding of eq.toEquiv.
     have heq_emb : @IsUniformEmbedding _ _ τQ _ eq.toEquiv := by
       apply @Equiv.isUniformEmbedding _ _ τQ _ eq.toEquiv heq_uc heq_symm_uc
     -- Transfer completeness via the embedding.
     exact (@completeSpace_congr _ _ τQ _ eq.toEquiv heq_emb).mp hτQ_complete⟩

end AddMonoidHom
