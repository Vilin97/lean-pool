/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaCompact
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpvAITopology
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaQCviaSpvAI
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicMorphismsCore

/-!
# No-`hArch` compactness and per-`v` cofinality (T-COMPACT-NO-HARCH)

Per round-22 reviewer (ChatGPT Pro, 2026-05-16): no-`hArch` compactness of
rational half-spaces, plus a per-`v` cofinality bridge used in the P3
domination lemma.

The half-space compactness itself remains a TODO (`Spv(A, I)` track), but
the **per-v cofinality** sub-lemma is fully proved here and is the
substantive ingredient for the domination lemma's open-cover argument.

## Mathematical content

For `v ∈ Spa(A, A⁺)` (continuous), `π : A` topologically nilpotent, and
`a : A` with `v(a) ≠ 0`, there exists `N : ℕ` with `v(π^N) < v(a)`. This
is per-`v` cofinality at the specific value `γ = v(a)`, following exactly
the technique of `not_vle_one_of_mem_spa_of_topologicallyNilpotent` (which
is the `γ = 1` specialisation).

No mul-archimedean assumption enters; the argument is just Wedhorn 7.7
continuity + topological nilpotence of `π`.

References: Wedhorn §7.1–§7.2 + §7.5 (arXiv:1910.05934). Round-22
reviewer reply at `.mathlib-quality/expert-review/2026-05-16-3/reply.md`.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **Per-`v` cofinality bridge (no `hArch`).** For a continuous valuation
`v ∈ Spa A A⁺`, a topologically nilpotent element `π : A`, and any `a : A`
with `v(a) ≠ 0`, there exists `N : ℕ` such that `v(π^N) < v(a)` strictly,
i.e. `¬ v.vle a (π^N)`.

Proved by adapting `not_vle_one_of_mem_spa_of_topologicallyNilpotent`
(`SpaCompact.lean`): continuity says `{x : v(x) < v(a)}` is open;
topological nilpotence of `π` says `π^N → 0` in `A`; so eventually
`v(π^N) < v(a)`. -/
lemma exists_pow_lt_of_topNilp_of_ne_zero
    {v : Spv A} (hv : v ∈ Spa A A⁺)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    {a : A} (ha : ¬ v.vle a 0) :
    ∃ N : ℕ, ¬ v.vle a (π ^ N) := by
  letI : ValuativeRel A := v.toValuativeRel
  -- Continuity of `v` yields `{x | val(x) < val(a)}` open.
  have hcont : v.IsContinuous := hv.1
  have h_open :
      IsOpen {x : A | (ValuativeRel.valuation A) x <
        (ValuativeRel.valuation A) a} :=
    hcont ((ValuativeRel.valuation A) a)
  -- `0` is in this set since `val(a) ≠ 0` (from `ha`).
  have h0_mem : (0 : A) ∈ {x : A | (ValuativeRel.valuation A) x <
      (ValuativeRel.valuation A) a} := by
    simp only [Set.mem_setOf_eq, map_zero]
    -- `val(a) ≠ 0` follows from `ha : ¬ v.vle a 0`.
    have hva_ne : (ValuativeRel.valuation A) a ≠ 0 := by
      intro h_eq
      apply ha
      -- `val(a) = 0` ⟹ `val(a) ≤ val(0) = 0` ⟹ `v.vle a 0`.
      have hva_le : (ValuativeRel.valuation A) a ≤
          (ValuativeRel.valuation A) 0 := by
        rw [h_eq, map_zero]
      exact (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation A) a 0).mpr hva_le
    exact zero_lt_iff.mpr hva_ne
  -- Topological nilpotence of `π` + open set containing 0 → eventually `π^n` is in.
  obtain ⟨N, hN⟩ := (hπ_tn.eventually (h_open.mem_nhds h0_mem)).exists
  -- `hN : (ValuativeRel.valuation A) (π^N) < (ValuativeRel.valuation A) a`.
  -- Translate to `¬ v.vle a (π^N)`.
  refine ⟨N, ?_⟩
  intro h_vle
  have h_le := (Valuation.Compatible.vle_iff_le
    (v := ValuativeRel.valuation A) a (π ^ N)).mp h_vle
  exact absurd h_le (not_le.mpr hN)

/-- **Uniform `π`-power domination on a compact set.** Given a compact set
`K ⊆ ↥(Spa A A⁺)`, a topologically nilpotent `π : A`, and `a : A` with
`v(a) ≠ 0` for every `v ∈ K`, there exists a uniform `N : ℕ` such that
`v.vle (π^N) a` for every `v ∈ K`.

Proof: the per-`v` cofinality `exists_pow_lt_of_topNilp_of_ne_zero`
supplies a per-point `N(v)`; the open sets
`U_N := K ∩ {w : (w : Spv A).vle (π^N) a}` are monotone increasing and
cover `K`; compactness extracts a single uniform `N₀`.

This is the substantive open-cover ingredient for the P3 domination
lemma, modulo the (still TODO) no-`hArch` compactness of the half-space
itself. -/
lemma exists_uniform_pow_vle_on_compact
    {K : Set ↥(Spa A A⁺)} (hK : IsCompact K)
    {π : A} (hπ_tn : IsTopologicallyNilpotent π)
    {a : A} (ha : ∀ w ∈ K, ¬ (w.1 : Spv A).vle a 0) :
    ∃ N : ℕ, ∀ w ∈ K, (w.1 : Spv A).vle (π ^ N) a := by
  -- The open cover: `U N` = `{w ∈ ↥(Spa A A⁺) : w.1.vle (π^N) a}`, intersected with K.
  -- Each open in `↥(Spa A A⁺)` since `basicOpen` is open in Spv and
  -- the subtype map is continuous.
  let U : ℕ → Set ↥(Spa A A⁺) := fun N ↦
    Subtype.val ⁻¹' (basicOpen (π ^ N) a : Set (Spv A))
  have hU_open : ∀ N, IsOpen (U N) := fun N ↦
    (isOpen_basicOpen _ _).preimage continuous_subtype_val
  -- The cover is monotone increasing (`U N ⊆ U (N+1)` via `v.vle (π^(N+1)) (π^N)`).
  have hU_mono : ∀ N M, N ≤ M → U N ⊆ U M := by
    intro N M hNM w hw
    obtain ⟨hwN_le, hw_a_ne⟩ := hw
    refine ⟨?_, hw_a_ne⟩
    -- `v.vle (π^M) a` from `v.vle (π^N) a` and `v.vle (π^M) (π^N)`.
    letI : ValuativeRel A := w.1.toValuativeRel
    have : (ValuativeRel.valuation A) (π ^ M) ≤
        (ValuativeRel.valuation A) (π ^ N) := by
      simp only [map_pow]
      have hπ_le_one : (ValuativeRel.valuation A) π ≤ 1 := by
        by_contra h_not
        push Not at h_not
        -- if v(π) > 1, then for the "v(π^n) < 1" set being a nbhd of 0, fails.
        -- Use that the Spa hypothesis gives bounded power.
        -- Actually for our purpose, we use that π is top.nilp. via hπ_tn.
        -- v(π) > 1 contradicts top.nilp.
        have h_nilp : ¬ w.1.vle 1 π := by
          have hw_spa : w.1 ∈ Spa A A⁺ := w.2
          exact not_vle_one_of_mem_spa_of_topologicallyNilpotent hw_spa hπ_tn
        apply h_nilp
        -- v(1) ≤ v(π) iff 1 ≤ v(π).
        have := (Valuation.Compatible.vle_iff_le
          (v := ValuativeRel.valuation A) 1 π).mpr
        apply this
        rw [map_one]
        exact h_not.le
      -- For `x ≤ 1` and `N ≤ M`, we have `x^M ≤ x^N`.
      -- Proof: x^M = x^N · x^(M-N) ≤ x^N · 1 = x^N (since x^(M-N) ≤ 1).
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
      rw [pow_add]
      calc (ValuativeRel.valuation A) π ^ N * (ValuativeRel.valuation A) π ^ k
          ≤ (ValuativeRel.valuation A) π ^ N * 1 :=
            mul_le_mul_right (Left.pow_le_one_of_le hπ_le_one k) _
        _ = (ValuativeRel.valuation A) π ^ N := mul_one _
    -- Now translate to vle.
    -- hwN_le : w.1.vle (π^N) a, i.e., v(π^N) ≤ v(a).
    -- We have v(π^M) ≤ v(π^N) ≤ v(a), so v(π^M) ≤ v(a).
    have hwN_le' := (Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation A) (π ^ N) a).mp hwN_le
    exact (Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation A) (π ^ M) a).mpr
      (le_trans this hwN_le')
  -- The cover covers K: for each `w ∈ K`, per-v cofinality gives some N.
  have hK_cover : K ⊆ ⋃ N, U N := by
    intro w hw
    have hw_spa : w.1 ∈ Spa A A⁺ := w.2
    have hw_a_ne : ¬ w.1.vle a 0 := ha w hw
    obtain ⟨N, hN_strict⟩ :=
      exists_pow_lt_of_topNilp_of_ne_zero hw_spa hπ_tn hw_a_ne
    refine Set.mem_iUnion.mpr ⟨N, ?_, hw_a_ne⟩
    -- `hN_strict : ¬ w.1.vle a (π^N)`, want `w.1.vle (π^N) a`.
    -- From totality of `vle`.
    rcases w.1.vle_total (π ^ N) a with h | h
    · exact h
    · exact absurd h hN_strict
  -- Apply `IsCompact.elim_directed_cover`.
  have hU_directed : Directed (· ⊆ ·) U := fun N M ↦
    ⟨max N M, hU_mono N (max N M) (le_max_left N M),
     hU_mono M (max N M) (le_max_right N M)⟩
  obtain ⟨N₀, hN₀⟩ := hK.elim_directed_cover U hU_open hK_cover hU_directed
  refine ⟨N₀, fun w hw ↦ ?_⟩
  exact (hN₀ hw).1

variable [IsHuberRing A] [IsTateRing A]

/-- **Sub-leaf L1.1.a' — closed intersection with `range ιSpv` in the Sierpinski
ambient.** On `range ιSpv`, the open cylinder `{r | r (g, h)}` is constrained by the
`apply_iff` valuation-characteristic axiom (Phase 2 of the Sierpinski embedding
machinery, `SpvAITopology.lean`); combined with closedness of `range ιSpv`, this lets
us conclude the intersection is closed in the Sierpinski product.

**⚠ B2 CANDIDATE (logged 2026-05-22).** The statement of this lemma is almost
certainly FALSE as written, for two independent reasons that both flow from the
Sierpinski choice of topology on `Prop`:

1. **`range ιSpv` is not closed in Sierpinski** (project's own counterexample at
   `ValuationSpectrumCompact.lean`, lines 440-451). Hence even the "easy" factor
   `range ιSpv ∩ S` cannot be obtained as "closed ∩ S" via `range ιSpv` being
   closed; the whole Phase-2 plan in `SpvAITopology.lean` (Sub-leaves 1-9) sits
   on hypothetical Sierpinski-closedness claims that have all been left as `sorry`
   (no progress on any of them), and the project has pivoted to Alexander's
   sub-basis theorem (`compactSpace_of_subbasic_subcover`) to avoid this route
   for compactness.

2. **The cylinder `{r | r (g, h) ∨ (¬ r (h, h) ∧ ¬ r (g, g))}` is open ∪ closed
   in Sierpinski, hence not closed.** Intersection with `range ιSpv` does
   reformulate `r (g, h)` via `apply_iff` (on range, `r (g, h) ↔ vleOf r g h ∧
   ¬ vleOf r h 0`), but this rewrites an open coordinate cylinder into a
   conjunction that still mixes an open conclusion with a closed condition;
   no resulting expression is a finite Boolean combination of Sierpinski-closed
   cylinders. The pointwise `boolToProp : Bool → Prop` map is continuous but
   **not closed** (`{true} ↦ {True}`, which is Sierpinski-open not -closed), so
   one cannot transfer closedness from the discrete Bool world (where
   `isClosed_range_ιSpv_bool` is genuinely proved) back to Sierpinski.

This sub-lemma was introduced as the "refold" step expected to discharge
`isClosed_ιSpv_preimage_vleCylinder` after the `ιSpv_isInducing.isClosed_iff`
reduction. Closing the consumer (`isClosed_ιSpv_preimage_vleCylinder` /
`isClosed_setOf_vle`) requires a completely different witness in the Sierpinski
ambient — the genuine closed-half-space content of `{v | v.vle g h}` in `Spv A`
must come from a route that does NOT go through Sierpinski closure
(e.g., via a discrete Bool ambient + a continuity-of-evaluation argument
on `Γ_v`, matching Wedhorn's actual proof of Spv spectrality / Thm 7.8).

Preserved as a sorry-bodied sub-lemma per CLAUDE.md BINDING RULE (no signature
changes, no hypotheses added) while the surrounding consumer is rerouted; the
lemma itself is flagged as a B2 candidate in `.mathlib-quality/b2_log.jsonl`. -/
private lemma isClosed_range_ιSpv_inter_vleCylinder (g h : A) :
    IsClosed (Set.range (ιSpv : Spv A → (A × A → Prop)) ∩
      { r : A × A → Prop | r (g, h) ∨ (¬ r (h, h) ∧ ¬ r (g, g)) }) := by
  sorry

/-- **Cylinder closedness in the Sierpinski power (L1.1.a).**
The cylinder `{r ∈ A×A → Prop | r (g, h) ∨ (¬ r (h, h) ∧ ¬ r (g, g))}` pulls back to a
closed subset of `Spv A` along the Huber embedding `ιSpv`.

This is the genuine topological content of `isClosed_setOf_vle`: the predicate
`vle_iff_ιSpv` rewrites `v.vle g h` as the indicated disjunction in `ιSpv v`, so
closedness of the half-space `{v | v.vle g h}` reduces to closedness of this preimage
cylinder. The cylinder itself is a disjunction of an open cylinder
(`{r | r (g, h)}`, Sierpinski-open) and a closed cylinder
(`{r | ¬ r (h, h) ∧ ¬ r (g, g)}`, intersection of two Sierpinski-closed cylinders),
so its preimage being closed is a non-trivial fact — it requires the closedness of
`range ιSpv` ("Phase 2" of the Sierpinski embedding machinery,
`ValuationSpectrumCompact.lean`), which lets one re-fold the open piece into the closed
range via the `vle_iff_ιSpv` characterisation.

**Proof.** Use `ιSpv_isInducing.isClosed_iff` to reduce closedness in `Spv A` to the
existence of a closed witness in the Sierpinski ambient. Choose the witness
`range ιSpv ∩ {r | r (g, h) ∨ (¬ r (h, h) ∧ ¬ r (g, g))}`: its preimage under `ιSpv`
equals the target (because `ιSpv` lands in its own range), and it is closed by the
named sub-lemma `isClosed_range_ιSpv_inter_vleCylinder` (Phase 2 obligation).

Tracked as L1.1.a in the work plan (`docs/TATE-ACYCLICITY-WORK-PLAN.md`). -/
theorem isClosed_ιSpv_preimage_vleCylinder (g h : A) :
    IsClosed (ιSpv ⁻¹' { r : A × A → Prop |
      r (g, h) ∨ (¬ r (h, h) ∧ ¬ r (g, g)) } : Set (Spv A)) := by
  rw [ιSpv_isInducing.isClosed_iff]
  refine ⟨Set.range ιSpv ∩ { r : A × A → Prop |
      r (g, h) ∨ (¬ r (h, h) ∧ ¬ r (g, g)) },
    isClosed_range_ιSpv_inter_vleCylinder g h, ?_⟩
  ext v
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨fun hh ↦ hh.2, fun hh ↦ ⟨⟨v, rfl⟩, hh⟩⟩

/-- **Sub-leaf of 1.1 — closedness at the `Spv A` level.**
The half-space `{v ∈ Spv A | v.vle g h}` is closed in the `Spv A` topology.

Wedhorn ref: implicit in 7.8 (evaluation `Spv A → Γ_v` is continuous) plus closedness of
`{(x, y) | x ≤ y}` in `Γ_v × Γ_v`. The proof requires Phase 2 of the Sierpinski embedding
machinery (`ValuationSpectrumCompact.lean`) and is the genuine mathematical content of
sub-lemma 1.1; the Spa-level version reduces to this via continuity of `Subtype.val`.

**Proof.** Rewrite `{v | v.vle g h}` via `vle_iff_ιSpv` as the preimage of the cylinder
`{r | r (g, h) ∨ (¬ r (h, h) ∧ ¬ r (g, g))}` under `ιSpv`, then invoke the (deferred)
sub-lemma `isClosed_ιSpv_preimage_vleCylinder`. -/
theorem isClosed_setOf_vle (g h : A) :
    IsClosed {v : Spv A | v.vle g h} := by
  have hrw : {v : Spv A | v.vle g h} =
      ιSpv ⁻¹' { r : A × A → Prop |
        r (g, h) ∨ (¬ r (h, h) ∧ ¬ r (g, g)) } := by
    ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    exact vle_iff_ιSpv v g h
  rw [hrw]
  exact isClosed_ιSpv_preimage_vleCylinder g h

/-- **Sub-lemma 1.1 of T-COMPACT-NO-HARCH (work plan, `TATE-ACYCLICITY-WORK-PLAN.md`).**
Closedness of the half-space `{w ∈ ↥(Spa A A⁺) | w.1.vle g h}` in the subtype topology.

Wedhorn ref: implicit in 7.8 (evaluation `Spv A → Γ_v` is continuous) plus closedness of
`{(x, y) | x ≤ y}` in `Γ_v × Γ_v`. Pulled back along the continuous inclusion
`Subtype.val : ↥(Spa A A⁺) → Spv A`.

**Proof.** Reduces to `isClosed_setOf_vle` (the Spv-level closed-half-space lemma) via
continuity of the inclusion `Subtype.val : ↥(Spa A A⁺) → Spv A`. -/
theorem isClosed_subtype_setOf_vle (g h : A) :
    IsClosed (Subtype.val ⁻¹' {v : Spv A | v.vle g h} : Set ↥(Spa A A⁺)) :=
  (isClosed_setOf_vle g h).preimage continuous_subtype_val

/-- **Genuine no-`hArch` Bool-image closedness (L1.3.a core, sub-sub-lemma α).**
In the no-`hArch` Tate case, the Bool image `ιSpvBool '' (Spa A A⁺)` is
closed in the discrete Bool product `(A × A → Bool)`.

This is the genuine mathematical content of L1.3.a, isolated from the
existence-of-closed-target packaging. In the `hArch` case it follows from
`isClosed_image_spa_ιSpv_bool_of_tate` (`SpaCompact.lean`) via the
`{r | r(1, π) = false}` cylinder; without `hArch` the witness instead encodes
the `Spv(A, I)`-spectrality coordinate constraints (Wedhorn 7.5 + 7.12 + 7.30),
i.e. the cofinal/microbial alternative on `v`.

**Decomposition (2026-05-23).** Per CLAUDE.md BINDING RULE this `sorry`-bodied
sub-lemma carries the genuine no-`hArch` obligation; downstream packaging
(`exists_closed_bool_target_noHArch`, `image_spa_ιSpv_bool_noHArch`) reduces
to it via the trivial-witness trick `S := image`, breaking the previous
circular dependency between the existence packaging and the closedness
extraction. Tracked as the no-`hArch` Spv(A,I)-spectral leaf. -/
private lemma isClosed_image_spa_ιSpv_bool_noHArch :
    IsClosed ((ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺)) := by
  sorry

/-- **Closed Bool target set for `Spa A A⁺` in the no-`hArch` Tate case
(L1.3.a, packaging).** A concrete closed subset of `A × A → Bool`
into which `ιSpvBool '' Spa A A⁺` exactly fits (relative to `range ιSpvBool`).

In the `hArch` case this would be `(⋂ a ∈ A⁺, {r | r(a,1) = true}) ∩
{r | r(1, π) = false}` from `image_spa_ιSpv_bool_of_tate`; without `hArch`
the description requires the Spv(A, I)-spectrality coordinate constraints
(Wedhorn 7.5 + 7.12 + 7.30), all packaged into the genuine sub-lemma
`isClosed_image_spa_ιSpv_bool_noHArch`.

**Proof.** Trivial-witness trick: take `S` to be the image itself. Closedness
comes from the named sub-lemma `isClosed_image_spa_ιSpv_bool_noHArch`, and
`range ∩ image = image` since `image ⊆ range`. -/
private lemma exists_closed_bool_target_noHArch :
    ∃ S : Set (A × A → Bool), IsClosed S ∧
      (ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
        Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩ S :=
  ⟨(ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺),
    isClosed_image_spa_ιSpv_bool_noHArch,
    (Set.inter_eq_right.mpr (Set.image_subset_range _ _)).symm⟩

/-- **Sub-lemma (genuine content of L1.3.a).** In the no-`hArch` Tate case,
`ιSpvBool '' Spa A A⁺` is closed in the discrete Bool product
`(A × A → Bool)`. Re-exports `isClosed_image_spa_ιSpv_bool_noHArch` under
the legacy name expected by `image_spa_ιSpv_bool_noHArch` below. -/
lemma isClosed_image_spa_ιSpv_bool_noHArch_aux :
    IsClosed ((ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺)) :=
  isClosed_image_spa_ιSpv_bool_noHArch

/-- **Sub-lemma L1.3.a of T-COMPACT-NO-HARCH (work plan, `TATE-ACYCLICITY-WORK-PLAN.md`).**
Closed Bool-image description for `Spa A A⁺` in the no-`hArch` Tate case.

Mathematical content: there exists a closed subset `S ⊆ A × A → Bool` such that
`ιSpvBool '' (Spa A A⁺) = range ιSpvBool ∩ S`. With `hArch` this is the
`{r | r (1, π) = false}` cylinder of `image_spa_ιSpv_bool_of_tate`; without
`hArch` the cylinder set instead encodes the `Spv(A, I)`-spectrality condition
(Wedhorn 7.5 + 7.12 + 7.30) via additional coordinate constraints capturing
the cofinal/microbial alternative on `v`.

**Decomposition (2026-05-22).** Per CLAUDE.md BINDING RULE the genuine
mathematical content — closedness of the Bool image of `Spa A A⁺` in the
no-`hArch` Tate setting — is isolated into the named sub-lemma
`isClosed_image_spa_ιSpv_bool_noHArch_aux` (still `sorry`-bodied). Given that
closedness, the existence claim is discharged by taking `S` to be the image
itself and noting `image ⊆ range`, so `range ∩ image = image`. -/
lemma image_spa_ιSpv_bool_noHArch :
    ∃ S : Set (A × A → Bool), IsClosed S ∧
      (ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺) =
        Set.range (ιSpvBool : Spv A → (A × A → Bool)) ∩ S :=
  ⟨(ιSpvBool : Spv A → (A × A → Bool)) '' (Spa A A⁺),
    isClosed_image_spa_ιSpv_bool_noHArch_aux,
    (Set.inter_eq_right.mpr (Set.image_subset_range _ _)).symm⟩

/-- **Sub-lemma 1.3 of T-COMPACT-NO-HARCH (work plan, `TATE-ACYCLICITY-WORK-PLAN.md`).**
Quasi-compactness of the preimage of a rational open `rationalOpen L.T L.s` in
`↥(Spa A A⁺)`, **without** any mul-archimedean assumption on valuation value groups.

Wedhorn ref: Theorem 7.35(2). The existing
`isCompact_preimage_rationalOpen_of_tate_pseudouniformizer` (`SpaCompact.lean:586`)
requires `hArch`; the no-`hArch` version is supplied via the `Spv(A, I)` spectral
infrastructure track (`T-SPV-AI-WEDHORN-710`, see `SpvAITopology.lean`).

**Proof.** Delegates to the abstract Bool-cylinder criterion
`isCompact_preimage_rationalOpen_of_isClosed_image` (Tate-style) with the
closed image description supplied by the sub-lemma
`image_spa_ιSpv_bool_noHArch`. The actual no-`hArch` content is concentrated
in that sub-lemma's body (still `sorry`-bodied, tracked as L1.3.a). -/
theorem isCompact_preimage_rationalOpen_noHArch
    [IsTateRing A] (hplus_open : IsOpen ((A⁺ : Subring A) : Set A))
    (L : RationalLocData A) (hRat : L.IsRational) :
    IsCompact (Subtype.val ⁻¹' rationalOpen L.T L.s : Set ↥(Spa A A⁺)) := by
  obtain ⟨P, π, hA₀le, hπ, hunit⟩ :=
    IsTateRing.exists_principal_pairOfDefinition_le_subring (A := A) hplus_open
  refine isCompact_subtype_rationalOpen P hπ (fun x => hA₀le x.2)
    (Ideal.span {((π : A))}) rfl L.T L.s ?_
  rw [hRat.span_eq_top, Ideal.radical_top]
  exact le_top

/-- **(T-COMPACT-NO-HARCH, round-22 reviewer-mandated.) Half-space compactness
without `hArch`.** The half-space `R(L) ∩ {v(g) ≤ v(h)}` in
`↥(Spa A A⁺)` is compact, **without** any mul-archimedean assumption on
valuation value groups.

**Proof.** Decomposed into two sub-lemmas (work plan L1.1 + L1.3, both retained
as `sorry`-bodied sub-lemmas):
* `isCompact_preimage_rationalOpen_noHArch` — quasi-compactness of the rational
  open preimage (Wedhorn 7.35(2), no-`hArch`);
* `isClosed_subtype_setOf_vle` — closedness of the half-space pulled back from
  `Spv A`.

The assembly is a one-liner: a closed subset of a compact set is compact
(`IsCompact.inter_right`). The `Subtype.val ⁻¹'` distributes over `∩` definitionally,
giving the required intersection form. -/
theorem isCompact_rationalOpen_inter_vle_noHArch
    [IsTateRing A] (hplus_open : IsOpen ((A⁺ : Subring A) : Set A))
    (L : RationalLocData A) (hRat : L.IsRational) (g h : A) :
    IsCompact (Subtype.val ⁻¹'
      (rationalOpen L.T L.s ∩ {v | v.vle g h}) : Set ↥(Spa A A⁺)) := by
  -- `Subtype.val ⁻¹' (A ∩ B) = Subtype.val ⁻¹' A ∩ Subtype.val ⁻¹' B`.
  rw [Set.preimage_inter]
  -- A compact set intersected with a closed set on the right is compact.
  exact (isCompact_preimage_rationalOpen_noHArch hplus_open L hRat).inter_right
    (isClosed_subtype_setOf_vle g h)

end ValuationSpectrum
