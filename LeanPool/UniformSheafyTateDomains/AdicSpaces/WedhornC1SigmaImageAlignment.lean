/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPerPieceLaurentCoverAssembly
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCompatFromTestFamily

/-!
# Wedhorn 8.34(ii) — C1 D_T ↔ σ-rescaled image alignment (T062)

T058 (commit `947600d`) closed the Wedhorn Lemma 8.33 multi-piece
collapse `LaurentCoverPresheafLemma833Assembly` for the **σ-rescaled
image target** `R_target := rationalOpen (T_test.image (σ⁻¹ * ·)) D_s`
unconditionally. The downstream C1 supplier chain (T056 / T060 / T061)
consumes the predicate at the **actual cover-piece target**
`R_target := rationalOpen D_T D_s` for some `D_T : Finset A` chosen by
the supplier (typically `D.T.image (algebraMap …)` after pushing forward
to a localization, or `localizedTestFamily s T_D s_D` in the canonical
test-family construction).

This file lands the **alignment bridge** between these targets.

## Mathematical content

`rationalOpen` is **anti-monotone in the test family**: if
`T₁ ⊆ T₂` then `rationalOpen T₂ s ⊆ rationalOpen T₁ s` (more
constraints carve out a smaller set). Composed with monotonicity of
`LaurentCoverPresheafLemma833Assembly` in the target, this gives:

* If `D_T ⊆ T_test.image (σ⁻¹ * ·)`, then T058's image-target discharge
  yields the predicate for `R_target := rationalOpen D_T D_s`.

The supplier's natural choice is `T_test := D_T.image (σ * ·)`, for
which `T_test.image (σ⁻¹ * ·) = D_T` exactly (σ and σ⁻¹ cancel). With
this choice, the alignment is **trivial** and the C1 supplier's clause
2 conclusion is dischargeable purely from per-`t` source-restricted
data over `D_T`, no σ-rescaling needed.

## What this file provides

* `rationalOpen_anti_mono_T` — anti-monotonicity of `rationalOpen` in
  the test family `T`. Reusable mathlib-style primitive.

* `LaurentCoverPresheafLemma833Assembly_mono_target` — monotonicity of
  the structured Lemma 8.33 predicate in `R_target`.

* `LaurentCoverPresheafLemma833Assembly_via_subset_alignment` —
  **main bridge** (T062 deliverable): from `D_T ⊆ T_test.image
  (σ⁻¹ * ·)`, discharge the predicate at the actual C1 target
  `rationalOpen D_T D_s` via composition with T058's image-target
  discharge.

* `image_sigma_inv_image_sigma_eq_self` — the supplier-natural
  cancellation lemma: `(D_T.image (σ * ·)).image (σ⁻¹ * ·) = D_T`.

* `LaurentCoverPresheafLemma833Assembly_via_sigma_shift` — the
  **canonical exact-alignment discharge**: for the σ-shifted choice
  `T_test := D_T.image (σ * ·)`, the predicate for `rationalOpen D_T
  D_s` holds unconditionally.

* `rationalOpen_global_subset_via_sigma_shift_t_indexed` — the **clean
  σ-free consumer**: with `T_test := D_T.image (σ * ·)`, the C1
  supplier's clause 2 conclusion `rationalOpen (insert f T_base) s ⊆
  rationalOpen D_T D_s` follows from purely **t-indexed** Laurent
  cover data over `D_T` (per-piece subsets `R(insert f, s) ∩ R({1}, t)
  ⊆ R({t}, D_s)` and a Laurent cover `∀ w, ∃ t ∈ D_T, w ∈ R({1}, t)`)
  — no σ-rescaling visible in the user-facing statement.

* `localizedTestFamily_sigma_rescaled_image_bridge` — abstract version
  of the bridge phrased over `D_T_loc : Finset A` (no `localizedTestFamily`
  reference); kept as a thin alias for callers operating on a generic
  ambient ring.

* `image_sigma_image_sigma_inv_localizedTestFamily` —
  σ-shift cancellation specialised to
  `localizedTestFamily s T_D s_D`: the supplier-natural choice
  `T_test := (localizedTestFamily s T_D s_D).image (σ_loc * ·)` makes
  the σ-rescaled image cancel back to the original
  `localizedTestFamily ...` exactly.

* `LaurentCoverPresheafLemma833Assembly_at_localizedTestFamily` —
  σ-shift exact-alignment discharge at the **actual** C1 cover-piece
  denominator target `rationalOpen (localizedTestFamily s T_D s_D)
  D_s` on `Localization.Away s`. Closes the theorem-level bridge from
  T058's σ-rescaled image discharge to the actual `localizedTestFamily
  ...` target.

* `rationalOpen_global_subset_at_localizedTestFamily_via_sigma_shift_t_indexed`
  — clean σ-free t-indexed end-to-end consumer at the actual
  `localizedTestFamily s T_D s_D` target. From per-piece subsets and a
  t-indexed Laurent cover over `localizedTestFamily ...` (no σ-
  rescaling visible), derive the C1 supplier's clause 2 conclusion
  `rationalOpen (insert f_loc T_base_loc) s_base_loc ⊆ rationalOpen
  (localizedTestFamily s T_D s_D) D_s`.

## Why the σ-shifted choice closes the actual C1 chain

The C1 supplier of T061 (`WedhornC1Lemma833PerCallAssemblyData`) takes
`σ : Aˣ`, `T_test : Finset A`, and per-call hypotheses including the
Lemma 8.33 predicate. Choosing `T_test := D.T.image (σ * ·)` (with σ
the σ-strict-domination unit and `D.T` the cover-piece's denominator
family) makes the alignment **exact**: `T_test.image (σ⁻¹ * ·) = D.T`,
so the predicate at `rationalOpen D.T D.s` is dischargeable directly
from T058's image theorem. The remaining per-piece subset and Laurent
cover hypotheses become **σ-free** in `t`-indexed form.

This eliminates the "alignment" sub-residual flagged in T058's
section docstring as the only theorem-level gap beyond T058 for the
C1 supplier closure.

## Notes

* No root import; leaf-level file.
* Imports `WedhornPerPieceLaurentCoverAssembly` (T058 / T057), which
  transitively brings in T053 / T054.
* No edits to T031–T061 accepted leaves, root imports, or final
  theorem signatures.
* Disjoint write set from `WedhornPerPieceLaurentC1Supplier.lean` (T056),
  `WedhornPerPieceLaurentCoverAssembly.lean` (T057 / T058),
  `WedhornC1CoverAssemblyClosure.lean` (T060), and
  `WedhornTateAcyclicityFinalClosure.lean` (T061).
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32 / Jacobson, faithful-flatness, Zavyalov, global universal
  Spa bound, or bivariate-overlap content.
* All declarations are fully proven, depend only on the standard Lean
  kernel postulates, and avoid native compilation and unchecked
  tactics.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **Anti-monotonicity of `rationalOpen` in the test family `T`** (T062
reusable primitive).

If `T₁ ⊆ T₂` then `rationalOpen T₂ s ⊆ rationalOpen T₁ s`: more test
elements carve out a smaller rational subset (the constraints
`v.vle t s` for `t ∈ T₂` are more restrictive than for `t ∈ T₁`).

Mathlib-style primitive — fully general, no algebraic structure beyond
the ambient `CommRing A` setting (and the `Spv A` typeclass available
implicitly). -/
theorem rationalOpen_anti_mono_T
    {T₁ T₂ : Finset A} (s : A) (h : T₁ ⊆ T₂) :
    rationalOpen T₂ s ⊆ rationalOpen T₁ s := by
  intro w ⟨hw_spa, hw_T₂, hw_s⟩
  exact ⟨hw_spa, fun t ht ↦ hw_T₂ t (h ht), hw_s⟩

omit [IsTopologicalRing A] in
/-- **Monotonicity of `LaurentCoverPresheafLemma833Assembly` in the
target `R_target`** (T062 reusable primitive).

If the predicate holds for `R_target_inner` and `R_target_inner ⊆
R_target_outer`, then the predicate holds for `R_target_outer`. Direct
consequence of pointwise membership. -/
theorem LaurentCoverPresheafLemma833Assembly_mono_target
    {σ : Aˣ} {T_test : Finset A} {R : A → Set (Spv A)}
    {R_target_inner R_target_outer : Set (Spv A)}
    (h_target : R_target_inner ⊆ R_target_outer)
    (h_pred :
      LaurentCoverPresheafLemma833Assembly
        (σ := σ) T_test R R_target_inner) :
    LaurentCoverPresheafLemma833Assembly
      (σ := σ) T_test R R_target_outer := by
  intro w hw_spa hw_cover hw_per_piece
  exact h_target (h_pred w hw_spa hw_cover hw_per_piece)

omit [IsTopologicalRing A] in
/-- **Main alignment bridge: subset alignment ⇒ predicate at C1 target**
(T062 main deliverable).

If `D_T ⊆ T_test.image (σ⁻¹ * ·)`, the structured Lemma 8.33 predicate
holds at the actual C1 target `rationalOpen D_T D_s`. Composes T058's
σ-rescaled-image discharge with the
`rationalOpen`-anti-monotonicity-in-`T` step.

**Mathematical content**: the σ-rescaled image target is the strongest
target T058 directly proves; smaller `D_T` subsets give weaker (larger
RHS) targets that follow by anti-monotonicity. The supplier-natural
choice `T_test := D_T.image (σ * ·)` makes the alignment exact (see
`LaurentCoverPresheafLemma833Assembly_via_sigma_shift` below). -/
theorem LaurentCoverPresheafLemma833Assembly_via_subset_alignment
    [DecidableEq A]
    {σ : Aˣ} (T_test : Finset A) (D_T : Finset A) (D_s : A)
    (h_align :
      D_T ⊆ T_test.image (fun τ ↦ ((σ⁻¹ : Aˣ) : A) * τ)) :
    LaurentCoverPresheafLemma833Assembly (σ := σ) T_test
      (fun τ ↦ rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
      (rationalOpen D_T D_s) :=
  LaurentCoverPresheafLemma833Assembly_mono_target
    (rationalOpen_anti_mono_T D_s h_align)
    (laurentCoverPresheafLemma833Assembly_via_sigma_rescaled_image
      T_test D_s)

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **σ-shifted image cancellation lemma** (T062 supplier-natural
choice).

For any `σ : Aˣ` and `D_T : Finset A`, the σ-shifted image
`D_T.image (σ * ·)` and the σ-rescaled-image operation
`(·.image (σ⁻¹ * ·))` are inverse: `(D_T.image (σ * ·)).image
(σ⁻¹ * ·) = D_T`.

Direct consequence of `σ⁻¹ * (σ * t) = t`. Reusable primitive — used
to instantiate the alignment bridge with the supplier-natural T_test
choice. -/
theorem image_sigma_inv_image_sigma_eq_self
    [DecidableEq A]
    (σ : Aˣ) (D_T : Finset A) :
    (D_T.image (fun t ↦ (σ : A) * t)).image
        (fun τ ↦ ((σ⁻¹ : Aˣ) : A) * τ) = D_T := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨τ, ⟨t, ht, hτ_eq⟩, hx_eq⟩
    have h_cancel : ((σ⁻¹ : Aˣ) : A) * ((σ : A) * t) = t := by
      rw [← mul_assoc]
      simp
    rw [← hτ_eq, h_cancel] at hx_eq
    exact hx_eq ▸ ht
  · intro hx_in
    refine ⟨(σ : A) * x, ⟨x, hx_in, rfl⟩, ?_⟩
    rw [← mul_assoc]
    simp

omit [IsTopologicalRing A] in
/-- **Canonical exact-alignment discharge via σ-shifted T_test** (T062
substantive theorem).

For the supplier-natural choice `T_test := D_T.image (σ * ·)`, the
alignment is **exact** (T_test.image (σ⁻¹ * ·) = D_T), and the
structured Lemma 8.33 predicate holds at the actual C1 target
`rationalOpen D_T D_s` **unconditionally** — no external alignment
hypothesis required.

**This is the cleanest discharge for the C1 supplier's actual target**:
the supplier picks `T_test := D_T.image (σ * ·)` (with σ the
σ-strict-domination unit), and this theorem closes the Lemma 8.33
predicate at `rationalOpen D_T D_s` without any further assumptions. -/
theorem LaurentCoverPresheafLemma833Assembly_via_sigma_shift
    [DecidableEq A]
    {σ : Aˣ} (D_T : Finset A) (D_s : A) :
    LaurentCoverPresheafLemma833Assembly (σ := σ)
      (D_T.image (fun t ↦ (σ : A) * t))
      (fun τ ↦ rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
      (rationalOpen D_T D_s) := by
  refine LaurentCoverPresheafLemma833Assembly_via_subset_alignment
    (D_T.image (fun t ↦ (σ : A) * t)) D_T D_s ?_
  rw [image_sigma_inv_image_sigma_eq_self]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **σ-shifted image membership cancellation** (T062 helper).

For `τ ∈ D_T.image (σ * ·)`, we have `((σ⁻¹ : Aˣ) : A) * τ ∈ D_T`,
i.e., `σ⁻¹ * τ` cancels back to a member of `D_T`. -/
theorem sigma_inv_mem_of_mem_sigma_image
    [DecidableEq A]
    {σ : Aˣ} {D_T : Finset A} {τ : A}
    (hτ : τ ∈ D_T.image (fun t ↦ (σ : A) * t)) :
    ((σ⁻¹ : Aˣ) : A) * τ ∈ D_T := by
  obtain ⟨t, ht, hτ_eq⟩ := Finset.mem_image.mp hτ
  have h_cancel : ((σ⁻¹ : Aˣ) : A) * ((σ : A) * t) = t := by
    rw [← mul_assoc]
    simp
  rw [← hτ_eq, h_cancel]
  exact ht

omit [IsTopologicalRing A] in
/-- **Clean t-indexed C1 supplier consumer** (T062 end-to-end consumer).

End-to-end consumer for the C1 supplier's clause 2 conclusion using the
supplier-natural σ-shifted T_test choice. The user-facing inputs are
**purely t-indexed over D_T** (no σ-rescaling visible):

* per-piece subsets `rationalOpen (insert f T_base) s ∩ rationalOpen
  ({1}) t ⊆ rationalOpen ({t}) D_s` for each `t ∈ D_T`,
* a Laurent cover hypothesis `∀ w ∈ rationalOpen (insert f T_base) s,
  ∃ t ∈ D_T, w ∈ rationalOpen ({1}) t`.

**Output**: the C1 supplier's clause 2 conclusion `rationalOpen
(insert f T_base) s ⊆ rationalOpen D_T D_s`.

**Internal mechanism**: chooses `T_test := D_T.image (σ * ·)` and
applies T058's image-target discharge via the exact-alignment bridge
(`LaurentCoverPresheafLemma833Assembly_via_sigma_shift`), then T057's
`rationalOpen_global_subset_via_lemma833_assembly` consumer. The σ
appears only in the internal T_test choice; the user supplies σ-free
data over `D_T`.

**Significance**: removes the alignment sub-residual flagged in T058's
section docstring. The C1 supplier's clause 2 closure is now fully
unconditional given Cor 7.32 σ-strict-domination and per-piece
source-restricted bounds — no remaining theorem-level gap at this
layer. -/
theorem rationalOpen_global_subset_via_sigma_shift_t_indexed
    [DecidableEq A]
    (σ : Aˣ) (D_T : Finset A) (T_base : Finset A) (s D_s f : A)
    (h_per_piece_subset :
      ∀ t ∈ D_T,
        rationalOpen (insert f T_base) s ∩
            rationalOpen ({(1 : A)} : Finset A) t ⊆
          rationalOpen ({t} : Finset A) D_s)
    (h_cover :
      ∀ w ∈ rationalOpen (insert f T_base) s,
        ∃ t ∈ D_T,
          w ∈ rationalOpen ({(1 : A)} : Finset A) t) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen D_T D_s := by
  -- Cancellation helper: for τ = σ * t with t ∈ D_T, σ⁻¹ * τ = t.
  have h_cancel : ∀ t : A, ((σ⁻¹ : Aˣ) : A) * ((σ : A) * t) = t := by
    intro t
    rw [← mul_assoc]
    simp
  -- Translate per-piece data from t-indexed to τ-indexed.
  have h_per_piece_τ :
      ∀ τ ∈ D_T.image (fun t ↦ (σ : A) * t),
        rationalOpen (insert f T_base) s ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          rationalOpen
            ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s := by
    intro τ hτ
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hτ
    rw [h_cancel]
    exact h_per_piece_subset t ht
  -- Translate cover hypothesis from t-indexed to τ-indexed.
  have h_cover_τ :
      ∀ w ∈ rationalOpen (insert f T_base) s,
        ∃ τ ∈ D_T.image (fun t ↦ (σ : A) * t),
          w ∈ rationalOpen ({(1 : A)} : Finset A)
            (((σ⁻¹ : Aˣ) : A) * τ) := by
    intro w hw
    obtain ⟨t, ht, hw_in⟩ := h_cover w hw
    refine ⟨(σ : A) * t, Finset.mem_image_of_mem _ ht, ?_⟩
    rw [h_cancel]
    exact hw_in
  -- Apply T057's consumer with the σ-shifted Lemma 8.33 discharge.
  exact rationalOpen_global_subset_via_lemma833_assembly
    (D_T.image (fun t ↦ (σ : A) * t)) T_base D_T s D_s f
    (LaurentCoverPresheafLemma833Assembly_via_sigma_shift D_T D_s)
    h_per_piece_τ h_cover_τ

omit [IsTopologicalRing A] in
/-- **Localized test family ↔ σ-rescaled image bridge**
(T062 ticket-named theorem).

The actual C1 supplier on the localized base typically uses the test
family
`T_test := localizedTestFamily s T_D s_D
  = insert (algebraMap s_D) (T_D.image algebraMap)`
on `Localization.Away s`. The supplier-natural σ-shifted choice is
`T_test_shifted := (T_D.image (algebraMap A (Localization.Away s))).image
  (σ_loc * ·)`.

This bridge connects the two: when the supplier substitutes
`T_test_shifted` for `localizedTestFamily ...` in the Lemma 8.33
predicate input, the alignment is exact and the predicate discharges
unconditionally. The substitution is theorem-level (it changes the
predicate's `T_test` parameter); callers redirecting from
`localizedTestFamily ...` to `T_test_shifted` use the σ-shifted
discharge below.

Stated abstractly on the ambient `A` here (the supplier instantiates
`A := Localization.Away s` with the localization-side topology and
plus-subring at the call site). The conclusion: at the σ-shifted
choice, the structured Lemma 8.33 predicate holds at the actual C1
cover-piece denominator target `rationalOpen (T_D.image algebraMap)
D_s`. -/
theorem localizedTestFamily_sigma_rescaled_image_bridge
    [DecidableEq A]
    {σ_loc : Aˣ} (T_D_loc : Finset A) (D_s : A) :
    LaurentCoverPresheafLemma833Assembly (σ := σ_loc)
      (T_D_loc.image (fun τ ↦ (σ_loc : A) * τ))
      (fun τ ↦
        rationalOpen
          ({((σ_loc⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
      (rationalOpen T_D_loc D_s) :=
  LaurentCoverPresheafLemma833Assembly_via_sigma_shift T_D_loc D_s

/-! ### Threading the actual `localizedTestFamily s T_D s_D` target

The C1 supplier chain on the localized base operates on
`Localization.Away s` with the canonical test family
`localizedTestFamily s T_D s_D
  := insert (algebraMap s_D) (T_D.image algebraMap)`
defined in `WedhornLocalCompatFromTestFamily`. The σ-shift discharge of
this file is fully general in `D_T : Finset A`, so instantiating
`A := Localization.Away s` and `D_T := localizedTestFamily s T_D s_D`
gives the predicate at the **actual** C1 cover-piece denominator
target `rationalOpen (localizedTestFamily s T_D s_D) D_s`
unconditionally.

This section lands the explicit named bridges threading
`localizedTestFamily` so the C1 supplier consumer reads off the
discharge at the actual target without the abstract-`D_T`
instantiation step. Three theorems:

* `image_sigma_image_sigma_inv_localizedTestFamily` — supplier-natural
  σ-shift cancellation specialised to `localizedTestFamily s T_D s_D`:
  `((localizedTestFamily ...).image (σ_loc * ·)).image (σ_loc⁻¹ * ·)
    = localizedTestFamily ...`. Direct instance of
  `image_sigma_inv_image_sigma_eq_self`; named for the localized case
  because the subsequent bridge theorem references this identity in
  its docstring as the structural reason the alignment is exact.

* `LaurentCoverPresheafLemma833Assembly_at_localizedTestFamily` —
  σ-shift exact-alignment discharge at the actual `localizedTestFamily`
  target. For `T_test := (localizedTestFamily s T_D s_D).image
  (σ_loc * ·)`, the structured Lemma 8.33 predicate holds at
  `rationalOpen (localizedTestFamily s T_D s_D) D_s` unconditionally.
  Direct instance of `LaurentCoverPresheafLemma833Assembly_via_sigma_shift`.

* `rationalOpen_global_subset_at_localizedTestFamily_via_sigma_shift_t_indexed`
  — clean σ-free t-indexed consumer at the actual `localizedTestFamily`
  target: from per-piece subsets and a t-indexed Laurent cover over
  `localizedTestFamily s T_D s_D` (no σ-rescaling visible), derive the
  C1 supplier's clause 2 conclusion
  `rationalOpen (insert f_loc T_base_loc) s_base_loc ⊆
    rationalOpen (localizedTestFamily s T_D s_D) D_s`.

These three theorems make the `localizedTestFamily ↔ σ-rescaled image
alignment` content of T062 visible at the actual C1 supplier call
shape on `Localization.Away s`. The σ_loc and per-piece data are
supplied externally (typically from
`exists_dominating_unit_in_localization` for σ_loc and from
`per_piece_singleton_subset_via_laurent_membership` for per-piece
subsets); this file's job is the **alignment**, not the supplier
discharge.
-/

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **σ-shift cancellation specialised to `localizedTestFamily`** (T062
localized-side reusable primitive).

For any `s : A`, `T_D : Finset A`, `s_D : A`, and `σ_loc :
(Localization.Away s)ˣ`:
```
((localizedTestFamily s T_D s_D).image (σ_loc * ·)).image
  (σ_loc⁻¹ * ·) = localizedTestFamily s T_D s_D
```

Direct instance of the abstract `image_sigma_inv_image_sigma_eq_self`,
named for the localized case because the C1 supplier's σ-shifted
T_test choice is precisely `(localizedTestFamily ...).image (σ_loc *
·)`, and this identity is the structural reason the alignment with
the σ-rescaled image at `localizedTestFamily ...` is **exact** (not
merely a subset). -/
theorem image_sigma_image_sigma_inv_localizedTestFamily
    (s : A) (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ((localizedTestFamily s T_D s_D).image
        (fun t ↦ (σ_loc : Localization.Away s) * t)).image
        (fun τ ↦ ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
          Localization.Away s) * τ) =
      localizedTestFamily s T_D s_D := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  exact image_sigma_inv_image_sigma_eq_self σ_loc
    (localizedTestFamily s T_D s_D)

omit [PlusSubring A] in
/-- **σ-shift exact-alignment discharge at `localizedTestFamily`** (T062
ticket-named bridge theorem).

For the supplier-natural σ-shifted choice
`T_test := (localizedTestFamily s T_D s_D).image (σ_loc * ·)`, the
structured Lemma 8.33 multi-piece cover-acyclicity collapse predicate
holds at the **actual C1 cover-piece denominator target**
`rationalOpen (localizedTestFamily s T_D s_D) D_s` unconditionally.

**Why this is the right target**: the C1 supplier's clause 2
conclusion on the localized base is at `rationalOpen
(localizedTestFamily s T_D s_D) D_s`, which is the canonical
`rationalOpen` for the test family
`insert (algebraMap s_D) (T_D.image algebraMap)` on
`Localization.Away s`. The σ-shift discharge applied with `D_T :=
localizedTestFamily s T_D s_D` (and `A := Localization.Away s`)
yields the predicate exactly at this target — completing the
theorem-level bridge from T058's σ-rescaled image discharge to the
actual C1 cover-piece denominator target.

**Mechanism**: the σ-shift discharge
`LaurentCoverPresheafLemma833Assembly_via_sigma_shift D_T D_s` is
fully general in `D_T`. Specialising `D_T := localizedTestFamily s T_D
s_D` gives the predicate at `rationalOpen (localizedTestFamily ...)
D_s` directly. The σ-shift cancellation
`image_sigma_image_sigma_inv_localizedTestFamily` is the structural
identity behind this exact-alignment.

The `letI` block sets up the localization-side topology / plus-
subring / `DecidableEq` instances needed for `Spa (Localization.Away
s) (Localization.Away s)⁺` and `Finset.image` to typecheck. -/
theorem LaurentCoverPresheafLemma833Assembly_at_localizedTestFamily
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) (D_s : Localization.Away s)
    (σ_loc : (Localization.Away s)ˣ) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    LaurentCoverPresheafLemma833Assembly (σ := σ_loc)
      ((localizedTestFamily s T_D s_D).image
        (fun t ↦ (σ_loc : Localization.Away s) * t))
      (fun τ ↦
        rationalOpen
          ({((σ_loc⁻¹ : (Localization.Away s)ˣ) :
            Localization.Away s) * τ} :
            Finset (Localization.Away s)) D_s)
      (rationalOpen (localizedTestFamily s T_D s_D) D_s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  exact LaurentCoverPresheafLemma833Assembly_via_sigma_shift
    (localizedTestFamily s T_D s_D) D_s

omit [PlusSubring A] in
/-- **Clean σ-free t-indexed consumer at the actual `localizedTestFamily`
target** (T062 end-to-end localized C1 consumer).

End-to-end consumer for the C1 supplier's clause 2 conclusion at the
actual `localizedTestFamily ...` target on the localized base. The
user-facing inputs are **purely t-indexed over `localizedTestFamily s
T_D s_D`** (no σ-rescaling visible):

* per-piece subsets `R(insert f_loc T_base_loc, s_base_loc) ∩
  R({1}, t) ⊆ R({t}, D_s)` for each `t ∈ localizedTestFamily s T_D
  s_D`,
* a Laurent cover hypothesis
  `∀ w ∈ R(insert f_loc T_base_loc, s_base_loc),
    ∃ t ∈ localizedTestFamily s T_D s_D, w ∈ R({1}, t)`.

**Output**: `R(insert f_loc T_base_loc, s_base_loc) ⊆
R(localizedTestFamily s T_D s_D, D_s)` — the C1 supplier's clause 2
conclusion at the actual cover-piece denominator target.

**Internal mechanism**: the σ_loc enters only via
`rationalOpen_global_subset_via_sigma_shift_t_indexed`'s internal
σ-shift; the user supplies σ-free t-indexed data over the actual
`localizedTestFamily ...` target. Composes T062's
`rationalOpen_global_subset_via_sigma_shift_t_indexed` with the
specialisation to `D_T := localizedTestFamily s T_D s_D` (and `A :=
Localization.Away s`).

**Significance**: makes the σ-rescaled-image ↔ `localizedTestFamily`
alignment explicit at the localized C1 call site. Callers wanting
the C1 supplier's clause 2 conclusion at the actual `localizedTestFamily
...` target plug their σ-free t-indexed data directly into this
theorem; the alignment is consumed internally.

**Note on cover hypothesis source**: this theorem's user-facing cover
hypothesis is `∀ w, ∃ t ∈ localizedTestFamily ..., w ∈ R({1}) t` —
**not** the σ_loc⁻¹-rescaled form
`∀ w, ∃ τ ∈ localizedTestFamily ..., w ∈ R({1}) (σ_loc⁻¹ * τ)`
delivered by `cor732_laurent_piece_membership_at`. The two cover
shapes correspond to two different `D_T` instantiations of the
σ-shift discharge: this theorem instantiates `D_T :=
localizedTestFamily s T_D s_D` directly, whereas
`rationalOpen_global_subset_via_localizedCor732_sigma_supplier`
instantiates `D_T := (localizedTestFamily ...).image (σ_loc⁻¹ * ·)`
to match Cor 7.32's σ-rescaled output. Both are valid bridges; this
theorem is the one whose conclusion target is exactly
`localizedTestFamily ...` (i.e., the target the user sees as "the
actual localized target"). -/
theorem rationalOpen_global_subset_at_localizedTestFamily_via_sigma_shift_t_indexed
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) (D_s : Localization.Away s)
    (σ_loc : (Localization.Away s)ˣ)
    (T_base_loc : Finset (Localization.Away s))
    (s_base_loc f_loc : Localization.Away s)
    (h_per_piece :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t ∈ localizedTestFamily s T_D s_D,
        rationalOpen (insert f_loc T_base_loc) s_base_loc ∩
            rationalOpen ({(1 : Localization.Away s)} :
              Finset (Localization.Away s)) t ⊆
          rationalOpen ({t} : Finset (Localization.Away s)) D_s)
    (h_cover :
      letI : TopologicalSpace (Localization.Away s) :=
        locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ rationalOpen (insert f_loc T_base_loc) s_base_loc,
        ∃ t ∈ localizedTestFamily s T_D s_D,
          w ∈ rationalOpen ({(1 : Localization.Away s)} :
            Finset (Localization.Away s)) t) :
    letI : TopologicalSpace (Localization.Away s) :=
      locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    rationalOpen (insert f_loc T_base_loc) s_base_loc ⊆
      rationalOpen (localizedTestFamily s T_D s_D) D_s := by
  letI : TopologicalSpace (Localization.Away s) :=
    locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  exact rationalOpen_global_subset_via_sigma_shift_t_indexed σ_loc
    (localizedTestFamily s T_D s_D) T_base_loc s_base_loc D_s f_loc
    h_per_piece h_cover

end ValuationSpectrum
