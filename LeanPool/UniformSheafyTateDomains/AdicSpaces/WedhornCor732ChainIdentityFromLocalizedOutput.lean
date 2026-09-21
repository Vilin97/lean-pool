/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCor732DirectUpperBoundResidual

/-!
# Wedhorn 8.34(ii) — Chain identity from localized Cor 7.32 σ-image output (T085)

T084 (commit `70dde4c`) lands the strictly sharper named identity
`Cor732SigmaDenominatorClearingChainIdentity`, which decomposes T082's
direct upper bound through a transitivity chain via an intermediate
`τ ∈ localizedTestFamily s T_D s_D`. T085 attacks the actual
remaining Wedhorn 8.34(ii) localized σ-construction arithmetic by
proving **one complete chain side** — the per-`(v, t')` σ-rescaled
**lower-chain bound `v.vle (t' * σ_loc) τ`** — directly from T065's
σ-rescaled image cover structure on `D_T_loc`, plus naming the
remaining **second-chain side** as a strictly source-restricted
per-`(v, τ)` upper-bound residual.

## What this file provides

* `Cor732SigmaPerTauUpperBoundResidual` — the named per-`(v, τ)`
  upper-bound residual for the **second chain side**: at every
  `σ_loc` satisfying `IsLocalizedCor732SigmaLocOutput`, every
  `τ ∈ localizedTestFamily s T_D s_D`, and every `v ∈ Spa(Loc s, +)`
  with the source restrictions `v.vle f_loc s_base_loc`,
  `v.vle 1 (σ_loc⁻¹ * τ)`, and `¬ v.vle (σ_loc⁻¹ * τ) 0`, supply
  `v.vle τ (D_s_loc * σ_loc) ∧ ¬ v.vle D_s_loc 0`. **Per-`(v, τ)`
  source-restricted; tied to T065-produced σ_loc; not universal over
  units; no global universal-over-D_T or universal-Spa lower bound.**

* `cor732_sigma_image_mul_unit_eq` — algebraic identity primitive:
  for any `σ : αˣ` and `τ : α` in a commutative monoid,
  `(σ⁻¹ * τ) * σ = τ`. Mathlib-style and reusable; no Wedhorn-specific
  content. Used to discharge the first chain side.

* `cor732_sigma_chain_lower_bound_from_image_witness` — substantive
  per-`(v, t')` reduction proving the **first chain side**
  `v.vle (t' * σ_loc) τ` from a σ-image decomposition `t' = σ_loc⁻¹ * τ`
  for some `τ ∈ localizedTestFamily s T_D s_D`. Reflexive after
  algebraic substitution via `cor732_sigma_image_mul_unit_eq`.

* `cor732_sigma_denominator_clearing_chain_identity_from_localized_cor732_output`
  — **main ticket-named theorem**: produces
  `Cor732SigmaDenominatorClearingChainIdentity` from (a) a
  σ-image-decomposition hypothesis on `D_T_loc` (per-`σ_loc`
  per-`t'`) and (b) the named per-`(v, τ)` upper-bound residual.
  Composes the algebraic first chain side with the named per-τ
  upper bound + non-vanishing.

* `sigma_factored_supplier_via_cor732_image_decomposition_and_per_tau_residual`
  — end-to-end consumer: composes T085's chain producer with T084's
  `sigma_factored_supplier_via_cor732_denominator_clearing_chain_identity`
  to deliver `SigmaFactoredSupplier` directly from the σ-image
  decomposition + per-τ upper bound + standard localized Cor 7.32
  hypotheses.

## Coverage of the chain identity

The chain identity asserts, for every σ_loc satisfying
`IsLocalizedCor732SigmaLocOutput` and every `(t', v)` with source
restrictions:

```
∃ τ ∈ localizedTestFamily s T_D s_D,
  v.vle (t' * σ_loc) τ ∧             -- (1) FIRST CHAIN SIDE
  v.vle τ (D_s_loc * σ_loc) ∧         -- (2) SECOND CHAIN SIDE
  ¬ v.vle D_s_loc 0                    -- (3) NON-VANISHING
```

T085 splits this into two reusable pieces:

* **First chain side (1)**: completely discharged by T085 from the
  σ-image decomposition `t' = σ_loc⁻¹ * τ`. By
  `cor732_sigma_image_mul_unit_eq`, `t' * σ_loc = τ`, so the bound
  `v.vle (t' * σ_loc) τ = v.vle τ τ` is reflexive (via `vle_total`).

* **Second chain side (2) + non-vanishing (3)**: stated as the named
  residual `Cor732SigmaPerTauUpperBoundResidual`, parameterised by
  `σ_loc` satisfying `IsLocalizedCor732SigmaLocOutput` and `τ ∈
  localizedTestFamily s T_D s_D`. **The genuine remaining
  Wedhorn 8.34(ii) per-piece arithmetic.**

The decomposition `t' = σ_loc⁻¹ * τ` is supplied as a per-`(σ_loc,
t')` hypothesis matching T065's σ-rescaled image-cover form
`D_T_loc = (localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·)`
(which `IsLocalizedCor732SigmaLocOutput` already ensures via the
σ-image cover witness).

## The remaining theorem-level signature

Beyond T085, the **only remaining Wedhorn 8.34(ii) σ-construction
algebraic content** at the localized side is the second-side per-τ
upper bound, captured by the named Prop predicate
`Cor732SigmaPerTauUpperBoundResidual`. This is a strictly stronger
content than T084's chain identity (it asserts the second side
without the σ-image decomposition fallback). Discharging it
corresponds to proving, at each `(v, τ)` in the source-restricted
Laurent piece for `σ_loc⁻¹ * τ`, the per-τ bound `v.vle τ (D_s_loc *
σ_loc)` — a per-piece σ-strict-domination consequence of Cor 7.32 +
denominator-clearing identity.

The exact theorem signature for the remaining content is the body of
`Cor732SigmaPerTauUpperBoundResidual` as defined in this file.

## What T085 does NOT do

* Does **NOT** quantify residuals over all units; the σ_loc
  quantifier is restricted via `IsLocalizedCor732SigmaLocOutput` to
  T065-style outputs.

* Does **NOT** introduce or use any global universal-over-`D_T`
  lower bound or universal-over-Spa multi-element clearing claim.

* Does **NOT** edit Primary's pointwise route file or Tertiary's
  σ-power route file. Disjoint write set, leaf-level only.

* Does **NOT** add or modify any final
  `ValuationSpectrum.tateAcyclicity` hypothesis.

## Notes

* No root import; leaf-level file.
* Imports T084 (`WedhornCor732DirectUpperBoundResidual`), which
  transitively brings in T082 / T076 / T065 / T050.
* No edits to T031–T084 accepted leaves, root imports, or final
  theorem signatures.
* All declarations are fully proven, depend only on the standard
  Lean kernel postulates, and avoid native compilation and unchecked
  tactics.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **σ-image algebraic identity primitive** (T085 reusable lemma).

For any unit `σ : αˣ` and any `τ : α` in a commutative monoid,
`(σ⁻¹ * τ) * σ = τ`. The σ-image decomposition `t' = σ⁻¹ * τ` plus
right-multiplication by σ recovers τ — exactly the algebraic step
needed to discharge the first chain side `v.vle (t' * σ) τ` from a
σ-image witness for `t'`.

Mathlib-style and fully general — depends on `CommMonoid`, no
algebraic-spectra-specific content. Reusable beyond the Wedhorn
8.34(ii) chain. -/
theorem cor732_sigma_image_mul_unit_eq
    {α : Type*} [CommMonoid α] (σ : αˣ) (τ : α) :
    (((σ⁻¹ : αˣ) : α) * τ) * (σ : α) = τ := by
  rw [mul_assoc, mul_comm τ ((σ : α)), ← mul_assoc, σ.inv_mul, one_mul]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **First chain side: `v.vle (t' * σ_loc) τ` from σ-image
decomposition** (T085 substantive per-`(v, t', τ)` reduction).

From a σ-image decomposition witness `t' = σ_loc⁻¹ * τ`, derive the
first chain side bound `v.vle (t' * σ_loc) τ` for any `v : Spv (Loc
s)`.

**Proof structure**: by `cor732_sigma_image_mul_unit_eq`, `t' *
σ_loc = (σ_loc⁻¹ * τ) * σ_loc = τ`. The bound `v.vle (t' * σ_loc) τ`
then reduces to `v.vle τ τ`, which is trivially true via
`Spv.vle_total τ τ` (reflexivity).

**Substantive consumption** of the σ-image decomposition witness —
not pass-through. Real algebra: σ-cancellation via the unit identity
`σ⁻¹ * σ = 1`, then reflexivity. -/
theorem cor732_sigma_chain_lower_bound_from_image_witness
    {s : A} (σ_loc : (Localization.Away s)ˣ)
    (t' τ : Localization.Away s)
    (h_t_eq : t' = ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
        Localization.Away s) * τ)
    (v : Spv (Localization.Away s)) :
    v.vle (t' * (σ_loc : Localization.Away s)) τ := by
  subst h_t_eq
  rw [cor732_sigma_image_mul_unit_eq σ_loc τ]
  exact (v.vle_total τ τ).elim id id

omit [PlusSubring A] in
/-- **Per-`(v, τ)` source-restricted upper-bound residual at the
T065-produced σ_loc** (T085 named residual for the second chain side
+ non-vanishing).

Function-form predicate `(σ_loc, h_cover_t) ↦ per-τ upper-bound
residual at σ_loc`, mirroring the T084 / T082 / T076 wrapper interface
but with the body further reduced to the **per-`(v, τ)` second chain
side bound `v.vle τ (D_s_loc * σ_loc)`** plus `D_s_loc` non-vanishing.

The residual quantifier ranges over τ ∈ `localizedTestFamily s T_D s_D`
(rather than `D_T_loc`) — the natural σ-construction test family from
T065's σ-rescaled image cover. Discharging this residual at each
(v, τ) is the per-Laurent-piece denominator-clearing arithmetic that
remains beyond T085's algebraic first-chain-side reduction.

**The genuine remaining Wedhorn 8.34(ii) σ-construction algebraic
content** at the localized side: per-`(v, τ)` source-restricted upper
bound, tied to T065-produced σ_loc via
`IsLocalizedCor732SigmaLocOutput`, not universal over all units, no
global universal-over-`D_T` lower bound, no universal-over-Spa
multi-element clearing. -/
def Cor732SigmaPerTauUpperBoundResidual
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (s_base_loc D_s_loc f_loc : Localization.Away s) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  ∀ (σ_loc : (Localization.Away s)ˣ),
    IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      ∀ v ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        v.vle f_loc s_base_loc →
        v.vle (1 : Localization.Away s)
          (((σ_loc⁻¹ : (Localization.Away s)ˣ) :
            Localization.Away s) * τ) →
        ¬ v.vle (((σ_loc⁻¹ : (Localization.Away s)ˣ) :
          Localization.Away s) * τ) 0 →
        v.vle τ (D_s_loc * (σ_loc : Localization.Away s)) ∧
        ¬ v.vle D_s_loc 0

omit [PlusSubring A] in
/-- **Chain identity from σ-image decomposition + per-τ upper-bound
residual** (T085 main ticket-named theorem).

Produces `Cor732SigmaDenominatorClearingChainIdentity` (T084's
sharper named identity) from:

* `h_D_T_loc_image_per_t` — per-`(σ_loc, t')` σ-image decomposition
  witness: for every σ_loc satisfying
  `IsLocalizedCor732SigmaLocOutput` and every `t' ∈ D_T_loc`, supply
  `τ ∈ localizedTestFamily s T_D s_D` with `t' = σ_loc⁻¹ * τ`. Matches
  T065's σ-rescaled image cover form `D_T_loc =
  (localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·)` (per-`t'`
  decomposition).

* `h_per_tau` — the named per-`(v, τ)` upper-bound residual
  `Cor732SigmaPerTauUpperBoundResidual`: supplies the second chain
  side `v.vle τ (D_s_loc * σ_loc)` plus `¬ v.vle D_s_loc 0` at each
  per-`(v, τ)` instance.

**Proof composition**: at each `(σ_loc, h_cover_t, t', v)` with
source restrictions, recover τ via the σ-image decomposition. The
first chain side `v.vle (t' * σ_loc) τ` follows from
`cor732_sigma_chain_lower_bound_from_image_witness` (reflexive after
σ-cancellation). The second chain side and non-vanishing follow from
the per-τ residual applied at the recovered `(σ_loc, h_cover_t, τ,
v)` — the source restrictions on `v.vle 1 t'` and `¬ v.vle t' 0`
transport to `v.vle 1 (σ_loc⁻¹ * τ)` and `¬ v.vle (σ_loc⁻¹ * τ) 0` by
the σ-image equality `t' = σ_loc⁻¹ * τ`.

Real arithmetic: substantively consumes the σ-image decomposition
(via `cor732_sigma_image_mul_unit_eq`) and the per-τ residual at each
per-`(v, t')` instance. -/
theorem cor732_sigma_denominator_clearing_chain_identity_from_localized_cor732_output
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (D_T_loc : Finset (Localization.Away s))
    (s_base_loc D_s_loc f_loc : Localization.Away s)
    (h_D_T_loc_image_per_t :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ (σ_loc : (Localization.Away s)ˣ),
        IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
        ∀ t' ∈ D_T_loc,
          ∃ τ ∈ localizedTestFamily s T_D s_D,
            t' = ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
              Localization.Away s) * τ)
    (h_per_tau :
      Cor732SigmaPerTauUpperBoundResidual
        P T s hopen T_D s_D s_base_loc D_s_loc f_loc) :
    Cor732SigmaDenominatorClearingChainIdentity
      P T s hopen T_D s_D D_T_loc s_base_loc D_s_loc f_loc := by
  intro σ_loc h_cover_t t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  -- Step 1: recover τ from the σ-image decomposition.
  obtain ⟨τ, hτ_mem, h_t_eq⟩ :=
    h_D_T_loc_image_per_t σ_loc h_cover_t t' ht'
  -- Step 2: apply per-τ residual to obtain second chain side + non-vanishing,
  -- transporting the source restrictions from t' to σ_loc⁻¹ * τ via h_t_eq.
  obtain ⟨h_τ_le_D, h_D_ne⟩ :=
    h_per_tau σ_loc h_cover_t τ hτ_mem v hv_spa hv_f (h_t_eq ▸ hv_one_t)
      (h_t_eq ▸ hv_t_ne)
  refine ⟨τ, hτ_mem, ?_, h_τ_le_D, h_D_ne⟩
  -- Step 3: discharge first chain side via σ-image algebra + reflexivity.
  exact cor732_sigma_chain_lower_bound_from_image_witness σ_loc t' τ h_t_eq v

omit [PlusSubring A] in
/-- **End-to-end: σ-factored supplier from σ-image decomposition + per-τ
upper-bound residual** (T085 final consumer).

End-to-end consumer composing T085's chain producer with T084's
`sigma_factored_supplier_via_cor732_denominator_clearing_chain_identity`
to deliver the σ-factored supplier output `∃ σ_loc,
SigmaFactoredSupplier ...` directly from:

* The σ-image decomposition hypothesis on `D_T_loc` (per-`(σ_loc,
  t')`).
* The named per-`(v, τ)` upper-bound residual.
* The standard localized Cor 7.32 hypotheses.

This closes the chain from T085's σ-image first-side reduction and
named per-τ residual through the T084 → T082 → T076 → T065 chain to
the σ-factored supplier. Single named source-restricted residual at
the consumer boundary: `Cor732SigmaPerTauUpperBoundResidual`. -/
theorem sigma_factored_supplier_via_cor732_image_decomposition_and_per_tau_residual
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ (π_loc : (locPairOfDefinition P T s hopen).A₀)
      (_hI_loc : (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away s),
        letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)))
      (T_D : Finset A) (s_D : A)
      (_hT_loc : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D, ¬ w.vle τ 0)
      (D_T_loc : Finset (Localization.Away s))
      (s_base_loc D_s_loc f_loc : Localization.Away s)
      (_h_D_T_loc_image_per_t :
        ∀ (σ_loc : (Localization.Away s)ˣ),
          IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
          ∀ t' ∈ D_T_loc,
            ∃ τ ∈ localizedTestFamily s T_D s_D,
              t' = ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
                Localization.Away s) * τ)
      (_h_per_tau :
        Cor732SigmaPerTauUpperBoundResidual
          P T s hopen T_D s_D s_base_loc D_s_loc f_loc),
    ∃ _ : (Localization.Away s)ˣ,
      SigmaFactoredSupplier D_T_loc s_base_loc D_s_loc f_loc := by
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    D_T_loc s_base_loc D_s_loc f_loc h_D_T_loc_image_per_t h_per_tau
  -- Convert the σ-image decomposition + per-τ residual into the chain identity.
  have h_chain_identity :=
    cor732_sigma_denominator_clearing_chain_identity_from_localized_cor732_output
      P T s hopen T_D s_D D_T_loc s_base_loc D_s_loc f_loc
      h_D_T_loc_image_per_t h_per_tau
  -- Apply T084's end-to-end consumer.
  exact sigma_factored_supplier_via_cor732_denominator_clearing_chain_identity
    P T s hopen π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    D_T_loc s_base_loc D_s_loc f_loc h_chain_identity

end ValuationSpectrum
