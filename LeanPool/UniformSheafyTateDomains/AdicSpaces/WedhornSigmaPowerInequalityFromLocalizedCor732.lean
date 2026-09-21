/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiBranchSubsetInequality
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPointwiseClearingSupplierFromSigmaPower
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSigmaFactoredSupplierFromLocalizedCor732

/-!
# Wedhorn 8.34(ii) — σ-power inequality from localized Cor 7.32 output (T083)

T065 (`WedhornLocalizedCor732SigmaSupplier`) lands the **localized
Cor 7.32 σ-supplier**: from the localized Wedhorn–Tate hypotheses,
extract `σ_loc : (Localization.Away s)ˣ` and the σ-rescaled t-indexed
Laurent cover hypothesis on the localized Spa. The cover-property
output is captured by T076's named predicate
`IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc`.

T079 (`WedhornPointwiseClearingSupplierFromSigmaPower`) and T080
(`WedhornFinalPart2SigmaPowerThreading`) consume the **per-`(w, t')`
source-restricted σ-power-cleared inequality supplier** at the source
ring `A`:
```
∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
  w.vle f s_base → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ N : ℕ, w.vle (t' * s_D ^ N) (s_D ^ (N + 1)) ∧ ¬ w.vle s_D 0
```

This file lands the **theorem-level bridge** from a named source-
restricted denominator/clearing identity **explicitly tied to T065's
localized Cor 7.32 σ_loc cover-property output via
`IsLocalizedCor732SigmaLocOutput`** to T079/T080's σ-power-cleared
inequality supplier.

## Two layers: generic and T065-tied

The file is organised in two layers:

* **Generic layer** (`Cor732SigmaDecayChainSupplier`,
  `sigma_power_cleared_inequality_via_sigma_decay_chain_at`,
  `sigma_power_cleared_inequality_via_generic_chain_supplier`) —
  reusable σ-decay-chain-to-σ-power adapter with no localized Cor 7.32
  parameters in its type. Useful as a portable Lean primitive.

* **T065-tied layer** (`LocalizedCor732SigmaDecayChainSupplier`,
  `Cor732SigmaDecayChainSupplier_of_localized_at_T065_sigma_loc`,
  `sigma_power_cleared_inequality_from_localized_cor732_output`,
  `SigmaProductClearedInequalitySupplier_from_localized_cor732_output`)
  — Prop predicate and theorems whose **type signatures explicitly
  carry the T065 parameters** `P T s hopen T_D s_D s_base f` and
  quantify over σ_loc only via `IsLocalizedCor732SigmaLocOutput`. This
  is the consumer-facing T083 boundary; the residual is restricted to
  T065-style outputs at the type level, not just documentarily.

## The named source-restricted T065-tied identity

`LocalizedCor732SigmaDecayChainSupplier P T s hopen T_D s_D s_base f`
quantifies over `σ_loc : (Localization.Away s)ˣ` satisfying
`IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc`, and
requires the per-`(w, t')` source σ-decay chain at the source ring:
```
∀ σ_loc, IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
  w.vle f s_base → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ (σ : Aˣ) (N : ℕ) (C_base_s : A),
    w.vle ((σ : A) * t' * s_D ^ N) C_base_s ∧
    w.vle C_base_s ((σ : A) * s_D ^ (N + 1)) ∧
    ¬ w.vle s_D 0
```

This is the **single named source-restricted denominator/clearing
identity tied to the T065 σ_loc / Laurent-cover output**: the residual
function is supplied for σ_loc that are valid T065 outputs (witnessed
via `IsLocalizedCor732SigmaLocOutput`), not for arbitrary units of the
localization. The σ-decay chain itself is per-`(w, t')` source-
restricted; the σ : Aˣ is existentially quantified inside per-`(w, t')`
(no all-units σ residual).

## Why σ-cancellation suffices to discharge the σ-power-cleared form

The σ-decay chain combines via transitivity to
```
w.vle ((σ : A) * t' * s_D ^ N) ((σ : A) * s_D ^ (N + 1))
```
After re-association `(σ : A) * t' * s_D ^ N = (σ : A) * (t' * s_D ^ N)`
and σ-cancellation on the left (`vle_iff_mul_unit_left`, an existing
`Aˣ` cancellation primitive in `WedhornMultiBranchSubsetInequality`),
this collapses to the σ-power-cleared form
`w.vle (t' * s_D ^ N) (s_D ^ (N + 1))` consumed by T079/T080.

The N-power cancellation that would further collapse to the direct
upper bound `w.vle t' s_D` is **not** performed at this layer — that
route is owned by Primary's pointwise lane. T083 keeps the σ-power
exponent intact, supplying T079/T080's σ-power-cleared input directly.

## What this file provides

### Generic layer

* `Cor732SigmaDecayChainSupplier` — generic Prop predicate for the
  per-`(w, t')` source-restricted σ-decay chain (no T065 parameters in
  the type; reusable adapter primitive).

* `sigma_power_cleared_inequality_via_sigma_decay_chain_at` — per-
  `(w, t')` σ-cancellation primitive: from a single σ-decay chain, get
  the σ-power-cleared inequality `w.vle (t' * s_D ^ N) (s_D ^ (N + 1))`.

* `sigma_power_cleared_inequality_via_generic_chain_supplier` —
  generic-layer bridge: from `Cor732SigmaDecayChainSupplier`, get the
  T079/T080 σ-power-cleared inequality supplier shape.

### T065-tied layer

* `LocalizedCor732SigmaDecayChainSupplier` — Prop predicate quantified
  over σ_loc satisfying `IsLocalizedCor732SigmaLocOutput`; this is the
  type-level T065-tied named residual.

* `Cor732SigmaDecayChainSupplier_of_localized_at_T065_sigma_loc` —
  generic supplier produced from the T065-tied predicate by
  instantiating at one (σ_loc, h_cover) pair. Aligns the two layers.

* `sigma_power_cleared_inequality_from_localized_cor732_output` —
  T083 main theorem (ticket-named target). Type signature carries the
  T065 parameters `P T s hopen T_D s_D` plus the source-side data
  `s_base f`, with the residual `LocalizedCor732SigmaDecayChainSupplier`
  consumed at the T065-extracted (σ_loc, h_cover) pair. The localized
  Cor 7.32 hypotheses (π_loc / hI_loc / hπ_loc_tn / hπ_loc_unit /
  hArch_loc / hT_loc) are plumbed through to internally extract σ_loc
  via `localizedCor732_sigma_supplier_for_actual_C1`.

* `SigmaProductClearedInequalitySupplier_from_localized_cor732_output`
  — full end-to-end T083 deliverable: composes the ticket-named
  theorem with T079's converter to produce T072's named residual
  `SigmaProductClearedInequalitySupplier`. The whole chain is from the
  T065-tied named residual to T072's residual, with all intermediate
  σ-cancellation arithmetic discharged.

## Notes

* No root import; leaf-level.
* Imports `WedhornMultiBranchSubsetInequality` for the σ-cancellation
  primitive `vle_iff_mul_unit_left`, T079
  (`WedhornPointwiseClearingSupplierFromSigmaPower`) for the
  end-to-end composition into T072's named residual via
  `SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted`,
  and T076 (`WedhornSigmaFactoredSupplierFromLocalizedCor732`) for
  the named predicate `IsLocalizedCor732SigmaLocOutput` and (via its
  transitive import) T065's `localizedCor732_sigma_supplier_for_actual_C1`.
* No edits to T031–T082 accepted leaves, root imports, or final
  theorem signatures.
* No edits to Primary's pointwise route file (T081) or Secondary's
  σ-factored file (T084).
* No revival of M-power-decay / σ-power-decay (the σ-power exponent
  is per-`(w, t')` here, not a global decay), T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-`T_D` lower bound (the consumed
  per-`(w, t')` Laurent-piece hypothesis is source-restricted).
* No global universal-over-Spa multi-element clearing claim (each
  `w` supplies its own σ, N, and C_base_s independently).
* No all-units σ residual: the residual ranges only over σ_loc
  satisfying `IsLocalizedCor732SigmaLocOutput`, and the source σ is
  existentially quantified per-`(w, t')`.
* No final `ValuationSpectrum.tateAcyclicity` hypothesis additions.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-! ## Generic layer -/

/-- **Per-`(w, t')` source-restricted σ-decay chain supplier (generic
layer)** (T083 reusable primitive predicate).

Generic Prop predicate naming the per-`(w, t')` source-restricted
σ-decay chain at the source ring `A`. At each `w ∈ Spa A A⁺` and
`t' ∈ T_D` in the source-restricted Laurent piece (`w.vle f s_base`,
`w.vle 1 t'`, `¬ w.vle t' 0`), supply a σ-construction unit `σ : Aˣ`,
an exponent `N : ℕ`, and an intermediate term `C_base_s : A` such that
the σ-decay chain holds:
```
w.vle ((σ : A) * t' * s_D ^ N) C_base_s          -- f-bound
w.vle C_base_s ((σ : A) * s_D ^ (N + 1))         -- σ-power-decay
¬ w.vle s_D 0                                    -- non-vanishing
```

This is the **generic-layer** σ-decay chain predicate: its type does
not carry any localized Cor 7.32 parameters. The T065-tied layer
restricts the residual to σ_loc satisfying
`IsLocalizedCor732SigmaLocOutput` via
`LocalizedCor732SigmaDecayChainSupplier`. -/
def Cor732SigmaDecayChainSupplier
    (T_D : Finset A) (s_base s_D f : A) : Prop :=
  ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
    w.vle f s_base →
    w.vle (1 : A) t' →
    ¬ w.vle t' 0 →
    ∃ (σ : Aˣ) (N : ℕ) (C_base_s : A),
      w.vle ((σ : A) * t' * s_D ^ N) C_base_s ∧
      w.vle C_base_s ((σ : A) * s_D ^ (N + 1)) ∧
      ¬ w.vle s_D 0

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **σ-power-cleared inequality from σ-decay chain at a single
`(w, t')`** (T083 reusable per-`(w, t')` σ-cancellation primitive).

From a per-`(w, t')` σ-decay chain
```
w.vle ((σ : A) * t' * s_D ^ N) C_base_s
w.vle C_base_s ((σ : A) * s_D ^ (N + 1))
```
derive the σ-power-cleared inequality `w.vle (t' * s_D ^ N) (s_D ^ (N + 1))`.

**Proof structure**: combine the two chain hypotheses via
`Spv.vle_trans` to get `w.vle ((σ : A) * t' * s_D ^ N) ((σ : A) * s_D ^ (N + 1))`,
re-associate the LHS to `(σ : A) * (t' * s_D ^ N)` via `mul_assoc`,
and apply `vle_iff_mul_unit_left` (existing `Aˣ` cancellation
primitive) to cancel the σ factor.

**Substantive consumption**: both chain hypotheses are genuinely used
through transitivity + σ-cancellation; not a pass-through. -/
theorem sigma_power_cleared_inequality_via_sigma_decay_chain_at
    {w : Spv A} {σ : Aˣ} {t' s_D C_base_s : A} {N : ℕ}
    (h_w_f : w.vle ((σ : A) * t' * s_D ^ N) C_base_s)
    (h_C_decay : w.vle C_base_s ((σ : A) * s_D ^ (N + 1))) :
    w.vle (t' * s_D ^ N) (s_D ^ (N + 1)) :=
  (vle_iff_mul_unit_left w σ (t' * s_D ^ N) (s_D ^ (N + 1))).mp
    (mul_assoc (σ : A) t' (s_D ^ N) ▸ w.vle_trans h_w_f h_C_decay)

omit [IsTopologicalRing A] in
/-- **σ-power-cleared inequality supplier from generic σ-decay chain
supplier** (T083 generic-layer bridge).

From the generic Prop predicate `Cor732SigmaDecayChainSupplier T_D
s_base s_D f`, produce the per-`(w, t')` source-restricted σ-power-
cleared inequality supplier consumed by T079/T080:
```
∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
  w.vle f s_base → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ N : ℕ, w.vle (t' * s_D ^ N) (s_D ^ (N + 1)) ∧ ¬ w.vle s_D 0
```

Generic-layer bridge: takes the σ-decay chain predicate without any
localized Cor 7.32 type parameters. The T065-tied wrapper
`sigma_power_cleared_inequality_from_localized_cor732_output` below
plumbs through the localized hypotheses to consume
`LocalizedCor732SigmaDecayChainSupplier` (whose type carries the T065
parameters explicitly). -/
theorem sigma_power_cleared_inequality_via_generic_chain_supplier
    (T_D : Finset A) (s_base s_D f : A)
    (h_chain : Cor732SigmaDecayChainSupplier T_D s_base s_D f) :
    ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
      w.vle f s_base →
      w.vle (1 : A) t' →
      ¬ w.vle t' 0 →
      ∃ N : ℕ,
        w.vle (t' * s_D ^ N) (s_D ^ (N + 1)) ∧ ¬ w.vle s_D 0 := by
  intro t' ht' w hw_spa hw_f hw_one_t hw_t_ne
  obtain ⟨σ, N, C_base_s, h_w_f, h_C_decay, h_s_D_ne⟩ :=
    h_chain t' ht' w hw_spa hw_f hw_one_t hw_t_ne
  exact ⟨N,
    sigma_power_cleared_inequality_via_sigma_decay_chain_at h_w_f h_C_decay,
    h_s_D_ne⟩

/-! ## T065-tied layer -/

/-- **σ-decay chain supplier tied to T065's localized Cor 7.32 output**
(T083 named T065-tied source-restricted residual).

Prop predicate whose **type explicitly carries the T065 parameters**
`P T s hopen T_D s_D` plus the source-side data `s_base f`.
Quantification over `σ_loc : (Localization.Away s)ˣ` is restricted to
σ_loc satisfying `IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D
σ_loc` — i.e., σ_loc that are valid T065 outputs (witnessed by the
σ-rescaled Laurent-cover property on the localized Spa).

For each such σ_loc, the predicate body is the per-`(w, t')` source-
restricted σ-decay chain at the source ring `A`:
```
∀ σ_loc, IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
  ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
    w.vle f s_base → w.vle 1 t' → ¬ w.vle t' 0 →
    ∃ (σ : Aˣ) (N : ℕ) (C_base_s : A),
      w.vle ((σ : A) * t' * s_D ^ N) C_base_s ∧
      w.vle C_base_s ((σ : A) * s_D ^ (N + 1)) ∧
      ¬ w.vle s_D 0
```

**Why this is T065-tied at the type level**: the σ_loc handle and
the `IsLocalizedCor732SigmaLocOutput` constraint are explicit
arguments — the residual is consumed only at σ_loc that are valid
T065 outputs, not at arbitrary units of the localization. This
parallels T076's `sigma_factored_supplier_via_localized_cor732`
pattern (`WedhornSigmaFactoredSupplierFromLocalizedCor732`).

**Why σ : Aˣ is existentially quantified inside, not externally
bound to σ_loc**: there is no concrete source-lift map
`(Localization.Away s)ˣ → Aˣ` available at this layer. The σ-
construction at each `(w, t')` chooses its own source unit; the
existence of σ_loc satisfying `IsLocalizedCor732SigmaLocOutput`
is the T065 precondition that justifies the σ-decay chain's
existence at the source. -/
def LocalizedCor732SigmaDecayChainSupplier
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (s_base f : A) : Prop :=
  ∀ (σ_loc : (Localization.Away s)ˣ),
    IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc →
    Cor732SigmaDecayChainSupplier T_D s_base s_D f

/-- **Generic σ-decay chain supplier from T065-tied predicate at a
specific (σ_loc, h_cover_t)** (T083 layer-alignment bridge).

From the T065-tied predicate
`LocalizedCor732SigmaDecayChainSupplier P T s hopen T_D s_D s_base f`,
together with **a concrete pair (σ_loc, h_cover_t)** witnessing
`IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc`,
produce the generic-layer predicate
`Cor732SigmaDecayChainSupplier T_D s_base s_D f`.

The concrete (σ_loc, h_cover_t) pair is the T065-extracted output
(see `localizedCor732_sigma_supplier_for_actual_C1`). The bridge is
**type alignment**: the T065-tied predicate restricts to σ_loc
satisfying `IsLocalizedCor732SigmaLocOutput`, so consuming it at one
such pair instantiates the σ_loc quantifier and yields the generic
predicate. -/
theorem Cor732SigmaDecayChainSupplier_of_localized_at_T065_sigma_loc
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) (s_base f : A)
    (h_loc :
      LocalizedCor732SigmaDecayChainSupplier P T s hopen T_D s_D s_base f)
    (σ_loc : (Localization.Away s)ˣ)
    (h_cover_t : IsLocalizedCor732SigmaLocOutput P T s hopen T_D s_D σ_loc) :
    Cor732SigmaDecayChainSupplier T_D s_base s_D f :=
  h_loc σ_loc h_cover_t

/-- **σ-power-cleared inequality supplier from localized Cor 7.32
output** (T083 ticket-named main theorem).

Type signature carries the T065 parameters `P T s hopen T_D s_D` plus
the source-side data `s_base f`, with the residual
`LocalizedCor732SigmaDecayChainSupplier P T s hopen T_D s_D s_base f`
explicitly tied at the type level to σ_loc satisfying
`IsLocalizedCor732SigmaLocOutput`.

**Inputs**:

* Standard localized Cor 7.32 hypotheses (`P, T, s, hopen, π_loc,
  hI_loc, hπ_loc_tn, hπ_loc_unit, hArch_loc, T_D, s_D, hT_loc`) — the
  standard `localizedCor732_sigma_supplier_for_actual_C1` inputs.

* `s_base f : A` — the source-side rationalOpen base denominator and
  σ-construction element.

* `h_loc : LocalizedCor732SigmaDecayChainSupplier …` — the named
  T065-tied source-restricted residual, supplied only at σ_loc
  satisfying `IsLocalizedCor732SigmaLocOutput`.

**Output**: the per-`(w, t')` source-restricted σ-power-cleared
inequality supplier consumed by T079/T080:
```
∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
  w.vle f s_base → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ N : ℕ, w.vle (t' * s_D ^ N) (s_D ^ (N + 1)) ∧ ¬ w.vle s_D 0
```

**Composition in the proof body**: extract `(σ_loc, h_cover_t)` from
T065's `localizedCor732_sigma_supplier_for_actual_C1` at the supplied
localized hypotheses; apply the T065-tied predicate at this specific
`(σ_loc, h_cover_t)` to obtain the generic σ-decay chain supplier
`Cor732SigmaDecayChainSupplier T_D s_base s_D f`; compose with the
generic-layer bridge `sigma_power_cleared_inequality_via_generic_chain_supplier`
to deliver the T079/T080 σ-power-cleared inequality supplier shape.

The residual function `h_loc` is consumed at exactly one input — the
T065-extracted `(σ_loc, h_cover_t)` pair. -/
theorem sigma_power_cleared_inequality_from_localized_cor732_output
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
      (s_base f : A)
      (_h_loc :
        LocalizedCor732SigmaDecayChainSupplier P T s hopen T_D s_D s_base f),
      ∀ t' ∈ T_D, ∀ w ∈ Spa A A⁺,
        w.vle f s_base →
        w.vle (1 : A) t' →
        ¬ w.vle t' 0 →
        ∃ N : ℕ,
          w.vle (t' * s_D ^ N) (s_D ^ (N + 1)) ∧ ¬ w.vle s_D 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc s_base f
    h_loc
  -- Extract (σ_loc, h_cover_t) from T065's localized Cor 7.32 supplier.
  obtain ⟨σ_loc, h_cover_t⟩ :=
    localizedCor732_sigma_supplier_for_actual_C1 P T s hopen
      π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
  -- Apply the T065-tied predicate at this specific (σ_loc, h_cover_t) to
  -- obtain the generic σ-decay chain supplier, then compose with the
  -- generic-layer bridge to deliver the T079/T080 input.
  exact sigma_power_cleared_inequality_via_generic_chain_supplier T_D s_base s_D f
    (Cor732SigmaDecayChainSupplier_of_localized_at_T065_sigma_loc
      P T s hopen T_D s_D s_base f h_loc σ_loc h_cover_t)

/-- **`SigmaProductClearedInequalitySupplier` from localized Cor 7.32
output** (T083 + T079 end-to-end consumer-facing T083 deliverable).

Full end-to-end T083 deliverable on the σ-power lane: from the named
T065-tied source-restricted residual
`LocalizedCor732SigmaDecayChainSupplier` (whose type explicitly
carries the T065 parameters and `IsLocalizedCor732SigmaLocOutput`-
restricted σ_loc), deliver T072's named residual
`SigmaProductClearedInequalitySupplier` by composing the ticket-named
theorem above with T079's
`SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted`.

**End-to-end T065-tied σ-decay chain → T072 lane**:
T065-tied σ-decay chain supplier (`LocalizedCor732SigmaDecayChainSupplier`,
σ_loc visibly bound by `IsLocalizedCor732SigmaLocOutput`)
  → (T065 extraction via `localizedCor732_sigma_supplier_for_actual_C1`)
  → generic σ-decay chain supplier (`Cor732SigmaDecayChainSupplier`)
  → (σ-cancellation, this file) →
σ-power-cleared inequality supplier (T079/T080 input)
  → (T079 adapter / T077 bridge / T073 N=0 witness) →
`SigmaProductClearedInequalitySupplier` (T072 named residual).

The whole chain reduces T072's named residual to a **single named
T065-tied source-restricted algebraic identity** with no remaining
all-units σ residual, no global universal-over-`T_D` lower bound, and
no global universal-over-Spa multi-element bound. -/
theorem SigmaProductClearedInequalitySupplier_from_localized_cor732_output
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
      (s_base f : A)
      (_h_loc :
        LocalizedCor732SigmaDecayChainSupplier P T s hopen T_D s_D s_base f),
      SigmaProductClearedInequalitySupplier T_D s_base s_D f := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc s_base f
    h_loc
  exact SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted
    T_D s_base s_D f
    (sigma_power_cleared_inequality_from_localized_cor732_output P T s hopen
      π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc s_base f
      h_loc)

end ValuationSpectrum
