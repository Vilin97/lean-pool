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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732SigmaSupplier
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPointwiseClearingSupplierFromSigmaPower

/-!
# Wedhorn 8.34(ii) — Pointwise clearing supplier from localized Cor 7.32 output (T081)

T065 (`WedhornLocalizedCor732SigmaSupplier`) lands the localized
Cor 7.32 σ-supplier producing `σ_loc : (Localization.Away s)ˣ` and
the **σ-rescaled image cover hypothesis**:

```
∀ w ∈ Spa(Localization.Away s, locSubring P T s),
  ∃ t ∈ (localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·),
    w ∈ rationalOpen ({1} : Finset (Localization.Away s)) t
```

T077 / T078 / T079 consume the **pointwise clearing supplier shape**
(per-`(v, t')`, source-restricted upper bound only) at the consumer
boundary:

```
∀ t' ∈ D_T_loc, ∀ w ∈ Spa A_loc A_loc⁺,
  w.vle f_loc s_base_loc → w.vle (1 : A_loc) t' → ¬ w.vle t' 0 →
  w.vle t' D_s
```

This file lands the **theorem-level bridge** producing the pointwise
clearing supplier shape from T065's σ-image cover output, with the
remaining mathematical content isolated as a single named
**per-τ source-restricted clearing residual** tied to the σ-rescaled
test family.

## What this file provides

* `LocalizedPerTauPointwiseClearingResidual` — Prop predicate naming
  the **per-τ source-restricted clearing residual** at the localized
  side. Captures the σ-construction's per-Laurent-piece algebraic
  identity for `τ ∈ localizedTestFamily s T_D s_D`: at every
  `w ∈ Spa(Loc s, +)` satisfying `f`-membership, Laurent-piece
  membership at `σ_loc⁻¹ * τ`, and `σ_loc⁻¹ * τ` non-vanishing,
  derive `w.vle (σ_loc⁻¹ * τ) D_s`.

* `pointwise_clearing_supplier_from_localized_cor732_output` — the
  **main bridge**: from a `σ_loc` choice and the per-τ source-
  restricted clearing residual, produce the pointwise clearing
  supplier shape consumed by T077 / T078 with `D_T :=
  (localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·)`. The bridge
  is a clean image-finset re-indexing of the residual; T065's σ_loc
  output is consumed mechanically as the σ-construction unit.

* `SigmaProductClearedInequalitySupplier_from_localized_cor732_output_pointwiseClearing`
  — end-to-end direct lane: composes the bridge with T077's
  `SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier`
  to deliver T072's named residual
  `SigmaProductClearedInequalitySupplier` (the C1 sigma-construction
  endgame target) from the same per-τ clearing residual + σ_loc.

## The single source-restricted algebraic residual

After T081, the residual content for the direct (pointwise) lane
reduces to **one named source-restricted algebraic identity** tied to
the T065-produced σ/Laurent-cover output:
`LocalizedPerTauPointwiseClearingResidual`. The residual is **per-`(τ,
w)` source-restricted** — only `τ ∈ localizedTestFamily s T_D s_D`
and the LHS rationalOpen membership data appear, with no
universal-over-`D_T` lower bound, no universal-over-units quantifier,
and no global universal-Spa lower bound.

In Wedhorn 8.34(ii), the residual corresponds to the per-Laurent-piece
σ-cancellation identity:

* For τ = `algebraMap s_D` (the α_s_D piece): `σ_loc⁻¹ * algebraMap s_D
  ≤ D_s` at `w` with `w.vle 1 (σ_loc⁻¹ * algebraMap s_D)` and
  non-vanishing.

* For τ ∈ `T_D.image (algebraMap)` (the α_T_D pieces): per-`t_D`
  clearing identity with the σ-rescaled Laurent piece data.

Both are concrete σ-construction algebraic identities at each
Laurent piece, deliverable from σ-strict-domination + denominator
clearing data. T081 does **NOT** discharge the residual; it isolates
the residual as the single named algebraic identity tied to T065's
σ/Laurent-cover output.

## Notes

* No root import; leaf-level.
* Imports T065 (`WedhornLocalizedCor732SigmaSupplier`) for the σ-image
  cover output and T079 (`WedhornPointwiseClearingSupplierFromSigmaPower`)
  for the downstream `SigmaProductClearedInequalitySupplier` chain.
* No edits to T031–T080 accepted leaves, root imports, or final
  theorem signatures.
* The named residual is **per-τ source-restricted** (only `τ` and
  the supplied LHS data appear); no universal-over-`D_T`, no
  universal-over-units, no global universal-Spa lower bound.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No final `ValuationSpectrum.tateAcyclicity` hypothesis additions.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Per-τ source-restricted pointwise clearing residual at the
localized side** (T081 named source-restricted algebraic residual).

Captures the σ-construction's per-Laurent-piece algebraic identity at
each `τ ∈ localizedTestFamily s T_D s_D`: at every `w ∈ Spa(Loc s,
+)` satisfying

* `w.vle f_loc s_base_loc` — the source `f`-membership,
* `w.vle (1 : Loc s) (σ_loc⁻¹ * τ)` — the σ-rescaled Laurent piece
  membership at `σ_loc⁻¹ * τ` (T065 output),
* `¬ w.vle (σ_loc⁻¹ * τ) 0` — `σ_loc⁻¹ * τ` non-vanishing
  (auto-derivable from σ_loc unit + τ non-vanishing),

derive `w.vle (σ_loc⁻¹ * τ) D_s`.

**The named source-restricted algebraic residual** at this layer is
the per-τ source-restricted clearing predicate. The σ_loc and σ-image
cover are consumed from T065's output; the residual is the genuine
σ-cancellation algebraic identity per Laurent piece. -/
def LocalizedPerTauPointwiseClearingResidual
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (s_base_loc D_s f_loc : Localization.Away s) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ τ ∈ localizedTestFamily s T_D s_D,
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle f_loc s_base_loc →
      w.vle (1 : Localization.Away s)
        (((σ_loc⁻¹ : (Localization.Away s)ˣ) :
          Localization.Away s) * τ) →
      ¬ w.vle (((σ_loc⁻¹ : (Localization.Away s)ˣ) :
        Localization.Away s) * τ) 0 →
      w.vle (((σ_loc⁻¹ : (Localization.Away s)ˣ) :
        Localization.Away s) * τ) D_s

omit [PlusSubring A] in
/-- **Pointwise clearing supplier from localized Cor 7.32 output**
(T081 main bridge).

Produces the pointwise clearing supplier shape consumed by T077 / T078
(at the localized A := Localization.Away s instantiation) from a
σ_loc choice + the per-τ source-restricted clearing residual:

```
∀ t' ∈ (localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·),
  ∀ w ∈ Spa(Loc s, +),
    w.vle f_loc s_base_loc → w.vle 1 t' → ¬ w.vle t' 0 →
    w.vle t' D_s
```

**Substantive consumption** of the per-τ source-restricted residual:
the bridge re-indexes the image-finset hypothesis `t' ∈ ...image (σ_loc⁻¹
* ·)` back to `τ ∈ localizedTestFamily s T_D s_D` via
`Finset.mem_image` and applies the residual at the recovered τ. The
σ_loc unit is consumed in the residual signature.

The σ-image cover hypothesis from T065 is **not** consumed by this
bridge directly — the bridge produces the per-`t'` shape required by
T077 / T078, regardless of how the σ-image cover establishes
membership. T065's σ-image cover supplies the LHS Laurent piece
membership at the consumer side; the residual supplies the per-τ
clearing identity. -/
theorem pointwise_clearing_supplier_from_localized_cor732_output
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (s_base_loc D_s f_loc : Localization.Away s)
    (h_per_tau_residual :
      LocalizedPerTauPointwiseClearingResidual
        P T s hopen T_D s_D σ_loc s_base_loc D_s f_loc) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ t' ∈ (localizedTestFamily s T_D s_D).image
      (fun τ => ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
        Localization.Away s) * τ),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle f_loc s_base_loc →
        w.vle (1 : Localization.Away s) t' →
        ¬ w.vle t' 0 →
        w.vle t' D_s := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro t' ht' w hw_spa hw_f hw_one_t hw_t_ne
  obtain ⟨τ, hτ_mem, rfl⟩ := Finset.mem_image.mp ht'
  exact h_per_tau_residual τ hτ_mem w hw_spa hw_f hw_one_t hw_t_ne

omit [PlusSubring A] in
/-- **`SigmaProductClearedInequalitySupplier` from localized Cor 7.32
output, end-to-end direct lane** (T081 + T077 composition).

End-to-end composition: from a σ_loc choice + the per-τ source-
restricted clearing residual, deliver T072's named residual
`SigmaProductClearedInequalitySupplier` (the C1 sigma-construction
endgame target) by composing T081's pointwise-clearing bridge with
T077's
`SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier`.

**End-to-end direct lane**:
per-τ clearing residual (T081 named) → pointwise clearing supplier
(T081 bridge) → direct upper bound supplier (T077 bridge) →
`SigmaProductClearedInequalitySupplier` (T073 `N = 0` witness).

The whole chain is closed-form per-`(v, t')` source-restricted
valuation arithmetic; the only non-mechanical content is the per-τ
source-restricted clearing residual (the genuine σ-cancellation
algebraic identity at each Laurent piece). -/
theorem SigmaProductClearedInequalitySupplier_from_localized_cor732_output_pointwiseClearing
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (s_base_loc D_s f_loc : Localization.Away s)
    (h_per_tau_residual :
      LocalizedPerTauPointwiseClearingResidual
        P T s hopen T_D s_D σ_loc s_base_loc D_s f_loc) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    SigmaProductClearedInequalitySupplier
      ((localizedTestFamily s T_D s_D).image
        (fun τ => ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
          Localization.Away s) * τ))
      s_base_loc D_s f_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  exact SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier
    ((localizedTestFamily s T_D s_D).image
      (fun τ => ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
        Localization.Away s) * τ))
    s_base_loc D_s f_loc
    (pointwise_clearing_supplier_from_localized_cor732_output
      P T s hopen T_D s_D σ_loc s_base_loc D_s f_loc h_per_tau_residual)

end ValuationSpectrum
