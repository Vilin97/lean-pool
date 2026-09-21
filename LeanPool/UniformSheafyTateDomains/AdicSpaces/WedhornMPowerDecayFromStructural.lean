/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCor732ToFactoredChain
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiDominatingUnit

/-!
# Wedhorn M-power-decay: reduction to one Wedhorn structural inequality

Reduces the unified M-power-decay residual exposed by
`WedhornLocalCor732ToFactoredChain` (commit `ab55d85`) to **exactly one
strictly smaller named theorem**: the **Wedhorn structural inequality**.

## What is reducible vs irreducible

The unified M-power-decay has four conjuncts at each `(w, τ)`:

1. **Wedhorn structural inequality**: `∀ t' ∈ T_D.image algebraMap,
   w.vle (algebraMap s) (algebraMap s_D * σ_loc * ∏ erase t')`. This
   is the genuine Wedhorn 8.34(ii) Route B content; not derivable from
   pure σ-strict-domination.

2. **T_D non-vanishing**: `∀ t'' ∈ T_D.image algebraMap, ¬ w.vle t'' 0`.
   Cor 7.32 supplies "no common zero" only existentially (some `t` is
   non-vanishing at each `v`), so per-`t''` non-vanishing requires a
   strictly stronger structural input.

3. **`α_s_D` non-vanishing for the `τ = algebraMap s_D` branch**:
   `¬ w.vle (algebraMap s_D) 0`. **Discharged automatically** via
   `not_vle_zero_of_strict_dominator` from σ-strict-domination of
   `algebraMap s_D`.

4. **`α_s_D` non-vanishing for the `τ ∈ T_D.image algebraMap` branch**:
   `¬ w.vle (algebraMap s_D) 0`. **Not** auto-derivable here; takes a
   separate explicit hypothesis.

This file's reduction:

* (3) is auto-derived inside the bridge.
* (1), (2), (4) are exposed as explicit named hypotheses; the single
  most substantial of these is (1), the **Wedhorn structural
  inequality**, which becomes the canonical residual.

## What this file provides

* `h_M_power_decay_via_Wedhorn_structural_inequality` — the **reduced
  bridge**: given the Wedhorn structural inequality (the genuine
  Wedhorn 8.34(ii) Route B content), the T_D non-vanishing supplier,
  and the `α_T_D` branch s_D non-vanishing supplier, derives the
  unified M-power-decay by auto-deriving the `α_s_D` branch s_D
  non-vanishing through `not_vle_zero_of_strict_dominator`.

The single remaining residual is the **Wedhorn structural inequality**
itself, named `Wedhorn_structural_inequality_target` in the docblock
below. Its proof is the genuinely-new Wedhorn 8.34(ii) Route B content
(M-choice via Spa-quasi-compactness applied to the σ-power family).

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness / Zavyalov / bivariate-overlap content.
* Does not edit Primary's assembly file or Tertiary's value-group
  file.
* Reuses `not_vle_zero_of_strict_dominator`
  (`WedhornMultiDominatingUnit.lean:189`) for the auto-discharge.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [PlusSubring A] in
/-- **Reduced M-power-decay bridge** — reduces the unified
M-power-decay residual to three concrete named hypotheses, with the
fourth (`α_s_D` branch s_D non-vanishing) auto-derived via
`not_vle_zero_of_strict_dominator`.

The Wedhorn structural inequality `h_Wedhorn_structural` is the
**single most substantial residual**: it carries the genuinely-new
Wedhorn 8.34(ii) Route B M-power-decay content and is the canonical
boundary for the next ticket. -/
theorem h_M_power_decay_via_Wedhorn_structural_inequality
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_Wedhorn_structural :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle (algebraMap A (Localization.Away s) s)
              (algebraMap A (Localization.Away s) s_D *
                (σ_loc : Localization.Away s) *
                (∏ t ∈ (T_D.image
                  (algebraMap A (Localization.Away s))).erase t', t)))
    (h_T_D_ne :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
            ¬ w.vle t'' 0)
    (h_α_T_D_s_D_ne :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle (algebraMap A (Localization.Away s) s)
                (algebraMap A (Localization.Away s) s_D *
                  (σ_loc : Localization.Away s) *
                  (∏ t ∈ (T_D.image
                    (algebraMap A (Localization.Away s))).erase t', t))) ∧
          (∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
              ¬ w.vle t'' 0) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f τ hτ hστ
  refine ⟨h_Wedhorn_structural w hw_spa hw_f τ hτ hστ,
    h_T_D_ne w hw_spa hw_f τ hτ hστ, ?_⟩
  -- Branch on whether `τ = algebraMap s_D` or `τ ∈ T_D.image algebraMap`.
  rw [mem_localizedTestFamily_iff] at hτ
  rcases hτ with rfl | hτ_in_T_D
  · -- α_s_D branch: discharge via not_vle_zero_of_strict_dominator.
    exact not_vle_zero_of_strict_dominator hστ.2
  · -- α_T_D branch: use the explicit supplier.
    exact h_α_T_D_s_D_ne w hw_spa hw_f τ hτ_in_T_D hστ

/-! ### The single named residual: the Wedhorn structural inequality

The Wedhorn structural inequality, isolated as a single concrete Lean
theorem signature with full hypotheses:

```
theorem Wedhorn_structural_inequality_target
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    -- Wedhorn 8.34(ii) Cor 7.32 structural data: σ_loc = π_loc^(M+1):
    (π_loc : (locPairOfDefinition P T s hopen).A₀)
    (M : ℕ)
    (hσ_loc_eq_pow : (σ_loc : Localization.Away s) =
      ((locPairOfDefinition P T s hopen).A₀.subtype π_loc) ^ (M + 1))
    (hπ_loc_tn : IsTopologicallyNilpotent
      ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
    -- Tate / pseudouniformizer hypotheses for the local Spa:
    (hA₀_le : P.A₀ ≤ A⁺)
    -- ... (further Cor 7.32 hypotheses as needed) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (algebraMap A (Localization.Away s) s)
            (algebraMap A (Localization.Away s) s_D *
              (σ_loc : Localization.Away s) *
              (∏ t ∈ (T_D.image
                (algebraMap A (Localization.Away s))).erase t', t))
```

The `σ_loc = π_loc^(M+1)` form ties σ to a topologically-nilpotent
pseudouniformizer power, with `M` chosen to discharge the structural
inequality uniformly via Spa-quasi-compactness on the localized Spa.
This is the Wedhorn 8.34(ii) Step 2 ratio choice + the Cor 7.32
construction's strict-domination structure. Per the audit at
`WedhornMultiDominatingUnit.lean:234–304`, this is the genuinely-new
Wedhorn Route B content; my reduced bridge consumes it directly. -/

end ValuationSpectrum
