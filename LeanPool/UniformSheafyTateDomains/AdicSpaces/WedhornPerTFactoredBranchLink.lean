/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalSubsetViaFactoredChains
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiBranchSubsetInequality
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornDominatingUnitInequality

/-!
# Wedhorn per-`t'` factored chain — α_s_D branch link

Proves the σ-factored per-`t'` chain at the canonical `α_s_D` branch
(`τ = algebraMap s_D`) under concrete named Wedhorn structural
hypotheses, closing the genuinely-Wedhorn-content gap exposed by
`WedhornLocalSubsetViaFactoredChains` (commit `14b90a4`) — at least
for this branch.

## Structural hypotheses

The proof uses TWO concrete named hypotheses on top of the standard
σ-strict-domination + f-membership data:

* **`h_T_D_ne`**: every `t'' ∈ T_D.image (algebraMap A (Localization.Away s))`
  is non-degenerate at `w` (`¬ w.vle t'' 0`). This is the natural
  Wedhorn 8.34(ii) input that the test family `T_D` consists of
  non-zero elements at the relevant Spa-points.

* **`h_Wedhorn_α_s_D`**: for each `t' ∈ T_D.image algebraMap`, the
  rational-open structural inequality
  `w.vle (algebraMap s) (algebraMap s_D * σ_loc * (∏ erase t'))`
  (where `erase t'` is `(T_D.image algebraMap).erase t'`). This is
  the genuine Wedhorn 8.34(ii) candidate-shape arithmetic linking
  `algebraMap s`, `algebraMap s_D`, `σ_loc`, and the per-`t'`
  excised product.

Under these two named inputs, the σ-factored per-`t'` chain at the
`α_s_D` branch is provable: the proof composes `Finset.mul_prod_erase`,
`Spv.vle_trans`, and `ValuativeRel.mul_vle_mul_iff_left` (right-side
cancellation) to turn the f-membership and Wedhorn structural
inequality into the desired per-`t'` factored bound.

## What this file provides

* `not_vle_zero_prod_of_pointwise` — small reusable helper: pointwise
  non-vanishing implies product non-vanishing (Finset induction).

* `per_t_factored_chain_α_s_D_branch` — pointwise (per `t'`) factored
  chain at the `α_s_D` branch, derived from the structural hypotheses
  above.

* `h_α_s_D_factored_via_Wedhorn_structural` — assembled `α_s_D`-branch
  hypothesis matching the input shape of
  `h_T_test_compat_loc_canonical_via_factored_chains` (commit
  `83f2964`) and
  `rationalOpen_subset_base_via_factored_chains` (commit `14b90a4`).

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness / Zavyalov / bivariate-overlap content.
* Does NOT edit Tertiary's localized Cor 7.32 consumer file.
* No σ-power-decay derivation; uses the structural inequality
  `h_Wedhorn_α_s_D` directly.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **Product non-vanishing from pointwise non-vanishing**. For any
indexed family `f : α → A` and a `Finset` `S`, if `f t ≠ 0` at `v` for
every `t ∈ S`, then `∏ t ∈ S, f t ≠ 0` at `v`. Direct
`Finset.induction_on` using `ValuativeRel.zero_vlt_mul`. -/
theorem not_vle_zero_prod_of_pointwise
    {α : Type*} (v : Spv A) (S : Finset α) (f : α → A)
    (h : ∀ t ∈ S, ¬ v.vle (f t) 0) :
    ¬ v.vle (∏ t ∈ S, f t) 0 := by
  classical
  letI : ValuativeRel A := v.toValuativeRel
  induction S using Finset.induction_on with
  | empty => simp [v.not_vle_one_zero]
  | insert a S' ha ih =>
      rw [Finset.prod_insert ha]
      exact ValuativeRel.zero_vlt_mul (h a (Finset.mem_insert_self a S'))
        (ih (fun t ht => h t (Finset.mem_insert_of_mem ht)))

variable [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A]

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **`α_s_D` branch link — per-`t'` factored chain at a Spa-point**.

For a fixed Spa-point `w ∈ Spa(Localization.Away s, locSubring P T s)`
and a fixed `t' ∈ T_D.image (algebraMap A (Localization.Away s))`,
under the named Wedhorn structural hypotheses `h_T_D_ne` and
`h_Wedhorn_α_s_D` plus σ-strict-domination by `algebraMap s_D`,
derive the σ-factored per-`t'` chain
`w.vle (t' * σ_loc) ((algebraMap s_D) * σ_loc)`.

**Proof outline**:

1. Decompose `∏ T_D.image algebraMap = t' * (∏ erase t')` via
   `Finset.mul_prod_erase`.
2. Combine with `hw_f` to extract the chain through `algebraMap s`.
3. Compose with `h_Wedhorn_α_s_D` (the structural inequality) via
   `Spv.vle_trans` to obtain the chain to
   `(algebraMap s_D) * σ_loc * (∏ erase t')`.
4. Cancel `∏ erase t'` on the right via
   `ValuativeRel.mul_vle_mul_iff_left`, using the product-nonzeroness
   from `h_T_D_ne` and `not_vle_zero_prod_of_pointwise`.
5. Commute factors on the LHS to match the conclusion's `t' * σ_loc`. -/
theorem per_t_factored_chain_α_s_D_branch
    [DecidableEq A]
    (s : A) (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (h_T_D_ne :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
        ¬ w.vle t'' 0)
    (hw_f :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s))
    (h_Wedhorn_α_s_D :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (algebraMap A (Localization.Away s) s)
          (algebraMap A (Localization.Away s) s_D *
            (σ_loc : Localization.Away s) *
            (∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t)))
    (t' : Localization.Away s)
    (ht' :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      t' ∈ T_D.image (algebraMap A (Localization.Away s))) :
    w.vle (t' * (σ_loc : Localization.Away s))
      (algebraMap A (Localization.Away s) s_D *
        (σ_loc : Localization.Away s)) := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  -- Step 1: product split via `Finset.mul_prod_erase`, then rewrite hw_f.
  rw [show (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t) =
      t' * (∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t)
      from (Finset.mul_prod_erase _ id ht').symm] at hw_f
  -- hw_f : w.vle (σ_loc * (t' * ∏ erase)) (algebraMap s)
  -- Reassociate: σ_loc * (t' * ∏ erase) = (σ_loc * t') * ∏ erase.
  rw [show ((σ_loc : Localization.Away s) *
        (t' * (∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t))) =
      ((σ_loc : Localization.Away s) * t') *
        (∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t)
      from by ring] at hw_f
  -- Step 3: chain via h_Wedhorn_α_s_D.
  have h_chain : w.vle ((σ_loc : Localization.Away s) * t' *
        (∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t))
      (algebraMap A (Localization.Away s) s_D *
        (σ_loc : Localization.Away s) *
        (∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t)) :=
    w.vle_trans hw_f (h_Wedhorn_α_s_D t' ht')
  -- Step 4: cancel ∏ erase on the right.
  have h_prod_ne : ¬ w.vle
      (∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t) 0 := by
    apply not_vle_zero_prod_of_pointwise
    intro t'' ht''
    exact h_T_D_ne t'' (Finset.mem_of_mem_erase ht'')
  rw [ValuativeRel.mul_vle_mul_iff_left h_prod_ne] at h_chain
  -- h_chain : w.vle (σ_loc * t') (algebraMap s_D * σ_loc)
  -- Step 5: commute on LHS.
  rwa [show (σ_loc : Localization.Away s) * t' =
        t' * (σ_loc : Localization.Away s) from mul_comm _ _] at h_chain

omit [PlusSubring A] in
/-- **Assembled `α_s_D`-branch hypothesis** matching the input shape of
`h_T_test_compat_loc_canonical_via_factored_chains` (commit `83f2964`)
and `rationalOpen_subset_base_via_factored_chains` (commit `14b90a4`).

Threads `per_t_factored_chain_α_s_D_branch` over all `t' ∈ T_D.image
algebraMap` and over all `w ∈ Spa(...)` with the f-membership and
σ-strict-domination hypotheses. The named structural hypotheses
`h_T_D_ne_supplier` and `h_Wedhorn_α_s_D_supplier` are
quantified per-`w`. -/
theorem h_α_s_D_factored_via_Wedhorn_structural
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_ne_supplier :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
          ¬ w.vle t'' 0)
    (h_Wedhorn_α_s_D_supplier :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (algebraMap A (Localization.Away s) s)
            (algebraMap A (Localization.Away s) s_D *
              (σ_loc : Localization.Away s) *
              (∏ t ∈ (T_D.image
                (algebraMap A (Localization.Away s))).erase t', t))) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w.vle (σ_loc : Localization.Away s)
          (algebraMap A (Localization.Away s) s_D) ∧
        ¬ w.vle (algebraMap A (Localization.Away s) s_D)
          (σ_loc : Localization.Away s) →
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (t' * (σ_loc : Localization.Away s))
          (algebraMap A (Localization.Away s) s_D *
            (σ_loc : Localization.Away s)) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f hστ t' ht'
  exact per_t_factored_chain_α_s_D_branch s T_D s_D σ_loc w
    (h_T_D_ne_supplier w hw_spa hw_f hστ)
    hw_f
    (h_Wedhorn_α_s_D_supplier w hw_spa hw_f hστ)
    t' ht'

omit [PlusSubring A] in
/-- **Assembled `α_T_D`-branch hypothesis** matching the input shape of
`h_T_test_compat_loc_canonical_via_factored_chains` (commit `83f2964`).

Parallel to `h_α_s_D_factored_via_Wedhorn_structural` but for the
`α_T_D` branches (`τ ∈ T_D.image algebraMap`). The per-`t'` factored
chain is branch-independent at the proof level — `per_t_factored_chain_α_s_D_branch`
applies regardless of which `τ` supplies σ-strict-domination — so the
α_T_D branch shares the same proof skeleton, with the σ-strict-domination
hypothesis `hστ` parameterised by `τ ∈ T_D.image algebraMap` rather than
fixed at `algebraMap s_D`. -/
theorem h_α_T_D_factored_via_Wedhorn_structural
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_ne_supplier :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
            ¬ w.vle t'' 0)
    (h_Wedhorn_α_T_D_supplier :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle (algebraMap A (Localization.Away s) s)
              (algebraMap A (Localization.Away s) s_D *
                (σ_loc : Localization.Away s) *
                (∏ t ∈ (T_D.image
                  (algebraMap A (Localization.Away s))).erase t', t))) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (t' * (σ_loc : Localization.Away s))
            (algebraMap A (Localization.Away s) s_D *
              (σ_loc : Localization.Away s)) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ w hw_spa hw_f hστ t' ht'
  exact per_t_factored_chain_α_s_D_branch s T_D s_D σ_loc w
    (h_T_D_ne_supplier τ hτ w hw_spa hw_f hστ)
    hw_f
    (h_Wedhorn_α_T_D_supplier τ hτ w hw_spa hw_f hστ)
    t' ht'

omit [PlusSubring A] in
/-- **Full canonical compatibility theorem via Wedhorn structural
inequalities**.

Composes `h_α_s_D_factored_via_Wedhorn_structural` and
`h_α_T_D_factored_via_Wedhorn_structural` with the explicit
`α_T_D`-branch `s_D` non-degeneracy supplier into a single
`h_T_test_compat_loc_canonical`-shape output for the canonical test
family `localizedTestFamily s T_D s_D`, ready for direct consumption
by `rationalOpen_subset_base_via_local_Cor732_chain`.

Both per-branch chains use the SAME structural inequality
`h_Wedhorn_α_T_D_supplier` (parameterised by `τ`); the α_s_D branch
reuses the same shape with τ specialised to `algebraMap s_D`. -/
theorem h_T_test_compat_loc_canonical_via_Wedhorn_structural
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    -- α_s_D branch suppliers (specialised to τ = algebraMap s_D):
    (h_T_D_ne_supplier_α_s_D :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
          ¬ w.vle t'' 0)
    (h_Wedhorn_α_s_D_supplier :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (algebraMap A (Localization.Away s) s)
            (algebraMap A (Localization.Away s) s_D *
              (σ_loc : Localization.Away s) *
              (∏ t ∈ (T_D.image
                (algebraMap A (Localization.Away s))).erase t', t)))
    -- α_T_D branch suppliers (parameterised over τ ∈ T_D.image):
    (h_T_D_ne_supplier_α_T_D :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
            ¬ w.vle t'' 0)
    (h_Wedhorn_α_T_D_supplier :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle (algebraMap A (Localization.Away s) s)
              (algebraMap A (Localization.Away s) s_D *
                (σ_loc : Localization.Away s) *
                (∏ t ∈ (T_D.image
                  (algebraMap A (Localization.Away s))).erase t', t)))
    (h_α_T_D_s_D_ne_supplier :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_canonical_via_factored_chains P T s hopen T_D s_D σ_loc
    (h_α_s_D_factored_via_Wedhorn_structural P T s hopen T_D s_D σ_loc
      h_T_D_ne_supplier_α_s_D h_Wedhorn_α_s_D_supplier)
    (h_α_T_D_factored_via_Wedhorn_structural P T s hopen T_D s_D σ_loc
      h_T_D_ne_supplier_α_T_D h_Wedhorn_α_T_D_supplier)
    h_α_T_D_s_D_ne_supplier

end ValuationSpectrum
