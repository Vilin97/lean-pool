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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Faithful flatness of adic completion under the Jacobson condition

**Stacks 00MA** (https://stacks.math.columbia.edu/tag/00MA):
For a Noetherian ring `R` and an ideal `I ⊆ R` with `I ⊆ Jacobson(R)`, the
adic completion `R → AdicCompletion I R` is faithfully flat.

This file provides the Mathlib-style generic theorem. Applications in the
adic-spaces project compose it with the specific faithful-flatness residual
(`locSubringToRingOfDef_faithfullyFlat_of_residual` in
`IdealLocalizationCompletion.lean`) to discharge `coeRingHom_preserves_proper`
(see `Cor832.coeRingHom_preserves_proper_of_stacks00MA`).

## Main result

* `AdicCompletion.faithfullyFlat_of_le_jacobson_bot`: for Noetherian `R`
  and `I ≤ Ideal.jacobson ⊥`, `Module.FaithfullyFlat R (AdicCompletion I R)`.

## Proof sketch

Flatness is Mathlib's `AdicCompletion.flat_of_isNoetherian` (requires only
Noetherianity). For the faithful-flat condition (maximal-ideal proper
descent):

1. Given a maximal ideal `m ⊆ R`, show `m • (⊤ : Submodule R (AdicCompletion I R)) ≠ ⊤`.
2. Using `Ideal.smul_top_eq_map`, this reduces to
   `Ideal.map (algebraMap R (AdicCompletion I R)) m ≠ ⊤`.
3. Apply the canonical surjection `evalₐ I 1 : AdicCompletion I R → R/I`,
   which is the "level-1 quotient" obtained by the adic completion's
   limit structure. Its composition with `algebraMap` is `Ideal.Quotient.mk I`.
4. If `m.map algebraMap = ⊤`, then after applying `Ideal.map (evalₐ 1)` and
   composing, we get `m.map (Quotient.mk I) = ⊤` in `R/I`.
5. By `Ideal.comap_map_quotientMk`: the comap of this is `I ⊔ m`. So
   `I ⊔ m = ⊤`, hence `R = I + m`. Since `I ⊆ Jacobson(⊥) ⊆ m` (every
   maximal contains the Jacobson radical), `I + m = m`, so `m = ⊤`,
   contradicting `m.IsMaximal`.
-/

@[expose] public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- **Stacks 00MA**: for Noetherian `R` and ideal `I ⊆ R` with
`I ⊆ Jacobson(⊥)`, the adic completion `AdicCompletion I R` is faithfully
flat over `R`.

**Proof**: flatness is `AdicCompletion.flat_of_isNoetherian` (Mathlib).
For the maximal-ideal proper descent condition, apply the level-1
evaluation `evalₐ I 1 : R^ → R/I^1 = R/I` to reduce to the statement that
the image ideal `m/I` is proper in `R/I`; this follows from `I ⊆ m` (every
maximal contains the Jacobson radical). -/
theorem faithfullyFlat_of_le_jacobson_bot (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) :
    Module.FaithfullyFlat R (AdicCompletion I R) := by
  refine ⟨?_⟩
  intro m hm
  rw [Ideal.smul_top_eq_map, Ne, Submodule.restrictScalars_eq_top_iff]
  intro hm_top
  have hIm : I ≤ m :=
    hI.trans (Ideal.jacobson_bot (R := R) ▸ Ring.jacobson_le_of_isMaximal m)
  have h_comp : ((AdicCompletion.evalₐ I 1).toRingHom.comp
      (algebraMap R (AdicCompletion I R))) = Ideal.Quotient.mk (I ^ 1) := by
    ext x
    exact AdicCompletion.evalₐ_of I 1 x
  have h_eval_map : Ideal.map ((AdicCompletion.evalₐ I 1).toRingHom.comp
      (algebraMap R (AdicCompletion I R))) m = ⊤ := by
    rw [← Ideal.map_map, hm_top, Ideal.map_top]
  rw [h_comp, show (I ^ 1 : Ideal R) = I from pow_one I] at h_eval_map
  have h_sup : I ⊔ m = ⊤ := by
    have := Ideal.comap_map_quotientMk I m
    rw [h_eval_map, Ideal.comap_top] at this
    exact this.symm
  exact hm.ne_top <| by rw [← h_sup, sup_eq_right.mpr hIm]

end AdicCompletion

/-! ### Boundary with the adic-spaces project

The generic theorem `AdicCompletion.faithfullyFlat_of_le_jacobson_bot` applies
to the project's Lane B residual (`locSubringToRingOfDef_faithfullyFlat_of_residual`
in `IdealLocalizationCompletion.lean`, which consumes
`Module.FaithfullyFlat locSubring (AdicCompletion locIdeal locSubring)`)
**only** if one can provide `locIdeal ≤ Ideal.jacobson ⊥` in `locSubring`.

**This Jacobson condition is NOT automatic** for arbitrary uncompleted
Tate/Huber localization rings:

* In the Tate setting, `locSubring = A₀[t₁/s, …, tₙ/s] ⊆ Localization.Away s`
  is generally not adic-complete, and its pair of definition ideal
  `locIdeal = I · locSubring` need not be contained in the Jacobson radical.
* The project currently provides two **conditional** paths to the Jacobson
  containment:
  - `locIdeal_le_jacobson_bot_of_isAdicComplete`
    (`IdealLocalization.lean`, asserts `locSubring` adic-complete);
  - `locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat`
    (`Cor832.lean`, asserts faithful-flatness of `locSubringToRingOfDef`);
  both circular with respect to Lane B's ultimate residual.

**What is NEEDED** to instantiate `faithfullyFlat_of_le_jacobson_bot` for
the project's `locSubring`/`locIdeal`:

```lean
-- OPEN, unconditional Jacobson-condition residual for locSubring:
theorem locIdeal_le_jacobson_bot_unconditional
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)] :
    locIdeal D.P D.T D.s ≤ Ideal.jacobson (⊥ : Ideal (locSubring D.P D.T D.s))
```

This is the **precise remaining ring-theoretic content** needed to close
T-IDEAL-2 Lane B unconditionally without circularity. It is not automatic:
arbitrary uncompleted localizations of Huber rings need not satisfy this
Jacobson condition. Closure would require either (a) a project-specific
proof specialized to the Tate/Huber setting using topological
nilpotence + bounded-subring structure, or (b) a broader argument valid
for general "reasonable" non-complete rings. -/
