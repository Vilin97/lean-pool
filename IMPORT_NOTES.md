# Quasicategory v4.18 → v4.32 bump — WIP status

Vendored project `LeanPool/Quasicategory/**` (author Jack McKoen, Apache-2.0), bumped from
Mathlib/Lean `v4.18.0-rc1` to `v4.32.0-rc1`. This is a ~14-version jump through the most
heavily-refactored part of Mathlib (CategoryTheory / simplicial sets), so breakage is heavy.

## Modules that build clean (error- and warning-free): 18

Foundational / leaf layer and everything reachable without the `SSet.Subcomplex` blocker:

- `TopCatModelCategory/CommSq.lean`
- `TopCatModelCategory/Fin.lean`
- `TopCatModelCategory/MonoCoprod.lean`
- `TopCatModelCategory/MonoidalClosed.lean`
- `TopCatModelCategory/MorphismProperty.lean`
- `TopCatModelCategory/Multiequalizer.lean`
- `TopCatModelCategory/Set.lean`
- `TopCatModelCategory/ULift.lean`
- `TopCatModelCategory/ColimitsType.lean`   (the hardest file — see notes below)
- `TopCatModelCategory/SSet/Basic.lean`
- `TopCatModelCategory/SSet/SimplexCategory.lean`
- `TopCatModelCategory/SSet/StrictSegal.lean`
- `TopCatModelCategory/SSet/MonoCoprod.lean`
- `InMathlib/Retract/Basic.lean`
- `InMathlib/Retract/MorphismProperty.lean`  (gutted — fully upstreamed)
- `InMathlib/Lifting/Basic.lean`             (gutted — fully upstreamed)
- `InMathlib/Closed/FunctorHom.lean`         (gutted — fully upstreamed)
- `InMathlib/Closed/FunctorToTypes.lean`     (gutted — fully upstreamed)

All 18 build together warning-free and pass `lake exe lint-style LeanPool` (no Quasicategory hits).

## Build frontier: buildable-but-still-broken (their deps are green)

`lake build LeanPool.Quasicategory.Main` reaches exactly four modules with errors; everything
else in the DAG is *blocked* behind `SSet/Subcomplex.lean`. Remaining error total from the Main
build: **155** across these four files.

- `TopCatModelCategory/SSet/Subcomplex.lean` — **34 errors** (down from 60+). All ~61 upstreamed
  duplicate declarations were removed (see below); the remaining errors are the `Subpresheaf` →
  `Subfunctor` refactor (Mathlib renamed the whole low-level API and moved it to
  `Mathlib.CategoryTheory.Subfunctor.*`) plus structure-field renames on `Lattice.BicartSq`
  (`max_eq`/`min_eq` → `sup_eq`/`inf_eq`) and `CompleteLattice.MulticoequalizerDiagram`
  (`min_eq` → `eq_inf`). **This is the single biggest blocker** — the entire SSet chain
  (`Boundary`, `Horn`, `Degenerate`, `HasDimensionLT`, `StandardSimplex`, `Monoidal`, `Skeleton`,
  `SmallObject`, `Presentable`, …) and hence every top-level `Quasicategory.*` file sits behind it.
- `TopCatModelCategory/SSet/EffectiveEpi.lean` — 14 errors. Same `ConcreteCategory` pattern as
  ColimitsType (`descApp_eq` cascade from a `↾`/`ConcreteCategory.hom` type mismatch). Independent
  of Subcomplex; a good next target.
- `Lex.lean` — many `simp`/`omega`/`Fin` proof breakages (self-contained leaf; downstream needs
  Subcomplex anyway).
- `PushoutProduct/Basic.lean` — monoidal/pushout API churn (`Cocones.precompose_obj_*` renamed,
  `whisker_exchange`, `pt_*_iso'` now propositions, several unsolved goals). Self-contained leaf.

No files were `exclude`d; the four `InMathlib/*` modules were reduced to header + import +
module-docstring placeholders because their entire content is now in Mathlib and nothing in the
project imports them.

## Key API-migration patterns discovered (reuse these for the rest of the chain)

1. **Type-category morphisms are now `ConcreteCategory`-wrapped.** `congr_fun h x` on an equation
   of morphisms in `Type u` → `ConcreteCategory.congr_hom h x`. A plain function used where a
   Type-hom `X ⟶ Y` is expected no longer coerces — wrap it with `↾` (asHom), e.g.
   `↾(fun ⟨a,ha⟩ ↦ (⟨f a, _⟩ : ↥A))`. Note `(A : Type u)` is only a coercion in *term* position;
   in a function-type position it parses as a binder, so use `↥A`.
2. **Large chunks of the vendored WIP are now IN Mathlib** and must be deleted, not fixed:
   - `InMathlib/*` (llp/rlp + stability, `Functor.HomObj`/`functorHom`, monoidal-closed
     functor-to-types, `IsStableUnderRetracts`) → `Mathlib.CategoryTheory.{MorphismProperty.
     LiftingProperty, Functor.FunctorHom, Monoidal.Closed.FunctorToTypes, MorphismProperty.Retract}`.
   - `ColimitsType` pushout/pullback lemmas → `Mathlib.CategoryTheory.Limits.Types.{Pushouts,
     Pullbacks}`; the cofan-injection lemmas → `CategoryTheory.Limits.Cofan.*`
     (`inj_injective_of_isColimit`, `inj_apply_eq_iff_of_isColimit`, …); `Quot.Rel` →
     `Functor.ColimitTypeRel`; `pushoutCocone_injective_inr_of_isColimit` →
     `pushoutCocone_inr_injective_of_isColimit`.
   - `Subcomplex` ~61 decls (`topIso`, `prod`, `homOfLE`, `unionProd`, `range`, `image`,
     `preimage`, `lift`, `prodIso`, …) are now in Mathlib's `SSet.Subcomplex` / `Subpresheaf` API.
3. **StrictSegal restructured**: the old typeclass `StrictSegal X` is now a *structure*;
   `IsStrictSegal X` is the class; obtain a structure value with `StrictSegal.ofIsStrictSegal X`
   and call `sx.spineInjective` / `sx.spineEquiv`.
4. **Import remaps applied** (v4.18 → v4.32):
   - `CategoryTheory.Closed.{Enrichment,FunctorToTypes,Monoidal}` → `CategoryTheory.Monoidal.
     Closed.{Enrichment,FunctorToTypes,Basic}`
   - `CategoryTheory.Limits.Shapes.Types` (split) → `CategoryTheory.Limits.Types.{Colimits,
     Pushouts,Pullbacks,Coproducts}`
   - `CategoryTheory.Limits.TypesFiltered` → `CategoryTheory.Limits.Types.Filtered`
   - `Data.Set.FunctorToTypes` → `CategoryTheory.Types.Set`
   - `CategoryTheory.Limits.Shapes.Pullback.CommSq` (deprecated) →
     `…Pullback.IsPullback.BicartesianSq`
   - `CategoryTheory.Adhesive` (deprecated) → `CategoryTheory.Adhesive.Basic`
5. **Deprecation renames swept** across the tree: `FunctorToTypes.{naturality,map_id_apply,
   map_comp_apply,comp}` → `{NatTrans.naturality_apply, Functor.map_id_apply,
   Functor.map_comp_apply, NatTrans.comp_app_apply}`; `Fin.coe_castSucc` → `Fin.val_castSucc`;
   `Fin.castSucc_lt_succ` arg is now implicit; `Ordinal.toType` → `Ordinal.ToType`,
   `toTypeOrderBot` → `Cardinal.orderBotAleph0OrdToType`; `Classical.not_and_iff_or_not_not` →
   `not_and_or`; `whiskerRight` → `Functor.whiskerRight`; `induction'` (unimported tactic) →
   core `induction … with`.

## Suggested next steps

1. `SSet/Subcomplex.lean`: resolve the `Subpresheaf` → `Subfunctor` rename (add
   `Mathlib.CategoryTheory.Subfunctor.{Basic,Image}` and switch to the new names) and the two
   structure-field renames; that unblocks the whole SSet chain.
2. `SSet/EffectiveEpi.lean`: apply the `ConcreteCategory.congr_hom` / `↾` pattern.
3. Then work outward through `Boundary → Horn → Degenerate → … → SmallObject → Basic`, and the
   `_007F/*` chain (needs `Lex`), finally the top-level `Quasicategory.*` files and `Main`.
