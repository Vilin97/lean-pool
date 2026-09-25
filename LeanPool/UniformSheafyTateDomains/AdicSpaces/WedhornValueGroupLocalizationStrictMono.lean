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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedArchimedeanTransfer

/-!
# Value-group strictMono hom audit + corrected target signature

The genuine remaining piece for the MulArchimedean transfer
(`WedhornLocalizedArchimedeanTransfer.lean`, commit `fa682a5`):
constructing the strictly monotonic monoid homomorphism

```
ValueGroupWithZero (Localization.Away s) →* ValueGroupWithZero A
```

(in the `Localization → A` direction) needed by
`mulArchimedean_localization_comap_via_strictMono_hom`.

## Audit finding

Mathlib provides `ValuativeExtension.mapValueGroupWithZero A B`
(`Mathlib.RingTheory.Valuation.ValuativeRel.Basic:1237`):

```
def mapValueGroupWithZero : ValueGroupWithZero A →*₀ ValueGroupWithZero B
```

This goes the **OPPOSITE direction** to what we need (`A → B` instead
of `B → A`). It's strictly monotonic
(`mapValueGroupWithZero_strictMono`).

`MulArchimedean.comap (f : G →* M) (hf : StrictMono f) [MulArchimedean M]
: MulArchimedean G` requires the homomorphism to go `G → M` with
`M` Archimedean. With `G = ValueGroupWithZero B` (target — we want
this Archimedean) and `M = ValueGroupWithZero A` (source — given
Archimedean), we need `f : VG(B) → VG(A)`. Mathlib's map is `VG(A) → VG(B)`.

**Resolution**: for `B = Localization.Away s` with `w(s) ≠ 0`, the
Mathlib map `mapValueGroupWithZero A B` is BIJECTIVE (every `[b]_B` for
`b = a/s^k` equals `mapValueGroupWithZero ([a]_A · [s]_A^(-k))`,
well-defined since `[s]_A ≠ 0`). Taking the inverse gives the desired
`B → A` direction.

## Corrected target signature

The single remaining residual is now precisely:

```lean
theorem mapValueGroupWithZero_bijective_of_localization
    {A : Type*} [CommRing A] (s : A)
    (w : Spv (Localization.Away s))
    (hws : ¬ w.vle (algebraMap A (Localization.Away s) s) 0) :
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    letI : ValuativeRel A :=
      (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
    Function.Bijective
      (ValuativeExtension.mapValueGroupWithZero A (Localization.Away s))
```

Mathematical content:

* **Surjectivity**: every `b ∈ Localization.Away s = a/s^k` has class
  `[b]_B`. We compute:
  `[b]_B = [a]_B · [s]_B^(-k)`
  `      = mapValueGroupWithZero ([a]_A) · mapValueGroupWithZero ([s]_A)^(-k)`
  `      = mapValueGroupWithZero ([a]_A · [s]_A^(-k))`
  (well-defined since `[s]_A ≠ 0` in `ValueGroupWithZero A` — derived
  from `hws` via `comap_vle`).

* **Injectivity**: follows from `mapValueGroupWithZero_strictMono`
  (a strictly monotonic function is injective).

## Composition with the existing reducer

Once `mapValueGroupWithZero_bijective_of_localization` lands, the chain
to `mulArchimedean_localization_comap_via_strictMono_hom` is:

1. From bijectivity, build a `MulEquiv₀` from `ValueGroupWithZero A`
   to `ValueGroupWithZero (Localization.Away s)` (via
   `MonoidWithZeroHom.toMulEquiv` plus the bijectivity hypothesis).
2. Take `.symm` to get the inverse `ValueGroupWithZero (Localization.Away s)
   →*₀ ValueGroupWithZero A`.
3. Strict monotonicity of the inverse follows from strict monotonicity
   of `mapValueGroupWithZero` plus bijectivity (an order-preserving
   bijection has an order-preserving inverse).
4. Apply `MulArchimedean.comap` (the inverse + strict mono).

## Why this file does NOT prove the residual

The bijectivity proof requires:
* The well-definedness verification of the surjective formula
  `[a]_A · [s]_A^(-k) ↦ [b]_B` (independent of the `(a, k)`
  decomposition of `b`).
* The `[s]_A ≠ 0` derivation from `hws`.

Both require careful manipulation of the `ValueGroupWithZero` quotient
construction (`Mathlib.RingTheory.Valuation.ValuativeRel.Basic:340`).
This is the next concrete sub-target.

The companion structural lemmas needed (likely Mathlib already, but
needs excavation):
* `MulEquiv.symm_strictMono` (or `OrderMulEquiv` properties).
* `MonoidWithZeroHom.bijective_iff_isMulEquiv`.

## Notes

* No root import; leaf-level file.
* No sorries.
* No edits to committed bridge files or Secondary's
  branch-compatibility files.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-! ## Surjectivity residual (with explicit witness formula)

The single remaining piece for the full chain to `MulArchimedean` transfer:

```lean
theorem mapValueGroupWithZero_surjective_of_localization
    {A : Type*} [CommRing A] (s : A)
    (w : Spv (Localization.Away s))
    (hws : ¬ w.vle (algebraMap A (Localization.Away s) s) 0) :
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    letI : ValuativeRel A :=
      (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
    Function.Surjective
      (ValuativeExtension.mapValueGroupWithZero A (Localization.Away s))
```

### Proof outline (with explicit witness)

Take `[b]_B ∈ ValueGroupWithZero (Localization.Away s)`. By
`ValueGroupWithZero.ind`, `[b]_B = ValueGroupWithZero.mk b₁ b₂` for
some `b₁ ∈ Localization.Away s` and `b₂ ∈ posSubmonoid (Localization.Away s)`
(i.e., `0 <ᵥ b₂` under `w.toValuativeRel`).

By `IsLocalization.surj` (Mathlib):
* `∃ a₁ ∈ A, k₁ : ℕ, b₁ * (algebraMap s)^k₁ = algebraMap a₁`.
* `∃ a₂ ∈ A, k₂ : ℕ, b₂ * (algebraMap s)^k₂ = algebraMap a₂`.

(With `a₂ ∈ A` having `0 <ᵥ algebraMap a₂` in B, hence `0 <ᵥ a₂` in A
under `comap w`'s ValuativeRel — so `a₂ ∈ posSubmonoid A`.)

The **explicit witness** for surjectivity:
* `a := a₁ * s^k₂ ∈ A`.
* `c := a₂ * s^k₁` with `c ∈ posSubmonoid A` (since `a₂ ∈ posSubmonoid A`
  by above and `s^k₁ ∈ posSubmonoid A` from `hws` via `comap`).

Computation:
* `algebraMap a · b₂ = algebraMap (a₁ * s^k₂) · b₂ = algebraMap a₁ ·
  algebraMap s^k₂ · b₂ = algebraMap a₁ · algebraMap a₂ = algebraMap (a₁ * a₂)`.
* `b₁ · algebraMap c = b₁ · algebraMap (a₂ * s^k₁) = b₁ · algebraMap s^k₁ ·
  algebraMap a₂ = algebraMap a₁ · algebraMap a₂ = algebraMap (a₁ * a₂)`.

Both equal `algebraMap (a₁ * a₂)`, so `mk (algebraMap a) (mapPosSubmonoid c) =
mk b₁ b₂` by `ValueGroupWithZero.mk_eq_mk` (via `vle_refl` from equal
representatives). Then `mapValueGroupWithZero_mk` gives
`mapValueGroupWithZero (mk a c) = mk (algebraMap a) (mapPosSubmonoid c) = mk b₁ b₂`. ✓

### Why this file does NOT prove the residual directly

The proof requires:
* Careful manipulation of `IsLocalization.surj` to extract `(a₁, k₁)` and
  `(a₂, k₂)` from `b₁` and `b₂`.
* `posSubmonoid A` membership for `c = a₂ * s^k₁` (combining `a₂ ∈
  posSubmonoid A` with `s^k₁ ∈ posSubmonoid A` from `hws`).
* `ValueGroupWithZero.sound` application with the equality of representatives.

This is multi-step Mathlib-level manipulation. The next concrete sub-target
is the surjectivity proof above, which when combined with
`mapValueGroupWithZero_strictMono` and `strictMonoHom_inverse_of_bijective`
(below) closes the full chain to `MulArchimedean.comap` and thence
`hArch_loc`. -/

/-- **Strict-mono hom `VG(B) →* VG(A)` from a strict-mono surjection
the OTHER way**.

Given a strictly monotonic surjective monoid hom `g : VG(A) →*
VG(B)` (the typical localization case), construct a strictly monotonic
monoid hom `f : VG(B) →* VG(A)` going the opposite direction.

**Construction**: under the strict mono surjection `g`, `g` is
bijective (strict mono ⟹ inj; surj by hypothesis), so `g.toEquiv` has
an inverse. The inverse is monoid-multiplicative (since `g` is) and
strictly monotonic (since `g` is, and the inverse of a strict mono
bijection is strict mono).

**Use case**: combined with the residual
`mapValueGroupWithZero_bijective_of_localization` (documented above),
this produces the `B → A` strict-mono hom needed for
`mulArchimedean_localization_comap_via_strictMono_hom`.

**Status**: this is structural infrastructure — should exist in
Mathlib in some form; if not, this is a clean self-contained
construction. -/
theorem strictMonoHom_inverse_of_bijective
    {G H : Type*} [LinearOrder G] [LinearOrder H]
    [CommMonoid G] [CommMonoid H]
    (g : G →* H) (hg_strictMono : StrictMono g)
    (hg_surj : Function.Surjective g) :
    ∃ f : H →* G, StrictMono f := by
  -- Inverse function via Function.invFun (avoids Equiv coercion issues).
  let invFn : H → G := Function.invFun g
  have hinv_left : ∀ x : H, g (invFn x) = x := Function.rightInverse_invFun hg_surj
  have hinv_mul : ∀ x y : H, invFn (x * y) = invFn x * invFn y := by
    intro x y
    apply hg_strictMono.injective
    rw [hinv_left, g.map_mul, hinv_left, hinv_left]
  have hinv_one : invFn 1 = 1 := by
    apply hg_strictMono.injective
    rw [hinv_left, g.map_one]
  refine ⟨{ toFun := invFn, map_one' := hinv_one, map_mul' := hinv_mul }, fun x y hxy => ?_⟩
  show invFn x < invFn y
  exact hg_strictMono.lt_iff_lt.mp (by rwa [hinv_left, hinv_left])

/-- **Surjectivity of `mapValueGroupWithZero` for `Localization.Away s`**.

For `w : Spv (Localization.Away s)` with `algebraMap s` non-zero at `w`,
the Mathlib `ValuativeExtension.mapValueGroupWithZero A (Localization.Away s)`
is surjective. Combined with `mapValueGroupWithZero_strictMono`
(injectivity), this gives the bijectivity needed by
`strictMonoHom_inverse_of_bijective` to invert into the
`B → A` direction for the MulArchimedean transfer.

**Proof**: induct on `γ ∈ ValueGroupWithZero (Localization.Away s)`. For
`γ = mk b₁ b₂`, decompose via `IsLocalization.Away.sec`:
* `b₁ * algebraMap (s^k₁) = algebraMap a₁`.
* `b₂ * algebraMap (s^k₂) = algebraMap a₂`.

Take witness `(a := a₁ * s^k₂, c := a₂ * s^k₁)` with `c ∈ posSubmonoid A`
(from `b₂.property`, `hws`, and `zero_vlt_mul`). Verify equality via
`mapValueGroupWithZero_mk` + `ValueGroupWithZero.sound`: both sides
equal `algebraMap (a₁ * a₂)` after cross-multiplication and `sec_spec`
substitution. -/
theorem mapValueGroupWithZero_surjective_of_localization
    (s : A) (w : Spv (Localization.Away s))
    (hws : ¬ w.vle (algebraMap A (Localization.Away s) s) 0) :
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    letI : ValuativeRel A :=
      (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
    letI : ValuativeExtension A (Localization.Away s) :=
      ⟨fun _ _ => Iff.rfl⟩
    Function.Surjective
      (ValuativeExtension.mapValueGroupWithZero A (Localization.Away s)) := by
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  letI : ValuativeRel A :=
    (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
  letI : ValuativeExtension A (Localization.Away s) := ⟨fun _ _ => Iff.rfl⟩
  -- Positivity of algebraMap s in B = Localization.Away s.
  have hs_alg_pos : (0 : Localization.Away s) <ᵥ
      algebraMap A (Localization.Away s) s := hws
  -- Positivity of s in A under comap (uses ValuativeExtension's Iff.rfl).
  have hs_A_pos : (0 : A) <ᵥ s := by
    change ¬ s ≤ᵥ (0 : A)
    rw [(ValuativeExtension.vle_iff_vle (A := A) (B := Localization.Away s) s 0).symm,
      map_zero]
    exact hws
  -- Positivity of s^k in A:
  have hs_A_pow_pos : ∀ k : ℕ, (0 : A) <ᵥ s ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact (ValuativeRel.posSubmonoid A).one_mem
    | succ n ih => rw [pow_succ]; exact ValuativeRel.zero_vlt_mul ih hs_A_pos
  -- Positivity of (algebraMap s)^k in B:
  have hs_alg_pow_pos : ∀ k : ℕ, (0 : Localization.Away s) <ᵥ
      (algebraMap A (Localization.Away s) s) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact (ValuativeRel.posSubmonoid (Localization.Away s)).one_mem
    | succ n ih => rw [pow_succ]; exact ValuativeRel.zero_vlt_mul ih hs_alg_pos
  intro γ
  induction γ using ValuativeRel.ValueGroupWithZero.ind with
  | mk b₁ b₂ =>
    set rec1 := IsLocalization.Away.sec s b₁
    set rec2 := IsLocalization.Away.sec s (b₂ : Localization.Away s)
    have h1 : b₁ * algebraMap A (Localization.Away s) (s ^ rec1.2) =
        algebraMap A (Localization.Away s) rec1.1 :=
      IsLocalization.Away.sec_spec s b₁
    have h2 : (b₂ : Localization.Away s) *
        algebraMap A (Localization.Away s) (s ^ rec2.2) =
        algebraMap A (Localization.Away s) rec2.1 :=
      IsLocalization.Away.sec_spec s _
    -- Positivity of rec2.1 = a₂ in A: from b₂.property + hs positivity + h2.
    have hrec2_pos : (0 : A) <ᵥ rec2.1 := by
      -- Goal in A: ¬ rec2.1 ≤ᵥ 0. Via ValuativeExtension: ¬ algebraMap rec2.1 ≤ᵥ 0 in B.
      change ¬ rec2.1 ≤ᵥ (0 : A)
      rw [(ValuativeExtension.vle_iff_vle
        (A := A) (B := Localization.Away s) rec2.1 0).symm, map_zero, ← h2, map_pow]
      -- Goal: ¬ b₂ * (algebraMap s)^rec2.2 ≤ᵥ 0 in B.
      exact ValuativeRel.zero_vlt_mul b₂.property (hs_alg_pow_pos rec2.2)
    -- c := rec2.1 * s^rec1.2 ∈ posSubmonoid A.
    have hc_pos : (0 : A) <ᵥ rec2.1 * s ^ rec1.2 :=
      ValuativeRel.zero_vlt_mul hrec2_pos (hs_A_pow_pos rec1.2)
    -- Build the preimage: mk a c with a := rec1.1 * s^rec2.2, c := ⟨rec2.1 * s^rec1.2, hc_pos⟩.
    refine ⟨ValuativeRel.ValueGroupWithZero.mk
      (rec1.1 * s ^ rec2.2) ⟨rec2.1 * s ^ rec1.2, hc_pos⟩, ?_⟩
    -- Both sides of the `sound` goal equal `algebraMap (rec1.1 * rec2.1)`.
    have hLHS : algebraMap A (Localization.Away s) (rec1.1 * s ^ rec2.2) *
        (b₂ : Localization.Away s) =
        algebraMap A (Localization.Away s) (rec1.1 * rec2.1) := by
      rw [map_mul, show algebraMap A (Localization.Away s) rec1.1 *
          algebraMap A (Localization.Away s) (s ^ rec2.2) *
          (b₂ : Localization.Away s) =
        algebraMap A (Localization.Away s) rec1.1 *
          ((b₂ : Localization.Away s) *
            algebraMap A (Localization.Away s) (s ^ rec2.2)) from by ring, h2, ← map_mul]
    have hRHS : b₁ * algebraMap A (Localization.Away s) (rec2.1 * s ^ rec1.2) =
        algebraMap A (Localization.Away s) (rec1.1 * rec2.1) := by
      rw [map_mul, show b₁ * (algebraMap A (Localization.Away s) rec2.1 *
          algebraMap A (Localization.Away s) (s ^ rec1.2)) =
        (b₁ * algebraMap A (Localization.Away s) (s ^ rec1.2)) *
          algebraMap A (Localization.Away s) rec2.1 from by ring, h1, ← map_mul]
    -- Apply mapValueGroupWithZero_mk and reduce to mk equality.
    rw [ValuativeExtension.mapValueGroupWithZero_mk]
    apply ValuativeRel.ValueGroupWithZero.sound
    · show algebraMap A (Localization.Away s) (rec1.1 * s ^ rec2.2) *
          (b₂ : Localization.Away s) ≤ᵥ b₁ *
        algebraMap A (Localization.Away s) (rec2.1 * s ^ rec1.2)
      rw [hLHS, hRHS]
    · show b₁ * algebraMap A (Localization.Away s) (rec2.1 * s ^ rec1.2) ≤ᵥ
        algebraMap A (Localization.Away s) (rec1.1 * s ^ rec2.2) *
        (b₂ : Localization.Away s)
      rw [hLHS, hRHS]

/-- **Concrete MulArchimedean transfer for the localization** (T019).

Composes the surjectivity (`mapValueGroupWithZero_surjective_of_localization`)
+ Mathlib's strict monotonicity (`mapValueGroupWithZero_strictMono`) +
the inversion lemma (`strictMonoHom_inverse_of_bijective`) +
`MulArchimedean.comap` (Mathlib) to produce the per-`w` MulArchimedean
transfer `MulArchimedean (VG A) → MulArchimedean (VG (Localization.Away s))`.

**Coercion choice**: `mapValueGroupWithZero` returns `→*₀`
(`MonoidWithZeroHom`); we extract the underlying `→*` via the
`.toMonoidHom` projection (since `MonoidWithZeroHom` extends `MonoidHom`).
The strict-mono property carries over since the underlying function
is the same.

This is the per-`w` discharger needed by
`mulArchimedean_localization_comap_via_strictMono_hom` (commit
`fa682a5`). -/
theorem mulArchimedean_localization_comap_transfer_concrete
    (s : A) (w : Spv (Localization.Away s))
    (hws : ¬ w.vle (algebraMap A (Localization.Away s) s) 0) :
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    letI : ValuativeRel A :=
      (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
    MulArchimedean (ValuativeRel.ValueGroupWithZero A) →
      MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)) := by
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  letI : ValuativeRel A :=
    (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
  letI : ValuativeExtension A (Localization.Away s) := ⟨fun _ _ => Iff.rfl⟩
  intro hArch_A
  -- The forward map (`→*₀`) from Mathlib, as a `→*`.
  let g : ValuativeRel.ValueGroupWithZero A →*
      ValuativeRel.ValueGroupWithZero (Localization.Away s) :=
    (ValuativeExtension.mapValueGroupWithZero A (Localization.Away s)).toMonoidHom
  -- Invert it (strict mono from Mathlib + surjectivity from above) and apply `comap`.
  obtain ⟨f, hf⟩ := strictMonoHom_inverse_of_bijective g
    ValuativeExtension.mapValueGroupWithZero_strictMono
    (mapValueGroupWithZero_surjective_of_localization s w hws)
  exact MulArchimedean.comap f hf

/-- **No-`hws` wrapper for the MulArchimedean transfer**.

`hws : ¬ w.vle (algebraMap A (Localization.Away s) s) 0` is automatic
since `algebraMap A (Localization.Away s) s` is a unit in the away
localization (`IsLocalization.Away.algebraMap_isUnit`), and units are
non-zero at any valuation (`not_vle_zero_of_isUnit`).

This wrapper is the callsite-ready form: just takes `w` and produces
the MulArchimedean transfer. -/
theorem mulArchimedean_localization_comap_transfer_unit
    (s : A) (w : Spv (Localization.Away s)) :
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    letI : ValuativeRel A :=
      (comap (algebraMap A (Localization.Away s)) w).toValuativeRel
    MulArchimedean (ValuativeRel.ValueGroupWithZero A) →
      MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)) :=
  mulArchimedean_localization_comap_transfer_concrete s w
    (not_vle_zero_of_isUnit (IsLocalization.Away.algebraMap_isUnit _) w)

/-! ### T211: localized `hArch` supplier from global `hArch`

Item 7 of T206's missing-input list (`WedhornMultiDominatingUnit.lean`)
is the per-`w` MulArchimedean condition on
`Spv (Localization.Away s)`. T211 below produces a callsite-ready
supplier from the global `hArch` on `Spv A`, by composing the
scaffold theorem `hArch_loc_via_value_group_iso`
(`Adic spaces/WedhornLocalizedArchimedeanTransfer.lean:73`) with the
fully-discharged per-`w` value-group transfer
`mulArchimedean_localization_comap_transfer_unit` (above, line 419).

Both pieces already exist; T211 is the short composition that gives
T206 its `hArch_loc` argument from the same `hArch` already used at
the `Cor732.exists_dominating_unit` callsite, with no further
mathematical input. -/

/-- **T211 localized `hArch` supplier**.

From the global `hArch : ∀ v : Spv A, MulArchimedean (ValueGroupWithZero
A)` (under `v.toValuativeRel`), produces the localized variant
`∀ w : Spv (Localization.Away s), MulArchimedean (ValueGroupWithZero
(Localization.Away s))` (under `w.toValuativeRel`) — exactly the
shape required by T206's `hArch_loc` input.

**Proof**: pointwise application of `hArch_loc_via_value_group_iso`
with the value-group transfer
`mulArchimedean_localization_comap_transfer_unit s w` (per-`w`
discharger that uses the unit-ness of `algebraMap s` in
`Localization.Away s` for the non-degeneracy precondition `hws`). -/
theorem hArch_loc_via_global_arch_localization
    [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    ∀ w : Spv (Localization.Away s),
      letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)) :=
  hArch_loc_via_value_group_iso P T s hopen hArch
    (fun w => mulArchimedean_localization_comap_transfer_unit s w)

end ValuationSpectrum
