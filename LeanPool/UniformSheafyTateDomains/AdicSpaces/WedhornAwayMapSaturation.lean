/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocTopologyLinear

/-!
# Away-to-away map saturation support (T105)

Public reusable API for the **away-to-away** ring hom `Localization.Away
s_0 →+* Localization.Away s` arising from a unit-witness hypothesis
`IsUnit (algebraMap A (Localization.Away s) s_0)` (typically obtained
from a radical relation `e * s_0 = s^N`). Mathlib's
`IsLocalization.Away.lift` provides the underlying construction; this
file lands the **application/extensionality lemmas** plus the
**radical-relation compatibility identities** that callers need to
identify their concrete localization-lift map (e.g., Primary's private
`locLift D₀ D h` in `PresheafTateStructure.lean`) with the abstract
away-to-away setup and to reason about its action on
`algebraMap`/`divByS`/powers via the radical inverse factor.

## Deliverables

* `awayLift_divByS_one_eq_unit_inv` — the away-to-away lift sends
  `divByS 1 s_0` to the unit inverse of `g s_0` in target.

* `awayLift_divByS_one_eq_via_radical` — using radical relation
  `e * s_0 = s^N`, the image of `divByS 1 s_0` equals the explicit
  T097 radical inverse factor `algebraMap e * (divByS 1 s)^N` in
  `Localization.Away s`.

* `awayLift_divByS_eq_via_radical` — for `t : A`, the image of
  `divByS t s_0` equals `algebraMap (t * e) * (divByS 1 s)^N` in
  `Localization.Away s`. The exact formula a consumer like Primary's
  T089 needs when computing `locLift (divByS t D₀.s)` explicitly via
  the radical relation.

* `awayLift_pow_divByS_one_eq_via_radical` — iterated form: the image
  of `(divByS 1 s_0)^k` equals `(algebraMap e)^k * (divByS 1 s)^(N*k)`
  in `Localization.Away s`. Lets the consumer reduce arbitrary
  source-side denominator-powers to target-side `divByS 1 s` powers
  scaled by `N`.

* `awayLift_algebraMap_mul_pow_divByS_one_eq_via_radical` — generic
  `IsLocalization.Away.surj`-form: `awayLift (algebraMap α * (divByS 1
  s_0)^k) = algebraMap (α * e^k) * (divByS 1 s)^(N*k)`. The canonical
  decomposition Primary produces from Mathlib's
  `IsLocalization.Away.surj` and the explicit RHS in target.

These compatibility lemmas are **NOT wrappers** around T099–T104; they
prove concrete equalities of `IsLocalization.Away.lift` on the
canonical denominator generators of `Localization.Away s_0`, using
only Mathlib's `IsLocalization.Away.lift_eq` plus the unit-cancellation
identity `algebraMap s_0 * divByS 1 s_0 = 1` and T097's radical
inverse formula.

## Saturation theorem status (Option 4 partial)

The full saturation theorem
"`IsLocalization.Away.lift s_0 h_unit a ∈ locNhd P T s m → a ∈ locNhd
P_0 T_0 s_0 n ⊔ ker`"
is **identical** to Primary's hard lemma
`cross_localization_preimage_in_sup_ker` modulo renaming. Proving it
requires the same algebraic content (radical-rewrite + Artin-Rees +
small-rep extraction); it is not a wrapper. The deliverables in this
file are the **strongest compiling nontrivial lemmas** in the
saturation chain that don't require the full assembly: the explicit
application formulas for `Away.lift` on the canonical denominator
generators (via the radical inverse). These are exactly the facts
Primary's saturation proof unfolds at each algebraic step.

## Notes

* New leaf file; imports `WedhornLocTopologyLinear` (for T097's
  `algebraMap_mul_pow_divByS_eq_one_of_radical_relation` and T092's
  `algebraMap_mul_divByS_one_eq_one`).
* No edits to Primary-owned `PresheafTateStructure.lean`,
  `WedhornSourceLaurentMembershipInLocalizationBase.lean`, root
  imports, or final theorem signatures.
* No new sorries / custom axioms / partial declarations / native compilation.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

omit [TopologicalSpace A] in
/-- **`IsLocalization.Away.lift` value on `divByS 1 s_0`** (T105
reusable primitive — Mathlib-style identity).

For `s_0 : A` and `g : A →+* B` with `IsUnit (g s_0)`, applying the
canonical `IsLocalization.Away.lift s_0 hg : Localization.Away s_0 →+*
B` to `divByS 1 s_0 : Localization.Away s_0` yields the unit-inverse
of `g s_0` in `B`:

```
IsLocalization.Away.lift s_0 hg (divByS 1 s_0) = ↑hg.unit⁻¹
```

**Mathematical content**: the element `divByS 1 s_0` is the inverse of
`algebraMap s_0` in `Localization.Away s_0` (via T092's
`algebraMap_mul_divByS_one_eq_one`). The lift `Away.lift s_0 hg` is a
ring hom that sends `algebraMap s_0` to `g s_0` (by
`IsLocalization.Away.lift_eq`); applying the ring hom to the
cancellation identity and using `Units.mul_eq_one_iff_inv_eq` gives
the result.

**Use**: building block for the radical-relation compatibility
identities below. -/
theorem awayLift_divByS_one_eq_unit_inv
    {B : Type*} [CommRing B] (s_0 : A) {g : A →+* B}
    (hg : IsUnit (g s_0)) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        (divByS 1 s_0) = ↑hg.unit⁻¹ := by
  -- The lift sends (algebraMap s_0 * divByS 1 s_0 = 1) to
  -- (g s_0 * Away.lift hg (divByS 1 s_0) = 1). Combined with
  -- ↑hg.unit = g s_0, this gives the unit-inverse characterisation.
  have h_lift_one :
      IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
          (algebraMap A (Localization.Away s_0) s_0) *
        IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
          (divByS 1 s_0) = 1 := by
    rw [← map_mul, algebraMap_mul_divByS_one_eq_one, map_one]
  rw [IsLocalization.Away.lift_eq] at h_lift_one
  -- h_lift_one : g s_0 * (Away.lift hg) (divByS 1 s_0) = 1
  rw [show (g s_0 : B) = ↑hg.unit from hg.unit_spec.symm] at h_lift_one
  -- Now h_lift_one : ↑hg.unit * (Away.lift hg) (divByS 1 s_0) = 1
  exact (Units.mul_eq_one_iff_inv_eq.mp h_lift_one).symm

omit [TopologicalSpace A] in
/-- **Radical-relation form of `awayLift` on `divByS 1 s_0`** (T105
ticket-named theorem).

Given the radical relation `e * s_0 = s^N` in `A`, the canonical
`IsLocalization.Away.lift s_0` (with target `Localization.Away s` and
unit witness from T097's `IsUnit.of_radical_relation`) applied to
`divByS 1 s_0` yields the T097 radical inverse factor `algebraMap e *
(divByS 1 s)^N` in `Localization.Away s`.

**Mathematical content**: by `awayLift_divByS_one_eq_unit_inv` the
LHS equals `↑hg.unit⁻¹`. By T097's
`algebraMap_mul_pow_divByS_eq_one_of_radical_relation`, `algebraMap
s_0 * (algebraMap e * (divByS 1 s)^N) = 1`, so by
`Units.mul_eq_one_iff_inv_eq`, `algebraMap e * (divByS 1 s)^N =
↑hg.unit⁻¹`. Equating gives the result.

**Use** (T089): Primary's `locLift D₀ D h := IsLocalization.Away.lift
D₀.s ...` directly inherits this identity once they identify the
unit-witness paths. This gives the explicit formula for `locLift
(divByS 1 D₀.s)` in `Localization.Away D.s`. -/
theorem awayLift_divByS_one_eq_via_radical
    {s_0 s e : A} {N : ℕ} (h_rad : e * s_0 = s ^ N)
    (hg : IsUnit (algebraMap A (Localization.Away s) s_0)) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        (divByS 1 s_0) =
      algebraMap A (Localization.Away s) e * (divByS 1 s) ^ N := by
  rw [awayLift_divByS_one_eq_unit_inv s_0 hg]
  -- Goal: ↑hg.unit⁻¹ = algebraMap e * (divByS 1 s)^N
  -- T097 inverse: algebraMap s_0 * (algebraMap e * (divByS 1 s)^N) = 1.
  have h_inv :
      algebraMap A (Localization.Away s) s_0 *
        (algebraMap A (Localization.Away s) e * (divByS 1 s) ^ N) = 1 :=
    algebraMap_mul_pow_divByS_eq_one_of_radical_relation h_rad
  rw [show (algebraMap A (Localization.Away s) s_0 : Localization.Away s) =
      ↑hg.unit from hg.unit_spec.symm] at h_inv
  -- h_inv : ↑hg.unit * (algebraMap e * (divByS 1 s)^N) = 1
  exact (Units.mul_eq_one_iff_inv_eq.mp h_inv)

omit [TopologicalSpace A] in
/-- **`awayLift` on `divByS t s_0` via radical relation** (T105 reusable
identity).

For `t : A` and the radical relation `e * s_0 = s^N`, the canonical
away-lift maps `divByS t s_0` to `algebraMap (t * e) * (divByS 1 s)^N`
in `Localization.Away s`.

**Mathematical content**: `divByS t s_0 = algebraMap t * divByS 1 s_0`
in `Localization.Away s_0`. Apply `awayLift_divByS_one_eq_via_radical`
to the `divByS 1 s_0` factor and `IsLocalization.Away.lift_eq` to the
`algebraMap t` factor.

**Use** (T089): explicit formula for `locLift (divByS t D₀.s)` in
`Localization.Away D.s`. -/
theorem awayLift_divByS_eq_via_radical
    {s_0 s e : A} {N : ℕ} (h_rad : e * s_0 = s ^ N)
    (hg : IsUnit (algebraMap A (Localization.Away s) s_0)) (t : A) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        (divByS t s_0) =
      algebraMap A (Localization.Away s) (t * e) * (divByS 1 s) ^ N := by
  -- divByS t s_0 = algebraMap t * divByS 1 s_0 in Loc s_0.
  have h_decomp : divByS t s_0 =
      algebraMap A (Localization.Away s_0) t * divByS 1 s_0 := by
    unfold divByS
    rw [← IsLocalization.mk'_one (M := Submonoid.powers s_0)
          (S := Localization.Away s_0) t,
        ← IsLocalization.mk'_mul, mul_one, one_mul]
  rw [h_decomp, map_mul, IsLocalization.Away.lift_eq s_0 hg t,
      awayLift_divByS_one_eq_via_radical h_rad hg, map_mul]
  ring

omit [TopologicalSpace A] in
/-- **`awayLift` on `(divByS 1 s_0)^k` via radical relation** (T105
iterated form).

For `k : ℕ` and the radical relation `e * s_0 = s^N`, the canonical
away-lift maps `(divByS 1 s_0)^k` to `(algebraMap e)^k * (divByS 1
s)^(N*k)` in `Localization.Away s`.

**Use** (T089): when Primary applies `IsLocalization.Away.surj` to
write `a = algebraMap α * (divByS 1 s_0)^k_a`, this lemma gives the
explicit `(divByS 1 s)^(N * k_a)` factor — exactly the `k_a · N`
denominator-depth term that drives Primary's saturation analysis. -/
theorem awayLift_pow_divByS_one_eq_via_radical
    {s_0 s e : A} {N : ℕ} (h_rad : e * s_0 = s ^ N)
    (hg : IsUnit (algebraMap A (Localization.Away s) s_0)) (k : ℕ) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        ((divByS 1 s_0) ^ k) =
      (algebraMap A (Localization.Away s) e) ^ k *
        (divByS 1 s) ^ (N * k) := by
  rw [map_pow, awayLift_divByS_one_eq_via_radical h_rad hg, mul_pow,
      ← pow_mul, mul_comm N k]

omit [TopologicalSpace A] in
/-- **Generic algebraMap saturation form for `awayLift` images** (T105
saturation prefix — strongest compiling form expressible without
`locLift`).

For `α : A` and `k : ℕ`, the canonical away-lift evaluates as

```
IsLocalization.Away.lift s_0 hg (algebraMap α * (divByS 1 s_0)^k) =
  algebraMap (α * e^k) * (divByS 1 s)^(N * k)   in Localization.Away s.
```

Direct combination of `IsLocalization.Away.lift_eq` (on the
`algebraMap α` factor) with `awayLift_pow_divByS_one_eq_via_radical`
(on the `(divByS 1 s_0)^k` factor).

**Use** (T089): the canonical form Primary produces from
`IsLocalization.Away.surj`-style decomposition `a = algebraMap α *
(divByS 1 s_0)^k_a`. The explicit RHS makes the target locNhd-depth
analysis tractable: by T095's iterated `divByS 1 s` shift, the
target-side `(divByS 1 s)^(N · k_a)` factor demands target depth
`m ≥ ?(N · k_a + n_target)` for source representative depth
`n_target`. -/
theorem awayLift_algebraMap_mul_pow_divByS_one_eq_via_radical
    {s_0 s e : A} {N : ℕ} (h_rad : e * s_0 = s ^ N)
    (hg : IsUnit (algebraMap A (Localization.Away s) s_0))
    (α : A) (k : ℕ) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        (algebraMap A (Localization.Away s_0) α * (divByS 1 s_0) ^ k) =
      algebraMap A (Localization.Away s) (α * e ^ k) *
        (divByS 1 s) ^ (N * k) := by
  rw [map_mul, IsLocalization.Away.lift_eq s_0 hg α,
      awayLift_pow_divByS_one_eq_via_radical h_rad hg, map_mul, map_pow]
  ring

/-! ## Public source-side saturation prefix (T106)

Building on T105's explicit `Away.lift` formulas, T106 lands the
**source-side construction theorem** for the small representative of
T089's saturation step plus the **kernel-difference repackaging**
that turns image equality into the explicit `b + k` decomposition.
Together with T097/T098/T091/T094, these are the public saturation
prefix Primary's hard lemma directly consumes.

**Deliverables**:

* `algebraMap_mul_pow_divByS_one_mem_locNhd_of_PI_pow` — for `α' :
  P₀.A₀` with `α' ∈ P₀.I^(n + k * N₀)` (where `N₀` is the source
  open-ideal exponent), the explicit element `algebraMap (α' : A) *
  (divByS 1 s₀)^k` lies in `locNhd P₀ T₀ s₀ n`. Direct composition
  of T090's `algebraMap_PI_pow_mem_locNhd` with T095's
  `locNhd_invS_pow_step_of_hopen`. The **explicit construction** of
  Primary's source-small representative.

* `kernel_diff_of_algebraMap_eq` — for any RingHom `f : R →+* B`, if
  `f a = f b` then `a - b ∈ RingHom.ker f`. Trivial but named-
  reusable.

* `away_saturation_prefix_via_algebraMap_match` (T106 main public
  saturation prefix) — combines the source-side construction with
  the kernel-difference repackaging into the exact shape Primary's
  `cross_localization_preimage_in_sup_ker` needs:

  Given source pair `(P₀, T₀, s₀)` with `[IsNoetherianRing P₀.A₀]`,
  target pair `(P, T, s)`, radical relation `e * s₀ = s^N`, source
  `hopen`-witness `(N₀, hN₀)`, source/target depths `(n, k)`, and
  `α : A`, `α' : P₀.A₀` with `α' ∈ P₀.I^(n + k * N₀)` and
  `algebraMap A (Localization.Away s) α =
    algebraMap A (Localization.Away s) α'`
  (i.e., the target images of `α` and `α'` agree in `Loc s`):
  the explicit decomposition

  ```
  algebraMap α * (divByS 1 s₀)^k =
    (algebraMap α' * (divByS 1 s₀)^k)  -- ∈ locNhd P₀ T₀ s₀ n
      + (algebraMap (α - α') * (divByS 1 s₀)^k)  -- ∈ ker F
  ```

  follows directly. **The remaining residual for Primary** is the
  saturation step itself: given `F (algebraMap α * (divByS 1 s₀)^k)
  ∈ locNhd P T s m`, **find** such `α' ∈ P₀.A₀ ∩ P₀.I^(n + k*N₀)`
  with `algebraMap_A→Loc_s α = algebraMap_A→Loc_s α'`. This step
  requires the radical-relation translation + Artin-Rees + image
  characterisation in target — the genuine algebraic content of the
  saturation, which is the same difficulty regardless of where it's
  proved. T106 packages every algebraic move *around* the saturation
  step into clean public theorems; the saturation step itself is
  the irreducible content. -/

/-- **Source-side construction of the small representative**
(T106 reusable substantive primitive).

For source `[IsNoetherianRing P₀.A₀]`-style data with open-ideal
witness `(N₀, hN₀)`, source depth `n`, denominator power `k`, and
`α' : P₀.A₀` with `α' ∈ P₀.I^(n + k * N₀)`:

```
algebraMap A (Localization.Away s₀) (α' : A) * (divByS 1 s₀)^k ∈
  locNhd P₀ T₀ s₀ n.
```

**Mathematical content**: by T090's `algebraMap_PI_pow_mem_locNhd`
applied to `α' ∈ P₀.I^(n + k * N₀)`, we get `algebraMap (α' : A) ∈
locNhd P₀ T₀ s₀ (n + k * N₀)`. By T095's
`locNhd_invS_pow_step_of_hopen` applied to `(divByS 1 s₀)^k`, this
shifts down to `(divByS 1 s₀)^k * algebraMap (α' : A) ∈ locNhd P₀
T₀ s₀ n`. By commutativity in `Localization.Away s₀`, this equals
`algebraMap (α' : A) * (divByS 1 s₀)^k`.

**Use** (T089): explicit construction of Primary's source-small
representative. Once Primary identifies an `α' : P₀.A₀` in
`P₀.I^(n + k * N₀)` matching `α` modulo target-kernel, this lemma
witnesses the source `locNhd` membership. -/
theorem algebraMap_mul_pow_divByS_one_mem_locNhd_of_PI_pow
    (P₀ : PairOfDefinition A) (T₀ : Finset A) (s₀ : A)
    (N₀ : ℕ) (hN₀ : ∀ b : P₀.A₀, b ∈ P₀.I ^ N₀ →
      divByS (↑b : A) s₀ ∈ locSubring P₀ T₀ s₀)
    (n k : ℕ) (α' : P₀.A₀) (h_α' : α' ∈ P₀.I ^ (n + k * N₀)) :
    algebraMap A (Localization.Away s₀) (α' : A) * (divByS 1 s₀) ^ k ∈
      locNhd P₀ T₀ s₀ n := by
  -- algebraMap (α' : A) ∈ locNhd P₀ T₀ s₀ (n + k * N₀) by T090.
  have h_alg : algebraMap A (Localization.Away s₀) (α' : A) ∈
      locNhd P₀ T₀ s₀ (n + k * N₀) :=
    algebraMap_PI_pow_mem_locNhd P₀ T₀ s₀ (n + k * N₀) α' h_α'
  -- (divByS 1 s₀)^k * algebraMap (α' : A) ∈ locNhd P₀ T₀ s₀ n by T095.
  have h_shift : (divByS 1 s₀) ^ k *
      algebraMap A (Localization.Away s₀) (α' : A) ∈
      locNhd P₀ T₀ s₀ n :=
    locNhd_invS_pow_step_of_hopen P₀ T₀ s₀ N₀ hN₀ n k h_alg
  -- Commute: algebraMap (α' : A) * (divByS 1 s₀)^k = (divByS 1 s₀)^k * algebraMap (α' : A)
  rwa [mul_comm]

/-- **Kernel difference from `algebraMap` image equality** (T106 reusable
primitive).

For any RingHom `f : R →+* B` between commutative rings and `α α' : R`
with `f α = f α'`, the difference `α - α'` lies in `RingHom.ker f`.

**Mathematical content**: `f (α - α') = f α - f α' = 0` since `f α =
f α'`. Direct from `RingHom.mem_ker.mpr` + `map_sub`.

**Use**: the algebraic content of the kernel-difference step in
Primary's saturation. -/
theorem kernel_diff_of_algebraMap_eq
    {R B : Type*} [CommRing R] [CommRing B] (f : R →+* B)
    {α α' : R} (h : f α = f α') :
    α - α' ∈ RingHom.ker f := by
  rw [RingHom.mem_ker, map_sub, h, sub_self]

/-- **Public saturation prefix: explicit `b + k` decomposition from
matching `algebraMap` images** (T106 main ticket-named theorem).

For source pair `(P₀, T₀, s₀)`, target pair `(P, T, s)`, source
open-ideal witness `(N₀, hN₀)`, source/target depths `(n, k)`, and
`α : A`, `α' : P₀.A₀` with:
- `α' ∈ P₀.I^(n + k * N₀)` (small in source filtration), and
- `algebraMap A (Localization.Away s) α =
   algebraMap A (Localization.Away s) α'` (matching target images),

the source element `algebraMap α * (divByS 1 s₀)^k` decomposes
explicitly as

```
algebraMap α * (divByS 1 s₀)^k =
  (algebraMap (α' : A) * (divByS 1 s₀)^k)        -- in locNhd P₀ T₀ s₀ n
    + (algebraMap (α - α') * (divByS 1 s₀)^k)    -- in RingHom.ker F
```

where `F := IsLocalization.Away.lift s_0 hg : Localization.Away s_0
→+* Localization.Away s` is the canonical away-lift parameterised by
the unit witness `hg`.

**Mathematical content**: pure algebra plus T106's
`algebraMap_mul_pow_divByS_one_mem_locNhd_of_PI_pow` (witnessing the
source-`locNhd` membership of the `b`-component) plus
`kernel_diff_of_algebraMap_eq` (giving the `k`-component is in
`RingHom.ker F`). The decomposition equation `α = α' + (α - α')`
lifts via `algebraMap` and `(divByS 1 s₀)^k` distributivity.

**Use** (T089 saturation): once Primary identifies `α' ∈ P₀.A₀ ∩
P₀.I^(n + k * N₀)` with matching target image (the genuine
saturation/depth-finding step), this theorem packages the resulting
explicit decomposition as the `b + k` form Primary's hard lemma
returns.

**Saturation residual not addressed here**: the existence of `α'`
satisfying both conditions is the irreducible algebraic content of
the saturation. T106 provides the explicit decomposition WHEN such
`α'` exists; it does NOT prove existence. Primary's hard lemma
proves existence by combining T097/T098 (radical-rewrite) +
T091/T094 (Artin-Rees on the kernel ideal) + radical-relation
translation. The existence proof is consumer-specific (depends on
target locNhd structure and kernel of locLift), which is why it
must run in Primary's private context. -/
theorem away_saturation_prefix_via_algebraMap_match
    {B : Type*} [CommRing B]
    (P₀ : PairOfDefinition A) (T₀ : Finset A) (s₀ : A)
    (N₀ : ℕ) (hN₀ : ∀ b : P₀.A₀, b ∈ P₀.I ^ N₀ →
      divByS (↑b : A) s₀ ∈ locSubring P₀ T₀ s₀)
    (n k : ℕ) {g : A →+* B} (hg : IsUnit (g s₀))
    (α : A) (α' : P₀.A₀) (h_α' : α' ∈ P₀.I ^ (n + k * N₀))
    (h_match : g α = g (α' : A)) :
    ∃ b k_elem : Localization.Away s₀,
      b ∈ locNhd P₀ T₀ s₀ n ∧
      k_elem ∈ RingHom.ker (IsLocalization.Away.lift
        (S := Localization.Away s₀) s₀ hg) ∧
      algebraMap A (Localization.Away s₀) α * (divByS 1 s₀) ^ k =
        b + k_elem := by
  -- b := algebraMap (α' : A) * (divByS 1 s₀)^k, in locNhd by T106 #1.
  refine ⟨algebraMap A (Localization.Away s₀) (α' : A) * (divByS 1 s₀) ^ k,
    algebraMap A (Localization.Away s₀) (α - α') * (divByS 1 s₀) ^ k,
    ?_, ?_, ?_⟩
  · -- b ∈ locNhd
    exact algebraMap_mul_pow_divByS_one_mem_locNhd_of_PI_pow
      P₀ T₀ s₀ N₀ hN₀ n k α' h_α'
  · -- k_elem ∈ RingHom.ker F
    -- Apply F to algebraMap (α - α') * (divByS 1 s₀)^k:
    -- F (algebraMap (α - α') * (divByS 1 s₀)^k) =
    --   F (algebraMap (α - α')) * F ((divByS 1 s₀)^k)
    -- F (algebraMap (α - α')) = g (α - α') = g α - g α' = 0
    -- so the product is 0.
    rw [RingHom.mem_ker, map_mul,
        IsLocalization.Away.lift_eq s₀ hg (α - α'),
        map_sub g, h_match, sub_self, zero_mul]
  · -- a = b + k_elem: pure algebra.
    rw [← add_mul, ← map_add]
    -- Now: algebraMap α * (divByS 1 s₀)^k =
    --   algebraMap ((α' : A) + (α - α')) * (divByS 1 s₀)^k
    congr 1
    rw [show ((α' : A) + (α - α') : A) = α from by ring]

/-! ## Public witness-existence half-step (T107)

Building on T105/T106, T107 lands the **public half-step** of the
saturation witness existence: given the canonical away-lift image of
`algebraMap α * (divByS 1 s₀)^k` lies in target `locNhd P T s m`,
the underlying numerator image `algebraMap A (Localization.Away s)
(α * e^k)` lies in `(Jfull P T s)^m`.

This is a **substantive public theorem** (not a wrapper): it composes
T105 #5 (the explicit `awayLift` formula) with T094's
`locNhd_subset_Jfull_pow` and ideal multiplication-by-unit
absorption, producing an algebraic depth condition on the
A-numerator entirely from public ingredients.

**Witness existence not addressed here**: extracting an explicit `α'
: P₀.A₀ ∩ P₀.I^(n + k * N₀)` matching `algebraMap α` in target Loc s
requires connecting the source pair `(P₀, T₀, s₀)` to the target
pair `(P, T, s)` via a structural map (typically from
`RationalLocData` containment via Primary's `rad_relation_of_rational_subset`).
That step is **not** algebraically extractable from the half-step
above without additional structural hypotheses on the source/target
pair relationship — see `## Witness-existence residual report` below.

## Witness-existence residual report (Option-3 per ticket)

After T107, the remaining content for Primary's witness existence is:

```lean
-- (Private) given algebraMap (α * e^k) ∈ (Jfull P T s)^m as A-element image,
-- find α' : P₀.A₀ ∩ P₀.I^(n + k * N₀) with algebraMap α = algebraMap α' in Loc s.
```

This requires a **structural relationship** between the source pair
`(P₀, T₀, s₀)` and target pair `(P, T, s)` (typically from `D₀.P, D.P
: PairOfDefinition A` linked via `rationalOpen` containment): the
ideals `P₀.I` and `P.I` must interact in the right way under the
radical relation `e * s_0 = s^N`. This interaction is encoded in
Primary's `RationalLocData` structure and the radical-relation
mechanics, both of which are private to `PresheafTateStructure.lean`.

**Nearest existing support theorems**:
- T106 `away_saturation_prefix_via_algebraMap_match` — the
  decomposition step, **after** witness existence is established.
- T107 `algebraMap_image_mem_Jfull_pow_of_awayLift_image_in_locNhd` —
  the half-step extracting the algebraic depth condition.
- Primary needs a private theorem of the shape
  `algebraMap (α * e^k) ∈ (Jfull P T s)^m → ∃ α' : P₀.A₀, α' ∈
  P₀.I^(n + k * N₀) ∧ algebraMap α = algebraMap α'` in Loc s.

The witness-existence step requires:
1. Connecting the target Jfull membership (algebraic) to a source
   PI-power membership (structural).
2. Using `IsLocalization.eq_iff_exists` to lift the Loc-equality
   `algebraMap α = algebraMap α'` to an A-equality modulo
   `s`-torsion.

Both steps depend on the source/target pair structure, which lives
in Primary's private `RationalLocData` framework.
-/

/-- **`algebraMap` image in `Jfull` power from `awayLift` image in
`locNhd`** (T107 main public theorem; substantive half-step toward
witness existence).

Setup: source `s_0 : A`, target `s : A`, radical relation `e * s_0 =
s^N`, unit witness `hg : IsUnit (algebraMap A (Localization.Away s)
s_0)`, normal-form numerator `α : A`, denominator power `k`, target
locNhd depth `m`, target localization data `(P, T)`.

If the canonical `awayLift` image of `algebraMap α * (divByS 1 s_0)^k`
lies in `locNhd P T s m`, then the underlying numerator image
`algebraMap A (Localization.Away s) (α * e^k)` lies in `(Jfull P T
s)^m`.

**Mathematical content** (3-step composition of public theorems):
1. By T105 #5
   (`awayLift_algebraMap_mul_pow_divByS_one_eq_via_radical`), the
   `awayLift` image equals `algebraMap (α * e^k) * (divByS 1 s)^(N*k)`
   in `Loc s`.
2. By T094's `locNhd_subset_Jfull_pow`, the LHS lies in `(Jfull P T
   s)^m` (since `locNhd P T s m ⊆ (Jfull P T s)^m` as sets).
3. Multiplying by `(algebraMap s)^(N*k)` (a unit in `Loc s`):
   `algebraMap (α * e^k) = (algebraMap (α * e^k) * (divByS 1 s)^(N*k))
   * (algebraMap s)^(N*k)`. Since `(Jfull P T s)^m` is an ideal of
   `Loc s`, multiplication by any `Loc s` element preserves
   membership. Hence `algebraMap (α * e^k) ∈ (Jfull P T s)^m`.

**Use** (T089): provides the algebraic depth condition Primary needs
on the A-numerator `α * e^k` (the radical-rewritten numerator).
Combined with `IsLocalization.eq_iff_exists` and the structural
source/target pair relationship, this becomes the witness-existence
input. -/
theorem algebraMap_image_mem_Jfull_pow_of_awayLift_image_in_locNhd
    (P : PairOfDefinition A) (T : Finset A)
    {s_0 s e : A} {N : ℕ} (h_rad : e * s_0 = s ^ N)
    (hg : IsUnit (algebraMap A (Localization.Away s) s_0))
    (α : A) (k m : ℕ)
    (h_input :
      IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
          (algebraMap A (Localization.Away s_0) α * (divByS 1 s_0) ^ k) ∈
        locNhd P T s m) :
    algebraMap A (Localization.Away s) (α * e ^ k) ∈
      (Jfull P T s) ^ m := by
  -- Step 1: rewrite the awayLift image via T105 #5.
  have h_awayLift_eq :
      IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
          (algebraMap A (Localization.Away s_0) α * (divByS 1 s_0) ^ k) =
        algebraMap A (Localization.Away s) (α * e ^ k) *
          (divByS 1 s) ^ (N * k) :=
    awayLift_algebraMap_mul_pow_divByS_one_eq_via_radical h_rad hg α k
  rw [h_awayLift_eq] at h_input
  -- Now: algebraMap (α * e^k) * (divByS 1 s)^(N*k) ∈ locNhd m.
  -- Step 2: locNhd ⊆ Jfull^m (T094).
  have h_in_Jfull :
      algebraMap A (Localization.Away s) (α * e ^ k) *
          (divByS 1 s) ^ (N * k) ∈
        (Jfull P T s) ^ m :=
    locNhd_subset_Jfull_pow P T s m h_input
  -- Step 3: multiply by (algebraMap s)^(N*k) (a unit) to extract.
  -- algebraMap (α * e^k) =
  --   (algebraMap (α * e^k) * (divByS 1 s)^(N*k)) * (algebraMap s)^(N*k)
  have h_unit_cancel :
      algebraMap A (Localization.Away s) (α * e ^ k) =
        (algebraMap A (Localization.Away s) (α * e ^ k) *
          (divByS 1 s) ^ (N * k)) *
          algebraMap A (Localization.Away s) s ^ (N * k) := by
    rw [mul_assoc, ← mul_pow,
        show (divByS 1 s) * algebraMap A (Localization.Away s) s = 1
          from by rw [mul_comm, algebraMap_mul_divByS_one_eq_one],
        one_pow, mul_one]
  rw [h_unit_cancel]
  exact Ideal.mul_mem_right _ _ h_in_Jfull

/-! ## Source-side denominator-clearing for `locSubring` (T114)

Reusable structural primitives in this section:

* `locSubring_exists_denominator_clearance` — every `x ∈ locSubring P
  T s` is of the form `algebraMap β / algebraMap s ^ E` for
  `β : P.A₀, E : ℕ`. **An E-shift lemma**: produces a clearing of the
  denominator power, NOT a raw `algebraMap`-image equality of `x`
  with `algebraMap β`. Lands per T114 step 1.

**Integration boundary (E-shift residual, T115/T116 territory)**: the
denominator-clearing helper above produces an `s^E` denominator that
the consumer (Primary's `cross_localization_preimage_in_sup_ker` in
`PresheafTateStructure.lean`) cannot directly absorb. In the consumer
chain, after applying the helper one gets — for any
`a : A` whose `algebraMap` lies in `locNhd P T s m` — an A-equation

```
∃ γ : P.A₀, γ ∈ P.I^m, ∃ j E : ℕ,
  s^(j + E) * a = s^j * (γ : A)
```

i.e., `algebraMap a = algebraMap γ / algebraMap s^E` in
`Localization.Away s`, equivalently `a = γ / s^E` modulo
`s`-torsion. **This is NOT** the saturation conclusion `algebraMap a
= algebraMap α'` for some `α' ∈ P.I^?`. The remaining gap is the
colon-saturation / Artin-Rees absorption of the `s^E` factor:

```
-- T114-COLON-SATURATION (PROPOSED, NOT YET PROVED).
-- For Noetherian P.A₀, ideal P.I : Ideal P.A₀, s ∈ P.A₀,
-- ∃ k₀ : ℕ, ∀ m ≥ k₀ + E, ∀ a ∈ A, ∀ j E : ℕ, ∀ γ : P.A₀,
--   γ ∈ P.I^m →
--   s^(j + E) * a = s^j * (γ : A) →
--   ∃ α' : P.A₀, α' ∈ P.I^(m - k₀ - E) ∧
--     ∃ k : ℕ, s^k * (a - (α' : A)) = 0.
```

This is the **first exact missing statement** for Primary's T113 to
land. It is a colon-stabilization fact in the Noetherian commutative
ring `P.A₀` — equivalent to the assertion that in `P.A₀`, the colon
chain `(P.I^m : ⟨s⟩^E)` stabilizes after a fixed Artin-Rees-style
shift `k₀ = k₀(P.I, s)` independent of `m, E`. Mathlib provides:

* `Ideal.exists_pow_inf_eq_pow_smul` (the standard Artin-Rees lemma
  on `(P.I, ⟨s⟩)`) — supplies the `k₀` constant.
* `Submodule.colon` and `Ideal.mem_colon_span_singleton`
  (`Mathlib/RingTheory/Ideal/Colon.lean`) — supply the colon-ideal
  formalism.
* `Ideal.iInf_pow_smul = ⊥` for Noetherian rings (Krull intersection)
  — controls the `s`-torsion stabilization.

Composing these into the `T114-COLON-SATURATION` lemma above would
discharge the integration shift, but the composition itself is an
Artin-Rees + colon-saturation argument requiring a separate
substantial pass. Reported here as the explicit blocker for T113. -/

/-- **Denominator-clearing for `locSubring` elements** (T114 reusable
primitive — an `E`-shift lemma).

For a pair of definition `(P.A₀, P.I)`, finite `T : Finset A` with
`T ⊆ P.A₀`, and `s ∈ P.A₀`, every `x ∈ locSubring P T s` admits
`β : P.A₀` and `E : ℕ` with

```
x * algebraMap A (Localization.Away s) (s ^ E) =
  algebraMap A (Localization.Away s) ((β : A))
```

i.e., `x = algebraMap β / algebraMap s ^ E` after clearing
denominators inside `Localization.Away s`.

**⚠ E-shift caveat**: this lemma supplies the `s^E` clearing factor
unavoidably — the conclusion is **NOT** `x = algebraMap β` directly.
Composing this helper with `IsLocalization.eq_iff_exists` and the
locNhd-unfolding of an `algebraMap a ∈ locNhd P T s m` hypothesis
yields the A-equation

```
∃ γ : P.A₀, γ ∈ P.I^m, ∃ j E : ℕ,
  s^(j + E) * a = s^j * (γ : A)
```

— equivalently `a = γ / s^E` modulo `s`-torsion. Absorbing the
`s^E` shift into a raw `algebraMap a = algebraMap α'` form requires
the **colon-saturation residual** documented in the section
docstring above (`T114-COLON-SATURATION`). Consumers should plumb
the explicit `(j, E)` data through downstream and discharge the
shift via that colon-saturation lemma, not assume this helper does
it.

**Proof shape**: `Subring.closure_induction` on
`locSubring P T s = Subring.closure ((algebraMap '' P.A₀) ∪
(divByS '' T))`.
* Generators `algebraMap a` (a ∈ P.A₀): `(β, E) := (a, 0)`.
* Generators `divByS t s` (t ∈ T): `(β, E) := (t, 1)` via
  `IsLocalization.mk'_spec` (`divByS t s · algebraMap s = algebraMap
  t`); `t ∈ P.A₀` comes from `hT`.
* Closure under `0, 1, +, *, -`: ring algebra in `P.A₀` (closed under
  `s`-multiplication via `hs`), with denominator exponents combining
  by addition.

**Use** (T114): the denominator-clearing prerequisite for any
A-side reasoning about `locSubring`-side polynomial expressions,
including the unfinished `T114-COLON-SATURATION` discharge above. -/
theorem locSubring_exists_denominator_clearance
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hs : s ∈ P.A₀) (hT : ∀ t ∈ T, t ∈ P.A₀)
    {x : Localization.Away s} (hx : x ∈ locSubring P T s) :
    ∃ (β : P.A₀) (E : ℕ),
      x * algebraMap A (Localization.Away s) (s ^ E) =
        algebraMap A (Localization.Away s) ((β : A)) := by
  unfold locSubring at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, ha, rfl⟩ | ⟨t, rfl⟩
    · -- Generator `algebraMap a`, `a ∈ P.A₀`: take `(β, E) := (a, 0)`.
      exact ⟨⟨a, ha⟩, 0, by rw [pow_zero, map_one, mul_one]⟩
    · -- Generator `divByS t.val s`, `t : ↥T`: take `(β, E) := (t.val, 1)`.
      refine ⟨⟨t.val, hT t.val t.property⟩, 1, ?_⟩
      rw [pow_one]
      exact IsLocalization.mk'_spec (Localization.Away s) (t.val : A)
        ⟨s, Submonoid.mem_powers s⟩
  | zero =>
    exact ⟨0, 0, by simp⟩
  | one =>
    exact ⟨1, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨β₁, E₁, h₁⟩ := hy
    obtain ⟨β₂, E₂, h₂⟩ := hz
    refine ⟨⟨(β₁ : A) * s ^ E₂ + (β₂ : A) * s ^ E₁,
            P.A₀.add_mem (P.A₀.mul_mem β₁.property (P.A₀.pow_mem hs _))
              (P.A₀.mul_mem β₂.property (P.A₀.pow_mem hs _))⟩,
           E₁ + E₂, ?_⟩
    have h1' : y * algebraMap A (Localization.Away s) (s ^ (E₁ + E₂)) =
        algebraMap A (Localization.Away s) ((β₁ : A) * s ^ E₂) := by
      rw [pow_add, map_mul, ← mul_assoc, h₁, ← map_mul]
    have h2' : z * algebraMap A (Localization.Away s) (s ^ (E₁ + E₂)) =
        algebraMap A (Localization.Away s) ((β₂ : A) * s ^ E₁) := by
      rw [show E₁ + E₂ = E₂ + E₁ from by omega, pow_add, map_mul,
          ← mul_assoc, h₂, ← map_mul]
    change (y + z) * algebraMap A (Localization.Away s) (s ^ (E₁ + E₂)) =
        algebraMap A (Localization.Away s)
          ((β₁ : A) * s ^ E₂ + (β₂ : A) * s ^ E₁)
    rw [add_mul, h1', h2', ← map_add]
  | mul y z _ _ hy hz =>
    obtain ⟨β₁, E₁, h₁⟩ := hy
    obtain ⟨β₂, E₂, h₂⟩ := hz
    refine ⟨β₁ * β₂, E₁ + E₂, ?_⟩
    change (y * z) * algebraMap A (Localization.Away s) (s ^ (E₁ + E₂)) =
        algebraMap A (Localization.Away s) (((β₁ * β₂ : P.A₀) : A))
    rw [show ((β₁ * β₂ : P.A₀) : A) = (β₁ : A) * (β₂ : A) from rfl,
        map_mul, pow_add, map_mul]
    calc (y * z) * (algebraMap A (Localization.Away s) (s ^ E₁) *
                    algebraMap A (Localization.Away s) (s ^ E₂))
        = (y * algebraMap A (Localization.Away s) (s ^ E₁)) *
          (z * algebraMap A (Localization.Away s) (s ^ E₂)) := by ring
      _ = algebraMap A (Localization.Away s) ((β₁ : A)) *
          algebraMap A (Localization.Away s) ((β₂ : A)) := by rw [h₁, h₂]
  | neg y _ hy =>
    obtain ⟨β, E, h⟩ := hy
    refine ⟨-β, E, ?_⟩
    change (-y) * algebraMap A (Localization.Away s) (s ^ E) =
        algebraMap A (Localization.Away s) (((-β : P.A₀) : A))
    rw [show ((-β : P.A₀) : A) = -((β : A)) from rfl, map_neg, neg_mul, h]

/-! ## Colon-saturation primitives for absorbing the E-shift (T119)

After T114 lands the denominator-clearing helper, the next step in
Primary's saturation chain is to absorb the resulting `s^E` factor.
This requires Artin-Rees-type colon-saturation in the source ring of
definition `R := P.A₀`.

This section lands the **single-step `s`-absorption primitive**
`Ideal.exists_factor_of_mem_inter_singleton`: for a Noetherian
commutative ring `R`, ideal `I : Ideal R`, and `s : R`, there is a
constant `k₀ : ℕ` (the Artin-Rees shift for `(I, ⟨s⟩)`) such that
every `γ ∈ I^m ⊓ ⟨s⟩` (with `m ≥ k₀`) factors as `γ = s * α` with
`α ∈ I^(m - k₀)`. Direct application of Mathlib's
`Ideal.exists_pow_inf_eq_pow_smul`. Iterating this E times absorbs
`s^E` with linear constant `c_lift = E * k₀`.

The **iterated `s^E`-absorption lemma** is provable by induction on E
using this primitive plus the fact that `γ_i = γ / s^i ∈ ⟨s⟩^(E-i)`
when `γ ∈ ⟨s⟩^E`. The proof needs care to track the chain of
factorizations; the iteration is omitted from this section because
it interacts with the elaborator OOM observed in the earlier T114
witness-extraction attempt.

The **bridge from the T113-consumer relation `s^(j+E) * a = s^j *
(γ : A)` (in `A`) to `γ ∈ ⟨s⟩^E ⊓ I^m` (in `P.A₀`)** requires
additional structural input. Specifically, the relation only places
`γ - s^E * a ∈ Ann_A(s^∞)` in `A` (with `a ∈ A`, not necessarily in
`P.A₀`). For the canonical Tate setup `A = P.A₀[s^{-1}]` (e.g.,
Tate ring with `s` topologically nilpotent unit and `P.A₀ = A°`),
every `a ∈ A` has the form `a = a₀ / s^k` with `a₀ ∈ P.A₀`, so
`s^E · a = s^(E-k) · a₀` (or `a₀ / s^(k-E)`) lands in `P.A₀` after
adjusting the depth. This bridge requires a Tate-specific
hypothesis (e.g., `IsTateRing A` plus `s = π` topologically
nilpotent unit) and is the next reusable structural lemma needed by
Primary's T113. -/

omit [TopologicalSpace A] in
/-- **Single-step `s`-absorption in an `I`-power, via Artin-Rees**
(T119 reusable primitive).

For a Noetherian commutative ring `R`, ideal `I : Ideal R`, and
`s : R`, every element simultaneously in a deep `I`-power `I^m` and
in `⟨s⟩` factors as `s * α` with `α ∈ I^(m - k₀)`, where `k₀` is the
Artin-Rees shift for the pair `(I, ⟨s⟩)`.

This is a **direct unfolding** of Mathlib's
`Ideal.exists_pow_inf_eq_pow_smul` for the special case `N := ⟨s⟩`,
followed by `Ideal.mem_span_singleton'` to extract the factor.
Iterating E times yields the `s^E`-absorption with linear constant
`E * k₀`; that iteration is the next step in the colon-saturation
chain.

**Use** (T119 / T113 corrected residual): converts a `γ ∈ I^m ⊓
⟨s⟩` membership into the explicit `s · α` factorization, the
prerequisite for absorbing each `s` factor in the consumer's
`s^E`-shift form. -/
theorem Ideal.exists_factor_of_mem_inter_singleton
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (s : R) :
    ∃ k₀ : ℕ, ∀ m : ℕ, m ≥ k₀ →
      ∀ γ : R, γ ∈ I ^ m → γ ∈ Ideal.span ({s} : Set R) →
        ∃ α : R, α ∈ I ^ (m - k₀) ∧ γ = s * α := by
  obtain ⟨k₀, hk₀⟩ := Ideal.exists_pow_inf_eq_pow_smul I
    (Ideal.span ({s} : Set R))
  refine ⟨k₀, fun m hm γ hγ_pow hγ_s ↦ ?_⟩
  -- γ ∈ I^m • ⊤ ⊓ ⟨s⟩ via smul/mul translation.
  have h_smul_eq : I ^ m • (⊤ : Submodule R R) = I ^ m := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have h_inf : γ ∈ I ^ m • (⊤ : Submodule R R) ⊓
      (Ideal.span ({s} : Set R) : Submodule R R) := by
    refine ⟨?_, hγ_s⟩
    rw [h_smul_eq]; exact hγ_pow
  rw [hk₀ m hm] at h_inf
  -- h_inf : γ ∈ I^(m-k₀) • (I^k₀ • ⊤ ⊓ ⟨s⟩).
  refine Submodule.smul_induction_on h_inf ?mem ?add
  case mem =>
    intro a ha b hb_inter
    obtain ⟨c, hc_eq⟩ := Ideal.mem_span_singleton'.mp hb_inter.2
    refine ⟨a * c, (I ^ (m - k₀)).mul_mem_right c ha, ?_⟩
    -- a • b = a * b = a * (c * s) = s * (a * c)
    change a • b = s * (a * c)
    rw [smul_eq_mul, ← hc_eq]; ring
  case add =>
    intro x y hx hy
    obtain ⟨αx, hαx_mem, hαx_eq⟩ := hx
    obtain ⟨αy, hαy_mem, hαy_eq⟩ := hy
    refine ⟨αx + αy, (I ^ (m - k₀)).add_mem hαx_mem hαy_mem, ?_⟩
    rw [hαx_eq, hαy_eq]; ring

omit [TopologicalSpace A] in
/-- **`s^E`-absorption in an `I`-power, via Artin-Rees**
(T122 reusable primitive — E-dependent constant).

For a Noetherian commutative ring `R`, ideal `I : Ideal R`, element
`s : R`, and a fixed exponent `E : ℕ`, every element simultaneously
in a deep `I`-power `I^m` and in the principal ideal `⟨s^E⟩`
factors as `s^E * α` with `α ∈ I^(m - k_E)`, where `k_E` is the
Artin-Rees shift for the pair `(I, ⟨s^E⟩)` (and depends on `E`).

This is the **E-dependent variant** of T119's
`Ideal.exists_factor_of_mem_inter_singleton`. The proof template is
identical: apply `Ideal.exists_pow_inf_eq_pow_smul` directly with
`N := Ideal.span {s^E}`, then unwind via
`Submodule.smul_induction_on` and `Ideal.mem_span_singleton'`. The
`E = 0` case is handled by the same statement: `s^0 = 1`, so the
factorization is by `1` and `k_0` is the Artin-Rees constant for
`(I, ⟨1⟩) = (I, ⊤)` (which is `0`).

**Note** (per T120 audit): the constant `k_E` is **E-dependent** by
design — Mathlib's Artin-Rees gives a per-`N` constant, and we
deliberately do NOT try to extract a uniform-in-`E` constant in this
primitive. The iteration to a uniform/linear constant requires
additional torsion or filtration hypotheses and is left to a
follow-up ticket.

**Use** (T119/T113 chain): converts a `γ ∈ I^m ⊓ ⟨s^E⟩` membership
into the explicit `s^E · α` factorization in one Artin-Rees step.
The Tate/source bridge (from the consumer's A-side relation
`s^(j+E) * a = s^j * (γ : A)` to `γ ∈ ⟨s^E⟩` in `P.A₀`) is the
remaining structural input. -/
theorem Ideal.exists_factor_pow_of_mem_inter_pow_singleton
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (s : R) (E : ℕ) :
    ∃ k_E : ℕ, ∀ m : ℕ, m ≥ k_E →
      ∀ γ : R, γ ∈ I ^ m → γ ∈ Ideal.span ({s ^ E} : Set R) →
        ∃ α : R, α ∈ I ^ (m - k_E) ∧ γ = s ^ E * α := by
  obtain ⟨k_E, hk_E⟩ := Ideal.exists_pow_inf_eq_pow_smul I
    (Ideal.span ({s ^ E} : Set R))
  refine ⟨k_E, fun m hm γ hγ_pow hγ_sE ↦ ?_⟩
  -- γ ∈ I^m • ⊤ ⊓ ⟨s^E⟩ via smul/mul translation.
  have h_smul_eq : I ^ m • (⊤ : Submodule R R) = I ^ m := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have h_inf : γ ∈ I ^ m • (⊤ : Submodule R R) ⊓
      (Ideal.span ({s ^ E} : Set R) : Submodule R R) := by
    refine ⟨?_, hγ_sE⟩
    rw [h_smul_eq]; exact hγ_pow
  rw [hk_E m hm] at h_inf
  -- h_inf : γ ∈ I^(m-k_E) • (I^k_E • ⊤ ⊓ ⟨s^E⟩).
  refine Submodule.smul_induction_on h_inf ?mem ?add
  case mem =>
    intro a ha b hb_inter
    obtain ⟨c, hc_eq⟩ := Ideal.mem_span_singleton'.mp hb_inter.2
    refine ⟨a * c, (I ^ (m - k_E)).mul_mem_right c ha, ?_⟩
    -- a • b = a * b = a * (c * s^E) = s^E * (a * c)
    change a • b = s ^ E * (a * c)
    rw [smul_eq_mul, ← hc_eq]; ring
  case add =>
    intro x y hx hy
    obtain ⟨αx, hαx_mem, hαx_eq⟩ := hx
    obtain ⟨αy, hαy_mem, hαy_eq⟩ := hy
    refine ⟨αx + αy, (I ^ (m - k_E)).add_mem hαx_mem hαy_mem, ?_⟩
    rw [hαx_eq, hαy_eq]; ring

end ValuationSpectrum

/-! ## Principal pair π-clearing API (T124)

A small denominator-clearing API for the principal pair of definition
of a Tate ring (see `IsTateRing.principalPair` /
`PrincipalPairOfDefinition` in `HuberRings.lean`). This is the **valid
π-specific** counterpart to the (invalid) generic `D.s` localization
bridge: it captures only the canonical fact that the chosen
generator `π : P.A₀` of a principal pair is topologically nilpotent in
`A`, lies in `P.I`, and clears any `a : A` into `P.A₀` after a
sufficient `π`-power.

* `PrincipalPairOfDefinition.pi_mem_I` — `P.π ∈ P.toPairOfDefinition.I`,
  immediate from `P.I_eq_span` and `Ideal.mem_span_singleton_self`.
* `PrincipalPairOfDefinition.pi_topologicallyNilpotent` — `(P.π : A)`
  is topologically nilpotent in `A`, via
  `PairOfDefinition.isTopologicallyNilpotent_of_mem`.
* `PrincipalPairOfDefinition.exists_pow_mul_mem_A₀` — for every
  `a : A`, some `π^n * a ∈ P.A₀`. Inlined from the same proof template
  as `PairOfDefinition.exists_pow_mul_mem_A₀` in `Lemma745.lean`
  (verbatim continuity-of-multiplication argument); inlined rather
  than imported to avoid pulling the heavier `Lemma745`/`ValuationContinuity`
  dependency into this file.
* `PrincipalPairOfDefinition.exists_pow_mul_eq_A₀` — explicit
  `(n, a₀ : P.A₀)` witness shape useful for downstream source-bridge
  reasoning. -/

/-- The generator `π` of a principal pair lies in its ideal of
definition `I`. -/
theorem PrincipalPairOfDefinition.pi_mem_I {A : Type*}
    [CommRing A] [TopologicalSpace A]
    (P : PrincipalPairOfDefinition A) :
    P.π ∈ P.toPairOfDefinition.I := by
  rw [P.I_eq_span]
  exact Ideal.mem_span_singleton_self _

/-- The generator `π` of a principal pair is topologically nilpotent
in `A`. -/
theorem PrincipalPairOfDefinition.pi_topologicallyNilpotent
    {A : Type*} [CommRing A] [TopologicalSpace A]
    (P : PrincipalPairOfDefinition A) :
    IsTopologicallyNilpotent ((P.π : A)) :=
  P.toPairOfDefinition.isTopologicallyNilpotent_of_mem P.pi_mem_I

/-- Every `a : A` admits a `π`-power that clears it into the ring of
definition `P.A₀`.

Inlined from `PairOfDefinition.exists_pow_mul_mem_A₀`
(`Lemma745.lean`) to avoid the heavier
`Lemma745`/`ValuationContinuity` import in this file. -/
theorem PrincipalPairOfDefinition.exists_pow_mul_mem_A₀
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PrincipalPairOfDefinition A) (a : A) :
    ∃ n : ℕ, ((P.π : A) ^ n) * a ∈ P.toPairOfDefinition.A₀ := by
  have h_cont : Continuous (· * a : A → A) := continuous_mul_const a
  have h_open : IsOpen {x : A | x * a ∈ P.toPairOfDefinition.A₀} :=
    P.toPairOfDefinition.isOpen.preimage h_cont
  have h_zero : (0 : A) ∈ {x : A | x * a ∈ P.toPairOfDefinition.A₀} := by
    simp only [Set.mem_ofPred_eq, zero_mul, P.toPairOfDefinition.A₀.zero_mem]
  have h_nhds : {x : A | x * a ∈ P.toPairOfDefinition.A₀} ∈
      nhds (0 : A) :=
    h_open.mem_nhds h_zero
  obtain ⟨n, hn⟩ := (P.pi_topologicallyNilpotent.eventually h_nhds).exists
  exact ⟨n, hn⟩

/-- Subtype/witness version of `exists_pow_mul_mem_A₀`: produces an
explicit `a₀ : P.A₀` with `(P.π : A) ^ n * a = (a₀ : A)`. The shape
downstream source-bridge reasoning consumes. -/
theorem PrincipalPairOfDefinition.exists_pow_mul_eq_A₀
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PrincipalPairOfDefinition A) (a : A) :
    ∃ (n : ℕ) (a₀ : P.toPairOfDefinition.A₀),
      ((P.π : A) ^ n) * a = (a₀ : A) := by
  obtain ⟨n, hn⟩ := P.exists_pow_mul_mem_A₀ a
  exact ⟨n, ⟨_, hn⟩, rfl⟩
