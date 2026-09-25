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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LocalizationTopology
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.IdealClosedness
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Prop752
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Ideal Closedness Transfer from `locSubring` to `Localization.Away s`
(T-IDEAL-2 / S-IDEAL-LOC)

Given a proper ideal `q ⊆ Localization.Away s` whose contraction
`Ideal.comap locSubring.subtype q` is closed in the `locSubring` subspace
topology (equivalently, in the `locIdeal`-adic topology via
`locSubring_topology_eq_adic`), we prove `q` is closed in
`Localization.Away s` with the `locTopology`.

The proof is a Tate-style "clearing denominators" argument (Wedhorn §8.2):
a topologically nilpotent unit `π ∈ P.A₀` lets us write every element
`x ∈ Localization.Away s` as `u · d` with `u ∈ (Localization.Away s)ˣ`
and `d ∈ locSubring`. Combined with the fact that `locSubring` is open in
`Localization.Away s` (`locSubring_isOpen`), this gives a neighborhood
`u · V` in `Localization.Away s` for any neighborhood `V` of `d` in
`locSubring`, enabling the separation argument for the closedness transfer.

## Main results

* `exists_unit_locSubring_decomp` — every element of
  `Localization.Away s` factors as (unit) · (locSubring element) under the
  topologically-nilpotent-unit hypothesis.
* `mem_ideal_iff_clearing_denominator` — the clearing-denominator form of
  `q = (q ∩ locSubring) · Localization.Away s`.
* `isClosed_in_locTopology_of_contraction_isClosed_in_locSubring` —
  topological transfer: closed contraction ⟹ closed ideal.

## Plug-in point

These are consumed by `S-IDEAL-ASM` (in `Cor832.lean`) to discharge
`coeRingHom_preserves_proper` via
`coeRingHom_preserves_proper_of_closed`. The `q ∩ locSubring` closedness
is itself to be discharged downstream (S-IDEAL-JAC for the generic Tate
case, via `Ideal.isClosed_of_le_jacobson` + `locSubring_topology_eq_adic`).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1, §8.2
* `.mathlib-quality/tickets.md` T-IDEAL-2 / S-IDEAL-LOC
-/

@[expose] public section

open Topology Filter

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### Step 1 — clearing denominators via a topologically nilpotent unit -/

/-- **Topological absorption into `P.A₀`.** For `π : A` topologically
nilpotent in `A` and any `a : A`, some power `π^n * a` lies in the open
subring `P.A₀`. Private helper for the clearing-denominators lemma;
mirrors `Lemma745.exists_pow_mul_mem_A₀` but inlined here to avoid an
import of the downstream `Lemma745` file. -/
private theorem exists_pow_mul_mem_A₀_aux
    (P : PairOfDefinition A) {π : A} (hπ : IsTopologicallyNilpotent π)
    (a : A) : ∃ n : ℕ, π ^ n * a ∈ P.A₀ := by
  have h_open : IsOpen {x : A | x * a ∈ P.A₀} :=
    P.isOpen.preimage (continuous_mul_const a)
  have h_zero : (0 : A) ∈ {x : A | x * a ∈ P.A₀} := by
    simp only [Set.mem_setOf_eq, zero_mul, P.A₀.zero_mem]
  exact (hπ.eventually (h_open.mem_nhds h_zero)).exists

/-- **Clearing denominators into `locSubring`** (S-IDEAL-LOC Step 1).

Every element `x : Localization.Away s` factors as `x = u * (d : Loc.Away s)`
for some unit `u ∈ (Localization.Away s)ˣ` and some `d ∈ locSubring P T s`,
provided there exists a topologically nilpotent unit `π ∈ P.A₀`. -/
theorem Localization.Away.exists_unit_locSubring_decomp
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (_hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (b : A) s ∈ locSubring P T s)
    {π : A} (hπ_nil : IsTopologicallyNilpotent π) (_hπ_A₀ : π ∈ P.A₀)
    (hπ_unit : IsUnit π) (x : Localization.Away s) :
    ∃ (u : (Localization.Away s)ˣ) (d : locSubring P T s),
      x = (u : Localization.Away s) * ((d : Localization.Away s)) := by
  classical
  obtain ⟨⟨a, ⟨sk, k, hsk⟩⟩, hx⟩ :=
    IsLocalization.surj (M := Submonoid.powers s) (S := Localization.Away s) x
  subst hsk
  -- hx : x * algebraMap (s^k) = algebraMap a
  obtain ⟨n, hna⟩ := exists_pow_mul_mem_A₀_aux P hπ_nil a
  have h_mem : algebraMap A (Localization.Away s) (π ^ n * a) ∈ locSubring P T s :=
    algebraMap_mem_locSubring P T s hna
  have h_prod_unit : IsUnit (((algebraMap A (Localization.Away s)) π) ^ n *
      ((algebraMap A (Localization.Away s)) s) ^ k) :=
    ((hπ_unit.map (algebraMap A (Localization.Away s))).pow n).mul
      ((IsLocalization.map_units (Localization.Away s)
        (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s)).pow k)
  set U : (Localization.Away s)ˣ := h_prod_unit.unit
  have hU_val : (U : Localization.Away s) =
      ((algebraMap A (Localization.Away s)) π) ^ n *
      ((algebraMap A (Localization.Away s)) s) ^ k := h_prod_unit.unit_spec
  -- Key: U.val * x = algebraMap (π^n * a).
  have key : (U : Localization.Away s) * x =
      algebraMap A (Localization.Away s) (π ^ n * a) := by
    calc (U : Localization.Away s) * x
        = ((algebraMap A (Localization.Away s)) π) ^ n *
            (x * ((algebraMap A (Localization.Away s)) s) ^ k) := by
          rw [hU_val]; ring
      _ = ((algebraMap A (Localization.Away s)) π) ^ n *
            algebraMap A (Localization.Away s) a := by
          congr 1
          rw [← map_pow]; exact hx
      _ = algebraMap A (Localization.Away s) (π ^ n * a) := by
          rw [← map_pow, ← map_mul]
  refine ⟨U⁻¹, ⟨algebraMap A (Localization.Away s) (π ^ n * a), h_mem⟩, ?_⟩
  change x = ((U⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
      algebraMap A (Localization.Away s) (π ^ n * a)
  rw [← key, ← mul_assoc, Units.inv_mul, one_mul]

/-! ### Step 2 — localization identity (clearing-denominator form) -/

/-- **Clearing-denominator form of the localization identity** (S-IDEAL-LOC
Step 2).

Every `x ∈ q` is `u * d` for some unit `u ∈ (Localization.Away s)ˣ` and
some `d ∈ locSubring P T s` with `(d : Localization.Away s) ∈ q`. -/
theorem Localization.Away.mem_ideal_iff_clearing_denominator
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (b : A) s ∈ locSubring P T s)
    {π : A} (hπ_nil : IsTopologicallyNilpotent π) (hπ_A₀ : π ∈ P.A₀)
    (hπ_unit : IsUnit π) (q : Ideal (Localization.Away s)) (x : Localization.Away s)
    (hx : x ∈ q) :
    ∃ (u : (Localization.Away s)ˣ) (d : locSubring P T s),
      (d : Localization.Away s) ∈ q ∧
      x = (u : Localization.Away s) * (d : Localization.Away s) := by
  obtain ⟨u, d, hxud⟩ :=
    Localization.Away.exists_unit_locSubring_decomp P T s hopen hπ_nil hπ_A₀ hπ_unit x
  refine ⟨u, d, ?_, hxud⟩
  -- d = u⁻¹ * x ∈ q.
  have h_d_eq : (d : Localization.Away s) = (u⁻¹ : (Localization.Away s)ˣ) * x := by
    rw [hxud, ← mul_assoc, u.inv_mul, one_mul]
  exact h_d_eq ▸ q.mul_mem_left _ hx

/-! ### Step 3 — topological transfer -/

/-- **Topological transfer of ideal closedness** (S-IDEAL-LOC Step 3 / main theorem).

Given a proper ideal `q ⊆ Localization.Away s` whose contraction
`Ideal.comap locSubring.subtype q` is closed in the `locSubring` subspace
topology, `q` is closed in `Localization.Away s` with the `locTopology`. -/
theorem Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (b : A) s ∈ locSubring P T s)
    {π : A} (hπ_nil : IsTopologicallyNilpotent π) (hπ_A₀ : π ∈ P.A₀)
    (hπ_unit : IsUnit π) (q : Ideal (Localization.Away s))
    (h_contr_closed : @IsClosed _
      ((locTopology P T s hopen).induced (locSubring P T s).subtype)
      ((Ideal.comap (locSubring P T s).subtype q : Ideal (locSubring P T s)) :
        Set (locSubring P T s))) :
    @IsClosed _ (locTopology P T s hopen) (q : Set (Localization.Away s)) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  haveI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx_not_mem
  obtain ⟨u, d, hxud⟩ :=
    Localization.Away.exists_unit_locSubring_decomp P T s hopen hπ_nil hπ_A₀ hπ_unit x
  have hd_notin_q : (d : Localization.Away s) ∉ q := by
    intro hd_in
    exact hx_not_mem (hxud ▸ q.mul_mem_left _ hd_in)
  have hd_notin_contr : d ∉ (Ideal.comap (locSubring P T s).subtype q :
      Ideal (locSubring P T s)) := by
    intro hcon
    exact hd_notin_q (Ideal.mem_comap.mp hcon)
  have h_nhd_subspace := h_contr_closed.isOpen_compl.mem_nhds hd_notin_contr
  rw [@nhds_induced] at h_nhd_subspace
  obtain ⟨V₀, hV₀_nhds, hV₀_sub⟩ := Filter.mem_comap.mp h_nhd_subspace
  set V : Set (Localization.Away s) :=
    V₀ ∩ (locSubring P T s : Set (Localization.Away s))
  have hV_nhds : V ∈ nhds (d : Localization.Away s) :=
    Filter.inter_mem hV₀_nhds ((locSubring_isOpen P T s hopen).mem_nhds d.property)
  have h_d_eq : (d : Localization.Away s) = (u⁻¹ : (Localization.Away s)ˣ) * x := by
    rw [hxud, ← mul_assoc, u.inv_mul, one_mul]
  have hV_preimage_nhd_x :
      (fun y : Localization.Away s =>
        ((u⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) * y) ⁻¹' V ∈ nhds x := by
    apply (continuous_const.mul continuous_id).continuousAt
    change V ∈ nhds (((u⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) * x)
    rw [← h_d_eq]; exact hV_nhds
  refine Filter.mem_of_superset hV_preimage_nhd_x ?_
  intro y hy_mem
  obtain ⟨hy_V₀, hy_locSub⟩ := hy_mem
  intro hy_in_q
  have h_uinv_y_in_q : (u⁻¹ : (Localization.Away s)ˣ) * y ∈ q :=
    q.mul_mem_left _ hy_in_q
  set z : locSubring P T s := ⟨(u⁻¹ : (Localization.Away s)ˣ) * y, hy_locSub⟩
  have hz_notin_contr : z ∉ (Ideal.comap (locSubring P T s).subtype q :
      Ideal (locSubring P T s)) := hV₀_sub hy_V₀
  exact hz_notin_contr h_uinv_y_in_q

/-! ### S-IDEAL-JAC — `locIdeal ≤ Ideal.jacobson ⊥` in `locSubring`

Tate specialization of the generic `Ideal.le_jacobson_bot_of_isAdic_complete`
(`IdealClosedness.lean`). The Mathlib lemma `IsAdicComplete.le_jacobson_bot`
gives the Jacobson containment directly when the adic-completeness witness
is available as a typeclass instance.

**Mathematical residual.** The Tate case does not automatically provide
`IsAdicComplete (locIdeal P T s) (locSubring P T s)`: the adic-complete
witness in the project is for the **completion** `presheafValue D` (see
`Cor832.presheafValue_isAdicComplete`), not for `locSubring` itself. The
Tate-specific discharge of this hypothesis is a residual for downstream
work. See `.mathlib-quality/tickets.md` §S-IDEAL-JAC interface. -/

omit [IsTopologicalRing A] in
/-- **S-IDEAL-JAC under `IsAdicComplete` (Tate specialization).**

`locIdeal P T s ≤ Ideal.jacobson ⊥` in `locSubring P T s`, given
`[IsAdicComplete (locIdeal P T s) (locSubring P T s)]`. Direct consequence of
Mathlib's `IsAdicComplete.le_jacobson_bot`.

Note: **asserts locSubring is adic-complete at `locIdeal`**, which is NOT
automatic in the Tate setting (the Tate completeness witness is for the
*completion* `presheafValue_ringOfDef D` via `Cor832.presheafValue_isAdicComplete`,
not for `locSubring` itself). Downstream consumers should prefer
`locIdeal_le_jacobson_bot_of_faithfullyFlat_to_ringOfDef` below, which
avoids asserting locSubring complete. -/
theorem locIdeal_le_jacobson_bot_of_isAdicComplete
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    [IsAdicComplete (locIdeal P T s) (locSubring P T s)] :
    locIdeal P T s ≤ Ideal.jacobson (⊥ : Ideal (locSubring P T s)) :=
  IsAdicComplete.le_jacobson_bot _

omit [IsTopologicalRing A] in
/-- **Unit lifting along a faithfully flat ring extension** (generic). If `S`
is faithfully flat over `R` and `algebraMap R S r` is a unit in `S`, then
`r` is a unit in `R`.

**Proof**: `IsUnit r ↔ (r) = ⊤`. By `Ideal.comap_map_eq_self_of_faithfullyFlat`,
`(r) = (algebraMap R S r).comap`. If `(algebraMap r) = ⊤`, then comap = ⊤,
so `(r) = ⊤`, so `r` is a unit. -/
private theorem isUnit_of_algebraMap_isUnit_of_faithfullyFlat
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {r : R}
    (hr : IsUnit (algebraMap R S r)) : IsUnit r := by
  rw [← Ideal.span_singleton_eq_top] at hr ⊢
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (A := R) (B := S) (Ideal.span {r}),
    Ideal.map_span, Set.image_singleton, hr, Ideal.comap_top]

omit [IsTopologicalRing A] in
/-- **S-IDEAL-JAC via faithful-flatness descent**.

Let `S` be an `(locSubring P T s)`-algebra with `[Module.FaithfullyFlat
(locSubring P T s) S]`. If the extension `Ideal.map (algebraMap _ S) (locIdeal)`
is contained in `Ideal.jacobson (⊥ : Ideal S)` at the target side, then
`locIdeal ≤ Ideal.jacobson (⊥ : Ideal (locSubring))` in the source.

**This form does not assert `locSubring` is adic-complete**. The Jacobson
containment at `S` can be discharged wherever `[IsAdicComplete J_S S]` holds
(e.g., the completion side via `Cor832.presheafValue_isAdicComplete` with
`S := presheafValue_ringOfDef D`), via Mathlib's
`IsAdicComplete.le_jacobson_bot`, and this theorem pulls it back.

**Proof**: for `x ∈ locIdeal`, use `Ideal.mem_jacobson_bot` in `S` to obtain
`IsUnit (algebraMap x · algebraMap y + 1)` for each `y`. Since this equals
`algebraMap (x·y + 1)`, by `isUnit_of_algebraMap_isUnit_of_faithfullyFlat`,
`IsUnit (x·y + 1)` holds in `locSubring`, giving `x ∈ Jacobson ⊥`. -/
theorem locIdeal_le_jacobson_bot_of_faithfullyFlat
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    {S : Type*} [CommRing S] [Algebra (locSubring P T s) S]
    [Module.FaithfullyFlat (locSubring P T s) S]
    (h_jac : Ideal.map (algebraMap (locSubring P T s) S) (locIdeal P T s) ≤
      Ideal.jacobson (⊥ : Ideal S)) :
    locIdeal P T s ≤ Ideal.jacobson (⊥ : Ideal (locSubring P T s)) := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hx_map : algebraMap (locSubring P T s) S x ∈
      Ideal.map (algebraMap (locSubring P T s) S) (locIdeal P T s) :=
    Ideal.mem_map_of_mem _ hx
  have hx_jac : algebraMap (locSubring P T s) S x ∈
      Ideal.jacobson (⊥ : Ideal S) := h_jac hx_map
  rw [Ideal.mem_jacobson_bot] at hx_jac
  refine isUnit_of_algebraMap_isUnit_of_faithfullyFlat (S := S) ?_
  rw [map_add, map_mul, map_one]
  exact hx_jac (algebraMap _ S y)

/-- **Topological-nilpotence transfer for `locIdeal`.**

Every element of `locIdeal P T s` is topologically nilpotent in `locSubring`
under the subspace topology (= `locIdeal`-adic topology, by `locSubring_isAdic`).
No completeness hypothesis needed. -/
theorem locIdeal_forall_isTopologicallyNilpotent
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    ∀ x ∈ locIdeal P T s,
      letI : TopologicalSpace (locSubring P T s) :=
        (locTopology P T s hopen).induced (locSubring P T s).subtype
      IsTopologicallyNilpotent x := by
  intro x hx
  letI : TopologicalSpace (locSubring P T s) :=
    (locTopology P T s hopen).induced (locSubring P T s).subtype
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  haveI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  haveI : IsTopologicalRing (locSubring P T s) :=
    Subring.instIsTopologicalRing (locSubring P T s)
  exact isTopologicallyNilpotent_of_mem_of_isAdic (locSubring_isAdic P T s hopen) hx

/-! ### S-IDEAL-ASM plug-in: closedness of ideals in `locSubring`

Under `[IsNoetherianRing (locSubring P T s)]` (from
`Prop752.locSubring_isNoetherian` with `[IsNoetherianRing P.A₀]`) and the
`IsAdicComplete` Jacobson witness, **every** ideal of `locSubring P T s`
is closed in the subspace topology inherited from `locTopology`. This is
the direct feed into `Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring`
(S-IDEAL-LOC) from the preceding section. -/

/-- **Any ideal of `locSubring` is closed in the subspace topology** under
Noetherian + `IsAdicComplete` hypotheses. Combines `locSubring_isAdic`,
`IsAdicComplete.le_jacobson_bot`, and `Ideal.isClosed_of_le_jacobson` from
`IdealClosedness.lean`. Direct S-IDEAL-ASM plug-in. -/
theorem Ideal.isClosed_in_locSubring_subspace_of_isAdicComplete
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    [IsNoetherianRing (locSubring P T s)]
    [IsAdicComplete (locIdeal P T s) (locSubring P T s)]
    (q : Ideal (locSubring P T s)) :
    @IsClosed _
      ((locTopology P T s hopen).induced (locSubring P T s).subtype)
      (q : Set (locSubring P T s)) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  haveI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  letI : TopologicalSpace (locSubring P T s) :=
    (locTopology P T s hopen).induced (locSubring P T s).subtype
  haveI : IsTopologicalRing (locSubring P T s) :=
    Subring.instIsTopologicalRing (locSubring P T s)
  exact Ideal.isClosed_of_le_jacobson
    (locSubring_isAdic P T s hopen)
    (IsAdicComplete.le_jacobson_bot _) q

/-- **End-to-end S-IDEAL-ASM consumer (under `IsAdicComplete`).**

Given `[IsNoetherianRing (locSubring P T s)]` + `[IsAdicComplete (locIdeal P T s)
(locSubring P T s)]` + a topologically-nilpotent unit `π ∈ P.A₀`, every proper
ideal of `Localization.Away s` is closed in the `locTopology`. This combines:

- `Ideal.isClosed_in_locSubring_subspace_of_isAdicComplete` (S-IDEAL-JAC
  route) to produce the contraction-closed hypothesis.
- `Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring`
  (S-IDEAL-LOC, preceding section) to lift to the ambient `locTopology`. -/
theorem Ideal.isClosed_in_locTopology_of_isAdicComplete
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    [IsNoetherianRing (locSubring P T s)]
    [IsAdicComplete (locIdeal P T s) (locSubring P T s)]
    {π : A} (hπ_nil : IsTopologicallyNilpotent π) (hπ_A₀ : π ∈ P.A₀)
    (hπ_unit : IsUnit π) (q : Ideal (Localization.Away s)) :
    @IsClosed _ (locTopology P T s hopen) (q : Set (Localization.Away s)) := by
  apply Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring
    P T s hopen hπ_nil hπ_A₀ hπ_unit q
  exact Ideal.isClosed_in_locSubring_subspace_of_isAdicComplete P T s hopen _

end ValuationSpectrum
