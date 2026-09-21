/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Localization Topology for Huber Rings

We construct the non-archimedean ring topology on `Localization.Away s` following §8.1 of Wedhorn.

## Main definitions

* `ValuationSpectrum.divByS t s` : The element `t/s` in `Localization.Away s`.
* `ValuationSpectrum.locSubring P T s` : The ring of definition `D = A₀[t₁/s, …, tₙ/s]`.
* `ValuationSpectrum.locIdeal P T s` : The ideal of definition `J = I · D` in `D`.
* `ValuationSpectrum.locNhd P T s n` : The `n`-th neighborhood `image(Jⁿ)` in `Aₛ`.
* `ValuationSpectrum.locBasis P T s` : The `RingSubgroupsBasis` structure.
* `ValuationSpectrum.locTopology P T s` : The resulting topology on `Aₛ`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1
-/

open PairOfDefinition Pointwise

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### The ring of definition `D` -/

/-- The element `t/s` in `Localization.Away s`. -/
noncomputable def divByS (t s : A) : Localization.Away s :=
  IsLocalization.mk' (Localization.Away s) t
    (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s)

omit [TopologicalSpace A] in
/-- When `s = 1`, the fraction `t/1` equals `algebraMap t`. -/
theorem divByS_eq_algebraMap (t : A) :
    divByS t (1 : A) = algebraMap A (Localization.Away (1 : A)) t := by
  unfold divByS
  exact IsLocalization.mk'_one (M := Submonoid.powers (1 : A))
    (S := Localization.Away (1 : A)) t

/-- The ring of definition `D = A₀[t₁/s, …, tₙ/s]` of `Localization.Away s`
(§8.1 of Wedhorn). -/
noncomputable def locSubring (P : PairOfDefinition A) (T : Finset A)
    (s : A) : Subring (Localization.Away s) :=
  Subring.closure
    ((algebraMap A (Localization.Away s)) '' (P.A₀ : Set A) ∪
     Set.range (fun t : T ↦ divByS (t : A) s))

/-- The image of `A₀` under `algebraMap` is contained in `D`. -/
theorem algebraMap_A₀_subset_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) :
    (algebraMap A (Localization.Away s)) '' (P.A₀ : Set A) ⊆
      (locSubring P T s : Set (Localization.Away s)) :=
  Set.subset_union_left.trans Subring.subset_closure

/-- Each element `t/s` (for `t ∈ T`) belongs to `D`. -/
theorem divByS_mem_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) {t : A} (ht : t ∈ T) :
    divByS t s ∈ locSubring P T s :=
  Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)

/-- An element of `A₀` maps into `D` under `algebraMap`. -/
theorem algebraMap_mem_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) {a : A} (ha : a ∈ P.A₀) :
    algebraMap A (Localization.Away s) a ∈ locSubring P T s :=
  algebraMap_A₀_subset_locSubring P T s ⟨a, ha, rfl⟩

/-! ### The ideal of definition `J` -/

/-- The ring homomorphism `A₀ →+* D` induced by `algebraMap`, restricted to codomain `D`. -/
noncomputable def algebraMapD (P : PairOfDefinition A) (T : Finset A)
    (s : A) : P.A₀ →+* (locSubring P T s) :=
  ((algebraMap A (Localization.Away s)).comp P.A₀.subtype).codRestrict
    (locSubring P T s)
    (fun a ↦ algebraMap_A₀_subset_locSubring P T s ⟨a, a.property, rfl⟩)

/-- The ideal of definition `J = I · D` in `D`. -/
noncomputable def locIdeal (P : PairOfDefinition A) (T : Finset A)
    (s : A) : Ideal (locSubring P T s) :=
  Ideal.map (algebraMapD P T s) P.I

/-- The ideal of definition `J` is finitely generated. -/
theorem locIdeal_fg (P : PairOfDefinition A) (T : Finset A) (s : A) :
    (locIdeal P T s).FG :=
  P.fg.map _

/-! ### The neighborhood basis -/

/-- The `n`-th neighborhood of `0` in `Localization.Away s`: the image of `Jⁿ` in `Aₛ`. -/
noncomputable def locNhd (P : PairOfDefinition A) (T : Finset A) (s : A)
    (n : ℕ) : AddSubgroup (Localization.Away s) :=
  ((locIdeal P T s) ^ n).toAddSubgroup.map
    (locSubring P T s).subtype.toAddMonoidHom

/-- The neighborhoods are antitone: `m ≤ n → locNhd n ≤ locNhd m`. -/
theorem locNhd_antitone (P : PairOfDefinition A) (T : Finset A) (s : A) :
    Antitone (locNhd P T s) :=
  fun _ _ h ↦ AddSubgroup.map_mono (Submodule.toAddSubgroup_mono (Ideal.pow_le_pow_right h))

/-- `0 ∈ locNhd n` for all `n`. -/
theorem zero_mem_locNhd (P : PairOfDefinition A) (T : Finset A) (s : A)
    (n : ℕ) : (0 : Localization.Away s) ∈ locNhd P T s n :=
  ⟨0, (locIdeal P T s ^ n).zero_mem, map_zero _⟩

/-- The preimage of `locNhd n` under the subtype embedding equals `locIdeal^n`.
This connects the localization topology on `Localization.Away s` to the
`locIdeal`-adic topology on `locSubring`. -/
theorem locNhd_preimage_eq_locIdeal_pow (P : PairOfDefinition A) (T : Finset A)
    (s : A) (n : ℕ) :
    (locSubring P T s).subtype ⁻¹' (locNhd P T s n : Set (Localization.Away s)) =
      ((locIdeal P T s) ^ n : Ideal (locSubring P T s)) := by
  ext d
  constructor
  · rintro ⟨d', hd', heq⟩
    exact (Subtype.val_injective heq) ▸ hd'
  · intro hd
    exact ⟨d, hd, rfl⟩

/-! ### The `RingSubgroupsBasis` -/

section Basis

variable [IsTopologicalRing A]

omit [IsTopologicalRing A] in
private theorem locNhd_mul (P : PairOfDefinition A) (T : Finset A)
    (s : A) (i : ℕ) :
    ∃ j, (locNhd P T s j : Set (Localization.Away s)) *
      (locNhd P T s j : Set (Localization.Away s)) ⊆
        (locNhd P T s i : Set (Localization.Away s)) := by
  refine ⟨i, ?_⟩
  rintro _ ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨d₂, hd₂, rfl⟩, rfl⟩
  exact ⟨d₁ * d₂, Ideal.pow_le_pow_right (Nat.le_add_left i i)
    (pow_add (locIdeal P T s) i i ▸ Ideal.mul_mem_mul hd₁ hd₂),
    MulMemClass.coe_mul ..⟩

omit [IsTopologicalRing A] in
/-- Multiplying `1/s` by an element of `J^N` lands in the localization subring `D`. -/
private theorem locNhd_invS_mem (P : PairOfDefinition A) (T : Finset A) (s : A)
    (N : ℕ) (hN : ∀ b : P.A₀, b ∈ P.I ^ N → divByS (↑b : A) s ∈ locSubring P T s)
    {d : locSubring P T s} (hd : d ∈ locIdeal P T s ^ N) :
    divByS 1 s * ↑d ∈ locSubring P T s := by
  rw [locIdeal, ← Ideal.map_pow, ← Ideal.span_eq (P.I ^ N), Ideal.map_span] at hd
  refine Submodule.span_induction (p := fun d _ ↦ divByS 1 s * ↑d ∈ locSubring P T s)
    ?_ ?_ ?_ ?_ hd
  · rintro d ⟨b, hb, rfl⟩
    change divByS 1 s * algebraMap A _ ↑b ∈ _
    rw [show divByS 1 s * algebraMap A (Localization.Away s) ↑b = divByS (↑b) s from by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers s) (S := Localization.Away s)
        (↑b : A), ← IsLocalization.mk'_mul, one_mul, mul_one]]
    exact hN b hb
  · simp [(locSubring P T s).zero_mem]
  · intro d1 d2 _ _ h1 h2
    simp only [AddMemClass.coe_add, mul_add]
    exact (locSubring P T s).add_mem h1 h2
  · intro r d1 _ h1
    rw [show (↑(r • d1) : Localization.Away s) = ↑r * ↑d1 from MulMemClass.coe_mul ..,
        mul_left_comm]
    exact (locSubring P T s).mul_mem r.property h1

omit [IsTopologicalRing A] in
/-- Multiplying `1/s` by an element of `locNhd (n + N)` lands in `locNhd n`. -/
private theorem locNhd_invS_step (P : PairOfDefinition A) (T : Finset A) (s : A)
    (N : ℕ) (hN : ∀ b : P.A₀, b ∈ P.I ^ N → divByS (↑b : A) s ∈ locSubring P T s)
    (n : ℕ) (y : Localization.Away s)
    (hy : y ∈ locNhd P T s (n + N)) : divByS 1 s * y ∈ locNhd P T s n := by
  obtain ⟨d, hd, rfl⟩ := hy
  change divByS 1 s * ↑d ∈ locNhd P T s n
  rw [Nat.add_comm, pow_add] at hd
  refine Submodule.mul_induction_on hd ?_ ?_
  · intro a ha b hb
    change divByS 1 s * (↑a * ↑b) ∈ locNhd P T s n
    rw [← mul_assoc]
    exact ⟨⟨divByS 1 s * ↑a, locNhd_invS_mem P T s N hN ha⟩ * b, Ideal.mul_mem_left _ _ hb,
      MulMemClass.coe_mul ..⟩
  · intro y1 y2 h1 h2
    simp only [AddMemClass.coe_add, mul_add]
    exact (locNhd P T s n).add_mem h1 h2

/-- Multiplying `algebraMap a` by an element of a suitable `locNhd j` lands in `locNhd i`. -/
private theorem locNhd_algMap_step (P : PairOfDefinition A) (T : Finset A) (s : A)
    (i : ℕ) (a : A) :
    ∃ j, ∀ y ∈ locNhd P T s j,
      algebraMap A (Localization.Away s) a * y ∈ locNhd P T s i := by
  obtain ⟨m₀, -, hm₀⟩ := P.hasBasis_nhds_zero.mem_iff.mp
    (continuous_const_mul a |>.continuousAt.preimage_mem_nhds
      (by rw [mul_zero]; exact P.hasBasis_nhds_zero.mem_of_mem trivial (i := i)))
  refine ⟨m₀, ?_⟩
  rintro y ⟨d, hd, rfl⟩
  change algebraMap A (Localization.Away s) a * ↑d ∈ locNhd P T s i
  rw [locIdeal, ← Ideal.map_pow, ← Ideal.span_eq (P.I ^ m₀), Ideal.map_span] at hd
  refine Submodule.span_induction (p := fun d _ ↦
    algebraMap A (Localization.Away s) a * ↑d ∈ locNhd P T s i) ?_ ?_ ?_ ?_ hd
  · rintro d ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hval⟩ := hm₀ ⟨b, hb, rfl⟩
    change algebraMap A _ a * algebraMap A _ ↑b ∈ _
    rw [← map_mul, show a * (↑b : A) = ↑c from hval.symm]
    exact ⟨algebraMapD P T s c,
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hc, rfl⟩
  · simp [(locNhd P T s i).zero_mem]
  · intro d1 d2 _ _ h1 h2
    simp only [AddMemClass.coe_add, mul_add]
    exact (locNhd P T s i).add_mem h1 h2
  · intro r d1 _ h1
    rw [show (↑(r • d1) : Localization.Away s) = ↑r * ↑d1 from MulMemClass.coe_mul ..,
        mul_left_comm]
    obtain ⟨e, he, he_eq⟩ := h1
    exact ⟨r * e, Ideal.mul_mem_left _ r he,
      congrArg ((↑r : Localization.Away s) * ·) he_eq⟩

/-- **Left multiplication continuity** for the localization topology (Wedhorn §5.51, §8.1). -/
theorem locNhd_leftMul (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (x : Localization.Away s) (i : ℕ) :
    ∃ j, (locNhd P T s j : Set (Localization.Away s)) ⊆
      (x * ·) ⁻¹' (locNhd P T s i : Set (Localization.Away s)) := by
  obtain ⟨N, hN⟩ := hopen
  induction x using Localization.induction_on with
  | H p =>
    obtain ⟨a, ⟨_, k, rfl⟩⟩ := p
    induction k generalizing a with
    | zero =>
      simp only [pow_zero]
      obtain ⟨j, hj⟩ := locNhd_algMap_step P T s i a
      exact ⟨j, fun _ hy ↦ hj _ hy⟩
    | succ k ih =>
      have hk1 : s ^ (k + 1) ∈ Submonoid.powers s := ⟨k + 1, rfl⟩
      have hk : s ^ k ∈ Submonoid.powers s := ⟨k, rfl⟩
      have hdecomp : Localization.mk a ⟨s ^ (k + 1), hk1⟩ =
          Localization.mk a ⟨s ^ k, hk⟩ * divByS 1 s := by
        rw [divByS, ← Localization.mk_eq_mk', Localization.mk_mul, mul_one]
        congr 1; exact Subtype.ext (pow_succ s k)
      obtain ⟨j₁, hj₁⟩ := ih a
      refine ⟨j₁ + N, fun y hy ↦ ?_⟩
      simp only [Set.mem_preimage]
      rw [hdecomp, mul_assoc]
      exact hj₁ (locNhd_invS_step P T s N hN j₁ _ hy)

/-- The `RingSubgroupsBasis` for the localization topology on `Aₛ`. -/
noncomputable def locBasis (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    RingSubgroupsBasis (locNhd P T s) :=
  .of_comm _
    (fun i j ↦ ⟨max i j,
      le_inf (locNhd_antitone P T s (le_max_left i j))
        (locNhd_antitone P T s (le_max_right i j))⟩)
    (locNhd_mul P T s)
    (locNhd_leftMul P T s hopen)

/-- The localization topology on `Localization.Away s` with `0`-neighborhoods `{image(Jⁿ)}`. -/
@[reducible] noncomputable def locTopology (P : PairOfDefinition A) (T : Finset A)
    (s : A) (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    TopologicalSpace (Localization.Away s) :=
  (locBasis P T s hopen).topology

/-- **The subspace topology on `locSubring` equals the `locIdeal`-adic topology.**
Both topologies have the same nhds 0 basis: `{locIdeal^n | n}`.
- Subspace side: `nhds 0` has basis `{subtype⁻¹(locNhd n)}` = `{locIdeal^n}`
  by `locNhd_preimage_eq_locIdeal_pow`.
- Adic side: `nhds 0` has basis `{(locIdeal^n : Set _)}`
  by `Ideal.hasBasis_nhds_zero_adic`.

This is the bridge gate connecting the localization topology world
(`presheafValue = Completion(Localization.Away s)`) to the adic completion world
(`AdicCompletion(locIdeal, locSubring)`), enabling `AdicCompletion.map_exact` for Step B. -/
theorem locSubring_topology_eq_adic (P : PairOfDefinition A) (T : Finset A)
    (s : A) (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    @IsAdic (locSubring P T s) _
      (TopologicalSpace.induced (locSubring P T s).subtype (locTopology P T s hopen))
      (locIdeal P T s) := by
  let : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  let : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  let : TopologicalSpace (locSubring P T s) :=
    TopologicalSpace.induced (locSubring P T s).subtype (locTopology P T s hopen)
  let : IsTopologicalRing (locSubring P T s) := Subring.instIsTopologicalRing _
  change TopologicalSpace.induced _ _ = _
  suffices h : @IsAdic (locSubring P T s) _
      (TopologicalSpace.induced (locSubring P T s).subtype (locTopology P T s hopen))
      (locIdeal P T s) from h
  rw [isAdic_iff]; constructor
  · intro n
    rw [@isOpen_induced_iff]
    refine ⟨(locNhd P T s n : Set (Localization.Away s)), ?_, ?_⟩
    · have hmem : (locNhd P T s n : Set (Localization.Away s)) ∈
          @nhds _ (locTopology P T s hopen) 0 :=
        (locBasis P T s hopen).hasBasis_nhds_zero.mem_of_mem (i := n) trivial
      let : @IsTopologicalAddGroup _ (locTopology P T s hopen) _ :=
        @IsTopologicalRing.to_topologicalAddGroup _ _
          (locTopology P T s hopen)
          (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
      exact (locNhd P T s n).isOpen_of_mem_nhds hmem
    · exact locNhd_preimage_eq_locIdeal_pow P T s n
  · intro U hU
    rw [@nhds_induced, show (locSubring P T s).subtype (0 : locSubring P T s) =
        (0 : Localization.Away s) from map_zero _] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨n, -, hn⟩ := (locBasis P T s hopen).hasBasis_nhds_zero.mem_iff.mp hV
    exact ⟨n, fun x hx ↦ hVU (show (locSubring P T s).subtype x ∈ V from
      hn (locNhd_preimage_eq_locIdeal_pow P T s n ▸ hx : x ∈ _))⟩

end Basis

/-! ### Universal property of the localization topology (Wedhorn §5.51)

The localization topology is the coarsest ring topology on `Localization.Away s`
making `algebraMap : A → Localization.Away s` continuous. Equivalently: if `τ` is
any ring topology making `algebraMap` continuous, then `locTopology P T s hopen ≤ τ`.

**Proof idea:** Under a ring topology `τ` with `algebraMap` continuous:
- `algebraMap(val(P.I^n))` is a `τ`-neighborhood of 0 (continuous preimage).
- `locSubring P T s` generates the ring, and multiplication is `τ`-continuous.
- Each `locNhd P T s n` (image of `(locIdeal)^n`) is contained in a `τ`-neighborhood
  because it's an ideal of `locSubring` times the `algebraMap(val(P.I^n))` generators.

This requires showing that `locSubring P T s` is `τ`-bounded, which follows from
`algebraMap(P.A₀)` being bounded (continuous image of bounded set) and `{divByS t s}`
being finite. -/

section UniversalProperty

variable [IsTopologicalRing A]

/-! **Universal property of `locTopology`** (Wedhorn §5.51, Prop 8.2): a ring homomorphism
FROM `(Localization.Away s, locTopology)` to a nonarchimedean topological ring `B` is
continuous if:
(a) `f ∘ algebraMap : A → B` is continuous, AND
(b) `{f(t/s) : t ∈ T}` are power-bounded in `B`.

Both conditions are necessary: (a) alone does not imply continuity because
`f(locSubring)` being bounded requires power-boundedness of the generators `f(t/s)`.

**Proof strategy** (nested-neighborhood finite-generator induction):
1. Fix an open additive subgroup `W ⊆ B`. Enumerate `T = {t₁,...,tᵣ}`.
2. For each `zᵢ = f(divByS tᵢ s)`, power-boundedness gives `Wᵢ` with
   `zᵢⁿ · Wᵢ ⊆ Wᵢ₋₁`.
3. From `hf_alg`, choose `m` with `f(algebraMap(I^m)) ⊆ Wᵣ`.
4. Base case: `f(algebraMap(A₀) · algebraMap(I^m)) ⊆ Wᵣ` (since `A₀ · I^m ⊆ I^m`).
5. Inductive step: adjoin one generator at a time using the nested `Wᵢ` chain.
6. Conclusion: `f(locSubring · algebraMap(I^m)) ⊆ W`, giving `f(locNhd m) ⊆ W`.

**Wedhorn reference:** Proposition 5.51, Remark 5.33, Section 8.1.
The proof is split into three private helpers below, culminating in
`locTopology_continuous_lift`. -/

theorem locTopology_continuous_lift {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [NonarchimedeanRing B]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (f : Localization.Away s →+* B)
    (hf_alg : Continuous (f.comp (algebraMap A (Localization.Away s))))
    (hpow : ∀ t ∈ T, TopologicalRing.IsPowerBounded (f (divByS t s))) :
    @Continuous _ _ (locTopology P T s hopen) _ f := by
  set S₀ : Subring (Localization.Away s) := P.A₀.map (algebraMap A (Localization.Away s))
  have hbase : ∀ (G : OpenAddSubgroup B), ∃ m : ℕ,
      ∀ x ∈ S₀, ∀ b : P.A₀, b ∈ P.I ^ m →
        f (x * algebraMap A (Localization.Away s) (b : A)) ∈ (G : Set B) := by
    intro G
    have hcont : Filter.Tendsto (f.comp (algebraMap A (Localization.Away s)))
        (nhds 0) (nhds 0) := by
      rw [← map_zero (f.comp (algebraMap A _))]; exact hf_alg.continuousAt
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ (b : P.A₀), b ∈ P.I ^ m →
        f (algebraMap A (Localization.Away s) (b : A)) ∈ (G : Set B) := by
      rw [Filter.tendsto_def] at hcont
      obtain ⟨n, _, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp
        (hcont _ (G.isOpen.mem_nhds G.zero_mem))
      exact ⟨n, fun b hb ↦ hn ⟨b, hb, rfl⟩⟩
    refine ⟨m, fun x hx b hb ↦ ?_⟩
    obtain ⟨a₀, ha₀, rfl⟩ := hx
    rw [← map_mul (algebraMap A (Localization.Away s))]
    exact hm ⟨(a₀ : A) * (b : A), P.A₀.mul_mem ha₀ b.property⟩
      (Ideal.mul_mem_left _ ⟨a₀, ha₀⟩ hb)
  have hfull : ∀ (G : OpenAddSubgroup B), ∃ m : ℕ,
      ∀ x ∈ locSubring P T s, ∀ b : P.A₀, b ∈ P.I ^ m →
        f (x * algebraMap A (Localization.Away s) (b : A)) ∈ (G : Set B) := by
    suffices haux : ∀ (U : Finset A),
        (∀ t ∈ U, TopologicalRing.IsPowerBounded (f (divByS t s))) →
        ∀ (G : OpenAddSubgroup B), ∃ m : ℕ,
          ∀ x ∈ locSubring P U s, ∀ b : P.A₀, b ∈ P.I ^ m →
            f (x * algebraMap A (Localization.Away s) (b : A)) ∈ (G : Set B) by
      exact haux T hpow
    classical
    intro U
    induction U using Finset.induction with
    | empty =>
      intro _ G; obtain ⟨m, hm⟩ := hbase G
      have hempty : locSubring P ∅ s = S₀ := by
        unfold locSubring S₀
        simp only [Set.range_eq_empty, Set.union_empty]
        rw [← Subring.coe_map]; exact Subring.closure_eq _
      exact ⟨m, fun x hx b hb ↦ hm x (hempty ▸ hx) b hb⟩
    | insert t U' ht ih =>
      intro hpowU G
      have hinsert_le : locSubring P (insert t U') s ≤
          Subring.closure ((locSubring P U' s : Set _) ∪ {divByS t s}) := by
        unfold locSubring
        apply Subring.closure_le.mpr
        rintro x (⟨a₀, ha₀, rfl⟩ | ⟨⟨t', ht'⟩, rfl⟩)
        · exact Subring.subset_closure (Or.inl (Subring.subset_closure (Or.inl
            ⟨a₀, ha₀, rfl⟩)))
        · simp only [Finset.mem_insert] at ht'
          rcases ht' with rfl | ht'U
          · exact Subring.subset_closure (Or.inr rfl)
          · exact Subring.subset_closure (Or.inl (Subring.subset_closure (Or.inr
              ⟨⟨t', ht'U⟩, rfl⟩)))
      obtain ⟨V, hV, hzV⟩ := hpowU t (Finset.mem_insert_self t U')
        (G : Set B) (G.isOpen.mem_nhds G.zero_mem)
      obtain ⟨W, hWV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
      obtain ⟨m, hm⟩ := ih (fun t' ht' ↦ hpowU t' (Finset.mem_insert_of_mem ht')) W
      refine ⟨m, fun x hx b hb ↦ ?_⟩
      -- Represent `x` as a polynomial in `divByS t s` with coefficients in
      -- `locSubring P U' s`, via the `Algebra.adjoin` bridge.
      have hx_in_adj : x ∈ Algebra.adjoin ↥(locSubring P U' s)
          ({divByS t s} : Set (Localization.Away s)) := by
        have h_le : Subring.closure
            ((locSubring P U' s : Set (Localization.Away s)) ∪ {divByS t s}) ≤
              (Algebra.adjoin ↥(locSubring P U' s)
                ({divByS t s} : Set _)).toSubring := by
          rw [Subring.closure_le]
          rintro w (hw | rfl)
          · exact Subalgebra.algebraMap_mem _ (⟨w, hw⟩ : ↥(locSubring P U' s))
          · exact Algebra.subset_adjoin rfl
        exact h_le (hinsert_le hx)
      rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx_in_adj
      obtain ⟨p, hp⟩ := hx_in_adj
      rw [← hp, Polynomial.aeval_eq_sum_range, Finset.sum_mul, map_sum]
      refine G.toAddSubgroup.sum_mem (fun i _ ↦ ?_)
      rw [Algebra.smul_def, Algebra.algebraMap_ofSubsemiring_apply,
        show ((p.coeff i : Localization.Away s) * (divByS t s) ^ i) *
              algebraMap A (Localization.Away s) (b : A) =
            ((p.coeff i : Localization.Away s) *
              algebraMap A (Localization.Away s) (b : A)) *
              (divByS t s) ^ i from by ring, map_mul, map_pow, mul_comm]
      exact hzV (Set.mul_mem_mul ⟨i, rfl⟩
        (hWV (hm _ (p.coeff i).property b hb)))
  let : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  let : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  apply continuous_of_continuousAt_zero f.toAddMonoidHom
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro V hV
  obtain ⟨W, hWV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  obtain ⟨m, hm⟩ := hfull W
  exact Filter.mem_of_superset
    ((locBasis P T s hopen).hasBasis_nhds_zero.mem_iff.mpr ⟨m, trivial, le_refl _⟩)
    (fun x hx ↦ hWV (by
      obtain ⟨d, hd, rfl⟩ := hx
      rw [locIdeal, ← Ideal.map_pow] at hd
      suffices ∀ (r : locSubring P T s),
          f ((locSubring P T s).subtype (r * d)) ∈ (W : Set B) by
        specialize this 1; simp only [one_mul] at this; exact this
      intro r₀; revert r₀
      refine Submodule.span_induction (p := fun d _ ↦
          ∀ (r : locSubring P T s),
            f ((locSubring P T s).subtype (r * d)) ∈ (W : Set B)) ?_ ?_ ?_ ?_ hd
      · rintro _ ⟨b, hb, rfl⟩ r
        exact hm r.val r.property b hb
      · intro r; simp [mul_zero, map_zero]
      · intro d₁ d₂ _ _ h₁ h₂ r
        rw [show (locSubring P T s).subtype (r * (d₁ + d₂)) =
          (locSubring P T s).subtype (r * d₁) +
          (locSubring P T s).subtype (r * d₂) by simp [mul_add, map_add], map_add]
        exact W.toAddSubgroup.add_mem (h₁ r) (h₂ r)
      · intro c d _ hd r
        have : (locSubring P T s).subtype (r * c • d) =
            (locSubring P T s).subtype ((r * c) * d) := by
          congr 1; change r * (c * d) = (r * c) * d; ring
        rw [this]
        exact hd (r * c)))

end UniversalProperty

/-! ### The `hopen` condition for `s = 1` -/

/-- The `hopen` condition holds trivially when `s = 1`. -/
theorem hopen_away_one (P : PairOfDefinition A) (T : Finset A) :
    ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) (1 : A) ∈ locSubring P T (1 : A) :=
  ⟨0, fun b _ ↦ by rw [divByS_eq_algebraMap]; exact algebraMap_mem_locSubring P T 1 b.2⟩

/-! ### Remark 8.3 infrastructure: `D = A₀` when `s = 1`, `T = {1}` -/

/-- When `T = {1}` and `s = 1`, `D = A₀.map (algebraMap A Aₛ)`. -/
theorem locSubring_singleton_one (P : PairOfDefinition A) :
    locSubring P {1} (1 : A) =
      P.A₀.map (algebraMap A (Localization.Away (1 : A))) := by
  unfold locSubring
  have h_range : Set.range (fun t : ({1} : Finset A) ↦
      divByS (↑t : A) (1 : A)) ⊆
      (algebraMap A (Localization.Away (1 : A))) '' (P.A₀ : Set A) := by
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    simp only [Finset.mem_singleton] at ht; subst ht
    exact ⟨1, P.A₀.one_mem, (divByS_eq_algebraMap (1 : A)).symm ▸ rfl⟩
  rw [Set.union_eq_left.mpr h_range, ← Subring.coe_map]
  exact Subring.closure_eq _

/-- `algebraMapD` is surjective when `T = {1}` and `s = 1`. -/
theorem algebraMapD_surjective_one (P : PairOfDefinition A) :
    Function.Surjective (algebraMapD P {1} (1 : A)) := by
  intro ⟨x, hx⟩
  rw [locSubring_singleton_one] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩

section Remark83Topology

variable [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- The localization neighborhoods at `s = 1`, `T = {1}` are the images of `I^n`. -/
theorem locNhd_singleton_one_eq (P : PairOfDefinition A) (n : ℕ) :
    (locNhd P {1} (1 : A) n : Set (Localization.Away (1 : A))) =
      (algebraMap A (Localization.Away (1 : A))) ''
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) := by
  ext x; constructor
  · rintro ⟨d, hd, rfl⟩
    rw [locIdeal, ← Ideal.map_pow] at hd
    let : RingHomSurjective (algebraMapD P {1} (1 : A)) := ⟨algebraMapD_surjective_one P⟩
    rw [Ideal.map_eq_submodule_map] at hd
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hd
    exact ⟨↑b, ⟨b, hb, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨algebraMapD P {1} 1 b,
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hb, rfl⟩

/-- At `s = 1`, `T = {1}`, the localization topology has the same `0`-neighborhood basis as `A`. -/
theorem locTopology_hasBasis_singleton_one (P : PairOfDefinition A) :
    letI := locTopology P {1} (1 : A) (hopen_away_one P {1})
    (nhds (0 : Localization.Away (1 : A))).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (algebraMap A (Localization.Away (1 : A))) ''
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀))) :=
  (locBasis P {1} 1 (hopen_away_one P {1})).hasBasis_nhds_zero.congr
    (fun _ ↦ Iff.rfl) (fun n _ ↦ locNhd_singleton_one_eq P n)

end Remark83Topology

/-! ### `locSubring` is Noetherian when `P.A₀` is Noetherian and `T` is finite

T-LOC-SUBRING-NOETH: discharge `IsNoetherianRing (locSubring P T s)` from
`IsNoetherianRing P.A₀` and the finiteness of `T`. The proof routes
through `MvPolynomial.aeval`: locSubring is the image of an algebra
homomorphism `MvPolynomial T P.A₀ → locSubring P T s` sending `X_t ↦ t/s`.

This map is surjective because locSubring is by definition the
`Subring.closure` of `algebraMap '' P.A₀ ∪ {t/s : t ∈ T}`, which is
exactly the image of `MvPolynomial.aeval`. Surjective ring hom +
`MvPolynomial` Noetherian (by iterated Hilbert basis) gives Noetherian
of the codomain. -/
theorem locSubring_isNoetherianRing (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (T : Finset A) (s : A) :
    IsNoetherianRing (locSubring P T s) := by
  let : Algebra P.A₀ (locSubring P T s) := (algebraMapD P T s).toAlgebra
  let g : T → locSubring P T s := fun t ↦
    ⟨divByS t.1 s, divByS_mem_locSubring P T s t.2⟩
  let aeval_g : MvPolynomial T P.A₀ →ₐ[P.A₀] locSubring P T s := MvPolynomial.aeval g
  have h_surj : Function.Surjective aeval_g := by
    intro x
    have hx_mem : x.1 ∈ Subring.closure
        ((algebraMap A (Localization.Away s)) '' (P.A₀ : Set A) ∪
         Set.range (fun t : T ↦ divByS (t : A) s)) := x.2
    -- Show that aeval_g hits every element of this closure (lifted to locSubring).
    -- Strategy: use Subring.closure_induction to walk the closure and produce a
    -- polynomial witness at each step.
    suffices h : ∃ p : MvPolynomial T P.A₀, (aeval_g p).1 = x.1 by
      obtain ⟨p, hp⟩ := h
      exact ⟨p, Subtype.ext hp⟩
    refine Subring.closure_induction
      (p := fun y _ ↦ ∃ p : MvPolynomial T P.A₀, (aeval_g p).1 = y)
      ?_ ?_ ?_ ?_ ?_ ?_ hx_mem
    · -- mem case: y ∈ algebraMap '' P.A₀ ∪ Set.range (divByS · s)
      intro y hy
      rcases hy with hy_alg | hy_range
      · obtain ⟨a, ha, rfl⟩ := hy_alg
        refine ⟨MvPolynomial.C ⟨a, ha⟩, ?_⟩
        show (aeval_g (MvPolynomial.C ⟨a, ha⟩)).1 = algebraMap A _ a
        simp only [aeval_g, MvPolynomial.aeval_C]
        rfl
      · obtain ⟨⟨t, ht⟩, rfl⟩ := hy_range
        refine ⟨MvPolynomial.X ⟨t, ht⟩, ?_⟩
        change (aeval_g (MvPolynomial.X ⟨t, ht⟩)).1 = divByS (t : A) s
        simp only [aeval_g, MvPolynomial.aeval_X, g]
    · -- zero case
      exact ⟨0, by simp [aeval_g]⟩
    · -- one case
      exact ⟨1, by simp [aeval_g]⟩
    · -- add case
      rintro y₁ y₂ _ _ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
      refine ⟨p₁ + p₂, ?_⟩
      change (aeval_g (p₁ + p₂)).1 = y₁ + y₂
      rw [map_add]; exact congr_arg₂ (· + ·) hp₁ hp₂
    · -- neg case
      rintro y _ ⟨p, hp⟩
      refine ⟨-p, ?_⟩
      change (aeval_g (-p)).1 = -y
      rw [map_neg]; exact congr_arg Neg.neg hp
    · -- mul case
      rintro y₁ y₂ _ _ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
      refine ⟨p₁ * p₂, ?_⟩
      change (aeval_g (p₁ * p₂)).1 = y₁ * y₂
      rw [map_mul]; exact congr_arg₂ (· * ·) hp₁ hp₂
  let : Fintype T := inferInstance
  let : IsNoetherianRing (MvPolynomial T P.A₀) :=
    MvPolynomial.isNoetherianRing
  exact isNoetherianRing_of_surjective _ _ aeval_g.toRingHom h_surj

/-- Instance version of `locSubring_isNoetherianRing`, so `IsNoetherianRing
(locSubring P T s)` is auto-derived from `IsNoetherianRing P.A₀` by
typeclass synthesis. -/
instance locSubring_isNoetherianRing_instance (P : PairOfDefinition A)
    [IsNoetherianRing P.A₀] (T : Finset A) (s : A) :
    IsNoetherianRing (locSubring P T s) :=
  locSubring_isNoetherianRing P T s

/-! ### Boundedness in the localization topology (Wedhorn Lemma 7.20 substrate)

`locSubring` is a ring of definition of the localization topology, hence bounded; the
canonical map `A → Aₛ` carries bounded (resp. power-bounded) subsets to bounded
(resp. power-bounded) ones. These feed Wedhorn Prop 7.19 / Lemma 7.20 for the plus
subring of `𝒪_X(R(T/s))` (`Presheaf.lean`). -/

/-- `locSubring` is bounded in the localization topology: it is a ring of definition
(ideal absorption `locSubring · locNhd n ⊆ locNhd n`).
Source: Wedhorn §6.1 (6.1.2) / Lemma 7.20 context. Pair-level (unbundled) form of
`locSubring_isBounded` (PresheafIdentification.lean, `RationalLocData`-bundled, proven) —
this one is available upstream, in `Presheaf.lean`; the two are dedup targets for cleanup. -/
theorem locSubring_isBounded_of_pair [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N → divByS (↑b : A) s ∈ locSubring P T s) :
    letI := locTopology P T s hopen
    TopologicalRing.IsBounded (locSubring P T s : Set (Localization.Away s)) := by
  let : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  have hbasis := (locBasis P T s hopen).hasBasis_nhds_zero
  intro U hU
  obtain ⟨k, -, hkU⟩ := hbasis.mem_iff.mp hU
  refine ⟨locNhd P T s k, hbasis.mem_of_mem trivial, ?_⟩
  intro z hz
  obtain ⟨d, hd, v, hv, rfl⟩ := Set.mem_mul.mp hz
  apply hkU
  obtain ⟨jv, hjv, rfl⟩ := hv
  exact ⟨⟨d, hd⟩ * jv, Ideal.mul_mem_left _ _ hjv, MulMemClass.coe_mul ..⟩

/-- The canonical map `A → Aₛ` carries bounded subsets to bounded subsets of the
localization topology: `locNhd`-neighbourhoods absorb images of `A`-bounded sets.
Source: Wedhorn Lemma 7.20 (p. 61) context (the polynomial part `b` and tail `c` of
`a = b + c` are power-bounded because `A`-bounded data stays bounded in `A⟨X⟩_T`). -/
theorem isBounded_image_algebraMap_of_isBounded [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N → divByS (↑b : A) s ∈ locSubring P T s)
    {S : Set A} (hS : TopologicalRing.IsBounded S) :
    letI := locTopology P T s hopen
    TopologicalRing.IsBounded (algebraMap A (Localization.Away s) '' S) := by
  let : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  have hbasis := (locBasis P T s hopen).hasBasis_nhds_zero
  intro U hU
  obtain ⟨n, -, hnU⟩ := hbasis.mem_iff.mp hU
  -- `A`-side absorption: `S * (image of I^m) ⊆ image of I^n`.
  obtain ⟨W, hW, hSW⟩ := hS (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀))
    ((P.pow_image_isOpen n).mem_nhds ⟨0, (P.I ^ n).zero_mem, rfl⟩)
  obtain ⟨m, -, hmW⟩ := P.hasBasis_nhds_zero.mem_iff.mp hW
  refine ⟨locNhd P T s m, hbasis.mem_of_mem trivial, ?_⟩
  intro z hz
  obtain ⟨y, ⟨x, hxS, rfl⟩, v, hv, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨d, hd, rfl⟩ := hv
  apply hnU
  -- `∀ d ∈ locIdeal^m`, `(algebraMap x) * ↑d ∈ locNhd n`, by span induction.
  rw [locIdeal, ← Ideal.map_pow, ← Ideal.span_eq (P.I ^ m), Ideal.map_span] at hd
  refine Submodule.span_induction
    (p := fun d _ ↦ algebraMap A (Localization.Away s) x * ↑d ∈ locNhd P T s n)
    ?_ ?_ ?_ ?_ hd
  · rintro d ⟨b, hb, rfl⟩
    change algebraMap A (Localization.Away s) x * algebraMap A _ ↑b ∈ _
    rw [← map_mul]
    obtain ⟨b', hb'n, heq⟩ := hSW (Set.mul_mem_mul hxS (hmW ⟨b, hb, rfl⟩))
    rw [← heq]
    exact ⟨algebraMapD P T s b',
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hb'n, rfl⟩
  · simp only [ZeroMemClass.coe_zero, mul_zero]
    exact zero_mem_locNhd P T s n
  · intro d1 d2 _ _ h1 h2
    simp only [AddMemClass.coe_add, mul_add]
    exact (locNhd P T s n).add_mem h1 h2
  · intro r d1 _ h1
    rw [show (↑(r • d1) : Localization.Away s) = ↑r * ↑d1 from MulMemClass.coe_mul ..,
      mul_left_comm]
    obtain ⟨d'', hd'', heq⟩ := h1
    rw [← heq]
    exact ⟨r * d'', Ideal.mul_mem_left _ _ hd'', MulMemClass.coe_mul ..⟩

/-- Power-bounded elements of `A` map to power-bounded elements of the localization
topology. Source: Wedhorn Lemma 7.20 (p. 61, "`b` … power-bounded"). -/
theorem isPowerBounded_algebraMap_of_isPowerBounded [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N → divByS (↑b : A) s ∈ locSubring P T s)
    {a : A} (ha : TopologicalRing.IsPowerBounded a) :
    letI := locTopology P T s hopen
    TopologicalRing.IsPowerBounded (algebraMap A (Localization.Away s) a) := by
  let : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  have h : Set.range ((algebraMap A (Localization.Away s) a) ^ · : ℕ → Localization.Away s) =
      algebraMap A (Localization.Away s) '' Set.range (a ^ · : ℕ → A) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨a ^ n, ⟨n, rfl⟩, map_pow _ a n⟩
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (map_pow _ a n).symm⟩
  show TopologicalRing.IsBounded
    (Set.range ((algebraMap A (Localization.Away s) a) ^ · : ℕ → Localization.Away s))
  rw [h]
  exact isBounded_image_algebraMap_of_isBounded P T s hopen ha

end ValuationSpectrum
