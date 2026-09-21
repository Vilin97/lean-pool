/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Quotient.Operations
import LeanPool.UniformSheafyTateDomains.AdicSpaces.GeometricSeries

/-!
# Bounded Subsets and Power-Bounded Elements

We define **bounded subsets**, **power-bounded elements**, and **topologically nilpotent
elements** for topological rings, following §5 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `TopologicalRing.IsBounded S` : A subset `S` of a topological ring is bounded if for every
  neighbourhood `U` of `0`, there exists a neighbourhood `V` of `0` with `S * V ⊆ U`
  (Definition 5.27 of Wedhorn).
* `TopologicalRing.IsPowerBounded a` : An element `a` is power-bounded if `{aⁿ | n ∈ ℕ}` is
  bounded (Definition 5.27 of Wedhorn).
* `TopologicalRing.powerBoundedSubring A` : The set `A°` of all power-bounded elements.
* `TopologicalRing.topologicallyNilpotentElements A` : The set `A°°` of all topologically
  nilpotent elements.

## Main results

* `IsBounded.subset` : Subsets of bounded sets are bounded.
* `IsBounded.union` : Union of bounded sets is bounded.
* `IsBounded.mul` : Product of bounded sets is bounded.
* `IsBounded.add` : Sum of bounded sets is bounded.
* `isPowerBounded_add` : In a non-archimedean ring, the sum of power-bounded elements is
  power-bounded (Proposition 5.30(3) of Wedhorn).
* `powerBoundedSubring.toSubring` : `A°` is a subring in a non-archimedean ring
  (Proposition 5.30(3) of Wedhorn).
* `IsTopologicallyNilpotent.isPowerBounded` : Topologically nilpotent implies power-bounded
  (Remark 5.28(4) of Wedhorn).
* `IsPowerBounded.isTopologicallyNilpotent_mul` : Product of power-bounded and topologically
  nilpotent is topologically nilpotent (Remark 5.28(5) of Wedhorn).
* `IsTopologicallyNilpotent.of_pow` : `A°°` is radical: if `a^m ∈ A°°` then `a ∈ A°°`
  (Proposition 5.30(4) of Wedhorn).
* `IsBounded.isPowerBounded_of_isIntegral` : `A°` is integrally closed
  (Proposition 5.30(4) of Wedhorn).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 5.25, Definition 5.27,
  Proposition 5.30
-/

open Filter Topology Pointwise Polynomial

-- INFRASTRUCTURE (not in Wedhorn): a linear topology (open *ideals* form a neighbourhood basis
-- at `0`) is in particular non-archimedean (open *additive subgroups* form a neighbourhood basis),
-- since every ideal is an additive subgroup. This lets any genuine `[IsLinearTopology A A]`
-- consumer reuse the non-archimedean `A°` API (`powerBoundedSubring.toSubring`,
-- `isPowerBounded_add`) without restating hypotheses. Kept as a plain lemma (NOT a global
-- `instance`) so it does not enlarge typeclass search for `NonarchimedeanAddGroup` elsewhere;
-- supply it locally with `haveI := IsLinearTopology.nonarchimedeanAddGroup`. -/
theorem IsLinearTopology.nonarchimedeanAddGroup
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] :
    NonarchimedeanAddGroup A where
  is_nonarchimedean := by
    intro U hU
    obtain ⟨I, hIopen, hIU⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
    exact ⟨⟨I.toAddSubgroup, hIopen⟩, hIU⟩

namespace TopologicalRing

/-! ### Bounded subsets -/

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A subset is bounded if for every nhd `U` of `0`, some nhd `V` satisfies `S * V ⊆ U`. -/
def IsBounded (S : Set A) : Prop :=
  ∀ U ∈ 𝓝 (0 : A), ∃ V ∈ 𝓝 (0 : A), S * V ⊆ U

/-- Subsets of bounded sets are bounded. -/
theorem IsBounded.subset {S T : Set A} (hS : IsBounded S) (hTS : T ⊆ S) : IsBounded T :=
  fun U hU ↦ let ⟨V, hV, hSV⟩ := hS U hU
  ⟨V, hV, (Set.mul_subset_mul_right hTS).trans hSV⟩

/-- The empty set is bounded. -/
theorem isBounded_empty : IsBounded (∅ : Set A) :=
  fun U _ ↦ ⟨Set.univ, univ_mem, by simp⟩

/-- The singleton `{0}` is bounded. -/
theorem isBounded_singleton_zero : IsBounded ({0} : Set A) :=
  fun U hU ↦ ⟨Set.univ, univ_mem, fun _ hx ↦ by
    obtain ⟨a, rfl, _, _, rfl⟩ := Set.mem_mul.mp hx; simp [mem_of_mem_nhds hU]⟩

/-- The pair `{0, 1}` is bounded. -/
theorem isBounded_pair_zero_one : IsBounded ({0, 1} : Set A) :=
  fun U hU ↦ ⟨U, hU, fun _ hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rw [zero_mul]; exact mem_of_mem_nhds hU
    · rwa [Set.mem_singleton_iff.mp ha, one_mul]⟩

/-- Union of two bounded sets is bounded (Remark 5.28(3)). -/
theorem IsBounded.union {S T : Set A} (hS : IsBounded S) (hT : IsBounded T) :
    IsBounded (S ∪ T) := by
  intro U hU
  obtain ⟨V₁, hV₁, hSV⟩ := hS U hU; obtain ⟨V₂, hV₂, hTV⟩ := hT U hU
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
  rw [Set.union_mul]; exact Set.union_subset
    ((Set.mul_subset_mul_left Set.inter_subset_left).trans hSV)
    ((Set.mul_subset_mul_left Set.inter_subset_right).trans hTV)

/-- Product of two bounded sets is bounded. -/
theorem IsBounded.mul {S T : Set A}
    (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S * T) := by
  intro U hU
  obtain ⟨W, hW, hTW⟩ := hT U hU; obtain ⟨V, hV, hSV⟩ := hS W hW
  exact ⟨V, hV, mul_comm S T ▸ mul_assoc T S V ▸ (Set.mul_subset_mul_left hSV).trans hTW⟩

/-- Every singleton is bounded (Remark 5.28(1)). -/
theorem isBounded_singleton [IsTopologicalRing A] (a : A) : IsBounded ({a} : Set A) := by
  intro U hU
  refine ⟨(a * ·) ⁻¹' U,
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simp [hU]), ?_⟩
  rintro _ ⟨b, hb, c, hc, rfl⟩; rwa [Set.mem_singleton_iff.mp hb]

/-- Every finite subset is bounded (Remark 5.28(1)). -/
theorem isBounded_finite [IsTopologicalRing A] {S : Set A} (hS : S.Finite) :
    IsBounded S := by
  refine @Set.Finite.induction_on A (fun s _ ↦ IsBounded s) S hS ?_ ?_
  · exact isBounded_empty
  · intro a s _ _ ih; exact Set.insert_eq a s ▸ (isBounded_singleton a).union ih

/-! ### Power-bounded elements -/

/-- An element is power-bounded if `{aⁿ | n}` is bounded (Definition 5.27). -/
def IsPowerBounded (a : A) : Prop :=
  IsBounded (Set.range (a ^ · : ℕ → A))

/-- The set `A°` of all power-bounded elements. -/
def powerBoundedSubring (A : Type*) [CommRing A] [TopologicalSpace A] : Set A :=
  {a : A | IsPowerBounded a}

/-- `0` is power-bounded. -/
theorem isPowerBounded_zero : IsPowerBounded (0 : A) := by
  apply isBounded_pair_zero_one.subset; rintro _ ⟨n, rfl⟩
  rcases n with _ | n <;> simp [zero_pow]

/-- `1` is power-bounded. -/
theorem isPowerBounded_one : IsPowerBounded (1 : A) := by
  apply isBounded_pair_zero_one.subset; rintro _ ⟨n, rfl⟩; simp

/-- `-a` is power-bounded if `a` is (Prop 5.30(3)). -/
theorem isPowerBounded_neg [IsTopologicalRing A] {a : A} (ha : IsPowerBounded a) :
    IsPowerBounded (-a) := by
  apply (((isBounded_singleton (-1)).union (isBounded_singleton 1)).mul ha).subset
  rintro _ ⟨n, rfl⟩; change (-a) ^ n ∈ _; rw [neg_pow]
  exact Set.mul_mem_mul (by rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    simp [hk, pow_succ]) ⟨n, rfl⟩

/-- `a * b` is power-bounded if `a` and `b` are (Prop 5.30(3)). -/
theorem isPowerBounded_mul {a b : A}
    (ha : IsPowerBounded a) (hb : IsPowerBounded b) : IsPowerBounded (a * b) := by
  apply (ha.mul hb).subset; rintro _ ⟨n, rfl⟩
  simp only [mul_pow]; exact Set.mul_mem_mul ⟨n, rfl⟩ ⟨n, rfl⟩

/-- Sum of two power-bounded elements is power-bounded in a nonarchimedean ring (Prop 5.30(3)). -/
theorem isPowerBounded_add [IsTopologicalRing A] [NonarchimedeanAddGroup A]
    {a b : A} (ha : IsPowerBounded a) (hb : IsPowerBounded b) :
    IsPowerBounded (a + b) := by
  -- Wedhorn Prop 5.30: the non-archimedean (open additive subgroup) structure, NOT a linear
  -- (open-ideal) topology — Tate rings have no proper open ideals, so `IsLinearTopology A A`
  -- is false for them; an open additive subgroup `G` absorbs both `∑` and ℕ-multiplication.
  have hS := ha.mul hb
  intro U hU
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  obtain ⟨V, hV, hSV⟩ := hS (G : Set A) (G.isOpen.mem_nhds G.zero_mem')
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨_, ⟨n, rfl⟩, v, hv, rfl⟩
  apply hGU; change (a + b) ^ n * v ∈ (G : Set A); rw [add_pow, Finset.sum_mul]
  refine sum_mem fun m _ ↦ ?_
  rw [show a ^ m * b ^ (n - m) * ↑(n.choose m) * v =
      ↑(n.choose m) * (a ^ m * b ^ (n - m) * v) by ring, ← nsmul_eq_mul]
  exact nsmul_mem (hSV (Set.mul_mem_mul (Set.mul_mem_mul ⟨m, rfl⟩ ⟨n - m, rfl⟩) hv)) _

/-- `A°` is a subring in a nonarchimedean topological ring (Prop 5.30(3)). -/
def powerBoundedSubring.toSubring (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [NonarchimedeanAddGroup A] : Subring A where
  carrier := powerBoundedSubring A
  mul_mem' := isPowerBounded_mul
  one_mem' := isPowerBounded_one
  add_mem' := isPowerBounded_add
  zero_mem' := isPowerBounded_zero
  neg_mem' := isPowerBounded_neg

/-! ### Topologically nilpotent elements -/

/-- The set `A°°` of all topologically nilpotent elements (Definition 5.25). -/
def topologicallyNilpotentElements (A : Type*) [CommRing A] [TopologicalSpace A] : Set A :=
  {a : A | IsTopologicallyNilpotent a}

/-- Topologically nilpotent implies power-bounded (Remark 5.28(4)). -/
theorem IsTopologicallyNilpotent.isPowerBounded [IsTopologicalRing A] {a : A}
    (ha : IsTopologicallyNilpotent a) : IsPowerBounded a := by
  intro U hU
  have hmul : (fun p : A × A ↦ p.1 * p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_mul.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at hmul
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp hmul
  obtain ⟨N, hN⟩ := (ha.eventually hU₁).exists_forall_of_atTop
  have hfin (i : Fin N) : ∃ V ∈ 𝓝 (0 : A), {a ^ (i : ℕ)} * V ⊆ U :=
    isBounded_singleton (a ^ (i : ℕ)) U hU
  choose V hV_mem hV_sub using hfin
  refine ⟨U₂ ∩ ⋂ i, V i, inter_mem hU₂ (Filter.iInter_mem.mpr hV_mem), ?_⟩
  intro x hx; obtain ⟨_, ⟨n, rfl⟩, c, hc, rfl⟩ := Set.mem_mul.mp hx
  by_cases hn : n < N
  · exact hV_sub ⟨n, hn⟩
      (Set.mem_mul.mpr ⟨a ^ n, rfl, c, Set.mem_iInter.mp hc.2 ⟨n, hn⟩, rfl⟩)
  · exact hprod (Set.mk_mem_prod (hN n (by omega)) hc.1)

/-- Sum of two topologically nilpotent elements is topologically nilpotent in a
nonarchimedean ring (Wedhorn Remark 5.28(5) + Prop 5.30(1), the two-case binomial bound).

This is the non-archimedean replacement for mathlib's `IsTopologicallyNilpotent.add`, which is
stated with `[IsLinearTopology R R]` — the wrong hypothesis for Tate rings (a topologically
nilpotent unit forces every open ideal to be `⊤`, so `IsLinearTopology` is unsatisfiable). The
open *additive subgroup* basis supplied by `NonarchimedeanAddGroup` absorbs both the binomial
sum and the `ℕ`-multiplication, which is all the argument needs. -/
theorem IsTopologicallyNilpotent.add_of_nonarch [IsTopologicalRing A] [NonarchimedeanAddGroup A]
    {a b : A} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) := by
  -- `IsTopologicallyNilpotent x = Tendsto (x ^ ·) atTop (𝓝 0)`.
  have ha_pb : IsPowerBounded a := IsTopologicallyNilpotent.isPowerBounded ha
  have hb_pb : IsPowerBounded b := IsTopologicallyNilpotent.isPowerBounded hb
  rw [IsTopologicallyNilpotent, Filter.tendsto_def]
  intro U hU
  -- Shrink `U` to an open additive subgroup `G ⊆ U`.
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  -- `a` power-bounded at `G`: `range (a ^ ·) * Wa ⊆ G`; `b ^ j ∈ Wa` for `j ≥ Mb`.
  obtain ⟨Wa, hWa, hWa_sub⟩ := ha_pb (G : Set A) (G.isOpen.mem_nhds G.zero_mem')
  obtain ⟨Mb, hMb⟩ :=
    (Filter.Tendsto.eventually_mem hb hWa).exists_forall_of_atTop
  -- `b` power-bounded at `G`: `range (b ^ ·) * Wb ⊆ G`; `a ^ k ∈ Wb` for `k ≥ Ma`.
  obtain ⟨Wb, hWb, hWb_sub⟩ := hb_pb (G : Set A) (G.isOpen.mem_nhds G.zero_mem')
  obtain ⟨Ma, hMa⟩ :=
    (Filter.Tendsto.eventually_mem ha hWb).exists_forall_of_atTop
  -- For `n ≥ Ma + Mb`, every binomial term `aᵏ b^(n-k)` lands in `G`.
  rw [Filter.mem_atTop_sets]
  refine ⟨Ma + Mb, fun n hn ↦ ?_⟩
  rw [Set.mem_preimage]
  apply hGU
  show (a + b) ^ n ∈ (G : Set A)
  rw [add_pow]
  refine sum_mem fun k hk ↦ ?_
  rw [mul_comm, ← nsmul_eq_mul]
  refine nsmul_mem ?_ _
  rw [Finset.mem_range] at hk
  -- Either `n - k ≥ Mb` (use `a` power-bounded) or `k ≥ Ma` (use `b` power-bounded).
  by_cases hcase : Mb ≤ n - k
  · -- `aᵏ · b^(n-k) ∈ range (a ^ ·) * Wa ⊆ G`.
    exact hWa_sub (Set.mul_mem_mul ⟨k, rfl⟩ (hMb (n - k) hcase))
  · -- Then `k ≥ Ma`, so `aᵏ · b^(n-k) = b^(n-k) · aᵏ ∈ range (b ^ ·) * Wb ⊆ G`.
    have hk_ge : Ma ≤ k := by omega
    rw [mul_comm]
    exact hWb_sub (Set.mul_mem_mul ⟨n - k, rfl⟩ (hMa k hk_ge))

/-- `A°°` is contained in `A°` (Remark 5.28(4)). -/
theorem topologicallyNilpotentElements_subset_powerBoundedSubring [IsTopologicalRing A] :
    topologicallyNilpotentElements A ⊆ powerBoundedSubring A :=
  fun _ ↦ IsTopologicallyNilpotent.isPowerBounded

/-- Product of power-bounded and topologically nilpotent is topologically nilpotent. -/
theorem IsPowerBounded.isTopologicallyNilpotent_mul [IsTopologicalRing A] {a b : A}
    (ha : IsPowerBounded a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) := by
  intro U hU; obtain ⟨V, hV, hSV⟩ := ha U hU
  rw [Filter.mem_map]; exact Filter.mem_of_superset (Filter.mem_map.mp (hb hV)) fun n hn ↦
    show (a * b) ^ n ∈ U from
      mul_pow a b n ▸ hSV (Set.mul_mem_mul ⟨n, rfl⟩ hn)

/-- `-a` is topologically nilpotent if `a` is (Prop 5.30, non-archimedean: `-a = (-1)·a`
with `-1` power-bounded). -/
theorem IsTopologicallyNilpotent.neg [IsTopologicalRing A] {a : A}
    (ha : IsTopologicallyNilpotent a) : IsTopologicallyNilpotent (-a) := by
  rw [← neg_one_mul]
  exact (isPowerBounded_neg isPowerBounded_one).isTopologicallyNilpotent_mul ha

/-- The topologically nilpotent elements `A°°` form an **additive subgroup of `A`**
(non-archimedean: open additive subgroups absorb sums — Wedhorn Def 5.23 / Prop 5.30).
Note `A°°` is NOT an ideal of `A` for a Tate ring (it contains a topologically nilpotent
*unit*, so it would contain `1`); it is an ideal of `A°` (`topNilpIdeal`) and this additive
subgroup of `A`. This is the faithful object for "`A°°` is open" (`NonarchimedeanAddGroup`,
no `IsLinearTopology`). -/
def topNilpAddSubgroup (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [NonarchimedeanAddGroup A] : AddSubgroup A where
  carrier := topologicallyNilpotentElements A
  zero_mem' := IsTopologicallyNilpotent.zero
  add_mem' := fun ha hb => IsTopologicallyNilpotent.add_of_nonarch ha hb
  neg_mem' := fun ha => IsTopologicallyNilpotent.neg ha

/-- `A°°` is radical: `a ^ m ∈ A°°` implies `a ∈ A°°` (Prop 5.30(4)). -/
theorem IsTopologicallyNilpotent.of_pow [IsTopologicalRing A] {a : A} {m : ℕ} (hm : 0 < m)
    (ha : IsTopologicallyNilpotent (a ^ m)) : IsTopologicallyNilpotent a := by
  have hfin : IsBounded (Set.range fun i : Fin m ↦ a ^ (i : ℕ)) :=
    isBounded_finite (Set.finite_range _)
  intro U hU
  obtain ⟨V, hV, hSV⟩ := hfin U hU
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (ha hV)
  refine Filter.mem_atTop_sets.mpr ⟨m * N, fun n hn ↦ ?_⟩
  rw [Set.mem_preimage, show a ^ n = a ^ (n % m) * (a ^ m) ^ (n / m) by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]]
  exact hSV (Set.mul_mem_mul ⟨⟨n % m, Nat.mod_lt n hm⟩, rfl⟩
    (hN _ ((Nat.le_div_iff_mul_le hm).mpr (by linarith))))

/-! ### Proposition 5.30 — A° is integrally closed -/

omit [TopologicalSpace A] in
/-- `aⁿ ∈ B` for positive `n` implies `a` is integral over `B`. -/
theorem isIntegral_of_pow_mem (B : Subring A) {a : A} {n : ℕ} (hn : 0 < n)
    (ha : a ^ n ∈ B) : IsIntegral (↥B) a :=
  ⟨X ^ n - C ⟨a ^ n, ha⟩, monic_X_pow_sub_C _ (by omega), by
    simp [sub_eq_zero]; rfl⟩

/-- Sum of two bounded sets is bounded. -/
theorem IsBounded.add [IsTopologicalRing A] {S T : Set A}
    (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S + T) := by
  intro U hU
  have hadd : (fun p : A × A ↦ p.1 + p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_add.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at hadd
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp hadd
  obtain ⟨V₁, hV₁, hSV⟩ := hS U₁ hU₁; obtain ⟨V₂, hV₂, hTV⟩ := hT U₂ hU₂
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, fun _ hx ↦ ?_⟩
  obtain ⟨_, ⟨s₀, hs₀, t₀, ht₀, rfl⟩, v, hv, rfl⟩ := Set.mem_mul.mp hx
  rw [add_mul]; exact hprod (Set.mk_mem_prod
    (hSV (Set.mul_mem_mul hs₀ hv.1))
    (hTV (Set.mul_mem_mul ht₀ hv.2)))

/-- A finite sum of bounded sets is bounded. -/
theorem isBounded_finset_sum [IsTopologicalRing A] {ι : Type*} (s : Finset ι)
    (f : ι → Set A) (hf : ∀ i ∈ s, IsBounded (f i)) :
    IsBounded (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact isBounded_singleton_zero
  | insert _ _ hni ih => rw [Finset.sum_insert hni]; exact
      (hf _ (Finset.mem_insert_self _ _)).add (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

omit [TopologicalSpace A] in
/-- Strong induction: every power `a ^ n` is a `B`-linear combination of `a ^ 0, …, a ^ (N-1)`,
given that `a ^ N` satisfies the monic relation `hp_rel`. Requires `N ≠ 0`. -/
private theorem pow_eq_lincomb_of_monic_rel {B : Subring A} {a : A} {N : ℕ}
    {p : (↥B)[X]} (_hN : N ≠ 0)
    (hp_rel : a ^ N = -(∑ i ∈ Finset.range N, (p.coeff i : A) * a ^ i)) :
    ∀ n, ∃ c : ℕ → ↥B, a ^ n = ∑ j ∈ Finset.range N, (c j : A) * a ^ j := by
  intro n; induction n using Nat.strongRecOn with
  | ind n ih =>
  by_cases hn : n < N
  · classical exact ⟨fun j ↦ if j = n then 1 else 0, by
      simp [apply_ite (Subtype.val), Finset.sum_ite_eq', Finset.mem_range.mpr hn]⟩
  · rw [not_lt] at hn
    choose d hd using fun i (hi : i ∈ Finset.range N) ↦
      ih (i + (n - N)) (by rw [Finset.mem_range] at hi; omega)
    refine ⟨fun j ↦ -(∑ i ∈ (Finset.range N).attach, p.coeff ↑i * d ↑i i.2 j), ?_⟩
    have step : a ^ n = -(∑ i ∈ (Finset.range N).attach,
        (p.coeff (i : ℕ) : A) * ∑ j ∈ Finset.range N, (d ↑i i.2 j : A) * a ^ j) := by
      calc a ^ n = a ^ (n - N) * a ^ N := by rw [← pow_add, Nat.sub_add_cancel hn]
        _ = -(∑ i ∈ Finset.range N, (p.coeff i : A) * a ^ (i + (n - N))) := by
            rw [hp_rel, mul_neg, neg_inj, Finset.mul_sum]; congr 1
            ext i; rw [mul_comm (a ^ (n - N)), mul_assoc, ← pow_add]
        _ = _ := by rw [← Finset.sum_attach]; congr 1
                    exact Finset.sum_congr rfl fun i _ ↦ by rw [hd ↑i i.2]
    rw [step]; simp_rw [Finset.mul_sum]
    rw [neg_inj.mpr (Finset.sum_comm ..), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast; simp only [Finset.sum_mul, neg_mul]; congr 1
    exact Finset.sum_congr rfl fun ⟨i, _⟩ _ ↦ by ring

/-- `A°` is integrally closed: integral over bounded implies power-bounded (Prop 5.30(4)). -/
theorem IsBounded.isPowerBounded_of_isIntegral [IsTopologicalRing A] {B : Subring A}
    (hB : IsBounded (B : Set A)) {a : A} (ha : IsIntegral (↥B) a) :
    IsPowerBounded a := by
  obtain ⟨p, hp_monic, hp_eval⟩ := ha
  set N := p.natDegree; set S := ∑ i ∈ Finset.range N, (B : Set A) * {a ^ i} with hS_def
  refine (isBounded_finset_sum (Finset.range N) (fun i ↦ (B : Set A) * {a ^ i})
    fun i _ ↦ hB.mul (isBounded_singleton _)).subset ?_
  rintro _ ⟨n, rfl⟩
  have hp_rel : a ^ N = -(∑ i ∈ Finset.range N, (p.coeff i : A) * a ^ i) := by
    rw [eval₂_eq_sum_range, Finset.sum_range_succ, hp_monic.coeff_natDegree, map_one, one_mul,
      add_comm] at hp_eval
    exact eq_neg_of_add_eq_zero_left hp_eval
  suffices key : ∀ n, ∃ c : ℕ → ↥B, a ^ n = ∑ j ∈ Finset.range N, (c j : A) * a ^ j by
    change a ^ n ∈ S; obtain ⟨c, hc⟩ := key n; rw [hc, hS_def]
    exact Set.finsetSum_mem_finsetSum _ _ _ fun j _ ↦ Set.mul_mem_mul (Subtype.coe_prop _) rfl
  by_cases hN : N = 0
  · intro n; refine ⟨0, ?_⟩; simp only [hN, Finset.range_zero, Finset.sum_empty]
    have h1 : (1 : A) = 0 := by simpa [hN] using hp_rel
    induction n with
    | zero => simpa using h1
    | succ m ihm => rw [pow_succ, ihm, zero_mul]
  exact pow_eq_lincomb_of_monic_rel hN hp_rel

/-! ### `A°` is integrally closed (Wedhorn Prop 5.30(2)+(4), pair-free forms)

Wedhorn states Prop 5.30 for arbitrary non-archimedean topological rings — no ring or
ideal of definition. The chain below keeps that generality: the prime subring is bounded;
the subring generated by finitely many power-bounded elements is bounded (5.30(2)); an
element integral over power-bounded elements is power-bounded (5.30(4)). This is the
pair-free form of `PairOfDefinition.isPowerBounded_of_monic_powerBounded_eval`
(`HuberRings.lean`), needed at the completions `𝒪_X(D)` where no `PairOfDefinition` is
available upstream of `Presheaf.lean`. -/

/-- The prime subring `⊥` is bounded in a nonarchimedean topological ring: an open
additive subgroup absorbs `ℤ`-multiples of its elements.
Source: Wedhorn Prop 5.30(2) (p. 37, base case). -/
theorem isBounded_bot [NonarchimedeanAddGroup A] :
    IsBounded ((⊥ : Subring A) : Set A) := by
  intro U hU
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  refine ⟨G, G.isOpen.mem_nhds G.zero_mem', ?_⟩
  rintro _ ⟨x, hx, v, hv, rfl⟩
  obtain ⟨n, rfl⟩ := Subring.mem_bot.mp hx
  show (n : A) * v ∈ U
  rw [show (n : A) * v = n • v from (zsmul_eq_mul v n).symm]
  exact hGU (zsmul_mem hv n)

/-- In a nonarchimedean topological ring, the additive subgroup generated by a bounded
set is bounded (Wedhorn Prop 5.30(1), bounded case, pair-free). -/
theorem isBounded_addSubgroupClosure [NonarchimedeanAddGroup A]
    {S : Set A} (hS : IsBounded S) :
    IsBounded (AddSubgroup.closure S : Set A) := by
  intro U hU
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  obtain ⟨V, hV, hSV⟩ := hS (G : Set A) (G.isOpen.mem_nhds G.zero_mem')
  have hcl : ∀ s ∈ AddSubgroup.closure S, ∀ w ∈ V, s * w ∈ (G : Set A) := by
    intro s hs
    induction hs using AddSubgroup.closure_induction with
    | mem x hx => intro w hw; exact hSV (Set.mul_mem_mul hx hw)
    | zero => intro w _; simp
    | add _ _ _ _ h₁ h₂ => intro w hw; rw [add_mul]; exact G.add_mem (h₁ w hw) (h₂ w hw)
    | neg _ _ h₁ => intro w hw; rw [neg_mul]; exact G.neg_mem (h₁ w hw)
  exact ⟨V, hV, fun z hz => by
    obtain ⟨s, hs, v, hv, rfl⟩ := Set.mem_mul.mp hz
    exact hGU (hcl s hs v hv)⟩

/-- **Wedhorn Prop 5.30(2)** (p. 37), finite case: the subring generated by finitely many
power-bounded elements of a nonarchimedean topological ring is bounded. -/
theorem isBounded_closure_finset_of_isPowerBounded [IsTopologicalRing A]
    [NonarchimedeanAddGroup A] {T : Finset A} (hT : ∀ t ∈ T, IsPowerBounded t) :
    IsBounded ((Subring.closure (T : Set A) : Subring A) : Set A) := by
  classical
  induction T using Finset.induction with
  | empty =>
    simp only [Finset.coe_empty, Subring.closure_empty]
    exact isBounded_bot
  | @insert a S ha ih =>
    have hT_S : ∀ t ∈ S, IsPowerBounded t :=
      fun t ht ↦ hT t (Finset.mem_insert_of_mem ht)
    specialize ih hT_S
    set B_old := Subring.closure (S : Set A) with hB_old
    have ha_pb : IsPowerBounded a := hT a (Finset.mem_insert_self a S)
    -- `B_old * range (a ^ ·)` is bounded (product of bounded sets)
    have hAM_bounded : IsBounded ((B_old : Set A) * Set.range (a ^ · : ℕ → A)) :=
      ih.mul ha_pb
    set BM := (B_old : Set A) * Set.range (a ^ · : ℕ → A) with hBM
    -- The additive closure of `BM` is closed under multiplication (products collapse).
    have hC_mul : ∀ x ∈ AddSubgroup.closure BM, ∀ y ∈ AddSubgroup.closure BM,
        x * y ∈ AddSubgroup.closure BM := by
      intro x hx y hy
      induction hx, hy using AddSubgroup.closure_induction₂ with
      | mem u v hu hv =>
        obtain ⟨b₁, hb₁, _, ⟨k₁, rfl⟩, rfl⟩ := Set.mem_mul.mp hu
        obtain ⟨b₂, hb₂, _, ⟨k₂, rfl⟩, rfl⟩ := Set.mem_mul.mp hv
        apply AddSubgroup.subset_closure
        rw [show b₁ * a ^ k₁ * (b₂ * a ^ k₂) = (b₁ * b₂) * a ^ (k₁ + k₂) by ring]
        exact Set.mul_mem_mul (B_old.mul_mem hb₁ hb₂) ⟨k₁ + k₂, rfl⟩
      | zero_left _ _ => simp
      | zero_right _ _ => simp
      | add_left _ _ _ _ _ _ ih₁ ih₂ =>
        rw [add_mul]; exact (AddSubgroup.closure BM).add_mem ih₁ ih₂
      | add_right _ _ _ _ _ _ ih₁ ih₂ =>
        rw [mul_add]; exact (AddSubgroup.closure BM).add_mem ih₁ ih₂
      | neg_left _ _ _ _ ih₁ =>
        rw [neg_mul]; exact (AddSubgroup.closure BM).neg_mem ih₁
      | neg_right _ _ _ _ ih₁ =>
        rw [mul_neg]; exact (AddSubgroup.closure BM).neg_mem ih₁
    have mem_BM (b : A) (hb : b ∈ B_old) (k : ℕ) : b * a ^ k ∈ BM :=
      Set.mul_mem_mul hb ⟨k, rfl⟩
    set C_subring : Subring A :=
      { carrier := AddSubgroup.closure BM
        mul_mem' := fun {_ _} ha hb ↦ hC_mul _ ha _ hb
        one_mem' := by
          rw [show (1 : A) = 1 * a ^ 0 by simp]
          exact AddSubgroup.subset_closure (mem_BM 1 B_old.one_mem 0)
        zero_mem' := (AddSubgroup.closure BM).zero_mem
        add_mem' := fun {_ _} ha hb ↦ (AddSubgroup.closure BM).add_mem ha hb
        neg_mem' := fun {_} ha ↦ (AddSubgroup.closure BM).neg_mem ha }
    have h_sub : ((insert a S : Finset A) : Set A) ⊆ (C_subring : Set A) := by
      rw [Finset.coe_insert]
      intro x hx
      change x ∈ (AddSubgroup.closure BM : Set A)
      rcases Set.mem_insert_iff.mp hx with hxa | hx_S
      · rw [hxa, show a = 1 * a ^ 1 by simp]
        exact AddSubgroup.subset_closure (mem_BM 1 B_old.one_mem 1)
      · rw [show x = x * a ^ 0 by simp]
        exact AddSubgroup.subset_closure
          (mem_BM x (Subring.subset_closure hx_S) 0)
    exact (isBounded_addSubgroupClosure hAM_bounded).subset (Subring.closure_le.mpr h_sub)

/-- **Wedhorn Prop 5.30(4)** (p. 37), pair-free: a root of a monic polynomial with
power-bounded coefficients is power-bounded. -/
theorem isPowerBounded_of_monic_eval_zero [IsTopologicalRing A] [NonarchimedeanAddGroup A]
    {x : A} {p : A[X]} (hp : p.Monic) (hcoeff : ∀ i, IsPowerBounded (p.coeff i))
    (heval : p.eval x = 0) : IsPowerBounded x := by
  classical
  set T : Finset A := (Finset.range (p.natDegree + 1)).image p.coeff with hT_def
  have hT_pb : ∀ t ∈ T, IsPowerBounded t := by
    intro t ht
    rw [hT_def, Finset.mem_image] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact hcoeff i
  set B' : Subring A := Subring.closure (T : Set A) with hB'_def
  have hB'_bounded : IsBounded (B' : Set A) := isBounded_closure_finset_of_isPowerBounded hT_pb
  have hcoeff_mem : ∀ i, p.coeff i ∈ B' := by
    intro i
    by_cases hi : i ≤ p.natDegree
    · exact Subring.subset_closure (Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
      exact B'.zero_mem
  have hcoeffs : (↑p.coeffs : Set A) ⊆ (B' : Set A) := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨i, _, rfl⟩ := hc
    exact hcoeff_mem i
  have hint : IsIntegral (↥B') x := by
    refine ⟨p.toSubring B' hcoeffs, ?_, ?_⟩
    · rw [Polynomial.monic_toSubring]; exact hp
    · show Polynomial.eval₂ (algebraMap (↥B') A) x (p.toSubring B' hcoeffs) = 0
      rw [Polynomial.eval₂_eq_eval_map,
        show (algebraMap (↥B') A) = B'.subtype from rfl, Polynomial.map_toSubring]
      exact heval
  exact hB'_bounded.isPowerBounded_of_isIntegral hint

/-- **Wedhorn Prop 5.30(4)** (p. 37): `A°` is integrally closed in `A` — an element
integral over a subring of power-bounded elements is power-bounded. -/
theorem isPowerBounded_of_isIntegral_of_subset_powerBounded [IsTopologicalRing A]
    [NonarchimedeanAddGroup A] {B : Subring A} (hB : (B : Set A) ⊆ powerBoundedSubring A)
    {x : A} (hx : IsIntegral (↥B) x) : IsPowerBounded x := by
  obtain ⟨p, hp_monic, hp_eval⟩ := hx
  refine isPowerBounded_of_monic_eval_zero (hp_monic.map B.subtype) (fun i ↦ ?_) ?_
  · rw [Polynomial.coeff_map]
    exact hB (p.coeff i).2
  · rw [Polynomial.eval_map]
    exact hp_eval

/-- Every element of a bounded subring is power-bounded (`{xⁿ} ⊆ B`).
Source: Wedhorn Remark 5.28(2) / Prop 5.30(3) context (pp. 36–37). -/
theorem IsBounded.isPowerBounded_of_mem {B : Subring A} (hB : IsBounded (B : Set A))
    {x : A} (hx : x ∈ B) : IsPowerBounded x := by
  apply hB.subset
  rintro _ ⟨n, rfl⟩
  exact B.pow_mem hx n

/-- The topological closure of a bounded set is bounded in a nonarchimedean topological
ring (absorb into a closed-open subgroup `G ⊆ U`).
Source: Wedhorn §5.6 context; used by Prop 7.19 / 8.16 at completions. -/
theorem IsBounded.closure [IsTopologicalRing A] [NonarchimedeanAddGroup A] {S : Set A}
    (hS : IsBounded S) : IsBounded (closure S) := by
  intro U hU
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  obtain ⟨V, hV, hSV⟩ := hS (G : Set A) (G.isOpen.mem_nhds G.zero_mem')
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨x, hx, v, hv, rfl⟩
  have hSv : S ⊆ (fun y ↦ y * v) ⁻¹' (G : Set A) :=
    fun s hs ↦ hSV (Set.mul_mem_mul hs hv)
  have hclosed : IsClosed ((fun y ↦ y * v) ⁻¹' (G : Set A)) :=
    G.isClosed.preimage (continuous_mul_right v)
  exact hGU (closure_minimal hSv hclosed hx)

end TopologicalRing

/-! ### Jacobson-radical building block: `1 - a*y` is a unit when `a` is
topologically nilpotent and `y` is power-bounded

For a complete Hausdorff nonarchimedean commutative ring, if `a` is
topologically nilpotent and `y` is power-bounded, the product `a*y` is
topologically nilpotent (Wedhorn Remark 5.28(5),
`IsPowerBounded.isTopologicallyNilpotent_mul`). Then `1 - a*y` is a unit
by the geometric-series argument (Wedhorn Prop 5.38,
`IsTopologicallyNilpotent.isUnit_one_sub`).

This is the project-specific Jacobson-radical building block: for an ideal
`I` whose elements are topologically nilpotent and whose ambient ring is
the power-bounded subring (`A° = TopologicalRing.powerBoundedSubring`),
every `1 - i*y` for `i ∈ I, y ∈ A°` is a unit. Useful for S-IDEAL-JAC of
T-IDEAL-2. -/

variable {A : Type*} [CommRing A]
  [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]

/-- `1 - a*y` is a unit when `a` is topologically nilpotent and `y` is
power-bounded. -/
theorem IsTopologicallyNilpotent.isUnit_one_sub_mul_of_isPowerBounded
    {a y : A} (ha : IsTopologicallyNilpotent a)
    (hy : TopologicalRing.IsPowerBounded y) :
    IsUnit (1 - a * y) := by
  rw [mul_comm a y]
  exact (hy.isTopologicallyNilpotent_mul ha).isUnit_one_sub

/-- Symmetric version: `1 - y*a` is a unit when `a` is topologically nilpotent
and `y` is power-bounded. -/
theorem IsTopologicallyNilpotent.isUnit_one_sub_mul_of_isPowerBounded_left
    {a y : A} (ha : IsTopologicallyNilpotent a)
    (hy : TopologicalRing.IsPowerBounded y) :
    IsUnit (1 - y * a) :=
  (hy.isTopologicallyNilpotent_mul ha).isUnit_one_sub

/-! ### Matrix Nakayama (BGR Lemma 1.2.4/6, for Remark 8.29 / Lemma 8.31)

`1 - B` is invertible when every entry of an `n × n` matrix `B` is topologically nilpotent.
Reduce to the scalar `isUnit_one_sub` via the determinant: over the power-bounded subring `A°`
(where the topologically nilpotent elements form the ideal `topNilpIdeal`), reduction mod
`topNilpIdeal` sends `1 - B` to the identity, so `det (1 - B) ≡ 1` and `det (1 - B) - 1` is
topologically nilpotent; `Matrix.isUnit_iff_isUnit_det` lifts the result back. This is the correct
form of "Nakayama 1.2.4/6": over a Tate ring the topologically nilpotent *elements* generate the
unit ideal (so the ideal-theoretic Nakayama is vacuous), but they form a genuine ideal of `A°`,
which is what the determinant argument uses. -/

open TopologicalRing in
/-- The topologically nilpotent elements form an ideal of the power-bounded subring `A°`. -/
def topNilpIdeal : Ideal (powerBoundedSubring.toSubring A) where
  carrier := {x | IsTopologicallyNilpotent (x : A)}
  zero_mem' := IsTopologicallyNilpotent.zero
  add_mem' := by
    intro x y hx hy
    show IsTopologicallyNilpotent ((x + y : powerBoundedSubring.toSubring A) : A)
    rw [Subring.coe_add]
    -- Wedhorn Remark 5.28(5): non-archimedean replacement for the linear-topology
    -- `IsTopologicallyNilpotent.add` (which is unsatisfiable for Tate rings).
    exact IsTopologicallyNilpotent.add_of_nonarch hx hy
  smul_mem' := by
    intro c x hx
    show IsTopologicallyNilpotent ((c • x : powerBoundedSubring.toSubring A) : A)
    rw [smul_eq_mul, Subring.coe_mul]
    exact (c.2 : IsPowerBounded (c : A)).isTopologicallyNilpotent_mul hx

open TopologicalRing in
omit [T2Space A] [CompleteSpace A] [IsUniformAddGroup A] in
/-- `1 - det (1 - B)` is topologically nilpotent when every entry of `B` is. -/
theorem IsTopologicallyNilpotent.one_sub_det_one_sub_matrix {n : Type*} [Fintype n]
    [DecidableEq n] (B : Matrix n n A)
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) :
    IsTopologicallyNilpotent (1 - (1 - B).det) := by
  let B' : Matrix n n (powerBoundedSubring.toSubring A) :=
    fun i j => ⟨B i j, (hB i j).isPowerBounded⟩
  have hB'_mem : ∀ i j, B' i j ∈ topNilpIdeal := fun i j => hB i j
  -- Reduction mod `topNilpIdeal` kills `B'`, so (working with the ring hom `mk.mapMatrix`)
  -- `mk.mapMatrix (1 - B') = 1`, hence `det (1 - B') ≡ 1`.
  have hzQ : (Ideal.Quotient.mk topNilpIdeal).mapMatrix B' = 0 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      (Ideal.Quotient.eq_zero_iff_mem).2 (hB'_mem i j)]
  have hone : (Ideal.Quotient.mk topNilpIdeal).mapMatrix (1 - B') = 1 := by
    rw [map_sub, map_one, hzQ]; abel
  have hquot : Ideal.Quotient.mk topNilpIdeal (1 - B').det = 1 := by
    rw [RingHom.map_det, hone]; exact Matrix.det_one
  -- Hence `det (1 - B') - 1 ∈ topNilpIdeal`, i.e. is topologically nilpotent.
  have hmem : IsTopologicallyNilpotent
      (((1 - B').det - 1 : powerBoundedSubring.toSubring A) : A) :=
    show ((1 - B').det - 1 : powerBoundedSubring.toSubring A) ∈ topNilpIdeal by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hquot, map_one]; abel
  -- Transfer back to `A`: the subring inclusion `mapMatrix` sends `1 - B'` to `1 - B`.
  have hsub : (powerBoundedSubring.toSubring A).subtype.mapMatrix (1 - B') = 1 - B := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
      map_sub, B']
  have hdet_eq : (1 - B).det
      = (powerBoundedSubring.toSubring A).subtype ((1 - B').det) := by
    rw [RingHom.map_det, hsub]
  rw [hdet_eq, show (1 : A) - (powerBoundedSubring.toSubring A).subtype ((1 - B').det)
      = -((powerBoundedSubring.toSubring A).subtype ((1 - B').det - 1)) by
      rw [map_sub, map_one]; ring]
  exact hmem.neg

/-- **Matrix Nakayama** (BGR Lemma 1.2.4/6, the form used in §3.7.2/1): if every entry of an
`n × n` matrix `B` over a complete Hausdorff nonarchimedean commutative ring `A` is topologically
nilpotent then `1 - B` is invertible. -/
theorem IsTopologicallyNilpotent.isUnit_one_sub_matrix {n : Type*} [Fintype n]
    [DecidableEq n] (B : Matrix n n A)
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) :
    IsUnit (1 - B) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simpa using (IsTopologicallyNilpotent.one_sub_det_one_sub_matrix B hB).isUnit_one_sub

omit [UniformSpace A] [T2Space A] [CompleteSpace A] [IsTopologicalRing A]
  [IsUniformAddGroup A] [NonarchimedeanAddGroup A] in
/-- **A unit matrix acts injectively on module-valued vectors.** If `B : Matrix n n A` is a
unit and `∑ⱼ Bᵢⱼ • yⱼ = 0` for every `i`, where `y : n → P` and `P` is any `A`-module, then
`y = 0`. This is the linear-algebra core of the Nakayama step in BGR §3.7.2/1: after passing
to the quotient `M̂ / M`, the defining relation becomes `∑ⱼ (1 - Ã)ᵥμ • ȳμ = 0` with `1 - Ã`
invertible, forcing `ȳ = 0`. -/
theorem eq_zero_of_isUnit_matrix_of_forall_sum_smul_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {P : Type*} [AddCommGroup P] [Module A P]
    {B : Matrix n n A} (hB : IsUnit B) {y : n → P}
    (hy : ∀ i, ∑ j, B i j • y j = 0) (k : n) : y k = 0 := by
  obtain ⟨u, rfl⟩ := hB
  obtain ⟨C, hC1, -⟩ : ∃ C : Matrix n n A,
      C * (↑u : Matrix n n A) = 1 ∧ (↑u : Matrix n n A) * C = 1 :=
    ⟨((u⁻¹ : (Matrix n n A)ˣ) : Matrix n n A), u.inv_mul, u.mul_inv⟩
  calc y k
      = ∑ j, (1 : Matrix n n A) k j • y j := by simp [Matrix.one_apply]
    _ = ∑ j, (C * (↑u : Matrix n n A)) k j • y j := by rw [hC1]
    _ = ∑ j, (∑ i, C k i * (↑u : Matrix n n A) i j) • y j := by simp_rw [Matrix.mul_apply]
    _ = ∑ j, ∑ i, (C k i * (↑u : Matrix n n A) i j) • y j := by simp_rw [Finset.sum_smul]
    _ = ∑ i, ∑ j, (C k i * (↑u : Matrix n n A) i j) • y j := Finset.sum_comm
    _ = ∑ i, C k i • ∑ j, (↑u : Matrix n n A) i j • y j := by
        simp_rw [Finset.smul_sum, mul_smul]
    _ = 0 := by simp [hy]

/-- The form of the matrix Nakayama used in BGR §3.7.2/1: if every entry of `B` is
topologically nilpotent and `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` for all `i` (a `P`-valued fixed-point
relation, `P` any `A`-module), then `y = 0`. -/
theorem eq_zero_of_forall_eq_sum_topNilp_smul    {n : Type*} [Fintype n] [DecidableEq n]
    {P : Type*} [AddCommGroup P] [Module A P]
    {B : Matrix n n A} (hB : ∀ i j, IsTopologicallyNilpotent (B i j))
    {y : n → P} (hy : ∀ i, y i = ∑ j, B i j • y j) (k : n) : y k = 0 := by
  refine eq_zero_of_isUnit_matrix_of_forall_sum_smul_eq_zero
    (IsTopologicallyNilpotent.isUnit_one_sub_matrix B hB) (y := y) ?_ k
  intro i
  have h1 : ∑ j, (1 - B : Matrix n n A) i j • y j
      = (∑ j, (1 : Matrix n n A) i j • y j) - ∑ j, B i j • y j := by
    simp_rw [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [h1, show (∑ j, (1 : Matrix n n A) i j • y j) = y i by simp [Matrix.one_apply],
    ← hy i, sub_self]
