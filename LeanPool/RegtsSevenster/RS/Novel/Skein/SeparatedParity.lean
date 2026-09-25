/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PathLedger

/-!
# The separated count parity

Discharges `SeparatedCountParity`: a separated repair square on a
localized configuration flips the circuit-count parity
(`Δ openCircuitCount = ±1`).

## Architecture

Instead of tracking the periodic-flag subtype (which changes across
the move in the chain-local cases), we close up the whole system
into a single permutation on **all** participating flags, the
*full walk* `Π = M ∘ σ`, where `σ` is the edge pairing and `M` is
the matching on internal flags extended by the path matching on
boundary flags.  Its orbits are the circuit orbits (two per
circuit) plus one orbit per boundary flag (each boundary chain
contributes its two traversal directions, each containing exactly
one boundary flag).  Hence

  `orbits Π = orbits (walkPermPeriodic) + boundaryFlags.card`.

Because a localized square leaves the path matching untouched
(`pathMatch_repair_of_localized`), the repaired full walk is the
old one multiplied by the double transposition `(a d)(b c)`.  An
abstract transposition lemma (multiplying by a swap changes the
orbit count by exactly one, splitting iff the swapped points share
an orbit) plus the mirror symmetry `σ Π σ = Π⁻¹` and the separated
orientation force the two swaps to act coherently: the orbit count
moves by exactly `±2`, i.e. the circuit count by `±1`.

## Main results

* `permOrbitCount_swap_mul_sameCycle` / `..._not_sameCycle` — the
  abstract transposition ledger for total orbit counts.
* `permOrbitCount_swap_swap_mul` — the coherent double swap.
* `EdgeSubset.fullPerm` — the closed-up walk permutation.
* `EdgeSubset.permOrbitCount_fullPerm_eq` — the orbit bookkeeping
  `orbits Π = orbits wpp + |B|`.
* `EdgeSubset.fullPerm_repair` — the move is the double swap.
* `separatedCountParity` — the discharged `SeparatedCountParity`.
-/

namespace RS



/-! ## (i) Abstract orbit counting -/

section AbstractOrbit

open Equiv Equiv.Perm

variable {Y : Type}

/-- The total orbit count of a permutation: nontrivial cycles plus
fixed points. -/
noncomputable def permOrbitCount [Fintype Y] [DecidableEq Y]
    (g : Perm Y) : ℕ :=
  g.cycleType.card + Fintype.card (Function.fixedPoints g)

/-- Fixed points and support partition the domain. -/
theorem card_fixedPoints_add_card_support [Fintype Y] [DecidableEq Y]
    (g : Perm Y) :
    Fintype.card (Function.fixedPoints g) + g.support.card =
      Fintype.card Y := by
  have h1 : Fintype.card (Function.fixedPoints g) =
      (Finset.univ.filter (fun x => g x = x)).card :=
    Fintype.card_subtype _
  have h2 : g.support = Finset.univ.filter (fun x => ¬ g x = x) := by
    ext x
    simp [Equiv.Perm.mem_support]
  rw [h1, h2, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not (fun x => g x = x)

/-- Reduce a permutation power at a recurrent point. -/
theorem perm_pow_mod {g : Perm Y} {x : Y} {p : ℕ} (_hp : 1 ≤ p)
    (hper : (g ^ p) x = x) (i : ℕ) :
    (g ^ i) x = (g ^ (i % p)) x := by
  have key : ∀ q r, (g ^ (p * q + r)) x = (g ^ r) x := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have hsplit : p * (q + 1) + r = (p * q + r) + p := by ring
      rw [hsplit, pow_add, Equiv.Perm.mul_apply]
      have hx : (g ^ p) x = x := hper
      rw [hx]
      exact ih r
  conv_lhs =>
    rw [show i = p * (i / p) + i % p from (Nat.div_add_mod i p).symm]
  exact key (i / p) (i % p)

/-- A `SameCycle` witness from a power. -/
theorem sameCycle_of_pow_eq {g : Perm Y} {x y : Y} {n : ℕ}
    (h : (g ^ n) x = y) : g.SameCycle x y :=
  ⟨(n : ℤ), by rw [zpow_natCast]; exact h⟩

/-- Trajectories avoiding both swapped points are untouched by the
swap. -/
private theorem swap_mul_pow_eq [DecidableEq Y]
    {g : Perm Y} {x y u : Y}
    (hx : ∀ k : ℕ, (g ^ k) u ≠ x) (hy : ∀ k : ℕ, (g ^ k) u ≠ y) :
    ∀ k : ℕ, ((Equiv.swap x y * g) ^ k) u = (g ^ k) u := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : ((Equiv.swap x y * g) ^ (k + 1)) u =
        (Equiv.swap x y * g) (((Equiv.swap x y * g) ^ k) u) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have h2 : (g ^ (k + 1)) u = g ((g ^ k) u) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [h1, ih, Equiv.Perm.mul_apply, ← h2,
      Equiv.swap_apply_of_ne_of_ne (hx (k + 1)) (hy (k + 1))]

/-- **Untouched orbits**: `SameCycle` from a point in neither
swapped orbit transfers across the swap-multiplication. -/
theorem sameCycle_swap_mul_iff [Fintype Y] [DecidableEq Y]
    {g : Perm Y} {x y u : Y}
    (hux : ¬ g.SameCycle u x) (huy : ¬ g.SameCycle u y) (v : Y) :
    (Equiv.swap x y * g).SameCycle u v ↔ g.SameCycle u v := by
  have hx : ∀ k : ℕ, (g ^ k) u ≠ x := by
    intro k hk
    exact hux (sameCycle_of_pow_eq hk)
  have hy : ∀ k : ℕ, (g ^ k) u ≠ y := by
    intro k hk
    exact huy (sameCycle_of_pow_eq hk)
  constructor
  · intro h
    obtain ⟨i, _, _, hiv⟩ := Equiv.Perm.SameCycle.exists_pow_eq _ h
    rw [swap_mul_pow_eq hx hy] at hiv
    exact sameCycle_of_pow_eq hiv
  · intro h
    obtain ⟨i, _, _, hiv⟩ := Equiv.Perm.SameCycle.exists_pow_eq _ h
    rw [← swap_mul_pow_eq hx hy] at hiv
    exact sameCycle_of_pow_eq hiv

/-- Along the swap-multiplied permutation, every point of a
`g`-trajectory of `x` is in the orbit of `x` or of `y`. -/
private theorem sameCycle_swap_mul_pow_target [DecidableEq Y]
    (g : Perm Y)
    (x y : Y) :
    ∀ k : ℕ, (Equiv.swap x y * g).SameCycle x ((g ^ k) x) ∨
      (Equiv.swap x y * g).SameCycle y ((g ^ k) x) := by
  intro k
  induction k with
  | zero => exact Or.inl (Equiv.Perm.SameCycle.refl _ _)
  | succ k ih =>
    have hstep : (g ^ (k + 1)) x = g ((g ^ k) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    by_cases h1 : g ((g ^ k) x) = x
    · refine Or.inl ?_
      rw [hstep, h1]
    by_cases h2 : g ((g ^ k) x) = y
    · refine Or.inr ?_
      rw [hstep, h2]
    · have happ : (Equiv.swap x y * g) ((g ^ k) x) =
          g ((g ^ k) x) := by
        rw [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne h1 h2]
      have hsc : (Equiv.swap x y * g).SameCycle ((g ^ k) x)
          ((g ^ (k + 1)) x) := by
        rw [hstep, ← happ]
        exact Equiv.Perm.sameCycle_apply_right.mpr
          (Equiv.Perm.SameCycle.refl _ _)
      rcases ih with h | h
      · exact Or.inl (h.trans hsc)
      · exact Or.inr (h.trans hsc)

/-- Cover: every support point of a cycle lands in the swap-orbit
of `x` or of `y`. -/
private theorem swap_mul_cycle_cover [Fintype Y] [DecidableEq Y]
    {c : Perm Y} (hc : c.IsCycle)
    {x y z : Y} (hx : x ∈ c.support) (hz : z ∈ c.support) :
    (Equiv.swap x y * c).SameCycle x z ∨
      (Equiv.swap x y * c).SameCycle y z := by
  have hsc : c.SameCycle x z :=
    hc.sameCycle (Equiv.Perm.mem_support.mp hx)
      (Equiv.Perm.mem_support.mp hz)
  obtain ⟨i, _, _, hiz⟩ := Equiv.Perm.SameCycle.exists_pow_eq _ hsc
  rw [← hiz]
  exact sameCycle_swap_mul_pow_target c x y i

/-- Fixed points of the swapped cycle inside the old support are
the swapped points. -/
private theorem swap_mul_cycle_fixed [Fintype Y] [DecidableEq Y]
    {c : Perm Y} (hc : c.IsCycle)
    {x y z : Y} (hx : x ∈ c.support) (hz : z ∈ c.support)
    (hfix : (Equiv.swap x y * c) z = z) : z = x ∨ z = y := by
  rcases swap_mul_cycle_cover (y := y) hc hx hz with h | h
  · exact Or.inl (h.eq_of_right hfix).symm
  · exact Or.inr (h.eq_of_right hfix).symm

/-- The swapped cycle has support inside the old support. -/
private theorem swap_mul_support_subset [Fintype Y] [DecidableEq Y]
    {c : Perm Y} {x y : Y}
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (Equiv.swap x y * c).support ⊆ c.support := by
  intro z hz
  by_contra hzc
  have hcz : c z = z := Equiv.Perm.notMem_support.mp hzc
  have hzx : z ≠ x := fun h => hzc (h ▸ hx)
  have hzy : z ≠ y := fun h => hzc (h ▸ hy)
  have : (Equiv.swap x y * c) z = z := by
    rw [Equiv.Perm.mul_apply, hcz,
      Equiv.swap_apply_of_ne_of_ne hzx hzy]
  exact Equiv.Perm.mem_support.mp hz this

/-- **No crossover**: swapping two points of one cycle separates
them. -/
private theorem not_sameCycle_swap_mul [Fintype Y] [DecidableEq Y]
    {g : Perm Y} {x y : Y}
    (hxy : x ≠ y) (hsc : g.SameCycle x y) :
    ¬ (Equiv.swap x y * g).SameCycle x y := by
  have hex : ∃ i, 0 < i ∧ (g ^ i) x = y := by
    obtain ⟨i, hi0, _, hiy⟩ := Equiv.Perm.SameCycle.exists_pow_eq _ hsc
    exact ⟨i, hi0, hiy⟩
  obtain ⟨m, hm0, hmy, hmin⟩ : ∃ m, 0 < m ∧ (g ^ m) x = y ∧
      ∀ j, 0 < j → j < m → (g ^ j) x ≠ y := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1,
      (Nat.find_spec hex).2, ?_⟩
    intro j hj0 hjm hjy
    exact Nat.find_min hex hjm ⟨hj0, hjy⟩
  have hne_x : ∀ j, 0 < j → j < m → (g ^ j) x ≠ x := by
    intro j hj0 hjm hjx
    have hmod := perm_pow_mod (p := j) hj0 hjx m
    rw [hmy] at hmod
    have hlt : m % j < j := Nat.mod_lt m hj0
    rcases Nat.eq_zero_or_pos (m % j) with h0 | hpos
    · rw [h0] at hmod
      exact hxy (by simpa using hmod.symm)
    · exact hmin (m % j) hpos (by omega) hmod.symm
  have htraj : ∀ i, i < m →
      ((Equiv.swap x y * g) ^ i) x = (g ^ i) x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have h1 : ((Equiv.swap x y * g) ^ (i + 1)) x =
          (Equiv.swap x y * g) (((Equiv.swap x y * g) ^ i) x) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      have h2 : (g ^ (i + 1)) x = g ((g ^ i) x) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [h1, ih (by omega), Equiv.Perm.mul_apply, ← h2,
        Equiv.swap_apply_of_ne_of_ne
          (hne_x (i + 1) (by omega) (by omega))
          (hmin (i + 1) (by omega) (by omega))]
  have hwrap : ((Equiv.swap x y * g) ^ m) x = x := by
    obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
    have h1 : ((Equiv.swap x y * g) ^ (m0 + 1)) x =
        (Equiv.swap x y * g) (((Equiv.swap x y * g) ^ m0) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have h2 : (g ^ (m0 + 1)) x = g ((g ^ m0) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [h1, htraj m0 (by omega), Equiv.Perm.mul_apply, ← h2, hmy,
      Equiv.swap_apply_right]
  intro hcon
  obtain ⟨i, hi0, _, hiy⟩ := Equiv.Perm.SameCycle.exists_pow_eq _ hcon
  rw [perm_pow_mod (p := m) (by omega) hwrap i] at hiy
  have hlt : i % m < m := Nat.mod_lt i (by omega)
  rcases Nat.eq_zero_or_pos (i % m) with h0 | hpos
  · rw [h0] at hiy
    exact hxy (by simpa using hiy)
  · rw [htraj (i % m) hlt] at hiy
    exact hmin (i % m) hpos hlt hiy

/-- **Merging**: swapping two points of different orbits joins
them. -/
theorem sameCycle_swap_mul_of_not [Fintype Y] [DecidableEq Y]
    {g : Perm Y} {x y : Y}
    (_hxy : x ≠ y) (hsc : ¬ g.SameCycle x y) :
    (Equiv.swap x y * g).SameCycle x y := by
  have hex : ∃ i, 0 < i ∧ (g ^ i) x = x := by
    refine ⟨orderOf g, ?_, ?_⟩
    · exact orderOf_pos g
    · rw [pow_orderOf_eq_one]; rfl
  obtain ⟨m, hm0, hmx, hmin⟩ : ∃ m, 0 < m ∧ (g ^ m) x = x ∧
      ∀ j, 0 < j → j < m → (g ^ j) x ≠ x := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1,
      (Nat.find_spec hex).2, ?_⟩
    intro j hj0 hjm hjx
    exact Nat.find_min hex hjm ⟨hj0, hjx⟩
  have hne_y : ∀ j : ℕ, (g ^ j) x ≠ y := by
    intro j hj
    exact hsc (sameCycle_of_pow_eq hj)
  have htraj : ∀ i, i < m →
      ((Equiv.swap x y * g) ^ i) x = (g ^ i) x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have h1 : ((Equiv.swap x y * g) ^ (i + 1)) x =
          (Equiv.swap x y * g) (((Equiv.swap x y * g) ^ i) x) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      have h2 : (g ^ (i + 1)) x = g ((g ^ i) x) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [h1, ih (by omega), Equiv.Perm.mul_apply, ← h2,
        Equiv.swap_apply_of_ne_of_ne
          (hmin (i + 1) (by omega) (by omega)) (hne_y (i + 1))]
  have hwrap : ((Equiv.swap x y * g) ^ m) x = y := by
    obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
    have h1 : ((Equiv.swap x y * g) ^ (m0 + 1)) x =
        (Equiv.swap x y * g) (((Equiv.swap x y * g) ^ m0) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have h2 : (g ^ (m0 + 1)) x = g ((g ^ m0) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [h1, htraj m0 (by omega), Equiv.Perm.mul_apply, ← h2, hmx,
      Equiv.swap_apply_left]
  exact sameCycle_of_pow_eq hwrap

/-! ### Orbit counting via representatives -/

/-- **Orbit counting by representatives**: a set meeting every
orbit exactly once has the orbit count as its cardinality. -/
theorem permOrbitCount_eq_card_of_reps [Fintype Y] [DecidableEq Y]
    (g : Perm Y) (S : Finset Y)
    (hcover : ∀ z : Y, ∃ w ∈ S, g.SameCycle w z)
    (hsep : ∀ w ∈ S, ∀ w' ∈ S, g.SameCycle w w' → w = w') :
    permOrbitCount g = S.card := by
  have hmoved : (S.filter (fun w => ¬ g w = w)).card =
      g.cycleFactorsFinset.card := by
    refine Finset.card_bij
      (fun w _ => g.cycleOf w) ?_ ?_ ?_
    · intro w hw
      rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
        Equiv.Perm.mem_support]
      exact (Finset.mem_filter.mp hw).2
    · intro w hw w' hw' hEq
      obtain ⟨hwS, hwm⟩ := Finset.mem_filter.mp hw
      obtain ⟨hwS', hwm'⟩ := Finset.mem_filter.mp hw'
      refine hsep w hwS w' hwS' ?_
      exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
        (Equiv.Perm.mem_support.mpr hwm)
        (Equiv.Perm.mem_support.mpr hwm')).mpr hEq
    · intro f' hf'
      have hcyc : f'.IsCycle :=
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hf').1
      obtain ⟨z, hz⟩ := hcyc.nonempty_support
      have hzg : z ∈ g.support := by
        rw [Equiv.Perm.mem_support]
        have h1 := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp
          hf').2 z hz
        rw [← h1]
        exact Equiv.Perm.mem_support.mp hz
      obtain ⟨w, hwS, hwz⟩ := hcover z
      have hwm : ¬ g w = w :=
        Equiv.Perm.mem_support.mp ((hwz.mem_support_iff).mpr hzg)
      refine ⟨w, Finset.mem_filter.mpr ⟨hwS, hwm⟩, ?_⟩
      rw [hwz.cycleOf_eq]
      exact (Equiv.Perm.cycle_is_cycleOf hz hf').symm
  have hfixed : (S.filter (fun w => g w = w)).card =
      Fintype.card (Function.fixedPoints g) := by
    rw [Fintype.card_subtype]
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      obtain ⟨w, hwS, hwz⟩ := hcover z
      have hwz' : w = z := hwz.eq_of_right h
      exact ⟨hwz' ▸ hwS, h⟩
  have hct : g.cycleType.card = g.cycleFactorsFinset.card := by
    rw [Equiv.Perm.cycleType_def, Multiset.card_map]
    rfl
  have hpart := Finset.card_filter_add_card_filter_not
    (s := S) (fun w => g w = w)
  unfold permOrbitCount
  rw [hct, ← hmoved, ← hfixed]
  omega

/-! ### The cycle split -/

/-- **The cycle split count**: swapping two support points of a
cycle yields exactly two orbits on its support. -/
private theorem swap_mul_cycle_count [Fintype Y] [DecidableEq Y]
    {c : Perm Y} (hc : c.IsCycle)
    {x y : Y} (hxy : x ≠ y) (hx : x ∈ c.support)
    (hy : y ∈ c.support) :
    (Equiv.swap x y * c).cycleType.card + c.support.card =
      2 + (Equiv.swap x y * c).support.card := by
  have hsub := swap_mul_support_subset (c := c) hx hy
  have hfac : ∀ f' ∈ (Equiv.swap x y * c).cycleFactorsFinset,
      f' = (Equiv.swap x y * c).cycleOf x ∨
        f' = (Equiv.swap x y * c).cycleOf y := by
    intro f' hf'
    have hcyc : f'.IsCycle :=
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hf').1
    obtain ⟨z, hz⟩ := hcyc.nonempty_support
    have hzs : z ∈ (Equiv.swap x y * c).support := by
      rw [Equiv.Perm.mem_support]
      have h1 := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp
        hf').2 z hz
      rw [← h1]
      exact Equiv.Perm.mem_support.mp hz
    have hzc : z ∈ c.support := hsub hzs
    have hfz : f' = (Equiv.swap x y * c).cycleOf z :=
      Equiv.Perm.cycle_is_cycleOf hz hf'
    rcases swap_mul_cycle_cover (y := y) hc hx hzc with h | h
    · left
      rw [hfz, h.cycleOf_eq]
    · right
      rw [hfz, h.cycleOf_eq]
  have hct : (Equiv.swap x y * c).cycleType.card =
      (Equiv.swap x y * c).cycleFactorsFinset.card := by
    rw [Equiv.Perm.cycleType_def, Multiset.card_map]
    rfl
  -- ═══════ FOUR CASES ON WHICH ENDS THE PRODUCT FIXES ═══════
  -- Multiplying by a transposition either splits one cycle in two
  -- or merges two into one; which, is read off the two fixed-point
  -- tests.
  by_cases hτx : (Equiv.swap x y * c) x = x <;>
    by_cases hτy : (Equiv.swap x y * c) y = y
  · -- both fixed: the swapped cycle is trivial, the cycle is the
    -- transposition
    have hsupp : (Equiv.swap x y * c).support = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      have hzc : z ∈ c.support := hsub hz
      have hzm : (Equiv.swap x y * c) z ≠ z :=
        Equiv.Perm.mem_support.mp hz
      rcases swap_mul_cycle_cover (y := y) hc hx hzc with h | h
      · exact hzm ((h.eq_of_left hτx) ▸ hτx)
      · exact hzm ((h.eq_of_left hτy) ▸ hτy)
    have h1 : Equiv.swap x y * c = 1 :=
      Equiv.Perm.support_eq_empty_iff.mp hsupp
    have hct0 : (Equiv.swap x y * c).cycleType.card = 0 := by
      rw [h1, Equiv.Perm.cycleType_one]
      rfl
    have hsc : c.support = {x, y} := by
      apply Finset.Subset.antisymm
      · intro z hzc
        have hzfix : (Equiv.swap x y * c) z = z := by
          rw [h1]
          rfl
        rcases swap_mul_cycle_fixed (y := y) hc hx hzc hzfix with
          h | h
        · simp [h]
        · simp [h]
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · rw [Finset.mem_singleton.mp hz]
          exact hy
    have hc2 : ({x, y} : Finset Y).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hxy
    rw [hct0, hsc, hsupp]
    simp [hc2]
  · -- x fixed, y moved: one orbit, support loses x
    have hxnot : x ∉ (Equiv.swap x y * c).support :=
      Equiv.Perm.notMem_support.mpr hτx
    have hsupp : (Equiv.swap x y * c).support =
        c.support.erase x := by
      apply Finset.Subset.antisymm
      · intro z hz
        exact Finset.mem_erase.mpr
          ⟨fun h => hxnot (h ▸ hz), hsub hz⟩
      · intro z hz
        obtain ⟨hzx, hzc⟩ := Finset.mem_erase.mp hz
        rw [Equiv.Perm.mem_support]
        intro hzfix
        rcases swap_mul_cycle_fixed (y := y) hc hx hzc hzfix with
          h | h
        · exact hzx h
        · rw [h] at hzfix
          exact hτy hzfix
    have hfacs : (Equiv.swap x y * c).cycleFactorsFinset =
        {(Equiv.swap x y * c).cycleOf y} := by
      apply Finset.Subset.antisymm
      · intro f' hf'
        rcases hfac f' hf' with h | h
        · exfalso
          rw [h,
            Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff] at hf'
          exact hxnot hf'
        · exact Finset.mem_singleton.mpr h
      · intro f' hf'
        rw [Finset.mem_singleton.mp hf',
          Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
          Equiv.Perm.mem_support]
        exact hτy
    have hpos : 1 ≤ c.support.card :=
      Finset.card_pos.mpr ⟨x, hx⟩
    rw [hct, hfacs, hsupp, Finset.card_singleton,
      Finset.card_erase_of_mem hx]
    omega
  · -- x moved, y fixed: one orbit, support loses y
    have hynot : y ∉ (Equiv.swap x y * c).support :=
      Equiv.Perm.notMem_support.mpr hτy
    have hsupp : (Equiv.swap x y * c).support =
        c.support.erase y := by
      apply Finset.Subset.antisymm
      · intro z hz
        exact Finset.mem_erase.mpr
          ⟨fun h => hynot (h ▸ hz), hsub hz⟩
      · intro z hz
        obtain ⟨hzy, hzc⟩ := Finset.mem_erase.mp hz
        rw [Equiv.Perm.mem_support]
        intro hzfix
        rcases swap_mul_cycle_fixed (y := y) hc hx hzc hzfix with
          h | h
        · rw [h] at hzfix
          exact hτx hzfix
        · exact hzy h
    have hfacs : (Equiv.swap x y * c).cycleFactorsFinset =
        {(Equiv.swap x y * c).cycleOf x} := by
      apply Finset.Subset.antisymm
      · intro f' hf'
        rcases hfac f' hf' with h | h
        · exact Finset.mem_singleton.mpr h
        · exfalso
          rw [h,
            Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff] at hf'
          exact hynot hf'
      · intro f' hf'
        rw [Finset.mem_singleton.mp hf',
          Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
          Equiv.Perm.mem_support]
        exact hτx
    have hpos : 1 ≤ c.support.card :=
      Finset.card_pos.mpr ⟨y, hy⟩
    rw [hct, hfacs, hsupp, Finset.card_singleton,
      Finset.card_erase_of_mem hy]
    omega
  · -- both moved: two orbits, support unchanged
    have hsupp : (Equiv.swap x y * c).support = c.support := by
      apply Finset.Subset.antisymm hsub
      intro z hzc
      rw [Equiv.Perm.mem_support]
      intro hzfix
      rcases swap_mul_cycle_fixed (y := y) hc hx hzc hzfix with
        h | h
      · rw [h] at hzfix
        exact hτx hzfix
      · rw [h] at hzfix
        exact hτy hzfix
    have hxs : x ∈ (Equiv.swap x y * c).support :=
      Equiv.Perm.mem_support.mpr hτx
    have hys : y ∈ (Equiv.swap x y * c).support :=
      Equiv.Perm.mem_support.mpr hτy
    have hne : (Equiv.swap x y * c).cycleOf x ≠
        (Equiv.swap x y * c).cycleOf y := by
      intro hEq
      have hscxy : (Equiv.swap x y * c).SameCycle x y :=
        (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support hxs
          hys).mpr hEq
      exact not_sameCycle_swap_mul hxy
        (hc.sameCycle (Equiv.Perm.mem_support.mp hx)
          (Equiv.Perm.mem_support.mp hy)) hscxy
    have hfacs : (Equiv.swap x y * c).cycleFactorsFinset =
        {(Equiv.swap x y * c).cycleOf x,
          (Equiv.swap x y * c).cycleOf y} := by
      apply Finset.Subset.antisymm
      · intro f' hf'
        rcases hfac f' hf' with h | h
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr h))
      · intro f' hf'
        rcases Finset.mem_insert.mp hf' with rfl | hf'
        · rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
          exact hxs
        · rw [Finset.mem_singleton.mp hf',
            Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
          exact hys
    have hc2 : ({(Equiv.swap x y * c).cycleOf x,
        (Equiv.swap x y * c).cycleOf y} :
          Finset (Perm Y)).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hne
    rw [hct, hfacs, hsupp, hc2]

/-! ### The transposition orbit ledger -/

/-- **Splitting**: multiplying by a transposition of two points on
one orbit raises the orbit count by one. -/
theorem permOrbitCount_swap_mul_sameCycle [Fintype Y] [DecidableEq Y]
    {g : Perm Y} {x y : Y}
    (hxy : x ≠ y) (hsc : g.SameCycle x y) :
    permOrbitCount (Equiv.swap x y * g) = permOrbitCount g + 1 := by
  have hgx : g x ≠ x := by
    intro h
    exact hxy (hsc.eq_of_left h)
  set c := g.cycleOf x with hc_def
  set d := c⁻¹ * g with hd_def
  have hcyc : c.IsCycle := Equiv.Perm.isCycle_cycleOf g hgx
  have hcd : g = c * d := by
    rw [hd_def, mul_inv_cancel_left]
  have hc_app : ∀ z, g.SameCycle x z → c z = g z := by
    intro z hz
    exact hz.cycleOf_apply
  have hc_fix : ∀ z, ¬ g.SameCycle x z → c z = z := by
    intro z hz
    exact Equiv.Perm.cycleOf_apply_of_not_sameCycle hz
  have hd_fix : ∀ z, g.SameCycle x z → d z = z := by
    intro z hz
    have h1 : c z = g z := hc_app z hz
    rw [hd_def, Equiv.Perm.mul_apply, ← h1, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply]
  have hd_app : ∀ z, ¬ g.SameCycle x z → d z = g z := by
    intro z hz
    have h1 : c⁻¹ (g z) = g z := by
      have h2 : c (g z) = g z := by
        refine hc_fix (g z) ?_
        intro hcon
        exact hz ((Equiv.Perm.sameCycle_apply_right).mp hcon)
      calc c⁻¹ (g z) = c⁻¹ (c (g z)) := by rw [h2]
        _ = g z := by
          rw [Equiv.Perm.inv_def]
          exact Equiv.symm_apply_apply c (g z)
    rw [hd_def, Equiv.Perm.mul_apply, h1]
  have hdisj : Equiv.Perm.Disjoint c d := by
    intro z
    by_cases hz : g.SameCycle x z
    · exact Or.inr (hd_fix z hz)
    · exact Or.inl (hc_fix z hz)
  have hxc : x ∈ c.support := by
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨Equiv.Perm.SameCycle.refl g x,
      Equiv.Perm.mem_support.mpr hgx⟩
  have hyc : y ∈ c.support := by
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨hsc, Equiv.Perm.mem_support.mpr hgx⟩
  have hdisj2 : Equiv.Perm.Disjoint (Equiv.swap x y * c) d := by
    intro z
    by_cases hz : g.SameCycle x z
    · exact Or.inr (hd_fix z hz)
    · refine Or.inl ?_
      have hzx : z ≠ x := by
        intro h
        exact hz (h ▸ Equiv.Perm.SameCycle.refl g x)
      have hzy : z ≠ y := by
        intro h
        exact hz (h ▸ hsc)
      rw [Equiv.Perm.mul_apply, hc_fix z hz,
        Equiv.swap_apply_of_ne_of_ne hzx hzy]
  have hmul : Equiv.swap x y * g =
      (Equiv.swap x y * c) * d := by
    rw [mul_assoc, ← hcd]
  -- counting
  have hcount := swap_mul_cycle_count hcyc hxy hxc hyc
  have hE1 := card_fixedPoints_add_card_support (Equiv.swap x y * g)
  have hE2 := card_fixedPoints_add_card_support g
  have hct1 : (Equiv.swap x y * g).cycleType =
      (Equiv.swap x y * c).cycleType + d.cycleType := by
    rw [hmul]
    exact hdisj2.cycleType_mul
  have hct2 : g.cycleType = c.cycleType + d.cycleType := by
    rw [hcd]
    exact hdisj.cycleType_mul
  have hs1 : (Equiv.swap x y * g).support.card =
      (Equiv.swap x y * c).support.card + d.support.card := by
    rw [hmul, hdisj2.support_mul]
    exact Finset.card_union_of_disjoint hdisj2.disjoint_support
  have hs2 : g.support.card = c.support.card + d.support.card := by
    rw [hcd, hdisj.support_mul]
    exact Finset.card_union_of_disjoint hdisj.disjoint_support
  have hcc : c.cycleType.card = 1 := by
    rw [hcyc.cycleType]
    rfl
  have hcards1 := congrArg Multiset.card hct1
  have hcards2 := congrArg Multiset.card hct2
  rw [Multiset.card_add] at hcards1 hcards2
  unfold permOrbitCount at *
  omega

/-- **Merging**: multiplying by a transposition of two points on
different orbits lowers the orbit count by one. -/
theorem permOrbitCount_swap_mul_not_sameCycle [Fintype Y] [DecidableEq Y]
    {g : Perm Y}
    {x y : Y} (hxy : x ≠ y) (hsc : ¬ g.SameCycle x y) :
    permOrbitCount g = permOrbitCount (Equiv.swap x y * g) + 1 := by
  have h2 : (Equiv.swap x y * g).SameCycle x y :=
    sameCycle_swap_mul_of_not hxy hsc
  have h3 := permOrbitCount_swap_mul_sameCycle hxy h2
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at h3
  exact h3

/-- **The coherent double swap**: with the mirror equivalence
`b ∼ c ↔ a ∼ d` and the two exclusions `a ≁ b`, `a ≁ c`, the double
transposition moves the orbit count by exactly two. -/
theorem permOrbitCount_swap_swap_mul [Fintype Y] [DecidableEq Y]
    {g : Perm Y} {a b c d : Y}
    (hbc : b ≠ c) (had : a ≠ d)
    (hiff : g.SameCycle b c ↔ g.SameCycle a d)
    (hab : ¬ g.SameCycle a b) (hac : ¬ g.SameCycle a c) :
    permOrbitCount (Equiv.swap a d * (Equiv.swap b c * g)) =
        permOrbitCount g + 2 ∨
      permOrbitCount g =
        permOrbitCount (Equiv.swap a d * (Equiv.swap b c * g)) + 2
    := by
  have htrans := sameCycle_swap_mul_iff (g := g) (x := b) (y := c)
    hab hac d
  by_cases hbcs : g.SameCycle b c
  · left
    have h1 := permOrbitCount_swap_mul_sameCycle hbc hbcs
    have h2 := permOrbitCount_swap_mul_sameCycle had
      (htrans.mpr (hiff.mp hbcs))
    omega
  · right
    have h1 := permOrbitCount_swap_mul_not_sameCycle hbc hbcs
    have h2 := permOrbitCount_swap_mul_not_sameCycle had
      (fun h => (fun hcon => hbcs (hiff.mpr hcon)) (htrans.mp h))
    omega

/-- Transporting a permutation along an equivalence preserves the
orbit count. -/
theorem permOrbitCount_permCongr {γ δ : Type} [Fintype γ]
    [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (e : γ ≃ δ) (g : Perm γ) :
    permOrbitCount (e.permCongr g) = permOrbitCount g := by
  unfold permOrbitCount
  rw [cycleType_permCongr, card_fixedPoints_permCongr]

/-- The orbit count of a `sumCongr` is the sum of the orbit
counts. -/
theorem permOrbitCount_sumCongr {γ δ : Type} [Fintype γ]
    [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (σ : Perm γ) (τ : Perm δ) :
    permOrbitCount (Equiv.sumCongr σ τ) =
      permOrbitCount σ + permOrbitCount τ := by
  unfold permOrbitCount
  rw [cycleType_sumCongr, Multiset.card_add,
    card_fixedPoints_sumCongr]
  omega

end AbstractOrbit

/-! ## (ii) The closed-up full walk permutation -/

namespace EdgeSubset

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}

/-- The edge pairing as a permutation of the participating flags. -/
noncomputable def pairingPermSP (F : EdgeSubset W) :
    Equiv.Perm {f : W.Flag // f ∈ F.flags} where
  toFun x := ⟨W.pairing x.val, F.pairing_mem x.val x.prop⟩
  invFun x := ⟨W.pairing x.val, F.pairing_mem x.val x.prop⟩
  left_inv x := Subtype.ext (W.pairing_invol x.val)
  right_inv x := Subtype.ext (W.pairing_invol x.val)

/-- The edge pairing as a permutation of participating flags, on
underlying flags. -/
@[simp] theorem pairingPermSP_val (x : {f : W.Flag // f ∈ F.flags}) :
    (pairingPermSP F x).val = W.pairing x.val := rfl

/-- It is an involution. -/
theorem pairingPermSP_invol (x : {f : W.Flag // f ∈ F.flags}) :
    pairingPermSP F (pairingPermSP F x) = x :=
  Subtype.ext (W.pairing_invol x.val)

/-- Equivalently, its square is the identity. -/
theorem pairingPermSP_mul_self :
    pairingPermSP F * pairingPermSP F = 1 := by
  apply Equiv.ext
  intro x
  exact pairingPermSP_invol x

/-- The matching extended by the path matching, as a function on
participating flags. -/
noncomputable def fullMatchFun (κ : F.RelTransitionSystem)
    (x : {f : W.Flag // f ∈ F.flags}) :
    {f : W.Flag // f ∈ F.flags} :=
  if h : x.val ∈ F.internalFlags then
    ⟨κ.match_ x.val,
      mem_flags_of_internalFlags F (κ.match_mem x.val h)⟩
  else
    ⟨κ.pathMatch x.val
        ((F.mem_internalFlags_or_boundaryFlags x.prop).resolve_left
          h),
      mem_flags_of_boundaryFlags F (κ.pathMatch_mem _)⟩

/-- The full matching is the system's own on internal flags. -/
theorem fullMatchFun_val_internal (κ : F.RelTransitionSystem)
    {x : {f : W.Flag // f ∈ F.flags}}
    (h : x.val ∈ F.internalFlags) :
    (fullMatchFun κ x).val = κ.match_ x.val := by
  unfold fullMatchFun
  rw [dite_eq_left h]

/-- And the path matching on boundary flags: this is what closes
the chains into orbits. -/
theorem fullMatchFun_val_boundary (κ : F.RelTransitionSystem)
    {x : {f : W.Flag // f ∈ F.flags}}
    (h : x.val ∈ F.boundaryFlags) :
    (fullMatchFun κ x).val = κ.pathMatch x.val h := by
  have hni : x.val ∉ F.internalFlags :=
    Finset.disjoint_right.mp F.internalFlags_disjoint_boundaryFlags
      h
  unfold fullMatchFun
  rw [dite_eq_right hni]

/-- The full matching is an involution, both halves being ones. -/
theorem fullMatchFun_invol (κ : F.RelTransitionSystem)
    (x : {f : W.Flag // f ∈ F.flags}) :
    fullMatchFun κ (fullMatchFun κ x) = x := by
  by_cases h : x.val ∈ F.internalFlags
  · have h1 : (fullMatchFun κ x).val = κ.match_ x.val :=
      fullMatchFun_val_internal κ h
    have h2 : (fullMatchFun κ x).val ∈ F.internalFlags := by
      rw [h1]
      exact κ.match_mem x.val h
    apply Subtype.ext
    rw [fullMatchFun_val_internal κ h2, h1]
    exact κ.match_invol x.val h
  · have hb : x.val ∈ F.boundaryFlags :=
      (F.mem_internalFlags_or_boundaryFlags x.prop).resolve_left h
    have h1 : (fullMatchFun κ x).val = κ.pathMatch x.val hb :=
      fullMatchFun_val_boundary κ hb
    have h2 : (fullMatchFun κ x).val ∈ F.boundaryFlags := by
      rw [h1]
      exact κ.pathMatch_mem hb
    apply Subtype.ext
    rw [fullMatchFun_val_boundary κ h2]
    have h3 := κ.pathMatch_congr h1 h2 (κ.pathMatch_mem hb)
    rw [h3]
    exact κ.pathMatch_invol hb

/-- The extended matching as an (involutive) permutation. -/
noncomputable def fullMatchPerm (κ : F.RelTransitionSystem) :
    Equiv.Perm {f : W.Flag // f ∈ F.flags} where
  toFun := fullMatchFun κ
  invFun := fullMatchFun κ
  left_inv := fullMatchFun_invol κ
  right_inv := fullMatchFun_invol κ

/-- The full matching as a permutation acts by that function. -/
@[simp] theorem fullMatchPerm_apply (κ : F.RelTransitionSystem)
    (x : {f : W.Flag // f ∈ F.flags}) :
    fullMatchPerm κ x = fullMatchFun κ x := rfl

/-- Its square is the identity. -/
theorem fullMatchPerm_mul_self (κ : F.RelTransitionSystem) :
    fullMatchPerm κ * fullMatchPerm κ = 1 := by
  apply Equiv.ext
  intro x
  exact fullMatchFun_invol κ x

/-- **The full walk permutation**: pairing followed by extended
matching, a permutation of all participating flags. -/
noncomputable def fullPerm (κ : F.RelTransitionSystem) :
    Equiv.Perm {f : W.Flag // f ∈ F.flags} :=
  fullMatchPerm κ * pairingPermSP F

/-- **The full walk**: cross the edge, then match — including at
the boundary, where matching follows the chain to its far end. -/
theorem fullPerm_apply (κ : F.RelTransitionSystem)
    (x : {f : W.Flag // f ∈ F.flags}) :
    fullPerm κ x = fullMatchFun κ (pairingPermSP F x) := rfl

/-- Its value when the edge partner is internal. -/
theorem fullPerm_val_internal {κ : F.RelTransitionSystem}
    {x : {f : W.Flag // f ∈ F.flags}}
    (h : W.pairing x.val ∈ F.internalFlags) :
    (fullPerm κ x).val = κ.match_ (W.pairing x.val) :=
  fullMatchFun_val_internal κ (x := pairingPermSP F x) h

/-- Its value when the edge partner is a boundary flag. -/
theorem fullPerm_val_boundary {κ : F.RelTransitionSystem}
    {x : {f : W.Flag // f ∈ F.flags}}
    (h : W.pairing x.val ∈ F.boundaryFlags) :
    (fullPerm κ x).val = κ.pathMatch (W.pairing x.val) h :=
  fullMatchFun_val_boundary κ (x := pairingPermSP F x) h

/-- Applying the full walk to a paired flag lands on the extended
matching. -/
theorem fullPerm_apply_pairing (κ : F.RelTransitionSystem)
    (x : {f : W.Flag // f ∈ F.flags}) :
    fullPerm κ (pairingPermSP F x) = fullMatchFun κ x := by
  rw [fullPerm_apply, pairingPermSP_invol]

/-- The inverse of the full walk. -/
theorem fullPerm_inv (κ : F.RelTransitionSystem) :
    (fullPerm κ)⁻¹ = pairingPermSP F * fullMatchPerm κ := by
  rw [inv_eq_iff_mul_eq_one]
  unfold fullPerm
  rw [mul_assoc, ← mul_assoc (pairingPermSP F), pairingPermSP_mul_self,
    one_mul, fullMatchPerm_mul_self]

/-- **Mirror symmetry**: the pairing conjugates the full walk to
its inverse, so `SameCycle` transfers to paired flags. -/
theorem sameCycle_pairingPermSP {κ : F.RelTransitionSystem}
    {x y : {f : W.Flag // f ∈ F.flags}}
    (h : (fullPerm κ).SameCycle x y) :
    (fullPerm κ).SameCycle (pairingPermSP F x) (pairingPermSP F y) := by
  have hconj : pairingPermSP F * fullPerm κ * (pairingPermSP F)⁻¹ =
      (fullPerm κ)⁻¹ := by
    have hp : (pairingPermSP F)⁻¹ = pairingPermSP F := by
      rw [inv_eq_iff_mul_eq_one]
      exact pairingPermSP_mul_self
    rw [hp, fullPerm_inv]
    unfold fullPerm
    rw [← mul_assoc, mul_assoc (pairingPermSP F * fullMatchPerm κ),
      pairingPermSP_mul_self, mul_one]
  have h2 := h.conj (g := pairingPermSP F)
  rw [hconj] at h2
  exact (Equiv.Perm.sameCycle_inv).mp h2

/-! ### Trajectories of the full walk -/

/-- While the pairings along a walk stay internal, powers of the
full walk follow the iterated walk. -/
theorem fullPerm_pow_val {κ : F.RelTransitionSystem}
    {x : {f : W.Flag // f ∈ F.flags}} {m : ℕ}
    (hcont : ∀ t, t < m →
      W.pairing (iterWalk κ x.val t) ∈ F.internalFlags) :
    ∀ j, j ≤ m → ((fullPerm κ ^ j) x).val = iterWalk κ x.val j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have h1 : (fullPerm κ ^ (j + 1)) x =
        fullPerm κ ((fullPerm κ ^ j) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have h2 : W.pairing (((fullPerm κ ^ j) x).val) ∈
        F.internalFlags := by
      rw [ih (by omega)]
      exact hcont j (by omega)
    rw [h1, fullPerm_val_internal h2, ih (by omega)]
    exact (iterWalk_succ κ x.val j).symm

/-- Powers of the full walk at a periodic flag follow the iterated
walk forever. -/
theorem fullPerm_pow_val_periodic {κ : F.RelTransitionSystem}
    {x : {f : W.Flag // f ∈ F.flags}}
    (hper : κ.PeriodicFlag x.val) (j : ℕ) :
    ((fullPerm κ ^ j) x).val = iterWalk κ x.val j :=
  fullPerm_pow_val (m := j)
    (fun t _ => all_pairings_internal_of_periodic κ hper t) j
    le_rfl

/-- `SameCycle` from a periodic flag produces a walk witness. -/
theorem sameCycle_periodic_val {κ : F.RelTransitionSystem}
    {x y : {f : W.Flag // f ∈ F.flags}}
    (hper : κ.PeriodicFlag x.val)
    (h : (fullPerm κ).SameCycle x y) :
    ∃ i : ℕ, iterWalk κ x.val i = y.val := by
  obtain ⟨i, _, _, hiy⟩ := Equiv.Perm.SameCycle.exists_pow_eq _ h
  refine ⟨i, ?_⟩
  rw [← fullPerm_pow_val_periodic hper i, hiy]

/-- **Mirror collision, periodic case**: a periodic flag is never
on the same full-walk orbit as its pairing. -/
theorem not_sameCycle_pairingPermSP_of_periodic {κ : F.RelTransitionSystem}
    {x : {f : W.Flag // f ∈ F.flags}}
    (hper : κ.PeriodicFlag x.val) :
    ¬ (fullPerm κ).SameCycle x (pairingPermSP F x) := by
  intro h
  obtain ⟨i, hi⟩ := sameCycle_periodic_val hper h
  refine pairing_iterWalk_ne κ
    (fun t _ => all_pairings_internal_of_periodic κ hper t)
    (Nat.zero_le i) (le_refl i) ?_
  rw [iterWalk_zero]
  exact hi.symm

/-! ### Chain orbits of the full walk -/

section ChainOrbit

variable {κ : F.RelTransitionSystem} {β : W.Flag}
  (hβ : β ∈ F.boundaryFlags) {k : ℕ} (hkle : k ≤ F.flags.card)
  (hcont : ∀ j, j < k →
    W.pairing (iterWalk κ β j) ∈ F.internalFlags)
  (hterm : W.pairing (iterWalk κ β k) ∈ F.boundaryFlags)

include hβ hkle hcont hterm

/-- **The chain wraps**: the full walk from a boundary flag closes
up after `k + 1` steps (through the path-matching jump). -/
theorem fullPerm_chain_wrap :
    (fullPerm κ ^ (k + 1)) ⟨β, mem_flags_of_boundaryFlags F hβ⟩ =
      ⟨β, mem_flags_of_boundaryFlags F hβ⟩ := by
  have hpow : (fullPerm κ ^ (k + 1))
      (⟨β, mem_flags_of_boundaryFlags F hβ⟩ :
        {f : W.Flag // f ∈ F.flags}) =
      fullPerm κ ((fullPerm κ ^ k)
        ⟨β, mem_flags_of_boundaryFlags F hβ⟩) := by
    rw [pow_succ', Equiv.Perm.mul_apply]
  have hval : ((fullPerm κ ^ k)
      (⟨β, mem_flags_of_boundaryFlags F hβ⟩ :
        {f : W.Flag // f ∈ F.flags})).val = iterWalk κ β k :=
    fullPerm_pow_val hcont k le_rfl
  apply Subtype.ext
  rw [hpow]
  have h2 : W.pairing (((fullPerm κ ^ k)
      (⟨β, mem_flags_of_boundaryFlags F hβ⟩ :
        {f : W.Flag // f ∈ F.flags})).val) ∈ F.boundaryFlags := by
    rw [hval]
    exact hterm
  rw [fullPerm_val_boundary h2]
  have hγ : κ.pathMatch β hβ = W.pairing (iterWalk κ β k) :=
    κ.pathMatch_eq hβ (traceChain_fuel_mono κ (by omega)
      (traceChain_forward κ β hcont hterm))
  have hγpm' : κ.pathMatch (W.pairing (iterWalk κ β k)) hterm =
      β :=
    calc κ.pathMatch (W.pairing (iterWalk κ β k)) hterm
        = κ.pathMatch (κ.pathMatch β hβ) (κ.pathMatch_mem hβ) :=
          κ.pathMatch_congr hγ.symm hterm _
      _ = β := κ.pathMatch_invol hβ
  calc κ.pathMatch (W.pairing (((fullPerm κ ^ k)
        (⟨β, mem_flags_of_boundaryFlags F hβ⟩ :
          {f : W.Flag // f ∈ F.flags})).val)) h2
      = κ.pathMatch (W.pairing (iterWalk κ β k)) hterm :=
        κ.pathMatch_congr (congrArg W.pairing hval) h2 hterm
    _ = β := hγpm'

/-- Values on the full-walk orbit of a boundary flag are chain
values. -/
theorem fullPerm_chain_sameCycle_val {z : {f : W.Flag // f ∈ F.flags}}
    (h : (fullPerm κ).SameCycle
      ⟨β, mem_flags_of_boundaryFlags F hβ⟩ z) :
    ∃ j, j ≤ k ∧ z.val = iterWalk κ β j := by
  obtain ⟨i, _, _, hiz⟩ := Equiv.Perm.SameCycle.exists_pow_eq _ h
  rw [perm_pow_mod (p := k + 1) (by omega)
    (fullPerm_chain_wrap hβ hkle hcont hterm) i] at hiz
  have hlt : i % (k + 1) < k + 1 := Nat.mod_lt i (by omega)
  refine ⟨i % (k + 1), by omega, ?_⟩
  rw [← hiz, fullPerm_pow_val hcont _ (by omega)]

/-- A boundary flag on the full-walk orbit of a boundary flag is
the base point. -/
theorem fullPerm_chain_boundary_eq {z : {f : W.Flag // f ∈ F.flags}}
    (h : (fullPerm κ).SameCycle
      ⟨β, mem_flags_of_boundaryFlags F hβ⟩ z)
    (hzb : z.val ∈ F.boundaryFlags) :
    z = ⟨β, mem_flags_of_boundaryFlags F hβ⟩ := by
  obtain ⟨j, hjk, hjv⟩ :=
    fullPerm_chain_sameCycle_val hβ hkle hcont hterm h
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [iterWalk_zero] at hjv
    exact Subtype.ext hjv
  · exfalso
    have hint : iterWalk κ β j ∈ F.internalFlags :=
      iterWalk_mem_internal κ k hj1 hjk hcont
    rw [← hjv] at hint
    exact Finset.disjoint_left.mp
      F.internalFlags_disjoint_boundaryFlags hint hzb

/-- **Mirror collision, chain case**: a chain flag is never on the
same full-walk orbit as its pairing. -/
theorem not_sameCycle_pairingPermSP_of_chain {f : W.Flag}
    (hfi : f ∈ F.flags) {t : ℕ} (htk : t ≤ k)
    (hft : f = iterWalk κ β t ∨ f = W.pairing (iterWalk κ β t)) :
    ¬ (fullPerm κ).SameCycle ⟨f, hfi⟩
      (pairingPermSP F ⟨f, hfi⟩) := by
  intro h
  rcases hft with hf1 | hf1
  · -- walk-side flag: the pairing would be a chain value
    have hx : (⟨f, hfi⟩ : {g : W.Flag // g ∈ F.flags}) =
        (fullPerm κ ^ t) ⟨β, mem_flags_of_boundaryFlags F hβ⟩ :=
      Subtype.ext (by rw [fullPerm_pow_val hcont t htk]; exact hf1)
    have hbx : (fullPerm κ).SameCycle
        ⟨β, mem_flags_of_boundaryFlags F hβ⟩ ⟨f, hfi⟩ := by
      rw [hx]
      exact sameCycle_of_pow_eq rfl
    obtain ⟨j, hjk, hjv⟩ := fullPerm_chain_sameCycle_val hβ hkle
      hcont hterm (hbx.trans h)
    have hjv' : W.pairing (iterWalk κ β t) = iterWalk κ β j := by
      rw [← hf1]
      exact hjv
    exact pairing_iterWalk_ne κ hcont htk hjk hjv'
  · -- pairing-side flag: the flag itself would be a chain value
    have hσx : pairingPermSP F (⟨f, hfi⟩ :
        {g : W.Flag // g ∈ F.flags}) =
        (fullPerm κ ^ t) ⟨β, mem_flags_of_boundaryFlags F hβ⟩ := by
      refine Subtype.ext ?_
      rw [fullPerm_pow_val hcont t htk, pairingPermSP_val]
      change W.pairing f = iterWalk κ β t
      rw [hf1, W.pairing_invol]
    have hbσ : (fullPerm κ).SameCycle
        ⟨β, mem_flags_of_boundaryFlags F hβ⟩
        (pairingPermSP F ⟨f, hfi⟩) := by
      rw [hσx]
      exact sameCycle_of_pow_eq rfl
    obtain ⟨j, hjk, hjv⟩ := fullPerm_chain_sameCycle_val hβ hkle
      hcont hterm (hbσ.trans h.symm)
    have hjv' : W.pairing (iterWalk κ β t) = iterWalk κ β j := by
      rw [← hf1]
      exact hjv
    exact pairing_iterWalk_ne κ hcont htk hjk hjv'

omit hβ hkle hterm in
/-- **Orientation constancy** along the walk side of a chain. -/
theorem isOut_iterWalk_chain (o : κ.Orientation) {i j : ℕ}
    (hi1 : 1 ≤ i) (hij : i ≤ j) (hjk : j ≤ k) :
    o.isOut (iterWalk κ β j) = o.isOut (iterWalk κ β i) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with heq | hlt
    · rw [heq]
    · have hj1 : 1 ≤ j := by omega
      have hstep : o.isOut (iterWalk κ β (j + 1)) =
          o.isOut (iterWalk κ β j) := by
        rw [iterWalk_succ, o.match_flip _ (hcont j (by omega)),
          o.pairing_flip _
            (iterWalk_mem_internal κ k hj1 (by omega) hcont)
            (hcont j (by omega)),
          Bool.not_not]
      rw [hstep]
      exact ih (by omega) (by omega)

omit hβ hkle hterm in
/-- The pairing-side orientation along a chain. -/
theorem isOut_pairing_iterWalk_chain (o : κ.Orientation) {j : ℕ}
    (hjk : j < k) :
    o.isOut (W.pairing (iterWalk κ β j)) =
      !o.isOut (iterWalk κ β (j + 1)) := by
  have h := o.match_flip _ (hcont j hjk)
  rw [← iterWalk_succ] at h
  rw [h, Bool.not_not]

end ChainOrbit

/-! ### The periodic/chain decomposition of the orbit count -/

section Decompose

variable (κ : F.RelTransitionSystem)

/-- Exit data from a terminating chain (a `LinearOrder`-free copy
of `traceChain_some_exit`). -/
private theorem traceChain_exit_data (κ : F.RelTransitionSystem) :
    ∀ (fuel : ℕ) (f b : W.Flag), traceChain κ fuel f = some b →
      ∃ k, (∀ j, j < k →
          W.pairing (iterWalk κ f j) ∈ F.internalFlags) ∧
        W.pairing (iterWalk κ f k) = b ∧ b ∈ F.boundaryFlags := by
  intro fuel
  induction fuel with
  | zero => intro f b h; simp [traceChain] at h
  | succ n ih =>
    intro f b h
    by_cases hb : W.pairing f ∈ F.boundaryFlags
    · rw [traceChain_boundary κ n f hb] at h
      refine ⟨0, fun j hj => absurd hj (by omega), ?_, ?_⟩
      · simpa using Option.some.inj h
      · rw [← Option.some.inj h]; exact hb
    · by_cases hi : W.pairing f ∈ F.internalFlags
      · rw [traceChain_internal κ n f hi] at h
        obtain ⟨k, hcont, hexit, hbb⟩ :=
          ih (κ.match_ (W.pairing f)) b h
        refine ⟨k + 1, ?_, ?_, hbb⟩
        · intro j hj
          cases j with
          | zero => simpa using hi
          | succ j' =>
            have hstep := hcont j' (by omega)
            rwa [iterWalk_shift] at hstep
        · rwa [iterWalk_shift] at hexit
      · rw [traceChain_neither κ n f hb hi] at h; cases h

/-- The full walk preserves periodicity. -/
theorem fullPerm_periodic_iff (x : {f : W.Flag // f ∈ F.flags}) :
    (fullPerm κ x).val ∈ κ.periodicFlags ↔
      x.val ∈ κ.periodicFlags := by
  constructor
  · intro h
    have hper : κ.PeriodicFlag ((fullPerm κ x).val) :=
      (κ.mem_periodicFlags).mp h
    have hzint : (fullPerm κ x).val ∈ F.internalFlags :=
      hper.mem_internal
    have hx : ((fullPerm κ)⁻¹ (fullPerm κ x)) = x := by
      rw [Equiv.Perm.inv_def]
      exact Equiv.symm_apply_apply _ _
    have h1 : ((fullPerm κ)⁻¹ (fullPerm κ x)).val =
        W.pairing (κ.match_ ((fullPerm κ x).val)) := by
      rw [fullPerm_inv]
      change (pairingPermSP F
        (fullMatchPerm κ (fullPerm κ x))).val = _
      rw [pairingPermSP_val, fullMatchPerm_apply,
        fullMatchFun_val_internal κ hzint]
    rw [hx] at h1
    rw [κ.mem_periodicFlags, h1]
    exact periodicFlag_pairing (periodicFlag_match hper)
  · intro h
    have hper : κ.PeriodicFlag x.val := (κ.mem_periodicFlags).mp h
    have hσ : W.pairing x.val ∈ F.internalFlags := by
      have h0 := all_pairings_internal_of_periodic κ hper 0
      rwa [iterWalk_zero] at h0
    rw [κ.mem_periodicFlags, fullPerm_val_internal hσ,
      show κ.match_ (W.pairing x.val) = iterWalk κ x.val 1 from
        rfl]
    exact periodicFlag_iterWalk κ hper 1

/-- The full walk restricted to periodic flags. -/
noncomputable def fullPermPeriodic :
    Equiv.Perm {x : {f : W.Flag // f ∈ F.flags} //
      x.val ∈ κ.periodicFlags} :=
  (fullPerm κ).subtypePerm (fun x => fullPerm_periodic_iff κ x)

/-- The full walk restricted to non-periodic flags. -/
noncomputable def fullPermChain :
    Equiv.Perm {x : {f : W.Flag // f ∈ F.flags} //
      ¬ x.val ∈ κ.periodicFlags} :=
  (fullPerm κ).subtypePerm
    (fun x => not_congr (fullPerm_periodic_iff κ x))

/-- The decomposition of the full walk over the periodicity
partition. -/
theorem fullPerm_eq_sumCongr :
    fullPerm κ = (Equiv.sumCompl
        (fun x : {f : W.Flag // f ∈ F.flags} =>
          x.val ∈ κ.periodicFlags)).permCongr
      (Equiv.sumCongr (fullPermPeriodic κ) (fullPermChain κ)) := by
  apply Equiv.ext
  intro z
  rw [Equiv.permCongr_apply]
  by_cases h : z.val ∈ κ.periodicFlags
  · rw [Equiv.sumCompl_symm_apply_of_pos
      (p := fun x : {f : W.Flag // f ∈ F.flags} =>
        x.val ∈ κ.periodicFlags) h]
    rfl
  · rw [Equiv.sumCompl_symm_apply_of_neg
      (p := fun x : {f : W.Flag // f ∈ F.flags} =>
        x.val ∈ κ.periodicFlags) h]
    rfl

/-- The orbit count splits over the partition. -/
theorem permOrbitCount_fullPerm_split :
    permOrbitCount (fullPerm κ) =
      permOrbitCount (fullPermPeriodic κ) +
        permOrbitCount (fullPermChain κ) := by
  rw [fullPerm_eq_sumCongr κ, permOrbitCount_permCongr,
    permOrbitCount_sumCongr]

/-- The double-subtype carrier of the periodic part. -/
noncomputable def periodicSubEquiv :
    {x : {f : W.Flag // f ∈ F.flags} //
      x.val ∈ κ.periodicFlags} ≃
      {f : W.Flag // f ∈ κ.periodicFlags} where
  toFun x := ⟨x.val.val, x.prop⟩
  invFun f := ⟨⟨f.val, mem_flags_of_internalFlags F
    (κ.periodicFlags_sub f.prop)⟩, f.prop⟩
  left_inv _x := Subtype.ext (Subtype.ext rfl)
  right_inv _f := rfl

/-- The periodic part of the full walk is the periodic walk
permutation. -/
theorem walkPermPeriodic_eq_permCongr :
    κ.walkPermPeriodic =
      (periodicSubEquiv κ).permCongr (fullPermPeriodic κ) := by
  apply Equiv.ext
  intro f
  apply Subtype.ext
  rw [Equiv.permCongr_apply]
  have hσ : W.pairing f.val ∈ F.internalFlags := by
    have h0 := all_pairings_internal_of_periodic κ
      ((κ.mem_periodicFlags).mp f.prop) 0
    rwa [iterWalk_zero] at h0
  change κ.internalWalk f.val =
    ((fullPerm κ) ⟨f.val, mem_flags_of_internalFlags F
      (κ.periodicFlags_sub f.prop)⟩).val
  rw [fullPerm_val_internal hσ]
  rfl

/-- The periodic part has the periodic orbit count. -/
theorem permOrbitCount_fullPermPeriodic :
    permOrbitCount (fullPermPeriodic κ) =
      permOrbitCount κ.walkPermPeriodic := by
  rw [walkPermPeriodic_eq_permCongr κ, permOrbitCount_permCongr]

/-- Values of powers of the chain part. -/
theorem fullPermChain_pow_val (z : {x : {f : W.Flag // f ∈ F.flags} //
      ¬ x.val ∈ κ.periodicFlags}) (n : ℕ) :
    (((fullPermChain κ) ^ n) z).val = ((fullPerm κ) ^ n) z.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : ((fullPermChain κ) ^ (n + 1)) z =
        (fullPermChain κ) (((fullPermChain κ) ^ n) z) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have h2 : ((fullPerm κ) ^ (n + 1)) z.val =
        (fullPerm κ) (((fullPerm κ) ^ n) z.val) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [h1, h2, ← ih]
    rfl

/-- `SameCycle` in the chain part descends to the full walk. -/
theorem sameCycle_fullPermChain_val {z w : {x : {f : W.Flag // f ∈ F.flags} //
      ¬ x.val ∈ κ.periodicFlags}}
    (h : (fullPermChain κ).SameCycle z w) :
    (fullPerm κ).SameCycle z.val w.val := by
  obtain ⟨i, _, _, hi⟩ := Equiv.Perm.SameCycle.exists_pow_eq _ h
  refine sameCycle_of_pow_eq (n := i) ?_
  rw [← fullPermChain_pow_val, hi]

/-- **The chain part counts the boundary flags**: each non-periodic
orbit contains exactly one boundary flag. -/
theorem permOrbitCount_fullPermChain :
    permOrbitCount (fullPermChain κ) = F.boundaryFlags.card := by
  classical
  have hres := permOrbitCount_eq_card_of_reps (fullPermChain κ)
    (Finset.univ.filter (fun z => z.val.val ∈ F.boundaryFlags))
    ?_ ?_
  · rw [hres]
    refine Finset.card_bij' (fun z _ => z.val.val)
      (fun b hb => ⟨⟨b, mem_flags_of_boundaryFlags F hb⟩,
        fun hper => Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags
          (κ.periodicFlags_sub hper) hb⟩) ?_ ?_ ?_ ?_
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro b hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
    · intro z _
      exact Subtype.ext (Subtype.ext rfl)
    · intro b _
      rfl
  · -- cover
    intro z
    by_cases hzb : z.val.val ∈ F.boundaryFlags
    · exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzb⟩,
        Equiv.Perm.SameCycle.refl _ _⟩
    · have hzi : z.val.val ∈ F.internalFlags :=
        (F.mem_internalFlags_or_boundaryFlags
          z.val.prop).resolve_right hzb
      have hznp : ¬ κ.PeriodicFlag z.val.val := fun hper =>
        z.prop ((κ.mem_periodicFlags).mpr hper)
      rcases internal_periodic_or_terminates κ z.val.val hzi with
        hper | ⟨fuel, b0, htr⟩
      · exact absurd hper hznp
      obtain ⟨kf, hcontf, hexitf, hb0⟩ :=
        traceChain_exit_data κ fuel z.val.val b0 htr
      refine ⟨((fullPermChain κ) ^ (kf + 1)) z, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [fullPermChain_pow_val]
        have h1 : ((fullPerm κ) ^ (kf + 1)) z.val =
            fullPerm κ (((fullPerm κ) ^ kf) z.val) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        have hval : (((fullPerm κ) ^ kf) z.val).val =
            iterWalk κ z.val.val kf :=
          fullPerm_pow_val (fun t ht => hcontf t ht) kf le_rfl
        have hb : W.pairing ((((fullPerm κ) ^ kf) z.val).val) ∈
            F.boundaryFlags := by
          rw [hval, hexitf]
          exact hb0
        rw [h1, fullPerm_val_boundary hb]
        exact κ.pathMatch_mem hb
      · exact (sameCycle_of_pow_eq (n := kf + 1) rfl).symm
  · -- separation
    intro w hw w' hw' hsc
    have hwb : w.val.val ∈ F.boundaryFlags :=
      (Finset.mem_filter.mp hw).2
    have hwb' : w'.val.val ∈ F.boundaryFlags :=
      (Finset.mem_filter.mp hw').2
    have hscv : (fullPerm κ).SameCycle w.val w'.val :=
      sameCycle_fullPermChain_val κ hsc
    obtain ⟨k, hkle, hcont, hterm⟩ :=
      chain_terminates_with_data κ hwb
    have hb : (fullPerm κ).SameCycle
        ⟨w.val.val, mem_flags_of_boundaryFlags F hwb⟩ w'.val :=
      hscv
    have := fullPerm_chain_boundary_eq hwb hkle hcont hterm hb
      hwb'
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val this.symm

/-- **The orbit bookkeeping**: the full walk's orbit count is the
periodic orbit count plus the number of boundary flags. -/
theorem permOrbitCount_fullPerm_eq :
    permOrbitCount (fullPerm κ) =
      permOrbitCount κ.walkPermPeriodic + F.boundaryFlags.card := by
  rw [permOrbitCount_fullPerm_split κ,
    permOrbitCount_fullPermPeriodic κ,
    permOrbitCount_fullPermChain κ]

end Decompose

/-! ### The move as a double swap -/

section RepairFull

variable {κ : F.RelTransitionSystem} {a b c d : W.Flag}
  {v : W.Vertex}

/-- **The move is a double swap**: on a square whose repair leaves
the path matching unchanged, the repaired full walk is the old full
walk multiplied by the double transposition `(a d)(b c)`. -/
theorem fullPerm_repair (hsq : RepairSquare κ a b c d v)
    (hpm : ∀ δ (hδ : δ ∈ F.boundaryFlags),
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ) :
    fullPerm (κ.repair a b c d v hsq) =
      Equiv.swap ⟨a, mem_flags_of_internalFlags F hsq.ha⟩
          ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ *
        (Equiv.swap ⟨b, mem_flags_of_internalFlags F hsq.hb⟩
            ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ *
          fullPerm κ) := by
  set aX : {f : W.Flag // f ∈ F.flags} :=
    ⟨a, mem_flags_of_internalFlags F hsq.ha⟩ with haX
  set bX : {f : W.Flag // f ∈ F.flags} :=
    ⟨b, mem_flags_of_internalFlags F hsq.hb⟩ with hbX
  set cX : {f : W.Flag // f ∈ F.flags} :=
    ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ with hcX
  set dX : {f : W.Flag // f ∈ F.flags} :=
    ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ with hdX
  have hval_a : aX.val = a := rfl
  have hval_b : bX.val = b := rfl
  have hval_c : cX.val = c := rfl
  have hval_d : dX.val = d := rfl
  have hne_ca : cX ≠ aX := fun h =>
    hsq.hac (by rw [← hval_a, ← hval_c, h])
  -- ═══════ THE SQUARE'S FOUR FLAGS ARE PAIRWISE DISTINCT ═══════
  -- Below: the repaired walk permutation is the old one times two
  -- transpositions, and its cycle count follows.
  have hne_cd : cX ≠ dX := fun h =>
    hsq.hdc (by rw [← hval_c, ← hval_d, h])
  have hne_ab : aX ≠ bX := fun h =>
    hsq.hba (by rw [← hval_a, ← hval_b, h])
  have hne_ac : aX ≠ cX := fun h =>
    hsq.hac (by rw [← hval_a, ← hval_c, h])
  have hne_db : dX ≠ bX := fun h =>
    hsq.hbd (by rw [← hval_b, ← hval_d, h])
  have hne_dc : dX ≠ cX := fun h =>
    hsq.hdc (by rw [← hval_c, ← hval_d, h])
  have hne_ba : bX ≠ aX := fun h =>
    hsq.hba (by rw [← hval_a, ← hval_b, h])
  have hne_bd : bX ≠ dX := fun h =>
    hsq.hbd (by rw [← hval_b, ← hval_d, h])
  apply Equiv.ext
  intro z
  apply Subtype.ext
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  by_cases hσi : W.pairing z.val ∈ F.internalFlags
  · by_cases h1 : W.pairing z.val = a
    · have hPi : fullPerm κ z = bX := Subtype.ext
        (by rw [fullPerm_val_internal hσi, h1, hval_b]
            exact hsq.hab)
      rw [hPi, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hne_ca hne_cd,
        fullPerm_val_internal (κ := κ.repair a b c d v hsq) hσi,
        h1, RelTransitionSystem.repair_match_a hsq]
    · by_cases h2 : W.pairing z.val = b
      · have hPi : fullPerm κ z = aX := Subtype.ext
          (by rw [fullPerm_val_internal hσi, h2, hval_a]
              exact hsq.hmb)
        rw [hPi, Equiv.swap_apply_of_ne_of_ne hne_ab hne_ac,
          Equiv.swap_apply_left,
          fullPerm_val_internal (κ := κ.repair a b c d v hsq) hσi,
          h2, RelTransitionSystem.repair_match_b hsq]
      · by_cases h3 : W.pairing z.val = c
        · have hPi : fullPerm κ z = dX := Subtype.ext
            (by rw [fullPerm_val_internal hσi, h3, hval_d]
                exact hsq.hcd)
          rw [hPi, Equiv.swap_apply_of_ne_of_ne hne_db hne_dc,
            Equiv.swap_apply_right,
            fullPerm_val_internal (κ := κ.repair a b c d v hsq)
              hσi,
            h3, RelTransitionSystem.repair_match_c hsq]
        · by_cases h4 : W.pairing z.val = d
          · have hPi : fullPerm κ z = cX := Subtype.ext
              (by rw [fullPerm_val_internal hσi, h4, hval_c]
                  exact hsq.hmd)
            rw [hPi, Equiv.swap_apply_right,
              Equiv.swap_apply_of_ne_of_ne hne_ba hne_bd,
              fullPerm_val_internal (κ := κ.repair a b c d v hsq)
                hσi,
              h4, RelTransitionSystem.repair_match_d hsq]
          · obtain ⟨n1, n2, n3, n4⟩ :=
              hsq.match_ne_four hσi h1 h2 h3 h4
            have hPiv : (fullPerm κ z).val =
                κ.match_ (W.pairing z.val) :=
              fullPerm_val_internal hσi
            have hzb : fullPerm κ z ≠ bX := fun h =>
              n2 (by rw [← hPiv, ← hval_b, h])
            have hzc : fullPerm κ z ≠ cX := fun h =>
              n3 (by rw [← hPiv, ← hval_c, h])
            have hza : fullPerm κ z ≠ aX := fun h =>
              n1 (by rw [← hPiv, ← hval_a, h])
            have hzd : fullPerm κ z ≠ dX := fun h =>
              n4 (by rw [← hPiv, ← hval_d, h])
            rw [Equiv.swap_apply_of_ne_of_ne hzb hzc,
              Equiv.swap_apply_of_ne_of_ne hza hzd,
              fullPerm_val_internal (κ := κ.repair a b c d v hsq)
                hσi,
              RelTransitionSystem.repair_match_of_ne hsq h1 h2 h3
                h4, hPiv]
  · have hσb : W.pairing z.val ∈ F.boundaryFlags :=
      (F.mem_internalFlags_or_boundaryFlags
        (F.pairing_mem z.val z.prop)).resolve_left hσi
    have hPiv : (fullPerm κ z).val =
        κ.pathMatch (W.pairing z.val) hσb :=
      fullPerm_val_boundary hσb
    have hbd : (fullPerm κ z).val ∈ F.boundaryFlags := by
      rw [hPiv]
      exact κ.pathMatch_mem hσb
    have hnotin : ∀ {g : W.Flag}, g ∈ F.internalFlags →
        ∀ (hgf : g ∈ F.flags), fullPerm κ z ≠ ⟨g, hgf⟩ := by
      intro g hg hgf h
      have hvv : (fullPerm κ z).val = g := by rw [h]
      rw [hvv] at hbd
      exact Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hg hbd
    rw [Equiv.swap_apply_of_ne_of_ne (hnotin hsq.hb _)
        (hnotin hsq.hc _),
      Equiv.swap_apply_of_ne_of_ne (hnotin hsq.ha _)
        (hnotin hsq.hd _),
      fullPerm_val_boundary (κ := κ.repair a b c d v hsq) hσb,
      hPiv]
    exact hpm _ hσb

end RepairFull

/-! ### Orientation exclusions -/

section OrientationExclusion

variable {κ : F.RelTransitionSystem}

/-- Orientation constancy along a periodic walk. -/
theorem isOut_iterWalk_periodic (o : κ.Orientation) {f : W.Flag}
    (hper : κ.PeriodicFlag f) (i : ℕ) :
    o.isOut (iterWalk κ f i) = o.isOut f := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hint : iterWalk κ f i ∈ F.internalFlags := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [iterWalk_zero]
        exact hper.mem_internal
      · exact iterWalk_mem_internal_of_periodic κ hper i hi
    rw [iterWalk_succ,
      o.match_flip _ (all_pairings_internal_of_periodic κ hper i),
      o.pairing_flip _ hint
        (all_pairings_internal_of_periodic κ hper i),
      Bool.not_not, ih]

/-- **The separated exclusion, periodic seed**: a flag oppositely
oriented to a periodic flag is not on its full-walk orbit. -/
theorem not_sameCycle_of_periodic_flip (o : κ.Orientation)
    {x y : {h : W.Flag // h ∈ F.flags}}
    (hper : κ.PeriodicFlag x.val)
    (hflip : o.isOut y.val = !o.isOut x.val) :
    ¬ (fullPerm κ).SameCycle x y := by
  intro h
  obtain ⟨i, hi⟩ := sameCycle_periodic_val hper h
  have hconst := isOut_iterWalk_periodic o hper i
  rw [hi, hflip] at hconst
  simp at hconst

/-- **The separated exclusion, chain seeds**: two chain flags in
separated orientation are not on a common full-walk orbit. -/
theorem not_sameCycle_of_chain_positions {β : W.Flag}
    (hβ : β ∈ F.boundaryFlags) {k : ℕ} (hkle : k ≤ F.flags.card)
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ β k) ∈ F.boundaryFlags)
    (o : κ.Orientation)
    {x y : {h : W.Flag // h ∈ F.flags}}
    (hxi : x.val ∈ F.internalFlags) (hyi : y.val ∈ F.internalFlags)
    {s t : ℕ} (hsk : s ≤ k) (htk : t ≤ k)
    (hxs : x.val = iterWalk κ β s ∨
      x.val = W.pairing (iterWalk κ β s))
    (hyt : y.val = iterWalk κ β t ∨
      y.val = W.pairing (iterWalk κ β t))
    (hflip : o.isOut y.val = !o.isOut x.val) :
    ¬ (fullPerm κ).SameCycle x y := by
  rcases hxs with hxs | hxs <;> rcases hyt with hyt | hyt
  · -- walk/walk: same orientation, contradiction with `hflip`
    intro _h
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with rfl | h
      · rw [iterWalk_zero] at hxs
        exact absurd hβ (Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags (hxs ▸ hxi))
      · exact h
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · rw [iterWalk_zero] at hyt
        exact absurd hβ (Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags (hyt ▸ hyi))
      · exact h
    have heq : o.isOut y.val = o.isOut x.val := by
      rw [hxs, hyt]
      rcases le_total s t with hst | hts
      · exact isOut_iterWalk_chain hcont o hs1 hst
          htk
      · exact (isOut_iterWalk_chain hcont o ht1 hts
          hsk).symm
    rw [heq] at hflip
    simp at hflip
  · -- walk/pairing: mirror collision
    intro h
    have hx' : x = (fullPerm κ ^ s)
        ⟨β, mem_flags_of_boundaryFlags F hβ⟩ :=
      Subtype.ext (by rw [fullPerm_pow_val hcont s hsk]; exact hxs)
    have hbx : (fullPerm κ).SameCycle
        ⟨β, mem_flags_of_boundaryFlags F hβ⟩ x := by
      rw [hx']
      exact sameCycle_of_pow_eq rfl
    obtain ⟨j, hjk, hjv⟩ := fullPerm_chain_sameCycle_val hβ hkle
      hcont hterm (hbx.trans h)
    refine pairing_iterWalk_ne κ hcont htk hjk ?_
    rw [← hyt]
    exact hjv
  · -- pairing/walk: mirror collision
    intro h
    have hy' : y = (fullPerm κ ^ t)
        ⟨β, mem_flags_of_boundaryFlags F hβ⟩ :=
      Subtype.ext (by rw [fullPerm_pow_val hcont t htk]; exact hyt)
    have hby : (fullPerm κ).SameCycle
        ⟨β, mem_flags_of_boundaryFlags F hβ⟩ y := by
      rw [hy']
      exact sameCycle_of_pow_eq rfl
    obtain ⟨j, hjk, hjv⟩ := fullPerm_chain_sameCycle_val hβ hkle
      hcont hterm (hby.trans h.symm)
    refine pairing_iterWalk_ne κ hcont hsk hjk ?_
    rw [← hxs]
    exact hjv
  · -- pairing/pairing: same orientation, contradiction
    intro _h
    have hsk' : s < k := by
      rcases Nat.eq_or_lt_of_le hsk with rfl | h
      · exfalso
        have hb : x.val ∈ F.boundaryFlags := by
          rw [hxs]
          exact hterm
        exact Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags hxi hb
      · exact h
    have htk' : t < k := by
      rcases Nat.eq_or_lt_of_le htk with rfl | h
      · exfalso
        have hb : y.val ∈ F.boundaryFlags := by
          rw [hyt]
          exact hterm
        exact Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags hyi hb
      · exact h
    have hwx : o.isOut x.val = !o.isOut (iterWalk κ β (s + 1)) := by
      rw [hxs]
      exact isOut_pairing_iterWalk_chain hcont o hsk'
    have hwy : o.isOut y.val = !o.isOut (iterWalk κ β (t + 1)) := by
      rw [hyt]
      exact isOut_pairing_iterWalk_chain hcont o htk'
    have hw : o.isOut (iterWalk κ β (t + 1)) =
        o.isOut (iterWalk κ β (s + 1)) := by
      rcases le_total (s + 1) (t + 1) with hst | hts
      · exact isOut_iterWalk_chain hcont o
          (by omega) hst (by omega)
      · exact (isOut_iterWalk_chain hcont o
          (by omega) hts (by omega)).symm
    rw [hwx, hwy, hw] at hflip
    simp at hflip

end OrientationExclusion

end EdgeSubset

/-! ## (iii) The discharged parity input -/

open EdgeSubset in
/-- **The separated count parity** (the input
`SeparatedCountParity`): a
separated square on a localized configuration flips the
circuit-count parity. -/
theorem separatedCountParity : SeparatedCountParity := by
  intro α W F κ a b c d v hsq o hflip hloc
  classical
  -- the pathMatch invariance of the localized move
  have hpm := pathMatch_repair_of_localized hsq hloc
  -- ═══════ STAGE 1: THE SQUARE'S CORNERS AND THEIR STEPS ═══════
  -- distinctness of the square corners in the flag subtype
  have hbcX : (⟨b, mem_flags_of_internalFlags F hsq.hb⟩ :
      {f : W.Flag // f ∈ F.flags}) ≠
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ := fun h =>
    hsq.hbc (congrArg Subtype.val h)
  have hadX : (⟨a, mem_flags_of_internalFlags F hsq.ha⟩ :
      {f : W.Flag // f ∈ F.flags}) ≠
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := fun h =>
    hsq.had (congrArg Subtype.val h)
  -- the single-step relations `σb ∼ a` and `σc ∼ d`
  have hstep_b : fullPerm κ (pairingPermSP F
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩) =
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩ := by
    apply Subtype.ext
    rw [fullPerm_apply_pairing,
      fullMatchFun_val_internal κ
        (show (⟨b, mem_flags_of_internalFlags F hsq.hb⟩ :
          {f : W.Flag // f ∈ F.flags}).val ∈ F.internalFlags from
          hsq.hb)]
    exact hsq.hmb
  have hstep_c : fullPerm κ (pairingPermSP F
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩) =
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := by
    apply Subtype.ext
    rw [fullPerm_apply_pairing,
      fullMatchFun_val_internal κ
        (show (⟨c, mem_flags_of_internalFlags F hsq.hc⟩ :
          {f : W.Flag // f ∈ F.flags}).val ∈ F.internalFlags from
          hsq.hc)]
    exact hsq.hcd
  have hrel_b : (fullPerm κ).SameCycle
      (pairingPermSP F ⟨b, mem_flags_of_internalFlags F hsq.hb⟩)
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩ := by
    rw [← hstep_b]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.SameCycle.refl _ _)
  have hrel_c : (fullPerm κ).SameCycle
      (pairingPermSP F ⟨c, mem_flags_of_internalFlags F hsq.hc⟩)
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := by
    rw [← hstep_c]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.SameCycle.refl _ _)
  -- ═══════ STAGE 2: THE MIRROR EQUIVALENCE `b ∼ c ↔ a ∼ d` ═══════
  have hiff : (fullPerm κ).SameCycle
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ ↔
      (fullPerm κ).SameCycle
        ⟨a, mem_flags_of_internalFlags F hsq.ha⟩
        ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := by
    constructor
    · intro h
      exact (hrel_b.symm.trans (sameCycle_pairingPermSP h)).trans
        hrel_c
    · intro h
      have h2 := sameCycle_pairingPermSP
        ((hrel_b.trans h).trans hrel_c.symm)
      rw [pairingPermSP_invol, pairingPermSP_invol] at h2
      exact h2
  -- ═══════ STAGE 3: THE THREE EXCLUSIONS ═══════
  -- exclusion `¬ b ∼ σb` (mirror collision at `b`)
  have hN1 : ¬ (fullPerm κ).SameCycle
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩
      (pairingPermSP F ⟨b, mem_flags_of_internalFlags F hsq.hb⟩)
      := by
    rcases hloc with ⟨hpa, _hpc⟩ | ⟨β, hβ, hall⟩
    · exact not_sameCycle_pairingPermSP_of_periodic
        (show κ.PeriodicFlag b from
          hsq.hab ▸ periodicFlag_match hpa)
    · rcases hall b (Or.inr (Or.inl rfl)) with hpb | hchain
      · exact not_sameCycle_pairingPermSP_of_periodic hpb
      · obtain ⟨k, hkle, hcont, hterm⟩ :=
          chain_terminates_with_data κ hβ
        obtain ⟨k', t, htk', hcont', hterm', hft⟩ := hchain
        have hkk : k' = k :=
          chain_exit_unique hcont' hterm' hcont hterm
        subst hkk
        exact not_sameCycle_pairingPermSP_of_chain hβ hkle hcont
          hterm (mem_flags_of_internalFlags F hsq.hb) htk' hft
  -- exclusion `¬ a ∼ b`
  have hab : ¬ (fullPerm κ).SameCycle
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩ := by
    intro h
    exact hN1 (h.symm.trans hrel_b.symm)
  -- exclusion `¬ a ∼ c` (the separated orientation)
  have hac : ¬ (fullPerm κ).SameCycle
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ := by
    rcases hloc with ⟨hpa, _hpc⟩ | ⟨β, hβ, hall⟩
    · exact not_sameCycle_of_periodic_flip o hpa hflip
    · rcases hall a (Or.inl rfl) with hpa | hchaina
      · exact not_sameCycle_of_periodic_flip o hpa hflip
      · rcases hall c (Or.inr (Or.inr (Or.inl rfl))) with
          hpc | hchainc
        · have hflip' : o.isOut a = !o.isOut c := by
            rw [hflip, Bool.not_not]
          exact fun h =>
            not_sameCycle_of_periodic_flip o hpc hflip' h.symm
        · obtain ⟨k, hkle, hcont, hterm⟩ :=
            chain_terminates_with_data κ hβ
          obtain ⟨ka, s, hsk, hconta, hterma, hfs⟩ := hchaina
          have hka : k = ka :=
            (chain_exit_unique hconta hterma hcont hterm).symm
          subst hka
          obtain ⟨kc, t, htk, hcontc, htermc, hftc⟩ := hchainc
          have hkc : k = kc :=
            (chain_exit_unique hcontc htermc hcont hterm).symm
          subst hkc
          exact not_sameCycle_of_chain_positions hβ hkle hcont
            hterm o hsq.ha hsq.hc hsk htk hfs hftc hflip
  -- ═══════ ASSEMBLY: THE DOUBLE SWAP AND THE ORBIT LEDGER ═══════
  have hswap := permOrbitCount_swap_swap_mul (g := fullPerm κ)
    hbcX hadX hiff hab hac
  rw [← fullPerm_repair hsq hpm] at hswap
  -- the orbit bookkeeping on both sides
  have h1 := permOrbitCount_fullPerm_eq κ
  have h2 := permOrbitCount_fullPerm_eq (κ.repair a b c d v hsq)
  have hc1 : κ.openCircuitCount =
      permOrbitCount κ.walkPermPeriodic / 2 := rfl
  have hc2 : (κ.repair a b c d v hsq).openCircuitCount =
      permOrbitCount (κ.repair a b c d v hsq).walkPermPeriodic / 2
      := rfl
  rw [Nat.odd_iff, hc1, hc2]
  rcases hswap with h | h <;> omega

end RS
