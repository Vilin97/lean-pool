/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Orientability
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance

/-!
# Legal set firings and the nested reduction chain

This module supplies the divisor-theoretic input of the van Dobben de
Bruyn--Gijswijt proof that `treewidth ≤ gonality`: their Lemma 1.3, which says
that an effective divisor can be driven to its `q`-reduced form through a
**nested** chain of legal set firings, every intermediate divisor effective.

The dependency (`chip-firing-with-lean`) supplies the legal-set vocabulary,
set-firing formulas, script primitives, and reduced-divisor chip test. What it
does not yet supply is the truncation lemma or nestedness of the firing sets,
which is what the extremal argument in
`TreewidthGonality/Gonality/BrambleGonality.lean` needs.

## Conventions (multiplicity!)

`outdegreeSet G U v = ∑_{u ∉ U} numEdges G v u` counts **with edge multiplicity**,
matching both `setFiring` and the dependency's `qReduced`. Firing every
vertex of `U` exactly once satisfies

* `setFiring G D U v = D v - outdegreeSet G U v` for `v ∈ U`;
* `setFiring G D U v = D v + outdegreeSet G Uᶜ v` for `v ∉ U`

— chips only ever *leave* the fired set and only ever *arrive* outside it.

A set `U` is **legal** for `D` when firing it keeps `D` effective, i.e.
`D u ≥ outdegreeSet G U u` for all `u ∈ U`.
-/

@[expose] public section

namespace Utilities.Gonality

open Finset

variable {G : CFGraph}

/-! ## Firing scripts and truncation

The nested chain below is obtained as the **level-set decomposition** of the
firing script that carries `D` to its `q`-reduced representative, so this section
records the one remaining piece of script calculus it needs. -/

/-- Firing everything once changes nothing, so **firing `Uᶜ` undoes firing `U`**.
This is what turns the step `Dⱼ₋₁ → Dⱼ` around in the main theorem: `Dⱼ₋₁` is
obtained from `Dⱼ` by firing the complement of `U j`. -/
theorem set_firing_compl_set_firing (D : CFDiv G) (U : Finset G.V) :
    setFiring G (setFiring G D U) Uᶜ = D := by
  classical
  funext v
  by_cases hv : v ∈ U
  · rw [set_firing_apply_of_not_mem G _ (by simpa),
      set_firing_apply_of_mem G D hv, compl_compl]
    omega
  · rw [set_firing_apply_of_mem G _ (by simpa),
      set_firing_apply_of_not_mem G D hv]
    omega

/-- **The truncation lemma.**  If `D` and `D + prin G x` are both effective then so
is every intermediate divisor obtained by truncating the script from below:
`D + prin G (x - c)⁺` is effective for every `c`.

This is the whole content of the nested chain: the level sets of `x` fire in
increasing order and every partial sum is such a truncation. -/
theorem effective_add_prin_truncate {D : CFDiv G} {x : firingScript G}
    (hD : effective D) (hDx : effective (D + prin G x)) (c : ℤ) :
    effective (D + prin G (fun v => max (x v - c) 0)) := by
  intro v
  have hynonneg : ∀ w : G.V, 0 ≤ max (x w - c) 0 := fun w => le_max_right _ _
  have hyge : ∀ w : G.V, x w - c ≤ max (x w - c) 0 := fun w => le_max_left _ _
  by_cases hv : x v ≤ c
  · have hyv : max (x v - c) 0 = 0 := max_eq_right (by omega)
    have hnn : 0 ≤ prin G (fun w => max (x w - c) 0) v := by
      rw [prin_apply]
      refine Finset.sum_nonneg fun u _ => ?_
      have : (0:ℤ) ≤ (fun w => max (x w - c) 0) u - (fun w => max (x w - c) 0) v := by
        show (0:ℤ) ≤ max (x u - c) 0 - max (x v - c) 0
        rw [hyv]
        have := hynonneg u
        omega
      exact mul_nonneg this (Int.natCast_nonneg _)
    have := hD v
    simp only [Pi.add_apply]
    omega
  · push Not at hv
    have hyv : max (x v - c) 0 = x v - c := max_eq_left (by omega)
    have hle : prin G x v ≤ prin G (fun w => max (x w - c) 0) v := by
      rw [prin_apply, prin_apply]
      refine Finset.sum_le_sum fun u _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (Int.natCast_nonneg _)
      show x u - x v ≤ max (x u - c) 0 - max (x v - c) 0
      rw [hyv]
      have := hyge u
      omega
    have := hDx v
    simp only [Pi.add_apply] at this ⊢
    omega

/-! ## Iterated firing -/

/-- `fireChain G D U i` is the result of firing `U 0, U 1, …, U (i-1)` in turn. -/
def fireChain (G : CFGraph) (D : CFDiv G) (U : ℕ → Finset G.V) : ℕ → CFDiv G
  | 0 => D
  | (i + 1) => setFiring G (fireChain G D U i) (U i)

@[simp] theorem fireChain_zero (D : CFDiv G) (U : ℕ → Finset G.V) :
    fireChain G D U 0 = D := rfl

@[simp] theorem fireChain_succ (D : CFDiv G) (U : ℕ → Finset G.V) (i : ℕ) :
    fireChain G D U (i + 1) = setFiring G (fireChain G D U i) (U i) := rfl

/-- Every divisor in a firing chain is linearly equivalent to the initial one. -/
theorem fireChain_linear_equiv (D : CFDiv G) (U : ℕ → Finset G.V) (i : ℕ) :
    linearEquiv G D (fireChain G D U i) := by
  induction i with
  | zero => exact linearEquiv.refl G D
  | succ i ih => exact linearEquiv.trans ih (linear_equiv_set_firing _ _)

/-- Every divisor in a chain of legal firings is effective. -/
theorem fireChain_effective {D : CFDiv G} (hD : effective D) {U : ℕ → Finset G.V}
    {k : ℕ} (hlegal : ∀ i, i < k → legalSet G (fireChain G D U i) (U i)) :
    ∀ i, i ≤ k → effective (fireChain G D U i) := by
  intro i
  induction i with
  | zero => intro _; exact hD
  | succ i ih =>
      intro hik
      exact effective_set_firing_of_legal_set G (ih (by omega)) (hlegal i (by omega))

/-! ## The nested chain (van Dobben de Bruyn--Gijswijt, Lemma 1.3) -/

/-- **The nested legal chain.**  From an effective divisor `D` and a vertex `q`
there is a finite chain of legal firings, with the fired sets *nested* and
avoiding `q`, whose end result is `q`-reduced.

Proved (2026-08-25); this is Lemma 1.3 of van Dobben de Bruyn--Gijswijt
(arXiv:1407.7055), and only existence is claimed — the paper never uses
uniqueness of the chain.

**The route actually taken is the paper's level-set decomposition, not the
"maximal legal set" route this docstring used to recommend.**  That route is a
dead end: a set `U` legal for `D` is *not* in general legal for
`setFiring G D U` (that would need `D u ≥ 2 · outdegreeSet G U u`), so maximality at consecutive steps
does not force nestedness.  What works instead:

* take `D'`, the `q`-reduced representative of `D` (`exists_q_reduced_representative`),
  effective because `D` is (`effective_of_winnable_and_q_reduced`);
* write `D' = D + prin G x` and normalize the script by `x q = 0`
  (`prin_sub_const`);
* `x ≥ 0`: the bottom level set `W = {v | x v = min x}` is legal for `D'` — it is
  the first firing of the *reverse* chain, so `effective_add_prin_truncate`
  applies — and a `q`-reduced divisor admits no nonempty legal subset of
  `univ.erase q`, forcing `q ∈ W`, i.e. `min x = x q = 0`;
* the chain is the level-set family `U i = {v | K - i ≤ x v}` with `K = max x`,
  fired in *increasing* order `i = 0, …, K-1`.  Its partial sums are exactly the
  truncations `(x - (K - t))⁺`, so `effective_add_prin_truncate` makes every
  intermediate divisor effective, which is the same thing as legality of each
  step; and the last truncation is `x` itself, so the chain ends at `D'`.

The only real content is `effective_add_prin_truncate`, four lines of case
analysis on `x v ≤ c`. -/
theorem exists_nested_legal_chain (h_conn : graphConnected G) (q : G.V)
    {D : CFDiv G} (hD : effective D) :
    ∃ (k : ℕ) (U : ℕ → Finset G.V),
      (∀ i, i < k → U i ⊆ Finset.univ.erase q) ∧
      (∀ i, i < k → (U i).Nonempty) ∧
      (∀ i j, i ≤ j → j < k → U i ⊆ U j) ∧
      (∀ i, i < k → legalSet G (fireChain G D U i) (U i)) ∧
      qReduced G q (fireChain G D U k) := by
  classical
  -- The target of the chain: the `q`-reduced representative, which is effective
  -- because `D` is.
  obtain ⟨D', hequiv, hred⟩ := exists_q_reduced_representative h_conn q D
  have hD'eff : effective D' :=
    effective_of_winnable_and_q_reduced G q D' ⟨D, hD, hequiv.symm⟩ hred
  -- The firing script carrying `D` to `D'`, normalized to vanish at `q`.
  obtain ⟨x₀, hx₀⟩ := (principal_iff_eq_prin G (D' - D)).mp hequiv
  set x : firingScript G := fun v => x₀ v - x₀ q with hxdef
  have hxq : x q = 0 := by simp [hxdef]
  have hD'eq : D' = D + prin G x := by
    rw [hxdef, prin_sub_const]
    funext v
    have h := congrFun hx₀ v
    simp only [Pi.sub_apply] at h
    simp only [Pi.add_apply]
    omega
  have hDx : effective (D + prin G x) := by rw [← hD'eq]; exact hD'eff
  -- The reverse script takes `D'` back to `D`.
  have hrev : effective (D' + prin G (fun v => -x v)) := by
    have hneg : prin G (fun v => -x v) = -prin G x := by
      have hxx : (fun v => -x v) = -x := rfl
      rw [hxx, map_neg]
    rw [hneg, hD'eq]
    have : D + prin G x + -prin G x = D := by abel
    rw [this]; exact hD
  -- **The script is nonnegative**: its minimum is attained at `q`, because the
  -- bottom level set is legal for the `q`-reduced divisor `D'`.
  have hxnonneg : ∀ v : G.V, 0 ≤ x v := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v₀, hv₀⟩ := hcon
    obtain ⟨m, -, hm⟩ :=
      Finset.exists_min_image (Finset.univ : Finset G.V) x ⟨q, Finset.mem_univ q⟩
    set W : Finset G.V := Finset.univ.filter (fun v => x v = x m) with hW
    have hmW : m ∈ W := by simp [hW]
    have hWq : q ∉ W := by
      simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      have hmv := hm v₀ (Finset.mem_univ v₀)
      omega
    -- `W` is legal for `D'`: it is the first firing of the reverse chain.
    have hWlegal : legalSet G D' W := by
      have htr := effective_add_prin_truncate hD'eff hrev (-(x m) - 1)
      have heq : (fun v => max ((fun w => -x w) v - (-(x m) - 1)) 0)
          = indicatorScript G W := by
        funext v
        have hge : x m ≤ x v := hm v (Finset.mem_univ v)
        by_cases h : x v = x m
        · have hvW : v ∈ W := by simp [hW, h]
          show max (-x v - (-(x m) - 1)) 0 = indicatorScript G W v
          rw [indicatorScript, if_pos hvW]
          omega
        · have hvW : v ∉ W := by simp [hW, h]
          show max (-x v - (-(x m) - 1)) 0 = indicatorScript G W v
          rw [indicatorScript, if_neg hvW]
          omega
      rw [heq, ← set_firing_eq_add_prin_indicator_script] at htr
      intro u hu
      have hu' := htr u
      rw [set_firing_apply_of_mem G D' hu] at hu'
      omega
    obtain ⟨v, hvW, hlt⟩ := hred.exists_lt_outdeg hWq ⟨m, hmW⟩
    have hge := hWlegal v hvW
    omega
  -- The top of the chain.
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_max_image (Finset.univ : Finset G.V) x ⟨q, Finset.mem_univ q⟩
  set K : ℤ := x p with hK
  have hK0 : 0 ≤ K := by rw [hK, ← hxq]; exact hp q (Finset.mem_univ q)
  set k : ℕ := K.toNat with hk
  have hkK : (k : ℤ) = K := Int.toNat_of_nonneg hK0
  -- The level sets, fired from the top level downwards, i.e. increasing.
  set U : ℕ → Finset G.V := fun i => Finset.univ.filter (fun v => K - (i : ℤ) ≤ x v) with hU
  have hmemU : ∀ (i : ℕ) (v : G.V), v ∈ U i ↔ K - (i : ℤ) ≤ x v := by
    intro i v
    simp [hU]
  -- The chain of divisors is the truncation family of the script.
  have hchain : ∀ t : ℕ,
      fireChain G D U t = D + prin G (fun v => max (x v - (K - (t : ℤ))) 0) := by
    intro t
    induction t with
    | zero =>
        have h0 : (fun v => max (x v - (K - ((0 : ℕ) : ℤ))) 0) = (0 : firingScript G) := by
          funext v
          have hpv := hp v (Finset.mem_univ v)
          show max (x v - (K - ((0 : ℕ) : ℤ))) 0 = 0
          push_cast
          omega
        rw [fireChain_zero, h0, map_zero]
        simp
    | succ t ih =>
        have key : (fun v : G.V => max (x v - (K - ((t : ℤ) + 1))) 0)
            = (fun v : G.V => max (x v - (K - (t : ℤ))) 0) + indicatorScript G (U t) := by
          funext v
          show max (x v - (K - ((t : ℤ) + 1))) 0
              = max (x v - (K - (t : ℤ))) 0 + indicatorScript G (U t) v
          by_cases h : K - (t : ℤ) ≤ x v
          · rw [indicatorScript, if_pos ((hmemU t v).mpr h)]
            omega
          · rw [indicatorScript, if_neg (fun hc => h ((hmemU t v).mp hc))]
            omega
        rw [fireChain_succ, ih, set_firing_eq_add_prin_indicator_script]
        push_cast
        rw [key, map_add]
        abel
  -- Effectivity of every divisor in the chain, by the truncation lemma.
  have heff : ∀ t : ℕ, effective (fireChain G D U t) := by
    intro t
    rw [hchain]
    exact effective_add_prin_truncate hD hDx _
  refine ⟨k, U, ?_, ?_, ?_, ?_, ?_⟩
  · -- the fired sets avoid `q`
    intro i hi v hv
    have hvx : K - (i : ℤ) ≤ x v := (hmemU i v).mp hv
    have hik : (i : ℤ) < K := by omega
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ v⟩
    intro hveq
    rw [hveq, hxq] at hvx
    omega
  · -- the fired sets are nonempty
    intro i _
    refine ⟨p, (hmemU i p).mpr ?_⟩
    have : K = x p := hK
    have : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    omega
  · -- the fired sets are nested
    intro i j hij _ v hv
    have hvx : K - (i : ℤ) ≤ x v := (hmemU i v).mp hv
    refine (hmemU j v).mpr ?_
    have : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    omega
  · -- every step is legal
    intro i _ u hu
    have h := heff (i + 1) u
    rw [fireChain_succ, set_firing_apply_of_mem G _ hu] at h
    omega
  · -- the chain ends at the `q`-reduced representative
    have hend : fireChain G D U k = D' := by
      rw [hchain, hD'eq, hkK]
      congr 1
      congr 1
      funext v
      have := hxnonneg v
      show max (x v - (K - K)) 0 = x v
      omega
    rw [hend]
    exact hred

end Utilities.Gonality
