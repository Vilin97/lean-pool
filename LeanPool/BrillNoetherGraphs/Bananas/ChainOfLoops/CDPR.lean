/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionSixChainConclusion
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.CycleTorsionOrder
public import LeanPool.BrillNoetherGraphs.Bananas.Examples.ExampleBngChain

/-!
# Cools--Draisma--Payne--Robeva nonexistence for a chain of loops

(Cools--Draisma--Payne--Robeva, *A tropical proof of the Brill--Noether
theorem*, arXiv:1001.2774).

CDPR **Theorem 1.1** (`thm:Main`) states that a generic chain of loops has no
effective divisor in the negative Brill--Noether range, and in the
nonnegative range has no such divisor containing the specified multiple of
the left endpoint.

CDPR **Definition 4.1** (`defn:Generic`) excludes arc-length ratios represented
by two positive integers whose sum is at most `2g - 2`.

## What is formalized here, and what is not

CDPR work with **metric** graphs: `ℓ_i` and `m_i` are arbitrary positive
reals and divisors are `ℤ`-combinations of arbitrary points of `Γ`.  This
file proves the **discrete** (Baker--Norine) statement, for a chain of cycles
with arbitrary positive *integer* arc lengths, which is the theory the
`Bananas` library speaks. The relationship is:

* the metric theorem implies the discrete one, so this is a priori weaker for
  any single graph;
* genericity is invariant under subdivision (`(ℓ,m) ↦ (nℓ,nm)` leaves
  `(ℓ+m)/gcd(ℓ,m)` fixed), so the discrete statement quantified over all
  integer length vectors covers every subdivision of every rational chain of
  loops -- and CDPR's own suggested instance `ℓ_i = 2g-2`, `m_i = 1` is one of
  them;
* closing the remaining gap needs rank-invariance under subdivision
  (Hladky--Kral--Norine / Luo), which this repository does not have.

CDPR's loops are glued **directly** at the vertices `v_i`; there are no
bridges.  That is exactly `Utilities.MarkedGraph.chain`.

## The route

Part (1) is a pure instantiation of theorems already proved in `Bananas/`:

* `Bananas.cycle_kGeneralTransmission` (Pflueger--Solomon Example 1.11): a
  cycle with arcs of lengths `a` and `b`, marked at its two junction
  vertices, has `k`-general transmission at `k = (a+b)/gcd(a,b)`;
* `Bananas.brillNoetherGeneral_mixedTorsionChain_of_minBudget`
  (Pflueger--Solomon Theorem 1.13(2) = Corollary 6.16(2)).

`Bananas/Examples/ExampleBngChain.lean` is the worked five-factor instance of
the same assembly.

Part (2) adds one genuinely new lemma,
`finitePointedDiagram_card_ge_of_vanishing`: the bridge from the repository's
Young-diagram formulation of once-marked Brill--Noether generality
(`Bananas.OnceMarkedBrillNoetherGeneral`) to CDPR's "no divisor contains
`m v`" phrasing.  It consumes
`Bananas.onceMarkedBrillNoetherGeneral_mixedTorsionChain`
(Theorem 1.13(1) = Corollary 6.16(1)) at the chain's right mark, and its
reversed counterpart at the left.

**Endpoint orientation is load-bearing.**  The marked chain theorem concludes
at the chain's *right* mark under the *prefix* budget `k_i > g_1 + ... + g_i`;
CDPR state part (2) at `v_0`, the left end, which needs the *suffix* budget
`k_i > g_i + ... + g_l` instead.  Under CDPR genericity both hold, so the
distinction costs nothing here -- but it is not cosmetic: a numeric screen run
at `v_0` under the prefix budget reports immediate counterexamples at `g = 2`
(`ℓ_1 = m_1`, torsion order two, so `2 v_0` has rank one).
-/

@[expose] public section

namespace ChainOfLoops

open Utilities Bananas

/-! ## Loops -/

/-- One loop of a chain of loops: a cycle subdivided into a top arc of length
`top` and a bottom arc of length `bot`, both positive.  These are CDPR's
`ℓ_i` and `m_i`.

The positivity hypotheses are bundled into the structure on purpose: a
`List Loop` can then be `List.map`ped, and `List.take`/`List.drop` lemmas
apply, where a `List (ℕ × ℕ)` with side conditions would force `List.pmap`
throughout the `ChainMinBudget` arithmetic. -/
structure Loop where
  /-- The positive number of edges in the upper strand of the loop. -/
  top : ℕ
  /-- The positive number of edges in the lower strand of the loop. -/
  bot : ℕ
  top_pos : 0 < top
  bot_pos : 0 < bot

namespace Loop

/-- The loop as a genus-one banana, i.e. a cycle: two parallel strands of
lengths `top` and `bot` between the two junction vertices. -/
noncomputable def banana (P : Loop) : Banana 1 :=
  bananaOfLengths 1 ![P.top, P.bot] (by
    intro i
    fin_cases i
    · simpa using P.top_pos
    · simpa using P.bot_pos)

@[simp] theorem banana_length_zero (P : Loop) : P.banana.length 0 = P.top := rfl

@[simp] theorem banana_length_one (P : Loop) : P.banana.length 1 = P.bot := rfl

/-- The torsion order of `(loop, v_{i-1}, v_i)`: the order of the class of
`v_i - v_{i-1}` in the Jacobian of the cycle, which is `(ℓ+m)/gcd(ℓ,m)`
(`Bananas.cycle_isTorsionOrder`, Pflueger--Solomon Example 1.11). -/
def torsionOrder (P : Loop) : ℕ := (P.top + P.bot) / Nat.gcd P.top P.bot

/-! ### The reduced pair `(ℓ/d, m/d)`

The arithmetic behind `cdprGeneric_iff`: writing `d = gcd(ℓ,m)`, the pair
`(ℓ/d, m/d)` is the *least* positive solution of `ℓ q = m p`, and its
coordinate sum is exactly `torsionOrder`. -/

theorem gcd_pos (P : Loop) : 0 < Nat.gcd P.top P.bot :=
  Nat.gcd_pos_of_pos_left _ P.top_pos

theorem gcd_mul_top_div (P : Loop) :
    Nat.gcd P.top P.bot * (P.top / Nat.gcd P.top P.bot) = P.top :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

theorem gcd_mul_bot_div (P : Loop) :
    Nat.gcd P.top P.bot * (P.bot / Nat.gcd P.top P.bot) = P.bot :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

theorem top_div_gcd_pos (P : Loop) : 0 < P.top / Nat.gcd P.top P.bot :=
  Nat.div_pos (Nat.le_of_dvd P.top_pos (Nat.gcd_dvd_left _ _)) P.gcd_pos

theorem bot_div_gcd_pos (P : Loop) : 0 < P.bot / Nat.gcd P.top P.bot :=
  Nat.div_pos (Nat.le_of_dvd P.bot_pos (Nat.gcd_dvd_right _ _)) P.gcd_pos

theorem coprime_div_gcd (P : Loop) :
    Nat.Coprime (P.top / Nat.gcd P.top P.bot) (P.bot / Nat.gcd P.top P.bot) :=
  Nat.coprime_div_gcd_div_gcd P.gcd_pos

/-- `(ℓ + m)/d = ℓ/d + m/d`. -/
theorem torsionOrder_eq (P : Loop) :
    P.torsionOrder =
      P.top / Nat.gcd P.top P.bot + P.bot / Nat.gcd P.top P.bot := by
  have hsum : P.top + P.bot =
      Nat.gcd P.top P.bot *
        (P.top / Nat.gcd P.top P.bot + P.bot / Nat.gcd P.top P.bot) := by
    rw [Nat.mul_add, P.gcd_mul_top_div, P.gcd_mul_bot_div]
  rw [torsionOrder, hsum, Nat.mul_div_cancel_left _ P.gcd_pos]

theorem torsionOrder_pos (P : Loop) : 0 < P.torsionOrder := by
  rw [P.torsionOrder_eq]
  exact lt_of_lt_of_le P.top_div_gcd_pos (Nat.le_add_right _ _)

/-- The reduced pair is itself a solution of `ℓ q = m p`. -/
theorem top_mul_bot_div_gcd (P : Loop) :
    P.top * (P.bot / Nat.gcd P.top P.bot) =
      P.bot * (P.top / Nat.gcd P.top P.bot) := by
  apply Nat.eq_of_mul_eq_mul_left P.gcd_pos
  calc Nat.gcd P.top P.bot * (P.top * (P.bot / Nat.gcd P.top P.bot))
      = P.top * (Nat.gcd P.top P.bot * (P.bot / Nat.gcd P.top P.bot)) := by ring
    _ = P.bot * (Nat.gcd P.top P.bot * (P.top / Nat.gcd P.top P.bot)) := by
        rw [P.gcd_mul_top_div, P.gcd_mul_bot_div]; ring
    _ = Nat.gcd P.top P.bot * (P.bot * (P.top / Nat.gcd P.top P.bot)) := by ring

/-- Any solution of `ℓ q = m p` reduces: `(ℓ/d) q = (m/d) p`. -/
theorem reduced_mul_eq_mul (P : Loop) {p q : ℕ} (heq : P.top * q = P.bot * p) :
    P.top / Nat.gcd P.top P.bot * q = P.bot / Nat.gcd P.top P.bot * p := by
  apply Nat.eq_of_mul_eq_mul_left P.gcd_pos
  calc Nat.gcd P.top P.bot * (P.top / Nat.gcd P.top P.bot * q)
      = Nat.gcd P.top P.bot * (P.top / Nat.gcd P.top P.bot) * q := by ring
    _ = P.top * q := by rw [P.gcd_mul_top_div]
    _ = P.bot * p := heq
    _ = Nat.gcd P.top P.bot * (P.bot / Nat.gcd P.top P.bot) * p := by
        rw [P.gcd_mul_bot_div]
    _ = Nat.gcd P.top P.bot * (P.bot / Nat.gcd P.top P.bot * p) := by ring

/-- The loop packaged as a chain factor, carrying its `k`-general
transmission at `k = torsionOrder`. -/
noncomputable def factor (P : Loop) : KGeneralChainFactor where
  marked := ⟨P.banana.graph, leftEndpoint P.banana, rightEndpoint P.banana⟩
  period := P.torsionOrder
  connected := banana_graph_connected P.banana
  kGeneral := by
    -- `cycle_kGeneralTransmission P.banana` verbatim; the exponent rewrites to
    -- `P.torsionOrder` because the arc lengths are `rfl`.  Template:
    -- `Bananas/Examples/ExampleBngChain.lean:91` (`bngF1`).
    have hk : (P.banana.length 0 + P.banana.length 1) /
        Nat.gcd (P.banana.length 0) (P.banana.length 1) = P.torsionOrder := rfl
    exact hk ▸ cycle_kGeneralTransmission P.banana

@[simp] theorem factor_period (P : Loop) : P.factor.period = P.torsionOrder := rfl

@[simp] theorem factor_marked_graph (P : Loop) :
    P.factor.marked.graph = P.banana.graph := rfl

/-- Every loop has genus one. -/
@[simp] theorem genus_factor (P : Loop) : genus P.factor.marked.graph = 1 :=
  P.banana.genus_graph

end Loop

/-! ## The chain -/

/-- The chain of loops with first loop `P` and remaining loops `L`, as a
twice-marked graph: `left` is CDPR's `v_0` and `right` is `v_g`.

`g = L.length + 1`.  The head/tail shape, and the doubly mapped factor list,
match `Utilities.MarkedGraph.chain` and every chain theorem in `Bananas/`
on the nose: `List.map_map` is not a definitional equality, so writing the
list as `(L.map Loop.factor).map KGeneralChainFactor.marked` rather than the
fused `L.map (·.factor.marked)` is what lets the bananas conclusions and the
reversal isomorphism apply without any list transport. -/
noncomputable def chainMarked (P : Loop) (L : List Loop) : MarkedGraph :=
  P.factor.marked.chain ((L.map Loop.factor).map KGeneralChainFactor.marked)

/-- The underlying graph of a chain of loops. -/
noncomputable def chainGraph (P : Loop) (L : List Loop) : CFGraph :=
  (chainMarked P L).graph

/-- A chain of connected factors is connected. -/
private theorem graph_connected_markedChain (M : MarkedGraph) (L : List MarkedGraph)
    (hM : _root_.graphConnected M.graph)
    (hL : ∀ N ∈ L, _root_.graphConnected N.graph) :
    _root_.graphConnected (M.chain L).graph := by
  induction L generalizing M with
  | nil => simpa using hM
  | cons N rest ih =>
      rw [MarkedGraph.chain_cons]
      exact ih (M.wedge N)
        (graph_connected_vertexWedge _ _ _ _ hM (hL N (by simp)))
        (fun Q hQ => hL Q (by simp [hQ]))

/-- A chain of loops is connected. -/
theorem graph_connected_chainGraph (P : Loop) (L : List Loop) :
    _root_.graphConnected (chainGraph P L) := by
  apply graph_connected_markedChain _ _ P.factor.connected
  intro N hN
  simp only [List.mem_map] at hN
  obtain ⟨F, hF, rfl⟩ := hN
  obtain ⟨Q, _, rfl⟩ := hF
  exact Q.factor.connected

/-- The genus of a chain of factors is the head genus plus the factor genus
sum. -/
theorem genus_markedChain_map (M : MarkedGraph)
    (Ls : List KGeneralChainFactor) :
    genus (M.chain (Ls.map KGeneralChainFactor.marked)).graph =
      genus M.graph + chainFactorGenus Ls := by
  rw [MarkedGraph.genus_chain, List.map_map, chainFactorGenus]
  rfl

/-- `chainFactorGenus` of a mapped loop list is its length: every factor has
genus one. -/
@[simp] theorem chainFactorGenus_map (L : List Loop) :
    chainFactorGenus (L.map Loop.factor) = (L.length : ℤ) := by
  induction L with
  | nil => simp
  | cons Q rest ih =>
      rw [List.map_cons, chainFactorGenus_cons, Loop.genus_factor, ih]
      simp only [List.length_cons]
      push_cast
      ring

/-- The genus of a chain of `g` loops is `g`. -/
theorem genus_chainGraph (P : Loop) (L : List Loop) :
    genus (chainGraph P L) = (L.length : ℤ) + 1 := by
  rw [chainGraph, chainMarked, genus_markedChain_map, Loop.genus_factor,
    chainFactorGenus_map]
  ring

/-! ## Genericity -/

/-- **CDPR Definition 4.1**, literally: none of the ratios `ℓ_i / m_i` equals
the ratio of two positive integers whose sum is at most `2g - 2`.

Cross multiplication avoids a division convention, exactly as in
`Bananas.EvenlyMarkedTheta`. -/
def CDPRGeneric (L : List Loop) : Prop :=
  ∀ P ∈ L, ∀ p q : ℕ, 0 < p → 0 < q → p + q ≤ 2 * L.length - 2 →
    P.top * q ≠ P.bot * p

/-- CDPR genericity is exactly a lower bound on the torsion orders.

Writing `d = gcd(ℓ,m)`, every positive solution of `ℓ q = m p` is
`(p,q) = t · (ℓ/d, m/d)`, so the least attainable `p + q` is
`(ℓ+m)/d = torsionOrder`. -/
theorem cdprGeneric_iff (L : List Loop) :
    CDPRGeneric L ↔ ∀ P ∈ L, 2 * L.length - 2 < P.torsionOrder := by
  constructor
  · -- Forward: instantiate CDPR genericity at the reduced pair
    -- `(p,q) = (ℓ/d, m/d)`, whose sum is exactly `torsionOrder`.
    intro h P hP
    by_contra hle
    simp only [Nat.not_lt] at hle
    exact h P hP _ _ P.top_div_gcd_pos P.bot_div_gcd_pos
      (by rw [← P.torsionOrder_eq]; exact hle) P.top_mul_bot_div_gcd
  · -- Backward: any positive `(p,q)` with `ℓq = mp` is a multiple of the
    -- reduced pair, so `p + q ≥ ℓ/d + m/d = torsionOrder`.
    intro h P hP p q hp hq hsum heq
    have hkey := P.reduced_mul_eq_mul heq
    have hdvdp : P.top / Nat.gcd P.top P.bot ∣ p :=
      (P.coprime_div_gcd).dvd_of_dvd_mul_left ⟨q, hkey.symm⟩
    have hdvdq : P.bot / Nat.gcd P.top P.bot ∣ q :=
      (P.coprime_div_gcd).symm.dvd_of_dvd_mul_left ⟨p, hkey⟩
    have hle : P.torsionOrder ≤ p + q := by
      rw [P.torsionOrder_eq]
      exact Nat.add_le_add (Nat.le_of_dvd hp hdvdp) (Nat.le_of_dvd hq hdvdq)
    exact absurd hsum (Nat.not_le.mpr (lt_of_lt_of_le (h P hP) hle))

/-! ## The budget inequalities -/

/-- The period of the `i`-th mapped chain factor is the `i`-th torsion order. -/
theorem factor_get_period (L : List Loop) (i : ℕ)
    (hi : i < (L.map Loop.factor).length) (hi' : i < L.length) :
    ((L.map Loop.factor).get ⟨i, hi⟩).period = (L.get ⟨i, hi'⟩).torsionOrder := by
  simp only [List.get_eq_getElem, List.getElem_map, Loop.factor_period]

/-- The `ChainMinBudget` hypothesis of Corollary 6.16(2), specialised to
genus-one factors: `min(i+1, g-i) < k_i`. -/
theorem chainMinBudget_of_torsion (P : Loop) (L : List Loop)
    (h : ∀ (i : ℕ) (hi : i < (P :: L).length),
      min ((i : ℤ) + 1) (((P :: L).length : ℤ) - (i : ℤ)) <
        (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ)) :
    ChainMinBudget ((P :: L).map Loop.factor) := by
  intro i hi
  have hi' : i < (P :: L).length := by simpa using hi
  have hperiod := factor_get_period (P :: L) i hi hi'
  rw [hperiod, ← List.map_take, ← List.map_drop, chainFactorGenus_map,
    chainFactorGenus_map, List.length_take, List.length_drop]
  have e1 : min (i + 1) (P :: L).length = i + 1 := by omega
  rw [e1, Nat.cast_sub hi'.le]
  exact h i hi'

/-- The `ChainPrefixBudget` hypothesis of Corollary 6.16(1), specialised to
genus-one factors: `i + 1 < k_i`. -/
theorem chainPrefixBudget_of_torsion (P : Loop) (L : List Loop)
    (h : ∀ (i : ℕ) (hi : i < (P :: L).length),
      (i : ℤ) + 1 < (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ)) :
    ChainPrefixBudget (genus P.factor.marked.graph) (L.map Loop.factor) := by
  apply (chainPrefixBudget_iff_indexed _ _).mpr
  intro i hi
  have hiL : i < L.length := by simpa using hi
  have hi' : i + 1 < (P :: L).length := by simp only [List.length_cons]; omega
  have hperiod : ((L.map Loop.factor).get ⟨i, hi⟩).period
      = ((P :: L).get ⟨i + 1, hi'⟩).torsionOrder := by
    rw [factor_get_period L i hi hiL]
    simp [List.get_eq_getElem]
  rw [hperiod, ← List.map_take, chainFactorGenus_map, List.length_take,
    Loop.genus_factor]
  have e1 : min (i + 1) L.length = i + 1 := by omega
  rw [e1]
  have hh := h (i + 1) hi'
  push_cast at hh ⊢
  linarith

/-- The `ChainSuffixBudget` hypothesis of the reversed chain theorem,
specialised to genus-one factors: `g - i < k_i`.  This is the budget that
puts CDPR's own mark `v_0` at the general end. -/
theorem chainSuffixBudget_of_torsion (P : Loop) (L : List Loop)
    (h : ∀ (i : ℕ) (hi : i < (P :: L).length),
      ((P :: L).length : ℤ) - (i : ℤ) <
        (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ)) :
    ChainSuffixBudget ((P :: L).map Loop.factor) := by
  apply (chainSuffixBudget_iff_indexed _).mpr
  intro i hi
  have hi' : i < (P :: L).length := by simpa using hi
  rw [factor_get_period (P :: L) i hi hi', ← List.map_drop, chainFactorGenus_map,
    List.length_drop, Nat.cast_sub hi'.le]
  exact h i hi'

/-- CDPR genericity implies both budgets: `2g - 2 ≥ g > min(i+1, g-i)` and
`2g - 2 ≥ g > i + 1` for `g ≥ 2`. -/
theorem torsion_bounds_of_cdprGeneric (P : Loop) (L : List Loop)
    (hg : 2 ≤ L.length + 1) (hGeneric : CDPRGeneric (P :: L)) :
    (∀ (i : ℕ) (hi : i < (P :: L).length),
        min ((i : ℤ) + 1) (((P :: L).length : ℤ) - (i : ℤ)) <
          (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ)) ∧
      ∀ (i : ℕ) (hi : i < (P :: L).length),
        (i : ℤ) + 1 < (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ) := by
  have hk := (cdprGeneric_iff (P :: L)).mp hGeneric
  -- `i + 1 ≤ g ≤ 2g - 2 < k_i` for every index `i`, whenever `g ≥ 2`.
  have hstep : ∀ (i : ℕ) (hi : i < (P :: L).length),
      (i : ℤ) + 1 < (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ) := by
    intro i hi
    have hmem : (P :: L).get ⟨i, hi⟩ ∈ (P :: L) := List.get_mem _ _
    have h1 := hk _ hmem
    simp only [List.length_cons] at h1 hi
    have hnat : i + 1 < ((P :: L).get ⟨i, hi⟩).torsionOrder := by omega
    exact_mod_cast hnat
  refine ⟨fun i hi => lt_of_le_of_lt (min_le_left _ _) (hstep i hi), hstep⟩

/-- CDPR genericity also implies the suffix budget `g - i < k_i`, which is
what puts the *left* mark `v_0` at the general end. -/
theorem torsion_suffix_bound_of_cdprGeneric (P : Loop) (L : List Loop)
    (hg : 2 ≤ L.length + 1) (hGeneric : CDPRGeneric (P :: L)) :
    ∀ (i : ℕ) (hi : i < (P :: L).length),
      ((P :: L).length : ℤ) - (i : ℤ) <
        (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ) := by
  have hk := (cdprGeneric_iff (P :: L)).mp hGeneric
  intro i hi
  have h1 := hk _ (List.get_mem (P :: L) ⟨i, hi⟩)
  have hilt : i < (P :: L).length := hi
  simp only [List.length_cons] at h1 hilt ⊢
  have hnat : L.length + 1 - i < ((P :: L).get ⟨i, hi⟩).torsionOrder := by omega
  have hcast : ((L.length + 1 - i : ℕ) : ℤ) = ((L.length : ℤ) + 1) - (i : ℤ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  calc ((L.length : ℤ) + 1) - (i : ℤ) = ((L.length + 1 - i : ℕ) : ℤ) := hcast.symm
    _ < _ := by exact_mod_cast hnat

/-! ## CDPR Theorem 1.1 -/

/-- The sharp unmarked statement actually proved: a chain of loops whose
torsion orders satisfy the Corollary 6.16(2) budget is Brill--Noether
general.  Only `min(i+1, g-i) < k_i` is required, which is far weaker than
CDPR's genericity. -/
theorem brillNoetherGeneral_chainOfLoops (P : Loop) (L : List Loop)
    (hBudget : ∀ (i : ℕ) (hi : i < (P :: L).length),
      min ((i : ℤ) + 1) (((P :: L).length : ℤ) - (i : ℤ)) <
        (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ)) :
    BrillNoetherGeneral (chainGraph P L) := by
  have hmin := chainMinBudget_of_torsion P L hBudget
  rw [List.map_cons] at hmin
  exact brillNoetherGeneral_mixedTorsionChain_of_minBudget
    P.factor (L.map Loop.factor) hmin

/-- **CDPR Theorem 1.1(1)**, discrete form.  A chain of `g` loops with
generic positive integer arc lengths carries no divisor of degree `d` and
rank at least `r` when the Brill--Noether number is negative. -/
theorem cdpr_nonexistence (P : Loop) (L : List Loop)
    (hg : 2 ≤ L.length + 1) (hGeneric : CDPRGeneric (P :: L))
    (r d : ℤ) (hr : 0 ≤ r) (hrho : bnNumber (chainGraph P L) r d < 0) :
    ¬ BNExists (chainGraph P L) r d := by
  intro hExists
  have hBN := brillNoetherGeneral_chainOfLoops P L
    (torsion_bounds_of_cdprGeneric P L hg hGeneric).1
  exact absurd (hBN r d hr hExists) (not_le.mpr hrho)

/-- CDPR's Brill--Noether number `ρ(g,r,d) = g - (r+1)(g-d+r)` for a chain of
`g` loops, written out.  Bridges `bnNumber` to the paper's `ρ`. -/
theorem bnNumber_chainGraph (P : Loop) (L : List Loop) (r d : ℤ) :
    bnNumber (chainGraph P L) r d =
      ((L.length : ℤ) + 1) - (r + 1) * (((L.length : ℤ) + 1) - d + r) := by
  rw [bnNumber, rectangleWidth, genus_chainGraph]

/-- The sharp once-marked statement: a chain of loops whose torsion orders
satisfy the Corollary 6.16(1) prefix budget `i + 1 < k_i` is once-marked
Brill--Noether general at its right-hand mark `v_g`. -/
theorem onceMarkedBrillNoetherGeneral_chainOfLoops (P : Loop) (L : List Loop)
    (hBudget : ∀ (i : ℕ) (hi : i < (P :: L).length),
      (i : ℤ) + 1 < (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ)) :
    OnceMarkedBrillNoetherGeneral (chainGraph P L) (chainMarked P L).right := by
  have hHead : genus P.factor.marked.graph < (P.factor.period : ℤ) := by
    have h0 := hBudget 0 (by simp)
    simpa using h0
  exact onceMarkedBrillNoetherGeneral_mixedTorsionChain
    P.factor (L.map Loop.factor) hHead (chainPrefixBudget_of_torsion P L hBudget)

/-! ## The pointed counting lemma

The bridge from the repository's Young-diagram formulation of once-marked
Brill--Noether generality to CDPR's "no divisor contains `m v`" phrasing.
This is the one piece of new mathematics in the campaign; it is the
summation of `Bananas/Wedge/OnceMarkedWedgeGenerality.lean:340-398` with the
`i = 0` row strengthened by the extra vanishing hypothesis. -/

universe u

/-- Pointed rank thresholds grow by at least one per row. -/
private theorem pointedRankThreshold_add_le
    (G : CFGraph.{u}) (hG : graphConnected G) (D : CFDiv G) (v : G.V)
    (i j : ℕ) (hij : i ≤ j) :
    pointedRankThreshold G hG D v i + ((j : ℤ) - (i : ℤ)) ≤
      pointedRankThreshold G hG D v j := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hstep := pointedRankThreshold_succ_le G hG D v n
      push_cast at ih ⊢
      omega

/-- **L8.**  If `D` has rank at least `r` and `D - m v` is still effective in
the sense of having nonnegative rank, then the first `r + 1` rows of the
Weierstrass diagram of `(D, v)` already contain
`(r+1)(g - deg D + r) + (m - r)` cells.

The `r + 1` rows are bounded below by the Brill--Noether rectangle width
`g - deg D + r`, exactly as in Proposition 6.14; the extra `m - r` comes from
the zeroth row, whose threshold is pushed down to `-m` by the vanishing
hypothesis. -/
theorem finitePointedDiagram_card_ge_of_vanishing
    (G : CFGraph.{u}) (hG : graphConnected G) (D : CFDiv G) (v : G.V)
    (r : ℕ) (m : ℤ)
    (hrank : (r : ℤ) ≤ rank G D)
    (hm : 0 ≤ rank G (D - m • oneChip v)) :
    ((r : ℤ) + 1) * (genus G - deg D + (r : ℤ)) + (m - (r : ℤ)) ≤
      ((finitePointedDiagram G hG D v r).card : ℤ) := by
  -- The `r`-th threshold is at most `0`, so the `i`-th is at most `i - r`.
  have hTop : pointedRankThreshold G hG D v r ≤ 0 := by
    apply pointedRankThreshold_le_of_rank_ge G hG D v r 0
    simpa using hrank
  have hStep : ∀ i : ℕ, i ≤ r →
      pointedRankThreshold G hG D v i ≤ (i : ℤ) - (r : ℤ) := by
    intro i hi
    have hmono := pointedRankThreshold_add_le G hG D v i r hi
    omega
  -- The vanishing hypothesis pushes the zeroth threshold down to `-m`.
  have hZero : pointedRankThreshold G hG D v 0 ≤ -m := by
    apply pointedRankThreshold_le_of_rank_ge G hG D v 0 (-m)
    have hrw : D + (-m) • oneChip v = D - m • oneChip v := by
      funext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        neg_mul]
      ring
    rw [hrw]
    simpa using hm
  -- Row lengths.  `Int.self_le_toNat` makes the truncation harmless.
  have hRawRow : ∀ i : ℕ,
      (i : ℤ) + genus G - deg D - pointedRankThreshold G hG D v i ≤
        (pointedRowLength G hG D v i : ℤ) := by
    intro i
    exact Int.self_le_toNat _
  have hRow : ∀ i : ℕ, i ≤ r →
      genus G - deg D + (r : ℤ) ≤ (pointedRowLength G hG D v i : ℤ) := by
    intro i hi
    have h1 := hStep i hi
    have h2 := hRawRow i
    omega
  have hRow0 : genus G - deg D + m ≤ (pointedRowLength G hG D v 0 : ℤ) := by
    have h2 := hRawRow 0
    simp only [Nat.cast_zero, zero_add] at h2
    omega
  -- Sum the rows.
  rw [finitePointedDiagram_card, finitePointedRows, List.sum_ofFn]
  rw [Nat.cast_sum, Fin.sum_univ_succ]
  have hTail : (r : ℤ) * (genus G - deg D + (r : ℤ)) ≤
      ∑ i : Fin r, (pointedRowLength G hG D v ((i.succ : Fin (r + 1)) : ℕ) : ℤ) := by
    have hle := Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin r)))
      (f := fun _ : Fin r => genus G - deg D + (r : ℤ))
      (g := fun i : Fin r =>
        (pointedRowLength G hG D v ((i.succ : Fin (r + 1)) : ℕ) : ℤ))
      (fun i _ => hRow _ (by have := i.isLt; simp only [Fin.val_succ]; omega))
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hle
  have hHead : genus G - deg D + m ≤
      (pointedRowLength G hG D v ((0 : Fin (r + 1)) : ℕ) : ℤ) := by
    simpa using hRow0
  have : ((r : ℤ) + 1) * (genus G - deg D + (r : ℤ)) + (m - (r : ℤ))
      = (genus G - deg D + m) + (r : ℤ) * (genus G - deg D + (r : ℤ)) := by
    ring
  rw [this]
  exact add_le_add hHead hTail

/-- The counting lemma, packaged for use: on a once-marked Brill--Noether
general pointed graph, no divisor of rank at least `r` vanishes to order
`r + ρ + 1` at the mark.

This is the graph-theoretic content of CDPR Theorem 1.1(2); the chain of
loops enters only through `hOM`. -/
theorem rank_sub_high_multiplicity_neg
    (G : CFGraph.{u}) (hG : graphConnected G) (v : G.V)
    (hOM : OnceMarkedBrillNoetherGeneral G v)
    (D : CFDiv G) (r : ℤ) (hr : 0 ≤ r) (hrank : r ≤ rank G D) :
    rank G (D - (r + bnNumber G r (deg D) + 1) • oneChip v) < 0 := by
  by_contra hcon
  have hL8 := finitePointedDiagram_card_ge_of_vanishing G hG D v r.toNat
    (r + bnNumber G r (deg D) + 1)
    (by rwa [Int.toNat_of_nonneg hr]) (not_lt.mp hcon)
  have hCard := hOM _ (finitePointedDiagram_censusContains G hG D v r.toNat)
  rw [Int.toNat_of_nonneg hr] at hL8
  have hbn : bnNumber G r (deg D)
      = genus G - (r + 1) * (genus G - deg D + r) := rfl
  linarith

/-- The same, transported along a graph isomorphism: it is enough for the
*image* of the mark to be once-marked Brill--Noether general. -/
theorem rank_sub_high_multiplicity_neg_of_iso
    {G : CFGraph.{u}} {H : CFGraph.{v}} (phi : CFGraphIso G H)
    (hG : graphConnected G) (v : G.V)
    (hOM : OnceMarkedBrillNoetherGeneral H (phi.vertexEquiv v))
    (D : CFDiv G) (r : ℤ) (hr : 0 ≤ r) (hrank : r ≤ rank G D) :
    rank G (D - (r + bnNumber G r (deg D) + 1) • oneChip v) < 0 := by
  have hkey := rank_sub_high_multiplicity_neg H (phi.graph_connected_map hG)
    (phi.vertexEquiv v) hOM (phi.mapDiv D) r hr
    (by rw [phi.rank_mapDiv]; exact hrank)
  rw [phi.deg_mapDiv] at hkey
  have hbn : bnNumber H r (deg D) = bnNumber G r (deg D) := by
    simp only [bnNumber, rectangleWidth, phi.genus_eq]
  rw [hbn] at hkey
  rw [← phi.rank_mapDiv]
  have hmap : phi.mapDiv (D - (r + bnNumber G r (deg D) + 1) • oneChip v)
      = phi.mapDiv D - (r + bnNumber G r (deg D) + 1) •
        oneChip (phi.vertexEquiv v) := by
    rw [map_sub, map_zsmul, CFGraphIso.mapDiv_one_chip]
  rw [hmap]
  exact hkey
/-- **CDPR Theorem 1.1(2)**, discrete form, at the chain's right-hand mark
`v_g`.  When `ρ ≥ 0` no divisor of degree `d` and rank at least `r` contains
`(r + ρ + 1) v_g`.

CDPR state this at `v_0`; see `cdpr_no_high_multiplicity_left`.

`hrbound` is CDPR's own standing range restriction (Notation 4.2, via
`d ≤ 2g - 2` and Clifford) and is kept in the statement for faithfulness; the
row estimate of `finitePointedDiagram_card_ge_of_vanishing` turned out not to
need it, since the `r + 1` rows it sums exist for every `r`. -/
theorem cdpr_no_high_multiplicity (P : Loop) (L : List Loop)
    (hg : 2 ≤ L.length + 1) (hGeneric : CDPRGeneric (P :: L))
    (D : CFDiv (chainGraph P L)) (r d : ℤ) (hr : 0 ≤ r)
    (hrbound : r < genus (chainGraph P L))
    (hdeg : deg D = d) (hrank : rank (chainGraph P L) D ≥ r)
    (hrho : 0 ≤ bnNumber (chainGraph P L) r d) :
    rank (chainGraph P L)
        (D - (r + bnNumber (chainGraph P L) r d + 1) •
          (oneChip (chainMarked P L).right : CFDiv (chainGraph P L))) < 0 := by
  subst hdeg
  exact rank_sub_high_multiplicity_neg (chainGraph P L)
    (graph_connected_chainGraph P L) (chainMarked P L).right
    (onceMarkedBrillNoetherGeneral_chainOfLoops P L
      (torsion_bounds_of_cdprGeneric P L hg hGeneric).2)
    D r hr hrank

/-- Once-marked Brill--Noether generality at the chain's *left* mark `v_0`,
obtained from the suffix budget through the reversed presentation of the
chain and its isomorphism to the canonical one.

Stated as membership of `v_0`'s image under `reversedFactorChainIso`, which
is the form `rank_sub_high_multiplicity_neg_of_iso` consumes. -/
theorem onceMarkedBrillNoetherGeneral_chainOfLoops_left
    (P : Loop) (L : List Loop)
    (hBudget : ∀ (i : ℕ) (hi : i < (P :: L).length),
      ((P :: L).length : ℤ) - (i : ℤ) <
        (((P :: L).get ⟨i, hi⟩).torsionOrder : ℤ)) :
    OnceMarkedBrillNoetherGeneral
      (reversedMarkedChain P.factor (L.map Loop.factor)).graph
      ((reversedFactorChainIso P.factor (L.map Loop.factor)).vertexEquiv
        (chainMarked P L).left) := by
  have hmark : (reversedFactorChainIso P.factor (L.map Loop.factor)).vertexEquiv
      (chainMarked P L).left
      = (reversedMarkedChain P.factor (L.map Loop.factor)).right :=
    reversedFactorChainIso_apply_left P.factor (L.map Loop.factor)
  rw [hmark]
  exact onceMarkedBrillNoetherGeneral_reversedMixedTorsionChain
    P.factor (L.map Loop.factor) (chainSuffixBudget_of_torsion P L hBudget)
/-- **CDPR Theorem 1.1(2)** at `v_0`, CDPR's own marked point.

The marked chain theorem concludes at the chain's *right* mark under the
prefix budget; CDPR state part (2) at the left end.  The transport is through
the reversed (outside-in) presentation `Bananas.reversedMarkedChain`, which is
once-marked general at its right mark under the *suffix* budget
`g - i < k_i`, and whose isomorphism `Bananas.reversedFactorChainIso` to the
canonical chain carries `v_0` to that mark.  Under CDPR genericity both
budgets hold, so the orientation costs nothing -- but it is not optional:
testing at `v_0` under the prefix budget is false (blueprint section 6.4). -/
theorem cdpr_no_high_multiplicity_left (P : Loop) (L : List Loop)
    (hg : 2 ≤ L.length + 1) (hGeneric : CDPRGeneric (P :: L))
    (D : CFDiv (chainGraph P L)) (r d : ℤ) (hr : 0 ≤ r)
    (hrbound : r < genus (chainGraph P L))
    (hdeg : deg D = d) (hrank : rank (chainGraph P L) D ≥ r)
    (hrho : 0 ≤ bnNumber (chainGraph P L) r d) :
    rank (chainGraph P L)
        (D - (r + bnNumber (chainGraph P L) r d + 1) •
          (oneChip (chainMarked P L).left : CFDiv (chainGraph P L))) < 0 := by
  subst hdeg
  exact rank_sub_high_multiplicity_neg_of_iso
    (reversedFactorChainIso P.factor (L.map Loop.factor))
    (graph_connected_chainGraph P L) (chainMarked P L).left
    (onceMarkedBrillNoetherGeneral_chainOfLoops_left P L
      (torsion_suffix_bound_of_cdprGeneric P L hg hGeneric))
    D r hr hrank

end ChainOfLoops
