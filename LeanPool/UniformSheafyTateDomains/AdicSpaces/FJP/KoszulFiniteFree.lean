/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# The finite free Koszul complex in all exterior degrees

For a commutative ring `R` and a sequence `r : Fin m → R` we realise the Koszul complex
`K(r₁, …, r_m)` concretely: the degree-`q` term is the free module of rank `m.choose q`
of functions on `KoszulIndex m q` (the `q`-element subsets of `Fin m`), and the
differential `koszulDifferential r q : KoszulTerm R m (q+1) →ₗ[R] KoszulTerm R m q` is
the signed deletion/insertion formula

`(d x)_J = ∑_{i ∉ J} (-1) ^ #{j ∈ J | j < i} * r i * x_{insert i J}`.

The sign `(-1) ^ #{j ∈ J | j < i}` is the position at which `i` is inserted into the
increasing enumeration of `J`, so this is the standard exterior-algebra convention
`d(e_{i₁} ∧ ⋯ ∧ e_{i_p}) = ∑_k (-1)^(k-1) r_{i_k} · e_{i₁} ∧ ⋯ ∧ ê_{i_k} ∧ ⋯ ∧ e_{i_p}`
(indices increasing).  In degrees `0` and `1` this matches the concrete graph–Koszul
differentials `d1`/`d2` of `FiniteJetGraphKoszul.lean` (with the [FJP] p.10 sign
`d₂(e_i ∧ e_j) = r_i e_j − r_j e_i` for `i < j`); the conjugation lemmas live there,
next to `d1`/`d2`.

## Main declarations

* `KoszulIndex m q`, `KoszulTerm R m q` — index type and free degree-`q` term, with
  `Fintype`/`DecidableEq` instances and the degenerate cases `q > m` (empty), `q = 0`
  (unique: `∅`), `q = m` (unique: `univ`).
* `koszulDifferential r q` with unfolding equation `koszulDifferential_apply`.
* `koszulDifferential_comp` : `d ∘ d = 0`.  Sign argument: expanding twice gives a sum
  over ordered pairs of fresh insertions; the two insertion orders of an unordered pair
  `{i, j}` (`j < i`) produce the sign products `(-1)^{#J<i} · (-1)^{#J<j}` and
  `(-1)^{#J<j} · (-1)^{#J<i + 1}` — inserting the smaller `j` first bumps the count of
  elements below `i` by exactly one (`card_filter_lt_insert_of_lt`) while inserting `i`
  first leaves the count below `j` unchanged (`card_filter_lt_insert_of_not_lt`) — so
  the pairs cancel by the involution `(i, j) ↦ (j, i)`.
* `koszulDifferential_map` (naturality along a ring hom, coefficientwise),
  `koszulDifferential_smul_sequence` (`r ↦ c * r` rescales `d` by `c`),
  `koszulDifferential_continuous` (product topologies over a topological ring),
  `koszulDifferential_zero` (`r = 0`), `koszulDifferential_eq_zero_of_le` and
  `koszulDifferential_fin_zero` (degenerate degrees/`m = 0`).
* `koszulTermZeroEquiv : KoszulTerm R m 0 ≃ₗ[R] R` and
  `koszulTermOneEquiv : KoszulTerm R m 1 ≃ₗ[R] (Fin m → R)` — degree identifications.

This file is deliberately **mathlib-only** (no project imports); see the FJP → CDVF
campaign crosswalk, decisions D3 and D4.  Positive-degree exactness of the coordinate
and graph sequences is ticket K4 and is *not* stated here.
-/

namespace FiniteJet.KoszulFree

/-! ### The index model: `q`-element subsets of `Fin m` -/

/-- Exterior-degree-`q` Koszul index: a `q`-element subset of `Fin m`.  There are
`m.choose q` of these.  A reducible definition, so that `DecidableEq` and `Fintype`
are inherited from the subtype-of-`Fintype` instances. -/
abbrev KoszulIndex (m q : ℕ) : Type :=
  {I : Finset (Fin m) // I.card = q}

namespace KoszulIndex

example (m q : ℕ) : DecidableEq (KoszulIndex m q) := inferInstance
example (m q : ℕ) : Fintype (KoszulIndex m q) := inferInstance

/-- Degenerate case `q > m`: there are no `q`-element subsets of `Fin m`. -/
theorem isEmpty_of_lt {m q : ℕ} (h : m < q) : IsEmpty (KoszulIndex m q) := by
  refine ⟨fun J => absurd ?_ (not_le.mpr h)⟩
  rw [← J.2]
  exact (Finset.card_le_univ J.1).trans_eq (Fintype.card_fin m)

instance (q : ℕ) : IsEmpty (KoszulIndex 0 (q + 1)) :=
  isEmpty_of_lt q.succ_pos

/-- Degenerate case `q = 0`: the empty set is the unique `0`-element subset. -/
instance (m : ℕ) : Unique (KoszulIndex m 0) where
  default := ⟨∅, Finset.card_empty⟩
  uniq J := Subtype.ext (Finset.card_eq_zero.mp J.2)

/-- Degenerate case `q = m`: an `m`-element subset of `Fin m` is all of it. -/
theorem val_eq_univ {m : ℕ} (J : KoszulIndex m m) : J.1 = Finset.univ :=
  Finset.eq_univ_of_card J.1 (J.2.trans (Fintype.card_fin m).symm)

/-- Degenerate case `q = m`: `univ` is the unique `m`-element subset of `Fin m`. -/
instance (m : ℕ) : Unique (KoszulIndex m m) where
  default := ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]⟩
  uniq J := Subtype.ext (val_eq_univ J)

end KoszulIndex

/-- The degree-`q` term of the finite free Koszul complex: the free `R`-module of rank
`m.choose q`, realised as functions on `q`-element subsets with the pointwise module
structure. -/
abbrev KoszulTerm (R : Type*) (m q : ℕ) :=
  KoszulIndex m q → R

/-- Degenerate case: the degree-`q` term is trivial for `q > m` (in particular all of
`KoszulTerm R 0 (q + 1)` for `m = 0`). -/
theorem koszulTerm_subsingleton_of_lt (R : Type*) {m q : ℕ} (h : m < q) :
    Subsingleton (KoszulTerm R m q) :=
  haveI := KoszulIndex.isEmpty_of_lt h
  inferInstance

/-- Index congruence for Koszul terms: transport an application along an equality of the
underlying subsets (the two membership proofs are irrelevant). -/
theorem koszulTerm_index_congr {R : Type*} {m q : ℕ} (x : KoszulTerm R m q)
    {s t : Finset (Fin m)} (hst : s = t) (hs : s.card = q) :
    x ⟨s, hs⟩ = x ⟨t, hst ▸ hs⟩ := by
  cases hst; rfl

/-! ### The differential -/

section Differential

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The Koszul differential in the subset model, by signed deletion/insertion:
`(d x)_J = ∑_{i ∉ J} (-1) ^ #{j ∈ J | j < i} * r i * x_{insert i J}` (summands with
`i ∈ J` are `0`).  The sign is the insertion position of `i` in the increasing
enumeration of `J`. -/
def koszulDifferential (r : Fin m → R) (q : ℕ) :
    KoszulTerm R m (q + 1) →ₗ[R] KoszulTerm R m q :=
  LinearMap.pi fun J =>
    ∑ i, if hi : i ∈ J.1 then 0 else
      ((-1 : R) ^ (J.1.filter (· < i)).card * r i) •
        LinearMap.proj ⟨insert i J.1, by rw [Finset.card_insert_of_notMem hi, J.2]⟩

/-- The unfolding equation for `koszulDifferential`. -/
theorem koszulDifferential_apply (r : Fin m → R) (q : ℕ) (x : KoszulTerm R m (q + 1))
    (J : KoszulIndex m q) :
    koszulDifferential r q x J =
      ∑ i, if hi : i ∈ J.1 then 0 else
        (-1 : R) ^ (J.1.filter (· < i)).card *
          (r i * x ⟨insert i J.1, by rw [Finset.card_insert_of_notMem hi, J.2]⟩) := by
  simp only [koszulDifferential, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ J.1
  · rw [dif_pos hi, dif_pos hi, LinearMap.zero_apply]
  · rw [dif_neg hi, dif_neg hi, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
      mul_assoc]

/-! ### `d ∘ d = 0`

The heart of the file.  Expanding the twice-iterated differential at `J` gives a double
sum over ordered pairs `(i, j)` of fresh insertions; `pairTerm` is the `(i, j)`-summand.
For `j < i` both fresh, the two insertion orders reach the same index `insert j
(insert i J) = insert i (insert j J)` with sign products differing by exactly one factor
`(-1)`: inserting the smaller element `j` first bumps `#{· < i}` by one, while inserting
`i` first leaves `#{· < j}` unchanged.  The involution `(i, j) ↦ (j, i)` therefore
cancels the whole sum. -/

/-- Inserting a fresh smaller element `j < i` bumps the count of elements below `i` by
one. -/
theorem card_filter_lt_insert_of_lt {J : Finset (Fin m)} {i j : Fin m} (hji : j < i)
    (hj : j ∉ J) :
    ((insert j J).filter (· < i)).card = (J.filter (· < i)).card + 1 := by
  rw [Finset.filter_insert, if_pos hji,
    Finset.card_insert_of_notMem fun h => hj (Finset.mem_of_mem_filter j h)]

/-- Inserting an element `i` that is not below `j` leaves the count of elements below
`j` unchanged. -/
theorem card_filter_lt_insert_of_not_lt {J : Finset (Fin m)} {i j : Fin m}
    (hij : ¬i < j) :
    ((insert i J).filter (· < j)).card = (J.filter (· < j)).card := by
  rw [Finset.filter_insert, if_neg hij]

/-- The `(i, j)`-summand of the twice-iterated Koszul differential at `J`: first insert
`i` into `J`, then `j`. -/
private def pairTerm (r : Fin m → R) (q : ℕ) (x : KoszulTerm R m (q + 1 + 1))
    (J : KoszulIndex m q) (i j : Fin m) : R :=
  if hi : i ∈ J.1 then 0
  else if hj : j ∈ insert i J.1 then 0
  else (-1 : R) ^ (J.1.filter (· < i)).card *
    (r i * ((-1 : R) ^ ((insert i J.1).filter (· < j)).card *
      (r j * x ⟨insert j (insert i J.1), by
        rw [Finset.card_insert_of_notMem hj, Finset.card_insert_of_notMem hi, J.2]⟩)))

private theorem comp_apply_eq_sum_pairTerm (r : Fin m → R) (q : ℕ)
    (x : KoszulTerm R m (q + 1 + 1)) (J : KoszulIndex m q) :
    koszulDifferential r q (koszulDifferential r (q + 1) x) J =
      ∑ i, ∑ j, pairTerm r q x J i j := by
  simp only [koszulDifferential_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ J.1
  · rw [dif_pos hi]
    exact (Finset.sum_eq_zero fun j _ => by simp only [pairTerm]; rw [dif_pos hi]).symm
  · rw [dif_neg hi, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pairTerm]
    rw [dif_neg hi]
    by_cases hj : j ∈ insert i J.1
    · rw [dif_pos hj, dif_pos hj, mul_zero, mul_zero]
    · rw [dif_neg hj, dif_neg hj]

private theorem pairTerm_self (r : Fin m → R) (q : ℕ) (x : KoszulTerm R m (q + 1 + 1))
    (J : KoszulIndex m q) (i : Fin m) : pairTerm r q x J i i = 0 := by
  simp only [pairTerm]
  by_cases hi : i ∈ J.1
  · rw [dif_pos hi]
  · rw [dif_neg hi, dif_pos (Finset.mem_insert_self i J.1)]

/-- The ordered-case cancellation: for `j < i` both outside `J`, the `(i, j)`- and
`(j, i)`-summands carry opposite signs. -/
private theorem pairTerm_add_swap_of_lt {r : Fin m → R} {q : ℕ}
    {x : KoszulTerm R m (q + 1 + 1)} {J : KoszulIndex m q} {i j : Fin m} (hji : j < i)
    (hi : i ∉ J.1) (hj : j ∉ J.1) :
    pairTerm r q x J i j + pairTerm r q x J j i = 0 := by
  have hj' : j ∉ insert i J.1 := fun hmem => by
    rcases Finset.mem_insert.mp hmem with rfl | h
    · exact lt_irrefl j hji
    · exact hj h
  have hi' : i ∉ insert j J.1 := fun hmem => by
    rcases Finset.mem_insert.mp hmem with rfl | h
    · exact lt_irrefl i hji
    · exact hi h
  simp only [pairTerm]
  rw [dif_neg hi, dif_neg hj', dif_neg hj, dif_neg hi',
    koszulTerm_index_congr x (Finset.insert_comm i j J.1),
    card_filter_lt_insert_of_not_lt hji.asymm, card_filter_lt_insert_of_lt hji hj,
    pow_succ]
  ring

private theorem pairTerm_add_swap (r : Fin m → R) (q : ℕ) (x : KoszulTerm R m (q + 1 + 1))
    (J : KoszulIndex m q) (i j : Fin m) :
    pairTerm r q x J i j + pairTerm r q x J j i = 0 := by
  by_cases hi : i ∈ J.1
  · have h1 : pairTerm r q x J i j = 0 := by simp only [pairTerm]; rw [dif_pos hi]
    have h2 : pairTerm r q x J j i = 0 := by
      simp only [pairTerm]
      by_cases hj : j ∈ J.1
      · rw [dif_pos hj]
      · rw [dif_neg hj, dif_pos (Finset.mem_insert_of_mem hi)]
    rw [h1, h2, add_zero]
  · by_cases hj : j ∈ J.1
    · have h1 : pairTerm r q x J i j = 0 := by
        simp only [pairTerm]
        rw [dif_neg hi, dif_pos (Finset.mem_insert_of_mem hj)]
      have h2 : pairTerm r q x J j i = 0 := by simp only [pairTerm]; rw [dif_pos hj]
      rw [h1, h2, add_zero]
    · rcases lt_trichotomy i j with hij | rfl | hji
      · rw [add_comm]
        exact pairTerm_add_swap_of_lt hij hj hi
      · rw [pairTerm_self, add_zero]
      · exact pairTerm_add_swap_of_lt hji hi hj

/-- `d ∘ d = 0` for the subset-model Koszul differential.  The two insertion orders of
an unordered pair of fresh indices produce opposite signs (see the section header), so
the double sum cancels under the involution `(i, j) ↦ (j, i)`. -/
theorem koszulDifferential_comp (r : Fin m → R) (q : ℕ) :
    (koszulDifferential r q).comp (koszulDifferential r (q + 1)) = 0 := by
  refine LinearMap.ext fun x => funext fun J => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  rw [comp_apply_eq_sum_pairTerm, ← Fintype.sum_prod_type']
  exact Finset.sum_involution (fun p _ => p.swap)
    (fun p _ => pairTerm_add_swap r q x J p.1 p.2)
    (fun p _ hp hswap => hp (by
      have h21 : p.2 = p.1 := congrArg Prod.fst hswap
      rw [h21]
      exact pairTerm_self r q x J p.1))
    (fun p _ => Finset.mem_univ _)
    (fun p _ => Prod.swap_swap p)

/-- Applied form of `koszulDifferential_comp`. -/
theorem koszulDifferential_koszulDifferential (r : Fin m → R) (q : ℕ)
    (x : KoszulTerm R m (q + 1 + 1)) :
    koszulDifferential r q (koszulDifferential r (q + 1) x) = 0 := by
  have := congrArg (fun f => f x) (koszulDifferential_comp r q)
  simpa using this

/-! ### Foundational API -/

/-- Naturality of the Koszul differential along a ring homomorphism, applied
coefficientwise.  In degrees `0`/`1` this specialises to `d1_map`/`d2_map` of
`FiniteJetGraphKoszul.lean`. -/
theorem koszulDifferential_map {S : Type*} [CommRing S] (φ : R →+* S) (r : Fin m → R)
    (q : ℕ) (x : KoszulTerm R m (q + 1)) (J : KoszulIndex m q) :
    φ (koszulDifferential r q x J) =
      koszulDifferential (fun i => φ (r i)) q (fun K => φ (x K)) J := by
  simp only [koszulDifferential_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ J.1
  · simp only [dif_pos hi, map_zero]
  · simp only [dif_neg hi, map_mul, map_pow, map_neg, map_one]

/-- Rescaling the sequence rescales the differential: every summand contains exactly one
`r`-factor. -/
theorem koszulDifferential_smul_sequence (c : R) (r : Fin m → R) (q : ℕ)
    (x : KoszulTerm R m (q + 1)) :
    koszulDifferential (fun i => c * r i) q x = c • koszulDifferential r q x := by
  funext J
  simp only [koszulDifferential_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ J.1
  · rw [dif_pos hi, dif_pos hi, mul_zero]
  · rw [dif_neg hi, dif_neg hi]
    ring

/-- The differential of the zero sequence is zero. -/
theorem koszulDifferential_zero (q : ℕ) :
    koszulDifferential (0 : Fin m → R) q = 0 := by
  refine LinearMap.ext fun x => funext fun J => ?_
  simp only [koszulDifferential_apply, LinearMap.zero_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i ∈ J.1
  · rw [dif_pos hi]
  · rw [dif_neg hi, zero_mul, mul_zero]

/-- Degenerate degrees: for `q ≥ m` the source `KoszulTerm R m (q + 1)` is a
subsingleton, so the differential is the zero map. -/
theorem koszulDifferential_eq_zero_of_le (r : Fin m → R) {q : ℕ} (h : m ≤ q) :
    koszulDifferential r q = 0 := by
  let := KoszulIndex.isEmpty_of_lt (Nat.lt_succ_of_le h)
  refine LinearMap.ext fun x => ?_
  rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- Degenerate case `m = 0`: every differential is zero. -/
theorem koszulDifferential_fin_zero (r : Fin 0 → R) (q : ℕ) :
    koszulDifferential r q = 0 :=
  koszulDifferential_eq_zero_of_le r (Nat.zero_le q)

/-- Over a topological ring, the Koszul differential is continuous for the product
topologies: each coordinate is a finite sum of continuous coordinate multiplications. -/
theorem koszulDifferential_continuous [TopologicalSpace R] [IsTopologicalRing R]
    (r : Fin m → R) (q : ℕ) : Continuous (koszulDifferential r q) := by
  refine continuous_pi fun J => ?_
  simp only [koszulDifferential_apply]
  refine continuous_finsetSum _ fun i _ => ?_
  by_cases hi : i ∈ J.1
  · simp only [dif_pos hi]
    exact continuous_const
  · simp only [dif_neg hi]
    exact ((continuous_apply _).const_mul _).const_mul _

end Differential

/-! ### Degree identifications -/

section Equivs

variable {R : Type*} [CommRing R] {m : ℕ}

/-- Degree `0`: evaluation at the empty index is a linear equivalence
`KoszulTerm R m 0 ≃ₗ[R] R`. -/
def koszulTermZeroEquiv : KoszulTerm R m 0 ≃ₗ[R] R :=
  LinearEquiv.funUnique (KoszulIndex m 0) R R

@[simp] theorem koszulTermZeroEquiv_apply (x : KoszulTerm R m 0) :
    koszulTermZeroEquiv x = x ⟨∅, Finset.card_empty⟩ :=
  rfl

/-- The singletons are exactly the `1`-element subsets: `Fin m ≃ KoszulIndex m 1`. -/
def KoszulIndex.singletonEquiv (m : ℕ) : Fin m ≃ KoszulIndex m 1 where
  toFun i := ⟨{i}, Finset.card_singleton i⟩
  invFun J := J.1.min' (Finset.card_pos.mp (by rw [J.2]; exact Nat.one_pos))
  left_inv i := Finset.min'_singleton i
  right_inv J := Subtype.ext (Finset.eq_of_subset_of_card_le
    (Finset.singleton_subset_iff.mpr (Finset.min'_mem _ _))
    ((J.2.trans (Finset.card_singleton _).symm).le))

/-- Degree `1`: singleton indexing is a linear equivalence
`KoszulTerm R m 1 ≃ₗ[R] (Fin m → R)`. -/
def koszulTermOneEquiv : KoszulTerm R m 1 ≃ₗ[R] (Fin m → R) :=
  LinearEquiv.funCongrLeft R R (KoszulIndex.singletonEquiv m)

@[simp] theorem koszulTermOneEquiv_apply (x : KoszulTerm R m 1) (i : Fin m) :
    koszulTermOneEquiv x i = x ⟨{i}, Finset.card_singleton i⟩ :=
  rfl

end Equivs

/-! ### Sign tests

Small-`m` checks that the displayed signs come out as in the exterior-algebra
convention `d(e_i ∧ e_j) = r_i e_j − r_j e_i` (`i < j`). -/

section SignExamples

variable {R : Type*} [CommRing R]

/-- `m = 2`, degree 0: `d₁`-shape `x ↦ r₀ x₍₀₎ + r₁ x₍₁₎`. -/
example (r : Fin 2 → R) (x : KoszulTerm R 2 1) :
    koszulTermZeroEquiv (koszulDifferential r 0 x) =
      r 0 * x ⟨{0}, Finset.card_singleton 0⟩ + r 1 * x ⟨{1}, Finset.card_singleton 1⟩ := by
  rw [koszulTermZeroEquiv_apply]
  simp only [koszulDifferential_apply]
  rw [Fin.sum_univ_two, dif_neg (Finset.notMem_empty 0), dif_neg (Finset.notMem_empty 1)]
  simp [Finset.filter_empty]

/-- `m = 2`, degree 1, coefficient of `e₀` in `d(c · e₀∧e₁)`: the sign is `−r₁`. -/
example (r : Fin 2 → R) (c : R) :
    koszulTermOneEquiv (koszulDifferential r 1 fun _ => c) 0 = -(r 1 * c) := by
  rw [koszulTermOneEquiv_apply]
  simp only [koszulDifferential_apply]
  rw [Fin.sum_univ_two, dif_pos (Finset.mem_singleton_self 0),
    dif_neg (Finset.notMem_singleton.mpr (by decide : (1 : Fin 2) ≠ 0))]
  simp [Finset.filter_singleton]

/-- `m = 2`, degree 1, coefficient of `e₁` in `d(c · e₀∧e₁)`: the sign is `+r₀`. -/
example (r : Fin 2 → R) (c : R) :
    koszulTermOneEquiv (koszulDifferential r 1 fun _ => c) 1 = r 0 * c := by
  rw [koszulTermOneEquiv_apply]
  simp only [koszulDifferential_apply]
  rw [Fin.sum_univ_two, dif_pos (Finset.mem_singleton_self 1),
    dif_neg (Finset.notMem_singleton.mpr (by decide : (0 : Fin 2) ≠ 1))]
  simp [Finset.filter_singleton]

/-- `m = 3`, degree 1, evaluated at `{1}`: `d(e_i ∧ e_j) = r_i e_j − r_j e_i` reads
`(d x)_{{1}} = r₀ x_{{0,1}} − r₂ x_{{1,2}}` — the smaller partner enters positively,
the larger one negatively. -/
example (r : Fin 3 → R) (x : KoszulTerm R 3 2) :
    koszulTermOneEquiv (koszulDifferential r 1 x) 1 =
      r 0 * x ⟨{0, 1}, by decide⟩ - r 2 * x ⟨{1, 2}, by decide⟩ := by
  rw [koszulTermOneEquiv_apply]
  simp only [koszulDifferential_apply]
  rw [Fin.sum_univ_three,
    dif_neg (Finset.notMem_singleton.mpr (by decide : (0 : Fin 3) ≠ 1)),
    dif_pos (Finset.mem_singleton_self 1),
    dif_neg (Finset.notMem_singleton.mpr (by decide : (2 : Fin 3) ≠ 1)),
    koszulTerm_index_congr x (by decide : (insert 2 {1} : Finset (Fin 3)) = {1, 2}),
    show (({1} : Finset (Fin 3)).filter (· < 0)).card = 0 by decide,
    show (({1} : Finset (Fin 3)).filter (· < 2)).card = 1 by decide,
    pow_zero, pow_one]
  ring

end SignExamples

end FiniteJet.KoszulFree
