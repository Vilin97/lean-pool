/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.KoszulFiniteFree
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Strict graph–Koszul exactness in degrees ≤ 2 ([FJP] Lemma 4.2)

Source: [FJP] Lemma 4.2 (verbatim statement): "Let `D` be an affinoid k-algebra, possibly
nonreduced, and let `g, f₁, …, f_m ∈ D` generate the unit ideal. Put `P_D = D⟨T₁,…,T_m⟩`,
`r_i = gT_i − f_i`. For `m ≥ 1`, the Koszul complex `K_{P_D}(r₁,…,r_m)` is strictly exact in
positive degrees. Moreover, every differential has closed image and is strict onto that
image. In particular, `I_D = im(d₁) ⊂ P_D` is closed and `d₁ : P_D^m ↠ I_D` is strict."

Design (DD6, `plan.md`): mathlib has no Koszul complexes, and the downstream consumer
([FJP] Lemma 4.3) uses only exterior degrees ≤ 2 — (4.7) `d₁`-lifting with constant and
(4.8) `d₂`-lifting onto `ker d₁` with constant. We therefore state everything concretely:
`d₁ u = ∑ uᵢ rᵢ` on `m`-tuples and `d₂` on strictly-ordered pairs with the [FJP] p.10 sign
convention `d₂(e_i ∧ e_j) = r_i e_j − r_j e_i`.

Proof architecture (mirrors [FJP]'s proof exactly):
1. polynomial level over any commutative ring: coordinate-sequence syzygies are
   Koszul-generated (elementary induction); translation `T ↦ T + a` and unit scaling
   transport this to `(gT_i − f_i)` over `D[T]_g`; the two-case prime-local argument plus
   `Submodule.eq_top_of_localization_maximal` globalises ("the localization of every positive
   Koszul homology module at every prime … is zero; hence each such homology module is
   zero" — degrees ≤ 1 form);
2. `P_D ≅ (D₀[T])^∧_ϖ[1/ϖ]` for a noetherian ring of definition `D₀` ([FJP] (4.4)); the base
   change `D[T] → P_D` is **flat** (mathlib `AdicCompletion.flat_of_isNoetherian` = Stacks
   00MB + localisation), and only *positive-degree* exactness transfers ([FJP]: "Notice that
   `g, f_i` need not lie in `D₀`, because exactness was established before completion" —
   and `H₀` genuinely changes: `r` can become a unit in `D⟨T⟩`);
3. strictness/closedness over the noetherian `P_D` via the finite-module theory
   (`NoetherianTateModules.lean`, Wedhorn 6.18 = the Huber [4, Lemma 2.4(ii)] citation) and
   the Banach open mapping theorem with constants
   (`ContinuousLinearMap.exists_preimage_norm_le`).
-/

open Filter Topology

namespace FiniteJet

namespace GraphKoszul

/-! ### The concrete differentials -/

section Differentials

variable {S : Type*} [CommRing S] {m : ℕ}

/-- Index type for exterior degree 2: strictly ordered pairs. -/
abbrev Pairs (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

/-- `d₁ u = ∑ᵢ uᵢ rᵢ` — the first graph–Koszul differential. -/
def d1 (r : Fin m → S) (u : Fin m → S) : S := ∑ i, u i * r i

/-- `d₂` on ordered pairs, with the [FJP] p.10 sign convention
`d₂(e_i ∧ e_j) = r_i e_j − r_j e_i` for `i < j`:
`(d₂ v)_j = ∑_{i<j} v_{ij} r_i − ∑_{k>j} v_{jk} r_k`. -/
def d2 (r : Fin m → S) (v : Pairs m → S) : Fin m → S := fun j =>
  (∑ i, if h : i < j then v ⟨(i, j), h⟩ * r i else 0) -
    ∑ k, if h : j < k then v ⟨(j, k), h⟩ * r k else 0

/-- `d₁ ∘ d₂ = 0` (the Koszul relations are syzygies). -/
theorem d1_d2 (r : Fin m → S) (v : Pairs m → S) : d1 r (d2 r v) = 0 := by
  unfold d1 d2
  simp only [sub_mul, Finset.sum_mul]
  rw [Finset.sum_sub_distrib, sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a < b
  · rw [dif_pos hab, dif_pos hab, mul_right_comm]
  · rw [dif_neg hab, dif_neg hab, zero_mul, zero_mul]

theorem d1_map {T : Type*} [CommRing T] (φ : S →+* T) (r : Fin m → S) (u : Fin m → S) :
    φ (d1 r u) = d1 (fun i => φ (r i)) (fun i => φ (u i)) := by
  unfold d1
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_mul φ _ _

theorem d2_map {T : Type*} [CommRing T] (φ : S →+* T) (r : Fin m → S) (v : Pairs m → S)
    (j : Fin m) :
    φ (d2 r v j) = d2 (fun i => φ (r i)) (fun p => φ (v p)) j := by
  unfold d2
  rw [map_sub, map_sum, map_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · by_cases hij : i < j
    · rw [dif_pos hij, dif_pos hij, map_mul]
    · rw [dif_neg hij, dif_neg hij, map_zero]
  · by_cases hij : j < i
    · rw [dif_pos hij, dif_pos hij, map_mul]
    · rw [dif_neg hij, dif_neg hij, map_zero]

theorem d2_smul (r : Fin m → S) (c : S) (v : Pairs m → S) (j : Fin m) :
    d2 r (fun p => c * v p) j = c * d2 r v j := by
  unfold d2
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · by_cases hij : i < j
    · rw [dif_pos hij, dif_pos hij, mul_assoc]
    · rw [dif_neg hij, dif_neg hij, mul_zero]
  · by_cases hij : j < i
    · rw [dif_pos hij, dif_pos hij, mul_assoc]
    · rw [dif_neg hij, dif_neg hij, mul_zero]

/-- Scaling the sequence by a unit rescales the wedge inversely. -/
theorem d2_unit_scale {c : S} (hc : IsUnit c) (ρ : Fin m → S) (v : Pairs m → S) (j : Fin m) :
    d2 (fun i => c * ρ i) (fun p => (hc.unit⁻¹ : Sˣ) * v p) j = d2 ρ v j := by
  unfold d2
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · by_cases hij : i < j
    · rw [dif_pos hij, dif_pos hij, mul_mul_mul_comm, mul_comm ((hc.unit⁻¹ : Sˣ) : S) c,
        IsUnit.mul_val_inv, one_mul]
    · rw [dif_neg hij, dif_neg hij]
  · by_cases hij : j < i
    · rw [dif_pos hij, dif_pos hij, mul_mul_mul_comm, mul_comm ((hc.unit⁻¹ : Sˣ) : S) c,
        IsUnit.mul_val_inv, one_mul]
    · rw [dif_neg hij, dif_neg hij]

theorem d2_zero (r : Fin m → S) (j : Fin m) : d2 r (fun _ => (0 : S)) j = 0 := by
  unfold d2
  dsimp only
  have h1 : (∑ i, if h : i < j then (0 : S) * r i else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      by_cases hij : i < j
      · rw [dif_pos hij, zero_mul]
      · rw [dif_neg hij]
  have h2 : (∑ i, if h : j < i then (0 : S) * r i else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      by_cases hij : j < i
      · rw [dif_pos hij, zero_mul]
      · rw [dif_neg hij]
  rw [h1, h2, sub_zero]

theorem d2_add (r : Fin m → S) (v w : Pairs m → S) (j : Fin m) :
    d2 r (fun p => v p + w p) j = d2 r v j + d2 r w j := by
  unfold d2
  dsimp only
  rw [sub_add_sub_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : i < j
    · rw [dif_pos hij, dif_pos hij, dif_pos hij, add_mul]
    · rw [dif_neg hij, dif_neg hij, dif_neg hij, add_zero]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : j < i
    · rw [dif_pos hij, dif_pos hij, dif_pos hij, add_mul]
    · rw [dif_neg hij, dif_neg hij, dif_neg hij, add_zero]

theorem d2_sum {ι : Type*} (s : Finset ι) (r : Fin m → S) (c : ι → S)
    (v : ι → Pairs m → S) (j : Fin m) :
    d2 r (fun p => ∑ i ∈ s, c i * v i p) j = ∑ i ∈ s, c i * d2 r (v i) j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact d2_zero r j
  | insert a s ha ih =>
    have hfun : (fun p => ∑ i ∈ insert a s, c i * v i p) =
        fun p => (c a * v a p) + ∑ i ∈ s, c i * v i p :=
      funext fun p => Finset.sum_insert ha
    rw [hfun, d2_add, d2_smul, ih, Finset.sum_insert ha]

/-- The contractibility case: multiplying a syzygy by any one `rᵢ` lands it in the Koszul
image, explicitly ([FJP] Lemma 4.2: "At a prime not containing every `rᵢ`, one generator is
a unit and the localized Koszul complex is contractible"). -/
theorem d2_koszul_single (r : Fin m → S) (u : Fin m → S) (h : d1 r u = 0) (i : Fin m) :
    d2 r (fun p => if p.1.2 = i then -u p.1.1 else if p.1.1 = i then u p.1.2 else 0) =
      fun k => r i * u k := by
  classical
  funext k
  unfold d2
  dsimp only
  rcases lt_trichotomy k i with hki | heq | hik
  · -- `k < i`: only the `(k,i)` wedge contributes, through the second sum
    have hs1 : (∑ a, if h : a < k then
        (if k = i then -u a else if a = i then u k else 0) * r a else 0) = 0 :=
      Finset.sum_eq_zero fun a _ => by
        by_cases hak : a < k
        · rw [dif_pos hak, if_neg (Fin.ne_of_lt hki), if_neg (Fin.ne_of_lt (hak.trans hki)),
            zero_mul]
        · rw [dif_neg hak]
    have hs2 : (∑ b, if h : k < b then
        (if b = i then -u k else if k = i then u b else 0) * r b else 0) = -u k * r i := by
      rw [Finset.sum_eq_single i (fun b _ hb => ?_) (fun hb => absurd (Finset.mem_univ i) hb)]
      · rw [dif_pos hki, if_pos rfl]
      · by_cases hkb : k < b
        · rw [dif_pos hkb, if_neg hb, if_neg (Fin.ne_of_lt hki), zero_mul]
        · rw [dif_neg hkb]
    rw [hs1, hs2, zero_sub, neg_mul, neg_neg, mul_comm]
  · -- `k = i`: the row collects `-∑_{j≠i} uⱼ rⱼ = uᵢ rᵢ`
    rw [heq]
    have hsum := h
    unfold d1 at hsum
    have hsplit : ∀ j : Fin m, u j * r j =
        (if j < i then u j * r j else 0) + ((if j = i then u j * r j else 0) +
          (if i < j then u j * r j else 0)) := fun j => by
      rcases lt_trichotomy j i with h1 | rfl | h1
      · rw [if_pos h1, if_neg (Fin.ne_of_lt h1), if_neg (asymm h1), add_zero, add_zero]
      · simp
      · rw [if_neg (asymm h1), if_neg (Fin.ne_of_gt h1), if_pos h1, zero_add, zero_add]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i (fun j => u j * r j),
      if_pos (Finset.mem_univ i)] at hsum
    have h1 : (∑ a, if h : a < i then
        (if i = i then -u a else if a = i then u i else 0) * r a else 0) =
        -∑ j, if j < i then u j * r j else 0 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hai : a < i
      · rw [dif_pos hai, if_pos rfl, if_pos hai, neg_mul]
      · rw [dif_neg hai, if_neg hai, neg_zero]
    have h2 : (∑ b, if h : i < b then
        (if b = i then -u i else if i = i then u b else 0) * r b else 0) =
        ∑ j, if i < j then u j * r j else 0 := by
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hib : i < b
      · rw [dif_pos hib, if_neg (Fin.ne_of_gt hib), if_pos rfl, if_pos hib]
      · rw [dif_neg hib, if_neg hib]
    rw [h1, h2, mul_comm (r i) (u i)]
    linear_combination -hsum
  · -- `i < k`: only the `(i,k)` wedge contributes, through the first sum
    have hs1 : (∑ a, if h : a < k then
        (if k = i then -u a else if a = i then u k else 0) * r a else 0) = u k * r i := by
      rw [Finset.sum_eq_single i (fun a _ ha => ?_) (fun ha => absurd (Finset.mem_univ i) ha)]
      · rw [dif_pos hik, if_neg (Fin.ne_of_gt hik), if_pos rfl]
      · by_cases hak : a < k
        · rw [dif_pos hak, if_neg (Fin.ne_of_gt hik), if_neg ha, zero_mul]
        · rw [dif_neg hak]
    have hs2 : (∑ b, if h : k < b then
        (if b = i then -u k else if k = i then u b else 0) * r b else 0) = 0 :=
      Finset.sum_eq_zero fun b _ => by
        by_cases hkb : k < b
        · rw [dif_pos hkb, if_neg (Fin.ne_of_gt (hik.trans hkb)), if_neg (Fin.ne_of_gt hik),
            zero_mul]
        · rw [dif_neg hkb]
    rw [hs1, hs2, sub_zero, mul_comm]

end Differentials

/-! ### Conjugation to the all-degree finite-free Koszul model

`KoszulFiniteFree.lean` (namespace `FiniteJet.KoszulFree`) implements the Koszul complex
of `r₁, …, r_m` in every exterior degree on the subset model
`KoszulIndex m q = {I : Finset (Fin m) // I.card = q}`, with the insertion-position sign
`(-1) ^ #{j ∈ J | j < i}`.  The two theorems below are the **sign check** promised by the
FJP → CDVF campaign crosswalk (decision D3): under the canonical degree-`0`/`1`/`2`
identifications `KoszulTerm S m 0 ≃ₗ[S] S`, `KoszulTerm S m 1 ≃ₗ[S] (Fin m → S)` and
`KoszulTerm S m 2 ≃ₗ[S] (Pairs m → S)`, the subset-model differentials in degrees `0` and
`1` are EXACTLY `d1` and `d2` above — for `q = 1` the subset-model formula reads
`(d x)_{{k}} = ∑_{i<k} r_i x_{{i,k}} − ∑_{i>k} r_i x_{{k,i}}`, matching the [FJP] p.10
convention `d₂(e_i ∧ e_j) = r_i e_j − r_j e_i` for `i < j`.  The statements of
`d1`/`d2`/`d1_d2` are untouched. -/

section KoszulFreeConjugation

open KoszulFree

variable {S : Type*} [CommRing S] {m : ℕ}

private theorem min'_pair {a b : Fin m} (hab : a < b)
    (H : ({a, b} : Finset (Fin m)).Nonempty) : ({a, b} : Finset (Fin m)).min' H = a :=
  le_antisymm (Finset.min'_le _ a (Finset.mem_insert_self a {b}))
    (Finset.le_min' _ _ a fun y hy => by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact le_rfl
      · exact hab.le.trans_eq (Finset.mem_singleton.mp hy).symm)

private theorem max'_pair {a b : Fin m} (hab : a < b)
    (H : ({a, b} : Finset (Fin m)).Nonempty) : ({a, b} : Finset (Fin m)).max' H = b :=
  le_antisymm
    (Finset.max'_le _ _ b fun y hy => by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hab.le
      · exact (Finset.mem_singleton.mp hy).le)
    (Finset.le_max' _ b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))

/-- Strictly ordered pairs are exactly the two-element subsets of `Fin m`. -/
def pairsEquivKoszulIndexTwo (m : ℕ) : Pairs m ≃ KoszulIndex m 2 where
  toFun p := ⟨{p.1.1, p.1.2}, Finset.card_pair_eq_two_iff.mpr p.2.ne⟩
  invFun J :=
    ⟨(J.1.min' (Finset.card_pos.mp (by rw [J.2]; exact Nat.zero_lt_two)),
      J.1.max' (Finset.card_pos.mp (by rw [J.2]; exact Nat.zero_lt_two))),
      Finset.min'_lt_max'_of_card _ (by rw [J.2]; exact Nat.one_lt_two)⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact min'_pair p.2 (Finset.insert_nonempty _ _)
    · exact max'_pair p.2 (Finset.insert_nonempty _ _)
  right_inv J := by
    obtain ⟨a, b, hab, hJ⟩ := Finset.card_eq_two.mp J.2
    refine Subtype.ext ?_
    rcases lt_or_gt_of_ne hab with h | h
    · simp only [hJ]
      rw [min'_pair h, max'_pair h]
    · rw [Finset.pair_comm] at hJ
      simp only [hJ]
      rw [min'_pair h, max'_pair h]

/-- Degree `2`: ordered-pair indexing is a linear equivalence
`KoszulTerm S m 2 ≃ₗ[S] (Pairs m → S)`. -/
def koszulTermTwoEquiv : KoszulTerm S m 2 ≃ₗ[S] (Pairs m → S) :=
  LinearEquiv.funCongrLeft S S (pairsEquivKoszulIndexTwo m)

@[simp] theorem koszulTermTwoEquiv_apply (x : KoszulTerm S m 2) (p : Pairs m) :
    koszulTermTwoEquiv x p =
      x ⟨{p.1.1, p.1.2}, Finset.card_pair_eq_two_iff.mpr p.2.ne⟩ :=
  rfl

/-- SIGN CHECK, degree 0: under the degree-`0`/`1` identifications, the subset-model
Koszul differential `koszulDifferential r 0` is exactly `d1`. -/
theorem koszulDifferential_zero_eq_d1 (r : Fin m → S) (x : KoszulTerm S m 1) :
    koszulTermZeroEquiv (koszulDifferential r 0 x) = d1 r (koszulTermOneEquiv x) := by
  rw [koszulTermZeroEquiv_apply]
  simp only [koszulDifferential_apply]
  unfold d1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_neg (Finset.notMem_empty i), koszulTermOneEquiv_apply]
  simp only [Finset.filter_empty, Finset.card_empty, pow_zero, one_mul]
  exact mul_comm _ _

/-- SIGN CHECK, degree 1: under the degree-`1`/`2` identifications, the subset-model
Koszul differential `koszulDifferential r 1` is exactly `d2` with the [FJP] p.10
convention `d₂(e_i ∧ e_j) = r_i e_j − r_j e_i` for `i < j`: the subset-model formula
`(d x)_{{j}} = ∑_{i<j} r_i x_{{i,j}} − ∑_{i>j} r_i x_{{j,i}}` matches summand by
summand. -/
theorem koszulDifferential_one_eq_d2 (r : Fin m → S) (x : KoszulTerm S m 2) (j : Fin m) :
    koszulTermOneEquiv (koszulDifferential r 1 x) j = d2 r (koszulTermTwoEquiv x) j := by
  rw [koszulTermOneEquiv_apply]
  simp only [koszulDifferential_apply]
  unfold d2
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases lt_trichotomy i j with hij | rfl | hji
  · -- `i < j`: positive sign, wedge `{i, j}` read through the first `d2`-sum
    rw [dif_neg (Finset.notMem_singleton.mpr hij.ne), dif_pos hij, dif_neg (asymm hij),
      sub_zero]
    simp only [Finset.filter_singleton, if_neg (asymm hij), Finset.card_empty, pow_zero,
      one_mul, koszulTermTwoEquiv_apply]
    exact mul_comm _ _
  · -- `i = j`: both sides vanish (the two identical `i < i` dites rewrite in one step)
    rw [dif_pos (Finset.mem_singleton_self i), dif_neg (lt_irrefl i), sub_zero]
  · -- `j < i`: negative sign, wedge `{j, i}` read through the second `d2`-sum
    rw [dif_neg (Finset.notMem_singleton.mpr hji.ne'), dif_neg (asymm hji), dif_pos hji,
      zero_sub]
    simp only [Finset.filter_singleton, if_pos hji, Finset.card_singleton, pow_one,
      koszulTermTwoEquiv_apply, neg_one_mul]
    rw [mul_comm (r i)]
    exact congrArg (fun y => -(y * r i)) (congrArg x (Subtype.ext (Finset.pair_comm i j)))

end KoszulFreeConjugation

/-! ### Polynomial level: syzygies of the graph sequence are Koszul-generated

[FJP] Lemma 4.2, proof (verbatim): "First work over `D[T₁,…,T_m]`. At a prime not containing
every `r_i`, one generator is a unit and the localized Koszul complex is contractible. At a
prime containing all `r_i`, choose `1 = a₀g + ∑ a_i f_i`. … Thus `g` is a unit in that local
ring … Over `D_g`, translation by the tuple `(f_i/g)_i` identifies `(T_i − f_i/g)_i` with the
coordinate sequence `(T_i)_i`. The coordinate sequence is regular over an arbitrary
coefficient ring … The polynomial Koszul complex is therefore exact in positive degrees, even
when `D` is nonreduced. Indeed, the localization of every positive Koszul homology module at
every prime of `D[T₁,…,T_m]` is zero by the two cases above; hence each such homology module
is zero." -/

section Polynomial

variable {D : Type*} [CommRing D] {m : ℕ}

open MvPolynomial in
/-- Coordinate-sequence syzygies over an arbitrary base are Koszul-generated (the elementary
multidegree induction; [FJP]: "The coordinate sequence is regular over an arbitrary
coefficient ring"). -/
theorem syzygy_coordinate (u : Fin m → MvPolynomial (Fin m) D)
    (h : d1 (fun i => (X i : MvPolynomial (Fin m) D)) u = 0) :
    ∃ v, d2 (fun i => (X i : MvPolynomial (Fin m) D)) v = u := by
  classical
  induction m with
  | zero => exact ⟨fun p => 0, funext fun i => i.elim0⟩
  | succ m ih =>
    set e := MvPolynomial.finSuccEquiv D m with he
    set U : Fin (m + 1) → Polynomial (MvPolynomial (Fin m) D) := fun i => e (u i) with hUdef
    -- the relation in `A[y]`, `y := X 0`
    have hrel : U 0 * Polynomial.X +
        ∑ i : Fin m, U i.succ * Polynomial.C (X i) = 0 := by
      have h0 := congrArg e h
      rw [map_zero] at h0
      rw [← h0]
      unfold d1
      rw [map_sum, Fin.sum_univ_succ]
      congr 1
      · rw [map_mul, MvPolynomial.finSuccEquiv_X_zero]
      · exact Finset.sum_congr rfl fun i _ => by
          rw [map_mul, MvPolynomial.finSuccEquiv_X_succ]
    -- reduction mod `y`: the constant coefficients form a coordinate syzygy over `Fin m`
    set a : Fin m → MvPolynomial (Fin m) D := fun i => (U i.succ).coeff 0 with hadef
    have hared : d1 (fun i => (X i : MvPolynomial (Fin m) D)) a = 0 := by
      have hc := congrArg (fun p : Polynomial (MvPolynomial (Fin m) D) => p.coeff 0) hrel
      simp only [Polynomial.coeff_add, Polynomial.coeff_zero, Polynomial.mul_coeff_zero,
        Polynomial.coeff_X_zero, mul_zero, zero_add, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_zero] at hc
      unfold d1
      exact hc
    obtain ⟨w, hw⟩ := ih a hared
    -- the `divX` decomposition of the positive part
    set Q : Fin m → Polynomial (MvPolynomial (Fin m) D) := fun i => (U i.succ).divX with hQdef
    have hdecomp : ∀ i : Fin m, U i.succ = Polynomial.X * Q i + Polynomial.C (a i) :=
      fun i => (Polynomial.X_mul_divX_add (U i.succ)).symm
    -- cancel `y`: the top coefficient is Koszul-expressed
    have hU0 : U 0 = -∑ i : Fin m, Q i * Polynomial.C (X i) := by
      have hXmul : Polynomial.X *
          (U 0 + ∑ i : Fin m, Q i * Polynomial.C (X i)) = 0 := by
        have hsplit : ∑ i : Fin m, U i.succ * Polynomial.C (X i) =
            Polynomial.X * ∑ i : Fin m, Q i * Polynomial.C (X i) +
              Polynomial.C (d1 (fun i => (X i : MvPolynomial (Fin m) D)) a) := by
          unfold d1
          rw [Finset.mul_sum, map_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hdecomp i, add_mul, map_mul, mul_assoc]
        rw [mul_add, mul_comm Polynomial.X (U 0)]
        have h2 := hrel
        rw [hsplit, hared, map_zero, add_zero] at h2
        exact h2
      have hcancel : U 0 + ∑ i : Fin m, Q i * Polynomial.C (X i) = 0 := by
        refine Polynomial.ext fun n => ?_
        have hcn := congrArg (fun q : Polynomial (MvPolynomial (Fin m) D) =>
          q.coeff (n + 1)) hXmul
        simpa [Polynomial.coeff_X_mul] using hcn
      exact eq_neg_of_add_eq_zero_left hcancel
    -- assemble the wedge
    have hp2ne : ∀ p : Pairs (m + 1), p.1.2 ≠ 0 := fun p =>
      Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le _) p.2)
    refine ⟨fun p =>
      if h0 : p.1.1 = 0 then e.symm (Q (p.1.2.pred (hp2ne p)))
      else e.symm (Polynomial.C (w ⟨(p.1.1.pred h0, p.1.2.pred (hp2ne p)),
        (Fin.pred_lt_pred_iff (ha := h0) (hb := hp2ne p)).mpr p.2⟩)), ?_⟩
    funext j
    refine Fin.cases ?_ ?_ j
    · -- component 0: `-∑ₖ v₀ₖ Xₖ = u 0` is exactly the `y`-cofactor identity `hU0`
      unfold d2
      simp only [Fin.not_lt_zero, Fin.sum_univ_succ, lt_irrefl, Fin.succ_pos, dif_pos,
        Fin.pred_succ]
      simp only [dif_neg not_false, Finset.sum_const_zero, zero_add, zero_sub]
      have hU0' : e (u 0) = -∑ i : Fin m, Q i * Polynomial.C (X i) := hU0
      apply e.injective
      rw [map_neg, map_sum, hU0', neg_inj]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_mul, AlgEquiv.apply_symm_apply, MvPolynomial.finSuccEquiv_X_succ]
    · -- component `j.succ`: the `divX` decomposition plus the IH wedge
      intro j
      unfold d2
      simp only [Fin.sum_univ_succ, Fin.succ_pos, dif_pos, Fin.not_lt_zero,
        Fin.succ_lt_succ_iff, Fin.succ_ne_zero, Fin.pred_succ]
      apply e.injective
      have hUj : e (u j.succ) = Polynomial.X * Q j +
          Polynomial.C (d2 (fun i => (X i : MvPolynomial (Fin m) D)) w j) := by
        rw [hw]
        exact hdecomp j
      rw [hUj]
      unfold d2
      have heX0 : e (X 0) = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
      have heXs : ∀ i : Fin m, e (X i.succ) = Polynomial.C (X i) := fun i =>
        MvPolynomial.finSuccEquiv_X_succ
      simp only [dif_neg not_false, zero_add, map_sub, map_add, map_sum, map_mul,
        AlgEquiv.apply_symm_apply, apply_dite e, apply_dite Polynomial.C, map_zero, heX0,
        heXs]
      ring

open MvPolynomial in
/-- Denominator clearing for the polynomial base change into `D_g`: every polynomial over
the localization is a `(C g)`-power multiple of a polynomial over `D` ([FJP] Lemma 4.2's
implicit "clear denominators" step). -/
theorem exists_pow_C_mul_eq_map (g : D) (y : MvPolynomial (Fin m) (Localization.Away g)) :
    ∃ (N : ℕ) (x : MvPolynomial (Fin m) D),
      MvPolynomial.map (algebraMap D (Localization.Away g)) x =
        C (algebraMap D (Localization.Away g) g) ^ N * y := by
  induction y using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨⟨d, s⟩, hds⟩ := IsLocalization.surj (Submonoid.powers g) a
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    refine ⟨n, C d, ?_⟩
    rw [MvPolynomial.map_C, ← map_pow, ← map_mul]
    congr 1
    rw [← hds, show ((s : Submonoid.powers g) : D) = g ^ n from hn.symm, map_pow]
    ring
  | add p q hp hq =>
    obtain ⟨Np, xp, hxp⟩ := hp
    obtain ⟨Nq, xq, hxq⟩ := hq
    refine ⟨Np + Nq, C g ^ Nq * xp + C g ^ Np * xq, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, MvPolynomial.map_C, hxp, hxq]
    ring
  | mul_X p i hp =>
    obtain ⟨N, x, hx⟩ := hp
    refine ⟨N, x * X i, ?_⟩
    rw [map_mul, MvPolynomial.map_X, hx]
    ring

open MvPolynomial in
/-- `g`-power torsion detects the kernel of the polynomial base change into `D_g`. -/
theorem exists_pow_C_mul_eq_zero_of_map_eq_zero (g : D) (z : MvPolynomial (Fin m) D)
    (hz : MvPolynomial.map (algebraMap D (Localization.Away g)) z = 0) :
    ∃ M : ℕ, C g ^ M * z = 0 := by
  classical
  have hcoeff : ∀ t : Fin m →₀ ℕ, ∃ n : ℕ, g ^ n * MvPolynomial.coeff t z = 0 := fun t => by
    have h0 : algebraMap D (Localization.Away g) (MvPolynomial.coeff t z) = 0 := by
      rw [← MvPolynomial.coeff_map, hz, MvPolynomial.coeff_zero]
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp h0
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    exact ⟨n, by rw [hn]; exact hs⟩
  choose nf hnf using hcoeff
  refine ⟨z.support.sup nf, ?_⟩
  ext t
  rw [← map_pow, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero]
  by_cases ht : t ∈ z.support
  · have hle : nf t ≤ z.support.sup nf := Finset.le_sup ht
    rw [show z.support.sup nf = (z.support.sup nf - nf t) + nf t by omega, pow_add,
      mul_assoc, hnf t, mul_zero]
  · rw [MvPolynomial.notMem_support_iff.mp ht, mul_zero]

open MvPolynomial in
/-- The translation `Xᵢ ↦ Xᵢ + C (c i)` as an algebra automorphism. -/
noncomputable def translationEquiv (c : Fin m → D) :
    MvPolynomial (Fin m) D ≃ₐ[D] MvPolynomial (Fin m) D :=
  AlgEquiv.ofAlgHom (aeval fun i => X i + C (c i)) (aeval fun i => X i - C (c i))
    (by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, aeval_X, map_sub, aeval_X, aeval_C, AlgHom.id_apply,
        algebraMap_eq]
      ring)
    (by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, aeval_X, map_add, aeval_X, aeval_C, AlgHom.id_apply,
        algebraMap_eq]
      ring)

open MvPolynomial in
theorem translationEquiv_X (c : Fin m → D) (i : Fin m) :
    translationEquiv c (X i) = X i + C (c i) :=
  aeval_X _ i

open MvPolynomial in
theorem translationEquiv_C (c : Fin m → D) (d : D) :
    translationEquiv c (C d) = C d := by
  rw [show translationEquiv c (C d) = aeval (fun i => X i + C (c i)) (C d) from rfl,
    aeval_C, algebraMap_eq]

open MvPolynomial in
/-- The unit-`g` case of [FJP] Lemma 4.2's polynomial layer: translation by `(g⁻¹fᵢ)ᵢ`
identifies the graph sequence with the coordinate sequence, up to the unit `C g`. -/
theorem syzygy_graph_of_isUnit (g : D) (hg : IsUnit g) (f : Fin m → D)
    (u : Fin m → MvPolynomial (Fin m) D)
    (h : d1 (fun i => C g * X i - C (f i)) u = 0) :
    ∃ v, d2 (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D)) v = u := by
  classical
  set c : Fin m → D := fun i => (hg.unit⁻¹ : Dˣ) * f i with hc
  set ρ : Fin m → MvPolynomial (Fin m) D := fun i => X i - C (c i) with hρ
  have hr : ∀ i, (C g * X i - C (f i) : MvPolynomial (Fin m) D) = C g * ρ i := fun i => by
    rw [hρ]
    show _ = C g * (X i - C (c i))
    rw [mul_sub, ← map_mul, hc]
    show _ = C g * X i - C (g * ((hg.unit⁻¹ : Dˣ) * f i))
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hCg : IsUnit (C g : MvPolynomial (Fin m) D) := hg.map C
  have hρsyz : d1 ρ u = 0 := by
    have hfac : d1 (fun i => C g * ρ i) u = C g * d1 ρ u := by
      unfold d1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [show (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D)) = fun i => C g * ρ i
      from funext hr, hfac] at h
    exact hCg.mul_right_eq_zero.mp h
  set α := translationEquiv c with hα
  have hαρ : ∀ i, α (ρ i) = X i := fun i => by
    rw [hρ]
    show α (X i - C (c i)) = X i
    rw [map_sub, hα, translationEquiv_X, translationEquiv_C]
    ring
  have hcoord : d1 (fun i => (X i : MvPolynomial (Fin m) D)) (fun i => α (u i)) = 0 := by
    have h0 := congrArg α hρsyz
    rw [map_zero] at h0
    rw [← h0]
    unfold d1
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hαρ]
  obtain ⟨w, hw⟩ := syzygy_coordinate (fun i => α (u i)) hcoord
  refine ⟨fun p => (hCg.unit⁻¹ : (MvPolynomial (Fin m) D)ˣ) * α.symm (w p), ?_⟩
  funext k
  apply α.injective
  have hpush : α (d2 (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D))
      (fun p => (hCg.unit⁻¹ : (MvPolynomial (Fin m) D)ˣ) * α.symm (w p)) k) =
      d2 (fun i => (X i : MvPolynomial (Fin m) D)) w k := by
    unfold d2
    rw [map_sub, map_sum, map_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
    · by_cases hik : i < k
      · rw [dif_pos hik, dif_pos hik]
        dsimp only
        rw [hr i, map_mul, map_mul, map_mul, AlgEquiv.apply_symm_apply, hαρ,
          mul_mul_mul_comm, ← map_mul, IsUnit.val_inv_mul, map_one, one_mul]
      · rw [dif_neg hik, dif_neg hik, map_zero]
    · by_cases hik : k < i
      · rw [dif_pos hik, dif_pos hik]
        dsimp only
        rw [hr i, map_mul, map_mul, map_mul, AlgEquiv.apply_symm_apply, hαρ,
          mul_mul_mul_comm, ← map_mul, IsUnit.val_inv_mul, map_one, one_mul]
      · rw [dif_neg hik, dif_neg hik, map_zero]
  rw [hpush]
  exact congrFun hw k

open MvPolynomial in
/-- Graph-sequence syzygies over the polynomial ring are Koszul-generated, given that
`(g, f₁, …, f_m)` generate the unit ideal (the two-case localization argument). For `m = 1`
this says `gT − f` is a nonzerodivisor (the pairs type is empty). -/
theorem syzygy_graph_polynomial (g : D) (f : Fin m → D)
    (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (u : Fin m → MvPolynomial (Fin m) D)
    (h : d1 (fun i => C g * X i - C (f i)) u = 0) :
    ∃ v, d2 (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D)) v = u := by
  classical
  set Dg := Localization.Away g with hDg
  set φ : MvPolynomial (Fin m) D →+* MvPolynomial (Fin m) Dg :=
    MvPolynomial.map (algebraMap D Dg) with hφdef
  -- the ideal of Koszul-reachable multipliers of `u`
  set A : Ideal (MvPolynomial (Fin m) D) :=
    { carrier := {a | ∃ v, d2 (fun i => C g * X i - C (f i)) v = fun k => a * u k}
      zero_mem' := ⟨fun _ => 0, funext fun k => by rw [d2_zero, zero_mul]⟩
      add_mem' := by
        rintro a b ⟨va, hva⟩ ⟨vb, hvb⟩
        refine ⟨fun p => va p + vb p, funext fun k => ?_⟩
        rw [d2_add, congrFun hva k, congrFun hvb k, add_mul]
      smul_mem' := by
        rintro b a ⟨va, hva⟩
        refine ⟨fun p => b * va p, funext fun k => ?_⟩
        rw [d2_smul, congrFun hva k, smul_eq_mul, mul_assoc] } with hAdef
  -- each `rᵢ` is reachable (contractibility)
  have hrA : ∀ i, (C g * X i - C (f i) : MvPolynomial (Fin m) D) ∈ A := fun i =>
    ⟨_, d2_koszul_single _ u h i⟩
  -- some power of `C g` is reachable (through `D_g`, translation, and clearing)
  have hgA : ∃ P : ℕ, (C g : MvPolynomial (Fin m) D) ^ P ∈ A := by
    have hg' : IsUnit (algebraMap D Dg g) :=
      IsLocalization.map_units Dg ⟨g, Submonoid.mem_powers g⟩
    have hφr : ∀ i, φ (C g * X i - C (f i)) =
        C (algebraMap D Dg g) * X i - C (algebraMap D Dg (f i)) := fun i => by
      rw [hφdef]
      show MvPolynomial.map _ _ = _
      rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]
    have hsyz' : d1 (fun i => C (algebraMap D Dg g) * X i - C (algebraMap D Dg (f i)))
        (fun i => φ (u i)) = 0 := by
      calc d1 (fun i => C (algebraMap D Dg g) * X i - C (algebraMap D Dg (f i)))
            (fun i => φ (u i))
          = d1 (fun i => φ (C g * X i - C (f i))) (fun i => φ (u i)) := by
            congr 1
            exact funext fun i => (hφr i).symm
        _ = φ (d1 (fun i => C g * X i - C (f i)) u) := (d1_map φ _ u).symm
        _ = 0 := by rw [h, map_zero]
    obtain ⟨v', hv'⟩ := syzygy_graph_of_isUnit (algebraMap D Dg g) hg'
      (fun i => algebraMap D Dg (f i)) (fun i => φ (u i)) hsyz'
    -- uniform denominator over the finite wedge index
    choose Nf xf hxf using fun p : Pairs m => exists_pow_C_mul_eq_map g (v' p)
    set Nmax := Finset.univ.sup Nf with hNmax
    set x' : Pairs m → MvPolynomial (Fin m) D :=
      fun p => C g ^ (Nmax - Nf p) * xf p with hx'def
    have hφx' : ∀ p, φ (x' p) = C (algebraMap D Dg g) ^ Nmax * v' p := fun p => by
      have hle : Nf p ≤ Nmax := Finset.le_sup (Finset.mem_univ p)
      rw [hx'def]
      show φ (C g ^ (Nmax - Nf p) * xf p) = _
      rw [map_mul, map_pow, hφdef]
      show MvPolynomial.map _ (C g) ^ _ * MvPolynomial.map _ (xf p) = _
      rw [MvPolynomial.map_C, hxf p, ← mul_assoc, ← pow_add,
        show Nmax - Nf p + Nf p = Nmax by omega]
    -- the pushed identity vanishes, so its preimage is `g`-power torsion
    have hker : ∀ k, φ (d2 (fun i => C g * X i - C (f i)) x' k - C g ^ Nmax * u k) = 0 :=
      fun k => by
        rw [map_sub, d2_map φ]
        have hcongr : d2 (fun i => φ (C g * X i - C (f i))) (fun p => φ (x' p)) k =
            d2 (fun i => C (algebraMap D Dg g) * X i - C (algebraMap D Dg (f i)))
              (fun p => C (algebraMap D Dg g) ^ Nmax * v' p) k := by
          congr 1
          · exact funext hφr
          · exact funext hφx'
        rw [hcongr, d2_smul, congrFun hv' k, map_mul, map_pow, hφdef]
        show C (algebraMap D Dg g) ^ Nmax * MvPolynomial.map _ (u k) -
          MvPolynomial.map _ (C g) ^ Nmax * MvPolynomial.map _ (u k) = 0
        rw [MvPolynomial.map_C, sub_self]
    choose Mf hMf using fun k =>
      exists_pow_C_mul_eq_zero_of_map_eq_zero g _ (hker k)
    set Mmax := Finset.univ.sup Mf with hMmax
    refine ⟨Mmax + Nmax, fun p => C g ^ Mmax * x' p, funext fun k => ?_⟩
    rw [d2_smul]
    have hle : Mf k ≤ Mmax := Finset.le_sup (Finset.mem_univ k)
    have h0 : C g ^ Mmax * (d2 (fun i => C g * X i - C (f i)) x' k - C g ^ Nmax * u k) = 0 := by
      rw [show Mmax = Mmax - Mf k + Mf k by omega, pow_add, mul_assoc, hMf k, mul_zero]
    rw [mul_sub] at h0
    rw [sub_eq_zero.mp h0, ← mul_assoc, ← pow_add]
  obtain ⟨P, hPA⟩ := hgA
  -- the span of `(C g)^P` and the `rᵢ` is contained in the reachable ideal …
  have hJle : Ideal.span ({(C g : MvPolynomial (Fin m) D) ^ P} ∪
      Set.range (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D))) ≤ A := by
    rw [Ideal.span_le]
    rintro x (hx | ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hPA
    · exact hrA i
  -- … and contains `1` ([FJP] (4.3) plus the quotient-nilpotence argument)
  have h1mem : (1 : D) ∈ Ideal.span ({g} ∪ Set.range f) := by
    rw [hunit]
    exact Submodule.mem_top
  rw [Set.singleton_union, ← Fin.range_cons g f] at h1mem
  obtain ⟨cc, hcc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1mem
  rw [Fin.sum_univ_succ] at hcc
  simp only [Fin.cons_zero, Fin.cons_succ] at hcc
  have hkey : (C g) * (C (cc 0) + ∑ k, C (cc k.succ) * X k) -
      ∑ k, C (cc k.succ) * (C g * X k - C (f k)) = 1 := by
    have h1 : (C (cc 0 * g + ∑ k, cc k.succ * f k) : MvPolynomial (Fin m) D) = 1 := by
      rw [hcc, map_one]
    rw [map_add, map_mul, map_sum] at h1
    simp only [map_mul] at h1
    rw [← h1, mul_add, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib,
      mul_comm (C g) (C (cc 0))]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have h1J : (1 : MvPolynomial (Fin m) D) ∈ Ideal.span
      ({(C g : MvPolynomial (Fin m) D) ^ P} ∪
        Set.range (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D))) := by
    set J := Ideal.span ({(C g : MvPolynomial (Fin m) D) ^ P} ∪
      Set.range (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D))) with hJdef
    have hmkr : ∀ k, Ideal.Quotient.mk J (C g * X k - C (f k)) = 0 := fun k =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_union_right _ ⟨k, rfl⟩))
    have hmk1 : Ideal.Quotient.mk J
        ((C g) * (C (cc 0) + ∑ k, C (cc k.succ) * X k)) = 1 := by
      have hsum0 : (∑ k, Ideal.Quotient.mk J (C (cc k.succ) * (C g * X k - C (f k)))) = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [map_mul, hmkr k, mul_zero]
      have hq := congrArg (Ideal.Quotient.mk J) hkey
      rw [map_one, map_sub, map_sum, hsum0, sub_zero] at hq
      exact hq
    have hq0 : (1 : MvPolynomial (Fin m) D ⧸ J) = 0 := by
      calc (1 : MvPolynomial (Fin m) D ⧸ J)
          = (Ideal.Quotient.mk J ((C g) * (C (cc 0) + ∑ k, C (cc k.succ) * X k))) ^ P := by
            rw [hmk1, one_pow]
        _ = Ideal.Quotient.mk J ((C g) ^ P) *
            Ideal.Quotient.mk J ((C (cc 0) + ∑ k, C (cc k.succ) * X k) ^ P) := by
            rw [← map_pow, ← map_mul, mul_pow]
        _ = 0 := by
            have hmem : ((C g : MvPolynomial (Fin m) D) ^ P) ∈ J :=
              Ideal.subset_span (Set.mem_union_left _ rfl)
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_one]; exact hq0)
  obtain ⟨v, hv⟩ := hJle h1J
  exact ⟨v, by rw [hv]; exact funext fun k => one_mul (u k)⟩

end Polynomial

/-! ### Coefficientwise maps of restricted rings (used here and in the localization layer) -/

section MapHom

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {n : ℕ}

/-- Coefficientwise application of a norm-nonincreasing ring homomorphism to restricted
multivariate power series ([FJP] Lemma 4.1's ambient maps). -/
noncomputable def mapRestricted (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (c : Fin n → ℝ) :
    MvPowerSeries.Restricted R c →+* MvPowerSeries.Restricted S c where
  toFun f := ⟨MvPowerSeries.map φ f.1, by
    show MvPowerSeries.IsRestrictedGauss _ _
    rw [← MvPowerSeries.isRestrictedGauss_abs_iff]
    have hf : MvPowerSeries.IsRestrictedGauss c f.1 := f.2
    rw [← MvPowerSeries.isRestrictedGauss_abs_iff, MvPowerSeries.IsRestrictedGauss] at hf
    rw [MvPowerSeries.IsRestrictedGauss]
    refine squeeze_zero (fun t => mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (abs_nonneg _) _)) (fun t => ?_) hf
    rw [MvPowerSeries.coeff_map]
    exact mul_le_mul_of_nonneg_right (hφ _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (abs_nonneg _) _)⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.map φ))
  map_mul' f g := Subtype.ext (map_mul (MvPowerSeries.map φ) f.1 g.1)
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.map φ))
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.map φ) f.1 g.1)

theorem norm_mapRestricted_le (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (c : Fin n → ℝ)
    [StrongPos c] (f : MvPowerSeries.Restricted R c) :
    ‖mapRestricted φ hφ c f‖ ≤ ‖f‖ := by
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine Real.iSup_le (fun t => ?_) (norm_nonneg f)
  show ‖MvPowerSeries.coeff t (MvPowerSeries.map φ f.1)‖ * _ ≤ _
  rw [MvPowerSeries.coeff_map]
  calc ‖φ (MvPowerSeries.coeff t f.1)‖ * t.prod (c · ^ ·)
      ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·) :=
        mul_le_mul_of_nonneg_right (hφ _)
          (Finset.prod_nonneg fun i _ => pow_nonneg (StrongPos_pos c i).le _)
    _ ≤ ‖f‖ := by
        rw [MvRestricted.norm_eq]
        exact MvPowerSeries.le_gaussNorm _ _ _ (MvRestricted.hasGaussNorm _ f) t

end MapHom

/-! ### Restricted level over an affinoid vertex

Statements are parametrised over a normed vertex `E` with a noetherian unit ball and a
noetherian restricted extension; instantiated at `E ∈ {𝓑, 𝓒, 𝓓}` via
`FiniteJetNoetherianVertices.lean`. `P := E⟨T₁,…,T_m⟩` is the vendored radius-one restricted
ring. -/

section UltrametricBanach

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormOneClass A]
  [CompleteSpace A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Sup norms of tuples scale exactly under a scaling element. -/
theorem pi_norm_scale {c : A} (hc : ∀ x : A, ‖c * x‖ = ‖c‖ * ‖x‖) (u : ι → A) :
    ‖fun i => c * u i‖ = ‖c‖ * ‖u‖ := by
  refine le_antisymm ?_ ?_
  · refine pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg c) (norm_nonneg u)) |>.mpr
      fun i => ?_
    rw [hc]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) (norm_nonneg c)
  · rcases eq_or_ne ‖c‖ 0 with hc0 | hc0
    · rw [hc0, zero_mul]
      exact norm_nonneg _
    · have hcpos : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg c) (Ne.symm hc0)
      have hui : ∀ i, ‖u i‖ ≤ ‖c‖⁻¹ * ‖fun j => c * u j‖ := fun i => by
        rw [le_inv_mul_iff₀ hcpos, ← hc]
        exact norm_le_pi_norm (fun j => c * u j) i
      have hle : ‖u‖ ≤ ‖c‖⁻¹ * ‖fun j => c * u j‖ :=
        pi_norm_le_iff_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg c))
          (norm_nonneg _)) |>.mpr hui
      calc ‖c‖ * ‖u‖ ≤ ‖c‖ * (‖c‖⁻¹ * ‖fun j => c * u j‖) :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg c)
        _ = ‖fun j => c * u j‖ := by
            rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

/-- Ultrametric triangle inequality for sup norms of tuples. -/
theorem pi_norm_add_le_max (u v : ι → A) : ‖u + v‖ ≤ max ‖u‖ ‖v‖ := by
  refine pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg u)) |>.mpr fun i => ?_
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  exact max_le_max (norm_le_pi_norm u i) (norm_le_pi_norm v i)

/-- **Ultrametric Banach open mapping with constants** ([FJP] Lemma 4.2's strictness;
Huber [4, Lemma 2.4(ii)]): a continuous `t`-equivariant additive map between finite tuple
spaces over a complete ultrametric normed ring lifts elements of its closed range with a
uniform norm constant. -/
theorem exists_lift_norm_le_of_closed_range
    {t : A} (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : A, ‖t * x‖ = ‖t‖ * ‖x‖)
    (f : (ι → A) →+ (κ → A)) (hcont : Continuous f)
    (hequiv : ∀ u, f (fun i => t * u i) = fun k => t * f u k)
    (hclosed : IsClosed (Set.range f)) :
    ∃ h : ℝ, 1 ≤ h ∧ ∀ y ∈ Set.range f, ∃ u, f u = y ∧ ‖u‖ ≤ h * ‖y‖ := by
  classical
  -- the closed range as a complete (hence Baire) subgroup
  have hrangeset : (f.range : Set (κ → A)) = Set.range f := AddMonoidHom.coe_range f
  haveI hYcomplete : CompleteSpace ↥(f.range) :=
    (show IsClosed (f.range : Set (κ → A)) by
      rw [hrangeset]; exact hclosed).completeSpace_coe
  -- the closures of the ball images cover the range
  set CN : ℕ → Set ↥(f.range) := fun N =>
    Subtype.val ⁻¹' closure (⇑f '' Metric.closedBall 0 ((‖t‖ ^ N)⁻¹)) with hCN
  have hCNclosed : ∀ N, IsClosed (CN N) := fun N =>
    isClosed_closure.preimage continuous_subtype_val
  have hCNcover : (⋃ N, CN N) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp y.2
    have hex : ∃ N : ℕ, ‖t‖ ^ N * ‖v‖ ≤ 1 := by
      rcases eq_or_ne ‖v‖ 0 with h0 | h0
      · exact ⟨0, by rw [h0, mul_zero]; exact zero_le_one⟩
      · have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm h0)
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) ht1
        exact ⟨N, by
          calc ‖t‖ ^ N * ‖v‖ ≤ ‖v‖⁻¹ * ‖v‖ :=
                mul_le_mul_of_nonneg_right hN.le (norm_nonneg _)
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)⟩
    obtain ⟨N, hN⟩ := hex
    have hvball : v ∈ Metric.closedBall (0 : ι → A) ((‖t‖ ^ N)⁻¹) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hpow : (0 : ℝ) < ‖t‖ ^ N := pow_pos ht0 N
      calc ‖v‖ = (‖t‖ ^ N)⁻¹ * (‖t‖ ^ N * ‖v‖) := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow), one_mul]
        _ ≤ (‖t‖ ^ N)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hN (inv_nonneg.mpr hpow.le)
        _ = (‖t‖ ^ N)⁻¹ := mul_one _
    exact Set.mem_iUnion.mpr ⟨N, subset_closure ⟨v, hvball, hv⟩⟩
  -- Baire: some ball-image closure has interior
  obtain ⟨N, hNne⟩ := nonempty_interior_of_iUnion_of_closed hCNclosed hCNcover
  obtain ⟨y₀, hy₀⟩ := hNne
  set R : ℝ := (‖t‖ ^ N)⁻¹ with hR
  have hRpos : 0 < R := inv_pos.mpr (pow_pos ht0 N)
  -- the closed ball is an additive subgroup (ultrametrically)
  set ballGrp : AddSubgroup (ι → A) :=
    { carrier := Metric.closedBall 0 R
      zero_mem' := Metric.mem_closedBall_self hRpos.le
      add_mem' := fun {u v} hu hv => by
        rw [Metric.mem_closedBall, dist_zero_right] at hu hv ⊢
        exact (pi_norm_add_le_max u v).trans (max_le hu hv)
      neg_mem' := fun {u} hu => by
        rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
        rwa [norm_neg] } with hballGrp
  set Gsub : AddSubgroup (κ → A) := (ballGrp.map f).topologicalClosure with hGsub
  set G' : AddSubgroup ↥(f.range) := Gsub.comap f.range.subtype with hG'
  have hG'eq : (G' : Set ↥(f.range)) = CN N := by
    have hGset : (Gsub : Set (κ → A)) = closure (⇑f '' Metric.closedBall 0 R) := by
      rw [hGsub]
      show closure ((ballGrp.map f : AddSubgroup (κ → A)) : Set (κ → A)) = _
      rw [AddSubgroup.coe_map]
      rfl
    show f.range.subtype ⁻¹' (Gsub : Set (κ → A)) = CN N
    rw [hGset, hCN]
    rfl
  -- the subgroup is open, so it contains a δ-ball
  have hG'open : IsOpen (G' : Set ↥(f.range)) := by
    refine AddSubgroup.isOpen_of_mem_nhds G' (g := y₀) ?_
    rw [hG'eq]
    exact mem_interior_iff_mem_nhds.mp hy₀
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp
    (hG'open.mem_nhds (zero_mem G'))
  have hδkey : ∀ z : κ → A, z ∈ Set.range f → ‖z‖ < δ →
      z ∈ closure (⇑f '' Metric.closedBall 0 R) := by
    intro z hzr hzn
    have hzmem : z ∈ f.range := AddMonoidHom.mem_range.mpr hzr
    have hz' : (⟨z, hzmem⟩ : ↥(f.range)) ∈ Metric.ball (0 : ↥(f.range)) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hzn
    have hmem : (⟨z, hzmem⟩ : ↥(f.range)) ∈ (G' : Set ↥(f.range)) := hδball hz'
    rw [hG'eq] at hmem
    exact hmem
  -- scaling helpers
  set tinv : A := ((htu.unit⁻¹ : Aˣ) : A) with htinv
  have htinvscale : ∀ x : A, ‖tinv * x‖ = ‖t‖⁻¹ * ‖x‖ := fun x => by
    have h1 : ‖t * (tinv * x)‖ = ‖t‖ * ‖tinv * x‖ := hscale _
    rw [← mul_assoc, htinv, IsUnit.mul_val_inv, one_mul] at h1
    rw [eq_inv_mul_iff_mul_eq₀ (ne_of_gt ht0)]
    exact h1.symm
  have hcancel : ∀ x : A, t * (tinv * x) = x := fun x => by
    rw [← mul_assoc, htinv, IsUnit.mul_val_inv, one_mul]
  have hcancel' : ∀ x : A, tinv * (t * x) = x := fun x => by
    rw [← mul_assoc, htinv, IsUnit.val_inv_mul, one_mul]
  have hequivinv : ∀ u, f (fun i => tinv * u i) = fun k => tinv * f u k := fun u => by
    have h1 := hequiv (fun i => tinv * u i)
    have h2 : (fun i => t * (tinv * u i)) = u := funext fun i => hcancel (u i)
    rw [h2] at h1
    funext k
    rw [h1]
    show f (fun i => tinv * u i) k = tinv * (t * f (fun i => tinv * u i) k)
    rw [hcancel']
  have hequiv_pow : ∀ (n : ℕ) (u), f (fun i => t ^ n * u i) = fun k => t ^ n * f u k := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      have hstep : (fun i => t ^ (n + 1) * u i) = fun i => t * (t ^ n * u i) :=
        funext fun i => by ring
      rw [hstep, hequiv, ih u]
      funext k
      show t * (t ^ n * f u k) = t ^ (n + 1) * f u k
      ring
  have hequivinv_pow : ∀ (n : ℕ) (u), f (fun i => tinv ^ n * u i) =
      fun k => tinv ^ n * f u k := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      have hstep : (fun i => tinv ^ (n + 1) * u i) = fun i => tinv * (tinv ^ n * u i) :=
        funext fun i => by ring
      rw [hstep, hequivinv, ih u]
      funext k
      show tinv * (tinv ^ n * f u k) = tinv ^ (n + 1) * f u k
      ring
  have htinvnorm : ‖tinv‖ = ‖t‖⁻¹ := by
    have h := htinvscale 1
    rwa [mul_one, norm_one, mul_one] at h
  have htinvscale' : ∀ x : A, ‖tinv * x‖ = ‖tinv‖ * ‖x‖ := fun x => by
    rw [htinvnorm]
    exact htinvscale x
  have htinvpow : ∀ (n : ℕ) (x : A), ‖tinv ^ n * x‖ = (‖t‖⁻¹) ^ n * ‖x‖ := fun n x => by
    have h := norm_pow_mul_of_scale (E := A) htinvscale' n x
    rwa [htinvnorm] at h
  have htpow : ∀ (n : ℕ) (x : A), ‖t ^ n * x‖ = ‖t‖ ^ n * ‖x‖ := fun n x =>
    norm_pow_mul_of_scale (E := A) hscale n x
  have hpitpow : ∀ (n : ℕ) (u : ι → A), ‖fun i => t ^ n * u i‖ = ‖t‖ ^ n * ‖u‖ := by
    intro n u
    have hnpow : ‖t ^ n‖ = ‖t‖ ^ n := by
      have h := htpow n 1
      rwa [mul_one, norm_one, mul_one] at h
    have hc : ∀ x : A, ‖t ^ n * x‖ = ‖t ^ n‖ * ‖x‖ := fun x => by
      rw [htpow, hnpow]
    rw [pi_norm_scale hc u, hnpow]
  have hpitinvpow : ∀ (n : ℕ) (u : κ → A), ‖fun k => tinv ^ n * u k‖ = (‖t‖⁻¹) ^ n * ‖u‖ := by
    intro n u
    have hnpow : ‖tinv ^ n‖ = (‖t‖⁻¹) ^ n := by
      have h := htinvpow n 1
      rwa [mul_one, norm_one, mul_one] at h
    have hc : ∀ x : A, ‖tinv ^ n * x‖ = ‖tinv ^ n‖ * ‖x‖ := fun x => by
      rw [htinvpow, hnpow]
    rw [pi_norm_scale hc u, hnpow]
  have hpitpowκ : ∀ (n : ℕ) (u : κ → A), ‖fun k => t ^ n * u k‖ = ‖t‖ ^ n * ‖u‖ := by
    intro n u
    have hnpow : ‖t ^ n‖ = ‖t‖ ^ n := by
      have h := htpow n 1
      rwa [mul_one, norm_one, mul_one] at h
    have hc : ∀ x : A, ‖t ^ n * x‖ = ‖t ^ n‖ * ‖x‖ := fun x => by rw [htpow, hnpow]
    rw [pi_norm_scale hc u, hnpow]
  have hpitinvpowι : ∀ (n : ℕ) (u : ι → A),
      ‖fun i => tinv ^ n * u i‖ = (‖t‖⁻¹) ^ n * ‖u‖ := by
    intro n u
    have hnpow : ‖tinv ^ n‖ = (‖t‖⁻¹) ^ n := by
      have h := htinvpow n 1
      rwa [mul_one, norm_one, mul_one] at h
    have hc : ∀ x : A, ‖tinv ^ n * x‖ = ‖tinv ^ n‖ * ‖x‖ := fun x => by
      rw [htinvpow, hnpow]
    rw [pi_norm_scale hc u, hnpow]
  -- the approximation step at scale `k`
  have step : ∀ (k : ℕ) (z : κ → A), z ∈ Set.range f → ‖z‖ < δ * ‖t‖ ^ k →
      ∃ u : ι → A, ‖u‖ ≤ R * ‖t‖ ^ k ∧ (z - f u) ∈ Set.range f ∧
        ‖z - f u‖ < δ * ‖t‖ ^ (k + 1) := by
    intro k z hzr hzn
    set w : κ → A := fun j => tinv ^ k * z j with hw
    have hwr : w ∈ Set.range f := by
      obtain ⟨v, rfl⟩ := hzr
      exact ⟨fun i => tinv ^ k * v i, hequivinv_pow k v⟩
    have hwn : ‖w‖ < δ := by
      rw [hw, hpitinvpow k z, inv_pow, inv_mul_lt_iff₀ (pow_pos ht0 k), mul_comm]
      exact hzn
    obtain ⟨fu₀img, hfu₀mem, hdist⟩ := Metric.mem_closure_iff.mp (hδkey w hwr hwn)
      (δ * ‖t‖) (by positivity)
    obtain ⟨u₀, hu₀ball, rfl⟩ := hfu₀mem
    rw [Metric.mem_closedBall, dist_zero_right] at hu₀ball
    have hz_eq : ∀ j, z j = t ^ k * w j := fun j => by
      rw [hw]
      show z j = t ^ k * (tinv ^ k * z j)
      rw [← mul_assoc, ← mul_pow, htinv, IsUnit.mul_val_inv, one_pow, one_mul]
    refine ⟨fun i => t ^ k * u₀ i, ?_, ?_, ?_⟩
    · rw [hpitpow k u₀]
      calc ‖t‖ ^ k * ‖u₀‖ ≤ ‖t‖ ^ k * R :=
            mul_le_mul_of_nonneg_left hu₀ball (pow_nonneg (norm_nonneg t) k)
        _ = R * ‖t‖ ^ k := mul_comm _ _
    · obtain ⟨v, rfl⟩ := hzr
      refine ⟨fun i => v i - t ^ k * u₀ i, ?_⟩
      rw [show (fun i => v i - t ^ k * u₀ i) = v - fun i => t ^ k * u₀ i from rfl, map_sub]
    · have hdiff : z - f (fun i => t ^ k * u₀ i) = fun j => t ^ k * (w - f u₀) j := by
        funext j
        rw [hequiv_pow k u₀]
        show z j - t ^ k * f u₀ j = t ^ k * (w j - f u₀ j)
        rw [mul_sub, ← hz_eq j]
      rw [hdiff, hpitpowκ k (w - f u₀)]
      have hd : ‖w - f u₀‖ < δ * ‖t‖ := by
        rw [← dist_eq_norm]
        exact hdist
      calc ‖t‖ ^ k * ‖w - f u₀‖ < ‖t‖ ^ k * (δ * ‖t‖) :=
            mul_lt_mul_of_pos_left hd (pow_pos ht0 k)
        _ = δ * ‖t‖ ^ (k + 1) := by ring
  -- geometric correction: δ-small elements of the range lift exactly within `R`
  have key : ∀ y ∈ Set.range f, ‖y‖ < δ → ∃ u : ι → A, f u = y ∧ ‖u‖ ≤ R := by
    intro y hyr hyδ
    let T : ℕ → Type _ := fun k => {z : κ → A // z ∈ Set.range f ∧ ‖z‖ < δ * ‖t‖ ^ k}
    let step' : ∀ k, T k → (ι → A) × T (k + 1) := fun k zk =>
      ⟨(step k zk.1 zk.2.1 zk.2.2).choose,
       ⟨zk.1 - f (step k zk.1 zk.2.1 zk.2.2).choose,
        (step k zk.1 zk.2.1 zk.2.2).choose_spec.2.1,
        (step k zk.1 zk.2.1 zk.2.2).choose_spec.2.2⟩⟩
    let Z : ∀ k, T k := fun k =>
      Nat.rec (⟨y, hyr, by simpa using hyδ⟩ : T 0) (fun k zk => (step' k zk).2) k
    let U : ℕ → ι → A := fun k => (step' k (Z k)).1
    have hUb : ∀ k, ‖U k‖ ≤ R * ‖t‖ ^ k := fun k =>
      (step k (Z k).1 (Z k).2.1 (Z k).2.2).choose_spec.1
    have hZsucc : ∀ k, (Z (k + 1)).1 = (Z k).1 - f (U k) := fun k => rfl
    have hZnorm : ∀ k, ‖(Z k).1‖ < δ * ‖t‖ ^ k := fun k => (Z k).2.2
    have htele : ∀ n, (Z n).1 = y - ∑ k ∈ Finset.range n, f (U k) := by
      intro n
      induction n with
      | zero => simp [show (Z 0).1 = y from rfl]
      | succ n ih =>
        rw [hZsucc n, ih, Finset.sum_range_succ]
        abel
    have hUsummable : Summable U :=
      Summable.of_norm_bounded
        ((summable_geometric_of_lt_one (norm_nonneg t) ht1).mul_left R) hUb
    obtain ⟨US, hUS⟩ := hUsummable
    have hfUS : HasSum (fun k => f (U k)) (f US) := hUS.map f hcont
    have htends1 : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, f (U k))
        Filter.atTop (𝓝 (f US)) := hfUS.tendsto_sum_nat
    have htends2 : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, f (U k))
        Filter.atTop (𝓝 y) := by
      have hz0 : Filter.Tendsto (fun n => (Z n).1) Filter.atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => (hZnorm n).le) ?_
        have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg t) ht1).const_mul δ
        simpa using h
      have heq : (fun n => ∑ k ∈ Finset.range n, f (U k)) = fun n => y - (Z n).1 := by
        funext n
        rw [htele n]
        abel
      rw [heq]
      simpa using tendsto_const_nhds.sub hz0
    have hfy : f US = y := tendsto_nhds_unique htends1 htends2
    have hURb : ∀ k, ‖U k‖ ≤ R := fun k =>
      (hUb k).trans (by
        calc R * ‖t‖ ^ k ≤ R * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg t) ht1.le) hRpos.le
          _ = R := mul_one _)
    have hpartial : ∀ F : Finset ℕ, ‖∑ k ∈ F, U k‖ ≤ R := by
      intro F
      induction F using Finset.induction_on with
      | empty => simpa using hRpos.le
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (pi_norm_add_le_max _ _).trans (max_le (hURb a) ih)
    have hUSnorm : ‖US‖ ≤ R := by
      have hn : Filter.Tendsto (fun F : Finset ℕ => ‖∑ k ∈ F, U k‖)
          Filter.atTop (𝓝 ‖US‖) := (continuous_norm.tendsto US).comp hUS
      exact le_of_tendsto hn (Filter.Eventually.of_forall hpartial)
    exact ⟨US, hfy, hUSnorm⟩
  -- the constant, via the `[δ‖t‖, δ)` window
  refine ⟨max 1 (R / (δ * ‖t‖)), le_max_left _ _, fun y hyr => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · refine ⟨0, map_zero f, ?_⟩
    rw [norm_zero, norm_zero, mul_zero]
  · have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hconst : 0 < R / (δ * ‖t‖) := by positivity
    by_cases hcase : ‖y‖ < δ
    · -- scale up by `tinv`-powers into the window
      have hex : ∃ n : ℕ, δ * ‖t‖ ≤ (‖t‖⁻¹) ^ n * ‖y‖ := by
        obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((δ * ‖t‖) / ‖y‖)
          ((one_lt_inv₀ ht0).mpr ht1)
        exact ⟨n, by
          rw [div_lt_iff₀ hypos] at hn
          exact hn.le⟩
      set n := Nat.find hex with hn
      have hnspec : δ * ‖t‖ ≤ (‖t‖⁻¹) ^ n * ‖y‖ := Nat.find_spec hex
      have hnlt : (‖t‖⁻¹) ^ n * ‖y‖ < δ := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · rw [h0, pow_zero, one_mul]
          exact hcase
        · have hmin := Nat.find_min hex (m := n - 1) (by omega)
          push Not at hmin
          have hstep : ((‖t‖⁻¹) ^ n * ‖y‖) = ‖t‖⁻¹ * ((‖t‖⁻¹) ^ (n - 1) * ‖y‖) := by
            rw [← mul_assoc, ← pow_succ']
            congr 2
            omega
          rw [hstep]
          calc ‖t‖⁻¹ * ((‖t‖⁻¹) ^ (n - 1) * ‖y‖) < ‖t‖⁻¹ * (δ * ‖t‖) :=
                mul_lt_mul_of_pos_left hmin (inv_pos.mpr ht0)
            _ = δ := by field_simp
      set y' : κ → A := fun j => tinv ^ n * y j with hy'
      have hy'r : y' ∈ Set.range f := by
        obtain ⟨v, rfl⟩ := hyr
        exact ⟨fun i => tinv ^ n * v i, hequivinv_pow n v⟩
      have hy'n : ‖y'‖ < δ := by
        rw [hy', hpitinvpow n y]
        exact hnlt
      obtain ⟨u', hu'f, hu'R⟩ := key y' hy'r hy'n
      refine ⟨fun i => t ^ n * u' i, ?_, ?_⟩
      · rw [hequiv_pow n u', hu'f]
        funext j
        rw [hy']
        show t ^ n * (tinv ^ n * y j) = y j
        rw [← mul_assoc, ← mul_pow, htinv, IsUnit.mul_val_inv, one_pow, one_mul]
      · have hyn : ‖y‖ = ‖t‖ ^ n * ‖y'‖ := by
          have : y = fun j => t ^ n * y' j := by
            funext j
            rw [hy']
            show y j = t ^ n * (tinv ^ n * y j)
            rw [← mul_assoc, ← mul_pow, htinv, IsUnit.mul_val_inv, one_pow, one_mul]
          rw [this, hpitpowκ n y']
        have hy'ge : δ * ‖t‖ ≤ ‖y'‖ := by
          rw [hy', hpitinvpow n y]
          exact hnspec
        rw [hpitpow n u']
        refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right 1 (R / (δ * ‖t‖)))
          (norm_nonneg y))
        rw [hyn]
        calc ‖t‖ ^ n * ‖u'‖ ≤ ‖t‖ ^ n * R :=
              mul_le_mul_of_nonneg_left hu'R (pow_nonneg (norm_nonneg t) n)
          _ = R / (δ * ‖t‖) * (‖t‖ ^ n * (δ * ‖t‖)) := by
              field_simp
          _ ≤ R / (δ * ‖t‖) * (‖t‖ ^ n * ‖y'‖) := by
              refine mul_le_mul_of_nonneg_left ?_ hconst.le
              exact mul_le_mul_of_nonneg_left hy'ge (pow_nonneg (norm_nonneg t) n)
    · -- scale down by `t`-powers into the window
      push Not at hcase
      have hex : ∃ m : ℕ, ‖t‖ ^ m * ‖y‖ < δ := by
        obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hδpos hypos) ht1
        exact ⟨m, by
          rw [lt_div_iff₀ hypos] at hm
          exact hm⟩
      set m := Nat.find hex with hm
      have hmspec : ‖t‖ ^ m * ‖y‖ < δ := Nat.find_spec hex
      have hmge : δ * ‖t‖ ≤ ‖t‖ ^ m * ‖y‖ := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · exfalso
          rw [h0, pow_zero, one_mul] at hmspec
          exact absurd hmspec (not_lt.mpr hcase)
        · have hmin := Nat.find_min hex (m := m - 1) (by omega)
          push Not at hmin
          have hstep : (‖t‖ ^ m * ‖y‖) = ‖t‖ * (‖t‖ ^ (m - 1) * ‖y‖) := by
            rw [← mul_assoc, ← pow_succ']
            congr 2
            omega
          rw [hstep]
          calc δ * ‖t‖ = ‖t‖ * δ := mul_comm _ _
            _ ≤ ‖t‖ * (‖t‖ ^ (m - 1) * ‖y‖) :=
                mul_le_mul_of_nonneg_left hmin (norm_nonneg t)
      set y' : κ → A := fun j => t ^ m * y j with hy'
      have hy'r : y' ∈ Set.range f := by
        obtain ⟨v, rfl⟩ := hyr
        exact ⟨fun i => t ^ m * v i, hequiv_pow m v⟩
      have hy'n : ‖y'‖ < δ := by
        rw [hy', hpitpowκ m y]
        exact hmspec
      obtain ⟨u', hu'f, hu'R⟩ := key y' hy'r hy'n
      refine ⟨fun i => tinv ^ m * u' i, ?_, ?_⟩
      · rw [hequivinv_pow m u', hu'f]
        funext j
        rw [hy']
        show tinv ^ m * (t ^ m * y j) = y j
        rw [← mul_assoc, ← mul_pow, htinv, IsUnit.val_inv_mul, one_pow, one_mul]
      · have hyn : ‖y‖ = (‖t‖⁻¹) ^ m * ‖y'‖ := by
          have hyeq : y = fun j => tinv ^ m * y' j := by
            funext j
            rw [hy']
            show y j = tinv ^ m * (t ^ m * y j)
            rw [← mul_assoc, ← mul_pow, htinv, IsUnit.val_inv_mul, one_pow, one_mul]
          rw [hyeq, hpitinvpow m y']
        have hy'ge : δ * ‖t‖ ≤ ‖y'‖ := by
          rw [hy', hpitpowκ m y]
          exact hmge
        rw [hpitinvpowι m u']
        refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right 1 (R / (δ * ‖t‖)))
          (norm_nonneg y))
        rw [hyn]
        calc (‖t‖⁻¹) ^ m * ‖u'‖ ≤ (‖t‖⁻¹) ^ m * R :=
              mul_le_mul_of_nonneg_left hu'R (pow_nonneg (by positivity) m)
          _ = R / (δ * ‖t‖) * ((‖t‖⁻¹) ^ m * (δ * ‖t‖)) := by
              field_simp
          _ ≤ R / (δ * ‖t‖) * ((‖t‖⁻¹) ^ m * ‖y'‖) := by
              refine mul_le_mul_of_nonneg_left ?_ hconst.le
              exact mul_le_mul_of_nonneg_left hy'ge (pow_nonneg (by positivity) m)

end UltrametricBanach

section Restricted

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] {m : ℕ}

-- v4.33: the `MvPolynomial`-`CommSemiring` diamond (`AddMonoidAlgebra.commSemiring` vs
-- `CommRing.toCommSemiring`) blocks the flat-lemma's instance unification at reducible
-- transparency; restore pre-v4.33 defeq behaviour for this declaration.
/-- Graph-sequence syzygies over `P_E = E⟨T⟩` are Koszul-generated **algebraically**
([FJP] Lemma 4.2: positive-degree exactness transfers along the flat base change; degree-1
form). -/
theorem syzygy_graph_restricted (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i)))
    (u : Fin m → P E m) (h : d1 r u = 0) :
    ∃ v, d2 r v = u := by
  classical
  letI : Algebra (MvPolynomial (Fin m) E) (P E m) := (polyToP (E := E) (m := m)).toAlgebra
  haveI hflat : Module.Flat (MvPolynomial (Fin m) E) (P E m) :=
    flat_polyToP hE₀ t htu ht1 ht0 hscale
  set ρ : Fin m → MvPolynomial (Fin m) E :=
    fun i => MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i) with hρ
  have hrel : ∑ i, ρ i • u i = 0 := by
    rw [← h]
    unfold d1
    exact Finset.sum_congr rfl fun i _ => by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hr i, mul_comm]
  obtain ⟨k, a, y, hxy, haj⟩ := hflat.isTrivialRelation_of_sum_smul_eq_zero hrel
  have hcol : ∀ j : Fin k, ∃ w, d2 ρ w = fun i => a i j := fun j => by
    refine syzygy_graph_polynomial g f hunit (fun i => a i j) ?_
    unfold d1
    rw [show (∑ i, a i j * (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))) =
      ∑ i, ρ i * a i j from Finset.sum_congr rfl fun i _ => mul_comm _ _]
    exact haj j
  choose w hw using hcol
  refine ⟨fun p => ∑ j, y j * polyToP (w j p), funext fun i => ?_⟩
  have hrfun : (fun i' => polyToP (E := E) (m := m) (ρ i')) = r :=
    funext fun i' => (hr i').symm
  calc d2 r (fun p => ∑ j, y j * polyToP (w j p)) i
      = ∑ j, y j * d2 r (fun p => polyToP (w j p)) i :=
        d2_sum Finset.univ r y (fun j p => polyToP (w j p)) i
    _ = ∑ j, y j * polyToP ((d2 ρ (w j)) i) := Finset.sum_congr rfl fun j _ => by
        rw [show d2 r (fun p => polyToP (E := E) (m := m) (w j p)) i =
          polyToP ((d2 ρ (w j)) i) from by
            rw [← hrfun]
            exact (d2_map polyToP ρ (w j) i).symm]
    _ = ∑ j, y j * polyToP (a i j) := Finset.sum_congr rfl fun j _ => by
        rw [congrFun (hw j) i]
    _ = ∑ j, a i j • y j := Finset.sum_congr rfl fun j _ => by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    _ = u i := (hxy i).symm

/-- The graph ideal `I_E = im(d₁) ⊂ P_E` is **closed** ([FJP] Lemma 4.2: "every
differential has closed image … In particular `I_D = im(d₁) ⊂ P_D` is closed"; via the
noetherian finite-module theory of `NoetherianTateModules.lean`). Requires `P_E`
noetherian (strong noetherianity of the vertex). -/
theorem isClosed_graphIdeal [IsNoetherianRing (P E m)]
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀P : IsNoetherianRing (unitBall (P E m)))
    (r : Fin m → P E m) :
    IsClosed ((Ideal.span (Set.range r) : Set (P E m))) := by
  haveI : IsTateRing (P E m) := isTateRing_of_scale (polyToP (MvPolynomial.C t))
    (isUnit_tP t htu)
    (by rw [norm_tP t hscale]; exact ht1)
    (by rw [norm_tP t hscale]; exact ht0)
    (fun G => by rw [norm_tP t hscale]; exact norm_tP_mul t hscale G)
  set pod := unitBallPod (E := P E m) (polyToP (MvPolynomial.C t)) (isUnit_tP t htu)
    (by rw [norm_tP t hscale]; exact ht1) (by rw [norm_tP t hscale]; exact ht0)
    (fun G => by rw [norm_tP t hscale]; exact norm_tP_mul t hscale G) with hpod
  haveI : IsNoetherianRing ↥pod.A₀ := hE₀P
  haveI : IsUniformAddGroup (P E m) := SeminormedAddCommGroup.to_isUniformAddGroup
  exact Wedhorn.isClosed_ideal_of_noetherian pod _

/-- Strictness of `d₁` with an explicit constant ([FJP] (4.7): "an element `x ∈ I_E` has a
representative `u ∈ P_E^m` with `d_{1,E}(u) = x`, `‖u‖ ≤ h_E ‖x‖`"; from closedness + the
Banach open mapping theorem with constants). -/
theorem exists_d1_lift [IsNoetherianRing (P E m)]
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀P : IsNoetherianRing (unitBall (P E m)))
    (r : Fin m → P E m) :
    ∃ h : ℝ, 1 ≤ h ∧ ∀ x ∈ Ideal.span (Set.range r),
      ∃ u : Fin m → P E m, d1 r u = x ∧ ‖u‖ ≤ h * ‖x‖ := by
  classical
  set tP : P E m := polyToP (MvPolynomial.C t) with htP
  have htPu : IsUnit tP := isUnit_tP t htu
  have htP1 : ‖tP‖ < 1 := by rw [htP, norm_tP t hscale]; exact ht1
  have htP0 : 0 < ‖tP‖ := by rw [htP, norm_tP t hscale]; exact ht0
  have htPs : ∀ G : P E m, ‖tP * G‖ = ‖tP‖ * ‖G‖ := fun G => by
    rw [htP, norm_tP t hscale]
    exact norm_tP_mul t hscale G
  set F : (Fin m → P E m) →+ (Fin 1 → P E m) :=
    { toFun := fun u => fun _ => d1 r u
      map_zero' := funext fun _ => by
        show d1 r 0 = 0
        unfold d1
        exact Finset.sum_eq_zero fun i _ => zero_mul _
      map_add' := fun u v => funext fun _ => by
        show d1 r (u + v) = d1 r u + d1 r v
        unfold d1
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          show (u i + v i) * r i = _
          ring } with hF
  have hrange : Set.range F = {y : Fin 1 → P E m | y 0 ∈ Ideal.span (Set.range r)} := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      show d1 r u ∈ Ideal.span (Set.range r)
      unfold d1
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨i, rfl⟩)
    · intro hy
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
      refine ⟨c, funext fun j => ?_⟩
      rw [Subsingleton.elim j 0]
      show d1 r c = y 0
      unfold d1
      exact hc
  have hclosed : IsClosed (Set.range F) := by
    rw [hrange]
    exact (isClosed_graphIdeal t htu ht1 ht0 hscale hE₀P r).preimage (continuous_apply 0)
  have hcont : Continuous F := by
    refine continuous_pi fun _ => ?_
    show Continuous fun u : Fin m → P E m => d1 r u
    unfold d1
    exact continuous_finsetSum _ fun i _ => ((continuous_apply i).mul continuous_const)
  have hequiv : ∀ u, F (fun i => tP * u i) = fun k => tP * F u k := fun u =>
    funext fun k => by
      show d1 r (fun i => tP * u i) = tP * d1 r u
      unfold d1
      rw [show (tP * ∑ i, u i * r i) = ∑ i, tP * (u i * r i) from Finset.mul_sum _ _ _]
      exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨h, hh1, hlift⟩ := exists_lift_norm_le_of_closed_range htPu htP1 htP0 htPs
    F hcont hequiv hclosed
  refine ⟨h, hh1, fun x hx => ?_⟩
  obtain ⟨u, hu, hun⟩ := hlift (fun _ => x) (by rw [hrange]; exact hx)
  refine ⟨u, congrFun hu 0, ?_⟩
  refine hun.trans ?_
  rw [pi_norm_const x]

/-- Strictness of `d₂` onto `ker d₁` with an explicit constant ([FJP] (4.8): "every
`s ∈ ker(d_{1,D})` has `v ∈ ⋀² P_D^m` satisfying `d_{2,D}(v) = s`, `‖v‖ ≤ z_D ‖s‖`").
For `m = 1` the conclusion forces `ker d₁ = 0` (`Pairs 1` is empty), which holds because
`gT − f` is a nonzerodivisor. -/
theorem exists_d2_lift [IsNoetherianRing (P E m)]
    (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))) :
    ∃ z : ℝ, 1 ≤ z ∧ ∀ u : Fin m → P E m, d1 r u = 0 →
      ∃ v : Pairs m → P E m, d2 r v = u ∧ ‖v‖ ≤ z * ‖u‖ := by
  classical
  set tP : P E m := polyToP (MvPolynomial.C t) with htP
  have htPu : IsUnit tP := isUnit_tP t htu
  have htP1 : ‖tP‖ < 1 := by rw [htP, norm_tP t hscale]; exact ht1
  have htP0 : 0 < ‖tP‖ := by rw [htP, norm_tP t hscale]; exact ht0
  have htPs : ∀ G : P E m, ‖tP * G‖ = ‖tP‖ * ‖G‖ := fun G => by
    rw [htP, norm_tP t hscale]
    exact norm_tP_mul t hscale G
  set F : (Pairs m → P E m) →+ (Fin m → P E m) :=
    { toFun := fun v => d2 r v
      map_zero' := funext fun j => d2_zero r j
      map_add' := fun v w => funext fun j => d2_add r v w j } with hF
  have hrange : Set.range F = {u : Fin m → P E m | d1 r u = 0} := by
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      exact d1_d2 r v
    · intro hu
      exact syzygy_graph_restricted hE₀ t htu ht1 ht0 hscale g f hunit r hr u hu
  have hd1cont : Continuous fun u : Fin m → P E m => d1 r u := by
    unfold d1
    exact continuous_finsetSum _ fun i _ => ((continuous_apply i).mul continuous_const)
  have hclosed : IsClosed (Set.range F) := by
    rw [hrange]
    exact isClosed_singleton.preimage hd1cont
  have hcont : Continuous F := by
    refine continuous_pi fun j => ?_
    show Continuous fun v : Pairs m → P E m => d2 r v j
    unfold d2
    refine Continuous.sub ?_ ?_
    · refine continuous_finsetSum _ fun i _ => ?_
      by_cases hij : i < j
      · simp only [dif_pos hij]
        exact (continuous_apply _).mul continuous_const
      · simp only [dif_neg hij]
        exact continuous_const
    · refine continuous_finsetSum _ fun i _ => ?_
      by_cases hij : j < i
      · simp only [dif_pos hij]
        exact (continuous_apply _).mul continuous_const
      · simp only [dif_neg hij]
        exact continuous_const
  have hequiv : ∀ v, F (fun p => tP * v p) = fun j => tP * F v j := fun v =>
    funext fun j => d2_smul r tP v j
  obtain ⟨z, hz1, hlift⟩ := exists_lift_norm_le_of_closed_range htPu htP1 htP0 htPs
    F hcont hequiv hclosed
  refine ⟨z, hz1, fun u hu => ?_⟩
  exact hlift u (by rw [hrange]; exact hu)

end Restricted

end GraphKoszul

end FiniteJet
