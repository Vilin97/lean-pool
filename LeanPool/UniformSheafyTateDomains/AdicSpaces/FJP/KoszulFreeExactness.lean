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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.KoszulFiniteFree
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Positive-degree exactness of the finite free Koszul complex

This file proves the polynomial-level positive-degree exactness statements of the
FJP → CDVF campaign (paper Lemma 5.1 clause 1 at the polynomial level; crosswalk
decision D5, ticket K4), for the subset-model Koszul complex of
`FJP/KoszulFiniteFree.lean`.

## Main results

* `koszulDifferential_exact_of_isUnit` : if some `r j` is a unit, the Koszul complex
  of `r` is exact in all positive degrees (contractibility via the insertion homotopy).
* `koszulDifferential_coordinate_exact` : over an arbitrary commutative ring `A`, the
  Koszul complex of the coordinate sequence `X 0, …, X (m-1)` in
  `MvPolynomial (Fin m) A` is exact in all positive degrees.
* `koszulGraph_polynomial_exact` : for `g : A`, `f : Fin m → A` with
  `Ideal.span ({g} ∪ Set.range f) = ⊤`, the Koszul complex of the graph sequence
  `r i = C g * X i - C (f i)` in `MvPolynomial (Fin m) A` is exact in all positive
  degrees.

Exactness is always stated at `K_{q+1}`, i.e. as
`Function.Exact (koszulDifferential r (q+1)) (koszulDifferential r q)` for all `q : ℕ`
(never at `K_0`).

## Proof architecture

Everything is element-level; no homology machinery is used.

* **Insertion chase** (`koszulDifferential_insertion_cancel`): the shared computational
  heart.  If `w` is an "insertion antiderivative" of a closed `x` with respect to the
  index `j` — meaning `w` is supported on indices containing `j` and satisfies
  `r j * w J = ± x (J.erase j)` — then `r j * (d w) = r j * x`.  Cancelling `r j`
  (possible when `r j` is a unit, or when `r j` is regular) yields `d w = x`.
* **Unit case**: for `r j` a unit, `w := ± (r j)⁻¹ • x (·.erase j)` qualifies, giving
  contractibility.  This handles the localizations at primes missing some `r j`.
* **Coordinate case**: the complex is multigraded by total multidegree
  (`indexDegree J + deg`); a closed element decomposes into finitely many closed
  homogeneous components (`koszulComponent`), the `μ = 0` component vanishes in
  positive exterior degrees, and for `μ ≠ 0` a variable `X j` with `μ j ≠ 0` divides
  every relevant coefficient, so the insertion antiderivative exists by explicit
  monomial division; cancel the regular element `X j`.  (This is the
  "multiplication-by-`Tᵢ` homotopy on multidegree components" route of D5, not the
  mapping-cone induction.)
* **Graph case**: exactness is checked after inverting each member of the spanning
  family `{C g} ∪ {r i}` (`exact_of_isLocalized_span`), using the identity
  `C g * (C a₀ + ∑ C (a i) * X i) - ∑ C (a i) * r i = 1` obtained from `hunit`.
  Inverting `r j` is the unit case.  Inverting `C g` identifies the localization with
  `MvPolynomial (Fin m) (Localization.Away g)` (via `MvPolynomial.isLocalization`),
  where `g` is a unit; there the graph sequence is the unit `C g` times a translate
  of the coordinate sequence, and exactness transports along the translation
  automorphism and the unit rescaling.
-/

@[expose] public section

namespace FiniteJet.KoszulFree

/-! ### The insertion chase

The computational heart of the file: if `w` is supported on indices containing `j`
and `r j * w J` is the signed `j`-erasure of a closed chain `x`, then
`r j • d w = r j • x`.  The sign `(-1) ^ #{k ∈ J | k < j}` is the position of `j`
in the increasing enumeration of `J` (same convention as the differential). -/

section InsertionChase

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The sign square `(-1)^c * (-1)^c = 1`. -/
private theorem neg_one_pow_mul_self (c : ℕ) : ((-1 : R) ^ c) * (-1 : R) ^ c = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨c, rfl⟩

/-- Erasing `j` does not change the elements below `j`. -/
private theorem filter_lt_erase (J : Finset (Fin m)) (j : Fin m) :
    (J.erase j).filter (· < j) = J.filter (· < j) := by
  rw [Finset.filter_erase,
    Finset.erase_eq_of_notMem (s := J.filter (· < j))
      fun h => absurd (Finset.mem_filter.mp h).2 (lt_irrefl j)]

/-- The four-sign identity for an insertion/erasure pair: for `j ∈ J`, `i ∉ J`,
`i ≠ j`, the sign of inserting `i` into `J` times the sign of `j` inside
`insert i J` is minus the sign of `j` inside `J` times the sign of inserting `i`
into `J.erase j`. -/
private theorem sign_insert_erase {J : Finset (Fin m)} {i j : Fin m}
    (hij : i ≠ j) (hjJ : j ∈ J) (hiJ : i ∉ J) :
    ((-1 : R) ^ (J.filter (· < i)).card) * (-1 : R) ^ (((insert i J).filter (· < j)).card) =
      -(((-1 : R) ^ (J.filter (· < j)).card) *
        (-1 : R) ^ (((J.erase j).filter (· < i)).card)) := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · -- `i < j`: inserting `i` bumps the count below `j`; erasing `j` keeps the count below `i`
    have h1 : (J.filter (· < i)).card = ((J.erase j).filter (· < i)).card := by
      conv_lhs => rw [← Finset.insert_erase hjJ]
      exact card_filter_lt_insert_of_not_lt hlt.asymm
    have h2 : ((insert i J).filter (· < j)).card = (J.filter (· < j)).card + 1 :=
      card_filter_lt_insert_of_lt hlt hiJ
    rw [h1, h2, pow_succ]
    ring
  · -- `j < i`: inserting `i` keeps the count below `j`; erasing `j` drops the count below `i`
    have h1 : (J.filter (· < i)).card = ((J.erase j).filter (· < i)).card + 1 := by
      conv_lhs => rw [← Finset.insert_erase hjJ]
      exact card_filter_lt_insert_of_lt hlt (Finset.notMem_erase j J)
    have h2 : ((insert i J).filter (· < j)).card = (J.filter (· < j)).card :=
      card_filter_lt_insert_of_not_lt hlt.asymm
    rw [h1, h2, pow_succ]
    ring

/-- **The insertion chase.**  Let `x` be a closed `(q+1)`-chain and `w` a `(q+2)`-chain
supported on indices containing `j` such that `r j * w J` is the signed `j`-erasure of
`x`.  Then `r j * (d w) J = r j * x J` for every `J`.  Cancelling `r j` (a unit, or a
regular element) shows that closed chains admitting such a `w` are boundaries. -/
theorem koszulDifferential_insertion_cancel (r : Fin m → R) (j : Fin m) (q : ℕ)
    (x : KoszulTerm R m (q + 1)) (w : KoszulTerm R m (q + 1 + 1))
    (hx : koszulDifferential r q x = 0)
    (hw0 : ∀ J : KoszulIndex m (q + 1 + 1), j ∉ J.1 → w J = 0)
    (hw1 : ∀ (J : KoszulIndex m (q + 1 + 1)) (hj : j ∈ J.1),
      r j * w J = (-1 : R) ^ ((J.1.filter (· < j)).card) *
        x ⟨J.1.erase j, by simp [Finset.card_erase_of_mem hj, J.2]⟩)
    (J : KoszulIndex m (q + 1)) :
    r j * koszulDifferential r (q + 1) w J = r j * x J := by
  by_cases hjJ : j ∈ J.1
  · -- main case: `j ∈ J`; compare the double sum with `(d x) (J.erase j) = 0`
    set Jer : KoszulIndex m q := ⟨J.1.erase j, by simp [Finset.card_erase_of_mem hjJ, J.2]⟩
      with hJer
    have hxJer : (0 : R) =
        ∑ i, if hi : i ∈ Jer.1 then 0 else
          (-1 : R) ^ (Jer.1.filter (· < i)).card *
            (r i * x ⟨insert i Jer.1, by rw [Finset.card_insert_of_notMem hi, Jer.2]⟩) := by
      rw [← koszulDifferential_apply r q x Jer, hx]
      rfl
    have key : ∀ i : Fin m,
        r j * (if hi : i ∈ J.1 then 0 else
          (-1 : R) ^ (J.1.filter (· < i)).card *
            (r i * w ⟨insert i J.1, by rw [Finset.card_insert_of_notMem hi, J.2]⟩)) =
        -((-1 : R) ^ ((J.1.filter (· < j)).card)) *
          (if hi : i ∈ Jer.1 then 0 else
            (-1 : R) ^ (Jer.1.filter (· < i)).card *
              (r i * x ⟨insert i Jer.1, by rw [Finset.card_insert_of_notMem hi, Jer.2]⟩)) +
          (if i = j then r j * x J else 0) := by
      intro i
      by_cases hijeq : i = j
      · -- diagonal term: reproduces `r j * x J` with the opposite sign
        subst hijeq
        rw [dite_eq_left hjJ, dite_eq_right (by simp [hJer]), ite_eq_left rfl, mul_zero]
        have hidx : x ⟨insert i Jer.1, by
              rw [Finset.card_insert_of_notMem (by simp [hJer]), Jer.2]⟩ = x J := by
          have : insert i Jer.1 = J.1 := by
            simpa [hJer] using Finset.insert_erase hjJ
          rw [koszulTerm_index_congr x this]
        rw [hidx]
        have hsgn : (Jer.1.filter (· < i)) = (J.1.filter (· < i)) := by
          simpa [hJer] using filter_lt_erase J.1 i
        rw [hsgn]
        linear_combination (r i * x J) * neg_one_pow_mul_self (R := R) (J.1.filter (· < i)).card
      · by_cases hiJ : i ∈ J.1
        · -- `i` already in `J`: both sides vanish
          rw [dite_eq_left hiJ, dite_eq_left (by simp [hJer, Finset.mem_erase, hijeq, hiJ]),
            ite_eq_right hijeq, mul_zero, mul_zero, add_zero]
        · -- fresh `i ≠ j`: the four-sign identity
          have hiJer : i ∉ Jer.1 := fun h => hiJ (Finset.mem_of_mem_erase h)
          rw [dite_eq_right hiJ, dite_eq_right hiJer, ite_eq_right hijeq, add_zero]
          have hjins : j ∈ (insert i J.1) := Finset.mem_insert_of_mem hjJ
          have h1 := hw1 ⟨insert i J.1, by rw [Finset.card_insert_of_notMem hiJ, J.2]⟩ hjins
          have hidx : x ⟨(insert i J.1).erase j, by
                simp [Finset.card_erase_of_mem hjins, Finset.card_insert_of_notMem hiJ, J.2]⟩ =
              x ⟨insert i Jer.1, by rw [Finset.card_insert_of_notMem hiJer, Jer.2]⟩ := by
            rw [koszulTerm_index_congr x (Finset.erase_insert_of_ne hijeq)]
          rw [hidx] at h1
          have hsign := sign_insert_erase (R := R) hijeq hjJ hiJ
          set y := x ⟨insert i Jer.1, by rw [Finset.card_insert_of_notMem hiJer, Jer.2]⟩
          set wi := w ⟨insert i J.1, by rw [Finset.card_insert_of_notMem hiJ, J.2]⟩
          -- `r j * (sgn i J * (r i * w)) = -(sgn j J) * (sgn i Jer * (r i * x))`
          simp only [hJer] at hsign ⊢
          linear_combination
            (((-1 : R) ^ ((J.1.filter (· < i)).card)) * r i) * h1 + (r i * y) * hsign
    calc r j * koszulDifferential r (q + 1) w J
        = ∑ i, r j * (if hi : i ∈ J.1 then 0 else
            (-1 : R) ^ (J.1.filter (· < i)).card *
              (r i * w ⟨insert i J.1, by rw [Finset.card_insert_of_notMem hi, J.2]⟩)) := by
          rw [koszulDifferential_apply, Finset.mul_sum]
      _ = ∑ i, (-((-1 : R) ^ ((J.1.filter (· < j)).card)) *
            (if hi : i ∈ Jer.1 then 0 else
              (-1 : R) ^ (Jer.1.filter (· < i)).card *
                (r i * x ⟨insert i Jer.1, by rw [Finset.card_insert_of_notMem hi, Jer.2]⟩)) +
            (if i = j then r j * x J else 0)) :=
          Finset.sum_congr rfl fun i _ => key i
      _ = r j * x J := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hxJer]
          simp
  · -- `j ∉ J`: the sum collapses to the `i = j` term
    rw [koszulDifferential_apply,
      Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun i _ hij => ?_), dite_eq_right hjJ]
    · have h1 := hw1 ⟨insert j J.1, by rw [Finset.card_insert_of_notMem hjJ, J.2]⟩
        (Finset.mem_insert_self j J.1)
      have hidx : x ⟨(insert j J.1).erase j, by
            rw [Finset.erase_insert hjJ]; exact J.2⟩ = x J := by
        rw [koszulTerm_index_congr x (Finset.erase_insert hjJ)]
      rw [hidx] at h1
      have hsgn : ((insert j J.1).filter (· < j)).card = (J.1.filter (· < j)).card :=
        card_filter_lt_insert_of_not_lt (lt_irrefl j)
      rw [hsgn] at h1
      set wj := w ⟨insert j J.1, by rw [Finset.card_insert_of_notMem hjJ, J.2]⟩
      linear_combination
        (((-1 : R) ^ ((J.1.filter (· < j)).card)) * r j) * h1 +
          (r j * x J) * neg_one_pow_mul_self (R := R) (J.1.filter (· < j)).card
    · by_cases hiJ : i ∈ J.1
      · rw [dite_eq_left hiJ]
      · rw [dite_eq_right hiJ,
          hw0 _ (fun h => (Finset.mem_insert.mp h).elim (fun h' => hij h'.symm)
            fun h' => hjJ h'), mul_zero, mul_zero]

/-- If some `r j` is a unit, the Koszul complex of `r` is exact in every positive
degree: the insertion homotopy `w J = ± (r j)⁻¹ * x (J.erase j)` contracts it. -/
theorem koszulDifferential_exact_of_isUnit {r : Fin m → R} {j : Fin m}
    (hj : IsUnit (r j)) (q : ℕ) :
    Function.Exact (koszulDifferential r (q + 1)) (koszulDifferential r q) := by
  classical
  intro y
  constructor
  · intro hy
    refine ⟨fun J => if h : j ∈ J.1 then
        (-1 : R) ^ ((J.1.filter (· < j)).card) *
          (↑hj.unit⁻¹ * y ⟨J.1.erase j, by simp [Finset.card_erase_of_mem h, J.2]⟩)
      else 0, ?_⟩
    funext J
    refine hj.mul_left_cancel ?_
    rw [koszulDifferential_insertion_cancel r j q y _ hy (fun J hJ => dite_eq_right hJ)
      (fun J hJ => ?_) J]
    rw [dite_eq_left hJ, mul_left_comm (r j), ← mul_assoc (r j), IsUnit.mul_val_inv hj, one_mul]
  · rintro ⟨x, rfl⟩
    exact koszulDifferential_koszulDifferential r q x

end InsertionChase

/-! ### Coordinate exactness

Over `MvPolynomial (Fin m) A` the Koszul complex of the coordinate sequence
`X 0, …, X (m-1)` is multigraded by *total multidegree*: the term `p • e_J` has
degree `deg p + indexDegree J`, where `indexDegree J = ∑_{j ∈ J} single j 1`, and the
differential preserves this grading.  A closed chain therefore splits into finitely
many closed homogeneous components (`koszulComponent`).  The `μ = 0` component
vanishes in positive exterior degree; for `μ ≠ 0` and `j` with `μ j ≠ 0`, every
coefficient of the component at an index avoiding `j` is divisible by `X j`, so the
insertion antiderivative of the chase exists by explicit monomial division, and the
regular element `X j` cancels. -/

section Coordinate

open MvPolynomial

variable {A : Type*} [CommRing A] {m : ℕ}

/-- The multidegree contributed by a Koszul index: `∑_{j ∈ J} single j 1`. -/
noncomputable def indexDegree (J : Finset (Fin m)) : Fin m →₀ ℕ :=
  ∑ j ∈ J, Finsupp.single j 1

theorem indexDegree_insert {i : Fin m} {J : Finset (Fin m)} (h : i ∉ J) :
    indexDegree (insert i J) = Finsupp.single i 1 + indexDegree J :=
  Finset.sum_insert h

theorem indexDegree_apply_of_notMem {i : Fin m} {J : Finset (Fin m)} (h : i ∉ J) :
    indexDegree J i = 0 := by
  rw [indexDegree, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun j hj =>
    Finsupp.single_eq_of_ne fun hij => h (hij ▸ hj)

theorem indexDegree_apply_of_mem {i : Fin m} {J : Finset (Fin m)} (h : i ∈ J) :
    indexDegree J i = 1 := by
  rw [indexDegree, Finsupp.finsetSum_apply,
    Finset.sum_eq_single_of_mem i h fun j _ hji => Finsupp.single_eq_of_ne hji.symm]
  exact Finsupp.single_eq_same

/-- The total-multidegree-`μ` component of a Koszul chain over `MvPolynomial (Fin m) A`:
at the index `J` it keeps exactly the `(μ - indexDegree J)`-monomial of `x J`
(and is `0` unless `indexDegree J ≤ μ`). -/
noncomputable def koszulComponent (μ : Fin m →₀ ℕ) {n : ℕ}
    (x : KoszulTerm (MvPolynomial (Fin m) A) m n) :
    KoszulTerm (MvPolynomial (Fin m) A) m n := fun J =>
  if indexDegree J.1 ≤ μ then
    monomial (μ - indexDegree J.1) ((x J).coeff (μ - indexDegree J.1))
  else 0

/-- The finitely many total multidegrees appearing in a Koszul chain. -/
noncomputable def koszulDegrees {n : ℕ} (x : KoszulTerm (MvPolynomial (Fin m) A) m n) :
    Finset (Fin m →₀ ℕ) :=
  Finset.univ.biUnion fun J => (x J).support.image (indexDegree J.1 + ·)

theorem koszulComponent_zero_chain (μ : Fin m →₀ ℕ) {n : ℕ} :
    koszulComponent μ (0 : KoszulTerm (MvPolynomial (Fin m) A) m n) = 0 := by
  funext J
  simp [koszulComponent]

/-- In positive exterior degree the multidegree-`0` component vanishes: the index
already contributes a positive multidegree. -/
theorem koszulComponent_zero_of_ne {n : ℕ} (hn : n ≠ 0)
    (x : KoszulTerm (MvPolynomial (Fin m) A) m n) :
    koszulComponent (0 : Fin m →₀ ℕ) x = 0 := by
  funext J
  have hne : ¬ indexDegree J.1 ≤ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Finset.card_pos.mp (by rw [J.2]; exact Nat.pos_of_ne_zero hn)
    have h1 := indexDegree_apply_of_mem hk
    rw [nonpos_iff_eq_zero.mp h] at h1
    simp at h1
  simp [koszulComponent, hne]

/-- Decomposition of a Koszul chain into its multidegree components. -/
theorem sum_koszulComponent {n : ℕ} (x : KoszulTerm (MvPolynomial (Fin m) A) m n) :
    ∑ μ ∈ koszulDegrees x, koszulComponent μ x = x := by
  classical
  funext J
  rw [Finset.sum_apply]
  have hsub : ((x J).support.image (indexDegree J.1 + ·)) ⊆ koszulDegrees x :=
    Finset.subset_biUnion_of_mem (fun J => (x J).support.image (indexDegree J.1 + ·))
      (Finset.mem_univ J)
  rw [← Finset.sum_subset hsub fun μ _ hμnot => ?_]
  · have hinj : Function.Injective (indexDegree J.1 + ·) := fun d1 d2 h =>
      Finsupp.ext fun k => by simpa [Finsupp.add_apply] using DFunLike.congr_fun h k
    rw [Finset.sum_image hinj.injOn]
    rw [Finset.sum_congr rfl fun d hd => ?_, support_sum_monomial_coeff (x J)]
    simp only [koszulComponent, ite_eq_left (self_le_add_right (indexDegree J.1) d),
      add_tsub_cancel_left]
  · simp only [koszulComponent]
    split_ifs with h
    · have hc : (x J).coeff (μ - indexDegree J.1) = 0 := by
        by_contra hc
        refine hμnot ?_
        have hμeq : indexDegree J.1 + (μ - indexDegree J.1) = μ := add_tsub_cancel_of_le h
        rw [← hμeq]
        exact Finset.mem_image_of_mem _ (mem_support_iff.mpr hc)
      rw [hc, monomial_zero]
    · rfl

private theorem indexDegree_insert_le_iff {μ : Fin m →₀ ℕ} {J : Finset (Fin m)} {i : Fin m}
    (hiJ : i ∉ J) (hJ : indexDegree J ≤ μ) :
    indexDegree (insert i J) ≤ μ ↔ i ∈ (μ - indexDegree J).support := by
  rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, indexDegree_apply_of_notMem hiJ,
    Nat.sub_zero, indexDegree_insert hiJ]
  constructor
  · intro h
    have h1 := Finsupp.le_def.mp h i
    rw [Finsupp.add_apply, Finsupp.single_eq_same, indexDegree_apply_of_notMem hiJ] at h1
    omega
  · intro h
    rw [Finsupp.le_def]
    intro k
    rw [Finsupp.add_apply]
    rcases eq_or_ne k i with rfl | hk
    · rw [Finsupp.single_eq_same, indexDegree_apply_of_notMem hiJ]
      omega
    · rw [Finsupp.single_eq_of_ne hk, zero_add]
      exact Finsupp.le_def.mp hJ k

private theorem tsub_indexDegree_insert {μ : Fin m →₀ ℕ} {J : Finset (Fin m)} {i : Fin m}
    (hiJ : i ∉ J) :
    μ - indexDegree J - Finsupp.single i 1 = μ - indexDegree (insert i J) := by
  rw [indexDegree_insert hiJ, tsub_tsub, add_comm]

private theorem single_le_tsub_of_notMem {μ : Fin m →₀ ℕ} {J : Finset (Fin m)} {j : Fin m}
    (hj : j ∉ J) (hμj : μ j ≠ 0) :
    Finsupp.single j 1 ≤ μ - indexDegree J := by
  rw [Finsupp.single_le_iff, Finsupp.tsub_apply, indexDegree_apply_of_notMem hj, Nat.sub_zero]
  omega

private theorem single_add_tsub_indexDegree {μ : Fin m →₀ ℕ} {J : Finset (Fin m)} {i : Fin m}
    (hiJ : i ∉ J) (hins : indexDegree (insert i J) ≤ μ) :
    Finsupp.single i 1 + (μ - indexDegree (insert i J)) = μ - indexDegree J := by
  rw [← tsub_indexDegree_insert hiJ]
  refine add_tsub_cancel_of_le (single_le_tsub_of_notMem hiJ ?_)
  have h1 := Finsupp.le_def.mp hins i
  rw [indexDegree_insert hiJ, Finsupp.add_apply, Finsupp.single_eq_same,
    indexDegree_apply_of_notMem hiJ] at h1
  omega

/-- The coordinate Koszul differential is homogeneous for the total multidegree:
taking components commutes with it. -/
theorem koszulComponent_differential (μ : Fin m →₀ ℕ) (q : ℕ)
    (x : KoszulTerm (MvPolynomial (Fin m) A) m (q + 1)) :
    koszulComponent μ
        (koszulDifferential (fun i => (X i : MvPolynomial (Fin m) A)) q x) =
      koszulDifferential (fun i => X i) q (koszulComponent μ x) := by
  classical
  funext J
  simp only [koszulComponent, koszulDifferential_apply]
  by_cases hJ : indexDegree J.1 ≤ μ
  · rw [ite_eq_left hJ, coeff_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hiJ : i ∈ J.1
    · simp only [dite_eq_left hiJ, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, monomial_zero]
    · rw [dite_eq_right hiJ, dite_eq_right hiJ]
      have hsgn : ((-1 : MvPolynomial (Fin m) A) ^ (J.1.filter (· < i)).card) =
          C ((-1 : A) ^ (J.1.filter (· < i)).card) := by
        rw [map_pow, map_neg, map_one]
      rw [hsgn, coeff_C_mul, coeff_X_mul']
      have hXmono : ∀ (ν : Fin m →₀ ℕ) (c : A),
          (X i : MvPolynomial (Fin m) A) * monomial ν c =
            monomial (Finsupp.single i 1 + ν) c := by
        intro ν c
        rw [monomial_single_add, pow_one]
      by_cases hins : indexDegree (insert i J.1) ≤ μ
      · rw [ite_eq_left ((indexDegree_insert_le_iff hiJ hJ).mp hins), ite_eq_left hins,
          tsub_indexDegree_insert hiJ, hXmono, single_add_tsub_indexDegree hiJ hins,
          C_mul_monomial]
      · rw [ite_eq_right fun h => hins ((indexDegree_insert_le_iff hiJ hJ).mpr h), ite_eq_right
          hins,
          mul_zero, mul_zero, mul_zero, monomial_zero]
  · rw [ite_eq_right hJ]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    by_cases hiJ : i ∈ J.1
    · rw [dite_eq_left hiJ]
    · rw [dite_eq_right hiJ, ite_eq_right fun h => hJ ?_, mul_zero, mul_zero]
      calc indexDegree J.1 ≤ indexDegree (insert i J.1) := by
            rw [indexDegree_insert hiJ]; exact self_le_add_left _ _
        _ ≤ μ := h

/-- **Positive-degree exactness of the coordinate Koszul complex** over an arbitrary
commutative ring: for every `q`, the Koszul complex of `X 0, …, X (m-1)` in
`MvPolynomial (Fin m) A` is exact at `K_{q+1}`. -/
theorem koszulDifferential_coordinate_exact (A : Type*) [CommRing A] (m q : ℕ) :
    Function.Exact
      (koszulDifferential (fun i => (X i : MvPolynomial (Fin m) A)) (q + 1))
      (koszulDifferential (fun i => (X i : MvPolynomial (Fin m) A)) q) := by
  classical
  intro y
  constructor
  · intro hy
    -- every multidegree component of `y` is closed
    have hcomp : ∀ μ : Fin m →₀ ℕ,
        koszulDifferential (fun i => (X i : MvPolynomial (Fin m) A)) q
          (koszulComponent μ y) = 0 := fun μ => by
      rw [← koszulComponent_differential, hy, koszulComponent_zero_chain]
    -- every component is a boundary
    have hstep : ∀ μ ∈ koszulDegrees y, ∃ w,
        koszulDifferential (fun i => (X i : MvPolynomial (Fin m) A)) (q + 1) w =
          koszulComponent μ y := by
      intro μ _
      rcases eq_or_ne μ 0 with rfl | hμ0
      · exact ⟨0, by rw [map_zero, koszulComponent_zero_of_ne (Nat.succ_ne_zero q)]⟩
      · obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hμ0
        have hμj : μ j ≠ 0 := Finsupp.mem_support_iff.mp hj
        refine ⟨fun J => if h : j ∈ J.1 ∧ indexDegree (J.1.erase j) ≤ μ then
            (-1 : MvPolynomial (Fin m) A) ^ ((J.1.filter (· < j)).card) *
              monomial (μ - indexDegree (J.1.erase j) - Finsupp.single j 1)
                ((y ⟨J.1.erase j, by simp [Finset.card_erase_of_mem h.1, J.2]⟩).coeff
                  (μ - indexDegree (J.1.erase j)))
          else 0, ?_⟩
        funext J
        refine (isRegular_X (n := j)).left ?_
        refine koszulDifferential_insertion_cancel _ j q (koszulComponent μ y) _ (hcomp μ)
          (fun J hJ => dite_eq_right fun hc => hJ hc.1) (fun J hJ => ?_) J
        by_cases herase : indexDegree (J.1.erase j) ≤ μ
        · have hXmono : ∀ (ν : Fin m →₀ ℕ) (c : A),
              (X j : MvPolynomial (Fin m) A) * monomial ν c =
                monomial (Finsupp.single j 1 + ν) c := by
            intro ν c
            rw [monomial_single_add, pow_one]
          rw [dite_eq_left ⟨hJ, herase⟩, koszulComponent, ite_eq_left herase, mul_left_comm, hXmono,
            add_tsub_cancel_of_le (single_le_tsub_of_notMem (Finset.notMem_erase j J.1) hμj)]
        · rw [dite_eq_right fun hc => herase hc.2, koszulComponent, ite_eq_right herase,
            mul_zero, mul_zero]
    choose W hW using hstep
    refine ⟨∑ μ ∈ (koszulDegrees y).attach, W μ.1 μ.2, ?_⟩
    rw [map_sum]
    calc ∑ μ ∈ (koszulDegrees y).attach,
          koszulDifferential (fun i => (X i : MvPolynomial (Fin m) A)) (q + 1) (W μ.1 μ.2)
        = ∑ μ ∈ (koszulDegrees y).attach, koszulComponent μ.1 y :=
          Finset.sum_congr rfl fun μ _ => hW μ.1 μ.2
      _ = ∑ μ ∈ koszulDegrees y, koszulComponent μ y :=
          Finset.sum_attach _ fun μ => koszulComponent μ y
      _ = y := sum_koszulComponent y
  · rintro ⟨x, rfl⟩
    exact koszulDifferential_koszulDifferential _ q x

end Coordinate

/-! ### Transport of exactness

Positive-degree exactness transports along a ring equivalence applied to the sequence,
and along rescaling of the sequence by a unit. -/

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

/-- `koszulDifferential_map`, specialised to a ring equivalence. -/
theorem koszulDifferential_map_equiv (e : R ≃+* S) (r : Fin m → R) (q : ℕ)
    (x : KoszulTerm R m (q + 1)) (J : KoszulIndex m q) :
    e (koszulDifferential r q x J) =
      koszulDifferential (fun i => e (r i)) q (fun K => e (x K)) J :=
  koszulDifferential_map (e : R →+* S) r q x J

/-- Transport of positive-degree Koszul exactness along a ring equivalence carrying
one sequence to the other. -/
theorem koszulDifferential_exact_congr (e : R ≃+* S) {r : Fin m → R} {s : Fin m → S}
    (hrs : ∀ i, s i = e (r i)) (q : ℕ)
    (hex : Function.Exact (koszulDifferential r (q + 1)) (koszulDifferential r q)) :
    Function.Exact (koszulDifferential s (q + 1)) (koszulDifferential s q) := by
  have hs : s = fun i => e (r i) := funext hrs
  subst hs
  intro y
  constructor
  · intro hy
    have hx : koszulDifferential r q (fun K => e.symm (y K)) = 0 := by
      funext K
      refine e.injective ?_
      rw [Pi.zero_apply, map_zero, koszulDifferential_map_equiv]
      have hyy : (fun K' => e (e.symm (y K'))) = y :=
        funext fun K' => e.apply_symm_apply (y K')
      rw [hyy]
      exact (congrFun hy K).trans rfl
    obtain ⟨w, hw⟩ := (hex _).mp hx
    refine ⟨fun K => e (w K), ?_⟩
    funext K
    rw [← koszulDifferential_map_equiv e r (q + 1) w K, hw]
    exact e.apply_symm_apply (y K)
  · rintro ⟨x, rfl⟩
    exact koszulDifferential_koszulDifferential _ q x

/-- Transport of positive-degree Koszul exactness along rescaling of the sequence by
a unit. -/
theorem koszulDifferential_exact_mul_of_isUnit {c : R} (hc : IsUnit c) (r : Fin m → R)
    (q : ℕ)
    (hex : Function.Exact (koszulDifferential r (q + 1)) (koszulDifferential r q)) :
    Function.Exact (koszulDifferential (fun i => c * r i) (q + 1))
      (koszulDifferential (fun i => c * r i) q) := by
  intro y
  constructor
  · intro hy
    rw [koszulDifferential_smul_sequence] at hy
    have hy' : koszulDifferential r q y = 0 := by
      funext K
      have h1 := congrFun hy K
      rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      exact hc.mul_right_eq_zero.mp h1
    obtain ⟨w, hw⟩ := (hex _).mp hy'
    refine ⟨(↑hc.unit⁻¹ : R) • w, ?_⟩
    rw [koszulDifferential_smul_sequence, map_smul, hw, smul_smul, IsUnit.mul_val_inv,
      one_smul]
  · rintro ⟨x, rfl⟩
    exact koszulDifferential_koszulDifferential _ q x

end Transport

/-! ### The graph sequence over a base where `g` is a unit

Over `MvPolynomial (Fin m) B` with `g : B` a unit, the graph sequence
`C g * X i - C (f i)` is the unit `C g` times the translate `X i - C (g⁻¹ f i)` of the
coordinate sequence, so its Koszul complex is exact in positive degrees. -/

section UnitBase

open MvPolynomial

variable {m : ℕ}

/-- The translation `X i ↦ X i + C (c i)` as an algebra automorphism (local analogue of
the degree-1/2 layer's `GraphKoszul.translationEquiv`; this file does not import
`FiniteJetGraphKoszul`). -/
noncomputable def mvTranslationEquiv {B : Type*} [CommRing B] (c : Fin m → B) :
    MvPolynomial (Fin m) B ≃ₐ[B] MvPolynomial (Fin m) B :=
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

theorem mvTranslationEquiv_X {B : Type*} [CommRing B] (c : Fin m → B) (i : Fin m) :
    mvTranslationEquiv c (X i) = X i + C (c i) :=
  aeval_X _ i

/-- For a unit `g`, the Koszul complex of the graph sequence `C g * X i - C (f i)` in
`MvPolynomial (Fin m) B` is exact in positive degrees. -/
theorem koszulGraph_exact_of_isUnit_base {B : Type*} [CommRing B] {g : B} (hg : IsUnit g)
    (f : Fin m → B) (q : ℕ) :
    Function.Exact
      (koszulDifferential
        (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) B)) (q + 1))
      (koszulDifferential (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) B)) q) := by
  have hseq : (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) B)) =
      fun i => C g * ((mvTranslationEquiv fun k => -(↑hg.unit⁻¹ * f k)) (X i)) := by
    funext i
    rw [mvTranslationEquiv_X, mul_add, ← C_mul, mul_neg, ← mul_assoc, IsUnit.mul_val_inv hg,
      one_mul, map_neg, ← sub_eq_add_neg]
  rw [hseq]
  refine koszulDifferential_exact_mul_of_isUnit (hg.map C) _ q ?_
  refine koszulDifferential_exact_congr
    (mvTranslationEquiv fun k => -(↑hg.unit⁻¹ * f k)).toRingEquiv
    (r := fun i => (X i : MvPolynomial (Fin m) B))
    (fun i => by simp only [AlgEquiv.coe_ringEquiv]) q ?_
  exact koszulDifferential_coordinate_exact B m q

end UnitBase

/-! ### Localization of Koszul terms

The Koszul terms are finite products of the base ring, so localization of modules
(`IsLocalizedModule`) matches the coordinatewise algebra map into the localized ring,
and the localized Koszul differential is the Koszul differential of the image
sequence. -/

section LocalizedTerms

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] {m : ℕ}

/-- The coordinatewise algebra map on Koszul terms, as an `R`-linear map. -/
def koszulTermAlgebraMap (m n : ℕ) : KoszulTerm R m n →ₗ[R] KoszulTerm B m n :=
  LinearMap.pi fun J => (Algebra.linearMap R B) ∘ₗ LinearMap.proj J

@[simp] theorem koszulTermAlgebraMap_apply (m n : ℕ) (x : KoszulTerm R m n)
    (J : KoszulIndex m n) :
    koszulTermAlgebraMap R B m n x J = algebraMap R B (x J) :=
  rfl

/-- Over a localization of the base ring, the coordinatewise algebra map on Koszul
terms is a localization of modules (finite products localize). -/
theorem isLocalizedModule_koszulTermAlgebraMap (S : Submonoid R) [IsLocalization S B]
    (m n : ℕ) : IsLocalizedModule S (koszulTermAlgebraMap R B m n) := by
  unfold koszulTermAlgebraMap
  infer_instance

/-- Naturality square: the coordinatewise algebra map intertwines the Koszul
differentials of a sequence and of its image. -/
theorem koszulTermAlgebraMap_comp_differential (r : Fin m → R) (n : ℕ) :
    (koszulTermAlgebraMap R B m n) ∘ₗ koszulDifferential r n =
      ((koszulDifferential (fun i => algebraMap R B (r i)) n).restrictScalars R) ∘ₗ
        koszulTermAlgebraMap R B m (n + 1) := by
  refine LinearMap.ext fun x => funext fun J => ?_
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    koszulTermAlgebraMap_apply]
  exact koszulDifferential_map (algebraMap R B) r n x J

/-- The localized Koszul differential is the Koszul differential of the image
sequence over the localized ring. -/
theorem isLocalizedModule_map_koszulDifferential (S : Submonoid R) [IsLocalization S B]
    (r : Fin m → R) (n : ℕ) :
    haveI := isLocalizedModule_koszulTermAlgebraMap R B S m (n + 1)
    haveI := isLocalizedModule_koszulTermAlgebraMap R B S m n
    IsLocalizedModule.map S (koszulTermAlgebraMap R B m (n + 1))
        (koszulTermAlgebraMap R B m n) (koszulDifferential r n) =
      (koszulDifferential (fun i => algebraMap R B (r i)) n).restrictScalars R := by
  let := isLocalizedModule_koszulTermAlgebraMap R B S m (n + 1)
  let := isLocalizedModule_koszulTermAlgebraMap R B S m n
  refine IsLocalizedModule.linearMap_ext S (koszulTermAlgebraMap R B m (n + 1))
    (koszulTermAlgebraMap R B m n) ?_
  rw [IsLocalizedModule.map_comp]
  exact koszulTermAlgebraMap_comp_differential R B r n

end LocalizedTerms

/-! ### The graph sequence over the polynomial ring -/

section GraphPolynomial

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {A : Type*} [CommRing A] {m : ℕ}

/-- **Positive-degree exactness of the graph-sequence Koszul complex** (paper
Lemma 5.1 clause 1 at the polynomial level): for `g : A` and `f : Fin m → A` with
`Ideal.span ({g} ∪ Set.range f) = ⊤`, the Koszul complex of the graph sequence
`r i = C g * X i - C (f i)` in `MvPolynomial (Fin m) A` is exact at `K_{q+1}` for
every `q : ℕ`.

The proof checks exactness after inverting each member of the spanning family
`{C g} ∪ {r i}` of `MvPolynomial (Fin m) A` (`exact_of_isLocalized_span`): inverting
`r j` makes the complex contractible, and inverting `C g` identifies the localization
with `MvPolynomial (Fin m) (Localization.Away g)`, where the graph sequence is a unit
times a translate of the coordinate sequence. -/
theorem koszulGraph_polynomial_exact (g : A) (f : Fin m → A)
    (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤) (q : ℕ) :
    Function.Exact
      (koszulDifferential
        (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) A)) (q + 1))
      (koszulDifferential (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) A)) q) := by
  classical
  -- extract a linear combination `cc 0 * g + ∑ cc k.succ * f k = 1` from `hunit`
  have h1mem : (1 : A) ∈ Ideal.span ({g} ∪ Set.range f) := hunit ▸ Submodule.mem_top
  rw [Set.singleton_union, ← Fin.range_cons g f] at h1mem
  obtain ⟨cc, hcc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1mem
  rw [Fin.sum_univ_succ] at hcc
  simp only [Fin.cons_zero, Fin.cons_succ] at hcc
  -- the key polynomial identity: `1` is a combination of `C g` and the `r i`
  have hkey : (C g : MvPolynomial (Fin m) A) * (C (cc 0) + ∑ k, C (cc k.succ) * X k) -
      ∑ k, C (cc k.succ) * (C g * X k - C (f k)) = 1 := by
    have h1 : (C (cc 0 * g + ∑ k, cc k.succ * f k) : MvPolynomial (Fin m) A) = 1 := by
      rw [hcc, map_one]
    rw [map_add, map_mul, map_sum] at h1
    simp only [map_mul] at h1
    rw [← h1, mul_add, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib,
      mul_comm (C g) (C (cc 0))]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  -- the spanning family
  have spn : Ideal.span ({(C g : MvPolynomial (Fin m) A)} ∪
      Set.range fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) A)) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hkey]
    refine Submodule.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
      (Submodule.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    · exact Set.mem_union_left _ rfl
    · exact Set.mem_union_right _ ⟨k, rfl⟩
  set s : Set (MvPolynomial (Fin m) A) :=
    {C g} ∪ Set.range fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) A) with hs
  let hloc : ∀ (n : ℕ) (t : s), IsLocalizedModule.Away t.1
      (koszulTermAlgebraMap (MvPolynomial (Fin m) A) (Localization.Away t.1) m n) :=
    fun n t => isLocalizedModule_koszulTermAlgebraMap _ _ (Submonoid.powers t.1) m n
  refine exact_of_isLocalized_span s spn _
    (fun t => koszulTermAlgebraMap _ (Localization.Away t.1) m (q + 1 + 1)) _
    (fun t => koszulTermAlgebraMap _ (Localization.Away t.1) m (q + 1)) _
    (fun t => koszulTermAlgebraMap _ (Localization.Away t.1) m q) _ _ fun t => ?_
  rw [isLocalizedModule_map_koszulDifferential, isLocalizedModule_map_koszulDifferential]
  simp only [Function.Exact, LinearMap.coe_restrictScalars]
  obtain ⟨t, ht⟩ := t
  rcases ht with ht | ⟨j, rfl⟩
  · -- inverting `C g`: transport from `MvPolynomial (Fin m) (Localization.Away g)`
    rw [Set.mem_singleton_iff] at ht
    subst ht
    let hlocg : IsLocalization
        (Submonoid.powers ((C g : MvPolynomial (Fin m) A)))
        (MvPolynomial (Fin m) (Localization.Away g)) := by
      rw [← Submonoid.map_powers (C : A →+* MvPolynomial (Fin m) A) g]
      exact MvPolynomial.isLocalization _ _
    refine koszulDifferential_exact_congr
      (IsLocalization.algEquiv (Submonoid.powers ((C g : MvPolynomial (Fin m) A)))
        (MvPolynomial (Fin m) (Localization.Away g))
        (Localization.Away ((C g : MvPolynomial (Fin m) A)))).toRingEquiv
      (r := fun i => algebraMap (MvPolynomial (Fin m) A)
        (MvPolynomial (Fin m) (Localization.Away g)) (C g * X i - C (f i)))
      (fun i => by
        rw [AlgEquiv.coe_ringEquiv]
        exact (AlgEquiv.commutes _ _).symm) q ?_
    have hseq0 : (fun i => algebraMap (MvPolynomial (Fin m) A)
        (MvPolynomial (Fin m) (Localization.Away g)) (C g * X i - C (f i))) =
        fun i => C (algebraMap A (Localization.Away g) g) * X i -
          C (algebraMap A (Localization.Away g) (f i)) := by
      funext i
      rw [MvPolynomial.algebraMap_def, map_sub, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, MvPolynomial.map_C]
    rw [hseq0]
    exact koszulGraph_exact_of_isUnit_base
      (IsLocalization.map_units (Localization.Away g) ⟨g, Submonoid.mem_powers g⟩) _ q
  · -- inverting `r j`: the complex is contractible
    exact koszulDifferential_exact_of_isUnit (j := j)
      (IsLocalization.map_units (Localization.Away _)
        ⟨_, Submonoid.mem_powers ((C g * X j - C (f j) : MvPolynomial (Fin m) A))⟩) q

end GraphPolynomial

end FiniteJet.KoszulFree
