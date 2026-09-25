/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.ZMod.Basic

/-!
# Basic
-/

@[expose] public section

open scoped BigOperators

namespace EGZ

/-- The vector space `𝔽_p^d`, represented as `d`-tuples over `ZMod p`.

The definitions are total for every natural number `p`.  Results using the
field structure will carry a primality hypothesis. -/
abbrev FpVec (p d : ℕ) := Fin d → ZMod p

/-- A sequence contains `p` terms, at distinct positions, whose sum is zero. -/
def HasZeroSumSubsequence {ι : Type*} (p : ℕ) {d : ℕ}
    (a : ι → FpVec p d) : Prop :=
  ∃ I : Finset ι, I.card = p ∧ ∑ i ∈ I, a i = 0

/-- Every sequence of exactly `n` vectors in `𝔽_p^d` has a zero-sum
subsequence of length `p`. -/
def EGZProperty (p d n : ℕ) : Prop :=
  ∀ a : Fin n → FpVec p d, HasZeroSumSubsequence p a

/-- A family `v₁, ..., vₛ` is `p`-hollow when the only nonnegative integer
combinations of total weight `p` that sum to zero put all their weight on a
single vector.  For prime `p`, this condition forces `v` to be injective. -/
def IsPHollow (p : ℕ) {d s : ℕ} (v : Fin s → FpVec p d) : Prop :=
  ∀ α : Fin s → ℕ,
    (∑ i, α i) = p →
      ((∑ i, α i • v i) = 0 ↔ ∃ i, α i = p)

/-- There is a `p`-hollow family of `s` vectors in `𝔽_p^d`. -/
def AdmitsPHollowLength (p d s : ℕ) : Prop :=
  ∃ v : Fin s → FpVec p d, IsPHollow p v

namespace FpVec

/-- The cardinality of `𝔽_p^d` (when `p` is nonzero, as it is for primes). -/
theorem card (p d : ℕ) [NeZero p] : Fintype.card (FpVec p d) = p ^ d := by
  simp [FpVec, ZMod.card]

/-- Every vector in `𝔽_p^d` is killed by `p`.  This also holds for the
degenerate value `p = 0`, for which `ZMod 0` is represented by the integers. -/
theorem characteristic_nsmul (p : ℕ) {d : ℕ} (x : FpVec p d) : p • x = 0 := by
  funext j
  simp [nsmul_eq_mul]

end FpVec

namespace IsPHollow

/-- A `p`-hollow parametrization has no repetitions once `p ≥ 2`. -/
theorem injective {p d s : ℕ} {v : Fin s → FpVec p d}
    (hv : IsPHollow p v) (hp : 2 ≤ p) : Function.Injective v := by
  classical
  intro i j hij
  by_contra hne
  let α : Fin s → ℕ := fun k ↦
    (if k = i then p - 1 else 0) + (if k = j then 1 else 0)
  have hji : j ≠ i := Ne.symm hne
  have hsum : (∑ k, α k) = p := by
    rw [show (∑ k, α k) =
        (∑ k, if k = i then p - 1 else 0) +
          ∑ k, if k = j then 1 else 0 by simp [α, Finset.sum_add_distrib]]
    simp only [Fintype.sum_ite_eq']
    omega
  have hzero : (∑ k, α k • v k) = 0 := by
    calc
      (∑ k, α k • v k) =
          (∑ k, (if k = i then p - 1 else 0) • v k) +
            ∑ k, (if k = j then 1 else 0) • v k := by
              simp only [α, add_nsmul, Finset.sum_add_distrib]
      _ = (p - 1) • v i + 1 • v j := by
        simp only [ite_smul, zero_smul, Fintype.sum_ite_eq']
      _ = 0 := by
        rw [← hij, ← add_nsmul]
        have hpred : p - 1 + 1 = p := by omega
        rw [hpred]
        exact FpVec.characteristic_nsmul p (v i)
  obtain ⟨k, hk⟩ := (hv α hsum).mp hzero
  by_cases hki : k = i
  · subst k
    simp [α, hne] at hk
    omega
  · by_cases hkj : k = j
    · subst k
      simp [α, hji] at hk
      omega
    · simp [α, hki, hkj] at hk
      omega

/-- A prime-field `p`-hollow family has at most all the vectors in the space. -/
theorem card_le {p d s : ℕ} {v : Fin s → FpVec p d}
    (hv : IsPHollow p v) (hp : Nat.Prime p) : s ≤ p ^ d := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [← Fintype.card_fin s, ← FpVec.card p d]
  exact Fintype.card_le_of_injective v (hv.injective hp.two_le)

/-- Operational form of hollowness: a `p`-term sum of members of a hollow
family vanishes exactly when all `p` selected members have the same index.

The indexing type is arbitrary; the cardinality hypothesis is what records
that the sum has exactly `p` terms. -/
theorem sum_eq_zero_iff_constant {p d s : ℕ} {v : Fin s → FpVec p d}
    (hv : IsPHollow p v) {κ : Type*} [Fintype κ]
    (hcard : Fintype.card κ = p) (f : κ → Fin s) :
    (∑ x, v (f x)) = 0 ↔ ∃ i, ∀ x, f x = i := by
  classical
  let α : Fin s → ℕ := fun i ↦ (Finset.univ.filter fun x : κ ↦ f x = i).card
  have hsum : (∑ i, α i) = p := by
    have hfiber : (Finset.univ : Finset κ).card = ∑ i, α i := by
      simpa only [α] using
        (Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset κ)) (t := (Finset.univ : Finset (Fin s)))
          (f := f) (by simp))
    calc
      (∑ i, α i) = (Finset.univ : Finset κ).card := hfiber.symm
      _ = Fintype.card κ := Finset.card_univ
      _ = p := hcard
  have hrewrite : (∑ i, α i • v i) = ∑ x, v (f x) := by
    calc
      (∑ i, α i • v i) =
          ∑ i ∈ (Finset.univ : Finset (Fin s)),
            ∑ x ∈ (Finset.univ : Finset κ) with f x = i, v i := by
              simp only [α, Finset.sum_const]
      _ = ∑ i ∈ (Finset.univ : Finset (Fin s)),
            ∑ x ∈ (Finset.univ : Finset κ) with f x = i, v (f x) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro x hx
              exact congrArg v (Finset.mem_filter.mp hx).2.symm
      _ = ∑ x, v (f x) := by
        simpa only using
          (Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset κ)) (t := (Finset.univ : Finset (Fin s)))
            (g := f) (by simp) (fun x ↦ v (f x)))
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := (hv α hsum).mp (hrewrite.trans hz)
    refine ⟨i, fun x ↦ ?_⟩
    have hle : (Finset.univ : Finset κ).card ≤
        (Finset.univ.filter fun x : κ ↦ f x = i).card := by
      simpa [α, hcard] using hi.symm.le
    have heq : (Finset.univ.filter fun x : κ ↦ f x = i) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hle
    have hx : x ∈ (Finset.univ.filter fun x : κ ↦ f x = i) := by
      rw [heq]
      simp
    exact (Finset.mem_filter.mp hx).2
  · rintro ⟨i, hi⟩
    calc
      (∑ x, v (f x)) = ∑ _x : κ, v i := by
        apply Fintype.sum_congr
        intro x
        rw [hi x]
      _ = Fintype.card κ • v i := by simp
      _ = p • v i := by rw [hcard]
      _ = 0 := FpVec.characteristic_nsmul p (v i)

/-- The common special case of `sum_eq_zero_iff_constant` indexed by `Fin p`. -/
theorem sum_fin_eq_zero_iff_constant {p d s : ℕ} {v : Fin s → FpVec p d}
    (hv : IsPHollow p v) (f : Fin p → Fin s) :
    (∑ x, v (f x)) = 0 ↔ ∃ i, ∀ x, f x = i :=
  hv.sum_eq_zero_iff_constant (by simp) f

end IsPHollow

/-- The existence predicate for hollow families inherits the ambient cardinality bound. -/
theorem AdmitsPHollowLength.le_pow {p d s : ℕ} (hp : Nat.Prime p)
    (h : AdmitsPHollowLength p d s) : s ≤ p ^ d := by
  obtain ⟨v, hv⟩ := h
  exact hv.card_le hp

/-- The empty family is hollow for every positive modulus. -/
theorem admitsPHollowLength_zero {p d : ℕ} (hp : 0 < p) :
    AdmitsPHollowLength p d 0 := by
  refine ⟨Fin.elim0, ?_⟩
  intro α hsum
  simp at hsum
  omega

namespace EGZProperty

/-- Exact-length EGZ properties persist when more terms are appended. -/
theorem mono {p d m n : ℕ} (hmn : m ≤ n)
    (hm : EGZProperty p d m) : EGZProperty p d n := by
  intro a
  obtain ⟨I, hIcard, hIz⟩ := hm (fun i ↦ a (Fin.castLE hmn i))
  refine ⟨I.map (Fin.castLEEmb hmn), ?_, ?_⟩
  · simpa only [Finset.card_map] using hIcard
  · simpa only [Finset.sum_map, Fin.castLEEmb_apply] using hIz

/-- A crude pigeonhole upper bound.  It is not intended to be sharp; its role
is to establish that the least EGZ length is well-defined. -/
theorem pigeonhole_bound (p d : ℕ) :
    EGZProperty p d ((p - 1) * p ^ d + 1) := by
  by_cases hp0 : p = 0
  · subst p
    intro a
    refine ⟨∅, by simp, ?_⟩
    simp
  · let : NeZero p := ⟨hp0⟩
    intro a
    have hpigeon : Fintype.card (FpVec p d) * (p - 1) <
        Fintype.card (Fin ((p - 1) * p ^ d + 1)) := by
      simp only [FpVec.card, Fintype.card_fin]
      rw [Nat.mul_comm (p ^ d) (p - 1)]
      omega
    obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card a hpigeon
    have hp_le : p ≤ (Finset.univ.filter fun i ↦ a i = y).card := by omega
    obtain ⟨I, hI, hIcard⟩ := Finset.exists_subset_card_eq hp_le
    refine ⟨I, hIcard, ?_⟩
    calc
      (∑ i ∈ I, a i) = ∑ _i ∈ I, y := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mem_filter.mp (hI hi)).2
      _ = I.card • y := Finset.sum_const y
      _ = p • y := by rw [hIcard]
      _ = 0 := FpVec.characteristic_nsmul p y

end EGZProperty

/-- Some exact length has the EGZ property, uniformly for all natural `p`. -/
theorem exists_egzProperty (p d : ℕ) : ∃ n, EGZProperty p d n :=
  ⟨(p - 1) * p ^ d + 1, EGZProperty.pigeonhole_bound p d⟩

/-- Repeating each member of a positive-modulus hollow family only `p - 1`
times gives a sequence with no `p`-term zero sum. -/
theorem not_egzProperty_of_admitsPHollowLength {p d s : ℕ} (hp : 0 < p)
    (hadm : AdmitsPHollowLength p d s) : ¬ EGZProperty p d (s * (p - 1)) := by
  classical
  obtain ⟨v, hv⟩ := hadm
  let e : Fin s × Fin (p - 1) ≃ Fin (s * (p - 1)) :=
    Fintype.equivOfCardEq (by simp)
  let a : Fin (s * (p - 1)) → FpVec p d := fun j ↦ v (e.symm j).1
  intro hEGZ
  obtain ⟨I, hIcard, hIzero⟩ := hEGZ a
  let f : I → Fin s := fun x ↦ (e.symm x.1).1
  have hcoeCard : Fintype.card I = p := by
    simpa only [Fintype.card_coe] using hIcard
  have hfzero : (∑ x, v (f x)) = 0 := by
    rw [← Finset.sum_attach] at hIzero
    simpa only [Finset.attach_eq_univ, f, a] using hIzero
  obtain ⟨i, hi⟩ := (hv.sum_eq_zero_iff_constant hcoeCard f).mp hfzero
  let g : I → Fin (p - 1) := fun x ↦ (e.symm x.1).2
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply e.symm.injective
    apply Prod.ext
    · simpa only [f] using (hi x).trans (hi y).symm
    · exact hxy
  have hbad := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_coe, Fintype.card_fin, hIcard] at hbad
  omega

end EGZ
