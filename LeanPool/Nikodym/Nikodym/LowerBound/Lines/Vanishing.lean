/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Jets

/-!
# The q−1 nonzero roots force a line identity

This file implements blueprint node **L02** of the lower-bound side of the sharp finite-field
Nikodym exponent.

A univariate polynomial of degree strictly less than `r (q - 1)` which is divisible by
`(T - ι(a))^r` for every nonzero `a ∈ F` must vanish. Combined with L01, a polynomial of total
degree at most `r (q - 1) - 1` that satisfies the non-private jet conditions along a line
restricts identically to zero on that line.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint L02: if `(X - a i)^r` divides `f` for pairwise distinct `a i`, and
`deg f < r · |s|`, then `f = 0`. -/
theorem eq_zero_of_dvd_pow_sub_C {ι : Type*} (s : Finset ι) (a : ι → K) (ha : Set.InjOn a s)
    (r : ℕ) {f : Polynomial K} (hdeg : f.natDegree < r * s.card)
    (hdvd : ∀ i ∈ s, (Polynomial.X - Polynomial.C (a i)) ^ r ∣ f) : f = 0 := by
  set p := ∏ i ∈ s, (Polynomial.X - Polynomial.C (a i)) ^ r
  have hp_dvd : p ∣ f := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro i hi j hj hij
    exact (Polynomial.pairwise_coprime_X_sub_C Function.injective_id (ha.ne hi hj hij)).pow
  have hfactor : ∀ i ∈ s, ((Polynomial.X - Polynomial.C (a i)) ^ r).Monic :=
    fun i _ ↦ (Polynomial.monic_X_sub_C _).pow r
  have hp_deg : p.natDegree = r * s.card := by
    rw [Polynomial.natDegree_prod_of_monic s _ hfactor]
    simp [Finset.sum_const, mul_comm]
  by_contra hf
  have hle : p.natDegree ≤ f.natDegree := Polynomial.natDegree_le_of_dvd hp_dvd hf
  rw [hp_deg] at hle
  exact (hle.trans_lt hdeg).false

variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

/-- Blueprint L02: if `(T - ι(a))^r` divides `f` for every nonzero `a ∈ F` and
`deg f < r (q - 1)`, then `f = 0`. -/
theorem eq_zero_of_dvd_nonzero {f : Polynomial K} (r : ℕ)
    (hdeg : f.natDegree < r * (Fintype.card F - 1))
    (hdvd : ∀ a : F, a ≠ 0 → (Polynomial.X - Polynomial.C (algebraMap F K a)) ^ r ∣ f) :
    f = 0 := by
  classical
  let s := Finset.univ.erase (0 : F)
  have hcard : s.card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  refine eq_zero_of_dvd_pow_sub_C s (algebraMap F K) ?_ r ?_ ?_
  · exact Set.injOn_of_injective (algebraMap F K).injective
  · rwa [hcard]
  · intro a ha
    exact hdvd a (Finset.ne_of_mem_erase ha)

/-- Blueprint L02: a polynomial of total degree at most `r (q - 1) - 1` which lies in every
non-private jet along the line `T ↦ b + T v` restricts to the zero polynomial. -/
theorem lineRes_eq_zero_of_jets (b v : Fin d → F) {I : Ideal (MvPolynomial (Fin d) K)}
    (hI : I ≤ lineIdeal (liftPt b) (liftPt v)) (r : ℕ) {g : MvPolynomial (Fin d) K}
    (hdeg : g.totalDegree ≤ r * (Fintype.card F - 1) - 1)
    (hr : 1 ≤ r * (Fintype.card F - 1))
    (hg : ∀ a : F, a ≠ 0 → g ∈ jetIdeal I (liftPt (b + a • v)) r) :
    lineRes (liftPt b) (liftPt v) g = 0 := by
  refine eq_zero_of_dvd_nonzero r ?_ fun a ha ↦
    dvd_lineRes_of_mem_jetIdeal_liftPt b v a hI r (hg a ha)
  refine (natDegree_lineRes_le (liftPt b) (liftPt v) g).trans_lt ?_
  omega

/-- Blueprint L02: the membership form of `lineRes_eq_zero_of_jets`. -/
theorem mem_lineIdeal_of_jets (b v : Fin d → F) {I : Ideal (MvPolynomial (Fin d) K)}
    (hI : I ≤ lineIdeal (liftPt b) (liftPt v)) (r : ℕ) {g : MvPolynomial (Fin d) K}
    (hdeg : g.totalDegree ≤ r * (Fintype.card F - 1) - 1)
    (hr : 1 ≤ r * (Fintype.card F - 1))
    (hg : ∀ a : F, a ≠ 0 → g ∈ jetIdeal I (liftPt (b + a • v)) r) :
    g ∈ lineIdeal (liftPt b) (liftPt v) :=
  mem_lineIdeal.mpr (lineRes_eq_zero_of_jets b v hI r hdeg hr hg)

/-- Blueprint L02: `lineRes_eq_zero_of_jets` with the degree bound packaged as membership in
`P_{d, ≤ r(q-1)-1}`. -/
theorem lineRes_eq_zero_of_jets_restrictTotalDegree (b v : Fin d → F)
    {I : Ideal (MvPolynomial (Fin d) K)} (hI : I ≤ lineIdeal (liftPt b) (liftPt v)) (r : ℕ)
    {g : MvPolynomial (Fin d) K}
    (hdeg : g ∈ restrictTotalDegree (Fin d) K (r * (Fintype.card F - 1) - 1))
    (hr : 1 ≤ r * (Fintype.card F - 1))
    (hg : ∀ a : F, a ≠ 0 → g ∈ jetIdeal I (liftPt (b + a • v)) r) :
    lineRes (liftPt b) (liftPt v) g = 0 :=
  lineRes_eq_zero_of_jets b v hI r (mem_restrictTotalDegree_iff.mp hdeg) hr hg

/-- Blueprint L02: the membership form of `lineRes_eq_zero_of_jets_restrictTotalDegree`. -/
theorem mem_lineIdeal_of_jets_restrictTotalDegree (b v : Fin d → F)
    {I : Ideal (MvPolynomial (Fin d) K)} (hI : I ≤ lineIdeal (liftPt b) (liftPt v)) (r : ℕ)
    {g : MvPolynomial (Fin d) K}
    (hdeg : g ∈ restrictTotalDegree (Fin d) K (r * (Fintype.card F - 1) - 1))
    (hr : 1 ≤ r * (Fintype.card F - 1))
    (hg : ∀ a : F, a ≠ 0 → g ∈ jetIdeal I (liftPt (b + a • v)) r) :
    g ∈ lineIdeal (liftPt b) (liftPt v) :=
  mem_lineIdeal.mpr (lineRes_eq_zero_of_jets_restrictTotalDegree b v hI r hdeg hr hg)

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
