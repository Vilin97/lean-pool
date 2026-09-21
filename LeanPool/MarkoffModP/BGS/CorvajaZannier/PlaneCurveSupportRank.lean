/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSupportDeterminant
import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems
import Mathlib.GroupTheory.Archimedean
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

/-!
# Absolute irreducibility forces rank-two torus support

This file proves the support-lattice bridge needed by the diagonal-stabilizer
route to the Corvaja--Zannier powered-image index bound.  A collinear finite
support lies in a translate of a cyclic subgroup of `ℤ²`; the corresponding
plane polynomial is a monomial times a directional homogenization of a
univariate polynomial.  Over an algebraically closed field, irreducibility
forces that univariate polynomial to have degree one, so a nonzero torus
character is constant on the curve.  This contradicts the semantic
`TorusCurveNotSubtorusTranslate` hypothesis.
-/

namespace BGS.CorvajaZannier

noncomputable section

private def integerVectorDet (u v : Fin 2 → ℤ) : ℤ :=
  u 0 * v 1 - u 1 * v 0

private def integerVectorLine (d : Fin 2 → ℤ) : AddSubgroup (Fin 2 → ℤ) where
  carrier := {w | integerVectorDet d w = 0}
  zero_mem' := by simp [integerVectorDet]
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq] at hu hv ⊢
    simp only [integerVectorDet] at hu hv
    simp only [integerVectorDet, Pi.add_apply]
    linear_combination hu + hv
  neg_mem' := by
    intro u hu
    simp only [Set.mem_setOf_eq] at hu ⊢
    simp only [integerVectorDet] at hu
    simp only [integerVectorDet, Pi.neg_apply]
    linear_combination -hu

private def integerCoordinate (i : Fin 2) : (Fin 2 → ℤ) →+ ℤ where
  toFun w := w i
  map_zero' := rfl
  map_add' _ _ := rfl

private def integerCoordinateOnLine (d : Fin 2 → ℤ) (i : Fin 2) :
    integerVectorLine d →+ (integerVectorLine d).map (integerCoordinate i) where
  toFun w := by
    refine ⟨integerCoordinate i w.1, ?_⟩
    change ∃ x, x ∈ integerVectorLine d ∧
      integerCoordinate i x = integerCoordinate i w.1
    exact ⟨w.1, w.2, rfl⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

private theorem integerCoordinate_zero_injectiveOn_integerVectorLine
    {d : Fin 2 → ℤ} (hi : d 0 ≠ 0) :
    Function.Injective
      ((integerCoordinate 0).comp (integerVectorLine d).subtype) := by
  intro u v huv
  apply Subtype.ext
  funext j
  have hj : j = 0 ∨ j = 1 := by
    have hjlt := j.isLt
    omega
  rcases hj with rfl | rfl
  · exact huv
  · have hu := u.property
    have hv := v.property
    change d 0 * u.1 1 - d 1 * u.1 0 = 0 at hu
    change d 0 * v.1 1 - d 1 * v.1 0 = 0 at hv
    dsimp [integerCoordinate] at huv
    have hmul : d 0 * u.1 1 = d 0 * v.1 1 := by
      calc
        d 0 * u.1 1 = d 1 * u.1 0 := by omega
        _ = d 1 * v.1 0 := by rw [huv]
        _ = d 0 * v.1 1 := by omega
    exact (mul_left_cancel₀ hi hmul)

private theorem integerCoordinate_one_injectiveOn_integerVectorLine
    {d : Fin 2 → ℤ} (hi : d 1 ≠ 0) :
    Function.Injective
      ((integerCoordinate 1).comp (integerVectorLine d).subtype) := by
  intro u v huv
  apply Subtype.ext
  funext j
  have hj : j = 0 ∨ j = 1 := by
    have hjlt := j.isLt
    omega
  rcases hj with rfl | rfl
  · have hu := u.property
    have hv := v.property
    change d 0 * u.1 1 - d 1 * u.1 0 = 0 at hu
    change d 0 * v.1 1 - d 1 * v.1 0 = 0 at hv
    dsimp [integerCoordinate] at huv
    have hmul : d 1 * u.1 0 = d 1 * v.1 0 := by
      calc
        d 1 * u.1 0 = d 0 * u.1 1 := by omega
        _ = d 0 * v.1 1 := by rw [huv]
        _ = d 1 * v.1 0 := by omega
    exact (mul_left_cancel₀ hi hmul)
  · exact huv

private theorem integerVectorLine_cyclic {d : Fin 2 → ℤ} (hd : d ≠ 0) :
    ∃ v : Fin 2 → ℤ, ∀ w : Fin 2 → ℤ,
      integerVectorDet d w = 0 → ∃ k : ℤ, w = k • v := by
  have hcoord : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
    by_cases h0 : d 0 = 0
    · right
      intro h1
      apply hd
      funext i
      have hi : i = 0 ∨ i = 1 := by
        have hilt := i.isLt
        omega
      rcases hi with rfl | rfl
      · exact h0
      · exact h1
    · exact Or.inl h0
  obtain ⟨i, hi, hinj⟩ : ∃ i : Fin 2, d i ≠ 0 ∧
      Function.Injective
        ((integerCoordinate i).comp (integerVectorLine d).subtype) := by
    rcases hcoord with h | h
    · exact ⟨0, h, integerCoordinate_zero_injectiveOn_integerVectorLine h⟩
    · exact ⟨1, h, integerCoordinate_one_injectiveOn_integerVectorLine h⟩
  let L := integerVectorLine d
  let phi : L →+ L.map (integerCoordinate i) := integerCoordinateOnLine d i
  have hphi_inj : Function.Injective phi := by
    intro u v huv
    apply hinj
    exact congrArg Subtype.val huv
  have hphi_surj : Function.Surjective phi := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, hwz⟩ := hz
    refine ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    exact hwz
  let e : L ≃+ L.map (integerCoordinate i) :=
    AddEquiv.ofBijective phi ⟨hphi_inj, hphi_surj⟩
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic (L.map (integerCoordinate i))
  have ha_mem : a ∈ L.map (integerCoordinate i) := by
    rw [ha]
    exact AddSubgroup.subset_closure (Set.mem_singleton a)
  let vL : L := e.symm ⟨a, ha_mem⟩
  refine ⟨vL.1, ?_⟩
  intro w hw
  have wmem : w ∈ L := hw
  let wL : L := ⟨w, wmem⟩
  have hew_mem : (e wL : ℤ) ∈ AddSubgroup.closure {a} := by
    rw [← ha]
    exact (e wL).property
  obtain ⟨k, hk⟩ := AddSubgroup.mem_closure_singleton.mp hew_mem
  refine ⟨k, ?_⟩
  have heq : wL = k • vL := by
    apply e.injective
    apply Subtype.ext
    simpa [vL] using hk.symm
  exact congrArg Subtype.val heq

private def planeExponentDifference
    (r s : Fin 2 →₀ ℕ) : Fin 2 → ℤ :=
  fun i => (s i : ℤ) - (r i : ℤ)

private theorem integerVectorDet_planeExponentDifference
    (r s t : Fin 2 →₀ ℕ) :
    integerVectorDet (planeExponentDifference r s)
        (planeExponentDifference r t) =
      planeCurveSupportDifferenceDet r s t := by
  rfl

theorem exists_support_direction_of_not_rankTwo
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    {r : Fin 2 →₀ ℕ} (hr : r ∈ f.support)
    (hnrank : ¬ PlaneCurveSupportHasRankTwo f)
    (hnonsingleton : ∃ s ∈ f.support, s ≠ r) :
    ∃ v : Fin 2 → ℤ, v ≠ 0 ∧
      ∀ s ∈ f.support, ∃ k : ℤ,
        planeExponentDifference r s = k • v := by
  obtain ⟨s, hs, hsr⟩ := hnonsingleton
  have hd : planeExponentDifference r s ≠ 0 := by
    intro h
    apply hsr
    apply Finsupp.ext
    intro i
    have hi := congrFun h i
    dsimp [planeExponentDifference] at hi
    omega
  obtain ⟨v, hv⟩ := integerVectorLine_cyclic hd
  have hparam : ∀ t ∈ f.support, ∃ k : ℤ,
      planeExponentDifference r t = k • v := by
    intro t ht
    apply hv
    rw [integerVectorDet_planeExponentDifference]
    by_contra hdet
    exact hnrank ⟨r, s, t, hr, hs, ht, hdet⟩
  have hvne : v ≠ 0 := by
    obtain ⟨k, hk⟩ := hparam s hs
    intro hv0
    apply hd
    simpa [hv0] using hk
  exact ⟨v, hvne, hparam⟩

private def intVectorPositive (v : Fin 2 → ℤ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (v i).toNat)

private def intVectorNegative (v : Fin 2 → ℤ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (-v i).toNat)

@[simp] private theorem intVectorPositive_apply (v : Fin 2 → ℤ) (i : Fin 2) :
    intVectorPositive v i = (v i).toNat := by
  simp [intVectorPositive]

@[simp] private theorem intVectorNegative_apply (v : Fin 2 → ℤ) (i : Fin 2) :
    intVectorNegative v i = (-v i).toNat := by
  simp [intVectorNegative]

private theorem intVectorPositive_sub_negative (v : Fin 2 → ℤ) (i : Fin 2) :
    (intVectorPositive v i : ℤ) - (intVectorNegative v i : ℤ) = v i := by
  simp only [intVectorPositive_apply, intVectorNegative_apply]
  rw [Int.ofNat_toNat, Int.ofNat_toNat]
  rcases le_total 0 (v i) with hvi | hvi
  · simp [hvi, neg_nonpos.mpr hvi]
  · simp [hvi]

private def directionalHomogenization {A : Type*} [CommSemiring A]
    (v : Fin 2 → ℤ) (p : Polynomial A) (n : ℕ) :
    MvPolynomial (Fin 2) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.monomial (intVectorPositive v) 1,
      MvPolynomial.monomial (intVectorNegative v) 1]
    (p.homogenize n)

private theorem directionalHomogenization_monomial
    {A : Type*} [CommSemiring A] (v : Fin 2 → ℤ)
    {k n : ℕ} (hkn : k ≤ n) (c : A) :
    directionalHomogenization v (Polynomial.monomial k c) n =
      MvPolynomial.monomial
        (k • intVectorPositive v + (n - k) • intVectorNegative v) c := by
  rw [directionalHomogenization, Polynomial.homogenize_monomial hkn]
  rw [MvPolynomial.eval₂Hom_monomial]
  simp [Finsupp.prod_fintype, Fin.prod_univ_two,
    MvPolynomial.monomial_pow, MvPolynomial.monomial_mul,
    MvPolynomial.C_mul_monomial]

private theorem directionalHomogenization_mul
    {A : Type*} [CommSemiring A] (v : Fin 2 → ℤ)
    (p q : Polynomial A) {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    directionalHomogenization v (p * q) (m + n) =
      directionalHomogenization v p m * directionalHomogenization v q n := by
  rw [directionalHomogenization, Polynomial.homogenize_mul p q hp hq]
  exact map_mul _ _ _

private def directionalExponent (v : Fin 2 → ℤ) (N k : ℕ) : Fin 2 →₀ ℕ :=
  k • intVectorPositive v + (N - k) • intVectorNegative v

private theorem directionalHomogenization_not_isUnit
    {A : Type*} [Field A] {v : Fin 2 → ℤ} (hvne : v ≠ 0)
    {q : Polynomial A} {N : ℕ} (hN : 0 < N)
    (hqdeg : q.natDegree = N) (hq0 : q.coeff 0 ≠ 0) :
    ¬ IsUnit (directionalHomogenization v q N) := by
  let H := directionalHomogenization v q N
  have hsum : H = ∑ k ∈ Finset.range (N + 1),
      MvPolynomial.monomial (directionalExponent v N k) (q.coeff k) := by
    have hqsum : q = ∑ k ∈ Finset.range (N + 1),
        Polynomial.monomial k (q.coeff k) := by
      simpa [hqdeg] using q.as_sum_range
    calc
      H = directionalHomogenization v q N := rfl
      _ = directionalHomogenization v
          (∑ k ∈ Finset.range (N + 1),
            Polynomial.monomial k (q.coeff k)) N := by rw [← hqsum]
      _ = ∑ k ∈ Finset.range (N + 1),
          directionalHomogenization v (Polynomial.monomial k (q.coeff k)) N := by
        simp only [directionalHomogenization,
          Polynomial.homogenize_finsetSum, map_sum]
      _ = ∑ k ∈ Finset.range (N + 1),
          MvPolynomial.monomial (directionalExponent v N k) (q.coeff k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [directionalHomogenization_monomial]
        · rfl
        · exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, v i ≠ 0 := by
    by_contra h
    apply hvne
    funext i
    exact Classical.not_not.mp (not_exists.mp h i)
  have coeff_sum (e : Fin 2 →₀ ℕ) :
      (∑ k ∈ Finset.range (N + 1),
        MvPolynomial.monomial (directionalExponent v N k) (q.coeff k)).coeff e =
      ∑ k ∈ Finset.range (N + 1),
        (MvPolynomial.monomial (directionalExponent v N k) (q.coeff k)).coeff e := by
    have coeff_finset_sum (S : Finset ℕ)
        (g : ℕ → MvPolynomial (Fin 2) A) :
        (∑ k ∈ S, g k).coeff e = ∑ k ∈ S, (g k).coeff e := by
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih => simp [ha, ih]
    exact coeff_finset_sum _ _
  have htop : q.coeff N ≠ 0 := by
    rw [← hqdeg]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr fun hq => hq0 (by simp [hq])
  rcases lt_or_gt_of_ne hi.symm with hvi | hvi
  · have hpos : 0 < intVectorPositive v i := by
      simp only [intVectorPositive_apply]
      apply Nat.pos_of_ne_zero
      intro hz
      have := Int.toNat_eq_zero.mp hz
      omega
    have hneg : intVectorNegative v i = 0 := by
      simp [Int.toNat_of_nonpos (neg_nonpos.mpr (le_of_lt hvi))]
    let e : Fin 2 →₀ ℕ := N • intVectorPositive v
    have hcoeff : H.coeff e = q.coeff N := by
      rw [hsum, coeff_sum e, Finset.sum_eq_single N]
      · rw [MvPolynomial.coeff_monomial]
        simp [e, directionalExponent]
      · intro k hk hkN
        rw [MvPolynomial.coeff_monomial]
        split_ifs with heq
        · have hcoord := congrArg (fun d : Fin 2 →₀ ℕ => d i) heq
          dsimp [e] at hcoord
          simp only [directionalExponent, Finsupp.add_apply, Finsupp.smul_apply,
            nsmul_eq_mul] at hcoord
          rw [hneg] at hcoord
          simp only [mul_zero, add_zero] at hcoord
          exact (hkN (Nat.eq_of_mul_eq_mul_right hpos hcoord)).elim
        · rfl
      · simp
    have he_mem : e ∈ H.support := MvPolynomial.mem_support_iff.mpr (hcoeff ▸ htop)
    have hei : 0 < e i := by
      simp only [e, Finsupp.smul_apply, nsmul_eq_mul]
      exact Nat.mul_pos hN hpos
    have htotal : 0 < H.totalDegree :=
      lt_of_lt_of_le hei <| (MvPolynomial.le_degreeOf_of_mem_support i he_mem).trans
        (MvPolynomial.degreeOf_le_totalDegree H i)
    intro hunit
    have hdvd : H ∣ (1 : MvPolynomial (Fin 2) A) := hunit.dvd
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd one_ne_zero
    rw [MvPolynomial.totalDegree_one] at hle
    omega
  · have hneg : 0 < intVectorNegative v i := by
      have hvneg : v i < 0 := hvi
      simp only [intVectorNegative_apply]
      apply Nat.pos_of_ne_zero
      intro hz
      have := Int.toNat_eq_zero.mp hz
      omega
    have hpos : intVectorPositive v i = 0 := by
      simp [Int.toNat_of_nonpos (le_of_lt hvi)]
    let e : Fin 2 →₀ ℕ := N • intVectorNegative v
    have hcoeff : H.coeff e = q.coeff 0 := by
      rw [hsum, coeff_sum e, Finset.sum_eq_single 0]
      · rw [MvPolynomial.coeff_monomial]
        simp [e, directionalExponent]
      · intro k hk hk0
        rw [MvPolynomial.coeff_monomial]
        split_ifs with heq
        · have hcoord := congrArg (fun d : Fin 2 →₀ ℕ => d i) heq
          dsimp [e] at hcoord
          simp only [directionalExponent, Finsupp.add_apply, Finsupp.smul_apply,
            nsmul_eq_mul] at hcoord
          rw [hpos] at hcoord
          simp only [mul_zero, zero_add] at hcoord
          have hk_le : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          have hsub : N - k = N := Nat.eq_of_mul_eq_mul_right hneg hcoord
          have hkzero : k = 0 := by omega
          exact (hk0 hkzero).elim
        · rfl
      · simp
    have he_mem : e ∈ H.support := MvPolynomial.mem_support_iff.mpr (hcoeff ▸ hq0)
    have hei : 0 < e i := by
      simp only [e, Finsupp.smul_apply, nsmul_eq_mul]
      exact Nat.mul_pos hN hneg
    have htotal : 0 < H.totalDegree :=
      lt_of_lt_of_le hei <| (MvPolynomial.le_degreeOf_of_mem_support i he_mem).trans
        (MvPolynomial.degreeOf_le_totalDegree H i)
    intro hunit
    have hdvd : H ∣ (1 : MvPolynomial (Fin 2) A) := hunit.dvd
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd one_ne_zero
    rw [MvPolynomial.totalDegree_one] at hle
    omega

private theorem exists_directionalPolynomial_representation
    {A : Type*} [Field A] {F : MvPolynomial (Fin 2) A}
    {r : Fin 2 →₀ ℕ} (hr : r ∈ F.support)
    {v : Fin 2 → ℤ} (_hvne : v ≠ 0)
    (hparam : ∀ s ∈ F.support, ∃ k : ℤ,
      planeExponentDifference r s = k • v)
    (hnonsingleton : ∃ s ∈ F.support, s ≠ r) :
    ∃ (q : Polynomial A) (N : ℕ) (w : Fin 2 →₀ ℕ),
      0 < N ∧ q.natDegree = N ∧ q.coeff 0 ≠ 0 ∧
        F = MvPolynomial.monomial w 1 *
          directionalHomogenization v q N := by
  let parameter : (Fin 2 →₀ ℕ) → ℤ := fun s =>
    if hs : s ∈ F.support then Classical.choose (hparam s hs) else 0
  have parameter_spec : ∀ s ∈ F.support,
      planeExponentDifference r s = parameter s • v := by
    intro s hs
    simp only [parameter, dif_pos hs]
    exact Classical.choose_spec (hparam s hs)
  have parameter_inj : ∀ {s t}, s ∈ F.support → t ∈ F.support →
      parameter s = parameter t → s = t := by
    intro s t hs ht heq
    have hdiff : planeExponentDifference r s = planeExponentDifference r t := by
      rw [parameter_spec s hs, parameter_spec t ht, heq]
    apply Finsupp.ext
    intro i
    have hi := congrFun hdiff i
    dsimp [planeExponentDifference] at hi
    omega
  let P : Finset ℤ := F.support.image parameter
  have hP : P.Nonempty := by
    rw [Finset.image_nonempty]
    exact ⟨r, hr⟩
  let lo : ℤ := P.min' hP
  let hi : ℤ := P.max' hP
  have hlo_mem : lo ∈ P := Finset.min'_mem P hP
  have hhi_mem : hi ∈ P := Finset.max'_mem P hP
  obtain ⟨slo, hslo, hslo_param⟩ := Finset.mem_image.mp hlo_mem
  obtain ⟨shi, hshi, hshi_param⟩ := Finset.mem_image.mp hhi_mem
  have parameter_bounds : ∀ s ∈ F.support, lo ≤ parameter s ∧ parameter s ≤ hi := by
    intro s hs
    constructor
    · exact Finset.min'_le P (parameter s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    · exact Finset.le_max' P (parameter s) (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  let index : (Fin 2 →₀ ℕ) → ℕ := fun s => (parameter s - lo).toNat
  let N : ℕ := (hi - lo).toNat
  have index_cast : ∀ s ∈ F.support, (index s : ℤ) = parameter s - lo := by
    intro s hs
    rw [show (index s : ℤ) = max (parameter s - lo) 0 by
      simpa [index] using Int.ofNat_toNat (parameter s - lo)]
    simp [parameter_bounds s hs |>.1]
  have N_cast : (N : ℤ) = hi - lo := by
    rw [show (N : ℤ) = max (hi - lo) 0 by
      simpa [N] using Int.ofNat_toNat (hi - lo)]
    have hlohi : lo ≤ hi := Finset.min'_le P hi hhi_mem
    simp [hlohi]
  have index_le : ∀ s ∈ F.support, index s ≤ N := by
    intro s hs
    have hcast : (index s : ℤ) ≤ (N : ℤ) := by
      rw [index_cast s hs, N_cast]
      exact sub_le_sub_right (parameter_bounds s hs).2 lo
    exact_mod_cast hcast
  have index_inj : ∀ {s t}, s ∈ F.support → t ∈ F.support →
      index s = index t → s = t := by
    intro s t hs ht heq
    apply parameter_inj hs ht
    have := congrArg (fun n : ℕ => (n : ℤ)) heq
    rw [index_cast s hs, index_cast t ht] at this
    omega
  have hindex_slo : index slo = 0 := by
    simp [index, hslo_param]
  have hindex_shi : index shi = N := by
    have h := index_cast shi hshi
    rw [hshi_param, ← N_cast] at h
    exact_mod_cast h
  have hlohi : lo < hi := by
    obtain ⟨s, hs, hsr⟩ := hnonsingleton
    by_contra hnot
    have hhile : hi ≤ lo := le_of_not_gt hnot
    have hparam_eq : parameter s = parameter r := by
      apply le_antisymm
      · exact (parameter_bounds s hs).2.trans hhile |>.trans (parameter_bounds r hr).1
      · exact (parameter_bounds r hr).2.trans hhile |>.trans (parameter_bounds s hs).1
    exact hsr (parameter_inj hs hr hparam_eq)
  let q : Polynomial A :=
    ∑ s ∈ F.support, Polynomial.monomial (index s) (MvPolynomial.coeff s F)
  have coeff_finset_sum (n : ℕ) (S : Finset (Fin 2 →₀ ℕ))
      (g : (Fin 2 →₀ ℕ) → Polynomial A) :
      (∑ s ∈ S, g s).coeff n = ∑ s ∈ S, (g s).coeff n := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp [ha, ih, Polynomial.coeff_add]
  have coeff_q_index : ∀ s ∈ F.support,
      q.coeff (index s) = MvPolynomial.coeff s F := by
    intro s hs
    rw [show q.coeff (index s) =
        ∑ t ∈ F.support,
          (Polynomial.monomial (index t) (MvPolynomial.coeff t F)).coeff (index s) by
      simpa [q] using coeff_finset_sum (index s) F.support
        (fun t => Polynomial.monomial (index t) (MvPolynomial.coeff t F))]
    rw [Finset.sum_eq_single s]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro t ht hts
      rw [Polynomial.coeff_monomial]
      simp only [ite_eq_right_iff]
      intro hit
      exfalso
      exact hts (index_inj ht hs hit)
    · intro hnot
      exact (hnot hs).elim
  have hNpos : 0 < N := by
    have hcast : (0 : ℤ) < (N : ℤ) := by
      rw [N_cast]
      exact sub_pos.mpr hlohi
    exact_mod_cast hcast
  have hqN : q.coeff N ≠ 0 := by
    rw [← hindex_shi, coeff_q_index shi hshi]
    exact MvPolynomial.mem_support_iff.mp hshi
  have hqdeg_ge : N ≤ q.natDegree := Polynomial.le_natDegree_of_ne_zero hqN
  have hqdeg_le : q.natDegree ≤ N := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [show q.coeff n =
        ∑ s ∈ F.support,
          (Polynomial.monomial (index s) (MvPolynomial.coeff s F)).coeff n by
      simpa [q] using coeff_finset_sum n F.support
        (fun s => Polynomial.monomial (index s) (MvPolynomial.coeff s F))]
    simp only [Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [ite_eq_right_iff]
    intro hisn
    subst n
    exact (Nat.not_lt_of_ge (index_le s hs) hn).elim
  have hqdeg : q.natDegree = N := Nat.le_antisymm hqdeg_le hqdeg_ge
  have hq0 : q.coeff 0 ≠ 0 := by
    rw [← hindex_slo, coeff_q_index slo hslo]
    exact MvPolynomial.mem_support_iff.mp hslo
  have support_coordinate : ∀ s ∈ F.support, ∀ i : Fin 2,
      (s i : ℤ) - (slo i : ℤ) = (index s : ℤ) * v i := by
    intro s hs i
    have hs_eq := congrFun (parameter_spec s hs) i
    have hlo_eq := congrFun (parameter_spec slo hslo) i
    change (s i : ℤ) - (r i : ℤ) = parameter s * v i at hs_eq
    change (slo i : ℤ) - (r i : ℤ) = parameter slo * v i at hlo_eq
    rw [hslo_param] at hlo_eq
    rw [index_cast s hs]
    calc
      (s i : ℤ) - (slo i : ℤ) =
          ((s i : ℤ) - (r i : ℤ)) - ((slo i : ℤ) - (r i : ℤ)) := by ring
      _ = parameter s * v i - lo * v i := by rw [hs_eq, hlo_eq]
      _ = (parameter s - lo) * v i := by ring
  have positive_sub_negative (i : Fin 2) :
      (intVectorPositive v i : ℤ) - (intVectorNegative v i : ℤ) = v i := by
    simp only [intVectorPositive_apply, intVectorNegative_apply]
    rw [Int.ofNat_toNat, Int.ofNat_toNat]
    rcases le_total 0 (v i) with hvi | hvi
    · simp [hvi, neg_nonpos.mpr hvi]
    · simp [hvi]
  have negative_le_slo (i : Fin 2) :
      N * intVectorNegative v i ≤ slo i := by
    by_cases hvi : 0 ≤ v i
    · have hneg : (-v i).toNat = 0 := Int.toNat_of_nonpos (neg_nonpos.mpr hvi)
      simp [intVectorNegative_apply, hneg]
    · have hvineg : v i < 0 := lt_of_not_ge hvi
      have hcoord := support_coordinate shi hshi i
      rw [hindex_shi] at hcoord
      have hnegcast : (intVectorNegative v i : ℤ) = -v i := by
        simp only [intVectorNegative_apply]
        rw [Int.ofNat_toNat]
        simp [le_of_lt hvineg]
      have hcast : ((N * intVectorNegative v i : ℕ) : ℤ) ≤ (slo i : ℤ) := by
        push_cast
        rw [hnegcast]
        have hshi_nonneg : (0 : ℤ) ≤ (shi i : ℤ) := by positivity
        nlinarith
      exact_mod_cast hcast
  let w : Fin 2 →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm
      (fun i => slo i - N * intVectorNegative v i)
  have w_apply (i : Fin 2) :
      w i = slo i - N * intVectorNegative v i := by
    simp [w]
  have exponent_eq : ∀ s ∈ F.support,
      s = w + index s • intVectorPositive v +
        (N - index s) • intVectorNegative v := by
    intro s hs
    apply Finsupp.ext
    intro i
    have hk := index_le s hs
    have hwcast : (w i : ℤ) =
        (slo i : ℤ) - (N : ℤ) * (intVectorNegative v i : ℤ) := by
      rw [w_apply, Nat.cast_sub (negative_le_slo i)]
      push_cast
      rfl
    have hcoord := support_coordinate s hs i
    have hpn := positive_sub_negative i
    have hcast : (s i : ℤ) =
        (w i : ℤ) + (index s : ℤ) * (intVectorPositive v i : ℤ) +
          ((N - index s : ℕ) : ℤ) * (intVectorNegative v i : ℤ) := by
      rw [Nat.cast_sub hk]
      nlinarith
    exact_mod_cast hcast
  refine ⟨q, N, w, hNpos, hqdeg, hq0, ?_⟩
  rw [← F.support_sum_monomial_coeff]
  have hhomog : directionalHomogenization v q N =
      ∑ s ∈ F.support,
        directionalHomogenization v
          (Polynomial.monomial (index s) (MvPolynomial.coeff s F)) N := by
    simp only [q, directionalHomogenization,
      Polynomial.homogenize_finsetSum, map_sum]
  rw [hhomog, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [directionalHomogenization_monomial v (index_le s hs)]
  rw [MvPolynomial.monomial_mul]
  simp only [one_mul]
  apply congrArg (fun e => MvPolynomial.monomial e (MvPolynomial.coeff s F))
  simpa [add_assoc] using exponent_eq s hs

private theorem directionalPolynomial_degree_eq_one_of_irreducible
    {A : Type*} [Field A] [IsAlgClosed A]
    {F : MvPolynomial (Fin 2) A} (hF : Irreducible F)
    {v : Fin 2 → ℤ} (hvne : v ≠ 0)
    {q : Polynomial A} {N : ℕ} {w : Fin 2 →₀ ℕ}
    (hN : 0 < N) (hqdeg : q.natDegree = N) (hq0 : q.coeff 0 ≠ 0)
    (hrep : F = MvPolynomial.monomial w 1 *
      directionalHomogenization v q N) :
    N = 1 := by
  let H := directionalHomogenization v q N
  have hHnonunit : ¬ IsUnit H :=
    directionalHomogenization_not_isUnit hvne hN hqdeg hq0
  have hwunit : IsUnit (MvPolynomial.monomial w (1 : A)) :=
    (hF.isUnit_or_isUnit hrep).resolve_right hHnonunit
  have hHirr : Irreducible H := by
    have hprod : Irreducible (MvPolynomial.monomial w (1 : A) * H) := by
      rw [← hrep]
      exact hF
    exact (irreducible_isUnit_mul hwunit).mp hprod
  by_contra hN1
  have hNone : 1 < N :=
    lt_of_le_of_ne (Nat.succ_le_iff.mpr hN) (Ne.symm hN1)
  have hqne : q ≠ 0 := fun hq => hq0 (by simp [hq])
  have hqdegree : q.degree ≠ 0 := by
    have hposNat : 0 < q.natDegree := by rw [hqdeg]; exact hN
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hposNat)
  obtain ⟨c, hcroot⟩ := IsAlgClosed.exists_root q hqdegree
  obtain ⟨q₂, hqfac⟩ := Polynomial.dvd_iff_isRoot.mpr hcroot
  have hlinear_ne : Polynomial.X - Polynomial.C c ≠ (0 : Polynomial A) :=
    Polynomial.X_sub_C_ne_zero c
  have hq₂ne : q₂ ≠ 0 := by
    intro hq₂
    apply hqne
    rw [hqfac, hq₂, mul_zero]
  have hq₂deg : q₂.natDegree = N - 1 := by
    have hmul := Polynomial.natDegree_mul hlinear_ne hq₂ne
    rw [Polynomial.natDegree_X_sub_C, ← hqfac, hqdeg] at hmul
    omega
  have hcne : c ≠ 0 := by
    intro hc
    apply hq0
    rw [hqfac, hc]
    simp [Polynomial.coeff_mul]
  have hq₂0 : q₂.coeff 0 ≠ 0 := by
    intro hq₂zero
    apply hq0
    rw [hqfac]
    simp [Polynomial.coeff_mul, hq₂zero]
  have hlinear0 : (Polynomial.X - Polynomial.C c).coeff 0 ≠ 0 := by
    simp [hcne]
  have hlinear_deg : (Polynomial.X - Polynomial.C c).natDegree = 1 :=
    Polynomial.natDegree_X_sub_C c
  have hq₂pos : 0 < N - 1 := by omega
  have hleft_nonunit :
      ¬ IsUnit (directionalHomogenization v (Polynomial.X - Polynomial.C c) 1) :=
    directionalHomogenization_not_isUnit hvne Nat.zero_lt_one hlinear_deg hlinear0
  have hright_nonunit :
      ¬ IsUnit (directionalHomogenization v q₂ (N - 1)) :=
    directionalHomogenization_not_isUnit hvne hq₂pos hq₂deg hq₂0
  have hHfac : H =
      directionalHomogenization v (Polynomial.X - Polynomial.C c) 1 *
        directionalHomogenization v q₂ (N - 1) := by
    dsimp [H]
    rw [hqfac]
    have hsumN : 1 + (N - 1) = N := by omega
    simpa [hsumN] using
      (directionalHomogenization_mul v (Polynomial.X - Polynomial.C c) q₂
        (m := 1) (n := N - 1) (by rw [hlinear_deg]) (by rw [hq₂deg]))
  exact (hHirr.isUnit_or_isUnit hHfac).elim hleft_nonunit hright_nonunit

private theorem directionalHomogenization_natDegree_one
    {A : Type*} [Field A] {v : Fin 2 → ℤ} {q : Polynomial A}
    (hqdeg : q.natDegree = 1) :
    directionalHomogenization v q 1 =
      MvPolynomial.monomial (intVectorNegative v) (q.coeff 0) +
        MvPolynomial.monomial (intVectorPositive v) (q.coeff 1) := by
  have hqsum : q = Polynomial.monomial 0 (q.coeff 0) +
      Polynomial.monomial 1 (q.coeff 1) := by
    rw [q.as_sum_range, hqdeg]
    simp [Finset.sum_range_succ]
  calc
    directionalHomogenization v q 1 =
        directionalHomogenization v
          (Polynomial.monomial 0 (q.coeff 0) +
            Polynomial.monomial 1 (q.coeff 1)) 1 := by rw [← hqsum]
    _ = directionalHomogenization v (Polynomial.monomial 0 (q.coeff 0)) 1 +
        directionalHomogenization v (Polynomial.monomial 1 (q.coeff 1)) 1 := by
      simp [directionalHomogenization, Polynomial.homogenize_add]
    _ = _ := by
      rw [directionalHomogenization_monomial v (Nat.zero_le 1),
        directionalHomogenization_monomial v le_rfl]
      simp

private theorem eval_monomial_fin_two
    {A : Type*} [CommSemiring A] (z : Fin 2 → A)
    (e : Fin 2 →₀ ℕ) (c : A) :
    MvPolynomial.eval z (MvPolynomial.monomial e c) =
      c * z 0 ^ e 0 * z 1 ^ e 1 := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two, mul_assoc]
  · intro i
    simp

private theorem torusCharacter_eq_of_directional_linear_representation
    {A : Type*} [Field A]
    {F : MvPolynomial (Fin 2) A} {v : Fin 2 → ℤ} {q : Polynomial A}
    {w : Fin 2 →₀ ℕ} (hqdeg : q.natDegree = 1) (hq0 : q.coeff 0 ≠ 0)
    (hrep : F = MvPolynomial.monomial w 1 *
      directionalHomogenization v q 1)
    (x y : Aˣ)
    (hzero : MvPolynomial.eval ![(x : A), (y : A)] F = 0) :
    x ^ v 0 * y ^ v 1 =
      Units.mk0 (-(q.coeff 0 / q.coeff 1)) (by
        have hqne : q ≠ 0 := fun hq => hq0 (by simp [hq])
        have hq1 : q.coeff 1 ≠ 0 := by
          rw [← hqdeg, Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr hqne
        exact neg_ne_zero.mpr (div_ne_zero hq0 hq1)) := by
  have hqne : q ≠ 0 := fun hq => hq0 (by simp [hq])
  have hq1 : q.coeff 1 ≠ 0 := by
    rw [← hqdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hqne
  have hx : (x : A) ≠ 0 := Units.ne_zero x
  have hy : (y : A) ≠ 0 := Units.ne_zero y
  have hmon : MvPolynomial.eval ![(x : A), (y : A)]
      (MvPolynomial.monomial w (1 : A)) ≠ 0 := by
    rw [eval_monomial_fin_two]
    simp [hx, hy]
  have hHzero : MvPolynomial.eval ![(x : A), (y : A)]
      (directionalHomogenization v q 1) = 0 := by
    rw [hrep, map_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hmon
  rw [directionalHomogenization_natDegree_one hqdeg, map_add,
    eval_monomial_fin_two, eval_monomial_fin_two] at hHzero
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hHzero
  let Apos : A := (x : A) ^ intVectorPositive v 0 *
    (y : A) ^ intVectorPositive v 1
  let Aneg : A := (x : A) ^ intVectorNegative v 0 *
    (y : A) ^ intVectorNegative v 1
  have hAneg : Aneg ≠ 0 := by
    dsimp [Aneg]
    exact mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy)
  have hratio : Apos / Aneg = -(q.coeff 0 / q.coeff 1) := by
    rw [← neg_div]
    apply (div_eq_div_iff hAneg hq1).mpr
    dsimp [Apos, Aneg]
    linear_combination hHzero
  have hvcoord (i : Fin 2) :
      v i = (intVectorPositive v i : ℤ) - (intVectorNegative v i : ℤ) := by
    exact (intVectorPositive_sub_negative v i).symm
  calc
    x ^ v 0 * y ^ v 1 =
        (x ^ (intVectorPositive v 0 : ℤ) *
            (x ^ (intVectorNegative v 0 : ℤ))⁻¹) *
          (y ^ (intVectorPositive v 1 : ℤ) *
            (y ^ (intVectorNegative v 1 : ℤ))⁻¹) := by
      rw [hvcoord 0, hvcoord 1, zpow_sub, zpow_sub]
    _ = (x ^ intVectorPositive v 0 * y ^ intVectorPositive v 1) *
        (x ^ intVectorNegative v 0 * y ^ intVectorNegative v 1)⁻¹ := by
      simp only [zpow_natCast]
      simp only [mul_inv_rev]
      ac_rfl
    _ = Units.mk0 (-(q.coeff 0 / q.coeff 1)) (by
          exact neg_ne_zero.mpr (div_ne_zero hq0 hq1)) := by
      apply Units.ext
      simpa [Apos, Aneg, div_eq_mul_inv] using hratio

/-- Absolute irreducibility and the semantic non-subtorus condition force the
support lattice of a plane torus curve to have rank two. -/
theorem planeCurveSupportHasRankTwo_of_absoluteIrreducible_notSubtorusTranslate
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hirr : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hnot : BGS.External.TorusCurveNotSubtorusTranslate f) :
    PlaneCurveSupportHasRankTwo f := by
  let A := AlgebraicClosure K
  let F : MvPolynomial (Fin 2) A :=
    MvPolynomial.map (algebraMap K A) f
  have hsupp : F.support = f.support := by
    exact MvPolynomial.support_map_of_injective f
      (algebraMap K A).injective
  by_contra hnrank
  have hnrankF : ¬ PlaneCurveSupportHasRankTwo F := by
    intro hrankF
    obtain ⟨r, s, t, hr, hs, ht, hdet⟩ := hrankF
    apply hnrank
    rw [hsupp] at hr hs ht
    exact ⟨r, s, t, hr, hs, ht, hdet⟩
  obtain ⟨x₀, y₀, hzero₀, _⟩ :=
    hnot 1 0 (Or.inl one_ne_zero) (1 : Aˣ)
  have hFne : F ≠ 0 := hirr.ne_zero
  obtain ⟨r, hr⟩ := MvPolynomial.support_nonempty.mpr hFne
  have hnonsingleton : ∃ s ∈ F.support, s ≠ r := by
    by_contra hsingle'
    have hsingle : ∀ s ∈ F.support, s = r := by
      intro s hs
      by_contra hsr
      exact hsingle' ⟨s, hs, hsr⟩
    have hsupp_single : F.support = {r} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hr, fun s hs => hsingle s hs⟩
    have hFmono : F = MvPolynomial.monomial r (MvPolynomial.coeff r F) := by
      rw [← F.support_sum_monomial_coeff, hsupp_single]
      simp
    have hcoeff : MvPolynomial.coeff r F ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hr
    have hx₀ : (x₀ : A) ≠ 0 := Units.ne_zero x₀
    have hy₀ : (y₀ : A) ≠ 0 := Units.ne_zero y₀
    change MvPolynomial.eval ![(x₀ : A), (y₀ : A)] F = 0 at hzero₀
    rw [hFmono, eval_monomial_fin_two] at hzero₀
    exact (mul_ne_zero (mul_ne_zero hcoeff (pow_ne_zero _ hx₀))
      (pow_ne_zero _ hy₀)) hzero₀
  obtain ⟨v, hvne, hparam⟩ :=
    exists_support_direction_of_not_rankTwo hr hnrankF hnonsingleton
  obtain ⟨q, N, w, hN, hqdeg, hq0, hrep⟩ :=
    exists_directionalPolynomial_representation hr hvne hparam hnonsingleton
  have hNone : N = 1 :=
    directionalPolynomial_degree_eq_one_of_irreducible hirr hvne hN hqdeg hq0 hrep
  have hqdeg1 : q.natDegree = 1 := hqdeg.trans hNone
  have hrep1 : F = MvPolynomial.monomial w 1 *
      directionalHomogenization v q 1 := by simpa [hNone] using hrep
  have hvcoords : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_cases h0 : v 0 = 0
    · right
      intro h1
      apply hvne
      funext i
      have hi : i = 0 ∨ i = 1 := by
        have hilt := i.isLt
        omega
      rcases hi with rfl | rfl
      · exact h0
      · exact h1
    · exact Or.inl h0
  let c : Aˣ := Units.mk0 (-(q.coeff 0 / q.coeff 1)) (by
    have hqne : q ≠ 0 := fun hq => hq0 (by simp [hq])
    have hq1 : q.coeff 1 ≠ 0 := by
      rw [← hqdeg1, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hqne
    exact neg_ne_zero.mpr (div_ne_zero hq0 hq1))
  obtain ⟨x, y, hzero, hcharacter⟩ := hnot (v 0) (v 1) hvcoords c
  apply hcharacter
  exact torusCharacter_eq_of_directional_linear_representation hqdeg1 hq0 hrep1 x y hzero

/-- Injective extension of coefficients preserves a rank-two support
certificate. -/
theorem planeCurveSupportHasRankTwo_map_of_injective
    {K E : Type*} [Field K] [Field E]
    (ι : K →+* E) (hι : Function.Injective ι)
    {f : MvPolynomial (Fin 2) K}
    (hrank : PlaneCurveSupportHasRankTwo f) :
    PlaneCurveSupportHasRankTwo (MvPolynomial.map ι f) := by
  obtain ⟨r, s, t, hr, hs, ht, hdet⟩ := hrank
  have hsupp : (MvPolynomial.map ι f).support = f.support :=
    MvPolynomial.support_map_of_injective f hι
  refine ⟨r, s, t, ?_, ?_, ?_, hdet⟩ <;> simpa only [hsupp]

end

end BGS.CorvajaZannier
