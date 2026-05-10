/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc.
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# The finite field Kakeya theorem

This file formalizes Dvir's 2008 theorem that any Kakeya set `K ⊆ Fin n → F`
over a finite field `F` (a set containing a line in every direction) has size
at least `Cₙ · q ^ n`, where `q = #F` and `Cₙ > 0` depends only on `n`.

The argument follows the polynomial method: a small Kakeya set would yield a
nonzero low-degree polynomial vanishing on it (`step1`); restricting to lines
forces the univariate restrictions to vanish identically (`step2`); the top
homogeneous component then vanishes everywhere (`step3`); multiplying by a high
power of a coordinate and inducting on the degree shows the polynomial is zero
(`step4`), contradicting `step1`.
-/

namespace LeanPool.KakeyaFiniteFields

/-- A *Kakeya set* `K ⊆ Fin n → F`: for every direction `d` there is a base
point `b` such that the whole line `{b + t • d | t : F}` lies in `K`. -/
def IsKakeyaSet {F : Type*} {n : ℕ} [Semiring F]
  (K : Set (Fin n → F)) : Prop :=
  ∀ d, ∃ b, { b + t • d | t : F } ⊆ K

lemma card_finsupp_sum_le_eq_sum_range
    {n m : ℕ} :
    Nat.card {s : (Fin n →₀ ℕ) // s.sum (fun _ e => e) ≤ m}
      = ∑ k ∈ Finset.range (m + 1),
          Nat.card {s : (Fin n →₀ ℕ) // s.sum (fun _ e => e) = k} :=
by
  have _ (k : Fin (m + 1)) : Finite {s : Fin n →₀ ℕ // s.sum (fun _ e => e) = k.1} :=
    Finite.of_equiv _ (Sym.equivNatSum (Fin n) k)
  rw [← Fin.sum_univ_eq_sum_range, ← Nat.card_sigma]
  refine Nat.card_congr ?e
  refine
    ⟨(fun x => ⟨⟨x.1.sum (fun _ e => e), Nat.lt_succ_of_le x.2⟩, x.1, rfl⟩),
     (fun ⟨_, s, _⟩ => ⟨s, by omega⟩),
     (fun _ => rfl),
     (fun ⟨_, _, h⟩ => Sigma.subtype_ext (by simp [h]) rfl)⟩

lemma finrank_restrictTotalDegree_choose
    {F : Type*} [Field F] {n m : ℕ} :
    Module.finrank F (MvPolynomial.restrictTotalDegree (σ := Fin n) (R := F) m)
      = Nat.choose (n + m) n :=
by
  suffices h : (∑ i ∈ Finset.range (m + 1), (n + i - 1).choose i) = (n + m).choose n by
    calc
      _ = Nat.card {s : (Fin n →₀ ℕ) // s.sum (fun _ e => e) ≤ m} := by
        simpa [MvPolynomial.restrictTotalDegree] using
          Module.finrank_eq_nat_card_basis
            (MvPolynomial.basisRestrictSupport (σ := Fin n) (R := F)
              {s | s.sum (fun _ e => e) ≤ m})
      _ = ∑ i ∈ Finset.range (m + 1),
            Nat.card {s : (Fin n →₀ ℕ) // s.sum (fun _ e => e) = i} :=
        by simpa using card_finsupp_sum_le_eq_sum_range
      _ = ∑ i ∈ Finset.range (m + 1), (n + i - 1).choose i :=
        Finset.sum_congr rfl fun i _ => by
          simpa [Sym.card_sym_eq_choose] using
            Nat.card_congr (Sym.equivNatSum (α := Fin n) (n := i)).symm
      _ = _ := h
  rcases eq_or_ne n 0 with rfl | hn
  · simp_rw [fun i => show (0 + i - 1).choose i = if i = 0 then 1 else 0 by cases i <;> simp]
    simp
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  calc _ = ∑ i ∈ Finset.range (m + 1), (i + s).choose i := by
        simp [Nat.add_comm, Nat.add_left_comm]
    _ = ∑ i ∈ Finset.range (m + 1), (i + s).choose s :=
        Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm i, Nat.choose_symm_add]
    _ = _ := by
        simpa [Nat.add_comm, Nat.add_assoc] using Nat.sum_range_add_choose (n := m) (k := s)

lemma step1
    {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (K : Set (Fin n → F))
    (hKcard : Nat.card K < Nat.choose (Fintype.card F + n - 1) n) :
    ∃ P : MvPolynomial (Fin n) F,
      P ≠ 0 ∧
      MvPolynomial.totalDegree P ≤ Fintype.card F - 1 ∧
      ∀ x ∈ K, MvPolynomial.eval x P = 0 :=
by
  set q : ℕ := Fintype.card F
  set m : ℕ := q - 1
  set V : Submodule F (MvPolynomial (Fin n) F) :=
    MvPolynomial.restrictTotalDegree (σ := Fin n) (R := F) m
  set Kidx := K
  haveI : Fintype Kidx := Fintype.ofFinite Kidx
  let xs : Kidx → (Fin n → F) := fun t => t.1
  let E : V →ₗ[F] (Kidx → F) :=
    LinearMap.pi
      (fun t =>
        ((MvPolynomial.aeval (σ := Fin n) (R := F) (S₁ := F) (xs t)).toLinearMap).comp V.subtype)
  have hlt : Module.finrank F (Kidx → F) < Module.finrank F V := by
    obtain ⟨q0, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fintype.card_pos_iff.2 ⟨(0 : F)⟩))
    have hKlt : Fintype.card Kidx < Nat.choose (q + n - 1) n := by
      simpa [Nat.card_eq_fintype_card, Kidx, q] using hKcard
    have : Fintype.card Kidx < Nat.choose (n + m) n := by
      simpa [m, q, Nat.add_comm, hq] using hKlt
    simpa [V,
           finrank_restrictTotalDegree_choose (F := F) (n := n) (m := m),
           Module.finrank_fintype_fun_eq_card (R := F) (η := Kidx)] using this
  have hker : (LinearMap.ker E) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := E) hlt
  obtain ⟨v, hvKer, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨(v : MvPolynomial (Fin n) F), ?_, ?_, ?_⟩
  · exact fun h => hvne (Subtype.ext (by simpa using h))
  · have hvV : (v : MvPolynomial (Fin n) F) ∈ V := v.property
    exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin n) (R := F) (m := m) _).1 hvV
  · intro x hx
    have hEv : E v = 0 := by simpa [LinearMap.mem_ker] using hvKer
    have hx' : E v ⟨x, hx⟩ = 0 := by
      simpa using congrArg (fun f => f ⟨x, hx⟩) hEv
    simpa [E, xs, LinearMap.pi_apply] using hx'

lemma step2
  {F : Type*} [Field F] [Fintype F] {n : ℕ}
  {K : Set (Fin n → F)}
  {P : MvPolynomial (Fin n) F}
  (hdeg : MvPolynomial.totalDegree P ≤ Fintype.card F - 1)
  (hvan : ∀ x ∈ K, MvPolynomial.eval x P = 0)
  (d : Fin n → F) :
  ∀ b : Fin n → F,
    ({ b + t • d | t : F } ⊆ K) →
    (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => Polynomial.C (b i) + Polynomial.C (d i) * Polynomial.X) P) = 0 :=
by
  intro b hline
  set Q := MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (b i) + Polynomial.C (d i) * Polynomial.X) P
  have hfdeg i : (Polynomial.C (b i) + Polynomial.C (d i) * Polynomial.X).natDegree ≤ 1 := by
    simpa [add_comm] using Polynomial.natDegree_linear_le (a := d i) (b := b i)
  have hdegQ : Q.natDegree ≤ Fintype.card F - 1 := by
    simpa [MvPolynomial.aeval_def] using MvPolynomial.aeval_natDegree_le (F := P) hdeg _ hfdeg
  by_contra hQ0
  refine
    (Polynomial.card_le_degree_of_subset_roots (Z := .univ) fun t _ =>
      (Polynomial.mem_roots hQ0).mpr ?_).not_gt
      (hdegQ.trans_lt (Nat.sub_lt Fintype.card_pos Nat.one_pos))
  have h := MvPolynomial.polynomial_eval_eval₂ (x := t) (f := Polynomial.C)
    (g := fun i => Polynomial.C (b i) + Polynomial.C (d i) * Polynomial.X) (p := P)
  have hEval : Q.eval t = MvPolynomial.eval (fun i => b i + d i * t) P := by
    simpa [Q, RingHom.ext_iff, MvPolynomial.eval, MvPolynomial.eval₂] using h
  simpa [hEval, Pi.add_def, smul_eq_mul, mul_comm] using
    hvan (b + t • d) (hline ⟨t, rfl⟩)

lemma coeff_prod_top_of_natDegree_le
  {F : Type*} [CommSemiring F] {ι : Type*}
  (s : Finset ι) (r : ι → Polynomial F) (e : ι → ℕ)
  (h : ∀ i ∈ s, (r i).natDegree ≤ e i) :
  (∏ i ∈ s, r i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (r i).coeff (e i) :=
by
  classical
  revert h
  refine Finset.induction_on s ?h0 ?hstep
  · intro h; simp
  · intro a s ha ih h
    have h' : ∀ i ∈ s, (r i).natDegree ≤ e i := fun i hi => h i (by simp [hi])
    have ha' : (r a).natDegree ≤ e a := by simpa [ha] using h a (by simp [ha])
    set P : Polynomial F := ∏ i ∈ s, r i
    set Es : ℕ := ∑ i ∈ s, e i
    have hdegP : P.natDegree ≤ Es :=
      (Polynomial.natDegree_prod_le (s := s) (f := fun i => r i)).trans
        (by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact h' i hi)
    have hsum : (∑ i ∈ insert a s, e i) = Es + e a := by
      simp [Es, Finset.sum_insert, ha, Nat.add_comm]
    have hprod : (∏ i ∈ insert a s, r i) = P * r a := by
      simp [P, Finset.prod_insert, ha, mul_comm]
    have hmul : (P * r a).coeff (Es + e a) = P.coeff Es * (r a).coeff (e a) :=
      Polynomial.coeff_mul_add_eq_of_natDegree_le (df := Es) (dg := e a) hdegP ha'
    have ih' := ih h'
    simpa [hsum, hprod, ih', Finset.prod_insert, ha, mul_comm, mul_left_comm, mul_assoc]
      using hmul

lemma coeff_top_eval_linear_hc_lt
  {F : Type*} [Field F] {σ : Type*}
  (P : MvPolynomial σ F) (b d : σ → F) {j m : ℕ}
  (hj : j < m) :
  Polynomial.coeff
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (b i) + Polynomial.C (d i) * Polynomial.X)
        (MvPolynomial.homogeneousComponent j P)) m = 0 :=
by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  refine Nat.lt_of_le_of_lt ?_ hj
  simpa [MvPolynomial.aeval_def, Nat.mul_one] using
    MvPolynomial.aeval_natDegree_le (σ := σ) (R := F) (m := j) (n := 1)
      (MvPolynomial.homogeneousComponent j P)
      (MvPolynomial.IsHomogeneous.totalDegree_le
        (MvPolynomial.homogeneousComponent_isHomogeneous (n := j) (φ := P)))
      (fun i => Polynomial.C (b i) + Polynomial.C (d i) * Polynomial.X)
      (by
        intro i
        simpa [add_comm] using
          (Polynomial.natDegree_linear_le :
            (Polynomial.natDegree (Polynomial.C (d i) * Polynomial.X + Polynomial.C (b i))) ≤ 1))

lemma step3
  {F : Type*} [Field F] [Fintype F] {n : ℕ}
  {K : Set (Fin n → F)} (hK : IsKakeyaSet K)
  {P : MvPolynomial (Fin n) F}
  (hdeg : MvPolynomial.totalDegree P ≤ Fintype.card F - 1)
  (hvan : ∀ x ∈ K, MvPolynomial.eval x P = 0) :
  MvPolynomial.homogeneousComponent (Fintype.card F - 1) P = 0 :=
by
  set m := Fintype.card F - 1; set H := MvPolynomial.homogeneousComponent m P
  have hHhom : H.IsHomogeneous m := MvPolynomial.homogeneousComponent_isHomogeneous ..
  suffices h : ∀ dir, MvPolynomial.eval dir H = 0 by
    simpa using
      hHhom.eq_zero_of_forall_eval_eq_zero_of_le_card h
        (by simpa [Cardinal.mk_fintype] using
          Nat.cast_le.mpr (Nat.sub_lt Fintype.card_pos (Nat.succ_pos 0)).le)
  intro dir; obtain ⟨b, hline⟩ := hK dir
  set L := fun i => Polynomial.C (b i) + Polynomial.C (dir i) * Polynomial.X
  by_cases hlt : MvPolynomial.totalDegree P < m
  · simp [H, MvPolynomial.homogeneousComponent_eq_zero (n := m) (φ := P) hlt]
  have hLdeg : ∀ i, (L i).natDegree ≤ 1 := fun i => by
    simpa [L, add_comm] using Polynomial.natDegree_linear_le (a := dir i) (b := b i)
  have hQcoeff : (MvPolynomial.eval₂Hom Polynomial.C L P).coeff m
      = (MvPolynomial.eval₂Hom Polynomial.C L H).coeff m := by
    have hvanish j (hj : j ∈ Finset.range (m + 1)) (hjm : j ≠ m) :
        ((MvPolynomial.eval₂Hom Polynomial.C L
            (MvPolynomial.homogeneousComponent j P)).coeff m) = 0 :=
      coeff_top_eval_linear_hc_lt P b dir
        (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hjm)
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent (φ := P)]
    simp only [map_sum, Polynomial.finset_sum_coeff, le_antisymm hdeg (le_of_not_gt hlt), H,
               Finset.sum_eq_single m hvanish
                 (fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_self m))).elim)]
  suffices (MvPolynomial.eval₂Hom Polynomial.C L H).coeff m = MvPolynomial.eval dir H by
    rw [← this, ← hQcoeff, step2 hdeg hvan dir b hline]
    simp
  have h0 := congrArg (·.coeff m) (MvPolynomial.eval₂_eq (g := Polynomial.C) (X := L) (f := H))
  simp only [Polynomial.finset_sum_coeff] at h0
  refine h0.trans (Finset.sum_congr rfl fun d hd => ?_)
  have hsumdeg := by
    simpa [Finsupp.degree] using
      (by simpa [Finsupp.degree_eq_weight_one] using hHhom (MvPolynomial.mem_support_iff.mp hd) :
        Finsupp.degree d = m)
  rw [Polynomial.coeff_C_mul, ← hsumdeg,
    coeff_prod_top_of_natDegree_le d.support _ _
      fun i _ => (Polynomial.natDegree_pow_le_of_le (d i) (hLdeg i)).trans (by simp)]
  refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
  have := Polynomial.coeff_pow_of_natDegree_le (m := d i) (hLdeg i)
  simp only [Nat.mul_one] at this
  simp only [this, show (L i).coeff 1 = dir i by simp [L]]

lemma step4
  {F : Type*} [Field F] [Fintype F] {n : ℕ}
  {K : Set (Fin n → F)} (hK : IsKakeyaSet K)
  {P : MvPolynomial (Fin n) F}
  (hdeg : MvPolynomial.totalDegree P ≤ Fintype.card F - 1)
  (hvan : ∀ x ∈ K, MvPolynomial.eval x P = 0) :
  P = 0 :=
by
  classical
  set d := MvPolynomial.totalDegree P with hd
  have hConst : MvPolynomial.totalDegree P = 0 → P = 0 := fun htd0 => by
    obtain ⟨y, hy⟩ := hK 0
    have := hvan y (hy ⟨0, by simp⟩)
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd0, MvPolynomial.eval_C] at this
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd0, this, MvPolynomial.C_0]
  by_cases hEmpty : IsEmpty (Fin n)
  · haveI := hEmpty
    exact hConst ((MvPolynomial.eq_C_of_isEmpty P).symm ▸ MvPolynomial.totalDegree_C _)
  obtain ⟨i⟩ := not_isEmpty_iff.mp hEmpty
  set s := Fintype.card F - 1 - d
  have hsd : s + d = Fintype.card F - 1 := by omega
  let H := MvPolynomial.X (R := F) i ^ s
  have hsum' :=
    (by simpa [hd] using MvPolynomial.sum_homogeneousComponent (φ := P) :
      ∑ j ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent j P = P)
  have htop : MvPolynomial.homogeneousComponent d P = 0 :=
      (MvPolynomial.isRegular_X_pow (k := s)).left.eq_iff.mp <| by
    have hHC : MvPolynomial.homogeneousComponent (Fintype.card F - 1) (H * P)
        = H * MvPolynomial.homogeneousComponent d P :=
      calc
        _ = _ := by rw [← hsum']
        _ = ∑ j ∈ Finset.range (d + 1),
              MvPolynomial.homogeneousComponent (Fintype.card F - 1)
                (H * MvPolynomial.homogeneousComponent j P) := by
            simp_rw [Finset.mul_sum]
            exact map_sum _ _ _
        _ = ∑ j ∈ Finset.range (d + 1),
              (if Fintype.card F - 1 = s + j then
                H * MvPolynomial.homogeneousComponent j P else 0) :=
          Finset.sum_congr rfl fun j _ => by
            simpa using
              MvPolynomial.homogeneousComponent_of_mem
                (by
                  simpa [MvPolynomial.mem_homogeneousSubmodule] using
                    (MvPolynomial.isHomogeneous_X_pow (R := F) i s).mul
                      (MvPolynomial.homogeneousComponent_isHomogeneous j P))
        _ = _ :=
          (Finset.sum_eq_single d
            (fun j _ hjd => if_neg fun h => hjd (Nat.add_left_cancel (hsd.trans h)).symm)
            fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_self d))).elim).trans
            (if_pos hsd.symm)
    rw [mul_zero, ← hHC]
    exact step3 hK
      ((MvPolynomial.totalDegree_mul H P).trans
        (by simp [H, MvPolynomial.totalDegree_X_pow, hd.symm, hsd]))
      fun x hx => by simp [MvPolynomial.eval_mul, hvan x hx]
  by_contra hP
  rcases eq_or_ne d 0 with hdz | hdnz
  · exact hP (hConst (hd.symm ▸ hdz))
  have key : MvPolynomial.totalDegree P
      ≤ (Finset.range (d + 1)).sup
          fun j => MvPolynomial.totalDegree (MvPolynomial.homogeneousComponent j P) := by
    conv_lhs => rw [← hsum']
    exact MvPolynomial.totalDegree_finset_sum _ _
  have hbound : ∀ j ∈ Finset.range (d + 1),
      MvPolynomial.totalDegree (MvPolynomial.homogeneousComponent j P) ≤ d - 1 := by
    intro j hj
    rcases eq_or_ne j d with rfl | hjd
    · simp [htop]
    exact (MvPolynomial.homogeneousComponent_isHomogeneous j P).totalDegree_le.trans
      (Nat.le_pred_of_lt (lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hjd))
  have : MvPolynomial.totalDegree P ≤ d - 1 := key.trans (Finset.sup_le hbound)
  omega

/-- **Dvir's finite field Kakeya theorem.** For each `n` there is a constant
`C > 0` (here `(n!)⁻¹`) such that every Kakeya set `K ⊆ Fin n → F` over any
finite field `F` satisfies `Nat.card K ≥ C * (#F) ^ n`. -/
theorem kakeya_set_bound (n : ℕ) :
  ∃ C : ℝ, 0 < C ∧
    ∀ (F : Type*) [Field F] [Fintype F] (K : Set (Fin n → F)),
      IsKakeyaSet K → Nat.card K ≥ C * Fintype.card F ^ n :=
by
  classical
  refine ⟨(Nat.factorial n : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast Nat.factorial_pos n), ?_⟩
  intro F _ _ K hK
  set q : ℕ := Fintype.card F
  have hχ : (Nat.choose (q + n - 1) n : ℝ) ≤ Nat.card K := by
    exact_mod_cast (by
      by_contra h
      rcases step1 K (lt_of_not_ge h) with ⟨P, hP, hdeg, hvan⟩
      exact hP (step4 (K := K) hK hdeg hvan))
  have h : (Nat.factorial n : ℝ)⁻¹ * (q : ℝ) ^ n ≤ Nat.choose (q + n - 1) n := by
    have : (q : ℝ) ^ n ≤ (Nat.ascFactorial q n : ℝ) := by
      exact_mod_cast (Nat.pow_succ_le_ascFactorial q n)
    simpa [mul_comm, mul_left_comm, mul_assoc,
           (by exact_mod_cast Nat.ascFactorial_eq_factorial_mul_choose' q n),
           (by exact_mod_cast (ne_of_gt (Nat.factorial_pos n)) : Nat.factorial n ≠ 0)] using
      mul_le_mul_of_nonneg_left this
        (inv_nonneg.mpr ((by exact_mod_cast Nat.factorial_pos n : 0 < (Nat.factorial n : ℝ)).le))
  simpa [q] using h.trans hχ

end LeanPool.KakeyaFiniteFields
