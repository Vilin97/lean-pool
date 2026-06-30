/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/

import LeanPool.PythagoreanPolynomialParametrization.Basic

/-! # Explanatory and cited source statements

This file records source-level material from Frisch--Vaserstein that is not used by
the main parametrization proof.
-/

namespace LeanPool.PythagoreanPolynomialParametrization

open MvPolynomial



/-! ## Finite integer-polynomial cover from one integer-valued tuple -/

private lemma bind_affine_sub_const_dvd {σ : Type*}
    (P : MvPolynomial σ ℤ) (D : ℤ) (r : σ → ℤ) :
    ∃ H : MvPolynomial σ ℤ,
      bind₁ (fun i => C (r i) + C D * X i) P =
        C (eval₂ (RingHom.id ℤ) r P) + C D * H := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, ?_⟩
      simp
  | add P Q hP hQ =>
      rcases hP with ⟨HP, hHP⟩
      rcases hQ with ⟨HQ, hHQ⟩
      refine ⟨HP + HQ, ?_⟩
      rw [map_add, hHP, hHQ, eval₂_add, C_add]
      ring
  | mul_X P i hP =>
      rcases hP with ⟨HP, hHP⟩
      refine ⟨C (eval₂ (RingHom.id ℤ) r P) * X i + C (r i) * HP + C D * HP * X i, ?_⟩
      rw [map_mul, bind₁_X_right, hHP, eval₂_mul, eval₂_X, C_mul]
      ring

private lemma rat_scaled_num_den_cast_eq (N : ℕ) (q : ℚ) (hdiv : q.den ∣ N) :
    (((N : ℤ) / (q.den : ℤ) * q.num : ℤ) : ℚ) = (N : ℚ) * q := by
  rcases hdiv with ⟨m, hm⟩
  have hden_ne_zero : (q.den : ℤ) ≠ 0 := by
    have h : q.den ≠ 0 := q.den_ne_zero
    exact_mod_cast h
  have hN_eq : (N : ℤ) = (q.den : ℤ) * (m : ℤ) := by
    have h : (N : ℕ) = q.den * m := hm
    have h' : (N : ℤ) = ((q.den * m : ℕ) : ℤ) := by exact_mod_cast h
    rw [h']
    norm_num [Nat.cast_mul]
  have h1 : ((N : ℤ) / (q.den : ℤ) : ℤ) = (m : ℤ) := by
    rw [hN_eq]
    exact Int.mul_ediv_cancel_left m hden_ne_zero
  have h2 : (N : ℚ) = (q.den : ℚ) * (m : ℚ) := by
    have h : (N : ℕ) = q.den * m := hm
    have h' : (N : ℚ) = ((q.den * m : ℕ) : ℚ) := by exact_mod_cast h
    rw [h']
    norm_num [Nat.cast_mul]
  have h3 : (q.den : ℚ) * q = (q.num : ℚ) := by
    exact_mod_cast Rat.den_mul_eq_num q
  calc
    (((N : ℤ) / (q.den : ℤ) * q.num : ℤ) : ℚ)
        = (((m : ℤ) * q.num : ℤ) : ℚ) := by rw [h1]
    _ = (m : ℚ) * (q.num : ℚ) := by norm_num
    _ = (m : ℚ) * ((q.den : ℚ) * q) := by rw [h3]
    _ = (q.den : ℚ) * (m : ℚ) * q := by ring
    _ = (N : ℚ) * q := by rw [h2]

private lemma coeff_mapRange_scaled_rat {n : ℕ} (F : RatPoly n) (N : ℕ)
    (hf_map : (fun q : ℚ => (N : ℤ) / (q.den : ℤ) * q.num) 0 = 0)
    (hdiv : ∀ s ∈ MvPolynomial.support F, (MvPolynomial.coeff s F).den ∣ N)
    (s : Fin n →₀ ℕ) :
    let P : MvPolynomial (Fin n) ℤ :=
      Finsupp.mapRange (fun q : ℚ => (N : ℤ) / (q.den : ℤ) * q.num) hf_map F
    (Int.cast (MvPolynomial.coeff s P) : ℚ) = (N : ℚ) * MvPolynomial.coeff s F := by
  intro P
  change
    (Int.cast (MvPolynomial.coeff s
      (Finsupp.mapRange (fun q : ℚ => (N : ℤ) / (q.den : ℤ) * q.num) hf_map F)) :
        ℚ) =
      (N : ℚ) * MvPolynomial.coeff s F
  by_cases hs : s ∈ MvPolynomial.support F
  · have hdiv_s := hdiv s hs
    have h1 :
        MvPolynomial.coeff s
          (Finsupp.mapRange (fun q : ℚ => (N : ℤ) / (q.den : ℤ) * q.num) hf_map F) =
            (N / (MvPolynomial.coeff s F).den : ℤ) * (MvPolynomial.coeff s F).num := by
      simp [MvPolynomial.coeff, Finsupp.mapRange_apply]
    rw [h1]
    exact rat_scaled_num_den_cast_eq N (MvPolynomial.coeff s F) hdiv_s
  · have hq : F s = 0 := by
      rwa [MvPolynomial.notMem_support_iff] at hs
    simp [MvPolynomial.coeff, Finsupp.mapRange_apply, hq]

private lemma map_intPoly_eq_nat_smul_of_coeff {n : ℕ}
    (F : RatPoly n) (P : MvPolynomial (Fin n) ℤ) (N : ℕ)
    (hcoeff : ∀ s : Fin n →₀ ℕ,
      (Int.cast (MvPolynomial.coeff s P) : ℚ) = (N : ℚ) * MvPolynomial.coeff s F) :
    MvPolynomial.map (Int.castRingHom ℚ) P = (N : ℚ) • F := by
  apply MvPolynomial.ext
  intro s
  simp [MvPolynomial.coeff_map, hcoeff s]

private lemma eval_bind1_affine_int {n : ℕ}
    (P : MvPolynomial (Fin n) ℤ) (D : ℕ) (r y : Fin n → ℤ) :
    MvPolynomial.eval y
      (MvPolynomial.bind₁ (fun j : Fin n =>
        MvPolynomial.C (D : ℤ) * MvPolynomial.X j + MvPolynomial.C (r j)) P) =
    MvPolynomial.eval (fun j : Fin n => (D : ℤ) * y j + r j) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp
  | add p q hp hq =>
      rw [map_add, MvPolynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p j hp =>
      rw [map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.eval_mul, hp]
      simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X]

private lemma int_eval_cast_eq_rat_eval_map {n : ℕ} (a : Fin n → ℤ)
    (P : MvPolynomial (Fin n) ℤ) :
    (MvPolynomial.eval a P : ℚ) =
      MvPolynomial.eval (fun j => (a j : ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp
  | add p q hp hq =>
      simp [hp, hq, MvPolynomial.eval_add]
  | mul_X p j hp =>
      simp [hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]

private lemma ratPolyEval_eq_intPolyEval_on_residue {n : ℕ}
    {F : RatPoly n} {P Q H : MvPolynomial (Fin n) ℤ} {D : ℕ}
    (hD_pos : 0 < D) (hF_int : IsIntValued F)
    (hP_eval : ∀ a : Fin n → ℤ, (eval a P : ℚ) = D * ratPolyEval F a)
    (r b a : Fin n → ℤ)
    (ha : a = fun j => (D : ℤ) * b j + r j)
    (hH : bind₁ (fun j => C (r j) + C (D : ℤ) * X j) P =
      C (eval₂ (RingHom.id ℤ) r P) + C (D : ℤ) * H)
    (hQ : Q = C (eval r P / (D : ℤ)) + H) :
    ratPolyEval F a = (intPolyEval Q b : ℚ) := by
  have h1 : eval a P = eval r P + D * eval b H := by
    rw [ha]
    have h3 := eval_bind1_affine_int P D r b
    rw [← h3]
    have h4 :
        bind₁ (fun j => C (D : ℤ) * X j + C (r j)) P =
          bind₁ (fun j => C (r j) + C (D : ℤ) * X j) P := by
      congr
      funext j
      ring
    rw [h4]
    have hH' :
        bind₁ (fun j => C (r j) + C (D : ℤ) * X j) P =
          C (eval r P) + C (D : ℤ) * H := by
      have h5 :
          bind₁ (fun j => C (r j) + C (D : ℤ) * X j) P =
            C (eval₂ (RingHom.id ℤ) r P) + C (D : ℤ) * H := hH
      rw [h5]
      have : eval₂ (RingHom.id ℤ) r P = eval r P := by
        rw [MvPolynomial.eval₂_id]
      rw [this]
    rw [hH']
    simp [eval_add, eval_mul]
  have h2 : (eval a P : ℚ) = D * ratPolyEval F a := hP_eval a
  have h3 :
      (eval r P : ℚ) =
        D * ((eval r P / (D : ℤ) : ℤ) : ℚ) := by
    obtain ⟨w, hw⟩ := hF_int r
    have hqr : (eval r P : ℚ) = (D : ℚ) * (w : ℚ) := by
      simpa [ratPolyEval, hw] using hP_eval r
    have hz : eval r P = (D : ℤ) * w := by
      exact_mod_cast hqr
    have hdiv : eval r P / (D : ℤ) = w := by
      apply Int.ediv_eq_of_eq_mul_left
      · exact_mod_cast (ne_of_gt hD_pos)
      · simpa [mul_comm] using hz
    rw [hdiv, hqr]
  have hG :
      (intPolyEval Q b : ℚ) =
        ((eval r P / (D : ℤ) : ℤ) : ℚ) + (eval b H : ℚ) := by
    rw [hQ]
    simp [intPolyEval]
  have h4 :
      D * ratPolyEval F a =
        D * (intPolyEval Q b : ℚ) := by
    have h1' :
        (eval a P : ℚ) = (eval r P : ℚ) + D * (eval b H : ℚ) := by
      exact_mod_cast h1
    rw [← h2, h1', h3, hG]
    ring
  exact mul_left_cancel₀ (by positivity : (D : ℚ) ≠ 0) h4

/-- Source-cited result, `pyth.tex` lines 138--141: every set of integer tuples
parametrized by a single integer-valued polynomial tuple is parametrized by a finite
number of integer-coefficient polynomial tuples.

The paper cites this from Frisch's work and does not use it in the proof of the main
Pythagorean-triple parametrization theorem. -/
theorem single_intValued_parametrization_yields_finite_intPoly_parametrization
    {n k : ℕ} {F : Fin k → RatPoly n} {S : Set (Fin k → ℤ)}
    (hF : IntValuedTupleParametrizes F S) :
    ∃ (m : ℕ) (G : Fin m → Fin k → IntPoly n),
      FiniteIntPolyTupleParametrizes G S := by
  rcases hF with ⟨hF_int, hF_eq⟩
  have hD :
      ∀ i : Fin k, ∃ D : ℕ, 0 < D ∧
        ∀ s, s ∈ (F i).support → (MvPolynomial.coeff s (F i)).den ∣ D := by
    intro i
    refine ⟨Finset.prod (F i).support fun s => (MvPolynomial.coeff s (F i)).den, ?_, ?_⟩
    · exact Finset.prod_pos fun s _ =>
        Nat.pos_of_ne_zero (Rat.den_ne_zero (MvPolynomial.coeff s (F i)))
    · intro s hs
      exact Finset.dvd_prod_of_mem _ hs
  choose D hD_pos hD_div using hD
  let D_total : ℕ := Finset.prod Finset.univ D
  have hD_total_pos : 0 < D_total := Finset.prod_pos fun i _ => hD_pos i
  have hD_total_div :
      ∀ (i : Fin k) (s : Fin n →₀ ℕ),
        s ∈ (F i).support → (MvPolynomial.coeff s (F i)).den ∣ D_total := by
    intro i s hs
    exact dvd_trans (hD_div i s hs) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hf_map : (fun q : ℚ => (D_total / q.den : ℤ) * q.num) 0 = 0 := by simp
  let P : Fin k → MvPolynomial (Fin n) ℤ := fun i =>
    Finsupp.mapRange (fun q => (D_total / q.den : ℤ) * q.num) hf_map (F i)
  have hP_coeff :
      ∀ (i : Fin k) (s : Fin n →₀ ℕ),
        (Int.cast (MvPolynomial.coeff s (P i)) : ℚ) =
          D_total * MvPolynomial.coeff s (F i) := by
    intro i s
    exact coeff_mapRange_scaled_rat (F i) D_total hf_map (hD_total_div i) s
  have hP_eval :
      ∀ (i : Fin k) (a : Fin n → ℤ),
        (eval a (P i) : ℚ) = D_total * eval (fun j => (a j : ℚ)) (F i) := by
    intro i a
    rw [int_eval_cast_eq_rat_eval_map a (P i)]
    have hmap :
        MvPolynomial.map (Int.castRingHom ℚ) (P i) = (D_total : ℚ) • (F i) := by
      exact map_intPoly_eq_nat_smul_of_coeff (F i) (P i) D_total (hP_coeff i)
    rw [hmap]
    simp
  let m := D_total ^ n
  have hcard : Fintype.card (Fin n → Fin D_total) = m := by
    simp [m]
  let e : Fin m ≃ (Fin n → Fin D_total) :=
    (finCongr hcard.symm).trans (Fintype.equivFin _).symm
  let G : Fin m → Fin k → MvPolynomial (Fin n) ℤ := fun idx i =>
    let r : Fin n → ℤ := fun j => ((e idx j : ℕ) : ℤ)
    let H := Classical.choose (bind_affine_sub_const_dvd (P i) D_total r)
    C (eval₂ (RingHom.id ℤ) r (P i) / (D_total : ℤ)) + H
  refine ⟨m, G, ?_⟩
  rw [FiniteIntPolyTupleParametrizes]
  ext v
  simp only [Set.mem_setOf_eq, hF_eq]
  constructor
  · rintro ⟨a, ha⟩
    let b : Fin n → ℤ := fun j => a j / D_total
    let r_nat : Fin n → ℕ := fun j => (a j % D_total).toNat
    have hr_nat : ∀ j, r_nat j < D_total := by
      intro j
      have hnonneg : 0 ≤ a j % D_total := Int.emod_nonneg (a j) (by positivity)
      have hlt : a j % D_total < D_total := Int.emod_lt_of_pos (a j) (by positivity)
      have htoNat : (a j % D_total).toNat = a j % D_total :=
        Int.toNat_of_nonneg hnonneg
      simp [r_nat]
      omega
    let r_fin : Fin n → Fin D_total := fun j => ⟨r_nat j, hr_nat j⟩
    let idx : Fin m := e.symm r_fin
    refine ⟨idx, b, ?_⟩
    intro i
    let r : Fin n → ℤ := fun j => ((e idx j : ℕ) : ℤ)
    let H := Classical.choose (bind_affine_sub_const_dvd (P i) D_total r)
    have hH := Classical.choose_spec (bind_affine_sub_const_dvd (P i) D_total r)
    have hr_eq : ∀ j, r j = r_nat j := by
      intro j
      simp [r, idx, r_fin]
    have ha_eq : ∀ j, a j = D_total * b j + r_nat j := by
      intro j
      have hnonneg : 0 ≤ a j % D_total := Int.emod_nonneg (a j) (by positivity)
      have htoNat : (a j % D_total).toNat = a j % D_total :=
        Int.toNat_of_nonneg hnonneg
      change
        a j = (D_total : ℤ) * (a j / (D_total : ℤ)) +
          (((a j % (D_total : ℤ)).toNat : ℕ) : ℤ)
      rw [htoNat]
      rw [Int.mul_ediv_add_emod (a j) D_total]
    have h_key : ratPolyEval (F i) a = (intPolyEval (G idx i) b : ℚ) := by
      have ha' : a = fun j => (D_total : ℤ) * b j + r j := by
        funext j
        rw [ha_eq j, hr_eq j]
      exact ratPolyEval_eq_intPolyEval_on_residue
        (F := F i) (P := P i) (Q := G idx i) (H := H)
        hD_total_pos (hF_int i) (hP_eval i) r b a ha' hH rfl
    have h_eq : intPolyEval (G idx i) b = v i := by
      have h : (intPolyEval (G idx i) b : ℚ) = (v i : ℚ) := by
        rw [← h_key]
        exact ha i
      exact_mod_cast h
    exact h_eq
  · rintro ⟨idx, b, hGb⟩
    let r : Fin n → ℤ := fun j => ((e idx j : ℕ) : ℤ)
    let a : Fin n → ℤ := fun j => D_total * b j + r j
    refine ⟨a, ?_⟩
    intro i
    let H := Classical.choose (bind_affine_sub_const_dvd (P i) D_total r)
    have hH := Classical.choose_spec (bind_affine_sub_const_dvd (P i) D_total r)
    have h_key : ratPolyEval (F i) a = (intPolyEval (G idx i) b : ℚ) := by
      exact ratPolyEval_eq_intPolyEval_on_residue
        (F := F i) (P := P i) (Q := G idx i) (H := H)
        hD_total_pos (hF_int i) (hP_eval i) r b a rfl hH rfl
    have h_eq : ratPolyEval (F i) a = (v i : ℚ) := by
      rw [h_key]
      exact_mod_cast hGb i
    exact h_eq

/-! ## The displayed integer-valued factorization example -/

/-- The falling factorial polynomial `x(x-1)...(x-k+1)` in `ℚ[x]`. -/
noncomputable def fallingFactorialRatPoly (k : ℕ) : RatPoly 1 :=
  Finset.prod (Finset.range k) fun i => X (0 : Fin 1) - C (i : ℚ)

/-- The binomial-coefficient polynomial `(x choose k)` over `ℚ[x]`, represented as
`(x(x-1)...(x-k+1))/k!`. -/
noncomputable def binomialRatPoly (k : ℕ) : RatPoly 1 :=
  C ((Nat.factorial k : ℚ)⁻¹) * fallingFactorialRatPoly k

/-- Source claim behind `pyth.tex` lines 185--186: the binomial-coefficient polynomial
is integer-valued. -/
theorem binomialRatPoly_intValued (k : ℕ) : IsIntValued (binomialRatPoly k) := by
  intro a
  refine ⟨(Ring.choose (a 0) k : ℤ), ?_⟩
  simp only [binomialRatPoly, fallingFactorialRatPoly, eval_mul, eval_C, eval_prod,
    eval_sub, eval_X]
  have hprod :
      ∏ x ∈ Finset.range k, ((a 0 : ℚ) - x) =
        (Nat.factorial k : ℚ) * ((Ring.choose (a 0) k : ℤ) : ℚ) := by
    rw [← descPochhammer_eval_eq_prod_range (R := ℚ) k (a 0 : ℚ)]
    rw [← descPochhammer_eval_cast (R := ℚ) k (a 0)]
    have hz :=
      Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) (r := a 0) (n := k)
    simpa [Polynomial.eval_eq_smeval, nsmul_eq_mul] using
      congrArg (fun z : ℤ => (z : ℚ)) hz
  rw [hprod]
  field_simp [Nat.factorial_ne_zero]

/-- The displayed identity `x(x-1)...(x-k+1) = k! * (x choose k)` from
`pyth.tex` lines 185--186. -/
theorem fallingFactorial_eq_factorial_mul_binomialRatPoly (k : ℕ) :
    fallingFactorialRatPoly k =
      C (Nat.factorial k : ℚ) * binomialRatPoly k := by
  rw [binomialRatPoly]
  rw [← mul_assoc, ← C_mul]
  simp [Nat.factorial_ne_zero]

/-- Source-level placeholder for `pyth.tex` lines 179--189: `Int(ℤ)` does not have
unique factorization into irreducibles. The displayed falling-factorial identity above
is the motivating example described in the paper. -/
theorem integerValued_polynomial_ring_not_uniqueFactorization :
    ¬ UniqueFactorizationMonoid (IntegerValuedPoly 1) := by
  classical
  let x : IntegerValuedPoly 1 := ⟨X (0 : Fin 1), by
    intro a
    exact ⟨a 0, by simp⟩⟩
  let b : IntegerValuedPoly 1 := ⟨binomialRatPoly 2, binomialRatPoly_intValued 2⟩
  have hdivprod : (2 : IntegerValuedPoly 1) ∣ x * (x - 1) := by
    refine ⟨b, ?_⟩
    apply Subtype.ext
    change
      (X (0 : Fin 1)) * ((X (0 : Fin 1)) - 1) =
        (C (2 : ℚ) * binomialRatPoly 2)
    trans fallingFactorialRatPoly 2
    · simp [fallingFactorialRatPoly, Finset.prod_range_succ]
    · have hf := fallingFactorial_eq_factorial_mul_binomialRatPoly 2
      norm_num at hf
      exact hf
  have hnotdivx : ¬ (2 : IntegerValuedPoly 1) ∣ x := by
    rintro ⟨q, hq⟩
    obtain ⟨z, hz⟩ := q.2 (fun _ : Fin 1 => (1 : ℤ))
    have h :=
      congrArg
        (fun p : RatPoly 1 => eval (fun _ : Fin 1 => (1 : ℚ)) p)
        (congrArg Subtype.val hq)
    have hz' : eval (fun _ : Fin 1 => (1 : ℚ)) q.1 = (z : ℚ) := hz
    have hrat :
        (1 : ℚ) =
          (eval (fun _ : Fin 1 => (1 : ℚ))
            ((2 : IntegerValuedPoly 1) : RatPoly 1)) * (z : ℚ) := by
      simpa [x, hz'] using h
    have htwo :
        eval (fun _ : Fin 1 => (1 : ℚ))
          ((2 : IntegerValuedPoly 1) : RatPoly 1) = (2 : ℚ) := by
      change eval (fun _ : Fin 1 => (1 : ℚ)) (C (2 : ℚ) : RatPoly 1) = (2 : ℚ)
      simp
    rw [htwo] at hrat
    have hint : (1 : ℤ) = 2 * z := by
      exact_mod_cast hrat
    omega
  have hnotdivxm1 : ¬ (2 : IntegerValuedPoly 1) ∣ x - 1 := by
    rintro ⟨q, hq⟩
    obtain ⟨z, hz⟩ := q.2 (fun _ : Fin 1 => (0 : ℤ))
    have h :=
      congrArg
        (fun p : RatPoly 1 => eval (fun _ : Fin 1 => (0 : ℚ)) p)
        (congrArg Subtype.val hq)
    have hz' : eval (fun _ : Fin 1 => (0 : ℚ)) q.1 = (z : ℚ) := hz
    have hz0 : constantCoeff (q.1 : RatPoly 1) = (z : ℚ) := by
      simpa using hz'
    have hrat :
        (-1 : ℚ) =
          constantCoeff (((2 : IntegerValuedPoly 1) : RatPoly 1)) * (z : ℚ) := by
      simpa [x, hz0] using h
    have htwo :
        constantCoeff (((2 : IntegerValuedPoly 1) : RatPoly 1)) = (2 : ℚ) := by
      change constantCoeff (C (2 : ℚ) : RatPoly 1) = (2 : ℚ)
      simp
    rw [htwo] at hrat
    have hint : (-1 : ℤ) = 2 * z := by
      exact_mod_cast hrat
    omega
  have hnotprime : ¬ Prime (2 : IntegerValuedPoly 1) := by
    intro hp
    exact (hp.not_dvd_mul hnotdivx hnotdivxm1) hdivprod
  have isUnit_of_val_C_int :
      ∀ (p : IntegerValuedPoly 1) (z : ℤ),
        p.1 = (C (z : ℚ) : RatPoly 1) → IsUnit z → IsUnit p := by
    intro p z hp hzunit
    rw [isUnit_iff_dvd_one]
    obtain ⟨w, hw⟩ := (isUnit_iff_dvd_one.mp hzunit)
    refine ⟨⟨(C (w : ℚ) : RatPoly 1), ?_⟩, ?_⟩
    · intro a
      exact ⟨w, by simp⟩
    · apply Subtype.ext
      change (1 : RatPoly 1) = p.1 * C (w : ℚ)
      rw [hp]
      have hwq : (1 : ℚ) = (z : ℚ) * (w : ℚ) := by
        exact_mod_cast hw
      calc
        (1 : RatPoly 1) = C (1 : ℚ) := by simp
        _ = C ((z : ℚ) * (w : ℚ)) := by rw [hwq]
        _ = C (z : ℚ) * C (w : ℚ) := by simp
  intro hUFM
  haveI := hUFM
  have hirr : Irreducible (2 : IntegerValuedPoly 1) := by
    refine ⟨?notunit, ?factor⟩
    · intro hunit
      exact hnotdivx (hunit.dvd : (2 : IntegerValuedPoly 1) ∣ x)
    · intro a c hac
      have hacv : (a.1 : RatPoly 1) * c.1 = (C (2 : ℚ) : RatPoly 1) := by
        have h := congrArg Subtype.val hac
        have htwo :
            (((2 : IntegerValuedPoly 1) : RatPoly 1)) = (C (2 : ℚ) : RatPoly 1) := by
          rfl
        simpa [htwo] using h.symm
      have hprod_ne : (a.1 * c.1 : RatPoly 1) ≠ 0 := by
        rw [hacv]
        norm_num
      have ha_ne : (a.1 : RatPoly 1) ≠ 0 := by
        intro ha
        exact hprod_ne (by simp [ha])
      have hc_ne : (c.1 : RatPoly 1) ≠ 0 := by
        intro hc
        exact hprod_ne (by simp [hc])
      have htd :=
        MvPolynomial.totalDegree_mul_of_isDomain
          (f := (a.1 : RatPoly 1)) (g := (c.1 : RatPoly 1)) ha_ne hc_ne
      have hsum : (a.1 : RatPoly 1).totalDegree + (c.1 : RatPoly 1).totalDegree = 0 := by
        rw [hacv] at htd
        simp at htd
        exact htd.symm
      have ha_td0 : (a.1 : RatPoly 1).totalDegree = 0 := by omega
      have hc_td0 : (c.1 : RatPoly 1).totalDegree = 0 := by omega
      have ha_const : (a.1 : RatPoly 1) = C (constantCoeff (a.1 : RatPoly 1)) := by
        exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp ha_td0
      have hc_const : (c.1 : RatPoly 1) = C (constantCoeff (c.1 : RatPoly 1)) := by
        exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hc_td0
      obtain ⟨za, hza⟩ := a.2 (fun _ : Fin 1 => (0 : ℤ))
      obtain ⟨zc, hzc⟩ := c.2 (fun _ : Fin 1 => (0 : ℤ))
      have hza_eval : eval (fun _ : Fin 1 => (0 : ℚ)) (a.1 : RatPoly 1) = (za : ℚ) := hza
      have hzc_eval : eval (fun _ : Fin 1 => (0 : ℚ)) (c.1 : RatPoly 1) = (zc : ℚ) := hzc
      have hza_eval_const :
          eval (fun _ : Fin 1 => (0 : ℚ)) (a.1 : RatPoly 1) =
            constantCoeff (a.1 : RatPoly 1) := by
        rw [ha_const]
        simp
      have hzc_eval_const :
          eval (fun _ : Fin 1 => (0 : ℚ)) (c.1 : RatPoly 1) =
            constantCoeff (c.1 : RatPoly 1) := by
        rw [hc_const]
        simp
      have hza_coeff : constantCoeff (a.1 : RatPoly 1) = (za : ℚ) := by
        exact hza_eval_const.symm.trans hza_eval
      have hzc_coeff : constantCoeff (c.1 : RatPoly 1) = (zc : ℚ) := by
        exact hzc_eval_const.symm.trans hzc_eval
      have ha_const_z : a.1 = (C (za : ℚ) : RatPoly 1) := by
        rw [ha_const, hza_coeff]
      have hc_const_z : c.1 = (C (zc : ℚ) : RatPoly 1) := by
        rw [hc_const, hzc_coeff]
      have hccprod := congrArg (fun p : RatPoly 1 => constantCoeff p) hacv
      have hratprod :
          constantCoeff (a.1 : RatPoly 1) * constantCoeff (c.1 : RatPoly 1) =
            (2 : ℚ) := by
        simpa using hccprod
      have hintprod : za * zc = (2 : ℤ) := by
        exact_mod_cast
          (by
            simpa [hza_coeff, hzc_coeff] using hratprod :
              (za : ℚ) * (zc : ℚ) = (2 : ℚ))
      have hIz : IsUnit za ∨ IsUnit zc := by
        have hp : Prime (2 : ℤ) := by norm_num
        exact hp.irreducible.isUnit_or_isUnit hintprod.symm
      rcases hIz with hzaunit | hzcunit
      · left
        exact isUnit_of_val_C_int a za ha_const_z hzaunit
      · right
        exact isUnit_of_val_C_int c zc hc_const_z hzcunit
  exact hnotprime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)

end LeanPool.PythagoreanPolynomialParametrization
