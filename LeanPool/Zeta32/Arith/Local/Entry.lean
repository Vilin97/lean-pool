/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta5Irrational.Arith.CoefficientMatrix
public import LeanPool.Zeta32.Arith.Local.PoleFun
public import LeanPool.Zeta32.Arith.Local.Binom
public import LeanPool.Zeta32.Arith.Small.Gram

/-!
# The entry functional and its local bound

For a numerator `A`, `Lfun r n A = U_r(A / D_{5n})` (the proof notes, §0):
`U_r(t^e) = (e+1)B_e + 2rB_{e+1}`, `U_r((t+j)^{-1}) = 2jX + β_j`, i.e.

  `Lfun r n A = (∑_j res_j · 2j) X + polynomialMoment r (A /ₘ D_{5n}) + ∑_j res_j β_j`.

* `Lfun_numerator` : `Lfun r n (numerator n m) = X · slope n m + intercept r n m`;
* `det_basis_change` : a monic basis `f_i` of degree `i` does not change the Hankel determinant;
* `Lfun_GV` (the proof notes, Lemma 4, entrywise, by class-wise partial fractions instead of the
  Tate-algebra functional): if `A` has at least `e_c` zeros in every class `c` mod `p`
  (`Adm`), `ℓ_c` is the number of poles `-j` (`1 ≤ j ≤ 5n`) in class `c`, `5n < p²`,
  `p ∤ den r` and `deg A ≤ 10n - 2`, then every coefficient of `Lfun r n A` has
  `v_p ≥ min_c (e_c + [c = 0] - ℓ_c) - 2`.
-/

public section

open Finset Polynomial

namespace Zeta32.Arith.Local

/-! ### The poles -/

/-- The pole set `{-1, …, -5n}`. -/
def Pl5 (n : ℕ) : Finset ℤ := (Finset.Icc 1 (5 * n)).image fun j : ℕ => -(j : ℤ)

lemma neg_natCast_injective : Function.Injective fun j : ℕ => -(j : ℤ) := by
  intro a b h
  simpa using h

lemma card_Pl5 (n : ℕ) : (Pl5 n).card = 5 * n := by
  unfold Pl5
  rw [Finset.card_image_of_injective _ neg_natCast_injective]
  simp

lemma D_eq_piPl (m : ℕ) : Zeta32.D m = piPl ((Finset.Icc 1 m).image fun j : ℕ => -(j : ℤ)) := by
  unfold Zeta32.D piPl
  rw [Finset.prod_image fun a _ b _ h => neg_natCast_injective h]
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rw [C_neg, sub_neg_eq_add]

lemma resP_Pl5 (A : ℚ[X]) (n j : ℕ) :
    resP A (Pl5 n) (-(j : ℤ)) =
      A.eval (-(j : ℚ)) / ∏ l ∈ (Finset.Icc 1 (5 * n)).erase j, ((l : ℚ) - (j : ℚ)) := by
  unfold resP Pl5
  rw [show (-(j : ℤ)) = (fun j : ℕ => -(j : ℤ)) j from rfl,
    ← Finset.image_erase neg_natCast_injective,
    Finset.prod_image fun a _ b _ h => neg_natCast_injective h]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  ring

/-! ### The entry functional -/

/-- `U_r(A / D_{5n})`, as a polynomial in `X`. -/
noncomputable def Lfun (r : ℚ) (n : ℕ) (A : ℚ[X]) : ℚ[X] :=
  C (∑ j ∈ Finset.Icc 1 (5 * n), resP A (Pl5 n) (-(j : ℤ)) * (2 * (j : ℚ))) * X +
    C (polynomialMoment r (A /ₘ Zeta32.D (5 * n)) +
      ∑ j ∈ Finset.Icc 1 (5 * n), resP A (Pl5 n) (-(j : ℤ)) * beta r j)

/-- The local residue formula is the same numerator functional used by the small-prime
Gram calculation. -/
lemma Lfun_eq_Ufun (r : ℚ) (n : ℕ) (A : ℚ[X]) :
    Lfun r n A = Small.Ufun r n A := by
  unfold Lfun Small.Ufun
  simp only [resP_Pl5, mul_add, ← mul_assoc, ← C_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [← map_sum, map_add]
  ring

lemma Lfun_numerator (r : ℚ) (n m : ℕ) :
    Lfun r n (numerator n m) = X * C (slope n m) + C (intercept r n m) := by
  rw [Lfun_eq_Ufun]
  exact Small.Ufun_entry r n m

lemma Lfun_add (r : ℚ) (n : ℕ) (A B : ℚ[X]) :
    Lfun r n (A + B) = Lfun r n A + Lfun r n B := by
  simp only [Lfun_eq_Ufun]
  exact Small.Ufun_add r n A B

lemma Lfun_C_mul (r : ℚ) (n : ℕ) (c : ℚ) (A : ℚ[X]) :
    Lfun r n (C c * A) = C c * Lfun r n A := by
  simp only [Lfun_eq_Ufun]
  exact Small.Ufun_C_mul r n c A

/-! ### Change of basis -/

/-- The coefficient matrix of a family of polynomials. -/
noncomputable abbrev coeffMat {h : ℕ} (E : Fin h → ℚ[X]) :
    Matrix (Fin h) (Fin h) ℚ := Zeta5Irrational.coeffMat E

lemma sum_coeffMat {h : ℕ} (E : Fin h → ℚ[X])
    (hE : ∀ a, (E a).natDegree < h) (a : Fin h) :
    E a = ∑ k : Fin h, C (coeffMat E a k) * X ^ (k : ℕ) :=
  Zeta5Irrational.sum_coeffMat E hE a

lemma det_coeffMat {h : ℕ} (E : Fin h → ℚ[X]) (hmon : ∀ i, (E i).Monic)
    (hdeg : ∀ i, (E i).natDegree = i) : (coeffMat E).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [coeffMat, Zeta5Irrational.coeffMat, Matrix.of_apply]
    have := (hmon i).leadingCoeff
    rwa [leadingCoeff, hdeg i] at this
  · intro i j hij
    rw [coeffMat, Zeta5Irrational.coeffMat, Matrix.of_apply]
    apply coeff_eq_zero_of_natDegree_lt
    rw [hdeg i]
    exact hij

/-- **Change of basis** for a `ℚ`-linear functional on numerators. -/
theorem det_basis_change {h : ℕ} (L : ℚ[X] → ℚ[X]) (hadd : ∀ A B, L (A + B) = L A + L B)
    (hC : ∀ c A, L (C c * A) = C c * L A) (W : ℚ[X]) (f : Fin h → ℚ[X])
    (hmon : ∀ i, (f i).Monic) (hdeg : ∀ i, (f i).natDegree = i) :
    (Matrix.of fun i k => L (f i * f k * W)).det =
      (Matrix.of fun i k : Fin h => L (X ^ (i.val + k.val) * W)).det := by
  have h0 : L 0 = 0 := by
    have := hC 0 0
    simpa using this
  have hsum : ∀ {ι : Type} (s : Finset ι) (g : ι → ℚ[X]), L (∑ i ∈ s, g i) = ∑ i ∈ s, L (g i) := by
    intro ι s g
    classical
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hlt : ∀ a, (f a).natDegree < h := fun a => by rw [hdeg a]; exact a.isLt
  set Cm := (coeffMat f).map (C : ℚ →+* ℚ[X]) with hCm
  set G := Matrix.of fun i k : Fin h => L (X ^ (i.val + k.val) * W) with hG
  have hM : (Matrix.of fun i k => L (f i * f k * W)) = Cm * G * Cm.transpose := by
    refine Matrix.ext fun a b => ?_
    have hexp : f a * f b * W = ∑ k : Fin h, ∑ l : Fin h,
        C (coeffMat f a k * coeffMat f b l) * (X ^ ((k : ℕ) + (l : ℕ)) * W) := by
      conv_lhs => rw [sum_coeffMat f hlt a, sum_coeffMat f hlt b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul, pow_add]; ring
    rw [Matrix.of_apply, hexp, hsum]
    simp only [hsum, hC, Matrix.mul_apply, Matrix.transpose_apply, hCm, Matrix.map_apply, hG,
      Finset.sum_mul, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul]; ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hCm, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, det_coeffMat f hmon hdeg]
  simp

/-- The Hankel matrix of `Q` is the matrix of `Lfun` on the monomial numerators. -/
lemma hankel_eq_Lfun (r : ℚ) (n : ℕ) :
    ((X : ℚ[X]) • (Zeta32.B n).map C + (Zeta32.A r n).map C) =
      Matrix.of fun i k : Fin (3 * n) => Lfun r n (X ^ (i.val + k.val) * Zeta32.D n ^ 4) := by
  refine Matrix.ext fun i k => ?_
  rw [Matrix.of_apply, show X ^ (i.val + k.val) * Zeta32.D n ^ 4 = numerator n (i.val + k.val)
    from rfl, Lfun_numerator]
  simp [Zeta32.A, Zeta32.B, smul_eq_mul]

/-- `Q` in any monic basis `f_i` of degree `i`. -/
theorem Q_eq_det_basis (r : ℚ) (n : ℕ) (f : Fin (3 * n) → ℚ[X]) (hmon : ∀ i, (f i).Monic)
    (hdeg : ∀ i, (f i).natDegree = i) :
    Zeta32.Q r n = (Matrix.of fun i k => Lfun r n (f i * f k * Zeta32.D n ^ 4)).det := by
  rw [det_basis_change (Lfun r n) (Lfun_add r n) (Lfun_C_mul r n) _ f hmon hdeg, Zeta32.Q,
    hankel_eq_Lfun]

/-! ### Valuations of the harmonic numbers and of `β_j` -/

variable {p : ℕ} [hp : Fact p.Prime]

lemma VG_H {e j : ℕ} (hj : j < p ^ 2) : VG p (H e j) (-(e : ℚ)) := by
  unfold H
  refine VG.sum _ fun v hv => ?_
  rw [Finset.mem_Icc] at hv
  rw [one_div]
  apply VG.inv
  rw [show ((v : ℚ) ^ e) = ((v ^ e : ℕ) : ℚ) by push_cast; ring, padicValRat.of_nat,
    padicValNat.pow v e]
  have h1 : padicValNat p v ≤ 1 := by
    by_contra hne
    rw [not_le] at hne
    have h2 : p ^ 2 ∣ v := (padicValNat_dvd_iff_le (by omega)).mpr hne
    exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
  have h3 : e * padicValNat p v ≤ e := by
    calc e * padicValNat p v ≤ e * 1 := Nat.mul_le_mul_left _ h1
      _ = e := mul_one e
  have h4 : ((e * padicValNat p v : ℕ) : ℚ) ≤ e := by exact_mod_cast h3
  simpa using h4

lemma VG_beta_weak {r : ℚ} (hr : VG p r 0) {j : ℕ} (hj : j < p ^ 2) :
    VG p (beta r j) (-3) := by
  unfold beta
  have h2 : VG p (2 : ℚ) 0 := by simpa using VG.natCast (p := p) 2
  have hjj : VG p (j : ℚ) 0 := VG.natCast j
  have t1 : VG p (2 * r) (-3) := (h2.mul hr).mono (by norm_num)
  have t2 : VG p (2 * (j : ℚ) * H 3 j) (-3) := by
    have := (h2.mul hjj).mul (VG_H (p := p) (e := 3) hj)
    exact this.mono (by norm_num)
  have t3 : VG p (2 * r * (j : ℚ) * H 2 j) (-3) := by
    have := ((h2.mul hr).mul hjj).mul (VG_H (p := p) (e := 2) hj)
    exact this.mono (by norm_num)
  exact (t1.sub t2).add t3

lemma VG_beta_strong {r : ℚ} (hr : VG p r 0) {j : ℕ} (hj : j < p ^ 2) (hpj : p ∣ j) :
    VG p (beta r j) (-2) := by
  unfold beta
  have h2 : VG p (2 : ℚ) 0 := by simpa using VG.natCast (p := p) 2
  have hjj : VG p (j : ℚ) 1 := by
    have := VG_int_one (p := p) (z := (j : ℤ)) (by exact_mod_cast hpj)
    simpa using this
  have t1 : VG p (2 * r) (-2) := (h2.mul hr).mono (by norm_num)
  have t2 : VG p (2 * (j : ℚ) * H 3 j) (-2) := by
    have := (h2.mul hjj).mul (VG_H (p := p) (e := 3) hj)
    exact this.mono (by norm_num)
  have t3 : VG p (2 * r * (j : ℚ) * H 2 j) (-2) := by
    have := ((h2.mul hr).mul hjj).mul (VG_H (p := p) (e := 2) hj)
    exact this.mono (by norm_num)
  exact (t1.sub t2).add t3

/-! ### The local bound -/
omit hp in
lemma sep_Pl5 {n : ℕ} (hn : 5 * n < p ^ 2) : Sep p (Pl5 n) := by
  intro r hr s hs hrs _ hdvd
  unfold Pl5 at hr hs
  rw [Finset.mem_image] at hr hs
  obtain ⟨j, hj, rfl⟩ := hr
  obtain ⟨l, hl, rfl⟩ := hs
  rw [Finset.mem_Icc] at hj hl
  have h0 : -(j : ℤ) - -(l : ℤ) = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdvd
    have : ((p ^ 2 : ℕ) : ℤ) = (p : ℤ) ^ 2 := by push_cast; ring
    rw [← this, abs_lt]
    constructor <;> push_cast <;> omega
  exact hrs (by linarith)

lemma class_neg_eq_zero_iff (j : ℕ) : (((-(j : ℤ)) : ℤ) : ZMod p) = 0 ↔ p ∣ j := by
  rw [Int.cast_neg, neg_eq_zero, Int.cast_natCast, ZMod.natCast_eq_zero_iff]

/-- **Local bound** for one entry. -/
theorem Lfun_GV {r : ℚ} (hr : VG p r 0) {n : ℕ} (hn : 5 * n < p ^ 2) {A : ℚ[X]}
    {e : ZMod p → ℤ} (hA : Adm p A e) (hdeg : A.natDegree + 2 ≤ 10 * n) (β : ℚ)
    (hβ : ∀ c : ZMod p,
      β ≤ (e c : ℚ) + (if c = 0 then 1 else 0) - (plc p (Pl5 n) c).card) :
    GV p (Lfun r n A) (β - 2) := by
  have hsep := sep_Pl5 (p := p) hn
  have hmem : ∀ j ∈ Finset.Icc 1 (5 * n), -(j : ℤ) ∈ Pl5 n := fun j hj =>
    Finset.mem_image_of_mem _ hj
  have hjp : ∀ j ∈ Finset.Icc 1 (5 * n), j < p ^ 2 := fun j hj => by
    rw [Finset.mem_Icc] at hj; omega
  -- the residue bound in the form used below
  have hres : ∀ j ∈ Finset.Icc 1 (5 * n),
      VG p (resP A (Pl5 n) (-(j : ℤ))) (β + 1 - (if p ∣ j then 1 else 0)) := by
    intro j hj
    have h1 := VG_res hA (Pl5 n) hsep (hmem j hj)
    have h2 := hβ (((-(j : ℤ)) : ℤ) : ZMod p)
    refine h1.mono ?_
    by_cases hpj : p ∣ j
    · rw [ite_eq_left ((class_neg_eq_zero_iff j).mpr hpj)] at h2
      rw [ite_eq_left hpj]; linarith
    · rw [ite_eq_right (fun h => hpj ((class_neg_eq_zero_iff j).mp h))] at h2
      rw [ite_eq_right hpj]; linarith
  -- the slope
  have hslope : VG p (∑ j ∈ Finset.Icc 1 (5 * n), resP A (Pl5 n) (-(j : ℤ)) * (2 * (j : ℚ)))
      (β - 2) := by
    refine VG.sum _ fun j hj => ?_
    have h2j : VG p (2 * (j : ℚ)) 0 := by simpa using VG.natCast (p := p) (2 * j)
    have := (hres j hj).mul h2j
    refine this.mono ?_
    split_ifs <;> linarith
  -- the pole part of the intercept
  have hpole : VG p (∑ j ∈ Finset.Icc 1 (5 * n), resP A (Pl5 n) (-(j : ℤ)) * beta r j)
      (β - 2) := by
    refine VG.sum _ fun j hj => ?_
    by_cases hpj : p ∣ j
    · have := (hres j hj).mul (VG_beta_strong hr (hjp j hj) hpj)
      refine this.mono ?_
      rw [ite_eq_left hpj]; linarith
    · have := (hres j hj).mul (VG_beta_weak hr (hjp j hj))
      refine this.mono ?_
      rw [ite_eq_right hpj]; linarith
  -- the polynomial part
  have hpoly : VG p (polynomialMoment r (A /ₘ Zeta32.D (5 * n))) (β - 2) := by
    have hq : A /ₘ Zeta32.D (5 * n) = polyPart A (Pl5 n) := by
      rw [polyPart, D_eq_piPl]; rfl
    rw [hq]
    have hn1 : 1 ≤ n := by omega
    have hdq : (X * polyPart A (Pl5 n)).natDegree ≤ 5 * n - 1 := by
      have h1 := natDegree_polyPart_le A (Pl5 n)
      rw [card_Pl5] at h1
      have h2 := natDegree_mul_le (p := (X : ℚ[X])) (q := polyPart A (Pl5 n))
      rw [natDegree_X] at h2
      omega
    refine VG_polynomialMoment hr hdq (by omega) fun m _ => ?_
    rw [eval_mul, eval_X]
    by_cases hm : ((m : ℤ) : ZMod p) = 0
    · have hvm : VG p (m : ℚ) 1 := by
        have := VG_int_one (p := p) (z := (m : ℤ)) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hm)
        simpa using this
      have hq' := VG_polyPart_eval hA (Pl5 n) hsep (m : ℤ) (β - 1)
        (by have := hβ ((m : ℤ) : ZMod p); rw [ite_eq_left hm] at this; linarith)
        (fun s _ hs => by
          have := hβ ((s : ℤ) : ZMod p)
          rw [ite_eq_right (fun h => hs (h.trans hm.symm))] at this; linarith)
      have := hvm.mul hq'
      simp only [Int.cast_natCast] at this
      exact this.mono (by linarith)
    · have hvm : VG p (m : ℚ) 0 := VG.natCast m
      have hq' := VG_polyPart_eval hA (Pl5 n) hsep (m : ℤ) β
        (by have := hβ ((m : ℤ) : ZMod p); rw [ite_eq_right hm] at this; linarith)
        (fun s _ _ => by
          have := hβ ((s : ℤ) : ZMod p)
          split_ifs at this <;> linarith)
      have := hvm.mul hq'
      simp only [Int.cast_natCast] at this
      exact this.mono (by linarith)
  unfold Lfun
  refine GV.add ?_ (GV.C (hpoly.add hpole))
  have := GV.C_mul hslope (GV.X (p := p))
  simpa using this

end Zeta32.Arith.Local

end
