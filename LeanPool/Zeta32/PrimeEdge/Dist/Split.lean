/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Dist.Mult

/-! Dissection of `∏_{j ∈ S} (t + j)` under `t = p u - b`, the truncated
local functional `dl` on a general numerator `F` (`discLocal r n p b A = dl r n p b (X A)`),
the error functional `Err`, and the exactness of the distribution formula on `Q · D_{5n}`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

noncomputable section

/-- Near poles of `S` on the disc `b`. -/
def nearS (p b : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (S.filter (fun j => j % p = b)).image (fun j => (j - b) / p)

/-- Far factors of `S` on the disc `b`. -/
def farS (p b : ℕ) (S : Finset ℕ) : ℚ[X] :=
  ∏ j ∈ S.filter (fun j => j % p ≠ b), (C ((j : ℚ) - b) + C (p : ℚ) * X)

lemma sub_eq_mul_div {p j b : ℕ} (h : j % p = b) : j - b = p * (j / p) := by
  have := Nat.mod_add_div j p
  rw [h] at this
  omega

lemma sub_div_eq {p j b : ℕ} (hp : 0 < p) (h : j % p = b) : (j - b) / p = j / p := by
  rw [sub_eq_mul_div h, Nat.mul_div_cancel_left _ hp]

lemma cast_eq_near {p j b : ℕ} (hp : 0 < p) (h : j % p = b) :
    (j : ℚ) = p * (((j - b) / p : ℕ) : ℚ) + b := by
  rw [sub_div_eq hp h]
  have := Nat.mod_add_div j p
  rw [h] at this
  have : ((b + p * (j / p) : ℕ) : ℚ) = j := by rw [this]
  push_cast at this
  linarith

lemma injOn_near {p b : ℕ} (hp : 0 < p) (S : Finset ℕ) :
    Set.InjOn (fun j => (j - b) / p) (S.filter (fun j => j % p = b) : Set ℕ) := by
  intro j hj j' hj' h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hj hj'
  have h1 := cast_eq_near hp hj.2
  have h2 := cast_eq_near hp hj'.2
  simp only at h
  rw [h] at h1
  exact_mod_cast h1.trans h2.symm

lemma card_nearS {p b : ℕ} (hp : 0 < p) (S : Finset ℕ) :
    (nearS p b S).card = (S.filter (fun j => j % p = b)).card :=
  Finset.card_image_of_injOn (injOn_near hp S)

lemma nearSet_eq (n p b : ℕ) : nearSet n p b = nearS p b (Finset.Icc 1 (5 * n)) := rfl

lemma farProd_eq (n p b : ℕ) : farProd n p b = farS p b (Finset.Icc 1 (5 * n)) := rfl

/-- **Dissection** of `∏_{j∈S} (t + j)` at `t = p u - b`. -/
theorem comp_mprod {p : ℕ} (hp : 0 < p) (b : ℕ) (S : Finset ℕ) :
    (mprod S).comp (C (p : ℚ) * X - C (b : ℚ)) =
      C ((p : ℚ) ^ (S.filter (fun j => j % p = b)).card) * mprod (nearS p b S) * farS p b S := by
  unfold mprod farS nearS
  rw [prod_comp, ← Finset.prod_filter_mul_prod_filter_not S (fun j => j % p = b)]
  congr 1
  · rw [Finset.prod_image (injOn_near hp S)]
    rw [Finset.prod_congr rfl (g := fun j => C (p : ℚ) * (X + C (((j - b) / p : ℕ) : ℚ))),
      Finset.prod_mul_distrib, Finset.prod_const, C_pow]
    intro j hj
    rw [Finset.mem_filter] at hj
    simp only [add_comp, X_comp, C_comp]
    rw [cast_eq_near hp hj.2, C_add, C_mul]
    ring
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [add_comp, X_comp, C_comp, C_sub]
    ring

lemma farS_coeff_zero_ne {p b : ℕ} (hb : b < p) (S : Finset ℕ) : (farS p b S).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero, farS, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [Finset.mem_filter] at hj
  simp only [eval_add, eval_C, eval_mul, eval_X, mul_zero, add_zero]
  intro h
  have : j = b := by exact_mod_cast sub_eq_zero.mp h
  exact hj.2 (by rw [this]; exact Nat.mod_eq_of_lt hb)

lemma ps_mul_inv {F : ℚ[X]} (h : F.coeff 0 ≠ 0) : (F : PowerSeries ℚ) * (F : PowerSeries ℚ)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rwa [Polynomial.constantCoeff_coe])

/-- The truncated local functional on a general numerator `F`. -/
def dl (r : ℚ) (n p b : ℕ) (F : ℚ[X]) : ℚ :=
  (p : ℚ) ^ (-((nearSet n p b).card : ℤ)) *
    locValue (r * p) (PowerSeries.trunc (truncOrder n)
      ((F.comp (C (p : ℚ) * X - C (b : ℚ)) : PowerSeries ℚ) * (farProd n p b : PowerSeries ℚ)⁻¹))
      (nearSet n p b)

lemma dl_add (r : ℚ) (n p b : ℕ) (F G : ℚ[X]) : dl r n p b (F + G) = dl r n p b F + dl r n p b G
  := by
  unfold dl
  rw [add_comp, Polynomial.coe_add, add_mul, map_add, dist_locValue_add, mul_add]

lemma dl_C_mul (r : ℚ) (n p b : ℕ) (c : ℚ) (F : ℚ[X]) :
    dl r n p b (C c * F) = c * dl r n p b F := by
  unfold dl
  rw [mul_comp, C_comp, Polynomial.coe_mul, Polynomial.coe_C, mul_assoc, PowerSeries.trunc_C_mul,
    dist_locValue_C_mul]
  ring

/-- The error of the truncated distribution formula on a numerator `F`. -/
def Err (r : ℚ) (n p : ℕ) (F : ℚ[X]) : ℚ :=
  locValue r F (Finset.Icc 1 (5 * n)) - (p : ℚ) ^ (-2 : ℤ) * ∑ b ∈ Finset.range p, dl r n p b F

lemma Err_add (r : ℚ) (n p : ℕ) (F G : ℚ[X]) : Err r n p (F + G) = Err r n p F + Err r n p G := by
  unfold Err
  simp only [dist_locValue_add, dl_add, Finset.sum_add_distrib]
  ring

lemma Err_C_mul (r : ℚ) (n p : ℕ) (c : ℚ) (F : ℚ[X]) : Err r n p (C c * F) = c * Err r n p F := by
  unfold Err
  simp only [dist_locValue_C_mul, dl_C_mul, ← Finset.mul_sum]
  ring

lemma Err_sum {ι : Type*} (r : ℚ) (n p : ℕ) (t : Finset ι) (F : ι → ℚ[X]) :
    Err r n p (∑ i ∈ t, F i) = ∑ i ∈ t, Err r n p (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have := Err_C_mul r n p 0 0
    simp only [C_0, zero_mul] at this
    simpa using this
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Err_add, ih]

lemma locValue_mul_mprod (s : ℚ) (M : Finset ℕ) (P : ℚ[X]) :
    locValue s (P * mprod M) M = locPoly s P := by
  have := locValue_pf s M P (fun _ => 0)
  simpa using this

lemma natDegree_comp_lin_le (Q : ℚ[X]) (p b : ℕ) :
    (Q.comp (C (p : ℚ) * X - C (b : ℚ))).natDegree ≤ Q.natDegree := by
  refine (natDegree_comp_le).trans ?_
  have : (C (p : ℚ) * X - C (b : ℚ)).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans ?_
    simp only [natDegree_C, max_le_iff, zero_le, and_true]
    exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  calc Q.natDegree * (C (p : ℚ) * X - C (b : ℚ)).natDegree ≤ Q.natDegree * 1 :=
        Nat.mul_le_mul_left _ this
    _ = Q.natDegree := mul_one _

lemma card_nearSet_le {p : ℕ} (hp : 0 < p) (n b : ℕ) : (nearSet n p b).card ≤ 5 * n := by
  rw [nearSet_eq, card_nearS hp]
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- On the disc `b`, `dl` of `Q · D_{5n}` is `locPoly (r p) (Q (p u - b))`. -/
lemma dl_poly {p : ℕ} (hp : 0 < p) (r : ℚ) (n b : ℕ) (hb : b < p) (Q : ℚ[X])
    (hQ : Q.natDegree + 5 * n < truncOrder n) :
    dl r n p b (Q * mprod (Finset.Icc 1 (5 * n))) =
      locPoly (r * p) (Q.comp (C (p : ℚ) * X - C (b : ℚ))) := by
  set M := Finset.Icc 1 (5 * n)
  set Qb := Q.comp (C (p : ℚ) * X - C (b : ℚ))
  set ℓ := (M.filter (fun j => j % p = b)).card with hℓ
  have hsplit := comp_mprod hp b M
  have hF := ps_mul_inv (farS_coeff_zero_ne hb M)
  unfold dl
  rw [mul_comp, hsplit, nearSet_eq, farProd_eq]
  have hps : ((Qb * (C ((p : ℚ) ^ ℓ) * mprod (nearS p b M) * farS p b M) : ℚ[X]) :
      PowerSeries ℚ) * (farS p b M : PowerSeries ℚ)⁻¹ =
      ((C ((p : ℚ) ^ ℓ) * (Qb * mprod (nearS p b M)) : ℚ[X]) : PowerSeries ℚ) := by
    simp only [Polynomial.coe_mul]
    calc _ = ((C ((p : ℚ) ^ ℓ) : ℚ[X]) : PowerSeries ℚ) * ((Qb : PowerSeries ℚ) *
          (mprod (nearS p b M) : PowerSeries ℚ)) * ((farS p b M : PowerSeries ℚ) *
          (farS p b M : PowerSeries ℚ)⁻¹) := by ring
      _ = _ := by rw [hF, mul_one]
  rw [hps, PowerSeries.trunc_coe_eq_self, dist_locValue_C_mul, locValue_mul_mprod, card_nearS
    hp, ← hℓ]
  · rw [← mul_assoc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast
    hp.ne')),
      one_mul]
  · refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
    refine lt_of_le_of_lt natDegree_mul_le ?_
    rw [natDegree_mprod]
    have h1 : Qb.natDegree ≤ Q.natDegree := natDegree_comp_lin_le Q p b
    have h2 : (nearS p b M).card ≤ 5 * n := by
      have := card_nearSet_le hp n b
      rwa [nearSet_eq] at this
    unfold truncOrder at hQ ⊢
    omega

/-- **The distribution formula is exact on `Q · D_{5n}`.** -/
theorem Err_poly {p : ℕ} (hp : 0 < p) (r : ℚ) (n : ℕ) (Q : ℚ[X])
    (hQ : Q.natDegree + 5 * n < truncOrder n) :
    Err r n p (Q * mprod (Finset.Icc 1 (5 * n))) = 0 := by
  unfold Err
  rw [locValue_mul_mprod, Finset.sum_congr rfl fun b hb =>
    dl_poly hp r n b (Finset.mem_range.mp hb) Q hQ, sum_locPoly_comp hp]
  have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [← mul_assoc, zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ this), one_mul, sub_self]

end

end Zeta32.PrimeEdge

end
