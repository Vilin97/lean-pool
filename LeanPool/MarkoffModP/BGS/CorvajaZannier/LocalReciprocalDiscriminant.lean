/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindDifferentDivisor
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Reciprocal normalization at a finite base place

This file supplies the local algebraic bridge used in the Corvaja--Zannier
middle game.  If a polynomial relation `f(v) = 0` has unit value `f(c)`, the
reciprocal parameter `z = (v-c)⁻¹` satisfies a monic integral equation.  The
normalization preserves primitive generation, becomes the minimal polynomial
under the full-degree hypothesis, and changes the discriminant only by a unit.
Consequently its discriminant has exactly the same order at every finite base
place as the discriminant of `f`.

The fixed-degree reflection/resultant identities are proved here because the
coefficient-reversal discriminant formula needed for a nonmonic relation was
not previously available in Mathlib in this form.
-/

@[expose] public section

namespace BGS.CorvajaZannier

open IsDedekindDomain Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- Reverse and exchange the two index blocks of a Sylvester matrix. -/
def reflectSylvesterEquiv (m n : ℕ) : Fin (n + m) ≃ Fin (m + n) :=
  (finCongr (Nat.add_comm n m)).trans Fin.revPerm

@[simp]
private theorem reflectSylvesterEquiv_symm_left (m n : ℕ) (j : Fin m) :
    (reflectSylvesterEquiv m n).symm (j.castAdd n) =
      (Fin.rev j).natAdd n := by
  ext
  simp [reflectSylvesterEquiv, Fin.rev]
  omega

@[simp]
private theorem reflectSylvesterEquiv_symm_right (m n : ℕ) (j : Fin n) :
    (reflectSylvesterEquiv m n).symm (j.natAdd m) =
      (Fin.rev j).castAdd m := by
  ext
  simp [reflectSylvesterEquiv, Fin.rev]
  omega

@[simp]
private theorem reflectSylvesterEquiv_symm_val (m n : ℕ) (i : Fin (m + n)) :
    ((reflectSylvesterEquiv m n).symm i : ℕ) = m + n - (i + 1) := by
  simp [reflectSylvesterEquiv, Fin.rev]

private theorem reflected_row_sub_reflected_shift
    (m n i j : ℕ) (_hi : i < m + n) (hj : j < m)
    (hji : j ≤ i) (hij : i ≤ j + n) :
    m + n - (i + 1) - (m - (j + 1)) = n - (i - j) := by
  omega

theorem sylvester_reflect (f g : R[X]) (m n : ℕ) :
    sylvester (reflect m f) (reflect n g) m n =
      (sylvester g f n m).reindex
        (reflectSylvesterEquiv m n) (reflectSylvesterEquiv m n) := by
  ext i j
  induction j using Fin.addCases with
  | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left,
        Matrix.reindex_apply, Matrix.submatrix_apply,
        reflectSylvesterEquiv_symm_left, Fin.addCases_right,
        reflectSylvesterEquiv_symm_val]
      simp only [coeff_reflect]
      split_ifs <;> simp_all [revAt] <;> try omega
      congr 1
      change revAtFun n ((i : ℕ) - j) = _
      rw [revAtFun, ite_eq_left (by omega)]
      exact (reflected_row_sub_reflected_shift m n i j i.isLt j.isLt
        (by omega) (by omega)).symm
  | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right,
        Matrix.reindex_apply, Matrix.submatrix_apply,
        reflectSylvesterEquiv_symm_right, Fin.addCases_left,
        reflectSylvesterEquiv_symm_val]
      simp only [coeff_reflect]
      split_ifs <;> simp_all [revAt] <;> try omega
      congr 1
      change revAtFun m ((i : ℕ) - j) = _
      rw [revAtFun, ite_eq_left (by omega)]
      simpa [Nat.add_comm] using
        (reflected_row_sub_reflected_shift n m i j (by omega) j.isLt
          (by omega) (by omega)).symm

/-- Reversing both coefficient lists changes the fixed-degree resultant only
by the standard interchange sign. -/
theorem resultant_reflect (f g : R[X]) (m n : ℕ) :
    resultant (reflect m f) (reflect n g) m n =
      (-1) ^ (m * n) * resultant f g m n := by
  rw [resultant, sylvester_reflect, Matrix.det_reindex_self, ← resultant]
  simpa [Nat.mul_comm] using resultant_comm g f n m

theorem reflect_derivative_relation (f : R[X]) (n : ℕ)
    (hf : f.natDegree ≤ n) :
    reflect (n - 1) f.derivative =
      C (n : R) * reflect n f - X * (reflect n f).derivative := by
  ext k
  by_cases hk0 : k = 0
  · subst k
    simp only [coeff_reflect, coeff_derivative, revAt_zero, coeff_sub,
      coeff_C_mul, coeff_X_mul_zero, sub_zero]
    by_cases hn : n = 0
    · subst n
      have hcoeff : f.coeff 1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hcoeff]
    · have hnsub : n - 1 + 1 = n := by omega
      have hncast : ((n - 1 : ℕ) : R) + 1 = (n : R) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun x : ℕ => (x : R)) hnsub
      rw [hnsub, hncast]
      exact mul_comm _ _
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simp only [coeff_reflect, coeff_derivative, coeff_sub, coeff_C_mul,
      coeff_X_mul]
    rcases lt_trichotomy (l + 1) n with hlt | heq | hgt
    · rw [revAt_le (by omega : l + 1 ≤ n - 1), revAt_le hlt.le]
      have hindex : n - 1 - (l + 1) + 1 = n - (l + 1) := by omega
      have hcast : ((n - 1 - (l + 1) : ℕ) : R) + 1 =
          ((n - (l + 1) : ℕ) : R) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun x : ℕ => (x : R)) hindex
      rw [hindex, hcast]
      rw [Nat.cast_sub hlt.le]
      push_cast
      ring
    · rw [← heq, revAt_le le_rfl,
        revAt_eq_self_of_lt (by omega : l + 1 - 1 < l + 1)]
      have hcoeff : f.coeff (l + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hcoeff, zero_mul]
      push_cast
      ring
    · rw [revAt_eq_self_of_lt hgt,
        revAt_eq_self_of_lt (by omega : n - 1 < l + 1)]
      have hcoeff : f.coeff (l + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      have hcoeff' : f.coeff (l + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hcoeff, hcoeff']
      simp

section Field

variable {F : Type*} [Field F]

theorem natDegree_reflect_eq (f : F[X]) (n : ℕ)
    (hf : f.natDegree ≤ n) (hzero : f.coeff 0 ≠ 0) :
    (reflect n f).natDegree = n := by
  apply le_antisymm
  · exact natDegree_reflect_le.trans (max_le le_rfl hf)
  · apply le_natDegree_of_ne_zero
    simpa [coeff_reflect, revAt_le le_rfl] using hzero

private theorem resultant_reflect_derivative_balance_of_splits
    (f : F[X]) (n : ℕ) (hf : f.natDegree ≤ n)
    (hzero : f.coeff 0 ≠ 0) (hs : (reflect n f).Splits) :
    (reflect n f).leadingCoeff *
        resultant (reflect n f) (reflect (n - 1) f.derivative) n (n - 1) =
      (reflect n f).coeff 0 *
        resultant (reflect n f) (reflect n f).derivative n (n - 1) := by
  let h := reflect n f
  let q := reflect (n - 1) f.derivative
  have hhdeg : h.natDegree = n := natDegree_reflect_eq f n hf hzero
  have hqdeg : q.natDegree ≤ n - 1 := by
    apply natDegree_reflect_le.trans
    rw [max_le_iff]
    exact ⟨le_rfl,
      (natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1)⟩
  have hh'deg : h.derivative.natDegree ≤ n - 1 := by
    rw [← hhdeg]
    exact natDegree_derivative_le h
  rw [show resultant h q n (n - 1) = resultant h q h.natDegree (n - 1) by rw [hhdeg],
    resultant_eq_prod_eval h q (n - 1) hqdeg hs]
  rw [show resultant h h.derivative n (n - 1) =
      resultant h h.derivative h.natDegree (n - 1) by rw [hhdeg],
    resultant_eq_prod_eval h h.derivative (n - 1) hh'deg hs]
  have hhne : h ≠ 0 := by
    intro hh
    apply hzero
    have hreflect : reflect n f = 0 := by simpa [h] using hh
    have : f = 0 := (reflect_eq_zero_iff (N := n) (f := f)).mp hreflect
    simp [this]
  have hqeval : ∀ r ∈ h.roots, q.eval r = -r * h.derivative.eval r := by
    intro r hr
    have hroot : h.eval r = 0 := (mem_roots hhne).mp hr
    have hrel : q = C (n : F) * h - X * h.derivative := by
      simpa [h, q] using reflect_derivative_relation f n hf
    rw [hrel]
    simp [eval_mul, hroot]
  have hprod : (h.roots.map q.eval).prod =
      (-1 : F) ^ n * h.roots.prod * (h.roots.map h.derivative.eval).prod := by
    calc
      (h.roots.map q.eval).prod =
          (h.roots.map (fun r => -r * h.derivative.eval r)).prod := by
        congr 1
        exact Multiset.map_congr rfl hqeval
      _ = (h.roots.map (fun r => (-1 : F))).prod *
          h.roots.prod * (h.roots.map h.derivative.eval).prod := by
        have hpoint : (h.roots.map (fun r => -r * h.derivative.eval r)) =
            h.roots.map (fun r => (((-1 : F) * r) * h.derivative.eval r)) := by
          apply Multiset.map_congr rfl
          intro r hr
          ring
        rw [hpoint, Multiset.prod_map_mul, Multiset.prod_map_mul]
        simp
      _ = (-1 : F) ^ n * h.roots.prod *
          (h.roots.map h.derivative.eval).prod := by
        have hconst : (h.roots.map (fun _ => (-1 : F))).prod =
            (-1 : F) ^ h.roots.card := by
          induction h.roots using Multiset.induction_on with
          | empty => simp
          | cons a s _ => simp [pow_succ]
        rw [hconst, ← hs.natDegree_eq_card_roots, hhdeg]
  rw [hprod, hs.coeff_zero_eq_leadingCoeff_mul_prod_roots, hhdeg]
  ring

theorem resultant_reflect_derivative_balance
    (f : F[X]) (n : ℕ) (hf : f.natDegree ≤ n)
    (hzero : f.coeff 0 ≠ 0) :
    (reflect n f).leadingCoeff *
        resultant (reflect n f) (reflect (n - 1) f.derivative) n (n - 1) =
      (reflect n f).coeff 0 *
        resultant (reflect n f) (reflect n f).derivative n (n - 1) := by
  let h := reflect n f
  let E := h.SplittingField
  let φ : F →+* E := algebraMap F E
  have hφ : Function.Injective φ := (algebraMap F E).injective
  apply hφ
  have hsplit : (reflect n (f.map φ)).Splits := by
    rw [reflect_map]
    exact SplittingField.splits h
  have hzeroMap : (f.map φ).coeff 0 ≠ 0 := by
    simpa [coeff_map] using hφ.ne hzero
  have hbalance := resultant_reflect_derivative_balance_of_splits
    (f.map φ) n (by simpa [natDegree_map_eq_of_injective hφ] using hf)
      hzeroMap hsplit
  rw [reflect_map, derivative_map, reflect_map, derivative_map] at hbalance
  simpa only [map_mul, resultant_map_map, coeff_map,
    leadingCoeff_map_of_injective hφ] using hbalance

/-- Reversing a polynomial of positive degree with nonzero constant term
preserves its discriminant. -/
theorem discr_reflect_eq (f : F[X]) (hzero : f.coeff 0 ≠ 0) :
    (reflect f.natDegree f).discr = f.discr := by
  let n := f.natDegree
  by_cases hn : n = 0
  · have hfdeg : f.natDegree = 0 := hn
    obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hfdeg
    simp [reflect]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let h := reflect n f
  have hfne : f ≠ 0 := by
    intro hf
    apply hzero
    simp [hf]
  have hhdeg : h.natDegree = n := natDegree_reflect_eq f n le_rfl hzero
  have hhne : h ≠ 0 := by
    intro hh
    apply hfne
    apply (reflect_eq_zero_iff (N := n) (f := f)).mp
    simpa [h] using hh
  have hfDegreePos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    exact hnpos
  have hhDegreePos : 0 < h.degree := by
    rw [← natDegree_pos_iff_degree_pos, hhdeg]
    exact hnpos
  have hbalance := resultant_reflect_derivative_balance f n le_rfl hzero
  have hreflect := resultant_reflect f f.derivative n (n - 1)
  have heven : (-1 : F) ^ (n * (n - 1)) = 1 :=
    n.even_mul_pred_self.neg_one_pow
  rw [heven, one_mul] at hreflect
  rw [hreflect] at hbalance
  have hfResultant := resultant_deriv (f := f) hfDegreePos
  have hhResultant := resultant_deriv (f := h) hhDegreePos
  rw [show f.natDegree = n from rfl] at hfResultant
  rw [hhdeg] at hhResultant
  rw [hfResultant, hhResultant] at hbalance
  have hhLeading : h.leadingCoeff = f.coeff 0 := by
    rw [leadingCoeff, hhdeg, coeff_reflect, revAt_le le_rfl]
    simp
  have hhCoeffZero : h.coeff 0 = f.leadingCoeff := by
    change (reflect n f).coeff 0 = f.leadingCoeff
    rw [coeff_reflect, revAt_zero]
    change f.coeff f.natDegree = f.coeff f.natDegree
    rfl
  rw [hhLeading, hhCoeffZero] at hbalance
  let s : F := (-1) ^ (n * (n - 1) / 2)
  have hs : s ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfne
  have hfactor : f.coeff 0 * f.leadingCoeff * s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hzero hlc) hs
  apply mul_left_cancel₀ hfactor
  change (f.coeff 0 * f.leadingCoeff * s) * h.discr =
    (f.coeff 0 * f.leadingCoeff * s) * f.discr
  change f.coeff 0 * (s * f.leadingCoeff * f.discr) =
    f.leadingCoeff * (s * f.coeff 0 * h.discr) at hbalance
  calc
    (f.coeff 0 * f.leadingCoeff * s) * h.discr =
        f.leadingCoeff * (s * f.coeff 0 * h.discr) := by ring
    _ = f.coeff 0 * (s * f.leadingCoeff * f.discr) := hbalance.symm
    _ = (f.coeff 0 * f.leadingCoeff * s) * f.discr := by ring

/-- Translation of the variable preserves the discriminant. -/
theorem discr_taylor_eq (f : F[X]) (c : F) :
    (f.taylor c).discr = f.discr := by
  by_cases hn : f.natDegree = 0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hn
    simp
  let n := f.natDegree
  let d := f.derivative.natDegree
  let k := n - 1 - d
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hdle : d ≤ n - 1 := natDegree_derivative_le f
  have hsum : d + k = n - 1 := by omega
  have htder : (f.taylor c).derivative = f.derivative.taylor c := by
    simp [taylor_apply, derivative_comp]
  have htdeg : (f.taylor c).natDegree = n := natDegree_taylor f c
  have htderdeg : (f.taylor c).derivative.natDegree = d := by
    rw [htder, natDegree_taylor]
  have hordinary :
      resultant (f.taylor c) (f.taylor c).derivative n d =
        resultant f f.derivative n d := by
    have ht := resultant_taylor f f.derivative c
    rw [← htder] at ht
    simpa [n, d, natDegree_taylor, htderdeg] using ht
  have hfixedF := resultant_add_right_deg f f.derivative n d k le_rfl
  have hfixedT := resultant_add_right_deg
    (f.taylor c) (f.taylor c).derivative n d k htderdeg.le
  rw [hsum] at hfixedF hfixedT
  have hfixed :
      resultant (f.taylor c) (f.taylor c).derivative n (n - 1) =
        resultant f f.derivative n (n - 1) := by
    rw [hfixedT, hfixedF, hordinary]
    rw [coeff_natDegree, ← htdeg, coeff_natDegree, leadingCoeff_taylor]
  have hfDegreePos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    exact hnpos
  have htDegreePos : 0 < (f.taylor c).degree := by
    rw [← natDegree_pos_iff_degree_pos, htdeg]
    exact hnpos
  have hfResultant := resultant_deriv (f := f) hfDegreePos
  have htResultant := resultant_deriv (f := f.taylor c) htDegreePos
  rw [show f.natDegree = n from rfl] at hfResultant
  rw [htdeg] at htResultant
  rw [htResultant, hfResultant] at hfixed
  have hfne : f ≠ 0 := by
    intro hf
    subst f
    simp at hn
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfne
  have hs : ((-1 : F) ^ (n * (n - 1) / 2)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hfactor : ((-1 : F) ^ (n * (n - 1) / 2)) * f.leadingCoeff ≠ 0 :=
    mul_ne_zero hs hlc
  rw [leadingCoeff_taylor] at hfixed
  exact mul_left_cancel₀ hfactor hfixed

/-- Scaling every coefficient by `b` scales the discriminant by
`b^(2 * degree - 2)`. -/
theorem discr_C_mul (f : F[X]) (b : F) (hb : b ≠ 0) :
    (C b * f).discr = b ^ (2 * f.natDegree - 2) * f.discr := by
  by_cases hn : f.natDegree = 0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hn
    rw [show b ^ (2 * (C a).natDegree - 2) * (C a).discr = 1 by simp]
    simpa only [C_mul] using (discr_C (b * a) : (C (b * a) : F[X]).discr = 1)
  let n := f.natDegree
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hfne : f ≠ 0 := by
    intro hf
    subst f
    simp at hn
  have hgdeg : (C b * f).natDegree = n := by
    rw [natDegree_C_mul hb]
  have hgder : (C b * f).derivative = C b * f.derivative := by simp
  have hres :
      resultant (C b * f) (C b * f.derivative) n (n - 1) =
        b ^ (n - 1) * b ^ n * resultant f f.derivative n (n - 1) := by
    rw [resultant_C_mul_left, resultant_C_mul_right]
    ring
  have hpow : b ^ (n - 1) * b ^ n =
      b * b ^ (2 * n - 2) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  rw [hpow] at hres
  have hfDegreePos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    exact hnpos
  have hgDegreePos : 0 < (C b * f).degree := by
    rw [← natDegree_pos_iff_degree_pos, hgdeg]
    exact hnpos
  have hfResultant := resultant_deriv (f := f) hfDegreePos
  have hgResultant := resultant_deriv (f := C b * f) hgDegreePos
  rw [show f.natDegree = n from rfl] at hfResultant
  rw [hgdeg, hgder] at hgResultant
  rw [hgResultant, hfResultant] at hres
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfne
  have hleading : (C b * f).leadingCoeff = b * f.leadingCoeff := by
    rw [leadingCoeff_mul' (mul_ne_zero (by simpa) hlc)]
    simp
  rw [hleading] at hres
  let s : F := (-1) ^ (n * (n - 1) / 2)
  have hs : s ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hfactor : s * b * f.leadingCoeff ≠ 0 :=
    mul_ne_zero (mul_ne_zero hs hb) hlc
  apply mul_left_cancel₀ hfactor
  change s * (b * f.leadingCoeff) * (C b * f).discr =
    b * b ^ (2 * n - 2) * (s * f.leadingCoeff * f.discr) at hres
  rw [show f.natDegree = n from rfl]
  calc
    (s * b * f.leadingCoeff) * (C b * f).discr =
        s * (b * f.leadingCoeff) * (C b * f).discr := by ring
    _ = b * b ^ (2 * n - 2) * (s * f.leadingCoeff * f.discr) := hres
    _ = (s * b * f.leadingCoeff) *
        (b ^ (2 * n - 2) * f.discr) := by ring

end Field

/-- The reciprocal translate `Z^deg(f) * f(c + Z⁻¹)`, represented without
Laurent polynomials as the reflection of the Taylor translate. -/
def reciprocalTranslate (f : R[X]) (c : R) : R[X] :=
  reflect f.natDegree (f.taylor c)

theorem reciprocalTranslate_natDegree_eq (f : R[X]) (c : R)
    (heval : f.eval c ≠ 0) :
    (reciprocalTranslate f c).natDegree = f.natDegree := by
  apply le_antisymm
  · exact natDegree_reflect_le.trans (by simp [natDegree_taylor])
  · apply le_natDegree_of_ne_zero
    simpa [reciprocalTranslate, coeff_reflect, revAt_le le_rfl,
      taylor_coeff_zero] using heval

theorem reciprocalTranslate_leadingCoeff (f : R[X]) (c : R)
    (heval : f.eval c ≠ 0) :
    (reciprocalTranslate f c).leadingCoeff = f.eval c := by
  rw [leadingCoeff, reciprocalTranslate_natDegree_eq f c heval]
  simp [reciprocalTranslate, coeff_reflect, revAt_le le_rfl,
    taylor_coeff_zero]

section DiscriminantMap

variable {S : Type*} [CommRing S] [IsDomain S]

/-- Discriminants commute with an injective coefficient map. -/
theorem discr_map_of_injective (φ : R →+* S) (hφ : Function.Injective φ)
    (f : R[X]) :
    (f.map φ).discr = φ f.discr := by
  by_cases hn : f.natDegree = 0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hn
    simp
  let n := f.natDegree
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hfDegreePos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    exact hnpos
  have hmapdeg : (f.map φ).natDegree = n :=
    natDegree_map_eq_of_injective hφ f
  have hmapDegreePos : 0 < (f.map φ).degree := by
    rw [← natDegree_pos_iff_degree_pos, hmapdeg]
    exact hnpos
  have hres := resultant_map_map f f.derivative n (n - 1) φ
  have hfResultant := resultant_deriv (f := f) hfDegreePos
  have hmapResultant := resultant_deriv (f := f.map φ) hmapDegreePos
  rw [show f.natDegree = n from rfl] at hfResultant
  rw [hmapdeg, derivative_map] at hmapResultant
  rw [hmapResultant, hfResultant, map_mul, map_mul, map_pow,
    map_neg, map_one, leadingCoeff_map_of_injective hφ] at hres
  have hfne : f ≠ 0 := by
    intro hf
    subst f
    simp at hn
  have hlc : φ f.leadingCoeff ≠ 0 :=
    by simpa using hφ.ne (leadingCoeff_ne_zero.mpr hfne)
  have hs : ((-1 : S) ^ (n * (n - 1) / 2)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  exact mul_left_cancel₀ (mul_ne_zero hs hlc) hres

end DiscriminantMap

section ReciprocalField

variable {F : Type*} [Field F]

theorem reciprocalTranslate_discr (f : F[X]) (c : F)
    (heval : f.eval c ≠ 0) :
    (reciprocalTranslate f c).discr = f.discr := by
  calc
    (reciprocalTranslate f c).discr = (f.taylor c).discr := by
      simpa [reciprocalTranslate, natDegree_taylor] using
        discr_reflect_eq (f.taylor c) (by simpa using heval)
    _ = f.discr := discr_taylor_eq f c

end ReciprocalField

section ReciprocalRoot

variable {A L : Type*} [CommRing A] [Field L] [Algebra A L]

theorem aeval_reciprocalTranslate_inv_sub_eq_zero
    (f : A[X]) (c : A) (v : L)
    (hvc : v ≠ algebraMap A L c) (hv : aeval v f = 0) :
    aeval ((v - algebraMap A L c)⁻¹) (reciprocalTranslate f c) = 0 := by
  let x : L := v - algebraMap A L c
  have hx : x ≠ 0 := sub_ne_zero.mpr hvc
  let : Invertible x := invertibleOfNonzero hx
  have htaylor : eval₂ (algebraMap A L) x (f.taylor c) = 0 := by
    rw [taylor_apply, eval₂_comp]
    simpa [x, aeval_def] using hv
  have hreflect := (eval₂_reflect_eq_zero_iff
    (algebraMap A L) x f.natDegree (f.taylor c)
      (by simp [natDegree_taylor])).2 htaylor
  simpa [reciprocalTranslate, aeval_def, x, invOf_eq_inv] using hreflect

end ReciprocalRoot

section ReciprocalPrimitiveElement

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- Replacing a primitive element `v` by `(v - c)⁻¹` preserves primitive
generation.  This is the field-theoretic half of the reciprocal local
normalization used below. -/
theorem adjoin_inv_sub_eq_top_of_adjoin_eq_top
    (c : K) (v : L) (hv : Algebra.adjoin K {v} = ⊤) :
    Algebra.adjoin K {(v - algebraMap K L c)⁻¹} = ⊤ := by
  apply (IntermediateField.adjoin_eq_top_iff).mp
  have hv' : IntermediateField.adjoin K {v} =
      (⊤ : IntermediateField K L) :=
    (IntermediateField.adjoin_eq_top_iff).mpr hv
  apply top_unique
  rw [← hv']
  apply IntermediateField.adjoin_simple_le_iff.mpr
  let z : L := (v - algebraMap K L c)⁻¹
  change v ∈ IntermediateField.adjoin K {z}
  have hz : z ∈ IntermediateField.adjoin K {z} :=
    IntermediateField.mem_adjoin_simple_self K z
  rw [show v = z⁻¹ + algebraMap K L c by simp [z]]
  exact add_mem (inv_mem hz) (IntermediateField.algebraMap_mem _ c)

end ReciprocalPrimitiveElement

section UnitNormalization

variable {A L : Type*} [CommRing A] [Nontrivial A] [Field L] [Algebra A L]

/-- Divide a reciprocal translate by its unit leading coefficient. -/
def unitNormalizedReciprocalTranslate
    (f : A[X]) (c : A) (u : Aˣ) : A[X] :=
  C (↑(u⁻¹) : A) * reciprocalTranslate f c

omit [Nontrivial A] in
theorem unitNormalizedReciprocalTranslate_map
    {S : Type*} [CommRing S] (φ : A →+* S) (hφ : Function.Injective φ)
    (f : A[X]) (c : A) (u : Aˣ) :
    (unitNormalizedReciprocalTranslate f c u).map φ =
      unitNormalizedReciprocalTranslate (f.map φ) (φ c) (Units.map φ u) := by
  rw [unitNormalizedReciprocalTranslate, unitNormalizedReciprocalTranslate,
    Polynomial.map_mul, Polynomial.map_C]
  simp only [Units.coe_map_inv]
  congr 1
  rw [reciprocalTranslate, reciprocalTranslate, ← reflect_map,
    map_taylor, natDegree_map_eq_of_injective hφ]

theorem unitNormalizedReciprocalTranslate_monic
    (f : A[X]) (c : A) (u : Aˣ) (hu : f.eval c = u) :
    (unitNormalizedReciprocalTranslate f c u).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  have heval : f.eval c ≠ 0 := by
    rw [hu]
    exact Units.ne_zero u
  rw [reciprocalTranslate_leadingCoeff f c heval]
  rw [hu]
  simp

omit [Nontrivial A] in
theorem aeval_unitNormalizedReciprocalTranslate_inv_sub_eq_zero
    (f : A[X]) (c : A) (u : Aˣ) (v : L)
    (hvc : v ≠ algebraMap A L c) (hv : aeval v f = 0) :
    aeval ((v - algebraMap A L c)⁻¹)
      (unitNormalizedReciprocalTranslate f c u) = 0 := by
  simp [unitNormalizedReciprocalTranslate,
    aeval_reciprocalTranslate_inv_sub_eq_zero f c v hvc hv]

/-- If `f(c)` is a unit, the reciprocal local parameter `(v-c)⁻¹` is
integral over the coefficient ring. -/
theorem isIntegral_inv_sub_of_eval_eq_unit
    (f : A[X]) (c : A) (u : Aˣ) (v : L)
    (hu : f.eval c = u)
    (hvc : v ≠ algebraMap A L c) (hv : aeval v f = 0) :
    IsIntegral A ((v - algebraMap A L c)⁻¹) := by
  refine ⟨unitNormalizedReciprocalTranslate f c u,
    unitNormalizedReciprocalTranslate_monic f c u hu, ?_⟩
  exact aeval_unitNormalizedReciprocalTranslate_inv_sub_eq_zero
    f c u v hvc hv

end UnitNormalization

section UnitNormalizationField

variable {F : Type*} [Field F]

theorem unitNormalizedReciprocalTranslate_discr
    (f : F[X]) (c : F) (u : Fˣ) (hu : f.eval c = u) :
    (unitNormalizedReciprocalTranslate f c u).discr =
      (↑(u⁻¹) : F) ^ (2 * f.natDegree - 2) * f.discr := by
  have heval : f.eval c ≠ 0 := by
    rw [hu]
    exact Units.ne_zero u
  rw [unitNormalizedReciprocalTranslate,
    discr_C_mul _ _ (Units.ne_zero (u⁻¹)),
    reciprocalTranslate_natDegree_eq f c heval,
    reciprocalTranslate_discr f c heval]

end UnitNormalizationField

section UnitNormalizationBaseChange

variable {A K : Type*} [CommRing A] [Nontrivial A]
  [Field K] [Algebra A K]

omit [Nontrivial A] in
/-- After embedding the coefficient ring in a field, normalization changes
the discriminant only by the displayed unit power. -/
theorem map_unitNormalizedReciprocalTranslate_discr
    (hAK : Function.Injective (algebraMap A K))
    (f : A[X]) (c : A) (u : Aˣ) (hu : f.eval c = u) :
    algebraMap A K (unitNormalizedReciprocalTranslate f c u).discr =
      algebraMap A K (↑(u⁻¹) : A) ^ (2 * f.natDegree - 2) *
        algebraMap A K f.discr := by
  let φ : A →+* K := algebraMap A K
  let uK : Kˣ := Units.map φ u
  have huK : (f.map φ).eval (φ c) = uK := by
    simpa [φ, uK, hu] using eval_map_apply (p := f) φ c
  rw [← discr_map_of_injective φ hAK
    (unitNormalizedReciprocalTranslate f c u)]
  rw [unitNormalizedReciprocalTranslate_map φ hAK]
  rw [unitNormalizedReciprocalTranslate_discr (f.map φ) (φ c) uK huK]
  rw [natDegree_map_eq_of_injective hAK]
  rw [discr_map_of_injective φ hAK f]
  simp [φ, uK]

end UnitNormalizationBaseChange

section ReciprocalMinpoly

variable {A K L : Type*}
  [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsFractionRing A K]
  [FiniteDimensional K L]

/-- If the original equation has the full extension degree, then its monic
reciprocal normalization is exactly the minimal polynomial of `(v-c)⁻¹` over
the fraction field. -/
theorem minpoly_inv_sub_eq_map_unitNormalizedReciprocalTranslate
    (f : A[X]) (c : A) (u : Aˣ) (v : L)
    (hu : f.eval c = u)
    (hvc : v ≠ algebraMap A L c) (hv : aeval v f = 0)
    (hprimitive : Algebra.adjoin K {v} = ⊤)
    (hdegree : f.natDegree = Module.finrank K L) :
    minpoly K ((v - algebraMap A L c)⁻¹) =
      (unitNormalizedReciprocalTranslate f c u).map (algebraMap A K) := by
  let z : L := (v - algebraMap A L c)⁻¹
  let q : A[X] := unitNormalizedReciprocalTranslate f c u
  have hq_monic_A : q.Monic :=
    unitNormalizedReciprocalTranslate_monic f c u hu
  have hq_monic_K : (q.map (algebraMap A K)).Monic :=
    hq_monic_A.map (algebraMap A K)
  have hq_root_A : aeval z q = 0 := by
    exact aeval_unitNormalizedReciprocalTranslate_inv_sub_eq_zero
      f c u v hvc hv
  have hq_root_K : aeval z (q.map (algebraMap A K)) = 0 := by
    rw [aeval_map_algebraMap]
    exact hq_root_A
  have hdvd : minpoly K z ∣ q.map (algebraMap A K) :=
    minpoly.dvd K z hq_root_K
  have hz_primitive_algebra : Algebra.adjoin K {z} = ⊤ := by
    simpa [z, IsScalarTower.algebraMap_apply A K L] using
      (adjoin_inv_sub_eq_top_of_adjoin_eq_top
        (algebraMap A K c) v hprimitive)
  have hz_primitive :
      IntermediateField.adjoin K {z} = (⊤ : IntermediateField K L) :=
    (IntermediateField.adjoin_eq_top_iff).mpr hz_primitive_algebra
  have hmin_degree : (minpoly K z).natDegree = Module.finrank K L :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K z).mp hz_primitive
  have heval : f.eval c ≠ 0 := by
    rw [hu]
    exact Units.ne_zero u
  have hq_degree :
      (q.map (algebraMap A K)).natDegree = (minpoly K z).natDegree := by
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective A K)]
    change (C ((↑u⁻¹ : A)) * reciprocalTranslate f c).natDegree = _
    rw [natDegree_C_mul (Units.ne_zero (u⁻¹)),
      reciprocalTranslate_natDegree_eq f c heval, hdegree, hmin_degree]
  have hq_eq : q.map (algebraMap A K) = minpoly K z :=
    eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral z)) hq_monic_K hdvd
      hq_degree.le
  exact hq_eq.symm

end ReciprocalMinpoly

section ReciprocalPrimitiveDifferent

variable {A K L B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra A B] [Algebra B L]
  [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegralClosure B A L] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]

/-- A reciprocal translate whose value at the center is a unit gives an
integral primitive element, and its minimal-polynomial derivative bounds the
different at every finite prime. -/
theorem exists_reciprocal_integral_primitive_and_different_bound
    (f : A[X]) (c : A) (u : Aˣ) (v : L)
    (hu : f.eval c = u)
    (hvc : v ≠ algebraMap A L c) (hv : aeval v f = 0)
    (hprimitive : Algebra.adjoin K {v} = ⊤)
    (w : HeightOneSpectrum B) :
    ∃ z : B,
      algebraMap B L z = (v - algebraMap A L c)⁻¹ ∧
      Algebra.adjoin K {algebraMap B L z} = ⊤ ∧
      multiplicity w.asIdeal (differentIdeal A B) ≤
        multiplicity w.asIdeal
          (Ideal.span {aeval z (derivative (minpoly A z))}) := by
  have hz_integral : IsIntegral A ((v - algebraMap A L c)⁻¹) :=
    isIntegral_inv_sub_of_eval_eq_unit f c u v hu hvc hv
  let z : B :=
    IsIntegralClosure.mk' B ((v - algebraMap A L c)⁻¹) hz_integral
  have hz_map : algebraMap B L z = (v - algebraMap A L c)⁻¹ := by
    simp [z]
  have hz_primitive : Algebra.adjoin K {algebraMap B L z} = ⊤ := by
    rw [hz_map]
    simpa only [IsScalarTower.algebraMap_apply A K L] using
      (adjoin_inv_sub_eq_top_of_adjoin_eq_top
        (algebraMap A K c) v hprimitive)
  refine ⟨z, hz_map, hz_primitive, ?_⟩
  exact differentIdeal_multiplicity_le_minpolyDerivativeSpan z hz_primitive w

end ReciprocalPrimitiveDifferent

section UnitNormalizationFinitePlace

variable {A K : Type*} [CommRing A] [IsDedekindDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]

/-- A base-ring unit has order zero at every finite place. -/
@[simp]
theorem finitePlaceOrderTop_algebraMap_unit
    (v : HeightOneSpectrum A) (u : Aˣ) :
    finitePlaceOrderTop v (algebraMap A K (u : A)) = 0 := by
  have hu_nonnegative :
      (0 : WithTop ℤ) ≤ finitePlaceOrderTop v (algebraMap A K (u : A)) :=
    finitePlaceOrderTop_algebraMap_nonnegative v (u : A)
  have hu_inv_nonnegative :
      (0 : WithTop ℤ) ≤ finitePlaceOrderTop v (algebraMap A K ((↑u⁻¹ : A))) :=
    finitePlaceOrderTop_algebraMap_nonnegative v (↑u⁻¹ : A)
  have hsum :
      finitePlaceOrderTop v (algebraMap A K (u : A)) +
          finitePlaceOrderTop v (algebraMap A K ((↑u⁻¹ : A))) = 0 := by
    rw [← finitePlaceOrderTop_mul]
    simp
  apply le_antisymm
  · calc
      finitePlaceOrderTop v (algebraMap A K (u : A)) ≤
          finitePlaceOrderTop v (algebraMap A K (u : A)) +
            finitePlaceOrderTop v (algebraMap A K ((↑u⁻¹ : A))) :=
        le_add_of_nonneg_right hu_inv_nonnegative
      _ = 0 := hsum
  · exact hu_nonnegative

/-- Unit-normalizing a reciprocal translate preserves the discriminant order
at every finite place of the coefficient ring. -/
theorem finitePlaceOrderTop_map_unitNormalizedReciprocalTranslate_discr
    (v : HeightOneSpectrum A)
    (f : A[X]) (c : A) (u : Aˣ) (hu : f.eval c = u) :
    finitePlaceOrderTop v
        (algebraMap A K (unitNormalizedReciprocalTranslate f c u).discr) =
      finitePlaceOrderTop v (algebraMap A K f.discr) := by
  rw [map_unitNormalizedReciprocalTranslate_discr
    (IsFractionRing.injective A K) f c u hu]
  rw [finitePlaceOrderTop_mul, finitePlaceOrderTop_pow,
    finitePlaceOrderTop_algebraMap_unit]
  simp

/-- Under the full-degree primitive-element hypothesis, the discriminant of
the reciprocal element's minimal polynomial has exactly the order of the
original equation's discriminant at every finite base place. -/
theorem finitePlaceOrderTop_minpoly_inv_sub_discr
    {L : Type*} [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    (v₀ : HeightOneSpectrum A)
    (f : A[X]) (c : A) (u : Aˣ) (v : L)
    (hu : f.eval c = u)
    (hvc : v ≠ algebraMap A L c) (hv : aeval v f = 0)
    (hprimitive : Algebra.adjoin K {v} = ⊤)
    (hdegree : f.natDegree = Module.finrank K L) :
    finitePlaceOrderTop v₀
        (minpoly K ((v - algebraMap A L c)⁻¹)).discr =
      finitePlaceOrderTop v₀ (algebraMap A K f.discr) := by
  rw [minpoly_inv_sub_eq_map_unitNormalizedReciprocalTranslate
    f c u v hu hvc hv hprimitive hdegree]
  rw [discr_map_of_injective (algebraMap A K)
    (IsFractionRing.injective A K)]
  exact finitePlaceOrderTop_map_unitNormalizedReciprocalTranslate_discr
    v₀ f c u hu

end UnitNormalizationFinitePlace


end

end BGS.CorvajaZannier
