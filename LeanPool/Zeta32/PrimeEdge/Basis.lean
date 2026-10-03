/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Index
public import LeanPool.Zeta32.PrimeEdge.Auxiliary.ClassBasis

/-! the proof notes, §6 "Basis": the CRT product basis for `n = p - 1`,
`φ_{b,i} = (t + b)^i ∏_{b' ≠ b} (t + b')^{m_{b'}}` (`0 ≤ b < p`, `i < m_b`), `h = 3(p-1)` vectors,
each of degree `< h`. On the disc `t = -b + p u` it is `(p u)^i · (p-unit)`, and on every other disc
`b'` it carries the factor `(t + b')^{m_{b'}}`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

/-- The CRT product basis vector `φ_a`. -/
noncomputable def crtBasis (p : ℕ) (a : Idx p) : ℚ[X] :=
  (X + C (a.1.val : ℚ)) ^ a.2.val *
    ∏ b ∈ (Finset.range p).erase a.1.val, (X + C (b : ℚ)) ^ mult p b

/-- The entry numerator `φ_a φ_c D_n^4`, `n = p - 1`. -/
noncomputable def Aent (p : ℕ) (a c : Idx p) : ℚ[X] :=
  crtBasis p a * crtBasis p c * Zeta32.D (p - 1) ^ 4

/-- An enumeration of the basis indices by `Fin h`. -/
noncomputable def idxEquiv (hp : 5 ≤ p) : Fin (3 * (p - 1)) ≃ Idx p :=
  (Fintype.equivFinOfCardEq (card_Idx hp)).symm

/-- Determinant of the change of basis from monomials to the CRT basis. -/
noncomputable def basisDet (p : ℕ) (hp : 5 ≤ p) : ℚ :=
  (coeffMat fun i => crtBasis p (idxEquiv hp i)).det

/-- **S1-deg.** `deg φ_a = i + (h - m_b) < h`. -/
theorem crtBasis_natDegree_lt (hp : 5 ≤ p) (a : Idx p) :
    (crtBasis p a).natDegree < 3 * (p - 1) := by
  have hmon : ∀ b ∈ (Finset.range p).erase a.1.val, ((X + C (b : ℚ)) ^ mult p b).Monic :=
    fun b _ => (monic_X_add_C _).pow _
  have hdeg : (crtBasis p a).natDegree =
      a.2.val + ∑ b ∈ (Finset.range p).erase a.1.val, mult p b := by
    unfold crtBasis
    rw [Monic.natDegree_mul ((monic_X_add_C _).pow _) (monic_prod_of_monic _ _ hmon),
      natDegree_pow, natDegree_X_add_C, natDegree_prod_of_monic _ _ hmon]
    rw [mul_one]
    congr 1
    exact Finset.sum_congr rfl fun b _ => by rw [natDegree_pow, natDegree_X_add_C, mul_one]
  have hsplit := Finset.add_sum_erase (Finset.range p) (mult p) (Finset.mem_range.mpr a.1.isLt)
  have hsum := sum_mult hp
  have hi := a.2.isLt
  omega

/-- **S1-unit.** The change of basis is unimodular over `ℤ_(p)`: the CRT basis is independent
modulo `p` (centres `-b` distinct mod `p`), so its coefficient determinant is a `p`-adic unit. -/
theorem basisDet_unit [Fact p.Prime] (hp : 5 ≤ p) :
    basisDet p hp ≠ 0 ∧ padicValRat p (basisDet p hp) = 0 := by
  classical
  set e := idxEquiv hp
  -- the integral model of the basis
  let Ez : Fin (3 * (p - 1)) → ℤ[X] := fun i =>
    (X + C (((e i).1.val : ℕ) : ℤ)) ^ (e i).2.val *
      ∏ b ∈ (Finset.range p).erase (e i).1.val, (X + C ((b : ℕ) : ℤ)) ^ mult p b
  have hmapQ : ∀ i, (Ez i).map (Int.castRingHom ℚ) = crtBasis p (e i) := by
    intro i
    simp only [Ez, crtBasis, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom,
      Int.cast_natCast]
  have hbd : basisDet p hp = (coeffMat fun i => (Ez i).map (Int.castRingHom ℚ)).det := by
    unfold basisDet
    simp_rw [hmapQ]
    rfl
  rw [hbd]
  refine Auxiliary.coeffMat_det_unit_of_independent Ez (fun i => ?_) (fun v hv => ?_)
  · have h := crtBasis_natDegree_lt hp (e i)
    rwa [← hmapQ, natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int] at h
  · -- independence modulo `p`: centres `-b`, `b < p`, are distinct in `ZMod p`
    have hprod : ∀ (b : Fin p) (f : ℕ → (ZMod p)[X]),
        ∏ k ∈ (Finset.range p).erase b.val, f k = ∏ c ∈ Finset.univ.erase b, f c.val := by
      intro b f
      have himg : (Finset.univ.erase b).image Fin.val = (Finset.range p).erase b.val := by
        ext k
        simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
          Finset.mem_range]
        constructor
        · rintro ⟨c, hc, rfl⟩
          exact ⟨fun h => hc (Fin.ext h), c.isLt⟩
        · rintro ⟨hk, hkp⟩
          exact ⟨⟨k, hkp⟩, fun h => hk (by rw [← h]), rfl⟩
      rw [← himg, Finset.prod_image (fun x _ y _ h => Fin.ext h)]
    have hmapP : ∀ i, (Ez i).map (Int.castRingHom (ZMod p)) =
        (∏ c ∈ Finset.univ.erase (e i).1, (X - C (-((c.val : ℕ) : ZMod p))) ^ mult p c.val) *
          (X - C (-(((e i).1.val : ℕ) : ZMod p))) ^ (e i).2.val := by
      intro i
      simp only [Ez, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod,
        Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom,
        Int.cast_natCast, map_neg, sub_neg_eq_add]
      rw [mul_comm, hprod (e i).1 fun k => (X + C ((k : ℕ) : ZMod p)) ^ mult p k]
    have hγ : Function.Injective fun c : Fin p => -((c.val : ℕ) : ZMod p) := by
      intro c d h
      have h' : ((c.val : ℕ) : ZMod p) = ((d.val : ℕ) : ZMod p) := neg_inj.mp h
      have h'' := congrArg ZMod.val h'
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt c.isLt,
        Nat.mod_eq_of_lt d.isLt] at h''
      exact Fin.ext h''
    refine Auxiliary.classBasis_independent (F := ZMod p)
      (fun c : Fin p => -((c.val : ℕ) : ZMod p)) hγ (fun c => mult p c.val)
      (fun i => (e i).1) (fun i => (e i).2.val) (fun i => (e i).2.isLt) ?_ v ?_
    · intro a b h1 h2
      apply e.injective
      exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).mpr h2)
    · simpa only [hmapP] using hv

lemma D_natDegree_le (m : ℕ) : (Zeta32.D m).natDegree ≤ m := by
  unfold Zeta32.D
  refine (natDegree_prod_le _ _).trans ?_
  have h : ∀ j ∈ Finset.Icc 1 m, (X + C (j : ℚ)).natDegree = 1 := fun j _ => natDegree_X_add_C _
  rw [Finset.sum_congr rfl h]
  simp

lemma Aent_natDegree (hp : 5 ≤ p) (a c : Idx p) :
    (Aent p a c).natDegree + 2 ≤ 10 * (p - 1) := by
  have ha := crtBasis_natDegree_lt hp a
  have hc := crtBasis_natDegree_lt hp c
  have hD := D_natDegree_le (p - 1)
  have h1 := natDegree_mul_le (p := crtBasis p a * crtBasis p c) (q := Zeta32.D (p - 1) ^ 4)
  have h2 := natDegree_mul_le (p := crtBasis p a) (q := crtBasis p c)
  have h3 := natDegree_pow_le (p := Zeta32.D (p - 1)) (n := 4)
  unfold Aent
  omega

end Zeta32.PrimeEdge

end
