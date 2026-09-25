/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Data.Nat.GCD.Prime
public import LeanPool.MarkoffModP.BGS.Markoff.Core.ConicParametrization
public import LeanPool.MarkoffModP.BGS.Markoff.Opening.AlgebraicClosureTransport
public import LeanPool.MarkoffModP.BGS.Markoff.Opening.CyclotomicBound
public import LeanPool.MarkoffModP.BGS.Markoff.Core.TraceClassification

/-!
# From residue traces to the concrete cyclotomic opening bound

This file chooses eigenvalues for arbitrary normalized traces over `ZMod p`, including the two
parabolic traces, and combines their exact orders by an lcm.
-/

@[expose] public section

namespace BGS.Markoff

private theorem prime_coprime_orderOf_splitUnit
    (p : ℕ) [Fact p.Prime] (w : (ZMod p)ˣ) :
    Nat.Coprime p (orderOf w) := by
  apply Nat.Coprime.of_dvd_right (orderOf_dvd_card : orderOf w ∣ Fintype.card (ZMod p)ˣ)
  rw [ZMod.card_units]
  exact (Nat.coprime_self_sub_right (Fact.out : p.Prime).one_le).2 (Nat.coprime_one_right p)

private theorem prime_coprime_orderOf_quadraticNormOne
    (p : ℕ) [Fact p.Prime] (w : quadraticNormOneTorus p) :
    Nat.Coprime p (orderOf w) := by
  apply Nat.Coprime.of_dvd_right
    (orderOf_dvd_card : orderOf w ∣ Fintype.card (quadraticNormOneTorus p))
  rw [Fintype.card_eq_nat_card, quadraticNormOneTorus_natCard]
  rw [add_comm, Nat.coprime_add_self_right]
  exact Nat.coprime_one_right p

private theorem mapped_split_eigenvalue
    (p : ℕ) [Fact p.Prime] (t : ZMod p) (w : (ZMod p)ˣ)
    (htrace : splitTorusTrace w = t) :
    ∃ W : (OpeningResidueClosure p)ˣ,
      algebraMap (ZMod p) (OpeningResidueClosure p) t = splitTorusTrace W ∧
      IsOfFinOrder W ∧ Nat.Coprime p (orderOf W) := by
  let f := algebraMap (ZMod p) (OpeningResidueClosure p)
  let W : (OpeningResidueClosure p)ˣ := Units.map f.toMonoidHom w
  refine ⟨W, ?_, ?_, ?_⟩
  · rw [← htrace]
    change f ((w : ZMod p) + ((w⁻¹ : (ZMod p)ˣ) : ZMod p)) =
      f (w : ZMod p) + f ((w⁻¹ : (ZMod p)ˣ) : ZMod p)
    exact map_add f _ _
  · exact (Units.map f.toMonoidHom).isOfFinOrder (isOfFinOrder_of_finite w)
  · rw [show orderOf W = orderOf w by
      exact orderOf_injective (Units.map f.toMonoidHom)
        (Units.map_injective f.injective) w]
    exact prime_coprime_orderOf_splitUnit p w

private theorem mapped_quadraticNormOne_eigenvalue
    (p : ℕ) [Fact p.Prime] (t : ZMod p) (w : quadraticNormOneTorus p)
    (htrace : quadraticNormOneTrace p w = t) :
    ∃ W : (OpeningResidueClosure p)ˣ,
      algebraMap (ZMod p) (OpeningResidueClosure p) t = splitTorusTrace W ∧
      IsOfFinOrder W ∧ Nat.Coprime p (orderOf W) := by
  let σ : quadraticFiniteField p →ₐ[ZMod p] OpeningResidueClosure p := IsAlgClosed.lift
  let W : (OpeningResidueClosure p)ˣ :=
    Units.map σ.toRingHom.toMonoidHom (w : (quadraticFiniteField p)ˣ)
  refine ⟨W, ?_, ?_, ?_⟩
  · calc
      algebraMap (ZMod p) (OpeningResidueClosure p) t =
          σ (algebraMap (ZMod p) (quadraticFiniteField p) t) := (σ.commutes t).symm
      _ = σ (splitTorusTrace (w : (quadraticFiniteField p)ˣ)) := by
        rw [← algebraMap_quadraticNormOneTrace p w, htrace]
      _ = splitTorusTrace W := by simp [W, splitTorusTrace]
  · exact (Units.map σ.toRingHom.toMonoidHom).isOfFinOrder
      (isOfFinOrder_of_finite (w : (quadraticFiniteField p)ˣ))
  · rw [show orderOf W = orderOf w by
      calc
        orderOf W = orderOf (w : (quadraticFiniteField p)ˣ) :=
          orderOf_injective (Units.map σ.toRingHom.toMonoidHom)
            (Units.map_injective σ.injective) _
        _ = orderOf w := orderOf_injective (quadraticNormOneTorus p).subtype
          Subtype.coe_injective w]
    exact prime_coprime_orderOf_quadraticNormOne p w

/-- Every normalized trace over an odd prime field has a finite-order eigenvalue in the fixed
residue closure.  Parabolic traces are represented explicitly by `1` or `-1`; all other traces
use the split/norm-one classification. -/
theorem exists_residueClosure_eigenvalue_of_trace
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (t : ZMod p) :
    ∃ W : (OpeningResidueClosure p)ˣ,
      algebraMap (ZMod p) (OpeningResidueClosure p) t = splitTorusTrace W ∧
      IsOfFinOrder W ∧ Nat.Coprime p (orderOf W) := by
  by_cases ht : t ^ 2 = 4
  · have hfactor : (t - 2) * (t + 2) = 0 := by
      calc
        (t - 2) * (t + 2) = t ^ 2 - 4 := by ring
        _ = 0 := sub_eq_zero.mpr ht
    rcases mul_eq_zero.mp hfactor with h | h
    · have htTwo : t = 2 := sub_eq_zero.mp h
      exact mapped_split_eigenvalue p t 1 (by
        rw [htTwo]
        change (1 : ZMod p) + 1 = 2
        ring)
    · have htNegTwo : t = -2 := eq_neg_of_add_eq_zero_left h
      exact mapped_split_eigenvalue p t (-1) (by
        rw [htNegTwo]
        change (-1 : ZMod p) + -1 = -2
        ring)
  · rcases exists_split_or_quadraticNormOneTrace p hpTwo t ht with
      ⟨w, htrace, _⟩ | ⟨w, htrace, _⟩
    · exact mapped_split_eigenvalue p t w htrace
    · exact mapped_quadraticNormOne_eigenvalue p t w htrace

/-- Every nonorigin normalized Markoff point over an odd prime field admits three compatible
residue-closure eigenvalues.  Their exact orders control the concrete cyclotomic opening bound. -/
theorem exists_exact_eigenvalue_orders_with_cyclotomic_bound
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (x : NormalizedPoint (ZMod p)) (hx : IsNormalizedMarkoff x)
    (hxne : x ≠ normalizedOrigin) :
    ∃ W₁ W₂ W₃ : (OpeningResidueClosure p)ˣ,
      algebraMap (ZMod p) (OpeningResidueClosure p) x.u1 = splitTorusTrace W₁ ∧
      algebraMap (ZMod p) (OpeningResidueClosure p) x.u2 = splitTorusTrace W₂ ∧
      algebraMap (ZMod p) (OpeningResidueClosure p) x.u3 = splitTorusTrace W₃ ∧
      IsOfFinOrder W₁ ∧ IsOfFinOrder W₂ ∧ IsOfFinOrder W₃ ∧
      Nat.Coprime p (orderOf W₁) ∧ Nat.Coprime p (orderOf W₂) ∧
      Nat.Coprime p (orderOf W₃) ∧
      p ≤ 20 ^ (max (orderOf W₁) (max (orderOf W₂) (orderOf W₃))) ^ 3 := by
  obtain ⟨W₁, htrace₁, hfin₁, hcoprime₁⟩ :=
    exists_residueClosure_eigenvalue_of_trace p hpTwo x.u1
  obtain ⟨W₂, htrace₂, hfin₂, hcoprime₂⟩ :=
    exists_residueClosure_eigenvalue_of_trace p hpTwo x.u2
  obtain ⟨W₃, htrace₃, hfin₃, hcoprime₃⟩ :=
    exists_residueClosure_eigenvalue_of_trace p hpTwo x.u3
  let l₁ := orderOf W₁
  let l₂ := orderOf W₂
  let l₃ := orderOf W₃
  let n := Nat.lcm l₁ (Nat.lcm l₂ l₃)
  let m := max l₁ (max l₂ l₃)
  have hl₁ : 0 < l₁ := hfin₁.orderOf_pos
  have hl₂ : 0 < l₂ := hfin₂.orderOf_pos
  have hl₃ : 0 < l₃ := hfin₃.orderOf_pos
  have hn : 0 < n := Nat.lcm_pos hl₁ (Nat.lcm_pos hl₂ hl₃)
  let : NeZero n := ⟨hn.ne'⟩
  have hcoprimeN : Nat.Coprime p n := by
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.2
    exact (Fact.out : p.Prime).not_dvd_lcm
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime₁)
      ((Fact.out : p.Prime).not_dvd_lcm
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime₂)
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime₃))
  have hW₁pow : (W₁ : OpeningResidueClosure p) ^ n = 1 := by
    simpa using congrArg Units.val
      (orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_left l₁ (Nat.lcm l₂ l₃)))
  have hW₂pow : (W₂ : OpeningResidueClosure p) ^ n = 1 := by
    have hdvd : l₂ ∣ n :=
      (Nat.dvd_lcm_left l₂ l₃).trans (Nat.dvd_lcm_right l₁ (Nat.lcm l₂ l₃))
    simpa using congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  have hW₃pow : (W₃ : OpeningResidueClosure p) ^ n = 1 := by
    have hdvd : l₃ ∣ n :=
      (Nat.dvd_lcm_right l₂ l₃).trans (Nat.dvd_lcm_right l₁ (Nat.lcm l₂ l₃))
    simpa using congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  obtain ⟨ω, a₁, a₂, a₃, hω, ha₁lt, ha₂lt, ha₃lt, ha₁, ha₂, ha₃⟩ :=
    exists_residue_common_primitiveRoot_powers p n hcoprimeN
      (W₁ : OpeningResidueClosure p) (W₂ : OpeningResidueClosure p)
      (W₃ : OpeningResidueClosure p) hW₁pow hW₂pow hW₃pow
  let f := algebraMap (ZMod p) (OpeningResidueClosure p)
  let xResidue : NormalizedPoint (OpeningResidueClosure p) := x.map f
  have hxResidue : IsNormalizedMarkoff xResidue := by
    change normalizedPolynomial (x.map f) = 0
    rw [normalizedPolynomial_map, hx, map_zero]
  have hxResidueNe : xResidue ≠ normalizedOrigin := by
    intro hzero
    apply hxne
    apply NormalizedPoint.ext
    · apply f.injective
      simpa [xResidue, f, NormalizedPoint.map, normalizedOrigin] using
        congrArg NormalizedPoint.u1 hzero
    · apply f.injective
      simpa [xResidue, f, NormalizedPoint.map, normalizedOrigin] using
        congrArg NormalizedPoint.u2 hzero
    · apply f.injective
      simpa [xResidue, f, NormalizedPoint.map, normalizedOrigin] using
        congrArg NormalizedPoint.u3 hzero
  have hcoord₁ : xResidue.u1 = cyclotomicTrace (ω ^ a₁) := by
    calc
      xResidue.u1 = f x.u1 := rfl
      _ = splitTorusTrace W₁ := htrace₁
      _ = cyclotomicTrace (W₁ : OpeningResidueClosure p) := by
        simp [splitTorusTrace, cyclotomicTrace]
      _ = cyclotomicTrace (ω ^ a₁) := by rw [ha₁]
  have hcoord₂ : xResidue.u2 = cyclotomicTrace (ω ^ a₂) := by
    calc
      xResidue.u2 = f x.u2 := rfl
      _ = splitTorusTrace W₂ := htrace₂
      _ = cyclotomicTrace (W₂ : OpeningResidueClosure p) := by
        simp [splitTorusTrace, cyclotomicTrace]
      _ = cyclotomicTrace (ω ^ a₂) := by rw [ha₂]
  have hcoord₃ : xResidue.u3 = cyclotomicTrace (ω ^ a₃) := by
    calc
      xResidue.u3 = f x.u3 := rfl
      _ = splitTorusTrace W₃ := htrace₃
      _ = cyclotomicTrace (W₃ : OpeningResidueClosure p) := by
        simp [splitTorusTrace, cyclotomicTrace]
      _ = cyclotomicTrace (ω ^ a₃) := by rw [ha₃]
  have hpCyclotomic : p ≤ 20 ^ n.totient :=
    modulus_le_twenty_pow_totient_of_compatible_residue_traces
      p n a₁ a₂ a₃ hcoprimeN ω hω (Nat.le_of_lt ha₁lt) (Nat.le_of_lt ha₂lt)
        (Nat.le_of_lt ha₃lt) xResidue hxResidue hcoord₁ hcoord₂ hcoord₃ hxResidueNe
  have hn_le_m_cube : n ≤ m ^ 3 := by
    have hl₁m : l₁ ≤ m := le_max_left _ _
    have hl₂m : l₂ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
    have hl₃m : l₃ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
    calc
      n ≤ l₁ * Nat.lcm l₂ l₃ := Nat.lcm_le_mul hl₁ (Nat.lcm_pos hl₂ hl₃)
      _ ≤ l₁ * (l₂ * l₃) :=
        Nat.mul_le_mul_left l₁ (Nat.lcm_le_mul hl₂ hl₃)
      _ = l₁ * l₂ * l₃ := by ring
      _ ≤ m * m * m := Nat.mul_le_mul (Nat.mul_le_mul hl₁m hl₂m) hl₃m
      _ = m ^ 3 := by ring
  have htotient : n.totient ≤ m ^ 3 := (Nat.totient_le n).trans hn_le_m_cube
  have hpMax : p ≤ 20 ^ m ^ 3 :=
    hpCyclotomic.trans (Nat.pow_le_pow_right (by norm_num) htotient)
  exact ⟨W₁, W₂, W₃, htrace₁, htrace₂, htrace₃, hfin₁, hfin₂, hfin₃,
    hcoprime₁, hcoprime₂, hcoprime₃, by simpa [l₁, l₂, l₃, m] using hpMax⟩

end BGS.Markoff
