/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Opening.CyclotomicReduction

/-!
# The concrete cyclotomic opening bound

This file evaluates the integral cyclotomic defect at the compatible residue prime and connects
that vanishing to the archimedean norm estimate.
-/

open scoped NumberField

namespace BGS.Markoff

/-- An integral reciprocal trace, written polynomially using `ζⁿ = 1`. -/
noncomputable def openingCyclotomicIntegerTrace
    (n a : ℕ) [NeZero n] : OpeningCyclotomicIntegers n :=
  openingCyclotomicIntegerRoot n ^ a + openingCyclotomicIntegerRoot n ^ (n - a)

/-- The integral defect formed from three polynomial reciprocal traces. -/
noncomputable def openingCyclotomicIntegerDefect
    (n a₁ a₂ a₃ : ℕ) [NeZero n] : OpeningCyclotomicIntegers n :=
  let t₁ := openingCyclotomicIntegerTrace n a₁
  let t₂ := openingCyclotomicIntegerTrace n a₂
  let t₃ := openingCyclotomicIntegerTrace n a₃
  t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃

private theorem openingCyclotomicRoot_pow_mul_complement
    (n a : ℕ) [NeZero n] (ha : a ≤ n) :
    openingCyclotomicRoot n ^ a * openingCyclotomicRoot n ^ (n - a) = 1 := by
  rw [← pow_add, Nat.add_sub_of_le ha]
  exact (openingCyclotomicRoot_isPrimitive n).pow_eq_one

private theorem residueRoot_pow_mul_complement
    {K : Type*} [Field K] {n a : ℕ} {w : K}
    (hw : IsPrimitiveRoot w n) (ha : a ≤ n) :
    w ^ a * w ^ (n - a) = 1 := by
  rw [← pow_add, Nat.add_sub_of_le ha]
  exact hw.pow_eq_one

private theorem coe_openingCyclotomicIntegerRoot (n : ℕ) [NeZero n] :
    algebraMap (OpeningCyclotomicIntegers n) (OpeningCyclotomicField n)
        (openingCyclotomicIntegerRoot n) = openingCyclotomicRoot n := by
  exact (openingCyclotomicRoot_isPrimitive n).coe_toInteger

/-- Coercing the integral polynomial trace to the cyclotomic field gives the reciprocal trace. -/
theorem coe_openingCyclotomicIntegerTrace
    (n a : ℕ) [NeZero n] (ha : a ≤ n) :
    ((openingCyclotomicIntegerTrace n a : OpeningCyclotomicIntegers n) :
        OpeningCyclotomicField n) =
      cyclotomicTrace (openingCyclotomicRoot n ^ a) := by
  rw [openingCyclotomicIntegerTrace, cyclotomicTrace]
  simp only [map_add, map_pow]
  rw [coe_openingCyclotomicIntegerRoot n]
  rw [eq_inv_of_mul_eq_one_right (openingCyclotomicRoot_pow_mul_complement n a ha)]

/-- Coercing the integral polynomial defect gives the characteristic-zero cyclotomic defect. -/
theorem coe_openingCyclotomicIntegerDefect
    (n a₁ a₂ a₃ : ℕ) [NeZero n]
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n) :
    ((openingCyclotomicIntegerDefect n a₁ a₂ a₃ : OpeningCyclotomicIntegers n) :
        OpeningCyclotomicField n) =
      cyclotomicDefect (openingCyclotomicRoot n ^ a₁)
        (openingCyclotomicRoot n ^ a₂) (openingCyclotomicRoot n ^ a₃) := by
  simp only [openingCyclotomicIntegerDefect, map_sub, map_add, map_mul, map_pow]
  rw [show algebraMap (OpeningCyclotomicIntegers n) (OpeningCyclotomicField n)
      (openingCyclotomicIntegerTrace n a₁) =
        cyclotomicTrace (openingCyclotomicRoot n ^ a₁) from
      coe_openingCyclotomicIntegerTrace n a₁ ha₁,
    show algebraMap (OpeningCyclotomicIntegers n) (OpeningCyclotomicField n)
      (openingCyclotomicIntegerTrace n a₂) =
        cyclotomicTrace (openingCyclotomicRoot n ^ a₂) from
      coe_openingCyclotomicIntegerTrace n a₂ ha₂,
    show algebraMap (OpeningCyclotomicIntegers n) (OpeningCyclotomicField n)
      (openingCyclotomicIntegerTrace n a₃) =
        cyclotomicTrace (openingCyclotomicRoot n ^ a₃) from
      coe_openingCyclotomicIntegerTrace n a₃ ha₃]
  rfl

/-- Compatible reduction sends the polynomial integral trace to the prescribed residue trace. -/
theorem openingCyclotomicReduction_integerTrace
    (p n a : ℕ) [Fact p.Prime] [NeZero n] (hcoprime : Nat.Coprime p n)
    (ω : OpeningResidueClosure p) (hω : IsPrimitiveRoot ω n) (ha : a ≤ n) :
    openingCyclotomicReduction p n hcoprime ω hω
        (openingCyclotomicIntegerTrace n a) =
      cyclotomicTrace (ω ^ a) := by
  rw [openingCyclotomicIntegerTrace, map_add, map_pow, map_pow,
    openingCyclotomicReduction_integerRoot, cyclotomicTrace]
  rw [eq_inv_of_mul_eq_one_right (residueRoot_pow_mul_complement hω ha)]

/-- Compatible reduction sends the integral defect to the residue-field cyclotomic defect. -/
theorem openingCyclotomicReduction_integerDefect
    (p n a₁ a₂ a₃ : ℕ) [Fact p.Prime] [NeZero n]
    (hcoprime : Nat.Coprime p n)
    (ω : OpeningResidueClosure p) (hω : IsPrimitiveRoot ω n)
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n) :
    openingCyclotomicReduction p n hcoprime ω hω
        (openingCyclotomicIntegerDefect n a₁ a₂ a₃) =
      cyclotomicDefect (ω ^ a₁) (ω ^ a₂) (ω ^ a₃) := by
  simp only [openingCyclotomicIntegerDefect, map_sub, map_add, map_mul, map_pow]
  rw [openingCyclotomicReduction_integerTrace p n a₁ hcoprime ω hω ha₁,
    openingCyclotomicReduction_integerTrace p n a₂ hcoprime ω hω ha₂,
    openingCyclotomicReduction_integerTrace p n a₃ hcoprime ω hω ha₃]
  rfl

/-- A normalized residue Markoff point makes the corresponding residue cyclotomic defect vanish. -/
theorem residueCyclotomicDefect_eq_zero_of_normalizedMarkoff
    {p : ℕ} [Fact p.Prime] (x : NormalizedPoint (OpeningResidueClosure p))
    (hx : IsNormalizedMarkoff x)
    {z₁ z₂ z₃ : OpeningResidueClosure p}
    (h₁ : x.u1 = cyclotomicTrace z₁) (h₂ : x.u2 = cyclotomicTrace z₂)
    (h₃ : x.u3 = cyclotomicTrace z₃) :
    cyclotomicDefect z₁ z₂ z₃ = 0 := by
  simpa [IsNormalizedMarkoff, normalizedPolynomial, cyclotomicDefect, h₁, h₂, h₃] using hx

/-- The integral defect therefore belongs to the compatible prime selected by the residue root. -/
theorem openingCyclotomicIntegerDefect_mem_prime_of_normalizedMarkoff
    (p n a₁ a₂ a₃ : ℕ) [Fact p.Prime] [NeZero n]
    (hcoprime : Nat.Coprime p n)
    (ω : OpeningResidueClosure p) (hω : IsPrimitiveRoot ω n)
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n)
    (x : NormalizedPoint (OpeningResidueClosure p)) (hx : IsNormalizedMarkoff x)
    (h₁ : x.u1 = cyclotomicTrace (ω ^ a₁))
    (h₂ : x.u2 = cyclotomicTrace (ω ^ a₂))
    (h₃ : x.u3 = cyclotomicTrace (ω ^ a₃)) :
    openingCyclotomicIntegerDefect n a₁ a₂ a₃ ∈
      openingCyclotomicPrime p n hcoprime ω hω := by
  rw [openingCyclotomicPrime, RingHom.mem_ker]
  rw [show (openingCyclotomicReduction p n hcoprime ω hω).toRingHom
      (openingCyclotomicIntegerDefect n a₁ a₂ a₃) =
        cyclotomicDefect (ω ^ a₁) (ω ^ a₂) (ω ^ a₃) from
      openingCyclotomicReduction_integerDefect p n a₁ a₂ a₃ hcoprime ω hω
        ha₁ ha₂ ha₃]
  exact residueCyclotomicDefect_eq_zero_of_normalizedMarkoff x hx h₁ h₂ h₃

private theorem openingCyclotomicRoot_pow_isOfFinOrder
    (n a : ℕ) [NeZero n] : IsOfFinOrder (openingCyclotomicRoot n ^ a) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨n, NeZero.pos n, ?_⟩
  rw [pow_right_comm, (openingCyclotomicRoot_isPrimitive n).pow_eq_one, one_pow]

/-- If the residue traces form a nonorigin point, the characteristic-zero cyclotomic defect of
the compatible powers is nonzero. -/
theorem openingCyclotomicDefect_ne_zero_of_residuePoint_ne_origin
    (p n a₁ a₂ a₃ : ℕ) [Fact p.Prime] [NeZero n]
    (hcoprime : Nat.Coprime p n)
    (ω : OpeningResidueClosure p) (hω : IsPrimitiveRoot ω n)
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n)
    (x : NormalizedPoint (OpeningResidueClosure p))
    (h₁ : x.u1 = cyclotomicTrace (ω ^ a₁))
    (h₂ : x.u2 = cyclotomicTrace (ω ^ a₂))
    (h₃ : x.u3 = cyclotomicTrace (ω ^ a₃))
    (hxne : x ≠ normalizedOrigin) :
    cyclotomicDefect (openingCyclotomicRoot n ^ a₁)
      (openingCyclotomicRoot n ^ a₂) (openingCyclotomicRoot n ^ a₃) ≠ 0 := by
  intro hzero
  let σ : OpeningCyclotomicField n →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let z₁ := openingCyclotomicRoot n ^ a₁
  let z₂ := openingCyclotomicRoot n ^ a₂
  let z₃ := openingCyclotomicRoot n ^ a₃
  have hz₁fin : IsOfFinOrder z₁ := openingCyclotomicRoot_pow_isOfFinOrder n a₁
  have hz₂fin : IsOfFinOrder z₂ := openingCyclotomicRoot_pow_isOfFinOrder n a₂
  have hz₃fin : IsOfFinOrder z₃ := openingCyclotomicRoot_pow_isOfFinOrder n a₃
  have hz₁prim : IsPrimitiveRoot z₁ (orderOf z₁) := IsPrimitiveRoot.orderOf z₁
  have hz₂prim : IsPrimitiveRoot z₂ (orderOf z₂) := IsPrimitiveRoot.orderOf z₂
  have hz₃prim : IsPrimitiveRoot z₃ (orderOf z₃) := IsPrimitiveRoot.orderOf z₃
  have hnorm₁ : ‖σ z₁‖ = 1 :=
    (hz₁prim.map_of_injective σ.injective).norm'_eq_one hz₁fin.orderOf_pos.ne'
  have hnorm₂ : ‖σ z₂‖ = 1 :=
    (hz₂prim.map_of_injective σ.injective).norm'_eq_one hz₂fin.orderOf_pos.ne'
  have hnorm₃ : ‖σ z₃‖ = 1 :=
    (hz₃prim.map_of_injective σ.injective).norm'_eq_one hz₃fin.orderOf_pos.ne'
  have hzeroComplex : cyclotomicDefect (σ z₁) (σ z₂) (σ z₃) = 0 := by
    simpa [z₁, z₂, z₃, cyclotomicDefect, cyclotomicTrace] using congrArg σ hzero
  obtain ⟨htrace₁Complex, htrace₂Complex, htrace₃Complex⟩ :=
    cyclotomicTrace_eq_zero_of_defect_eq_zero hnorm₁ hnorm₂ hnorm₃ hzeroComplex
  have htrace₁ : cyclotomicTrace z₁ = 0 := by
    apply σ.injective
    simpa [cyclotomicTrace] using htrace₁Complex
  have htrace₂ : cyclotomicTrace z₂ = 0 := by
    apply σ.injective
    simpa [cyclotomicTrace] using htrace₂Complex
  have htrace₃ : cyclotomicTrace z₃ = 0 := by
    apply σ.injective
    simpa [cyclotomicTrace] using htrace₃Complex
  have hIntegerTrace₁ : openingCyclotomicIntegerTrace n a₁ = 0 := by
    apply NumberField.RingOfIntegers.coe_injective
    simpa [z₁, coe_openingCyclotomicIntegerTrace n a₁ ha₁] using htrace₁
  have hIntegerTrace₂ : openingCyclotomicIntegerTrace n a₂ = 0 := by
    apply NumberField.RingOfIntegers.coe_injective
    simpa [z₂, coe_openingCyclotomicIntegerTrace n a₂ ha₂] using htrace₂
  have hIntegerTrace₃ : openingCyclotomicIntegerTrace n a₃ = 0 := by
    apply NumberField.RingOfIntegers.coe_injective
    simpa [z₃, coe_openingCyclotomicIntegerTrace n a₃ ha₃] using htrace₃
  have hResidueTrace₁ : cyclotomicTrace (ω ^ a₁) = 0 := by
    simpa [hIntegerTrace₁] using
      (openingCyclotomicReduction_integerTrace p n a₁ hcoprime ω hω ha₁).symm
  have hResidueTrace₂ : cyclotomicTrace (ω ^ a₂) = 0 := by
    simpa [hIntegerTrace₂] using
      (openingCyclotomicReduction_integerTrace p n a₂ hcoprime ω hω ha₂).symm
  have hResidueTrace₃ : cyclotomicTrace (ω ^ a₃) = 0 := by
    simpa [hIntegerTrace₃] using
      (openingCyclotomicReduction_integerTrace p n a₃ hcoprime ω hω ha₃).symm
  apply hxne
  apply NormalizedPoint.ext
  · simpa [normalizedOrigin, h₁] using hResidueTrace₁
  · simpa [normalizedOrigin, h₂] using hResidueTrace₂
  · simpa [normalizedOrigin, h₃] using hResidueTrace₃

/-- The concrete cyclotomic opening inequality.  A nonorigin normalized Markoff point whose three
coordinates are reciprocal traces of powers of one primitive residue root forces
`p ≤ 20 ^ φ(n)`. -/
theorem modulus_le_twenty_pow_totient_of_compatible_residue_traces
    (p n a₁ a₂ a₃ : ℕ) [Fact p.Prime] [NeZero n]
    (hcoprime : Nat.Coprime p n)
    (ω : OpeningResidueClosure p) (hω : IsPrimitiveRoot ω n)
    (ha₁ : a₁ ≤ n) (ha₂ : a₂ ≤ n) (ha₃ : a₃ ≤ n)
    (x : NormalizedPoint (OpeningResidueClosure p)) (hx : IsNormalizedMarkoff x)
    (h₁ : x.u1 = cyclotomicTrace (ω ^ a₁))
    (h₂ : x.u2 = cyclotomicTrace (ω ^ a₂))
    (h₃ : x.u3 = cyclotomicTrace (ω ^ a₃))
    (hxne : x ≠ normalizedOrigin) :
    p ≤ 20 ^ n.totient := by
  letI : NeZero (n : ℚ) := ⟨by exact_mod_cast (NeZero.ne n)⟩
  letI : IsCyclotomicExtension {n} ℚ (OpeningCyclotomicField n) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let z₁ := openingCyclotomicRoot n ^ a₁
  let z₂ := openingCyclotomicRoot n ^ a₂
  let z₃ := openingCyclotomicRoot n ^ a₃
  let l₁ := orderOf z₁
  let l₂ := orderOf z₂
  let l₃ := orderOf z₃
  have hz₁fin : IsOfFinOrder z₁ := openingCyclotomicRoot_pow_isOfFinOrder n a₁
  have hz₂fin : IsOfFinOrder z₂ := openingCyclotomicRoot_pow_isOfFinOrder n a₂
  have hz₃fin : IsOfFinOrder z₃ := openingCyclotomicRoot_pow_isOfFinOrder n a₃
  have hz₁ : IsPrimitiveRoot z₁ l₁ := IsPrimitiveRoot.orderOf z₁
  have hz₂ : IsPrimitiveRoot z₂ l₂ := IsPrimitiveRoot.orderOf z₂
  have hz₃ : IsPrimitiveRoot z₃ l₃ := IsPrimitiveRoot.orderOf z₃
  have hl₁ : 0 < l₁ := hz₁fin.orderOf_pos
  have hl₂ : 0 < l₂ := hz₂fin.orderOf_pos
  have hl₃ : 0 < l₃ := hz₃fin.orderOf_pos
  let P := openingCyclotomicPrime p n hcoprime ω hω
  have hdefectNe : cyclotomicDefect z₁ z₂ z₃ ≠ 0 := by
    exact openingCyclotomicDefect_ne_zero_of_residuePoint_ne_origin
      p n a₁ a₂ a₃ hcoprime ω hω ha₁ ha₂ ha₃ x h₁ h₂ h₃ hxne
  have hred :
      let γ : OpeningCyclotomicIntegers n :=
        ⟨cyclotomicDefect z₁ z₂ z₃,
          isIntegral_cyclotomicDefect_of_primitiveRoots hz₁ hl₁ hz₂ hl₂ hz₃ hl₃⟩
      Ideal.Quotient.mk P γ = 0 := by
    dsimp only
    erw [Ideal.Quotient.eq_zero_iff_mem]
    have hmem := openingCyclotomicIntegerDefect_mem_prime_of_normalizedMarkoff
      p n a₁ a₂ a₃ hcoprime ω hω ha₁ ha₂ ha₃ x hx h₁ h₂ h₃
    rw [show (⟨cyclotomicDefect z₁ z₂ z₃,
        isIntegral_cyclotomicDefect_of_primitiveRoots hz₁ hl₁ hz₂ hl₂ hz₃ hl₃⟩ :
          OpeningCyclotomicIntegers n) = openingCyclotomicIntegerDefect n a₁ a₂ a₃ by
      apply Subtype.ext
      exact (coe_openingCyclotomicIntegerDefect n a₁ a₂ a₃ ha₁ ha₂ ha₃).symm]
    exact hmem
  exact modulus_le_twenty_pow_totient_of_cyclotomicDefect_reduction
    (n := n) hz₁ hl₁ hz₂ hl₂ hz₃ hl₃ P p
      (by simpa [P] using openingCyclotomicPrime_under p n hcoprime ω hω)
      hdefectNe hred

end BGS.Markoff
