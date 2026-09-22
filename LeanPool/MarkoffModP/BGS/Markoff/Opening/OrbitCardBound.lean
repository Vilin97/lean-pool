/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Opening.RotationOrbitCard
import LeanPool.MarkoffModP.BGS.Markoff.Opening.TraceOrderBound

/-!
# Bounding the opening orders by the full Gamma orbit

The nonzero semisimple fibers use the existing conic parametrizations.  Trace zero and the two
parabolic traces are handled explicitly, since the generic parametrizations deliberately exclude
those values.
-/

namespace BGS.Markoff

private theorem two_ne_zero_zmod_of_prime_ne_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
  exact hpTwo (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hpDvd)
    (Fact.out : p.Prime).two_le)

private theorem four_le_normalizedGammaOrbit_ncard_of_firstCoordinate_zero
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (hpTwo : p ≠ 2)
    (x : NormalizedMarkoffSurface (ZMod p)) (hxzero : x.1.u1 = 0)
    (hxne : x.1 ≠ normalizedOrigin) :
    4 ≤ (normalizedGammaOrbit x).ncard := by
  classical
  have hsurface : x.1.u2 ^ 2 + x.1.u3 ^ 2 = 0 := by
    have := x.property
    change normalizedPolynomial x.1 = 0 at this
    rw [normalizedPolynomial, hxzero] at this
    simpa using this
  have h₂ : x.1.u2 ≠ 0 := by
    intro hzero
    rw [hzero] at hsurface
    have h₃sq : x.1.u3 ^ 2 = 0 := by simpa using hsurface
    have h₃ : x.1.u3 = 0 := sq_eq_zero_iff.mp h₃sq
    apply hxne
    ext
    · simpa [normalizedOrigin] using hxzero
    · simpa [normalizedOrigin] using hzero
    · simpa [normalizedOrigin] using h₃
  have h₃ : x.1.u3 ≠ 0 := by
    intro hzero
    rw [hzero] at hsurface
    have h₂sq : x.1.u2 ^ 2 = 0 := by simpa using hsurface
    exact h₂ (sq_eq_zero_iff.mp h₂sq)
  have h₂₃ : x.1.u2 ≠ x.1.u3 := by
    intro heq
    have htwo : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod_of_prime_ne_two p hpTwo
    have hsq : 2 * x.1.u2 ^ 2 = 0 := by
      rw [← heq] at hsurface
      linear_combination hsurface
    have : x.1.u2 ^ 2 = 0 := (mul_eq_zero.mp hsq).resolve_left htwo
    exact h₂ (sq_eq_zero_iff.mp this)
  let x₁₂ := normalizedSwap12Surface x
  let x₂₃ := normalizedSwap23Surface x
  let x₂₃₁₂ := normalizedSwap12Surface x₂₃
  let f : Fin 4 → NormalizedMarkoffSurface (ZMod p) := ![x, x₁₂, x₂₃, x₂₃₁₂]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      exfalso
      have hval := congrArg Subtype.val hij
      have hfirst := congrArg NormalizedPoint.u1 hval
      have hsecond := congrArg NormalizedPoint.u2 hval
      have hthird := congrArg NormalizedPoint.u3 hval
      simp [f, x₁₂, x₂₃, x₂₃₁₂, normalizedSwap12Surface,
        normalizedSwap23Surface, normalizedSwap12, normalizedSwap23, hxzero] at hfirst hsecond hthird
      first
      | exact h₂ hfirst
      | exact h₂ hfirst.symm
      | exact h₂ hsecond
      | exact h₂ hsecond.symm
      | exact h₂ hthird
      | exact h₂ hthird.symm
      | exact h₃ hfirst
      | exact h₃ hfirst.symm
      | exact h₃ hsecond
      | exact h₃ hsecond.symm
      | exact h₃ hthird
      | exact h₃ hthird.symm
      | exact h₂₃ hfirst
      | exact h₂₃ hfirst.symm
      | exact h₂₃ hsecond
      | exact h₂₃ hsecond.symm
  let cycle : Finset (NormalizedMarkoffSurface (ZMod p)) := Finset.univ.image f
  have hcard : cycle.card = 4 := by
    change (Finset.univ.image f).card = 4
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hsubset : (cycle : Set (NormalizedMarkoffSurface (ZMod p))) ⊆ normalizedGammaOrbit x := by
    change ((↑(Finset.univ.image f) : Set _) ⊆ normalizedGammaOrbit x)
    intro y hy
    rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨i, _hi, rfl⟩ := hy
    fin_cases i
    · exact (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp
        (sameNormalizedComponent_refl x)
    · exact (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp
        (sameNormalizedComponent_swap12Surface x)
    · exact (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp
        (sameNormalizedComponent_swap23Surface x)
    · exact (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp
        (sameNormalizedComponent_trans (sameNormalizedComponent_swap23Surface x)
          (sameNormalizedComponent_swap12Surface (normalizedSwap23Surface x)))
  rw [← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsubset

private theorem two_le_normalizedGammaOrbit_ncard_of_parabolic_firstCoordinate
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (hpTwo : p ≠ 2)
    (x : NormalizedMarkoffSurface (ZMod p)) (hxparabolic : x.1.u1 ^ 2 = 4) :
    2 ≤ (normalizedGammaOrbit x).ncard := by
  classical
  have hrotateNe : normalizedRotate1Surface x ≠ x := by
    intro hfix
    have hval := congrArg Subtype.val hfix
    have h₂ := congrArg NormalizedPoint.u2 hval
    have h₃ := congrArg NormalizedPoint.u3 hval
    change x.1.u3 = x.1.u2 at h₂
    change x.1.u1 * x.1.u3 - x.1.u2 = x.1.u3 at h₃
    have hcases : x.1.u1 = 2 ∨ x.1.u1 = -2 := by
      have hfactor : (x.1.u1 - 2) * (x.1.u1 + 2) = 0 := by
        calc
          (x.1.u1 - 2) * (x.1.u1 + 2) = x.1.u1 ^ 2 - 4 := by ring
          _ = 0 := sub_eq_zero.mpr hxparabolic
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    have htwo : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod_of_prime_ne_two p hpTwo
    rcases hcases with ht | ht
    · have hsurface : normalizedPolynomial x.1 = 0 := x.property
      rw [normalizedPolynomial, ht, h₂] at hsurface
      have hfourZero : (4 : ZMod p) = 0 := by linear_combination hsurface
      have hfour : (4 : ZMod p) ≠ 0 := by
        (convert pow_ne_zero 2 htwo using 1; norm_num [pow_two])
      exact hfour hfourZero
    · have hy : x.1.u2 = 0 := by
        rw [ht, h₂] at h₃
        have hfour : (4 : ZMod p) ≠ 0 := by
          (convert pow_ne_zero 2 htwo using 1; norm_num [pow_two])
        exact (mul_eq_zero.mp (by linear_combination -h₃)).resolve_left hfour
      have hsurface : normalizedPolynomial x.1 = 0 := x.property
      rw [normalizedPolynomial, ht, h₂, hy] at hsurface
      have hfourZero : (4 : ZMod p) = 0 := by linear_combination hsurface
      have hfour : (4 : ZMod p) ≠ 0 := by
        (convert pow_ne_zero 2 htwo using 1; norm_num [pow_two])
      exact hfour hfourZero
  let pair : Finset (NormalizedMarkoffSurface (ZMod p)) := {x, normalizedRotate1Surface x}
  have hcard : pair.card = 2 := by
    change ({x, normalizedRotate1Surface x} : Finset _).card = 2
    exact Finset.card_pair hrotateNe.symm
  have hsubset : (pair : Set (NormalizedMarkoffSurface (ZMod p))) ⊆ normalizedGammaOrbit x := by
    change ((↑({x, normalizedRotate1Surface x} : Finset _) : Set _) ⊆ normalizedGammaOrbit x)
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy
    · subst y
      apply (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp
      exact sameNormalizedComponent_refl x
    · subst y
      apply (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp
      exact sameNormalizedComponent_rotate1Surface x
  rw [← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsubset

/-- The exact order of any residue-closure eigenvalue representing the first trace is bounded by
the full normalized Gamma orbit.  Nonzero semisimple traces use the conic rotation cycles; trace
zero and parabolic traces use the explicit exceptional lower bounds above. -/
theorem eigenvalueOrder_le_normalizedGammaOrbit_ncard
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (hpTwo : p ≠ 2)
    (x : NormalizedMarkoffSurface (ZMod p)) (hxne : x.1 ≠ normalizedOrigin)
    (W : (OpeningResidueClosure p)ˣ)
    (htrace : algebraMap (ZMod p) (OpeningResidueClosure p) x.1.u1 = splitTorusTrace W) :
    orderOf W ≤ (normalizedGammaOrbit x).ncard := by
  by_cases hparabolic : x.1.u1 ^ 2 = 4
  · have htraceSq : (splitTorusTrace W) ^ 2 = 4 := by
      rw [← htrace, ← map_pow, hparabolic, map_ofNat]
    have hdiffSq :
        ((W : OpeningResidueClosure p) - ((W⁻¹ : (OpeningResidueClosure p)ˣ) :
          OpeningResidueClosure p)) ^ 2 = 0 := by
      have hmul : (W : OpeningResidueClosure p) *
          ((W⁻¹ : (OpeningResidueClosure p)ˣ) : OpeningResidueClosure p) = 1 := by simp
      rw [splitTorusTrace] at htraceSq
      linear_combination htraceSq - 4 * hmul
    have hinv : ((W⁻¹ : (OpeningResidueClosure p)ˣ) : OpeningResidueClosure p) = W := by
      exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hdiffSq)).symm
    have hWsq : W ^ 2 = 1 := by
      apply Units.ext
      change (W : OpeningResidueClosure p) ^ 2 = 1
      calc
        (W : OpeningResidueClosure p) ^ 2 = W * W := pow_two _
        _ = W * ((W⁻¹ : (OpeningResidueClosure p)ˣ) : OpeningResidueClosure p) := by rw [hinv]
        _ = 1 := by simp
    have horder : orderOf W ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hWsq)
    exact horder.trans
      (two_le_normalizedGammaOrbit_ncard_of_parabolic_firstCoordinate p hpTwo x hparabolic)
  · by_cases hzero : x.1.u1 = 0
    · have hsum : splitTorusTrace W = 0 := by rw [← htrace, hzero, map_zero]
      have hWsq : ((W : OpeningResidueClosure p) ^ 2) = -1 := by
        have hmul : (W : OpeningResidueClosure p) *
            ((W⁻¹ : (OpeningResidueClosure p)ˣ) : OpeningResidueClosure p) = 1 := by simp
        rw [splitTorusTrace] at hsum
        calc
          (W : OpeningResidueClosure p) ^ 2 =
              W * (W + ((W⁻¹ : (OpeningResidueClosure p)ˣ) : OpeningResidueClosure p)) -
                W * ((W⁻¹ : (OpeningResidueClosure p)ˣ) : OpeningResidueClosure p) := by ring
          _ = 0 - 1 := by rw [hsum, mul_zero, hmul]
          _ = -1 := by ring
      have hWfour : W ^ 4 = 1 := by
        apply Units.ext
        change (W : OpeningResidueClosure p) ^ 4 = 1
        calc
          (W : OpeningResidueClosure p) ^ 4 = ((W : OpeningResidueClosure p) ^ 2) ^ 2 := by ring
          _ = (-1 : OpeningResidueClosure p) ^ 2 := by rw [hWsq]
          _ = 1 := by ring
      have horder : orderOf W ≤ 4 :=
        Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hWfour)
      exact horder.trans
        (four_le_normalizedGammaOrbit_ncard_of_firstCoordinate_zero p hpTwo x hzero hxne)
    · have hWnonparabolic : (W : OpeningResidueClosure p) ^ 2 ≠ 1 := by
        intro hW
        apply hparabolic
        apply (algebraMap (ZMod p) (OpeningResidueClosure p)).injective
        rw [map_pow, map_ofNat, htrace]
        have hinv : ((W⁻¹ : (OpeningResidueClosure p)ˣ) : OpeningResidueClosure p) = W :=
          Units.inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hW)
        rw [splitTorusTrace, hinv]
        calc
          ((W : OpeningResidueClosure p) + W) ^ 2 = 4 * (W : OpeningResidueClosure p) ^ 2 := by ring
          _ = 4 := by rw [hW, mul_one]
      have hrotation : rotationOrder x.1.u1 = orderOf W :=
        rotationOrder_eq_orderOf_extensionEigenvalue x.1.u1 W hWnonparabolic htrace
      let xf : ↑(normalizedFiber1 x.1.u1) := ⟨x.1, x.property, rfl⟩
      have hcycle : (normalizedRotationCycle x.1.u1 x.1).card = rotationOrder x.1.u1 := by
        simpa [xf] using normalizedRotationCycle_card_of_nonzero_nonparabolic
          p hpTwo x.1.u1 hparabolic hzero xf
      calc
        orderOf W = rotationOrder x.1.u1 := hrotation.symm
        _ = (normalizedRotationCycle x.1.u1 x.1).card := hcycle.symm
        _ ≤ (normalizedGammaOrbit x).ncard :=
          normalizedRotationCycle_card_le_normalizedGammaOrbit_ncard x

private theorem three_ne_zero_zmod_of_prime_ne_three
    (p : ℕ) [Fact p.Prime] (hpThree : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 hzero
  have hpLe : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpDvd
  have hpGe : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpTwoOrThree : p = 2 ∨ p = 3 := by omega
  rcases hpTwoOrThree with hpTwo | hpThreeEq
  · subst p
    norm_num at hpDvd
  · exact hpThree hpThreeEq

/-- The concrete opening exponent can be bounded by the cardinality of the full normalized Gamma
orbit.  The exclusions `p ≠ 2, 3` are explicit: oddness is used by the trace classification and
`3` must be invertible for the transported normalized action. -/
theorem prime_le_twenty_pow_normalizedGammaOrbit_ncard_cube
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (hpThree : p ≠ 3)
    (x : NormalizedMarkoffSurface (ZMod p)) (hxne : x.1 ≠ normalizedOrigin) :
    p ≤ 20 ^ (letI : Invertible (3 : ZMod p) :=
      invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
      normalizedGammaOrbit x).ncard ^ 3 := by
  let : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
  obtain ⟨W₁, W₂, W₃, htrace₁, htrace₂, htrace₃, _hfin₁, _hfin₂, _hfin₃,
      _hcoprime₁, _hcoprime₂, _hcoprime₃, hpBound⟩ :=
    exists_exact_eigenvalue_orders_with_cyclotomic_bound p hpTwo x.1 x.property hxne
  let m := (normalizedGammaOrbit x).ncard
  have horder₁ : orderOf W₁ ≤ m :=
    eigenvalueOrder_le_normalizedGammaOrbit_ncard p hpTwo x hxne W₁ htrace₁
  let x₂ := normalizedSwap12Surface x
  have hx₂ne : x₂.1 ≠ normalizedOrigin := by
    intro hzero
    simp [x₂, normalizedSwap12Surface, normalizedSwap12, normalizedOrigin] at hzero
    apply hxne
    ext
    · exact hzero.2.1
    · exact hzero.1
    · exact hzero.2.2
  have horbit₂ : normalizedGammaOrbit x₂ = normalizedGammaOrbit x := by
    apply MulAction.orbit_eq_iff.mpr
    exact (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp
      (sameNormalizedComponent_swap12Surface x)
  have horder₂ : orderOf W₂ ≤ m := by
    have h := eigenvalueOrder_le_normalizedGammaOrbit_ncard p hpTwo x₂ hx₂ne W₂ (by
      simpa [x₂, normalizedSwap12Surface, normalizedSwap12] using htrace₂)
    simpa [m, horbit₂] using h
  let x₃ := normalizedSwap12Surface (normalizedSwap23Surface x)
  have hx₃ne : x₃.1 ≠ normalizedOrigin := by
    intro hzero
    simp [x₃, normalizedSwap12Surface, normalizedSwap23Surface,
      normalizedSwap12, normalizedSwap23, normalizedOrigin] at hzero
    apply hxne
    ext
    · exact hzero.2.1
    · exact hzero.2.2
    · exact hzero.1
  have hx₃component : SameNormalizedComponent x x₃ :=
    sameNormalizedComponent_trans (sameNormalizedComponent_swap23Surface x)
      (sameNormalizedComponent_swap12Surface (normalizedSwap23Surface x))
  have horbit₃ : normalizedGammaOrbit x₃ = normalizedGammaOrbit x := by
    apply MulAction.orbit_eq_iff.mpr
    exact (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp hx₃component
  have horder₃ : orderOf W₃ ≤ m := by
    have h := eigenvalueOrder_le_normalizedGammaOrbit_ncard p hpTwo x₃ hx₃ne W₃ (by
      simpa [x₃, normalizedSwap12Surface, normalizedSwap23Surface,
        normalizedSwap12, normalizedSwap23] using htrace₃)
    simpa [m, horbit₃] using h
  have hmax : max (orderOf W₁) (max (orderOf W₂) (orderOf W₃)) ≤ m := by
    exact max_le horder₁ (max_le horder₂ horder₃)
  exact hpBound.trans (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left hmax 3))

/-- Normalization carries the original Gamma orbit bijectively onto the transported normalized
Gamma orbit. -/
theorem normalizedGammaOrbit_normalization_eq_image
    {R : Type*} [Field R] [Invertible (3 : R)] (x : MarkoffSurface R) :
    normalizedGammaOrbit (normalizationSurfaceEquiv R x) =
      normalizationSurfaceEquiv R '' gammaOrbit x := by
  ext y
  constructor
  · intro hy
    have hcomponent : SameNormalizedComponent (normalizationSurfaceEquiv R x) y :=
      (sameNormalizedComponent_iff_mem_normalizedGammaOrbit _ _).2 hy
    have horiginal : SameComponent x ((normalizationSurfaceEquiv R).symm y) := by
      simpa [SameNormalizedComponent] using hcomponent
    exact ⟨(normalizationSurfaceEquiv R).symm y, horiginal,
      (normalizationSurfaceEquiv R).apply_symm_apply y⟩
  · rintro ⟨z, hz, rfl⟩
    apply (sameNormalizedComponent_iff_mem_normalizedGammaOrbit _ _).1
    have horiginal : SameComponent x z := hz
    simpa [SameNormalizedComponent] using horiginal

/-- Original and normalized Gamma orbits have the same cardinality. -/
theorem normalizedGammaOrbit_normalization_ncard
    {R : Type*} [Field R] [Invertible (3 : R)] (x : MarkoffSurface R) :
    (normalizedGammaOrbit (normalizationSurfaceEquiv R x)).ncard = (gammaOrbit x).ncard := by
  rw [normalizedGammaOrbit_normalization_eq_image]
  exact Set.ncard_image_of_injective _ (normalizationSurfaceEquiv R).injective

/-- Original-coordinate form of the orbit-card opening bound. -/
theorem prime_le_twenty_pow_gammaOrbit_ncard_cube
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (hpThree : p ≠ 3)
    (x : MarkoffSurface (ZMod p)) (hxne : x.1 ≠ origin) :
    p ≤ 20 ^ (gammaOrbit x).ncard ^ 3 := by
  let : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
  let xn := normalizationSurfaceEquiv (ZMod p) x
  have hxnNe : xn.1 ≠ normalizedOrigin := by
    intro hzero
    apply hxne
    change toNormalized x.1 = normalizedOrigin at hzero
    have hsurfaceOriginal : x = ⟨origin, markoffPolynomial_origin⟩ := by
      apply (normalizationSurfaceEquiv (ZMod p)).injective
      apply Subtype.ext
      change toNormalized x.1 = toNormalized origin
      simpa using hzero
    exact congrArg Subtype.val hsurfaceOriginal
  have hbound := prime_le_twenty_pow_normalizedGammaOrbit_ncard_cube
    p hpTwo hpThree xn hxnNe
  rw [normalizedGammaOrbit_normalization_ncard] at hbound
  exact hbound

end BGS.Markoff
