/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindDifferentDivisor
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Scaling derivations at ramified Dedekind places

Let `C → S → T → U` be a tower, let `D` preserve `S`, and let `E` be an
ambient derivation on `U` extending `D`. The transitivity exact sequence for
Kähler differentials shows that every element annihilating `Ω[T⁄S]` clears the
obstruction to `E` preserving `T`.

For a power basis, the minimal-polynomial derivative supplies such a factor
and generates the trace different. For a general ramified extension, the
comparison between the trace different and the Kähler annihilator is retained
as an explicit hypothesis; mathlib does not currently supply it in the needed
generality.
-/

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable {C S T U : Type*}
  [CommRing C] [CommRing S] [CommRing T] [CommRing U]
  [Algebra C S] [Algebra C T] [Algebra S T]
  [Algebra C U] [Algebra S U] [Algebra T U]
  [IsScalarTower C S T] [IsScalarTower C S U]
  [IsScalarTower C T U] [IsScalarTower S T U]

/-- The ideal of scalars annihilating the relative Kähler differentials. -/
def kaehlerDifferentialAnnihilator (S T : Type*)
    [CommRing S] [CommRing T] [Algebra S T] : Ideal T :=
  Module.annihilator T Ω[T⁄S]

theorem mem_kaehlerDifferentialAnnihilator_iff (c : T) :
    c ∈ kaehlerDifferentialAnnihilator S T ↔
      ∀ ω : Ω[T⁄S], c • ω = 0 := by
  exact Module.mem_annihilator

theorem liftKaehlerDifferential_algebraMap_compDer
    (D : Derivation C S S) :
    ((Algebra.linearMap S T).compDer D).liftKaehlerDifferential =
      (Algebra.linearMap S T).comp D.liftKaehlerDifferential := by
  apply Derivation.liftKaehlerDifferential_unique
  ext s
  simp

/-- Evaluation of a base-changed differential agrees with evaluation by an
ambient derivation extending the base derivation. -/
theorem kaehler_baseChange_evaluation_naturality
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s))
    (z : TensorProduct S T (KaehlerDifferential C S)) :
    algebraMap T U
        (((((Algebra.linearMap S T).compDer D).liftKaehlerDifferential).liftBaseChange T) z) =
      E.liftKaehlerDifferential
        (KaehlerDifferential.map C C T U
          (KaehlerDifferential.mapBaseChange C S T z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t ω =>
      rw [LinearMap.liftBaseChange_tmul,
        KaehlerDifferential.mapBaseChange_tmul]
      simp only [map_smul]
      let l₁ : KaehlerDifferential C S →ₗ[S] U :=
        (Algebra.linearMap S U).comp D.liftKaehlerDifferential
      let l₂ : KaehlerDifferential C S →ₗ[S] U :=
        (E.liftKaehlerDifferential.restrictScalars S).comp
          ((KaehlerDifferential.map C C T U).restrictScalars S |>.comp
            (KaehlerDifferential.map C C S T))
      have hl : l₁ = l₂ := by
        apply Derivation.liftKaehlerDifferential_unique
        apply Derivation.ext
        intro s
        change l₁ (KaehlerDifferential.D C S s) =
          l₂ (KaehlerDifferential.D C S s)
        dsimp only [l₁, l₂, LinearMap.comp_apply,
          LinearMap.restrictScalars_apply]
        rw [Derivation.liftKaehlerDifferential_comp_D,
          KaehlerDifferential.map_D, KaehlerDifferential.map_D,
          Derivation.liftKaehlerDifferential_comp_D]
        rw [← IsScalarTower.algebraMap_apply S T U]
        simpa using (hE s).symm
      have hω :
          algebraMap T U
              (((Algebra.linearMap S T).compDer D).liftKaehlerDifferential ω) =
            E.liftKaehlerDifferential
              (KaehlerDifferential.map C C T U
                (KaehlerDifferential.map C C S T ω)) := by
        rw [liftKaehlerDifferential_algebraMap_compDer]
        change algebraMap T U
            (algebraMap S T (D.liftKaehlerDifferential ω)) = _
        rw [← IsScalarTower.algebraMap_apply S T U]
        simpa [l₁, l₂] using LinearMap.congr_fun hl ω
      simpa [Algebra.smul_def] using
        congrArg (fun y : U => algebraMap T U t * y) hω
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- A scalar annihilating `Ω[T⁄S]` makes the scaled ambient derivation preserve
`T`. This is the ramified analogue of formal-étale derivation preservation. -/
theorem scaled_ambientDerivation_preserves_of_mem_kaehlerDifferentialAnnihilator
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s))
    (c : T) (hc : c ∈ kaehlerDifferentialAnnihilator S T) :
    ∀ t : T, ∃ t' : T,
      algebraMap T U c * E (algebraMap T U t) = algebraMap T U t' := by
  intro t
  have hker : KaehlerDifferential.map C S T T
      (c • KaehlerDifferential.D C T t) = 0 := by
    rw [map_smul, KaehlerDifferential.map_D]
    exact (mem_kaehlerDifferentialAnnihilator_iff c).mp hc _
  have hrange : c • KaehlerDifferential.D C T t ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange C S T) :=
    ((KaehlerDifferential.exact_mapBaseChange_map C S T)
      (c • KaehlerDifferential.D C T t)).mp hker
  obtain ⟨z, hz⟩ := hrange
  let t' : T :=
    (((((Algebra.linearMap S T).compDer D).liftKaehlerDifferential).liftBaseChange T) z)
  refine ⟨t', ?_⟩
  rw [kaehler_baseChange_evaluation_naturality D E hE z, hz, map_smul,
    KaehlerDifferential.map_D]
  simp [Derivation.liftKaehlerDifferential_comp_D, Algebra.smul_def]

section PrincipalAnnihilatingIdeal

variable [IsPrincipalIdealRing T]

/-- A nonzero principal ideal contained in the Kähler annihilator has a
nonzero generator which clears the ambient derivation. -/
theorem exists_generator_scaled_ambientDerivation_preserves
    (I : Ideal T) (hI : I ≠ ⊥)
    (hIann : I ≤ kaehlerDifferentialAnnihilator S T)
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s)) :
    ∃ c : T,
      c ≠ 0 ∧
      Ideal.span {c} = I ∧
      c ∈ kaehlerDifferentialAnnihilator S T ∧
      ∀ t : T, ∃ t' : T,
        algebraMap T U c * E (algebraMap T U t) = algebraMap T U t' := by
  let c : T := Submodule.IsPrincipal.generator I
  have hspan : Ideal.span {c} = I := Ideal.span_singleton_generator I
  have hc : c ≠ 0 := by
    intro hc0
    have hbot : Ideal.span {c} = ⊥ :=
      Ideal.span_singleton_eq_bot.mpr hc0
    exact hI (hspan.symm.trans hbot)
  have hcann : c ∈ kaehlerDifferentialAnnihilator S T :=
    hIann (Submodule.IsPrincipal.generator_mem I)
  exact ⟨c, hc, hspan, hcann,
    scaled_ambientDerivation_preserves_of_mem_kaehlerDifferentialAnnihilator
      D E hE c hcann⟩

end PrincipalAnnihilatingIdeal

section PowerBasisAnnihilator

/-- For a power basis, the derivative of the generator's minimal polynomial
annihilates the relative Kähler differentials. -/
theorem powerBasis_minpolyDerivative_mem_kaehlerDifferentialAnnihilator
    (pb : PowerBasis S T) :
    Polynomial.aeval pb.gen
        (Polynomial.derivative (minpoly S pb.gen)) ∈
      kaehlerDifferentialAnnihilator S T := by
  rw [mem_kaehlerDifferentialAnnihilator_iff]
  let c : T := Polynomial.aeval pb.gen
    (Polynomial.derivative (minpoly S pb.gen))
  have hcgen : c • KaehlerDifferential.D S T pb.gen = 0 := by
    have hchain :=
      (KaehlerDifferential.D S T).map_aeval (minpoly S pb.gen) pb.gen
    rw [minpoly.aeval, map_zero] at hchain
    exact hchain.symm
  intro ω
  change c • ω = 0
  let l : KaehlerDifferential S T →ₗ[T] KaehlerDifferential S T :=
    LinearMap.lsmul T (KaehlerDifferential S T) c
  have hl : l = 0 := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext_of_adjoin_eq_top {pb.gen} pb.adjoin_gen_eq_top
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    change c • KaehlerDifferential.D S T pb.gen = 0
    exact hcgen
  have hω := LinearMap.congr_fun hl ω
  simpa [l] using hω

/-- The minimal-polynomial derivative of a power-basis generator clears the
ambient derivation. -/
theorem powerBasis_minpolyDerivative_scaled_ambientDerivation_preserves
    (pb : PowerBasis S T)
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s)) :
    ∀ t : T, ∃ t' : T,
      algebraMap T U
          (Polynomial.aeval pb.gen
            (Polynomial.derivative (minpoly S pb.gen))) *
        E (algebraMap T U t) = algebraMap T U t' := by
  exact
    scaled_ambientDerivation_preserves_of_mem_kaehlerDifferentialAnnihilator
      D E hE _
      (powerBasis_minpolyDerivative_mem_kaehlerDifferentialAnnihilator pb)

end PowerBasisAnnihilator

section PrincipalDifferent

variable [IsDomain S] [IsDedekindDomain T]
  [Module.IsTorsionFree S T]

/-- If the trace different is contained in the Kähler annihilator, a generator
of the different is an exact ramified derivation-clearing factor. -/
theorem exists_differentGenerator_scaled_ambientDerivation_preserves
    [IsPrincipalIdealRing T]
    (hDifferent : differentIdeal S T ≠ ⊥)
    (hDifferentKaehler :
      differentIdeal S T ≤ kaehlerDifferentialAnnihilator S T)
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s)) :
    ∃ c : T,
      c ≠ 0 ∧
      Ideal.span {c} = differentIdeal S T ∧
      c ∈ kaehlerDifferentialAnnihilator S T ∧
      ∀ t : T, ∃ t' : T,
        algebraMap T U c * E (algebraMap T U t) = algebraMap T U t' := by
  exact exists_generator_scaled_ambientDerivation_preserves
    (differentIdeal S T) hDifferent hDifferentKaehler D E hE

variable {F : Type*} [Field F] [Algebra T F] [IsFractionRing T F]

/-- A generator of the different has finite-place order exactly equal to the
different multiplicity. -/
theorem finitePlaceOrder_differentGenerator_eq_multiplicity
    (c : T) (hc : c ≠ 0)
    (hspan : Ideal.span {c} = differentIdeal S T)
    (v : HeightOneSpectrum T) :
    finitePlaceOrder v (algebraMap T F c) =
      (multiplicity v.asIdeal (differentIdeal S T) : ℤ) := by
  rw [finitePlaceOrder_algebraMap_eq_multiplicity v c hc, hspan]

/-- A single certificate combining ramified derivation preservation with the
exact local order of the clearing factor. -/
theorem exists_differentGenerator_scaling_certificate
    [IsPrincipalIdealRing T]
    (hDifferent : differentIdeal S T ≠ ⊥)
    (hDifferentKaehler :
      differentIdeal S T ≤ kaehlerDifferentialAnnihilator S T)
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s)) :
    ∃ c : T,
      c ≠ 0 ∧
      Ideal.span {c} = differentIdeal S T ∧
      c ∈ kaehlerDifferentialAnnihilator S T ∧
      (∀ v : HeightOneSpectrum T,
        finitePlaceOrder v (algebraMap T F c) =
          (multiplicity v.asIdeal (differentIdeal S T) : ℤ)) ∧
      ∀ t : T, ∃ t' : T,
        algebraMap T U c * E (algebraMap T U t) = algebraMap T U t' := by
  obtain ⟨c, hc, hspan, hcann, hpreserves⟩ :=
    exists_differentGenerator_scaled_ambientDerivation_preserves
      hDifferent hDifferentKaehler D E hE
  exact ⟨c, hc, hspan, hcann,
    fun v => finitePlaceOrder_differentGenerator_eq_multiplicity c hc hspan v,
    hpreserves⟩

end PrincipalDifferent

section ReparameterizedLocalOrder

variable {R A F : Type*} [CommRing R] [IsDomain R]
  [CommRing A] [IsDedekindDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]
  [Field F] [Algebra A F] [IsFractionRing A F]

/-- Multiplication of two nonzero field elements adds their finite-place
orders.  This non-`WithTop` form is convenient for exact local certificates. -/
theorem finitePlaceOrder_mul_eq_add
    (v : HeightOneSpectrum A) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    finitePlaceOrder v (x * y) =
      finitePlaceOrder v x + finitePlaceOrder v y := by
  have h := finitePlaceOrderTop_mul v x y
  rw [finitePlaceOrderTop_eq_coe v (x * y) (mul_ne_zero hx hy),
    finitePlaceOrderTop_eq_coe v x hx,
    finitePlaceOrderTop_eq_coe v y hy] at h
  exact_mod_cast h

/-- Inversion negates finite-place order. -/
theorem finitePlaceOrder_inv_eq_neg'
    (v : HeightOneSpectrum A) (x : F) (hx : x ≠ 0) :
    finitePlaceOrder v x⁻¹ = -finitePlaceOrder v x := by
  have h := finitePlaceOrder_mul_eq_add v x⁻¹ x (inv_ne_zero hx) hx
  rw [inv_mul_cancel₀ hx] at h
  have hone : finitePlaceOrder v (1 : F) = 0 := by
    have htop := finitePlaceOrderTop_one (L := F) v
    rw [finitePlaceOrderTop_eq_coe v 1 one_ne_zero] at htop
    exact_mod_cast htop
  rw [hone] at h
  omega

/-- Negating a nonzero field element does not change its finite-place order. -/
theorem finitePlaceOrder_neg_eq
    (v : HeightOneSpectrum A) (x : F) (hx : x ≠ 0) :
    finitePlaceOrder v (-x) = finitePlaceOrder v x := by
  have hval : (v.valuation F) (-x) = (v.valuation F) x := by simp
  rw [valuation_eq_exp_neg_finitePlaceOrder v (-x) (neg_ne_zero.mpr hx),
    valuation_eq_exp_neg_finitePlaceOrder v x hx] at hval
  exact neg_injective (WithZero.exp_injective hval)

/-- If `s` generates a base height-one prime, then its order at a prime above
it is exactly the ramification index. -/
theorem finitePlaceOrder_algebraMap_uniformizer_eq_ramificationIdx
    (p : HeightOneSpectrum R) (v : HeightOneSpectrum A)
    [v.asIdeal.LiesOver p.asIdeal]
    (s : R) (hs : s ≠ 0) (hspan : p.asIdeal = Ideal.span {s}) :
    finitePlaceOrder v (algebraMap A F (algebraMap R A s)) =
      (v.asIdeal.ramificationIdx R : ℤ) := by
  have hsA : algebraMap R A s ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R A).ne hs
  rw [finitePlaceOrder_algebraMap_eq_multiplicity v _ hsA]
  have hmap : p.asIdeal.map (algebraMap R A) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot p.ne_bot
  rw [show Ideal.span {algebraMap R A s} =
      p.asIdeal.map (algebraMap R A) by
    rw [hspan, Ideal.map_span, Set.image_singleton]]
  exact_mod_cast
    (Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      p.asIdeal v.asIdeal hmap).symm

end ReparameterizedLocalOrder

section PowerBasisDifferent

variable {K L : Type*} [Field K] [Field L]
  [Algebra S K] [Algebra T L] [Algebra K L] [Algebra S L]
  [IsScalarTower S K L] [IsScalarTower S T L]
  [IsDomain S] [IsFractionRing S K] [IsFractionRing T L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegralClosure T S L] [IsIntegrallyClosed S] [IsDedekindDomain T]
  [Module.IsTorsionFree S T]

omit [IsFractionRing T L] in
/-- For an integral power basis generated by a primitive field element, the
trace different is exactly the principal ideal generated by the
minimal-polynomial derivative. -/
theorem differentIdeal_eq_span_powerBasis_minpolyDerivative
    (pb : PowerBasis S T)
    (hprimitive : Algebra.adjoin K {algebraMap T L pb.gen} = ⊤) :
    differentIdeal S T =
      Ideal.span
        {Polynomial.aeval pb.gen
          (Polynomial.derivative (minpoly S pb.gen))} := by
  have h := conductor_mul_differentIdeal S K L pb.gen hprimitive
  simpa [conductor_eq_top_of_powerBasis pb] using h

/-- The power-basis derivative has exact order equal to the different
multiplicity at every finite place. -/
theorem powerBasis_minpolyDerivative_finitePlaceOrder_eq_differentMultiplicity
    (pb : PowerBasis S T)
    (hprimitive : Algebra.adjoin K {algebraMap T L pb.gen} = ⊤)
    (v : HeightOneSpectrum T) :
    finitePlaceOrder v
        (algebraMap T L
          (Polynomial.aeval pb.gen
            (Polynomial.derivative (minpoly S pb.gen)))) =
      (multiplicity v.asIdeal (differentIdeal S T) : ℤ) := by
  rw [finitePlaceOrder_algebraMap_eq_multiplicity v _
    (minpolyDerivative_ne_zero (A := S) (K := K) (L := L) pb.gen)]
  rw [differentIdeal_eq_span_powerBasis_minpolyDerivative pb hprimitive]

/-- In the power-basis case, the minimal-polynomial derivative simultaneously
generates the different, annihilates relative differentials, has exact local
different order, and clears the ambient derivation. -/
theorem exists_powerBasis_differentGenerator_scaled_ambientDerivation_preserves
    (pb : PowerBasis S T)
    (hprimitive : Algebra.adjoin K {algebraMap T L pb.gen} = ⊤)
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s)) :
    ∃ c : T,
      c ≠ 0 ∧
      Ideal.span {c} = differentIdeal S T ∧
      c ∈ kaehlerDifferentialAnnihilator S T ∧
      (∀ v : HeightOneSpectrum T,
        finitePlaceOrder v (algebraMap T L c) =
          (multiplicity v.asIdeal (differentIdeal S T) : ℤ)) ∧
      ∀ t : T, ∃ t' : T,
        algebraMap T U c * E (algebraMap T U t) = algebraMap T U t' := by
  let c : T := Polynomial.aeval pb.gen
    (Polynomial.derivative (minpoly S pb.gen))
  refine ⟨c,
    minpolyDerivative_ne_zero (A := S) (K := K) (L := L) pb.gen,
    ?_, powerBasis_minpolyDerivative_mem_kaehlerDifferentialAnnihilator pb,
    ?_, ?_⟩
  · exact (differentIdeal_eq_span_powerBasis_minpolyDerivative
      pb hprimitive).symm
  · exact fun v =>
      powerBasis_minpolyDerivative_finitePlaceOrder_eq_differentMultiplicity
        pb hprimitive v
  · exact powerBasis_minpolyDerivative_scaled_ambientDerivation_preserves
      pb D E hE

/-- Placewise finite certificate extracted from an integral power basis: one
nonzero scalar has exactly the local different order and makes the ambient
derivation preserve the local Dedekind ring. -/
theorem exists_powerBasis_finitePlace_different_scaling_certificate
    (pb : PowerBasis S T)
    (hprimitive : Algebra.adjoin K {algebraMap T L pb.gen} = ⊤)
    (v : HeightOneSpectrum T)
    (D : Derivation C S S) (E : Derivation C U U)
    (hE : ∀ s : S, E (algebraMap S U s) = algebraMap S U (D s)) :
    ∃ c : T,
      c ≠ 0 ∧
      finitePlaceOrder v (algebraMap T L c) =
        (multiplicity v.asIdeal (differentIdeal S T) : ℤ) ∧
      ∀ t : T, ∃ t' : T,
        algebraMap T U c * E (algebraMap T U t) = algebraMap T U t' := by
  obtain ⟨c, hc, _hspan, _hcann, horder, hpreserves⟩ :=
    exists_powerBasis_differentGenerator_scaled_ambientDerivation_preserves
      pb hprimitive D E hE
  exact ⟨c, hc, horder v, hpreserves⟩

/-- Exact change from the local parameter derivation `D_s` to the global
`X`-derivation when `s = X⁻¹`.  If `D_X = -s² D_s`, dividing a different
generator by `-s²` leaves the scaled derivation unchanged and subtracts
`2e` from its local order.  Thus the resulting scalar realizes exactly the
infinity coefficient `different exponent - 2 * ramification index` of the
canonical different divisor. -/
theorem exists_powerBasis_infinity_different_scaling_certificate
    [Algebra C L] [IsScalarTower C S L] [IsScalarTower C T L]
    (pb : PowerBasis S T)
    (hprimitive : Algebra.adjoin K {algebraMap T L pb.gen} = ⊤)
    (p : HeightOneSpectrum S) (v : HeightOneSpectrum T)
    [v.asIdeal.LiesOver p.asIdeal]
    (s : S) (hs : s ≠ 0) (hspan : p.asIdeal = Ideal.span {s})
    (Ds : Derivation C S S) (Es DX : Derivation C L L)
    (hEs : ∀ r : S, Es (algebraMap S L r) = algebraMap S L (Ds r))
    (hDX : DX = (-(algebraMap S L s) ^ 2) • Es) :
    ∃ δ : T,
      δ ≠ 0 ∧
      Ideal.span {δ} = differentIdeal S T ∧
      let c : L := -(algebraMap T L δ) / (algebraMap S L s) ^ 2
      finitePlaceOrder v c =
          (multiplicity v.asIdeal (differentIdeal S T) : ℤ) -
            2 * (v.asIdeal.ramificationIdx S : ℤ) ∧
        ∀ t : T, ∃ t' : T,
          c * DX (algebraMap T L t) = algebraMap T L t' := by
  obtain ⟨δ, hδ, hδspan, _hδann, hδorder, hδpreserves⟩ :=
    exists_powerBasis_differentGenerator_scaled_ambientDerivation_preserves
      (U := L) pb hprimitive Ds Es hEs
  refine ⟨δ, hδ, hδspan, ?_, ?_⟩
  · have hsK : algebraMap S K s ≠ 0 := by
      intro hzero
      exact hs (IsFractionRing.injective S K (by simpa using hzero))
    have hsL : algebraMap S L s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply S K L]
      exact (map_ne_zero (algebraMap K L)).2 hsK
    have hδL : algebraMap T L δ ≠ 0 := by
      intro hzero
      exact hδ (IsFractionRing.injective T L (by simpa using hzero))
    have hsOrder :
        finitePlaceOrder v (algebraMap S L s) =
          (v.asIdeal.ramificationIdx S : ℤ) := by
      simpa only [IsScalarTower.algebraMap_apply S T L] using
        finitePlaceOrder_algebraMap_uniformizer_eq_ramificationIdx
          (F := L) p v s hs hspan
    rw [div_eq_mul_inv,
      finitePlaceOrder_mul_eq_add v
        (-(algebraMap T L δ)) (((algebraMap S L s) ^ 2)⁻¹)
        (neg_ne_zero.mpr hδL) (inv_ne_zero (pow_ne_zero 2 hsL)),
      finitePlaceOrder_neg_eq v (algebraMap T L δ) hδL,
      finitePlaceOrder_inv_eq_neg' v ((algebraMap S L s) ^ 2)
        (pow_ne_zero 2 hsL)]
    have hsSquareOrder := finitePlaceOrder_mul_eq_add v
      (algebraMap S L s) (algebraMap S L s) hsL hsL
    rw [← pow_two] at hsSquareOrder
    rw [hδorder v, hsSquareOrder, hsOrder]
    ring
  · intro t
    obtain ⟨t', ht'⟩ := hδpreserves t
    refine ⟨t', ?_⟩
    have hsK : algebraMap S K s ≠ 0 := by
      intro hzero
      exact hs (IsFractionRing.injective S K (by simpa using hzero))
    have hsL : algebraMap S L s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply S K L]
      exact (map_ne_zero (algebraMap K L)).2 hsK
    rw [hDX, Derivation.smul_apply, Algebra.smul_def]
    calc
      (-(algebraMap T L δ) / (algebraMap S L s) ^ 2) *
          (-(algebraMap S L s) ^ 2 * Es (algebraMap T L t)) =
          algebraMap T L δ * Es (algebraMap T L t) := by
            field_simp
      _ = algebraMap T L t' := ht'

end PowerBasisDifferent

end

end BGS.CorvajaZannier
