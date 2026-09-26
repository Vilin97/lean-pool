/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageCurve
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.AbsoluteIrreducibilityBaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic

/-!
# Powered-image relations over the Frobenius constant field

This file proves that the equation of the image of a plane curve under the
coordinate-power map remains irreducible after arbitrary scalar extension.
It then transports that equation to the Frobenius constant field and applies
the relation criterion to obtain the auxiliary-family linear independence
used in the Corvaja--Zannier Wronskian argument.
-/

@[expose] public section

open scoped TensorProduct Polynomial

namespace BGS.CorvajaZannier

open Polynomial

noncomputable section

variable {K A B : Type*} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

noncomputable def bivariateEvalAlgHom (u v : A) :
    Polynomial (Polynomial K) →ₐ[K] A :=
  Polynomial.eval₂AlgHom (Polynomial.aeval u) v (fun _ ↦ Commute.all _ _)

theorem bivariateEvalAlgHom_comp (F : A →ₐ[K] B) (u v : A) :
    F.comp (bivariateEvalAlgHom (K := K) u v) =
      bivariateEvalAlgHom (K := K) (F u) (F v) := by
  apply AlgHom.ext
  intro P
  have hr :
      (F.comp (bivariateEvalAlgHom (K := K) u v)).toRingHom =
        (bivariateEvalAlgHom (K := K) (F u) (F v)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro q
      change F (bivariateEvalAlgHom (K := K) u v (Polynomial.C q)) =
        bivariateEvalAlgHom (K := K) (F u) (F v) (Polynomial.C q)
      simp only [bivariateEvalAlgHom, Polynomial.eval₂AlgHom_apply,
        Polynomial.eval₂_C]
      induction q using Polynomial.induction_on' with
      | add q r hq hr =>
          simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hq hr
      | monomial j c => simp
    · simp [bivariateEvalAlgHom]
  exact DFunLike.congr_fun hr P

theorem bivariateQuotientEvalEmbedding
    (u v : A) (g : Polynomial (Polynomial K))
    (hzero : bivariateEvalAlgHom u v g = 0)
    (hdiv : ∀ P, bivariateEvalAlgHom u v P = 0 → g ∣ P) :
    ∃ F : (Polynomial (Polynomial K) ⧸ Ideal.span {g}) →ₐ[K] A,
      Function.Injective F := by
  let φ : Polynomial (Polynomial K) →ₐ[K] A :=
    bivariateEvalAlgHom (K := K) u v
  have hspan : ∀ a, a ∈ Ideal.span {g} → φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [φ, hzero]
  let F : (Polynomial (Polynomial K) ⧸ Ideal.span {g}) →ₐ[K] A :=
    Ideal.Quotient.liftₐ (Ideal.span {g}) φ hspan
  refine ⟨F, ?_⟩
  exact RingHom.lift_injective_of_ker_le_ideal (Ideal.span {g}) hspan (by
    intro a ha
    rw [RingHom.mem_ker] at ha
    exact Ideal.mem_span_singleton.mpr (hdiv a (by simpa [φ] using ha)))

variable {L : Type*} [Field L] [Algebra K L]

@[simp]
theorem bivariateEvalAlgHom_eq_evalBivariate (u v : L)
    (P : Polynomial (Polynomial K)) :
    bivariateEvalAlgHom (K := K) u v P = evalBivariate u v P := by
  rfl

theorem primitiveClearedMinpolyRelation_dvd_of_evalBivariate_eq_zero
    (u : L) (hu : Transcendental K u) (v : L)
    (hv : IsIntegral (IntermediateField.adjoin K {u}) v)
    (P : Polynomial (Polynomial K))
    (hP : evalBivariate u v P = 0) :
    primitiveClearedMinpolyRelation u hu v ∣ P := by
  let := Classical.arbitrary (NormalizedGCDMonoid K)
  let e := RatFunc.algEquivOfTranscendental u hu
  let P_rat : Polynomial (RatFunc K) :=
    P.map (algebraMap (Polynomial K) (RatFunc K))
  let P_adjoin : Polynomial (IntermediateField.adjoin K {u}) :=
    P_rat.map e.toRingEquiv
  have hroot_rat :
      Polynomial.eval₂ (ratFuncSpecialization u hu) v P_rat = 0 := by
    simpa only [P_rat, ← evalBivariate_eq_eval₂_ratFuncSpecialization_map]
      using hP
  have hroot_adjoin : Polynomial.aeval v P_adjoin = 0 := by
    rw [Polynomial.aeval_def]
    change Polynomial.eval₂ (algebraMap (IntermediateField.adjoin K {u}) L) v
      (P_rat.map e.toRingEquiv.toRingHom) = 0
    rw [Polynomial.eval₂_map]
    have hcoeff :
        (algebraMap (IntermediateField.adjoin K {u}) L).comp
            e.toRingEquiv.toRingHom = ratFuncSpecialization u hu := by
      rfl
    rw [hcoeff]
    exact hroot_rat
  obtain ⟨R, hR⟩ := minpoly.dvd (IntermediateField.adjoin K {u}) v hroot_adjoin
  have hq_dvd : ratFuncMinpoly u hu v ∣ P_rat := by
    refine ⟨R.map e.symm.toRingEquiv.toRingHom, ?_⟩
    have hmapped := congrArg
      (fun Q : Polynomial (IntermediateField.adjoin K {u}) ↦
        Q.map e.symm.toRingEquiv.toRingHom) hR
    have hcomp :
        e.symm.toRingEquiv.toRingHom.comp
            (e.toRingEquiv.toRingHom.comp
              (algebraMap (Polynomial K) (RatFunc K))) =
          algebraMap (Polynomial K) (RatFunc K) := by
      apply DFunLike.ext _ _
      intro z
      exact e.symm_apply_apply _
    simp only [P_adjoin, P_rat, Polynomial.map_mul, Polynomial.map_map] at hmapped
    change Polynomial.map
        (e.symm.toRingEquiv.toRingHom.comp
          (e.toRingEquiv.toRingHom.comp
            (algebraMap (Polynomial K) (RatFunc K)))) P =
      Polynomial.map e.symm.toRingEquiv.toRingHom
          (minpoly (IntermediateField.adjoin K {u}) v) *
        Polynomial.map e.symm.toRingEquiv.toRingHom R at hmapped
    rw [hcomp] at hmapped
    have hmin : ratFuncMinpoly u hu v =
        Polynomial.map e.symm.toRingEquiv.toRingHom
          (minpoly (IntermediateField.adjoin K {u}) v) := by
      rfl
    rw [hmin]
    exact hmapped
  obtain ⟨c, hc, hgmap⟩ :=
    map_primitiveClearedMinpolyRelation_eq_C_mul u hu v hv
  obtain ⟨R, hR⟩ := hq_dvd
  have hgmap_dvd :
      (primitiveClearedMinpolyRelation u hu v).map
          (algebraMap (Polynomial K) (RatFunc K)) ∣ P_rat := by
    refine ⟨Polynomial.C c⁻¹ * R, ?_⟩
    rw [hgmap]
    calc
      P_rat = ratFuncMinpoly u hu v * R := hR
      _ = (Polynomial.C c * ratFuncMinpoly u hu v) *
          (Polynomial.C c⁻¹ * R) := by
        rw [mul_mul_mul_comm, ← Polynomial.C_mul, mul_inv_cancel₀ hc,
          Polynomial.C_1, one_mul]
  exact (integerClearedMinpoly u hu v).isPrimitive_primPart
    |>.dvd_of_fraction_map_dvd_fraction_map hgmap_dvd

theorem poweredCoordinateImageRelation_quotient_embeds_source
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    let g := poweredCoordinateImageRelation hf hpartialSecond m hm n
    ∃ F : (Polynomial (Polynomial K) ⧸ Ideal.span {g}) →ₐ[K]
        PlaneCurveCoordinateRing f,
      Function.Injective F := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let A := PlaneCurveCoordinateRing f
  let xA : A := (planeCurveCoordinate f 0) ^ m
  let yA : A := (planeCurveCoordinate f 1) ^ n
  let xL : L := (planeCurveFunction f 0) ^ m
  let yL : L := (planeCurveFunction f 1) ^ n
  let ι : A →ₐ[K] L := IsScalarTower.toAlgHom K A L
  let φA : Polynomial (Polynomial K) →ₐ[K] A :=
    bivariateEvalAlgHom (K := K) xA yA
  let φL : Polynomial (Polynomial K) →ₐ[K] L :=
    bivariateEvalAlgHom (K := K) xL yL
  have hcomp : ι.comp φA = φL := by
    simpa [φA, φL, xA, xL, yA, yL, ι, planeCurveFunction] using
      (bivariateEvalAlgHom_comp (K := K) ι xA yA)
  let : FiniteDimensional (FirstPoweredCoordinateSubfield f m) L :=
    finiteDimensional_over_firstPoweredCoordinate hf hpartialSecond m hm
  have hv : IsIntegral (FirstPoweredCoordinateSubfield f m) yL :=
    IsIntegral.of_finite _ _
  let g := poweredCoordinateImageRelation hf hpartialSecond m hm n
  have hzeroL : φL g = 0 := by
    simpa [φL, xL, yL, g] using
      (evalBivariate_poweredCoordinateImageRelation_eq_zero
        hf hpartialSecond m hm n)
  have hι : Function.Injective ι := by
    exact IsFractionRing.injective A L
  have hzeroA : φA g = 0 := by
    apply hι
    rw [map_zero, ← AlgHom.comp_apply, hcomp]
    exact hzeroL
  apply bivariateQuotientEvalEmbedding xA yA g hzeroA
  intro P hP
  change primitiveClearedMinpolyRelation xL
      (firstPoweredCoordinate_transcendental hf hpartialSecond m hm) yL ∣ P
  apply primitiveClearedMinpolyRelation_dvd_of_evalBivariate_eq_zero
      xL (firstPoweredCoordinate_transcendental hf hpartialSecond m hm) yL hv
  change φL P = 0
  rw [← hcomp, AlgHom.comp_apply, hP, map_zero]

noncomputable def iteratedPolynomialBaseChangeEquiv
    (E : Type*) [Field E] [Algebra K E] :
    E ⊗[K] Polynomial (Polynomial K) ≃ₐ[E]
      Polynomial (Polynomial E) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E)
      (Polynomial.Bivariate.equivMvPolynomial K)).trans
    ((MvPolynomial.algebraTensorAlgEquiv K E).trans
      (Polynomial.Bivariate.equivMvPolynomial E).symm)

theorem bivariateEquiv_map_commutes
    (E : Type*) [Field E] [Algebra K E]
    (g : Polynomial (Polynomial K)) :
    (Polynomial.Bivariate.equivMvPolynomial E).symm
        (MvPolynomial.map (algebraMap K E)
          (Polynomial.Bivariate.equivMvPolynomial K g)) =
      g.map (Polynomial.mapRingHom (algebraMap K E)) := by
  let lhs : Polynomial (Polynomial K) →+* Polynomial (Polynomial E) :=
    (Polynomial.Bivariate.equivMvPolynomial E).symm.toRingEquiv.toRingHom.comp
      ((MvPolynomial.map (algebraMap K E)).comp
        (Polynomial.Bivariate.equivMvPolynomial K).toRingEquiv.toRingHom)
  let rhs : Polynomial (Polynomial K) →+* Polynomial (Polynomial E) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap K E))
  change lhs g = rhs g
  congr 1
  apply Polynomial.ringHom_ext
  · intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simp only [map_add, hq, hr]
    | monomial n c =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp [lhs, rhs]
  · simp [lhs, rhs]

theorem iteratedPolynomialBaseChangeEquiv_tmul_one
    (E : Type*) [Field E] [Algebra K E]
    (g : Polynomial (Polynomial K)) :
    iteratedPolynomialBaseChangeEquiv (K := K) E (1 ⊗ₜ[K] g) =
      g.map (Polynomial.mapRingHom (algebraMap K E)) := by
  change (Polynomial.Bivariate.equivMvPolynomial E).symm
      ((MvPolynomial.algebraTensorAlgEquiv K E)
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E)
          (Polynomial.Bivariate.equivMvPolynomial K)) (1 ⊗ₜ[K] g))) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    MvPolynomial.algebraTensorAlgEquiv_tmul]
  change (Polynomial.Bivariate.equivMvPolynomial E).symm
      ((1 : E) • MvPolynomial.map (algebraMap K E)
        (Polynomial.Bivariate.equivMvPolynomial K g)) = _
  rw [one_smul]
  exact bivariateEquiv_map_commutes E g

noncomputable def bivariateQuotientEquivMvPolynomial
    (g : Polynomial (Polynomial K)) :
    (Polynomial (Polynomial K) ⧸ Ideal.span {g}) ≃ₐ[K]
      PlaneCurveCoordinateRing
        (Polynomial.Bivariate.equivMvPolynomial K g) := by
  apply Ideal.quotientEquivAlg
    (Ideal.span {g})
    (Ideal.span {Polynomial.Bivariate.equivMvPolynomial K g})
    (Polynomial.Bivariate.equivMvPolynomial K)
  simp only [Ideal.map_span, Set.image_singleton]
  rfl

theorem tensorProduct_map_id_injective
    (E : Type*) [Field E] [Algebra K E]
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (F : A →ₐ[K] B) (hF : Function.Injective F) :
    Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id E E) F) := by
  have heq :
      (Algebra.TensorProduct.map (AlgHom.id E E) F).toLinearMap.restrictScalars K =
        F.toLinearMap.lTensor E := by
    ext e a
    simp
  rw [← heq] at *
  exact Module.Flat.lTensor_preserves_injective_linearMap F.toLinearMap hF

theorem tensorProduct_isDomain_of_embedding
    (E : Type*) [Field E] [Algebra K E]
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (F : A →ₐ[K] B) (hF : Function.Injective F)
    (hdom : IsDomain (E ⊗[K] B)) :
    IsDomain (E ⊗[K] A) := by
  let Φ := Algebra.TensorProduct.map (AlgHom.id E E) F
  have hΦ : Function.Injective Φ :=
    tensorProduct_map_id_injective E F hF
  let : IsDomain (E ⊗[K] B) := hdom
  apply (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr
  constructor
  · exact hΦ.noZeroDivisors Φ (map_zero Φ) (map_mul Φ)
  · exact domain_nontrivial Φ (map_zero Φ) (map_one Φ)

noncomputable def planeCurveCoordinateRingBaseChangeEquiv
    (E : Type*) [Field E] [Algebra K E]
    (f : MvPolynomial (Fin 2) K) :
    E ⊗[K] PlaneCurveCoordinateRing f ≃+*
      PlaneCurveCoordinateRing
        (MvPolynomial.map (algebraMap K E) f) := by
  let P := MvPolynomial (Fin 2) K
  let PE := MvPolynomial (Fin 2) E
  let I : Ideal P := Ideal.span {f}
  let eP : E ⊗[K] P ≃ₐ[E] PE :=
    MvPolynomial.algebraTensorAlgEquiv K E
  let IT : Ideal (E ⊗[K] P) :=
    I.map (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := P))
  let IE : Ideal PE :=
    Ideal.span {MvPolynomial.map (algebraMap K E) f}
  have hideal : IE = IT.map eP.toRingEquiv.toRingHom := by
    simp only [IE, IT, I, Ideal.map_span, Set.image_singleton]
    congr 2
    symm
    change (MvPolynomial.algebraTensorAlgEquiv K E)
      (1 ⊗ₜ[K] f) = MvPolynomial.map (algebraMap K E) f
    simpa only [one_smul] using
      (MvPolynomial.algebraTensorAlgEquiv_tmul
        (R := K) (A := E) (a := (1 : E)) f)
  exact
    (Algebra.TensorProduct.tensorQuotientEquiv
        (R := K) E P E I).toRingEquiv.trans
      (Ideal.quotientEquiv IT IE eP.toRingEquiv hideal)

theorem planeCurveCoordinateRingBaseChange_isDomain
    (E : Type*) [Field E] [Algebra K E]
    (f : MvPolynomial (Fin 2) K)
    (hfE : Irreducible (MvPolynomial.map (algebraMap K E) f)) :
    IsDomain (E ⊗[K] PlaneCurveCoordinateRing f) := by
  let : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) f)) :=
    planeCurveCoordinateRing_isDomain hfE
  exact (planeCurveCoordinateRingBaseChangeEquiv E f).toMulEquiv.isDomain_iff.mpr
    inferInstance

theorem irreducible_mvPolynomial_map_of_tensorQuotient_isDomain
    (E : Type*) [Field E] [Algebra K E]
    (G : MvPolynomial (Fin 2) K) (hG : Irreducible G)
    (hdom : IsDomain
      (E ⊗[K] PlaneCurveCoordinateRing G)) :
    Irreducible (MvPolynomial.map (algebraMap K E) G) := by
  let : IsDomain (E ⊗[K] PlaneCurveCoordinateRing G) := hdom
  let e := planeCurveCoordinateRingBaseChangeEquiv E G
  let : IsDomain (PlaneCurveCoordinateRing
      (MvPolynomial.map (algebraMap K E) G)) := by
    have hsource := (isDomain_iff_noZeroDivisors_and_nontrivial
      (E ⊗[K] PlaneCurveCoordinateRing G)).mp hdom
    let : NoZeroDivisors (E ⊗[K] PlaneCurveCoordinateRing G) := hsource.1
    let : Nontrivial (E ⊗[K] PlaneCurveCoordinateRing G) := hsource.2
    apply (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr
    constructor
    · exact e.symm.injective.noZeroDivisors e.symm
        (map_zero e.symm) (map_mul e.symm)
    · exact e.symm.surjective.nontrivial
  have hmap_ne : MvPolynomial.map (algebraMap K E) G ≠ 0 := by
    intro hzero
    apply hG.ne_zero
    exact MvPolynomial.map_injective (algebraMap K E)
      (algebraMap K E).injective (by simpa using hzero)
  have hprime :
      (Ideal.span {MvPolynomial.map (algebraMap K E) G} :
        Ideal (MvPolynomial (Fin 2) E)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  exact ((Ideal.span_singleton_prime hmap_ne).mp hprime).irreducible

theorem poweredCoordinateImageRelation_irreducible_map
    {E : Type*} [Field E] [Algebra K E]
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Irreducible
      ((poweredCoordinateImageRelation hf hpartialSecond m hm n).map
        (Polynomial.mapRingHom (algebraMap K E))) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let g := poweredCoordinateImageRelation hf hpartialSecond m hm n
  let G := Polynomial.Bivariate.equivMvPolynomial K g
  have hg : Irreducible g :=
    poweredCoordinateImageRelation_irreducible
      hf hpartialSecond m hm n
  have hG : Irreducible G :=
    hg.map (Polynomial.Bivariate.equivMvPolynomial K).toMulEquiv
  obtain ⟨F, hF⟩ :=
    poweredCoordinateImageRelation_quotient_embeds_source
      hf hpartialSecond m hm n
  let eQ := bivariateQuotientEquivMvPolynomial g
  let FMv : PlaneCurveCoordinateRing G →ₐ[K]
      PlaneCurveCoordinateRing f := F.comp eQ.symm.toAlgHom
  have hFMv : Function.Injective FMv := hF.comp eQ.symm.injective
  have hfE : Irreducible (MvPolynomial.map (algebraMap K E) f) :=
    irreducible_map_of_irreducible_map_algebraicClosure
      (algebraMap K E) f habsolute
  have htarget : IsDomain (E ⊗[K] PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRingBaseChange_isDomain E f hfE
  have hsource : IsDomain (E ⊗[K] PlaneCurveCoordinateRing G) :=
    tensorProduct_isDomain_of_embedding E FMv hFMv htarget
  have hGE : Irreducible (MvPolynomial.map (algebraMap K E) G) :=
    irreducible_mvPolynomial_map_of_tensorQuotient_isDomain
      E G hG hsource
  have hback := hGE.map
    (Polynomial.Bivariate.equivMvPolynomial E).symm.toMulEquiv
  change Irreducible
    ((Polynomial.Bivariate.equivMvPolynomial E).symm
      (MvPolynomial.map (algebraMap K E)
        (Polynomial.Bivariate.equivMvPolynomial K g))) at hback
  rw [bivariateEquiv_map_commutes E g] at hback
  exact hback

theorem transposeBivariate_map
    {E : Type*} [Field E] (i : K →+* E)
    (P : Polynomial (Polynomial K)) :
    transposeBivariate
        (P.map (Polynomial.mapRingHom i)) =
      (transposeBivariate P).map (Polynomial.mapRingHom i) := by
  let lhs : Polynomial (Polynomial K) →+* Polynomial (Polynomial E) :=
    transposeBivariate.comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom i))
  let rhs : Polynomial (Polynomial K) →+* Polynomial (Polynomial E) :=
    (Polynomial.mapRingHom (Polynomial.mapRingHom i)).comp transposeBivariate
  change lhs P = rhs P
  congr 1
  apply Polynomial.ringHom_ext
  · intro q
    simp only [lhs, rhs, RingHom.comp_apply, transposeBivariate_C]
    ext c
    simp
  · simp [lhs, rhs, transposeBivariate]

theorem evalBivariate_map_mapRingHom
    {E : Type*} [Field E] [Algebra K E]
    {L : Type*} [Field L] [Algebra K L] [Algebra E L]
    [IsScalarTower K E L]
    (u v : L) (P : Polynomial (Polynomial K)) :
    evalBivariate u v
        (P.map (Polynomial.mapRingHom (algebraMap K E))) =
      evalBivariate u v P := by
  unfold evalBivariate
  rw [Polynomial.eval₂_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro c
    simp [IsScalarTower.algebraMap_apply K E L]
  · simp

variable {p : ℕ} [Fact p.Prime] [CharP K p] [PerfectField K]

noncomputable def poweredCoordinateFrobeniusImageRelation
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    Polynomial (Polynomial
      (frobeniusSubfield (PlaneCurveFunctionField f) p)) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  letI : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let ι : K →+* frobeniusSubfield L p :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)
  exact transposeBivariate
    ((poweredCoordinateImageRelation hf hpartialSecond m hm n).map
      (Polynomial.mapRingHom ι))

theorem poweredCoordinateFrobeniusImageRelation_natDegree
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    (poweredCoordinateFrobeniusImageRelation
        (p := p) hf hpartialSecond m hm n).natDegree =
      (transposeBivariate
        (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let ι : K →+* F :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)
  have hι : Function.Injective ι :=
    perfectConstantsToFrobeniusSubfield_injective
      (K := K) (L := L) (p := p)
  have hmap : Function.Injective (Polynomial.mapRingHom ι) :=
    Polynomial.map_injective ι hι
  change (transposeBivariate
      ((poweredCoordinateImageRelation hf hpartialSecond m hm n).map
        (Polynomial.mapRingHom ι))).natDegree = _
  rw [transposeBivariate_map]
  exact Polynomial.natDegree_map_eq_of_injective hmap _

theorem transposeBivariate_poweredCoordinateFrobeniusImageRelation_natDegree
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    (transposeBivariate
      (poweredCoordinateFrobeniusImageRelation
        (p := p) hf hpartialSecond m hm n)).natDegree =
      (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let ι : K →+* F :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)
  have hι : Function.Injective ι :=
    perfectConstantsToFrobeniusSubfield_injective
      (K := K) (L := L) (p := p)
  have hmap : Function.Injective (Polynomial.mapRingHom ι) :=
    Polynomial.map_injective ι hι
  change (transposeBivariate (transposeBivariate
      ((poweredCoordinateImageRelation hf hpartialSecond m hm n).map
        (Polynomial.mapRingHom ι)))).natDegree = _
  rw [transposeBivariate_transposeBivariate]
  exact Polynomial.natDegree_map_eq_of_injective hmap _

theorem evalBivariate_poweredCoordinateFrobeniusImageRelation_eq_zero
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    evalBivariate
      ((planeCurveFunction f 1) ^ n)
      ((planeCurveFunction f 0) ^ m)
      (poweredCoordinateFrobeniusImageRelation
        (p := p) hf hpartialSecond m hm n) = 0 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let ι : K →+* F :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)
  let : Algebra K F := ι.toAlgebra
  let : IsScalarTower K F L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    exact (coe_perfectConstantsToFrobeniusSubfield
      (K := K) (L := L) (p := p) c).symm
  change evalBivariate
    ((planeCurveFunction f 1) ^ n)
    ((planeCurveFunction f 0) ^ m)
    (transposeBivariate
      ((poweredCoordinateImageRelation hf hpartialSecond m hm n).map
        (Polynomial.mapRingHom (algebraMap K F)))) = 0
  rw [evalBivariate_transposeBivariate, evalBivariate_map_mapRingHom]
  exact evalBivariate_poweredCoordinateImageRelation_eq_zero
    hf hpartialSecond m hm n

theorem poweredCoordinateFrobeniusImageRelation_irreducible
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    Irreducible
      (poweredCoordinateFrobeniusImageRelation
        (p := p) hf hpartialSecond m hm n) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let ι : K →+* F :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)
  have hbase : Irreducible
      ((poweredCoordinateImageRelation hf hpartialSecond m hm n).map
        (Polynomial.mapRingHom ι)) := by
    let : Algebra K F := ι.toAlgebra
    exact poweredCoordinateImageRelation_irreducible_map
      (E := F) habsolute hf hpartialSecond m hm n
  exact irreducible_transposeBivariate hbase

theorem poweredCoordinateFrobeniusImage_auxiliaryFamily_linearIndependent
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : ¬ p ∣ n)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k)
    (hsize :
      letI := planeCurveCoordinateRing_isDomain hf
      letI : CharP (PlaneCurveFunctionField f) p :=
        charP_of_injective_algebraMap
          (algebraMap K (PlaneCurveFunctionField f)).injective p
      let g := poweredCoordinateFrobeniusImageRelation
        (p := p) hf hpartialSecond m hm n
      g.natDegree * h + (transposeBivariate g).natDegree * k < p)
    (hexcluded :
      letI := planeCurveCoordinateRing_isDomain hf
      letI : CharP (PlaneCurveFunctionField f) p :=
        charP_of_injective_algebraMap
          (algebraMap K (PlaneCurveFunctionField f)).injective p
      let g := poweredCoordinateFrobeniusImageRelation
        (p := p) hf hpartialSecond m hm n
      ¬ (g.natDegree ≤ k ∧ (transposeBivariate g).natDegree ≤ h)) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    LinearIndependent
      (frobeniusSubfield (PlaneCurveFunctionField f) p)
      (auxiliaryFamily ((planeCurveFunction f 0) ^ m)
        ((planeCurveFunction f 1) ^ n) h k) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let ι : K →+* F :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)
  let : Algebra K F := ι.toAlgebra
  let : IsScalarTower K F L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    exact (coe_perfectConstantsToFrobeniusSubfield
      (K := K) (L := L) (p := p) c).symm
  let gK := poweredCoordinateImageRelation hf hpartialSecond m hm n
  let gBase : Polynomial (Polynomial F) :=
    gK.map (Polynomial.mapRingHom ι)
  let g : Polynomial (Polynomial F) := transposeBivariate gBase
  have hι : Function.Injective ι :=
    perfectConstantsToFrobeniusSubfield_injective
      (K := K) (L := L) (p := p)
  have hmap : Function.Injective (Polynomial.mapRingHom ι) :=
    Polynomial.map_injective ι hι
  have hg : Irreducible g := by
    exact poweredCoordinateFrobeniusImageRelation_irreducible
      (p := p) habsolute hf hpartialSecond m hm n
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hn
    simp [hn0]
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn0
  have hdegreeG : g.natDegree =
      (transposeBivariate gK).natDegree := by
    dsimp [g, gBase]
    rw [transposeBivariate_map]
    exact Polynomial.natDegree_map_eq_of_injective hmap _
  have ha : 0 < g.natDegree := by
    rw [hdegreeG]
    exact poweredCoordinateImageRelation_transpose_natDegree_pos
      hf hpartialFirst hpartialSecond m hm n hnPos
  have hdegreeTranspose : (transposeBivariate g).natDegree = gK.natDegree := by
    dsimp [g]
    rw [transposeBivariate_transposeBivariate]
    dsimp [gBase]
    exact Polynomial.natDegree_map_eq_of_injective hmap _
  have hb : 0 < (transposeBivariate g).natDegree := by
    rw [hdegreeTranspose]
    exact poweredCoordinateImageRelation_natDegree_pos
      hf hpartialSecond m hm n
  have hcoeff : ∀ i, (g.coeff i).natDegree ≤
      (transposeBivariate g).natDegree := by
    intro i
    have hcoeffBase := transposeBivariate_coeff_natDegree_le gBase
      gBase.natDegree le_rfl i
    simpa only [g, transposeBivariate_transposeBivariate] using hcoeffBase
  have hzeroBase : evalBivariate
      ((planeCurveFunction f 0) ^ m)
      ((planeCurveFunction f 1) ^ n) gBase = 0 := by
    dsimp [gBase]
    change evalBivariate
      ((planeCurveFunction f 0) ^ m)
      ((planeCurveFunction f 1) ^ n)
      (gK.map (Polynomial.mapRingHom (algebraMap K F))) = 0
    rw [evalBivariate_map_mapRingHom]
    exact evalBivariate_poweredCoordinateImageRelation_eq_zero
      hf hpartialSecond m hm n
  have hzero : evalBivariate
      ((planeCurveFunction f 1) ^ n)
      ((planeCurveFunction f 0) ^ m) g = 0 := by
    dsimp [g]
    rw [evalBivariate_transposeBivariate]
    exact hzeroBase
  exact poweredCoordinates_auxiliaryFamily_linearIndependent_of_relation
    hf hpartialFirst m n hn g g.natDegree
      (transposeBivariate g).natDegree h k ha hh hk hg rfl rfl
      hcoeff hzero hsize hexcluded

end

end BGS.CorvajaZannier
