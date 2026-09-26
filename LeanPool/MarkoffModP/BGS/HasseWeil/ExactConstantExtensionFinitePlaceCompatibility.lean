/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionFinitePlaceBridge
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFinitePlace
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZeroCounting

/-!
# Compatibility of the two finite-place models in a constant extension

The explicit constant-extension normalization is naturally a normalization
over `S[X]`, whereas the relative Galois action is implemented on the
normalization over `C[X]`.  This file identifies the corresponding finite
places and their residue fields.  In particular, an `S`-rational place has
absolute `C`-degree `[S : C]`, in precisely the model used by the
decomposition-group theorem.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


/-- The equality-transport normalization equivalence does not change the
underlying element of the ambient function field. -/
private theorem integralClosureAlgEquivRatFuncFiniteOfEq_coe
    {k T : Type*} [Field k] [Field T] [Algebra (RatFunc k) T]
    (a : Algebra k[X] T)
    (h : ratFuncInducedPolynomialAlgebra k T = a)
    (x : letI := a; integralClosure k[X] T) :
    letI := a
    (((integralClosureAlgEquivRatFuncFiniteOfEq k T a h) x :
        RatFuncFiniteIntegralClosure k T) : T) = x := by
  subst a
  rfl

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance compatibilityBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance compatibilityBasePolynomialAlgebra : Algebra C[X] N :=
  bridgeBasePolynomialAlgebra C N

local instance compatibilityBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance compatibilityBaseConstantPolynomialTower :
    IsScalarTower C C[X] N :=
  bridgeBaseConstantPolynomialTower C N

local instance compatibilityPolynomialCoefficientAlgebra :
    Algebra C[X] S[X] :=
  (Polynomial.mapRingHom (algebraMap C S)).toAlgebra

local instance compatibilityRatFuncCoefficientAlgebra :
    Algebra (RatFunc C) (RatFunc S) :=
  ratFuncCoefficientAlgebra C S

local instance compatibilityTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

local instance compatibilityTensorNormalizationPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
  bridgeTensorNormalizationPolynomialAlgebra C S N

local instance compatibilityOldNormalizationConstantAlgebra :
    Algebra C (integralClosure C[X] N) :=
  RingHom.toAlgebra
    ((algebraMap C[X] (integralClosure C[X] N)).comp
      (algebraMap C C[X]))

omit [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N]
  [FiniteDimensional C S] [IsGalois C S] in
/-- The two normalization equivalences used by the residue and polynomial
models have the same underlying map. -/
private theorem finiteFieldConstantExtensionIntegralClosureAlgEquiv_apply_eq_polynomial
    (z : S ⊗[C] integralClosure C[X] N) :
    finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N z =
      finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv C S N z := by
  induction z using TensorProduct.inductionOn with
  | tmul s a =>
      apply Subtype.ext
      rw [finiteFieldConstantExtensionIntegralClosureAlgEquiv_tmul,
        finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv_tmul]
  | add x y hx hy =>
      calc
        finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N (x + y) =
            finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N x +
              finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N y :=
          (finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N).map_add x y
        _ = finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv C S N x +
              finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv C S N y := by
          rw [hx, hy]
        _ = finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv C S N (x + y) :=
          ((finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv C S N).map_add x y).symm

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

include hExact

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [Algebra.IsSeparable (RatFunc C) N] in
/-- The exact constant extension is finite over the original rational
function field.  This is the finite-dimensional input needed to compare its
`C[X]`- and `S[X]`-normalizations. -/
theorem finiteDimensional_exactConstantExtension_over_baseRatFunc :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    FiniteDimensional (RatFunc C) (ExactConstantExtension C N S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let e := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  let : Module.Finite N (ExactConstantExtension C N S) :=
    Module.Finite.equiv e
  exact Module.Finite.trans N (ExactConstantExtension C N S)

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] in
/-- Polynomial coefficient extension is compatible with the two canonical
rational-function embeddings into the exact constant extension. -/
theorem exactConstantExtension_ratFunc_polynomialCompatibility
    (p : C[X]) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    algebraMap (RatFunc C) (ExactConstantExtension C N S)
          (algebraMap C[X] (RatFunc C) p) =
        algebraMap (RatFunc S) (ExactConstantExtension C N S)
          (algebraMap S[X] (RatFunc S) (algebraMap C[X] S[X] p)) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  rw [rationalBase_algebraMap_eq C S N hExact]
  apply congrArg (algebraMap (RatFunc S) (ExactConstantExtension C N S))
  exact ratFuncCoefficientAlgHom_algebraMap C S p

/-- The finite place over `C` corresponding to a place in the explicit
`S[X]`-normalization.  Extending its constants back to `S` recovers the
finite place constructed in `ConstantExtensionFinitePlaceBridge`. -/
noncomputable def exactConstantExtensionCompatibleBaseFinitePlace
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    FiniteExtensionFinitePlace C (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  exact (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (ratFuncFiniteIntegralClosureRingEquiv C S
        (ExactConstantExtension C N S)
        (exactConstantExtension_ratFunc_polynomialCompatibility
          C S N hExact))).symm
      (exactConstantExtensionUpstairsFinitePlace C S N hExact q)

omit [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N] in
@[simp]
theorem exactConstantExtensionCompatibleBaseFinitePlace_baseChange
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
        (ratFuncFiniteIntegralClosureRingEquiv C S
          (ExactConstantExtension C N S)
          (exactConstantExtension_ratFunc_polynomialCompatibility
            C S N hExact))
        (exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q) =
      exactConstantExtensionUpstairsFinitePlace C S N hExact q := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  exact Equiv.apply_symm_apply _ _

/-- The identity equivalence between the `C[X]`- and `S[X]`-normalizations
is linear over the enlarged constant field. -/
noncomputable def exactConstantExtensionFiniteClosureBaseChangeAlgEquiv :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) :=
      exactConstantExtensionFiniteIntegralClosureConstantAlgebra
        C N S hExact
    letI : Algebra S (RatFuncFiniteIntegralClosure S
        (ExactConstantExtension C N S)) :=
      RingHom.toAlgebra
        ((algebraMap S[X] (RatFuncFiniteIntegralClosure S
          (ExactConstantExtension C N S))).comp (algebraMap S S[X]))
    RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S) ≃ₐ[S]
      RatFuncFiniteIntegralClosure S (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra S (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) :=
    exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
  letI : Algebra S (RatFuncFiniteIntegralClosure S
      (ExactConstantExtension C N S)) :=
    RingHom.toAlgebra
      ((algebraMap S[X] (RatFuncFiniteIntegralClosure S
        (ExactConstantExtension C N S))).comp (algebraMap S S[X]))
  exact { ratFuncFiniteIntegralClosureRingEquiv C S
      (ExactConstantExtension C N S)
      (exactConstantExtension_ratFunc_polynomialCompatibility
        C S N hExact) with
    commutes' := fun s => by
      apply Subtype.ext
      change
        ((algebraMap S (RatFuncFiniteIntegralClosure C
            (ExactConstantExtension C N S)) s :
          RatFuncFiniteIntegralClosure C
            (ExactConstantExtension C N S)) :
              ExactConstantExtension C N S) =
        ((algebraMap S (RatFuncFiniteIntegralClosure S
            (ExactConstantExtension C N S)) s :
          RatFuncFiniteIntegralClosure S
            (ExactConstantExtension C N S)) :
              ExactConstantExtension C N S)
      rw [exactConstantExtensionFiniteIntegralClosure_algebraMap_val]
      change (Algebra.TensorProduct.includeLeft
          (R := C) (S := C) (A := S) (B := N)) s =
        algebraMap (RatFunc S) (ExactConstantExtension C N S)
          (algebraMap S[X] (RatFunc S) (Polynomial.C s))
      change (Algebra.TensorProduct.includeLeft
          (R := C) (S := C) (A := S) (B := N)) s =
        (ratFuncToExactConstantExtension C S N hExact)
          (algebraMap S (RatFunc S) s)
      exact (ratFuncToExactConstantExtension C S N hExact).commutes s |>.symm }

omit [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N] in
/-- The actual upstairs finite place is exactly the transport of the
presented prime along the equality bridge from the compatible polynomial
normalization to the canonical rational-function normalization. -/
theorem exactConstantExtensionUpstairsFinitePlace_eq_compatibleNormalizationTransport
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let e := integralClosureAlgEquivRatFuncFiniteOfAlgebraMap
      S (ExactConstantExtension C N S)
        (constantExtensionTensorPolynomialAlgebra C S N)
        (ratFuncToExactConstantExtension_algebraMap C S N hExact)
    exactConstantExtensionUpstairsFinitePlace C S N hExact q =
      heightOneSpectrumEquivOfAlgEquiv e q := by
  let E := ExactConstantExtension C N S
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let e := integralClosureAlgEquivRatFuncFiniteOfAlgebraMap
    S E (constantExtensionTensorPolynomialAlgebra C S N)
      (ratFuncToExactConstantExtension_algebraMap C S N hExact)
  let eNorm := exactConstantExtensionNormalizationAlgEquiv C S N hExact
  let qTensor := exactConstantExtensionTensorNormalizationHeightOne C S N q
  have hNormalizationToPolynomial
      (z : S ⊗[C] integralClosure C[X] N) :
      ((eNorm z : RatFuncFiniteIntegralClosure S E) : E) =
        ((finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv
          C S N z : integralClosure S[X] E) : E) := by
    simp only [exactConstantExtensionNormalizationAlgEquiv,
      normalizationAlgEquivRatFuncFiniteOfAlgebraMap,
      integralClosureAlgEquivRatFuncFiniteOfAlgebraMap, AlgEquiv.trans_apply, eNorm]
    rw [integralClosureAlgEquivRatFuncFiniteOfEq_coe]
  apply IsDedekindDomain.HeightOneSpectrum.ext
  have hActualIdeal :
      (exactConstantExtensionUpstairsFinitePlace
        C S N hExact q).asIdeal =
        qTensor.asIdeal.comap eNorm.symm := rfl
  have hDirectIdeal :
      (heightOneSpectrumEquivOfAlgEquiv e q).asIdeal =
        q.asIdeal.comap e.symm := rfl
  rw [hActualIdeal, hDirectIdeal]
  rw [show qTensor.asIdeal = q.asIdeal.comap
      (finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N) by rfl]
  ext x
  change finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N
      (eNorm.symm x) ∈ q.asIdeal ↔ e.symm x ∈ q.asIdeal
  rw [show finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N
      (eNorm.symm x) = e.symm x by
    apply Subtype.ext
    calc
      ((finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N
          (eNorm.symm x) : integralClosure S[X] E) : E) =
          ((finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv
            C S N (eNorm.symm x) : integralClosure S[X] E) : E) :=
        congrArg Subtype.val
          (finiteFieldConstantExtensionIntegralClosureAlgEquiv_apply_eq_polynomial
            C S N (eNorm.symm x))
      _ = ((eNorm (eNorm.symm x) : RatFuncFiniteIntegralClosure S E) : E) :=
        (hNormalizationToPolynomial (eNorm.symm x)).symm
      _ = (x : E) := congrArg Subtype.val (eNorm.apply_symm_apply x)
      _ = ((e.symm x : integralClosure S[X] E) : E) := by
        calc
          (x : E) = ((e (e.symm x) : RatFuncFiniteIntegralClosure S E) : E) :=
            congrArg Subtype.val (e.apply_symm_apply x).symm
          _ = ((e.symm x : integralClosure S[X] E) : E) :=
            integralClosureAlgEquivRatFuncFiniteOfEq_coe
              (constantExtensionTensorPolynomialAlgebra C S N)
              (ratFuncInducedPolynomialAlgebra_eq S E
                (constantExtensionTensorPolynomialAlgebra C S N)
                (ratFuncToExactConstantExtension_algebraMap C S N hExact))
              (e.symm x)]

/-- Corresponding finite places have equivalent residue fields as
`S`-algebras, even though the source place is represented in the
`C[X]`-normalization. -/
noncomputable def exactConstantExtensionCompatibleResidueFieldAlgEquiv
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) :=
      exactConstantExtensionFiniteIntegralClosureConstantAlgebra
        C N S hExact
    letI : Algebra S (RatFuncFiniteIntegralClosure S
        (ExactConstantExtension C N S)) :=
      RingHom.toAlgebra
        ((algebraMap S[X] (RatFuncFiniteIntegralClosure S
          (ExactConstantExtension C N S))).comp (algebraMap S S[X]))
    (exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q).asIdeal.ResidueField
        ≃ₐ[S]
      (exactConstantExtensionUpstairsFinitePlace C S N hExact q).asIdeal.ResidueField := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra S (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) :=
    exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
  letI : Algebra S (RatFuncFiniteIntegralClosure S
      (ExactConstantExtension C N S)) :=
    RingHom.toAlgebra
      ((algebraMap S[X] (RatFuncFiniteIntegralClosure S
        (ExactConstantExtension C N S))).comp (algebraMap S S[X]))
  let e := exactConstantExtensionFiniteClosureBaseChangeAlgEquiv
    C S N hExact
  let Q := exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q
  apply Ideal.residueFieldAlgEquiv Q.asIdeal
    (exactConstantExtensionUpstairsFinitePlace C S N hExact q).asIdeal e
  change Q.asIdeal =
    (exactConstantExtensionUpstairsFinitePlace C S N hExact q).asIdeal.comap e
  rfl

omit [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N] in
/-- The two representations of the upstairs place have the same residue
degree over the enlarged constants. -/
theorem exactConstantExtensionCompatibleResidueField_finrank_eq
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) :=
      exactConstantExtensionFiniteIntegralClosureConstantAlgebra
        C N S hExact
    letI : Algebra S (RatFuncFiniteIntegralClosure S
        (ExactConstantExtension C N S)) :=
      RingHom.toAlgebra
        ((algebraMap S[X] (RatFuncFiniteIntegralClosure S
          (ExactConstantExtension C N S))).comp (algebraMap S S[X]))
    Module.finrank S
        (exactConstantExtensionCompatibleBaseFinitePlace
          C S N hExact q).asIdeal.ResidueField =
      Module.finrank S
        (exactConstantExtensionUpstairsFinitePlace
          C S N hExact q).asIdeal.ResidueField :=
  by
    let : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let : Algebra S (RatFuncFiniteIntegralClosure C
        (ExactConstantExtension C N S)) :=
      exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
    let : Algebra S (RatFuncFiniteIntegralClosure S
        (ExactConstantExtension C N S)) :=
      RingHom.toAlgebra
        ((algebraMap S[X] (RatFuncFiniteIntegralClosure S
          (ExactConstantExtension C N S))).comp (algebraMap S S[X]))
    exact (exactConstantExtensionCompatibleResidueFieldAlgEquiv
      C S N hExact q).toLinearEquiv.finrank_eq

/-- An `S`-rational place in the explicit normalization has absolute
`C`-degree `[S : C]` in the finite-place model used by the Galois action. -/
theorem exactConstantExtensionCompatibleBaseFinitePlace_degree_eq
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S)))
    :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : SMul (RatFunc S) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc S) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc S)
        (ExactConstantExtension C N S) :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc S)
        (ExactConstantExtension C N S) :=
      isSeparable_over_extendedRatFunc C S N hExact
    finiteExtensionPlaceDegree S
      (ExactConstantExtension C N S)
        (.inl (exactConstantExtensionUpstairsFinitePlace
          C S N hExact q)) = 1 →
      finiteExtensionPlaceDegree C (ExactConstantExtension C N S)
        (.inl (exactConstantExtensionCompatibleBaseFinitePlace
          C S N hExact q)) = Module.finrank C S := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc S)
      (ExactConstantExtension C N S) :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S)
      (ExactConstantExtension C N S) :=
    isSeparable_over_extendedRatFunc C S N hExact
  intro hRational
  rw [finiteExtensionFinitePlace_degree_baseChange C S
    (ExactConstantExtension C N S)
    (exactConstantExtension_ratFunc_polynomialCompatibility
      C S N hExact)]
  rw [exactConstantExtensionCompatibleBaseFinitePlace_baseChange,
    hRational, Nat.mul_one]

omit [DecidableEq C] [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)] in
/-- Restricting the compatible `C[X]`-place to the original function field
recovers the downstairs place obtained by contracting the explicit constant
extension ideal. -/
theorem exactConstantExtensionCompatibleBaseFinitePlace_under_original
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    finitePlaceUnder C N (ExactConstantExtension C N S)
        (exactConstantExtensionCompatibleBaseFinitePlace
          C S N hExact q) =
      exactConstantExtensionDownstairsFinitePlace C S N hExact q := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext x
  rw [finitePlaceUnder_asIdeal,
    exactConstantExtensionDownstairsFinitePlace_asIdeal]
  change finiteIntegralClosureMap C N (ExactConstantExtension C N S) x ∈
      (exactConstantExtensionCompatibleBaseFinitePlace
        C S N hExact q).asIdeal ↔
    finiteFieldConstantExtensionIntegralClosureRingHom C S N x ∈ q.asIdeal
  let eBase := ratFuncFiniteIntegralClosureRingEquiv C S
    (ExactConstantExtension C N S)
    (exactConstantExtension_ratFunc_polynomialCompatibility C S N hExact)
  let Qs := exactConstantExtensionUpstairsFinitePlace C S N hExact q
  have hBaseIdeal :
      (exactConstantExtensionCompatibleBaseFinitePlace
        C S N hExact q).asIdeal = Qs.asIdeal.comap eBase := rfl
  rw [hBaseIdeal]
  change eBase (finiteIntegralClosureMap C N
      (ExactConstantExtension C N S) x) ∈ Qs.asIdeal ↔
    finiteFieldConstantExtensionIntegralClosureRingHom C S N x ∈ q.asIdeal
  let qTensor := exactConstantExtensionTensorNormalizationHeightOne C S N q
  let eNorm := exactConstantExtensionNormalizationAlgEquiv C S N hExact
  have hTargetIdeal : Qs.asIdeal = qTensor.asIdeal.comap eNorm.symm := rfl
  rw [hTargetIdeal]
  change eNorm.symm (eBase (finiteIntegralClosureMap C N
      (ExactConstantExtension C N S) x)) ∈ qTensor.asIdeal ↔
    finiteFieldConstantExtensionIntegralClosureRingHom C S N x ∈ q.asIdeal
  let eTensor := finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N
  have hTensorIdeal : qTensor.asIdeal = q.asIdeal.comap eTensor := rfl
  rw [hTensorIdeal]
  change eTensor (eNorm.symm (eBase (finiteIntegralClosureMap C N
      (ExactConstantExtension C N S) x))) ∈ q.asIdeal ↔
    finiteFieldConstantExtensionIntegralClosureRingHom C S N x ∈ q.asIdeal
  have hNormalizationToPolynomial
      (z : S ⊗[C] integralClosure C[X] N) :
      ((eNorm z : RatFuncFiniteIntegralClosure S
          (ExactConstantExtension C N S)) :
        ExactConstantExtension C N S) =
        ((finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv
          C S N z : integralClosure S[X]
            (ExactConstantExtension C N S)) :
          ExactConstantExtension C N S) := by
    simp only [exactConstantExtensionNormalizationAlgEquiv,
      normalizationAlgEquivRatFuncFiniteOfAlgebraMap,
      integralClosureAlgEquivRatFuncFiniteOfAlgebraMap, AlgEquiv.trans_apply, eNorm]
    rw [integralClosureAlgEquivRatFuncFiniteOfEq_coe]
  have hNormalizationMapsAgree
      (z : S ⊗[C] integralClosure C[X] N) :
      ((eTensor z : integralClosure S[X] (ExactConstantExtension C N S)) :
          ExactConstantExtension C N S) =
        ((eNorm z : RatFuncFiniteIntegralClosure S
            (ExactConstantExtension C N S)) :
          ExactConstantExtension C N S) := by
    calc
      ((eTensor z : integralClosure S[X]
          (ExactConstantExtension C N S)) :
        ExactConstantExtension C N S) =
          ((finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv
            C S N z : integralClosure S[X]
              (ExactConstantExtension C N S)) :
            ExactConstantExtension C N S) :=
        congrArg Subtype.val
          (finiteFieldConstantExtensionIntegralClosureAlgEquiv_apply_eq_polynomial
            C S N z)
      _ = ((eNorm z : RatFuncFiniteIntegralClosure S
          (ExactConstantExtension C N S)) :
        ExactConstantExtension C N S) := (hNormalizationToPolynomial z).symm
  rw [show eTensor (eNorm.symm (eBase (finiteIntegralClosureMap C N
        (ExactConstantExtension C N S) x))) =
      finiteFieldConstantExtensionIntegralClosureRingHom C S N x by
    apply Subtype.ext
    calc
      ((eTensor (eNorm.symm (eBase (finiteIntegralClosureMap C N
          (ExactConstantExtension C N S) x))) :
          integralClosure S[X] (ExactConstantExtension C N S)) :
            ExactConstantExtension C N S) =
        ((eNorm (eNorm.symm (eBase (finiteIntegralClosureMap C N
          (ExactConstantExtension C N S) x))) :
          RatFuncFiniteIntegralClosure S
            (ExactConstantExtension C N S)) :
              ExactConstantExtension C N S) :=
        hNormalizationMapsAgree _
      _ = ((eBase (finiteIntegralClosureMap C N
          (ExactConstantExtension C N S) x) :
          RatFuncFiniteIntegralClosure S
            (ExactConstantExtension C N S)) :
              ExactConstantExtension C N S) := by
        rw [eNorm.apply_symm_apply]
      _ = ((finiteFieldConstantExtensionIntegralClosureRingHom C S N x :
          integralClosure S[X] (ExactConstantExtension C N S)) :
            ExactConstantExtension C N S) := by
        calc
          ((eBase (finiteIntegralClosureMap C N
              (ExactConstantExtension C N S) x) :
            RatFuncFiniteIntegralClosure S
              (ExactConstantExtension C N S)) :
                ExactConstantExtension C N S) =
              ((finiteIntegralClosureMap C N
                (ExactConstantExtension C N S) x :
                RatFuncFiniteIntegralClosure C
                  (ExactConstantExtension C N S)) :
                    ExactConstantExtension C N S) := by
            rfl
          _ = (1 : S) ⊗ₜ[C] (x : N) := by rfl
          _ = ((finiteFieldConstantExtensionIntegralClosureRingHom C S N x :
              integralClosure S[X] (ExactConstantExtension C N S)) :
                ExactConstantExtension C N S) :=
            (finiteFieldConstantExtensionIntegralClosureRingHom_coe
              C S N x).symm]

section IntermediateField

variable (L : Type*) [Field L]
  [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  [Algebra L N] [IsScalarTower (RatFunc C) L N]
  [FiniteDimensional L N] [IsGalois L N]

local instance compatibilityIntermediateConstantAlgebra : Algebra C L :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) L).comp
    (algebraMap C (RatFunc C)))

local instance compatibilityConstantIntermediateTopTower :
    IsScalarTower C L N := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
    algebraMap L N
      (algebraMap (RatFunc C) L (algebraMap C (RatFunc C) c))
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N _

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [FiniteDimensional L N] [IsGalois L N] in
/-- The rational-function base, an intermediate field, and the exact
constant extension form the tower used by the relative Galois action. -/
private theorem exactConstantExtensionCompatibility_ratFuncBaseTower :
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) := by
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module L (ExactConstantExtension C N S) := Algebra.toModule
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change (1 : S) ⊗ₜ[C] algebraMap (RatFunc C) N x =
    (1 : S) ⊗ₜ[C] algebraMap L N (algebraMap (RatFunc C) L x)
  congr 1
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N x

/-- For an actual finite place in the constant-extended normalization, a
rational restriction to `L` and divisibility `[N : L] ∣ [S : C]` imply the
decomposition-group cardinality identity.  The residue-degree-one, absolute
top-degree, and rational-base hypotheses of the generic theorem are all
derived internally. -/
theorem exactConstantExtensionFinitePlace_decompositionGroup_card_of_rational_base
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S)))
    (hBase : finiteExtensionPlaceDegree C L
      (.inl (finitePlaceUnder C L N
        (exactConstantExtensionDownstairsFinitePlace C S N hExact q))) = 1)
    (hDegreeDiv : Module.finrank L N ∣ Module.finrank C S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) L
        (ExactConstantExtension C N S) :=
      by exact exactConstantExtensionCompatibility_ratFuncBaseTower C S N hExact L
    letI : IsGalois L (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C L N S hExact
    let Q := exactConstantExtensionCompatibleBaseFinitePlace
      C S N hExact q
    Nat.card (finitePlaceDecompositionGroup C L
        (ExactConstantExtension C N S) Q) =
      Nat.card
          ((exactConstantExtensionConstantQuotient C L N S hExact).comp
            (finitePlaceDecompositionGroup C L
              (ExactConstantExtension C N S) Q).subtype).ker *
        Nat.card (S ≃ₐ[C] S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module L (ExactConstantExtension C N S) := Algebra.toModule
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) L
      (ExactConstantExtension C N S) :=
    exactConstantExtensionCompatibility_ratFuncBaseTower C S N hExact L
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsScalarTower L N (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C L N S
  let : IsGalois L (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C L N S hExact
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc S)
      (ExactConstantExtension C N S) :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S)
      (ExactConstantExtension C N S) :=
    isSeparable_over_extendedRatFunc C S N hExact
  let : Algebra S (RatFuncFiniteIntegralClosure C
      (ExactConstantExtension C N S)) :=
    exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
  let : Algebra S (RatFuncFiniteIntegralClosure S
      (ExactConstantExtension C N S)) :=
    RingHom.toAlgebra
      ((algebraMap S[X] (RatFuncFiniteIntegralClosure S
        (ExactConstantExtension C N S))).comp (algebraMap S S[X]))
  let : MulSemiringAction
      (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S)
      (RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)) :=
    finiteIntegralClosureGalAction C L (ExactConstantExtension C N S)
  let P := exactConstantExtensionDownstairsFinitePlace C S N hExact q
  let P₀ := finitePlaceUnder C L N P
  let Q := exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q
  let Qs := exactConstantExtensionUpstairsFinitePlace C S N hExact q
  have hInertiaDiv : finitePlaceRelativeInertiaDeg C L N P ∣
      Module.finrank L N := by
    let PInFiber : FinitePlaceUnderFiber C L N P₀ := ⟨P, rfl⟩
    have hFiber :=
      finitePlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
        C L N P₀ PInFiber
    refine ⟨Fintype.card (FinitePlaceUnderFiber C L N P₀) *
      finitePlaceRelativeRamificationIdx C L N P, ?_⟩
    simpa [PInFiber, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hFiber.symm
  have hDownDegreeEq : finiteExtensionPlaceDegree C N (.inl P) =
      finitePlaceRelativeInertiaDeg C L N P := by
    have hDegree := finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg
      C L N P
    simpa [P₀, P, hBase] using hDegree
  have hDownDegreeDiv : finiteExtensionPlaceDegree C N (.inl P) ∣
      Module.finrank C S := by
    rw [hDownDegreeEq]
    exact hInertiaDiv.trans hDegreeDiv
  have hUpstairsRational :
      finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
        (.inl Qs) = 1 := by
    rw [show finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
          (.inl Qs) =
        finiteExtensionPlaceDegree C N (.inl P) /
          Nat.gcd (Module.finrank C S)
            (finiteExtensionPlaceDegree C N (.inl P)) by
      exact exactConstantExtensionFinitePlace_degree_eq_div_gcd
        C S N hExact q]
    rw [(Nat.gcd_eq_right_iff_dvd).2 hDownDegreeDiv]
    exact Nat.div_self
      (finiteExtensionPlaceDegree_pos C N (.inl P))
  have hResidue : Module.finrank S Q.asIdeal.ResidueField = 1 := by
    calc
      Module.finrank S Q.asIdeal.ResidueField =
          Module.finrank S Qs.asIdeal.ResidueField :=
        exactConstantExtensionCompatibleResidueField_finrank_eq
          C S N hExact q
      _ = finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
          (.inl Qs) :=
        (finiteExtensionFinitePlace_degree_eq_finrank_residueField
          S (ExactConstantExtension C N S) Qs).symm
      _ = 1 := hUpstairsRational
  have hTop : finiteExtensionPlaceDegree C
      (ExactConstantExtension C N S) (.inl Q) = Module.finrank C S :=
    exactConstantExtensionCompatibleBaseFinitePlace_degree_eq
      C S N hExact q hUpstairsRational
  let R₀ := RatFuncFiniteIntegralClosure C L
  let R₁ := RatFuncFiniteIntegralClosure C N
  let R₂ := RatFuncFiniteIntegralClosure C (ExactConstantExtension C N S)
  let : Algebra R₀ R₁ := (finiteIntegralClosureMap C L N).toAlgebra
  let : Algebra R₁ R₂ :=
    (finiteIntegralClosureMap C N (ExactConstantExtension C N S)).toAlgebra
  let : Algebra R₀ R₂ :=
    (finiteIntegralClosureMap C L (ExactConstantExtension C N S)).toAlgebra
  let : SMul R₀ R₁ := Algebra.toSMul
  let : Module R₀ R₁ := Algebra.toModule
  let : SMul R₁ R₂ := Algebra.toSMul
  let : Module R₁ R₂ := Algebra.toModule
  let : SMul R₀ R₂ := Algebra.toSMul
  let : Module R₀ R₂ := Algebra.toModule
  let : IsScalarTower R₀ R₁ R₂ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap L (ExactConstantExtension C N S) (x : L) =
      algebraMap N (ExactConstantExtension C N S)
        (algebraMap L N (x : L))
    exact IsScalarTower.algebraMap_apply L N
      (ExactConstantExtension C N S) _
  have hUnderOriginal : finitePlaceUnder C N
      (ExactConstantExtension C N S) Q = P :=
    exactConstantExtensionCompatibleBaseFinitePlace_under_original
      C S N hExact q
  have hUnder : finitePlaceUnder C L
      (ExactConstantExtension C N S) Q = finitePlaceUnder C L N P := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    change Q.asIdeal.under R₀ = P.asIdeal.under R₀
    calc
      Q.asIdeal.under R₀ = (Q.asIdeal.under R₁).under R₀ :=
        (Ideal.under_under Q.asIdeal).symm
      _ = P.asIdeal.under R₀ := by
        rw [show Q.asIdeal.under R₁ = P.asIdeal by
          exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
            hUnderOriginal]
  have hBaseTop : finiteExtensionPlaceDegree C L
      (.inl (finitePlaceUnder C L (ExactConstantExtension C N S) Q)) = 1 := by
    rw [hUnder]
    exact hBase
  exact exactConstantExtensionFinitePlace_decompositionGroup_card
    C N S hExact L Q hResidue hTop hBaseTop

end IntermediateField

end

end BGS.HasseWeil
