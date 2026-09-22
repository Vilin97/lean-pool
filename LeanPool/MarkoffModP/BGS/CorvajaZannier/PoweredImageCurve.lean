/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredCoordinateRelation
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The actual powered-coordinate image curve

For a plane curve with function-field coordinates `x,y`, this file defines
the intermediate field `K(x^m,y^n)` and controls its two projection degrees.
It then transports the minimal polynomial of `y^n` over `K(x^m)` to the
standard rational-function field, clears denominators, takes the primitive
part, and applies Gauss' lemma.  The resulting polynomial in `K[U,V]` is
irreducible, vanishes at `(x^m,y^n)`, and has coordinate degrees exactly the
two projection degrees of the powered image.

Consequently its degree in `y^n` is at most `m * degreeOf 1 f`, while its
degree in `x^m` is at most `n * degreeOf 0 f`.  This is the source-sensitive
elimination input needed for the Corvaja--Zannier middle game.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped nonZeroDivisors Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem adjoin_pow_le_adjoin (z : L) (m : ℕ) :
    IntermediateField.adjoin K {z ^ m} ≤ IntermediateField.adjoin K {z} := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst w
  exact (IntermediateField.adjoin K {z}).toSubalgebra.pow_mem
    (IntermediateField.subset_adjoin K {z} (Set.mem_singleton z)) m

theorem restrictScalars_adjoin_over_adjoin_pow_eq_adjoin
    (z : L) (m : ℕ) :
    (IntermediateField.adjoin (IntermediateField.adjoin K {z ^ m}) {z}).restrictScalars K =
      IntermediateField.adjoin K {z} := by
  rw [IntermediateField.restrictScalars_adjoin_eq_sup]
  exact sup_eq_right.mpr (adjoin_pow_le_adjoin z m)

theorem finrank_adjoin_over_adjoin_pow_le
    (z : L) (m : ℕ) (hm : 0 < m) :
    Module.finrank (IntermediateField.adjoin K {z ^ m})
      (IntermediateField.adjoin (IntermediateField.adjoin K {z ^ m}) {z}) ≤ m := by
  let E0 := IntermediateField.adjoin K {z ^ m}
  let c : E0 :=
    ⟨z ^ m, IntermediateField.subset_adjoin K {z ^ m} (Set.mem_singleton (z ^ m))⟩
  let q : Polynomial E0 := Polynomial.X ^ m - Polynomial.C c
  have hqMonic : q.Monic := Polynomial.monic_X_pow_sub_C c hm.ne'
  have hqRoot : Polynomial.aeval z q = 0 := by
    simp [q, c]
  have hzIntegral : IsIntegral E0 z := ⟨q, hqMonic, hqRoot⟩
  have hqNe : q ≠ 0 := hqMonic.ne_zero
  calc
    Module.finrank E0 (IntermediateField.adjoin E0 {z}) =
        (minpoly E0 z).natDegree :=
      IntermediateField.adjoin.finrank hzIntegral
    _ ≤ q.natDegree :=
      Polynomial.natDegree_le_of_dvd (minpoly.dvd E0 z hqRoot) hqNe
    _ = m := by simp [q]

theorem finiteDimensional_over_adjoin_pow
    (z : L) (m : ℕ) (hm : 0 < m)
    [FiniteDimensional (IntermediateField.adjoin K {z}) L] :
    FiniteDimensional (IntermediateField.adjoin K {z ^ m}) L := by
  let E0 := IntermediateField.adjoin K {z ^ m}
  let A := IntermediateField.adjoin E0 {z}
  let AK : IntermediateField K L :=
    IntermediateField.restrictScalars (L' := E0) K A
  have hA : AK = IntermediateField.adjoin K {z} := by
    exact restrictScalars_adjoin_over_adjoin_pow_eq_adjoin z m
  let c : E0 :=
    ⟨z ^ m, IntermediateField.subset_adjoin K {z ^ m} (Set.mem_singleton (z ^ m))⟩
  let q : Polynomial E0 := Polynomial.X ^ m - Polynomial.C c
  have hqMonic : q.Monic := Polynomial.monic_X_pow_sub_C c hm.ne'
  have hqRoot : Polynomial.aeval z q = 0 := by simp [q, c]
  have hzIntegral : IsIntegral E0 z := ⟨q, hqMonic, hqRoot⟩
  let : FiniteDimensional E0 A :=
    IntermediateField.adjoin.finiteDimensional hzIntegral
  let : FiniteDimensional A L := by
    change FiniteDimensional AK L
    rw [hA]
    infer_instance
  exact FiniteDimensional.trans E0 A L

theorem finrank_over_adjoin_pow_le_mul
    (z : L) (m d : ℕ) (hm : 0 < m)
    [FiniteDimensional (IntermediateField.adjoin K {z}) L]
    (hdegree : Module.finrank (IntermediateField.adjoin K {z}) L ≤ d) :
    Module.finrank (IntermediateField.adjoin K {z ^ m}) L ≤ m * d := by
  let E0 := IntermediateField.adjoin K {z ^ m}
  let A := IntermediateField.adjoin E0 {z}
  let AK : IntermediateField K L :=
    IntermediateField.restrictScalars (L' := E0) K A
  have hA : AK = IntermediateField.adjoin K {z} := by
    exact restrictScalars_adjoin_over_adjoin_pow_eq_adjoin z m
  let c : E0 :=
    ⟨z ^ m, IntermediateField.subset_adjoin K {z ^ m} (Set.mem_singleton (z ^ m))⟩
  let q : Polynomial E0 := Polynomial.X ^ m - Polynomial.C c
  have hqMonic : q.Monic := Polynomial.monic_X_pow_sub_C c hm.ne'
  have hqRoot : Polynomial.aeval z q = 0 := by simp [q, c]
  have hzIntegral : IsIntegral E0 z := ⟨q, hqMonic, hqRoot⟩
  let : FiniteDimensional E0 A :=
    IntermediateField.adjoin.finiteDimensional hzIntegral
  let : FiniteDimensional A L := by
    change FiniteDimensional AK L
    rw [hA]
    infer_instance
  have hrelative : Module.finrank E0 A ≤ m :=
    finrank_adjoin_over_adjoin_pow_le z m hm
  have htop : Module.finrank A L ≤ d := by
    change Module.finrank AK L ≤ d
    rw [hA]
    exact hdegree
  have : Module.Free A L := Module.Free.of_divisionRing A L
  have : Module.Free E0 A := Module.Free.of_divisionRing E0 A
  calc
    Module.finrank E0 L = Module.finrank E0 A * Module.finrank A L := by
      rw [Module.finrank_mul_finrank]
    _ ≤ m * d := Nat.mul_le_mul hrelative htop

/-! ## Clearing the minimal polynomial over a rational coordinate field -/

/-- Transport the minimal polynomial of `v` over `K(u)` to the standard
rational-function field `K(X)`. -/
noncomputable def ratFuncMinpoly
    (u : L) (hu : Transcendental K u) (v : L) : Polynomial (RatFunc K) :=
  (minpoly (IntermediateField.adjoin K {u}) v).map
    (RatFunc.algEquivOfTranscendental u hu).symm.toRingEquiv

/-- Clear the coefficient denominators in the transported minimal
polynomial.  This is an iterated polynomial over `K`. -/
noncomputable def integerClearedMinpoly
    (u : L) (hu : Transcendental K u) (v : L) :
    Polynomial (Polynomial K) :=
  IsLocalization.integerNormalization (nonZeroDivisors (Polynomial K))
    (ratFuncMinpoly u hu v)

/-- The primitive bivariate relation obtained from the minimal polynomial
of `v` over `K(u)`. -/
noncomputable def primitiveClearedMinpolyRelation
    (u : L) (hu : Transcendental K u) (v : L) :
    Polynomial (Polynomial K) := by
  letI := Classical.arbitrary (NormalizedGCDMonoid K)
  exact (integerClearedMinpoly u hu v).primPart

theorem ratFuncMinpoly_ne_zero
    (u : L) (hu : Transcendental K u) (v : L)
    (hv : IsIntegral (IntermediateField.adjoin K {u}) v) :
    ratFuncMinpoly u hu v ≠ 0 := by
  exact Polynomial.map_ne_zero (minpoly.ne_zero hv)

theorem ratFuncMinpoly_irreducible
    (u : L) (hu : Transcendental K u) (v : L)
    (hv : IsIntegral (IntermediateField.adjoin K {u}) v) :
    Irreducible (ratFuncMinpoly u hu v) := by
  let e := RatFunc.algEquivOfTranscendental u hu
  have h := (minpoly.irreducible hv).map (Polynomial.mapEquiv e.symm.toRingEquiv)
  simpa only [ratFuncMinpoly, e, Polynomial.mapEquiv_apply] using h

theorem integerClearedMinpoly_ne_zero
    (u : L) (hu : Transcendental K u) (v : L)
    (hv : IsIntegral (IntermediateField.adjoin K {u}) v) :
    integerClearedMinpoly u hu v ≠ 0 := by
  exact IsFractionRing.integerNormalization_eq_zero_iff.not.mpr
    (ratFuncMinpoly_ne_zero u hu v hv)

theorem primitiveClearedMinpolyRelation_ne_zero
    (u : L) (hu : Transcendental K u) (v : L) :
    primitiveClearedMinpolyRelation u hu v ≠ 0 := by
  let := Classical.arbitrary (NormalizedGCDMonoid K)
  exact (integerClearedMinpoly u hu v).primPart_ne_zero

theorem primitiveClearedMinpolyRelation_natDegree
    (u : L) (hu : Transcendental K u) (v : L)
    (hv : IsIntegral (IntermediateField.adjoin K {u}) v) :
    (primitiveClearedMinpolyRelation u hu v).natDegree =
      (minpoly (IntermediateField.adjoin K {u}) v).natDegree := by
  let := Classical.arbitrary (NormalizedGCDMonoid K)
  let q := ratFuncMinpoly u hu v
  let N := integerClearedMinpoly u hu v
  obtain ⟨b, hb, hmap⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors (Polynomial K)) q
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hqb0 : algebraMap (Polynomial K) (RatFunc K) b ≠ 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (Polynomial K) (RatFunc K)).not.mpr hb0
  have hq0 : q ≠ 0 := ratFuncMinpoly_ne_zero u hu v hv
  calc
    (primitiveClearedMinpolyRelation u hu v).natDegree = N.natDegree := by
      exact Polynomial.natDegree_primPart N
    _ = (N.map (algebraMap (Polynomial K) (RatFunc K))).natDegree := by
      symm
      exact Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective (Polynomial K) (RatFunc K)) N
    _ = q.natDegree := by
      change (Polynomial.map (algebraMap (Polynomial K) (RatFunc K))
        (IsLocalization.integerNormalization
          (nonZeroDivisors (Polynomial K)) q)).natDegree = q.natDegree
      rw [hmap, Algebra.smul_def]
      change (Polynomial.C (algebraMap (Polynomial K) (RatFunc K) b) * q).natDegree =
        q.natDegree
      exact Polynomial.natDegree_C_mul hqb0
    _ = (minpoly (IntermediateField.adjoin K {u}) v).natDegree := by
      exact Polynomial.natDegree_map_eq_of_injective
        (RatFunc.algEquivOfTranscendental u hu).symm.injective _

/-- After embedding the coefficient ring in `K(X)`, the primitive cleared
relation is a nonzero constant multiple of the transported minimal
polynomial. -/
theorem map_primitiveClearedMinpolyRelation_eq_C_mul
    (u : L) (hu : Transcendental K u) (v : L)
    (hv : IsIntegral (IntermediateField.adjoin K {u}) v) :
    ∃ c : RatFunc K, c ≠ 0 ∧
      (primitiveClearedMinpolyRelation u hu v).map
          (algebraMap (Polynomial K) (RatFunc K)) =
        Polynomial.C c * ratFuncMinpoly u hu v := by
  let := Classical.arbitrary (NormalizedGCDMonoid K)
  let q := ratFuncMinpoly u hu v
  let N := integerClearedMinpoly u hu v
  let g := primitiveClearedMinpolyRelation u hu v
  obtain ⟨b, hb, hmap⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors (Polynomial K)) q
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hN0 : N ≠ 0 := integerClearedMinpoly_ne_zero u hu v hv
  have hcontent0 : N.content ≠ 0 :=
    Polynomial.content_eq_zero_iff.not.mpr hN0
  let a : RatFunc K := algebraMap (Polynomial K) (RatFunc K) N.content
  let b' : RatFunc K := algebraMap (Polynomial K) (RatFunc K) b
  have ha0 : a ≠ 0 := by
    exact (FaithfulSMul.algebraMap_eq_zero_iff
      (Polynomial K) (RatFunc K)).not.mpr hcontent0
  have hb'0 : b' ≠ 0 := by
    exact (FaithfulSMul.algebraMap_eq_zero_iff
      (Polynomial K) (RatFunc K)).not.mpr hb0
  have hdecomp :
      N.map (algebraMap (Polynomial K) (RatFunc K)) =
        Polynomial.C a * g.map (algebraMap (Polynomial K) (RatFunc K)) := by
    rw [N.eq_C_content_mul_primPart, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hmap' :
      N.map (algebraMap (Polynomial K) (RatFunc K)) =
        Polynomial.C b' * q := by
    change (IsLocalization.integerNormalization
      (nonZeroDivisors (Polynomial K)) q).map
        (algebraMap (Polynomial K) (RatFunc K)) = Polynomial.C b' * q
    rw [hmap, Algebra.smul_def]
    rfl
  have hab :
      Polynomial.C a * g.map (algebraMap (Polynomial K) (RatFunc K)) =
        Polynomial.C b' * q := hdecomp.symm.trans hmap'
  refine ⟨a⁻¹ * b', mul_ne_zero (inv_ne_zero ha0) hb'0, ?_⟩
  change g.map (algebraMap (Polynomial K) (RatFunc K)) =
    Polynomial.C (a⁻¹ * b') * q
  calc
    g.map (algebraMap (Polynomial K) (RatFunc K)) =
        Polynomial.C a⁻¹ *
          (Polynomial.C a *
            g.map (algebraMap (Polynomial K) (RatFunc K))) := by
      rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ ha0,
        Polynomial.C_1, one_mul]
    _ = Polynomial.C a⁻¹ * (Polynomial.C b' * q) := by rw [hab]
    _ = Polynomial.C (a⁻¹ * b') * q := by
      rw [← mul_assoc, ← Polynomial.C_mul]

/-- The cleared minimal-polynomial relation is irreducible in `K[U,V]`. -/
theorem primitiveClearedMinpolyRelation_irreducible
    (u : L) (hu : Transcendental K u) (v : L)
    (hv : IsIntegral (IntermediateField.adjoin K {u}) v) :
    Irreducible (primitiveClearedMinpolyRelation u hu v) := by
  let := Classical.arbitrary (NormalizedGCDMonoid K)
  let q := ratFuncMinpoly u hu v
  let g := primitiveClearedMinpolyRelation u hu v
  obtain ⟨c, hc0, hmap⟩ :=
    map_primitiveClearedMinpolyRelation_eq_C_mul u hu v hv
  have hunit : IsUnit (Polynomial.C c : Polynomial (RatFunc K)) :=
    Polynomial.isUnit_C.mpr hc0.isUnit
  have hassociated : Associated
      (g.map (algebraMap (Polynomial K) (RatFunc K))) q := by
    rw [hmap]
    simpa only [mul_comm] using
      associated_mul_unit_left q (Polynomial.C c) hunit
  have hmapIrreducible :
      Irreducible (g.map (algebraMap (Polynomial K) (RatFunc K))) :=
    hassociated.symm.irreducible (ratFuncMinpoly_irreducible u hu v hv)
  exact (integerClearedMinpoly u hu v).isPrimitive_primPart
    |>.irreducible_iff_irreducible_map_fraction_map.mpr hmapIrreducible

/-- Specialize the rational-function variable `X` at a transcendental
element `u`, then include `K(u)` in the ambient field. -/
noncomputable def ratFuncSpecialization
    (u : L) (hu : Transcendental K u) : RatFunc K →+* L :=
  (algebraMap (IntermediateField.adjoin K {u}) L).comp
    (RatFunc.algEquivOfTranscendental u hu).toRingEquiv.toRingHom

theorem ratFuncSpecialization_comp_polynomial_algebraMap
    (u : L) (hu : Transcendental K u) :
    (ratFuncSpecialization u hu).comp
        (algebraMap (Polynomial K) (RatFunc K)) =
      Polynomial.eval₂RingHom (algebraMap K L) u := by
  apply Polynomial.ringHom_ext
  · intro c
    simp [ratFuncSpecialization]
    rw [← RatFunc.algebraMap_eq_C,
      (RatFunc.algEquivOfTranscendental u hu).commutes]
    rfl
  · simp [ratFuncSpecialization,
      RatFunc.algEquivOfTranscendental_X]

theorem ratFuncSpecialization_comp_symm_algEquiv
    (u : L) (hu : Transcendental K u) :
    (ratFuncSpecialization u hu).comp
        (RatFunc.algEquivOfTranscendental u hu).symm.toRingEquiv.toRingHom =
      algebraMap (IntermediateField.adjoin K {u}) L := by
  ext z
  simp [ratFuncSpecialization]

/-- Evaluation of an iterated polynomial at `(u,v)` agrees with first
mapping its coefficient polynomials to `K(X)` and then specializing `X` at
`u`. -/
theorem evalBivariate_eq_eval₂_ratFuncSpecialization_map
    (u : L) (hu : Transcendental K u) (v : L)
    (P : Polynomial (Polynomial K)) :
    evalBivariate u v P =
      Polynomial.eval₂ (ratFuncSpecialization u hu) v
        (P.map (algebraMap (Polynomial K) (RatFunc K))) := by
  rw [Polynomial.eval₂_map,
    ratFuncSpecialization_comp_polynomial_algebraMap]
  rfl

/-- The transported minimal polynomial vanishes after specializing the
rational-function variable at `u` and the outer variable at `v`. -/
theorem eval₂_ratFuncSpecialization_ratFuncMinpoly_eq_zero
    (u : L) (hu : Transcendental K u) (v : L) :
    Polynomial.eval₂ (ratFuncSpecialization u hu) v
      (ratFuncMinpoly u hu v) = 0 := by
  rw [ratFuncMinpoly, Polynomial.eval₂_map]
  change Polynomial.eval₂
    ((ratFuncSpecialization u hu).comp
      (RatFunc.algEquivOfTranscendental u hu).symm.toRingEquiv.toRingHom)
      v (minpoly (IntermediateField.adjoin K {u}) v) = 0
  rw [ratFuncSpecialization_comp_symm_algEquiv]
  exact minpoly.aeval (IntermediateField.adjoin K {u}) v

/-- The primitive cleared relation really vanishes at `(u,v)`. -/
theorem evalBivariate_primitiveClearedMinpolyRelation_eq_zero
    (u : L) (hu : Transcendental K u) (v : L)
    (hv : IsIntegral (IntermediateField.adjoin K {u}) v) :
    evalBivariate u v (primitiveClearedMinpolyRelation u hu v) = 0 := by
  rw [evalBivariate_eq_eval₂_ratFuncSpecialization_map u hu v]
  obtain ⟨c, hc, hmap⟩ :=
    map_primitiveClearedMinpolyRelation_eq_C_mul u hu v hv
  rw [hmap, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    eval₂_ratFuncSpecialization_ratFuncMinpoly_eq_zero u hu v, mul_zero]

/-- Swapping the two variables preserves irreducibility. -/
theorem irreducible_transposeBivariate
    {P : Polynomial (Polynomial K)} (hP : Irreducible P) :
    Irreducible (transposeBivariate P) := by
  rw [transposeBivariate_eq_bivariateSwap]
  change Irreducible ((Polynomial.Bivariate.swap (R := K)) P)
  exact hP.map (Polynomial.Bivariate.swap (R := K))

/-- An irreducible relation vanishing at a pair whose first coordinate is
transcendental must genuinely depend on its outer variable.  Applied after
swapping, this says the original relation genuinely depends on its inner
variable. -/
theorem transposeBivariate_natDegree_ne_zero_of_eval_eq_zero
    (u v : L) (hv : Transcendental K v)
    {P : Polynomial (Polynomial K)} (hP : Irreducible P)
    (hzero : evalBivariate u v P = 0) :
    (transposeBivariate P).natDegree ≠ 0 := by
  let Q := transposeBivariate P
  have hzeroQ : evalBivariate v u Q = 0 := by
    change evalBivariate v u (transposeBivariate P) = 0
    rw [evalBivariate_transposeBivariate]
    exact hzero
  intro hdegree
  have hQ : Q = Polynomial.C (Q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdegree
  have hcoeffEval :
      Polynomial.eval₂ (algebraMap K L) v (Q.coeff 0) = 0 := by
    have hzeroQ' := hzeroQ
    rw [hQ] at hzeroQ'
    unfold evalBivariate at hzeroQ'
    rw [Polynomial.eval₂_C] at hzeroQ'
    exact hzeroQ'
  have hcoeff : Q.coeff 0 = 0 := by
    have hinj : Function.Injective
        (Polynomial.aeval (R := K) v : Polynomial K →ₐ[K] L) :=
      transcendental_iff_injective.mp hv
    apply hinj
    simpa only [Polynomial.aeval_def, map_zero] using hcoeffEval
  have hQzero : Q = 0 := by rw [hQ, hcoeff, map_zero]
  apply hP.ne_zero
  apply transposeBivariate_injective
  have hQzero' : transposeBivariate P = 0 := by
    simpa only [Q] using hQzero
  simpa only [map_zero] using hQzero'

/-- For an irreducible bivariate relation at a transcendental pair, the
degree in the first coordinate is exactly the minimal-polynomial degree over
the rational field generated by the second coordinate. -/
theorem transposeBivariate_natDegree_eq_minpoly
    (u v : L) (hvTrans : Transcendental K v)
    {P : Polynomial (Polynomial K)} (hP : Irreducible P)
    (hzero : evalBivariate u v P = 0) :
    (transposeBivariate P).natDegree =
      (minpoly (IntermediateField.adjoin K {v}) u).natDegree := by
  let := Classical.arbitrary (NormalizedGCDMonoid K)
  let Q := transposeBivariate P
  let e := RatFunc.algEquivOfTranscendental v hvTrans
  let qRat : Polynomial (RatFunc K) :=
    Q.map (algebraMap (Polynomial K) (RatFunc K))
  let qAdjoin : Polynomial (IntermediateField.adjoin K {v}) :=
    qRat.map e.toRingEquiv
  have hQIrreducible : Irreducible Q :=
    irreducible_transposeBivariate hP
  have hQDegree : Q.natDegree ≠ 0 :=
    transposeBivariate_natDegree_ne_zero_of_eval_eq_zero
      u v hvTrans hP hzero
  have hQPrimitive : Q.IsPrimitive :=
    hQIrreducible.isPrimitive hQDegree
  have hqRatIrreducible : Irreducible qRat := by
    exact hQPrimitive.irreducible_iff_irreducible_map_fraction_map.mp
      hQIrreducible
  have hqAdjoinIrreducible : Irreducible qAdjoin := by
    have h := hqRatIrreducible.map (Polynomial.mapEquiv e.toRingEquiv)
    simpa only [qAdjoin, Polynomial.mapEquiv_apply] using h
  have hzeroQ : evalBivariate v u Q = 0 := by
    change evalBivariate v u (transposeBivariate P) = 0
    rw [evalBivariate_transposeBivariate]
    exact hzero
  have hqAdjoinRootEval :
      Polynomial.eval₂
        (algebraMap (IntermediateField.adjoin K {v}) L) u qAdjoin = 0 := by
    dsimp only [qAdjoin]
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ (ratFuncSpecialization v hvTrans) u qRat = 0
    rw [← evalBivariate_eq_eval₂_ratFuncSpecialization_map v hvTrans u Q]
    exact hzeroQ
  have hqAdjoinRoot : Polynomial.aeval u qAdjoin = 0 := by
    simpa only [Polynomial.aeval_def] using hqAdjoinRootEval
  have heq := minpoly.eq_of_irreducible hqAdjoinIrreducible hqAdjoinRoot
  have hminDegree :
      (minpoly (IntermediateField.adjoin K {v}) u).natDegree =
        qAdjoin.natDegree := by
    calc
      (minpoly (IntermediateField.adjoin K {v}) u).natDegree =
          (qAdjoin * Polynomial.C qAdjoin.leadingCoeff⁻¹).natDegree := by
        rw [heq]
      _ = qAdjoin.natDegree := Polynomial.natDegree_mul_C
        (inv_ne_zero
          (Polynomial.leadingCoeff_ne_zero.mpr hqAdjoinIrreducible.ne_zero))
  calc
    (transposeBivariate P).natDegree = Q.natDegree := rfl
    _ = qRat.natDegree := by
      symm
      exact Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective (Polynomial K) (RatFunc K)) Q
    _ = qAdjoin.natDegree := by
      symm
      exact Polynomial.natDegree_map_eq_of_injective e.injective qRat
    _ = (minpoly (IntermediateField.adjoin K {v}) u).natDegree :=
      hminDegree.symm

/-! ## Powered coordinate fields of a plane curve -/

/-- The rational subfield generated by the powered first coordinate. -/
abbrev FirstPoweredCoordinateSubfield
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)] (m : ℕ) :=
  IntermediateField.adjoin K
    ({(planeCurveFunction f 0) ^ m} : Set (PlaneCurveFunctionField f))

/-- The rational subfield generated by the powered second coordinate. -/
abbrev SecondPoweredCoordinateSubfield
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)] (n : ℕ) :=
  IntermediateField.adjoin K
    ({(planeCurveFunction f 1) ^ n} : Set (PlaneCurveFunctionField f))

/-- The function field of the image of the powered-coordinate map, realized
inside the source function field. -/
abbrev PoweredCoordinateImageField
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)] (m n : ℕ) :=
  IntermediateField.adjoin K
    ({(planeCurveFunction f 0) ^ m, (planeCurveFunction f 1) ^ n} :
      Set (PlaneCurveFunctionField f))

/-- A positive power of the first coordinate remains transcendental. -/
theorem firstPoweredCoordinate_transcendental
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    letI := planeCurveCoordinateRing_isDomain hf
    Transcendental K ((planeCurveFunction f 0) ^ m) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  exact (firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)).pow hm

/-- A positive power of the second coordinate remains transcendental. -/
theorem secondPoweredCoordinate_transcendental
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    Transcendental K ((planeCurveFunction f 1) ^ n) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  exact (secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)).pow hn

/-- The canonical irreducible equation of the powered-coordinate image,
obtained by clearing the minimal polynomial over `K(x^m)`.  The outer
variable is the powered second coordinate. -/
noncomputable def poweredCoordinateImageRelation
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) : Polynomial (Polynomial K) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  exact primitiveClearedMinpolyRelation
    ((planeCurveFunction f 0) ^ m)
    (firstPoweredCoordinate_transcendental hf hpartialSecond m hm)
    ((planeCurveFunction f 1) ^ n)

/-- The source function field is finite over the field generated by a
positive power of its first coordinate. -/
theorem finiteDimensional_over_firstPoweredCoordinate
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    letI := planeCurveCoordinateRing_isDomain hf
    FiniteDimensional (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (FirstCoordinateSubfield f)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstCoordinate_of_irreducible hf hpartialSecond
  exact finiteDimensional_over_adjoin_pow
    (planeCurveFunction f 0) m hm

/-- Raising the first coordinate to the `m`-th power multiplies the source
degree bound by at most `m`. -/
theorem finrank_over_firstPoweredCoordinate_le
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) ≤ m * MvPolynomial.degreeOf 1 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (FirstCoordinateSubfield f)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstCoordinate_of_irreducible hf hpartialSecond
  exact finrank_over_adjoin_pow_le_mul
    (planeCurveFunction f 0) m (MvPolynomial.degreeOf 1 f) hm
      (finrank_over_firstCoordinate_le_degreeOf_second_of_irreducible
        hf hpartialSecond)

/-- The source function field is finite over the field generated by a
positive power of its second coordinate. -/
theorem finiteDimensional_over_secondPoweredCoordinate
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    FiniteDimensional (SecondPoweredCoordinateSubfield f n)
      (PlaneCurveFunctionField f) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (SecondCoordinateSubfield f)
      (PlaneCurveFunctionField f) :=
    (finiteSeparable_over_secondCoordinate_of_irreducible
      hf hpartialFirst).1
  exact finiteDimensional_over_adjoin_pow
    (planeCurveFunction f 1) n hn

/-- Raising the second coordinate to the `n`-th power multiplies the source
degree bound by at most `n`. -/
theorem finrank_over_secondPoweredCoordinate_le
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (SecondPoweredCoordinateSubfield f n)
      (PlaneCurveFunctionField f) ≤ n * MvPolynomial.degreeOf 0 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (SecondCoordinateSubfield f)
      (PlaneCurveFunctionField f) :=
    (finiteSeparable_over_secondCoordinate_of_irreducible
      hf hpartialFirst).1
  exact finrank_over_adjoin_pow_le_mul
    (planeCurveFunction f 1) n (MvPolynomial.degreeOf 0 f) hn
      (finrank_over_secondCoordinate_eq_degreeOf_first_of_irreducible
        hf hpartialFirst).le

/-- The powered image field, presented as an extension of the powered first
coordinate field by the powered second coordinate. -/
abbrev PoweredImageOverFirst
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)] (m n : ℕ) :=
  IntermediateField.adjoin (FirstPoweredCoordinateSubfield f m)
    ({(planeCurveFunction f 1) ^ n} : Set (PlaneCurveFunctionField f))

/-- The powered image field, presented as an extension of the powered second
coordinate field by the powered first coordinate. -/
abbrev PoweredImageOverSecond
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)] (m n : ℕ) :=
  IntermediateField.adjoin (SecondPoweredCoordinateSubfield f n)
    ({(planeCurveFunction f 0) ^ m} : Set (PlaneCurveFunctionField f))

/-- Forgetting the relative base field identifies the first presentation
with `K(x^m,y^n)`. -/
theorem restrictScalars_poweredImageOverFirst_eq
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)] (m n : ℕ) :
    (PoweredImageOverFirst f m n).restrictScalars K =
      PoweredCoordinateImageField f m n := by
  simpa only [Set.singleton_union] using
    (IntermediateField.adjoin_adjoin_left K
      ({(planeCurveFunction f 0) ^ m} : Set (PlaneCurveFunctionField f))
      ({(planeCurveFunction f 1) ^ n} : Set (PlaneCurveFunctionField f)))

/-- Forgetting the relative base field identifies the second presentation
with `K(x^m,y^n)`. -/
theorem restrictScalars_poweredImageOverSecond_eq
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)] (m n : ℕ) :
    (PoweredImageOverSecond f m n).restrictScalars K =
      PoweredCoordinateImageField f m n := by
  rw [IntermediateField.adjoin_adjoin_left]
  congr 1
  ext z
  simp

/-- The degree of the powered image over `K(x^m)` is bounded by the source
degree over that same rational subfield. -/
theorem finrank_poweredImageOverFirst_le
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (FirstPoweredCoordinateSubfield f m)
        (PoweredImageOverFirst f m n) ≤
      m * MvPolynomial.degreeOf 1 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstPoweredCoordinate hf hpartialSecond m hm
  exact (PoweredImageOverFirst f m n).toSubalgebra.toSubmodule.finrank_le.trans
    (finrank_over_firstPoweredCoordinate_le hf hpartialSecond m hm)

/-- The degree of the powered image over `K(y^n)` is bounded by the source
degree over that same rational subfield. -/
theorem finrank_poweredImageOverSecond_le
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (m n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (SecondPoweredCoordinateSubfield f n)
        (PoweredImageOverSecond f m n) ≤
      n * MvPolynomial.degreeOf 0 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (SecondPoweredCoordinateSubfield f n)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_secondPoweredCoordinate hf hpartialFirst n hn
  exact (PoweredImageOverSecond f m n).toSubalgebra.toSubmodule.finrank_le.trans
    (finrank_over_secondPoweredCoordinate_le hf hpartialFirst n hn)

/-- The canonical powered-image equation is irreducible over `K`. -/
theorem poweredCoordinateImageRelation_irreducible
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Irreducible (poweredCoordinateImageRelation hf hpartialSecond m hm n) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstPoweredCoordinate hf hpartialSecond m hm
  have hv : IsIntegral (FirstPoweredCoordinateSubfield f m)
      ((planeCurveFunction f 1) ^ n) := IsIntegral.of_finite _ _
  change Irreducible (primitiveClearedMinpolyRelation
    ((planeCurveFunction f 0) ^ m)
    (firstPoweredCoordinate_transcendental hf hpartialSecond m hm)
    ((planeCurveFunction f 1) ^ n))
  exact primitiveClearedMinpolyRelation_irreducible _ _ _ hv

/-- The canonical equation vanishes on the powered coordinate pair. -/
theorem evalBivariate_poweredCoordinateImageRelation_eq_zero
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    evalBivariate ((planeCurveFunction f 0) ^ m)
      ((planeCurveFunction f 1) ^ n)
      (poweredCoordinateImageRelation hf hpartialSecond m hm n) = 0 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstPoweredCoordinate hf hpartialSecond m hm
  have hv : IsIntegral (FirstPoweredCoordinateSubfield f m)
      ((planeCurveFunction f 1) ^ n) := IsIntegral.of_finite _ _
  change evalBivariate ((planeCurveFunction f 0) ^ m)
    ((planeCurveFunction f 1) ^ n)
    (primitiveClearedMinpolyRelation
      ((planeCurveFunction f 0) ^ m)
      (firstPoweredCoordinate_transcendental hf hpartialSecond m hm)
      ((planeCurveFunction f 1) ^ n)) = 0
  exact evalBivariate_primitiveClearedMinpolyRelation_eq_zero _ _ _ hv

/-- The degree in the powered second coordinate is exactly the projection
degree of the image over `K(x^m)`. -/
theorem poweredCoordinateImageRelation_natDegree_eq_finrank
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree =
      Module.finrank (FirstPoweredCoordinateSubfield f m)
        (PoweredImageOverFirst f m n) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstPoweredCoordinate hf hpartialSecond m hm
  have hv : IsIntegral (FirstPoweredCoordinateSubfield f m)
      ((planeCurveFunction f 1) ^ n) := IsIntegral.of_finite _ _
  calc
    (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree =
        (minpoly (FirstPoweredCoordinateSubfield f m)
          ((planeCurveFunction f 1) ^ n)).natDegree := by
      change (primitiveClearedMinpolyRelation
        ((planeCurveFunction f 0) ^ m)
        (firstPoweredCoordinate_transcendental hf hpartialSecond m hm)
        ((planeCurveFunction f 1) ^ n)).natDegree = _
      exact primitiveClearedMinpolyRelation_natDegree _ _ _ hv
    _ = Module.finrank (FirstPoweredCoordinateSubfield f m)
        (PoweredImageOverFirst f m n) :=
      (IntermediateField.adjoin.finrank hv).symm

/-- The degree in the powered first coordinate is exactly the projection
degree of the image over `K(y^n)`. -/
theorem poweredCoordinateImageRelation_transpose_natDegree_eq_finrank
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    (transposeBivariate
      (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree =
      Module.finrank (SecondPoweredCoordinateSubfield f n)
        (PoweredImageOverSecond f m n) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (SecondPoweredCoordinateSubfield f n)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_secondPoweredCoordinate hf hpartialFirst n hn
  have hu : IsIntegral (SecondPoweredCoordinateSubfield f n)
      ((planeCurveFunction f 0) ^ m) := IsIntegral.of_finite _ _
  have hdegree := transposeBivariate_natDegree_eq_minpoly
    ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n)
    (secondPoweredCoordinate_transcendental hf hpartialFirst n hn)
    (poweredCoordinateImageRelation_irreducible
      hf hpartialSecond m hm n)
    (evalBivariate_poweredCoordinateImageRelation_eq_zero
      hf hpartialSecond m hm n)
  calc
    (transposeBivariate
      (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree =
        (minpoly (SecondPoweredCoordinateSubfield f n)
          ((planeCurveFunction f 0) ^ m)).natDegree := hdegree
    _ = Module.finrank (SecondPoweredCoordinateSubfield f n)
        (PoweredImageOverSecond f m n) :=
      (IntermediateField.adjoin.finrank hu).symm

/-- Source-degree bounds for both coordinate degrees of the actual powered
image equation. -/
theorem poweredCoordinateImageRelation_bidegree_le
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree ≤
        m * MvPolynomial.degreeOf 1 f ∧
      (transposeBivariate
        (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree ≤
        n * MvPolynomial.degreeOf 0 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  constructor
  · rw [poweredCoordinateImageRelation_natDegree_eq_finrank
      hf hpartialSecond m hm n]
    exact finrank_poweredImageOverFirst_le
      hf hpartialSecond m n hm
  · rw [poweredCoordinateImageRelation_transpose_natDegree_eq_finrank
      hf hpartialFirst hpartialSecond m hm n hn]
    exact finrank_poweredImageOverSecond_le
      hf hpartialFirst m n hn

/-- Every coefficient of the canonical powered-image equation has degree at
most its first-coordinate degree. -/
theorem poweredCoordinateImageRelation_coeff_natDegree_le
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n i : ℕ) :
    ((poweredCoordinateImageRelation hf hpartialSecond m hm n).coeff i).natDegree ≤
      (transposeBivariate
        (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree := by
  have h := transposeBivariate_coeff_natDegree_le
    (transposeBivariate
      (poweredCoordinateImageRelation hf hpartialSecond m hm n))
    (transposeBivariate
      (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree
    le_rfl i
  simpa only [transposeBivariate_transposeBivariate] using h

/-- The canonical powered-image equation has positive degree in the powered
second coordinate. -/
theorem poweredCoordinateImageRelation_natDegree_pos
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    0 < (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : FiniteDimensional (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstPoweredCoordinate hf hpartialSecond m hm
  have hv : IsIntegral (FirstPoweredCoordinateSubfield f m)
      ((planeCurveFunction f 1) ^ n) := IsIntegral.of_finite _ _
  rw [poweredCoordinateImageRelation_natDegree_eq_finrank
    hf hpartialSecond m hm n, IntermediateField.adjoin.finrank hv]
  exact minpoly.natDegree_pos hv

/-- The canonical powered-image equation has positive degree in the powered
first coordinate. -/
theorem poweredCoordinateImageRelation_transpose_natDegree_pos
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : 0 < n) :
    0 < (transposeBivariate
      (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  apply Nat.pos_of_ne_zero
  exact transposeBivariate_natDegree_ne_zero_of_eval_eq_zero
    ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n)
    (secondPoweredCoordinate_transcendental hf hpartialFirst n hn)
    (poweredCoordinateImageRelation_irreducible
      hf hpartialSecond m hm n)
    (evalBivariate_poweredCoordinateImageRelation_eq_zero
      hf hpartialSecond m hm n)

/-- A single endpoint collecting the algebraic geometry of the powered
coordinate image: an irreducible equation over `K`, its vanishing, positive
bidegrees, source-degree bounds, and the corresponding coefficient bound. -/
theorem poweredCoordinateImageRelation_spec
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    let g := poweredCoordinateImageRelation hf hpartialSecond m hm n
    Irreducible g ∧
      evalBivariate ((planeCurveFunction f 0) ^ m)
        ((planeCurveFunction f 1) ^ n) g = 0 ∧
      0 < g.natDegree ∧
      0 < (transposeBivariate g).natDegree ∧
      g.natDegree ≤ m * MvPolynomial.degreeOf 1 f ∧
      (transposeBivariate g).natDegree ≤ n * MvPolynomial.degreeOf 0 f ∧
      ∀ i, (g.coeff i).natDegree ≤ n * MvPolynomial.degreeOf 0 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let g := poweredCoordinateImageRelation hf hpartialSecond m hm n
  have hbidegree := poweredCoordinateImageRelation_bidegree_le
    hf hpartialFirst hpartialSecond m hm n hn
  refine ⟨poweredCoordinateImageRelation_irreducible
      hf hpartialSecond m hm n,
    evalBivariate_poweredCoordinateImageRelation_eq_zero
      hf hpartialSecond m hm n,
    poweredCoordinateImageRelation_natDegree_pos
      hf hpartialSecond m hm n,
    poweredCoordinateImageRelation_transpose_natDegree_pos
      hf hpartialFirst hpartialSecond m hm n hn,
    hbidegree.1, hbidegree.2, ?_⟩
  intro i
  exact (poweredCoordinateImageRelation_coeff_natDegree_le
    hf hpartialSecond m hm n i).trans hbidegree.2

end

end BGS.CorvajaZannier
