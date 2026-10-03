/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
/-!
# Compactness of norm-one idele classes

This module combines local compactness, the logarithmic unit lattice, and the
principal-idele norm formula to prove compactness of the norm-one subgroup of
the idele class group.
-/

@[expose] public section

open scoped NumberField Pointwise RestrictedProduct NNReal
open NumberField IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem

noncomputable
section


variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

open scoped Classical in
/-- The product of all local integral-unit groups, embedded in the finite
idele group. -/
def integralStructureMap :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletionIntegers K).units) → FiniteIdeleGroup K :=
  RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      (v.adicCompletionIntegers K).units)
    Filter.cofinite

open scoped Classical in
theorem range_integralStructureMap :
    Set.range (integralStructureMap (K := K)) =
      (integralSubgroup (K := K) : Set (FiniteIdeleGroup K)) := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩ v
    exact (u v).property
  · intro ha
    let u : ∀ v : HeightOneSpectrum (𝓞 K),
        (v.adicCompletionIntegers K).units :=
      fun v ↦ ⟨a v, ha v⟩
    exact ⟨u, rfl⟩

open scoped Classical in
/-- The everywhere integral finite ideles form a compact group. -/
theorem isCompact_integralSubgroup :
    IsCompact
      ((integralSubgroup (K := K) :
        Subgroup (FiniteIdeleGroup K)) : Set (FiniteIdeleGroup K)) := by
  have hlocal :
      ∀ v : HeightOneSpectrum (𝓞 K),
        CompactSpace (v.adicCompletionIntegers K).units := by
    intro v
    exact isCompact_iff_compactSpace.mp
      (isCompact_finiteLocalUnits K v)
  let (v : HeightOneSpectrum (𝓞 K)) :
      CompactSpace (v.adicCompletionIntegers K).units :=
    hlocal v
  have hdomain :
      IsCompact
        (Set.univ : Set (∀ v : HeightOneSpectrum (𝓞 K),
          (v.adicCompletionIntegers K).units)) :=
    isCompact_univ
  rw [← range_integralStructureMap (K := K)]
  unfold integralStructureMap
  simpa only [Set.image_univ] using
    hdomain.image
      (RestrictedProduct.isEmbedding_structureMap.continuous :
        Continuous (integralStructureMap (K := K)))

end FiniteIdeleGroup

namespace InfiniteIdeleGroup

open scoped Classical in
/-- A compact annulus in one archimedean local multiplicative group. -/
def localAnnulus (w : InfinitePlace K) (B : ℝ) :
    Set w.Completionˣ :=
  {x | Real.exp (-B) ≤ ‖(x : w.Completion)‖ ∧
    ‖(x : w.Completion)‖ ≤ Real.exp B}

omit [NumberField K] in
open scoped Classical in
theorem isCompact_localAnnulus (w : InfinitePlace K) (B : ℝ) :
    IsCompact (localAnnulus w B) := by
  have hnorm_two : ‖(2 : w.Completion)‖ = 2 := by
    calc
      ‖(2 : w.Completion)‖ =
          ‖NumberField.InfinitePlace.Completion.extensionEmbedding w
            (2 : w.Completion)‖ :=
        (Isometry.norm_map_of_map_zero
          (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w)
          (map_zero _) _).symm
      _ = 2 := by
        rw [map_ofNat]
        norm_num
  let : NontriviallyNormedField w.Completion :=
    NontriviallyNormedField.ofNormNeOne
      ⟨2, by
        intro h
        have hz : ‖(2 : w.Completion)‖ = 0 := by rw [h, norm_zero]
        rw [hnorm_two] at hz
        norm_num at hz,
       by rw [hnorm_two]; norm_num⟩
  let : ProperSpace w.Completion :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace
      w.Completion
  let A : Set w.Completion :=
    {x | Real.exp (-B) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp B}
  have hAclosed : IsClosed A := by
    change IsClosed
      ((fun x : w.Completion ↦ ‖x‖) ⁻¹'
        Set.Icc (Real.exp (-B)) (Real.exp B))
    exact isClosed_Icc.preimage continuous_norm
  have hAbounded : Bornology.IsBounded A := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨Real.exp B, fun x hx ↦ hx.2⟩
  have hAcompact : IsCompact A :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨hAclosed, hAbounded⟩
  have hArange : A ⊆ Set.range (Units.val : w.Completionˣ → w.Completion) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      have hnonpos : Real.exp (-B) ≤ 0 := by
        simpa using hx.1
      exact (not_lt_of_ge hnonpos) (Real.exp_pos (-B))
    exact ⟨Units.mk0 x hx0, rfl⟩
  change IsCompact (Units.val ⁻¹' A)
  exact
    (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff hArange).mpr
      hAcompact

open scoped Classical in
/-- A compact product of local archimedean annuli. -/
def annulus (B : ℝ) : Set (InfiniteIdeleGroup K) :=
  ContinuousMulEquiv.piUnits.symm ''
    Set.univ.pi (fun w : InfinitePlace K ↦ localAnnulus w B)

omit [NumberField K] in
open scoped Classical in
theorem isCompact_annulus (B : ℝ) :
    IsCompact (annulus (K := K) B) := by
  apply IsCompact.image
  · exact isCompact_univ_pi fun w ↦ isCompact_localAnnulus w B
  · exact ContinuousMulEquiv.piUnits.symm.continuous

omit [NumberField K] in
open scoped Classical in
theorem mem_annulus_iff (a : InfiniteIdeleGroup K) (B : ℝ) :
    a ∈ annulus (K := K) B ↔
      ∀ w : InfinitePlace K,
        Real.exp (-B) ≤
            ‖((component w a : w.Completionˣ) : w.Completion)‖ ∧
          ‖((component w a : w.Completionˣ) : w.Completion)‖ ≤
            Real.exp B := by
  constructor
  · rintro ⟨u, hu, rfl⟩ w
    change Real.exp (-B) ≤ ‖(u w : w.Completion)‖ ∧
      ‖(u w : w.Completion)‖ ≤ Real.exp B
    exact hu w (Set.mem_univ w)
  · intro ha
    refine ⟨ContinuousMulEquiv.piUnits a, ?_, ?_⟩
    · intro w _
      exact ha w
    · exact ContinuousMulEquiv.piUnits.symm_apply_apply a

open scoped Classical in
/-- The archimedean norm is continuous. -/
theorem continuous_archimedeanNorm :
    Continuous (archimedeanNorm (K := K)) := by
  classical
  rw [show (archimedeanNorm (K := K) :
      InfiniteIdeleGroup K → ℝ≥0ˣ) =
      fun a ↦ ∏ w : InfinitePlace K,
        nnnormUnitHom w.Completion (component w a) ^ w.mult by
    rfl]
  apply continuous_finsetProd
  intro w _
  apply Continuous.pow
  exact (continuous_nnnorm.units_map _).comp
    ((continuous_apply w).comp
      ContinuousMulEquiv.piUnits.continuous)

open scoped Classical in
/-- The logarithms of the normalized archimedean absolute values, with the
distinguished place omitted as in Dirichlet's unit theorem. -/
def logNorm (a : InfiniteIdeleGroup K) :
    logSpace K :=
  fun w ↦ w.1.mult *
    Real.log ‖((component w.1 a : w.1.Completionˣ) : w.1.Completion)‖

open scoped Classical in
@[simp]
theorem logNorm_mul (a b : InfiniteIdeleGroup K) :
    logNorm (a * b) = logNorm a + logNorm b := by
  ext w
  have ha :
      ‖((component w.1 a : w.1.Completionˣ) :
        w.1.Completion)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (component w.1 a).ne_zero
  have hb :
      ‖((component w.1 b : w.1.Completionˣ) :
        w.1.Completion)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (component w.1 b).ne_zero
  simp only [logNorm, Pi.add_apply, map_mul, Units.val_mul, norm_mul,
    Real.log_mul ha hb, mul_add]

open scoped Classical in
/-- Ring-of-integers units, viewed as units of the number field. -/
def ringUnitToFieldUnit :
    (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K)

open scoped Classical in
theorem norm_infiniteComponent_principalIdele (x : Kˣ)
    (w : InfinitePlace K) :
    ‖((component w (IdeleGroup.principalIdele K x).1 :
        w.Completionˣ) : w.Completion)‖ =
      w (x : K) := by
  change ‖(((WithAbs.equiv w.1).symm (x : K) :
    WithAbs w.1) : w.Completion)‖ = w (x : K)
  rw [NumberField.InfinitePlace.Completion.norm_coe,
    (WithAbs.equiv w.1).apply_symm_apply]

open scoped Classical in
/-- On an algebraic integer unit, the archimedean idele log is exactly
Dirichlet's logarithmic embedding. -/
theorem logNorm_principalRingUnit (u : (𝓞 K)ˣ) :
    logNorm (IdeleGroup.principalIdele K
        (ringUnitToFieldUnit (K := K) u)).1 =
      NumberField.Units.logEmbedding K (Additive.ofMul u) := by
  ext w
  rw [logNorm, logEmbedding_component,
    norm_infiniteComponent_principalIdele]
  rfl

open scoped Classical in
theorem logNorm_component_le {r : ℝ} (a : InfiniteIdeleGroup K)
    (h : ‖logNorm a‖ ≤ r)
    (w : {w : InfinitePlace K //
      w ≠ w₀ (K := K)}) :
    |logNorm a w| ≤ r := by
  simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm (logNorm a) w).trans h

open scoped Classical in
/-- If the total archimedean norm is one, the omitted logarithmic coordinate
is the negative sum of all the other coordinates. -/
theorem sum_logNorm_eq_neg_distinguished
    (a : InfiniteIdeleGroup K)
    (ha : archimedeanNorm a = 1) :
    ∑ w, logNorm a w =
      -(w₀ (K := K)).mult *
        Real.log
          ‖((component (w₀ (K := K)) a :
              (w₀ (K := K)).Completionˣ) :
            (w₀ (K := K)).Completion)‖ := by
  have hprod :
      ∏ w : InfinitePlace K,
          ‖((component w a : w.Completionˣ) : w.Completion)‖ ^ w.mult =
        1 := by
    have h := congrArg
      (fun z : ℝ≥0ˣ ↦ (((z : ℝ≥0) : ℝ))) ha
    simpa only [archimedeanNorm_apply, Units.coe_prod,
      Units.val_pow_eq_pow_val, nnnormUnitHom_val, NNReal.coe_prod,
      NNReal.coe_pow, coe_nnnorm, Units.val_one, NNReal.coe_one] using h
  have hsum :
      ∑ w : InfinitePlace K,
          w.mult *
            Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖ = 0 := by
    calc
      ∑ w : InfinitePlace K,
          w.mult *
            Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖ =
          Real.log
            (∏ w : InfinitePlace K,
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖ ^ w.mult) := by
              rw [Real.log_prod]
              · apply Finset.sum_congr rfl
                intro w _
                rw [Real.log_pow]
              · intro w _
                exact pow_ne_zero _ <|
                  norm_ne_zero_iff.mpr (component w a).ne_zero
      _ = 0 := by rw [hprod, Real.log_one]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ (K := K))] at hsum
  have hsum' :
      (∑ w : {w : InfinitePlace K // w ≠ w₀ (K := K)},
          w.1.mult *
            Real.log
              ‖((component w.1 a : w.1.Completionˣ) :
                w.1.Completion)‖) =
        -(w₀ (K := K)).mult *
          Real.log
            ‖((component (w₀ (K := K)) a :
                (w₀ (K := K)).Completionˣ) :
              (w₀ (K := K)).Completion)‖ := by
    simpa only [neg_mul] using
      (eq_neg_of_add_eq_zero_right hsum)
  simpa only [logNorm] using hsum'

open scoped Classical in
/-- A norm bound in the logarithmic space bounds every local logarithm.
The harmless factor `#S∞` also covers the omitted coordinate. -/
theorem abs_log_norm_component_le
    {r : ℝ} (hr : 0 ≤ r) (a : InfiniteIdeleGroup K)
    (hlog : ‖logNorm a‖ ≤ r)
    (hnorm : archimedeanNorm a = 1)
    (w : InfinitePlace K) :
    |Real.log
        ‖((component w a : w.Completionˣ) : w.Completion)‖| ≤
      (Fintype.card (InfinitePlace K) : ℝ) * r := by
  have hmult :
      ∀ x : ℝ, 0 ≤ x → x ≤ w.mult * x := by
    intro x hx
    nth_rw 1 [← one_mul x]
    refine mul_le_mul ?_ le_rfl hx ?_
    all_goals
      rw [NumberField.InfinitePlace.mult]
      split_ifs <;> norm_num
  by_cases hw : w = w₀ (K := K)
  · have h := congrArg (‖·‖)
      (sum_logNorm_eq_neg_distinguished a hnorm).symm
    replace h := (le_of_eq h).trans (norm_sum_le _ _)
    simp_rw [norm_mul, norm_neg, Real.norm_eq_abs, Nat.abs_cast] at h
    refine (le_trans ?_ h).trans ?_
    · rw [← hw]
      exact hmult _ (abs_nonneg _)
    · refine (Finset.sum_le_card_nsmul _ _ _
          (fun v _ ↦ logNorm_component_le a hlog v)).trans ?_
      rw [nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hr
      exact_mod_cast
        (Fintype.card_subtype_le
          (fun w : InfinitePlace K ↦ w ≠ w₀ (K := K)))
  · have h := logNorm_component_le a hlog ⟨w, hw⟩
    rw [logNorm, abs_mul, Nat.abs_cast] at h
    refine (le_trans ?_ h).trans ?_
    · exact hmult _ (abs_nonneg _)
    · nth_rw 1 [← one_mul r]
      exact mul_le_mul
        (Nat.one_le_cast.mpr Fintype.card_pos)
        le_rfl hr (Nat.cast_nonneg _)

open scoped Classical in
/-- Exponentiating the preceding logarithmic estimate gives a compact
annulus containing the idele. -/
theorem mem_annulus_of_logNorm_le
    {r : ℝ} (hr : 0 ≤ r) (a : InfiniteIdeleGroup K)
    (hlog : ‖logNorm a‖ ≤ r)
    (hnorm : archimedeanNorm a = 1) :
    a ∈ annulus (K := K)
      ((Fintype.card (InfinitePlace K) : ℝ) * r) := by
  rw [mem_annulus_iff]
  intro w
  let B := (Fintype.card (InfinitePlace K) : ℝ) * r
  have h :=
    abs_log_norm_component_le hr a hlog hnorm w
  have hnpos :
      0 <
        ‖((component w a : w.Completionˣ) :
          w.Completion)‖ :=
    norm_pos_iff.mpr (component w a).ne_zero
  have habs :
      -B ≤
          Real.log
            ‖((component w a : w.Completionˣ) :
              w.Completion)‖ ∧
        Real.log
            ‖((component w a : w.Completionˣ) :
              w.Completion)‖ ≤ B := by
    simpa only [B] using (abs_le.mp h)
  constructor
  · calc
      Real.exp (-B) ≤
          Real.exp
            (Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖) :=
        Real.exp_le_exp.mpr habs.1
      _ = ‖((component w a : w.Completionˣ) :
            w.Completion)‖ :=
        Real.exp_log hnpos
  · calc
      ‖((component w a : w.Completionˣ) :
          w.Completion)‖ =
          Real.exp
            (Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖) :=
        (Real.exp_log hnpos).symm
      _ ≤ Real.exp B := Real.exp_le_exp.mpr habs.2

open scoped Classical in
/-- A real basis obtained from the full unit lattice. -/
def unitLatticeRealBasis :
    Module.Basis
      (Module.Free.ChooseBasisIndex ℤ
        (NumberField.Units.unitLattice K))
      ℝ (logSpace K) :=
  (Module.Free.chooseBasis ℤ
    (NumberField.Units.unitLattice K)).ofZLatticeBasis
      ℝ (NumberField.Units.unitLattice K)

open scoped Classical in
/-- An explicit uniform logarithmic bound for representatives modulo the
ordinary unit lattice. -/
def logFundamentalBound : ℝ :=
  ∑ i, ‖unitLatticeRealBasis (K := K) i‖

open scoped Classical in
theorem logFundamentalBound_nonneg :
    0 ≤ logFundamentalBound (K := K) :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

open scoped Classical in
/-- Every archimedean idele can be multiplied by an algebraic integer unit
so that its logarithmic vector lies in a fixed bounded fundamental
parallelepiped. -/
theorem exists_ringUnit_logNorm_le (a : InfiniteIdeleGroup K) :
    ∃ u : (𝓞 K)ˣ,
      ‖logNorm
          (a * (IdeleGroup.principalIdele K
            (ringUnitToFieldUnit (K := K) u)).1)‖ ≤
        logFundamentalBound (K := K) := by
  let b := unitLatticeRealBasis (K := K)
  let f := ZSpan.floor b (logNorm a)
  have hf :
      (f : logSpace K) ∈ NumberField.Units.unitLattice K := by
    have hspan :
        Submodule.span ℤ (Set.range (b :
          Module.Free.ChooseBasisIndex ℤ
              (NumberField.Units.unitLattice K) →
            logSpace K)) =
          NumberField.Units.unitLattice K := by
      dsimp [b, unitLatticeRealBasis]
      exact (Module.Free.chooseBasis ℤ
        (NumberField.Units.unitLattice K)).ofZLatticeBasis_span
          ℝ (NumberField.Units.unitLattice K)
    exact hspan.le f.property
  change (f : logSpace K) ∈
      Submodule.map
        (NumberField.Units.logEmbedding K).toIntLinearMap ⊤ at hf
  obtain ⟨u, -, hu⟩ := hf
  refine ⟨u.toMul⁻¹, ?_⟩
  have hinv :
      NumberField.Units.logEmbedding K
          (Additive.ofMul u.toMul⁻¹) =
        -(f : logSpace K) := by
    calc
      NumberField.Units.logEmbedding K
          (Additive.ofMul u.toMul⁻¹) =
          -NumberField.Units.logEmbedding K u := by
            rw [← map_neg]
            rfl
      _ = -(f : logSpace K) := congrArg Neg.neg hu
  rw [logNorm_mul, logNorm_principalRingUnit, hinv,
    ← sub_eq_add_neg, ← ZSpan.fract_apply]
  exact ZSpan.norm_fract_le b (logNorm a)

end InfiniteIdeleGroup

namespace IdeleGroup

open scoped Classical in
/-- A principal idele coming from a unit of the ring of integers is integral
at every finite place. -/
theorem principalRingUnit_mem_integralAtFinitePlaces
    (u : (𝓞 K)ˣ) :
    principalIdele K
        (InfiniteIdeleGroup.ringUnitToFieldUnit (K := K) u) ∈
      integralAtFinitePlaces (K := K) := by
  rw [← fractionalIdeal_ker, MonoidHom.mem_ker,
    fractionalIdeal_principalIdele]
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (u : 𝓞 K)) =
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    Ideal.span_singleton_eq_top.mpr u.isUnit,
    FractionalIdeal.coeIdeal_top]

open scoped Classical in
theorem finite_absoluteNorm_eq_one_of_integral
    (a : FiniteIdeleGroup K)
    (ha : a ∈ FiniteIdeleGroup.integralSubgroup (K := K)) :
    FiniteIdeleGroup.absoluteNorm a = 1 := by
  rw [FiniteIdeleGroup.absoluteNorm_eq_fractionalIdealAbsoluteNorm]
  have hfrac :
      FiniteIdeleGroup.fractionalIdeal a = 1 := by
    rw [← MonoidHom.mem_ker,
      FiniteIdeleGroup.fractionalIdeal_ker]
    exact ha
  rw [hfrac, map_one]

open scoped Classical in
/-- For an idele which is integral at all finite places, the global norm-one
condition is exactly the archimedean norm-one condition. -/
theorem archimedeanNorm_eq_one_of_normOne_integral
    (a : IdeleGroup K)
    (hnorm : a ∈ normOneSubgroup (K := K))
    (hintegral :
      a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)) :
    InfiniteIdeleGroup.archimedeanNorm a.1 = 1 := by
  have hfin :=
    finite_absoluteNorm_eq_one_of_integral a.2 hintegral
  change absoluteNorm a = 1 at hnorm
  rw [absoluteNorm_apply, hfin, one_mul] at hnorm
  exact inv_eq_one.mp hnorm

open scoped Classical in
/-- The fixed compact set of norm-one ideles which are integral at every
finite place and logarithmically reduced modulo the ordinary units. -/
def compactIntegralNormOneSet : Set (IdeleGroup K) :=
  (InfiniteIdeleGroup.annulus (K := K)
      ((Fintype.card (InfinitePlace K) : ℝ) *
        InfiniteIdeleGroup.logFundamentalBound (K := K)) ×ˢ
    (FiniteIdeleGroup.integralSubgroup (K := K) :
      Set (FiniteIdeleGroup K))) ∩
  {a | InfiniteIdeleGroup.archimedeanNorm a.1 = 1}

open scoped Classical in
theorem isCompact_compactIntegralNormOneSet :
    IsCompact (compactIntegralNormOneSet (K := K)) := by
  apply IsCompact.inter_right
  · exact
      (InfiniteIdeleGroup.isCompact_annulus
        ((Fintype.card (InfinitePlace K) : ℝ) *
          InfiniteIdeleGroup.logFundamentalBound (K := K))).prod
        (FiniteIdeleGroup.isCompact_integralSubgroup (K := K))
  · exact isClosed_singleton.preimage
      (InfiniteIdeleGroup.continuous_archimedeanNorm.comp continuous_fst)

open scoped Classical in
theorem mem_compactIntegralNormOneSet_iff (a : IdeleGroup K) :
    a ∈ compactIntegralNormOneSet (K := K) ↔
      a.1 ∈ InfiniteIdeleGroup.annulus (K := K)
          ((Fintype.card (InfinitePlace K) : ℝ) *
            InfiniteIdeleGroup.logFundamentalBound (K := K)) ∧
        a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) ∧
        InfiniteIdeleGroup.archimedeanNorm a.1 = 1 := by
  change
    ((a.1 ∈ InfiniteIdeleGroup.annulus (K := K)
          ((Fintype.card (InfinitePlace K) : ℝ) *
            InfiniteIdeleGroup.logFundamentalBound (K := K)) ∧
        a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)) ∧
      InfiniteIdeleGroup.archimedeanNorm a.1 = 1) ↔ _
  tauto

open scoped Classical in
/-- A norm-one idele integral at every finite place is principal-equivalent
to an element of the fixed compact representative set. -/
theorem exists_compactIntegralNormOneSet_representative
    (a : IdeleGroup K)
    (hnorm : a ∈ normOneSubgroup (K := K))
    (hintegral :
      a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)) :
    ∃ b ∈ compactIntegralNormOneSet (K := K),
      QuotientGroup.mk' (principalSubgroup K) b =
        QuotientGroup.mk' (principalSubgroup K) a := by
  obtain ⟨u, hu⟩ :=
    InfiniteIdeleGroup.exists_ringUnit_logNorm_le a.1
  let p : IdeleGroup K :=
    principalIdele K
      (InfiniteIdeleGroup.ringUnitToFieldUnit (K := K) u)
  let b : IdeleGroup K := a * p
  have hpIntegral :
      p ∈ integralAtFinitePlaces (K := K) := by
    exact principalRingUnit_mem_integralAtFinitePlaces u
  have hbIntegral :
      b.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) := by
    exact (integralAtFinitePlaces (K := K)).mul_mem hintegral
      hpIntegral
  have hpNorm :
      p ∈ normOneSubgroup (K := K) := by
    exact principalSubgroup_le_normOneSubgroup
      ⟨InfiniteIdeleGroup.ringUnitToFieldUnit (K := K) u, rfl⟩
  have hbNorm :
      b ∈ normOneSubgroup (K := K) :=
    (normOneSubgroup (K := K)).mul_mem hnorm hpNorm
  have hbArch :
      InfiniteIdeleGroup.archimedeanNorm b.1 = 1 :=
    archimedeanNorm_eq_one_of_normOne_integral b hbNorm hbIntegral
  have hbLog :
      ‖InfiniteIdeleGroup.logNorm b.1‖ ≤
        InfiniteIdeleGroup.logFundamentalBound (K := K) := by
    exact hu
  have hbAnnulus :
      b.1 ∈ InfiniteIdeleGroup.annulus (K := K)
        ((Fintype.card (InfinitePlace K) : ℝ) *
          InfiniteIdeleGroup.logFundamentalBound (K := K)) :=
    InfiniteIdeleGroup.mem_annulus_of_logNorm_le
      InfiniteIdeleGroup.logFundamentalBound_nonneg b.1 hbLog hbArch
  refine ⟨b,
    (mem_compactIntegralNormOneSet_iff b).mpr
      ⟨hbAnnulus, hbIntegral, hbArch⟩, ?_⟩
  change
    (QuotientGroup.mk' (principalSubgroup K)) (a * p) =
      (QuotientGroup.mk' (principalSubgroup K)) a
  rw [map_mul]
  have hpOne :
      QuotientGroup.mk' (principalSubgroup K) p = 1 := by
    apply (QuotientGroup.eq_one_iff p).mpr
    exact
      ⟨InfiniteIdeleGroup.ringUnitToFieldUnit (K := K) u, rfl⟩
  rw [hpOne]
  exact mul_one
    (QuotientGroup.mk' (principalSubgroup K) a)

open scoped Classical in
/-- For every ordinary ideal class which occurs on a norm-one idele, choose
one such representative; use `1` for the (irrelevant) remaining classes. -/
def normOneIdealClassRepresentative
    (c : ClassGroup (𝓞 K)) : IdeleGroup K :=
  if h : ∃ a : IdeleGroup K,
      a ∈ normOneSubgroup (K := K) ∧ idealClass a = c then
    Classical.choose h
  else
    1

open scoped Classical in
private theorem normOneIdealClassRepresentative_mem
    (c : ClassGroup (𝓞 K)) :
    normOneIdealClassRepresentative (K := K) c ∈
      normOneSubgroup (K := K) := by
  rw [normOneIdealClassRepresentative]
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact (normOneSubgroup (K := K)).one_mem

open scoped Classical in
private theorem idealClass_normOneIdealClassRepresentative
    (c : ClassGroup (𝓞 K))
    (h : ∃ a : IdeleGroup K,
      a ∈ normOneSubgroup (K := K) ∧ idealClass a = c) :
    idealClass (normOneIdealClassRepresentative (K := K) c) = c := by
  rw [normOneIdealClassRepresentative, dite_eq_left h]
  exact (Classical.choose_spec h).2

open scoped Classical in
/-- The finite set of chosen norm-one representatives of ordinary ideal
classes. -/
def normOneIdealClassRepresentativeSet : Set (IdeleGroup K) :=
  Set.range (normOneIdealClassRepresentative (K := K))

open scoped Classical in
theorem isCompact_normOneIdealClassRepresentativeSet :
    IsCompact (normOneIdealClassRepresentativeSet (K := K)) := by
  apply Set.Finite.isCompact
  exact Set.finite_range _

open scoped Classical in
theorem normOneIdealClassRepresentativeSet_subset_normOne :
    normOneIdealClassRepresentativeSet (K := K) ⊆
      (normOneSubgroup (K := K) : Set (IdeleGroup K)) := by
  rintro _ ⟨c, rfl⟩
  exact normOneIdealClassRepresentative_mem c

open scoped Classical in
/-- Remove the ordinary ideal class of a norm-one idele.  The result is
integral at every finite place, and multiplying back by the chosen
representative recovers the original idele class. -/
theorem exists_integral_normOne_reduction
    (a : IdeleGroup K)
    (ha : a ∈ normOneSubgroup (K := K)) :
    ∃ b : IdeleGroup K,
      b.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) ∧
      b ∈ normOneSubgroup (K := K) ∧
      QuotientGroup.mk' (principalSubgroup K)
          (b * normOneIdealClassRepresentative
            (K := K) (idealClass a)) =
        QuotientGroup.mk' (principalSubgroup K) a := by
  let r :=
    normOneIdealClassRepresentative (K := K) (idealClass a)
  have hrNorm : r ∈ normOneSubgroup (K := K) :=
    normOneIdealClassRepresentative_mem (idealClass a)
  have hrClass : idealClass r = idealClass a :=
    idealClass_normOneIdealClassRepresentative
      (idealClass a) ⟨a, ha, rfl⟩
  let d : IdeleGroup K := a * r⁻¹
  have hdClass : idealClass d = 1 := by
    dsimp [d]
    rw [map_mul, map_inv, hrClass]
    exact mul_inv_cancel _
  have hdPrincipal :
      fractionalIdeal d ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
    change ClassGroup.mk K (fractionalIdeal d) = 1 at hdClass
    exact (classGroup_mk_eq_one_iff (fractionalIdeal d)).mp hdClass
  obtain ⟨x, hx⟩ := hdPrincipal
  let p : IdeleGroup K := principalIdele K x
  let b : IdeleGroup K := d * p⁻¹
  have hbIntegral :
      b.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) := by
    change b ∈ integralAtFinitePlaces (K := K)
    rw [← fractionalIdeal_ker, MonoidHom.mem_ker]
    dsimp [b, p]
    rw [map_mul, map_inv, fractionalIdeal_principalIdele,
      hx, mul_inv_cancel]
  have hdNorm :
      d ∈ normOneSubgroup (K := K) :=
    (normOneSubgroup (K := K)).mul_mem ha
      ((normOneSubgroup (K := K)).inv_mem hrNorm)
  have hpNorm :
      p ∈ normOneSubgroup (K := K) :=
    principalSubgroup_le_normOneSubgroup ⟨x, rfl⟩
  have hbNorm :
      b ∈ normOneSubgroup (K := K) :=
    (normOneSubgroup (K := K)).mul_mem hdNorm
      ((normOneSubgroup (K := K)).inv_mem hpNorm)
  refine ⟨b, hbIntegral, hbNorm, ?_⟩
  apply QuotientGroup.eq_iff_div_mem.mpr
  change b * r * a⁻¹ ∈ principalSubgroup K
  refine ⟨x⁻¹, ?_⟩
  dsimp [b, d, p]
  rw [map_inv]
  symm
  calc
    a * r⁻¹ * (principalIdele K x)⁻¹ * r * a⁻¹ =
        (a * a⁻¹) * (r⁻¹ * r) * (principalIdele K x)⁻¹ := by
      ac_rfl
    _ = (principalIdele K x)⁻¹ := by simp

open scoped Classical in
/-- A compact set of ideles meeting every norm-one idele class. -/
def compactNormOneClassCover : Set (IdeleGroup K) :=
  compactIntegralNormOneSet (K := K) *
    normOneIdealClassRepresentativeSet (K := K)

open scoped Classical in
theorem isCompact_compactNormOneClassCover :
    IsCompact (compactNormOneClassCover (K := K)) :=
  by
    simpa [compactNormOneClassCover] using
      (isCompact_compactIntegralNormOneSet (K := K)).mul
        (isCompact_normOneIdealClassRepresentativeSet (K := K))

open scoped Classical in
theorem compactIntegralNormOneSet_subset_normOne :
    compactIntegralNormOneSet (K := K) ⊆
      (normOneSubgroup (K := K) : Set (IdeleGroup K)) := by
  intro a ha
  rw [mem_compactIntegralNormOneSet_iff] at ha
  have hfin :=
    finite_absoluteNorm_eq_one_of_integral a.2 ha.2.1
  change absoluteNorm a = 1
  rw [absoluteNorm_apply, hfin, ha.2.2, inv_one, mul_one]

open scoped Classical in
theorem compactNormOneClassCover_subset_normOne :
    compactNormOneClassCover (K := K) ⊆
      (normOneSubgroup (K := K) : Set (IdeleGroup K)) := by
  rintro z ⟨b, hb, r, hr, rfl⟩
  exact (normOneSubgroup (K := K)).mul_mem
    (compactIntegralNormOneSet_subset_normOne hb)
    (normOneIdealClassRepresentativeSet_subset_normOne hr)

end IdeleGroup

namespace IdeleClassGroup

open scoped Classical in
/-- The image of the compact idele cover is exactly the group of norm-one
idele classes. -/
theorem image_compactNormOneClassCover :
    (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)) ''
        IdeleGroup.compactNormOneClassCover (K := K) =
      (normOneSubgroup (K := K) : Set (IdeleClassGroup K)) := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mk_mem_normOneSubgroup_iff (K := K) a).mpr
      (IdeleGroup.compactNormOneClassCover_subset_normOne ha)
  · intro hq
    obtain ⟨a, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (IdeleGroup.principalSubgroup K) q
    have ha :
        a ∈ IdeleGroup.normOneSubgroup (K := K) :=
      (mk_mem_normOneSubgroup_iff a).mp hq
    obtain ⟨b, hbIntegral, hbNorm, hbClass⟩ :=
      IdeleGroup.exists_integral_normOne_reduction a ha
    obtain ⟨c, hcCompact, hcClass⟩ :=
      IdeleGroup.exists_compactIntegralNormOneSet_representative
        b hbNorm hbIntegral
    let r : IdeleGroup K :=
      IdeleGroup.normOneIdealClassRepresentative
        (K := K) (IdeleGroup.idealClass a)
    refine ⟨c * r, ?_, ?_⟩
    · exact
        ⟨c, hcCompact, r,
          ⟨IdeleGroup.idealClass a, rfl⟩, rfl⟩
    · calc
        QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (c * r) =
            QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) c *
              QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) r := by
                  rw [map_mul]
        _ =
            QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) b *
              QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) r := by
                  rw [hcClass]
        _ =
            QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) (b * r) := by
                rw [map_mul]
        _ =
            QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) a := hbClass

open scoped Classical in
/-- The norm-one idele class group is compact. -/
theorem normOneSubgroup_isCompact :
    IsCompact
      ((normOneSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) := by
  rw [← image_compactNormOneClassCover (K := K)]
  exact
    (IdeleGroup.isCompact_compactNormOneClassCover (K := K)).image
      QuotientGroup.continuous_mk

open scoped Classical in
/-- Compact-space form of the compactness theorem for norm-one idele classes. -/
instance normOneSubgroupCompactSpace :
    CompactSpace (normOneSubgroup (K := K)) :=
  isCompact_iff_compactSpace.mp
    (normOneSubgroup_isCompact (K := K))

end IdeleClassGroup
