/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeColoring
import LeanPool.CoarseGraining.Homogenization.Geometry.ScaleColoring
import LeanPool.CoarseGraining.Homogenization.Probability.RandomField
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Random Field Measurability -/

namespace Homogenization

/-!
Foundational measurability lemmas for coefficient fields viewed as the sample
space of the probability layer.

This file stays deliberately law-centric: the primitive random object remains a
measure on `CoeffField d`. The role of the present API is to expose the basic
measurable coefficient-field transforms and the `LocalSigma` measurability of
the generator observables used to define locality in law.
-/

theorem measurable_coeffField_entry {d : ℕ} (x : Vec d) (i j : Fin d) :
    Measurable (fun a : CoeffField d => a x i j) := by
  have hMat : Measurable (fun a : CoeffField d => a x) :=
    measurable_coeffField_eval (d := d) x
  have hRow : Measurable (fun a : CoeffField d => (a x) i) := Measurable.eval hMat
  exact Measurable.eval hRow

theorem measurable_restrictCoeffField {d : ℕ} (U : Set (Vec d)) :
    Measurable (restrictCoeffField (d := d) U) := by
  classical
  refine measurable_coeffField_to_ambient ?_ (fun V hV => ?_)
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    by_cases hx : x ∈ U
    · simpa [restrictCoeffField, hx] using measurable_coeffField_entry (d := d) x i j
    · simp [restrictCoeffField, hx]
  · refine measurable_localSigma_of_local (T := restrictCoeffField U) ?_ V hV
    intro W hW
    refine ⟨U ∩ W, hW.subset Set.inter_subset_right, ?_⟩
    intro a b hab x hxW
    by_cases hxU : x ∈ U
    · simp [restrictCoeffField, hxU, hab x ⟨hxU, hxW⟩]
    · simp [restrictCoeffField, hxU]

theorem restrictionSigma_le_coeffField {d : ℕ} (U : Set (Vec d)) :
    RestrictionSigma U ≤ instMeasurableSpaceCoeffField d :=
  measurable_iff_comap_le.mp (measurable_restrictCoeffField U)

theorem measurable_restrictCoeffField_restrictionSigma {d : ℕ} (U : Set (Vec d)) :
    @Measurable (CoeffField d) (CoeffField d) (RestrictionSigma U) _ (restrictCoeffField U) :=
  comap_measurable (restrictCoeffField U)

theorem restrictCoeffField_comp_restrictCoeffField_of_subset {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    restrictCoeffField U ∘ restrictCoeffField V = restrictCoeffField U := by
  funext a x
  by_cases hx : x ∈ U
  · have hxV : x ∈ V := hUV hx
    simp [Function.comp, restrictCoeffField, hx, hxV]
  · simp [Function.comp, restrictCoeffField, hx]

theorem measurable_restrictCoeffField_restrictionSigma_of_subset {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    @Measurable (CoeffField d) (CoeffField d) (RestrictionSigma V) _
      (restrictCoeffField U) := by
  simpa [restrictCoeffField_comp_restrictCoeffField_of_subset hUV, Function.comp] using
    (measurable_restrictCoeffField U).comp
      (measurable_restrictCoeffField_restrictionSigma (d := d) V)

theorem RestrictionSigma_mono {d : ℕ} {U V : Set (Vec d)} (hUV : U ⊆ V) :
    RestrictionSigma U ≤ RestrictionSigma V := by
  simpa [RestrictionSigma] using
    (measurable_iff_comap_le.mp
      (measurable_restrictCoeffField_restrictionSigma_of_subset (d := d) hUV))

theorem localTestObservable_translateCoeffField {d : ℕ} (z e e' : Vec d)
    (φ : Vec d → ℝ) (a : CoeffField d) :
    localTestObservable e e' φ (translateCoeffField z a) =
      localTestObservable e e' (fun y : Vec d => φ (y - z)) a := by
  let f : Vec d → ℝ := fun y => vecDot e' (matVecMul (a y) e) * φ (y - z)
  have hcv := setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z Set.univ f
  have huniv : translateSet z (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨y - z, trivial, ?_⟩
      ext i
      simp [sub_eq_add_neg, add_assoc]
  unfold localTestObservable
  calc
    ∫ x, (vecDot e' (matVecMul (translateCoeffField z a x) e) * φ x)
        ∂MeasureTheory.volume
        = ∫ x, f (x + z) ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          have hx : (x + z) - z = x := by
            ext i
            simp [sub_eq_add_neg, add_assoc]
          have hvec : (fun i => x i + z i) = x + z := by
            ext i
            rfl
          simp [f, translateCoeffField, hx, hvec]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (x + z) ∂MeasureTheory.volume := by
          simp
    _ = ∫ y in translateSet z (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume :=
          hcv
    _ = ∫ y, (vecDot e' (matVecMul (a y) e) * φ (y - z)) ∂MeasureTheory.volume := by
          simp [f, huniv]

theorem localFiniteTestObservable_translateCoeffField {d : ℕ} {ι : Type}
    (z : Vec d) (I : Finset ι) (e e' : ι → Vec d) (φ : ι → Vec d → ℝ)
    (a : CoeffField d) :
    localFiniteTestObservable I e e' φ (translateCoeffField z a) =
      localFiniteTestObservable I e e' (fun k y => φ k (y - z)) a := by
  let f : Vec d → ℝ := fun y =>
    ∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) * φ k (y - z)
  have hcv := setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z Set.univ f
  have huniv : translateSet z (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨y - z, trivial, ?_⟩
      ext i
      simp [sub_eq_add_neg, add_assoc]
  unfold localFiniteTestObservable
  calc
    ∫ x, (∑ k ∈ I, vecDot (e' k) (matVecMul (translateCoeffField z a x) (e k)) *
        φ k x) ∂MeasureTheory.volume
        = ∫ x, f (x + z) ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          have hx : (x + z) - z = x := by
            ext i
            simp [sub_eq_add_neg, add_assoc]
          have hvec : (fun i => x i + z i) = x + z := by
            ext i
            rfl
          simp [f, translateCoeffField, hx, hvec]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (x + z) ∂MeasureTheory.volume := by
          simp
    _ = ∫ y in translateSet z (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume :=
          hcv
    _ = ∫ y, (∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) *
        φ k (y - z)) ∂MeasureTheory.volume := by
          simp [f, huniv]

theorem measurable_translateCoeffField {d : ℕ} (z : Vec d) :
    Measurable (translateCoeffField (d := d) z) := by
  refine measurable_coeffField_to_ambient ?_ (fun V hV => ?_)
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    simpa [translateCoeffField] using
      measurable_coeffField_entry (d := d) (fun k => x k + z k) i j
  · refine measurable_localSigma_of_local (T := translateCoeffField z) ?_ V hV
    intro W hW
    refine ⟨{y : Vec d | y - z ∈ W}, ?_, ?_⟩
    · have htranslate :
          Bornology.IsBounded ((fun y : Vec d => y + z) '' W) :=
        isBounded_image_of_continuous_vec (continuous_id.add continuous_const) hW
      refine htranslate.subset ?_
      intro y hy
      refine ⟨y - z, hy, ?_⟩
      ext i
      simp [sub_eq_add_neg, add_assoc]
    intro a b hab x hxW
    have hx_pre : (fun i => x i + z i) ∈ {y : Vec d | y - z ∈ W} := by
      have hsub : (fun i => x i + z i) - z = x := by
        ext i
        simp [sub_eq_add_neg, add_assoc]
      simpa [hsub] using hxW
    simp [translateCoeffField, hab (fun i => x i + z i) hx_pre]

theorem measurable_translateByInt {d : ℕ} (z : Fin d → ℤ) :
    Measurable (translateByInt (d := d) z) := by
  simpa [translateByInt] using
    measurable_translateCoeffField (d := d) (intVecToRealVec z)

theorem vecDot_matVecMul_symmPart_cross {d : ℕ} (A : Mat d) (e e' : Vec d) :
    vecDot e' (matVecMul (symmPart A) e) =
      (1 / 2 : ℝ) *
        (vecDot e' (matVecMul A e) + vecDot e (matVecMul A e')) := by
  rw [symmPart_eq_smul_add_transpose, smul_matVecMul, add_matVecMul,
    vecDot_smul_right, vecDot_add_right, vecDot_matVecMul_transpose, vecDot_comm]
  rw [vecDot_comm (matVecMul A e') e]

theorem vecDot_matVecMul_skewPart_cross {d : ℕ} (A : Mat d) (e e' : Vec d) :
    vecDot e' (matVecMul (skewPart A) e) =
      (1 / 2 : ℝ) *
        (vecDot e' (matVecMul A e) - vecDot e (matVecMul A e')) := by
  rw [skewPart_eq_smul_sub_transpose, smul_matVecMul, sub_matVecMul,
    vecDot_smul_right]
  simp [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right,
    vecDot_matVecMul_transpose, vecDot_comm]

theorem localFiniteTestObservable_symmCoeffField {d : ℕ} {ι : Type}
    (I : Finset ι) (e e' : ι → Vec d) (φ : ι → Vec d → ℝ) (a : CoeffField d) :
    localFiniteTestObservable I e e' φ (symmCoeffField a) =
      localFiniteTestObservable (I.product (Finset.univ : Finset Bool))
        (fun kb => if kb.2 then e' kb.1 else e kb.1)
        (fun kb => if kb.2 then e kb.1 else e' kb.1)
        (fun kb x => (1 / 2 : ℝ) * φ kb.1 x) a := by
  classical
  unfold localFiniteTestObservable
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp [Finset.product_eq_sprod, Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro k hk
  change vecDot (e' k) (matVecMul (symmPart (a x)) (e k)) * φ k x =
    vecDot (e k) (matVecMul (a x) (e' k)) * (2⁻¹ * φ k x) +
      vecDot (e' k) (matVecMul (a x) (e k)) * (2⁻¹ * φ k x)
  rw [vecDot_matVecMul_symmPart_cross]
  ring_nf

theorem localFiniteTestObservable_skewCoeffField {d : ℕ} {ι : Type}
    (I : Finset ι) (e e' : ι → Vec d) (φ : ι → Vec d → ℝ) (a : CoeffField d) :
    localFiniteTestObservable I e e' φ (skewCoeffField a) =
      localFiniteTestObservable (I.product (Finset.univ : Finset Bool))
        (fun kb => if kb.2 then e' kb.1 else e kb.1)
        (fun kb => if kb.2 then e kb.1 else e' kb.1)
        (fun kb x => if kb.2 then -(1 / 2 : ℝ) * φ kb.1 x else (1 / 2 : ℝ) * φ kb.1 x) a := by
  classical
  unfold localFiniteTestObservable
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp [Finset.product_eq_sprod, Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro k hk
  change vecDot (e' k) (matVecMul (skewPart (a x)) (e k)) * φ k x =
    -(vecDot (e k) (matVecMul (a x) (e' k)) * (2⁻¹ * φ k x)) +
      vecDot (e' k) (matVecMul (a x) (e k)) * (2⁻¹ * φ k x)
  rw [vecDot_matVecMul_skewPart_cross]
  ring_nf

theorem measurable_symmCoeffField {d : ℕ} :
    Measurable (symmCoeffField (d := d)) := by
  refine measurable_coeffField_to_ambient ?_ (fun V hV => ?_)
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    have hij : Measurable (fun a : CoeffField d => a x i j) :=
      measurable_coeffField_entry (d := d) x i j
    have hji : Measurable (fun a : CoeffField d => a x j i) :=
      measurable_coeffField_entry (d := d) x j i
    simpa [symmCoeffField, symmPart_eq_smul_add_transpose, matTranspose] using!
      (measurable_const.mul (hij.add hji))
  · refine measurable_localSigma_of_local (T := symmCoeffField) ?_ V hV
    intro W hW
    refine ⟨W, hW, ?_⟩
    intro a b hab x hxW
    simp [symmCoeffField, hab x hxW]

theorem measurable_skewCoeffField {d : ℕ} :
    Measurable (skewCoeffField (d := d)) := by
  refine measurable_coeffField_to_ambient ?_ (fun V hV => ?_)
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    have hij : Measurable (fun a : CoeffField d => a x i j) :=
      measurable_coeffField_entry (d := d) x i j
    have hji : Measurable (fun a : CoeffField d => a x j i) :=
      measurable_coeffField_entry (d := d) x j i
    simpa [skewCoeffField, skewPart_eq_smul_sub_transpose, matTranspose] using!
      (measurable_const.mul (hij.sub hji))
  · refine measurable_localSigma_of_local (T := skewCoeffField) ?_ V hV
    intro W hW
    refine ⟨W, hW, ?_⟩
    intro a b hab x hxW
    simp [skewCoeffField, hab x hxW]

theorem IsStationary.map_translateByInt {d : ℕ}
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsStationary P) (z : Fin d → ℤ) :
    MeasureTheory.Measure.map (translateByInt z) P = P :=
  hP z

theorem integral_comp_translateByInt_eq_of_isStationary {d : ℕ}
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsStationary P)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (z : Fin d → ℤ) (f : CoeffField d → E)
    (hf : MeasureTheory.AEStronglyMeasurable f P) :
    ∫ a, f (translateByInt z a) ∂P = ∫ a, f a ∂P :=
  integral_comp_eq_of_map_eq (measurable_translateByInt z) (hP z) f hf

theorem localTestObservable_eq_of_ae_eq {d : ℕ} {a b : CoeffField d}
    (h : a =ᵐ[MeasureTheory.volume] b) (e e' : Vec d) (φ : Vec d → ℝ) :
    localTestObservable e e' φ a = localTestObservable e e' φ b := by
  unfold localTestObservable
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp [hx]

theorem localFiniteTestObservable_eq_of_ae_eq {d : ℕ} {ι : Type} {a b : CoeffField d}
    (h : a =ᵐ[MeasureTheory.volume] b) (I : Finset ι)
    (e e' : ι → Vec d) (φ : ι → Vec d → ℝ) :
    localFiniteTestObservable I e e' φ a = localFiniteTestObservable I e e' φ b := by
  unfold localFiniteTestObservable
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp [hx]

theorem mem_iff_of_measurableSet_pointwiseLocalSigma_of_pointwiseAgreementOn {d : ℕ}
    {U : Set (Vec d)} {s : Set (CoeffField d)}
    (hs : @MeasurableSet (CoeffField d) (PointwiseLocalSigma U) s) {a b : CoeffField d}
    (hab : PointwiseAgreementOn U a b) :
    a ∈ s ↔ b ∈ s := by
  let C : Set (Set (CoeffField d)) :=
    {s | IsPointwiseLocalEvent U s}
  have hC : ∀ t ∈ C, a ∈ t ↔ b ∈ t := by
    intro t ht
    exact ht hab
  have hsC : @MeasurableSet (CoeffField d) (MeasurableSpace.generateFrom C) s := by
    simpa [PointwiseLocalSigma, C] using! hs
  exact (MeasurableSpace.forall_generateFrom_mem_iff_mem_iff (S := C) (x := a) (y := b)).2
    hC s hsC

theorem mem_iff_of_measurableSet_localSigma_of_localAgreementOn {d : ℕ}
    {U : Set (Vec d)} {s : Set (CoeffField d)}
    (hs : @MeasurableSet (CoeffField d) (LocalSigma U) s) {a b : CoeffField d}
    (hab : LocalAgreementOn U a b) :
    a ∈ s ↔ b ∈ s :=
  mem_iff_of_measurableSet_pointwiseLocalSigma_of_pointwiseAgreementOn hs hab

theorem mem_iff_of_measurableSet_pointwiseLocalSigma_of_eqOn {d : ℕ} {U : Set (Vec d)}
    {s : Set (CoeffField d)} (hs : @MeasurableSet (CoeffField d) (PointwiseLocalSigma U) s)
    {a b : CoeffField d} (h : ∀ x, x ∈ U → a x = b x) :
    a ∈ s ↔ b ∈ s :=
  mem_iff_of_measurableSet_pointwiseLocalSigma_of_pointwiseAgreementOn hs h

theorem mem_iff_of_measurableSet_localSigma_of_eqOn {d : ℕ} {U : Set (Vec d)}
    {s : Set (CoeffField d)} (hs : @MeasurableSet (CoeffField d) (LocalSigma U) s)
    {a b : CoeffField d} (h : ∀ x, x ∈ U → a x = b x) :
    a ∈ s ↔ b ∈ s :=
  mem_iff_of_measurableSet_pointwiseLocalSigma_of_eqOn hs h

/-- A sample-space-valued coefficient field is pointwise-locally measurable on
`U` if it is measurable with codomain `PointwiseLocalSigma U`. -/
def IsPointwiseLocalSigmaMeasurableOn {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (A : Ω → CoeffField d) (U : Set (Vec d)) : Prop :=
  @Measurable Ω (CoeffField d) _ (PointwiseLocalSigma U) A

/-- Compatibility name for `IsPointwiseLocalSigmaMeasurableOn`. -/
abbrev IsLocalSigmaMeasurableOn {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (A : Ω → CoeffField d) (U : Set (Vec d)) : Prop :=
  IsPointwiseLocalSigmaMeasurableOn A U

/-- A sample-space-valued coefficient field is restriction-measurable on `U` if
it is measurable with codomain `RestrictionSigma U`. -/
def IsRestrictionSigmaMeasurableOn {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (A : Ω → CoeffField d) (U : Set (Vec d)) : Prop :=
  @Measurable Ω (CoeffField d) _ (RestrictionSigma U) A

theorem AreUnitSeparated.symm {d : ℕ} {U V : Set (Vec d)}
    (hUV : AreUnitSeparated U V) :
    AreUnitSeparated V U := by
  intro x y hx hy
  simpa [dist_comm] using hUV hy hx

theorem areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleColorClass {d : ℕ}
    {Q R S : TriadicCube d} {k : ℤ} {c : CubeColor d} (hk : 0 ≤ k)
    (hR : R ∈ descendantsAtScaleColorClass Q k c)
    (hS : S ∈ descendantsAtScaleColorClass Q k c) (hneq : R ≠ S) :
    AreUnitSeparated (cubeSet R) (cubeSet S) := by
  intro x y hx hy
  exact one_le_dist_of_ne_of_mem_descendantsAtScaleColorClass hk hR hS hneq hx hy

theorem pairwise_areUnitSeparated_cubeSet_descendantsAtScaleColorClass {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : 0 ≤ k) (c : CubeColor d) :
    (descendantsAtScaleColorClass Q k c : Set (TriadicCube d)).Pairwise
      (fun R S => AreUnitSeparated (cubeSet R) (cubeSet S)) := by
  intro R hR S hS hneq
  exact areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleColorClass hk hR hS hneq

theorem pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleColorClass {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : 0 ≤ k) (c : CubeColor d) :
    Pairwise
      (fun R S : {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c} =>
        AreUnitSeparated (cubeSet R.1) (cubeSet S.1)) := by
  intro R S hRS
  exact areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleColorClass hk R.2 S.2
    (by
      intro h
      apply hRS
      exact Subtype.ext h)

theorem areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleScaleColorClass {d : ℕ}
    {Q R S : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    (hR : R ∈ descendantsAtScaleScaleColorClass Q k c)
    (hS : S ∈ descendantsAtScaleScaleColorClass Q k c) (hneq : R ≠ S) :
    AreUnitSeparated (cubeSet R) (cubeSet S) := by
  intro x y hx hy
  exact one_le_dist_of_ne_of_mem_descendantsAtScaleScaleColorClass hR hS hneq hx hy

theorem pairwise_areUnitSeparated_cubeSet_descendantsAtScaleScaleColorClass {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (c : ScaleColor d k) :
    (descendantsAtScaleScaleColorClass Q k c : Set (TriadicCube d)).Pairwise
      (fun R S => AreUnitSeparated (cubeSet R) (cubeSet S)) := by
  intro R hR S hS hneq
  exact areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleScaleColorClass hR hS hneq

theorem pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleScaleColorClass {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (c : ScaleColor d k) :
    Pairwise
      (fun R S : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c} =>
        AreUnitSeparated (cubeSet R.1) (cubeSet S.1)) := by
  intro R S hRS
  exact areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleScaleColorClass R.2 S.2
    (by
      intro h
      apply hRS
      exact Subtype.ext h)

theorem areUnitSeparated_biUnion_right {d : ℕ} {ι : Type*} [DecidableEq ι] {U : Set (Vec d)}
    {V : ι → Set (Vec d)} {s : Finset ι}
    (h : ∀ i ∈ s, AreUnitSeparated U (V i)) :
    AreUnitSeparated U (⋃ i ∈ s, V i) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨i, hi, hyi⟩
  exact h i hi hx hyi

theorem measurableSet_biInter_restrictionSigma_biUnion {d : ℕ} {ι : Type*}
    [DecidableEq ι] {U : ι → Set (Vec d)} {f : ι → Set (CoeffField d)}
    {s : Finset ι}
    (hf : ∀ i ∈ s, @MeasurableSet (CoeffField d) (RestrictionSigma (U i)) (f i)) :
    @MeasurableSet (CoeffField d) (RestrictionSigma (⋃ i ∈ s, U i)) (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hi_meas :
          @MeasurableSet (CoeffField d) (RestrictionSigma (⋃ j ∈ insert i s, U j)) (f i) := by
        exact (RestrictionSigma_mono (d := d) hsubset_i) (f i) (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hs_meas :
          @MeasurableSet (CoeffField d) (RestrictionSigma (⋃ j ∈ insert i s, U j))
            (⋂ j ∈ s, f j) := by
        exact (RestrictionSigma_mono (d := d) hsubset_s) (⋂ j ∈ s, f j)
          (ih (fun j hj => hf j (by simp [hj])))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

theorem iIndep_restrictionSigma_of_isRestrictionUnitRangeDependent {d : ℕ} {ι : Type*}
    [DecidableEq ι] {P : MeasureTheory.Measure (CoeffField d)}
    [MeasureTheory.IsProbabilityMeasure P] {U : ι → Set (Vec d)}
    (hP : IsRestrictionUnitRangeDependent P)
    (hsep : Pairwise fun i j => AreUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndep (fun i => RestrictionSigma (U i)) P := by
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hsep_union : AreUnitSeparated (U i) (⋃ j ∈ s, U j) := by
        refine areUnitSeparated_biUnion_right (U := U i) (V := U) ?_
        intro j hj
        exact hsep (by
          intro hij
          exact hi (hij ▸ hj))
      have hs_meas :
          @MeasurableSet (CoeffField d) (RestrictionSigma (⋃ j ∈ s, U j)) (⋂ j ∈ s, f j) :=
        measurableSet_biInter_restrictionSigma_biUnion (U := U)
          (f := f) (s := s) fun j hj => hf j (by simp [hj])
      have h_inter :
          P (f i ∩ ⋂ j ∈ s, f j) = P (f i) * P (⋂ j ∈ s, f j) := by
        exact (ProbabilityTheory.Indep_iff
          (RestrictionSigma (U i)) (RestrictionSigma (⋃ j ∈ s, U j)) P).1
            (hP (U i) (⋃ j ∈ s, U j) hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        P (⋂ j ∈ insert i s, f j) = P (f i ∩ ⋂ j ∈ s, f j) := by
          simp
        _ = P (f i) * P (⋂ j ∈ s, f j) := h_inter
        _ = P (f i) * ∏ j ∈ s, P (f j) := by rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, P (f j) := by simp [Finset.prod_insert, hi]

theorem iIndep_restrictionSigma_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} (hk : 0 ≤ k) {c : CubeColor d}
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P) :
    ProbabilityTheory.iIndep
      (fun R : {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c} =>
        RestrictionSigma (cubeSet R.1)) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c}
  let U : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (U R) (U S) := by
    simpa [I, U] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleColorClass (Q := Q) hk c
  simpa [I, U] using
    (iIndep_restrictionSigma_of_isRestrictionUnitRangeDependent
      (d := d) (ι := I) (U := U) hP hsep)

theorem iIndep_restrictionSigma_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P) :
    ProbabilityTheory.iIndep
      (fun R : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c} =>
        RestrictionSigma (cubeSet R.1)) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c}
  let U : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (U R) (U S) := by
    simpa [I, U] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleScaleColorClass (Q := Q) c
  simpa [I, U] using
    (iIndep_restrictionSigma_of_isRestrictionUnitRangeDependent
      (d := d) (ι := I) (U := U) hP hsep)

theorem IsPointwiseLocalSigmaMeasurableOn.measurable_localTestObservable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {A : Ω → CoeffField d} {U : Set (Vec d)}
    (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (e e' : Vec d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U) :
    Measurable fun ω => localTestObservable e e' φ (A ω) := by
  exact
    (measurable_localTestObservable_localSigma (U := U) e e' hφ_cont hφ_compact hφ_support).comp
      hA

/-- Compatibility spelling for the pointwise-local measurability theorem. -/
theorem IsLocalSigmaMeasurableOn.measurable_localTestObservable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {A : Ω → CoeffField d} {U : Set (Vec d)}
    (hA : IsLocalSigmaMeasurableOn A U)
    (e e' : Vec d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U) :
    Measurable fun ω => localTestObservable e e' φ (A ω) :=
  IsPointwiseLocalSigmaMeasurableOn.measurable_localTestObservable hA e e' hφ_cont
    hφ_compact hφ_support

end Homogenization
