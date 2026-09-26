/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.WidetildeTheta
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Scalarization
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Expectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Dilation
public import LeanPool.CoarseGraining.Homogenization.Probability.RescaledLaw

/-! # Dilation Law -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory
open scoped Pointwise

noncomputable section

/-!
# Dilation of Chapter 4 laws

This file starts the law-facing dilation API used in Section 5.5.  The
normalized law is the push-forward of the original coefficient law by the
triadic pullback which sends scale `k` in the original coordinates to scale
zero in normalized coordinates.
-/

/-- Scale-normalize a carrier coefficient law by pulling honest fields back under
the triadic dilation `x ↦ 3^k x` (the carrier endomorphism `dilateReg`). -/
noncomputable def restrictionScaleNormalizedLaw {d : ℕ} (k : ℕ) (P : RestrictionCoeffLaw d) :
    RestrictionCoeffLaw d :=
  Measure.map (dilateReg (-(k : ℤ))) P

/-- The existing probability-layer rescaling is the same map as the Ch2
dilation by the negative natural scale (raw coefficient fields; kept as the public
raw-layer bridge still consumed by the coarse-graining and high-contrast tracks). -/
theorem rescaleCoeffField_eq_dilateCoeffField_neg_nat {d : ℕ} (k : ℕ) :
    rescaleCoeffField (d := d) k = Ch02.dilateCoeffField (-(k : ℤ)) := by
  funext a x i j
  have hvec : Ch02.undilateVec (-(k : ℤ)) x = triadicDilateVec k x := by
    ext r
    simp [Ch02.undilateVec, Ch02.triadicDilationFactor, triadicDilateVec,
      smul_eq_mul, zpow_neg]
  simp [rescaleCoeffField, Ch02.dilateCoeffField, hvec]

/-- The honest sample of a triadically rescaled carrier field is the raw triadic
rescaling of its honest sample (`rfl`). -/
theorem rescaleReg_toFun {d : ℕ} (k : ℕ) (a : RegCoeffField d) :
    (rescaleReg k a).toFun = rescaleCoeffField k a.toFun := rfl

/-- The honest sample of a triadically dilated carrier field is the raw triadic
dilation of its honest sample (`rfl`). -/
theorem dilateReg_toFun {d : ℕ} (k : ℤ) (a : RegCoeffField d) :
    (dilateReg k a).toFun = Ch02.dilateCoeffField k a.toFun := rfl

/-- The carrier triadic rescaling by `3^k` is the carrier dilation by the negative
natural scale (carrier analog of `rescaleCoeffField_eq_dilateCoeffField_neg_nat`). -/
theorem rescaleReg_eq_dilateReg_neg_nat {d : ℕ} (k : ℕ) :
    rescaleReg (d := d) k = dilateReg (-(k : ℤ)) := by
  funext a
  apply RegCoeffField.ext
  intro x
  have hs : ((3 : ℝ) ^ k) = (((3 : ℝ) ^ (-(k : ℤ)))⁻¹) := by
    rw [zpow_neg, zpow_natCast, inv_inv]
  simp only [rescaleReg_apply, dilateReg_apply, hs]

/-- `restrictionScaleNormalizedLaw` is the pushforward under the carrier triadic rescaling. -/
theorem restrictionScaleNormalizedLaw_eq_map_rescaleReg {d : ℕ} (k : ℕ) (P : RestrictionCoeffLaw d) :
    restrictionScaleNormalizedLaw k P = Measure.map (rescaleReg k) P := by
  rw [restrictionScaleNormalizedLaw, rescaleReg_eq_dilateReg_neg_nat]

/-- A scale-normalized probability law is again a probability law. -/
theorem isProbabilityMeasure_restrictionScaleNormalizedLaw {d : ℕ} (k : ℕ) (P : RestrictionCoeffLaw d)
    [IsProbabilityMeasure P] :
    IsProbabilityMeasure (restrictionScaleNormalizedLaw k P) := by
  rw [restrictionScaleNormalizedLaw]
  exact Measure.isProbabilityMeasure_map (measurable_dilateReg (d := d) (-(k : ℤ))).aemeasurable

/-- Bochner integral under a scale-normalized law. -/
theorem integral_restrictionScaleNormalizedLaw {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] {P : RestrictionCoeffLaw d} (k : ℕ)
    (X : RegCoeffField d → E)
    (hX : AEStronglyMeasurable X (restrictionScaleNormalizedLaw k P)) :
    ∫ a, X a ∂restrictionScaleNormalizedLaw k P =
      ∫ a, X (dilateReg (-(k : ℤ)) a) ∂P := by
  rw [restrictionScaleNormalizedLaw]
  exact MeasureTheory.integral_map
    (measurable_dilateReg (d := d) (-(k : ℤ))).aemeasurable hX

/-- Integrability under a scale-normalized law is integrability after
composing with the defining dilation. -/
theorem integrable_restrictionScaleNormalizedLaw_iff {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] {P : RestrictionCoeffLaw d} (k : ℕ)
    {X : RegCoeffField d → E}
    (hX : AEStronglyMeasurable X (restrictionScaleNormalizedLaw k P)) :
    Integrable X (restrictionScaleNormalizedLaw k P) ↔
      Integrable (fun a => X (dilateReg (-(k : ℤ)) a)) P := by
  simpa [restrictionScaleNormalizedLaw, Function.comp] using!
    (integrable_map_measure
      (μ := P) (f := dilateReg (d := d) (-(k : ℤ))) (g := X)
      hX (measurable_dilateReg (d := d) (-(k : ℤ))).aemeasurable)

/-- Triadic dilation preserves Borel measurability of ambient regions: the image
of a measurable set under scaling by `3^k` is the preimage of that set under
scaling by `(3^k)⁻¹`, hence measurable. -/
theorem measurableSet_triadicDilateSet {d : ℕ} (k : ℕ) {U : Set (Vec d)}
    (hU : MeasurableSet U) : MeasurableSet (triadicDilateSet k U) := by
  have hc : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  have hg : Measurable (fun x : Vec d => fun i => ((3 : ℝ) ^ k)⁻¹ * x i) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).const_mul _)
  have hset : triadicDilateSet k U
      = (fun x : Vec d => fun i => ((3 : ℝ) ^ k)⁻¹ * x i) ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hxy : (fun i => ((3 : ℝ) ^ k)⁻¹ * triadicDilateVec k y i) = y := by
        funext i
        simp only [triadicDilateVec]
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      simp only [Set.mem_preimage, hxy]
      exact hy
    · intro hx
      refine ⟨fun i => ((3 : ℝ) ^ k)⁻¹ * x i, hx, ?_⟩
      funext i
      simp only [triadicDilateVec]
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [hset]
  exact hU.preimage hg

/-- **Restriction/dilation commutation on the carrier.**  Restricting a triadically
rescaled field to `U` equals rescaling the field restricted to the dilated set
`triadicDilateSet k U` — the escape route recorded in the LOCALSIGMA plan. -/
theorem restrictReg_comp_rescaleReg_eq {d : ℕ} (k : ℕ) (U : Set (Vec d))
    (hU : MeasurableSet U) :
    restrictReg U hU ∘ rescaleReg k
      = rescaleReg k
        ∘ restrictReg (triadicDilateSet k U) (measurableSet_triadicDilateSet k hU) := by
  funext a
  apply RegCoeffField.ext
  intro x
  have hc : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  have hmem : (((3 : ℝ) ^ k) • x) ∈ triadicDilateSet k U ↔ x ∈ U := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hxeq : x = y := by
        funext i
        have := congrFun hxy i
        simp only [triadicDilateVec, Pi.smul_apply, smul_eq_mul] at this
        exact mul_left_cancel₀ hc this
      rwa [hxeq]
    · intro hx
      exact ⟨x, hx, by funext i; simp [triadicDilateVec, Pi.smul_apply, smul_eq_mul]⟩
  have htdv : triadicDilateVec k x = ((3 : ℝ) ^ k) • x := by
    funext i; simp [triadicDilateVec, Pi.smul_apply, smul_eq_mul]
  simp only [Function.comp_apply, restrictReg_apply, rescaleReg_apply, rescaleReg_toFun]
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    simp only [rescaleCoeffField, htdv]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.mp h))]

/-- Pullback by carrier triadic rescaling sends restriction-local information on
`U` to restriction-local information on the dilated set. -/
theorem measurable_rescaleReg_restrictionSigmaR {d : ℕ}
    (k : ℕ) (U : Set (Vec d)) (hU : MeasurableSet U) :
    @Measurable (RegCoeffField d) (RegCoeffField d)
      (RestrictionSigmaR (triadicDilateSet k U) (measurableSet_triadicDilateSet k hU))
      (RestrictionSigmaR U hU)
      (rescaleReg k) := by
  rw [measurable_iff_comap_le, RestrictionSigmaR, MeasurableSpace.comap_comp]
  have hmeas :
      @Measurable (RegCoeffField d) (RegCoeffField d)
        (RestrictionSigmaR (triadicDilateSet k U) (measurableSet_triadicDilateSet k hU)) _
        (restrictReg U hU ∘ rescaleReg k) := by
    rw [restrictReg_comp_rescaleReg_eq k U hU]
    exact (measurable_rescaleReg k).comp
      (measurable_restrictReg_restrictionSigmaR (triadicDilateSet k U)
        (measurableSet_triadicDilateSet k hU))
  exact hmeas.comap_le

private theorem localTestObservable_dilateCoeffField_int_eq_const_mul
    {d : ℕ} (n : ℤ) (e e' : Vec d) (φ : Vec d → ℝ) (a : CoeffField d) :
    localTestObservable e e' φ (Ch02.dilateCoeffField n a) =
      (((Ch02.triadicDilationFactor n)⁻¹) ^ d)⁻¹ *
        localTestObservable e e'
          (fun y : Vec d => φ (((Ch02.triadicDilationFactor n)⁻¹)⁻¹ • y)) a := by
  let q : ℝ := (Ch02.triadicDilationFactor n)⁻¹
  have hq : 0 < q := inv_pos.mpr (Ch02.triadicDilationFactor_pos n)
  let f : Vec d → ℝ := fun y => vecDot e' (matVecMul (a y) e) * φ (q⁻¹ • y)
  have hcv := Ch01.setIntegral_comp_smul_of_pos
    (d := d) (E := ℝ) (r := q) hq Set.univ f
  have huniv : q • (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨q⁻¹ • y, trivial, ?_⟩
      ext i
      simp [Pi.smul_apply, smul_eq_mul, hq.ne']
  have hundilate : ∀ x : Vec d, Ch02.undilateVec n x = q • x := by
    intro x
    ext i
    simp [Ch02.undilateVec, q, Pi.smul_apply, smul_eq_mul]
  unfold localTestObservable
  calc
    ∫ x, (vecDot e' (matVecMul (Ch02.dilateCoeffField n a x) e) * φ x) ∂volume
        = ∫ x, f (q • x) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          have hqx : q⁻¹ • (q • x) = x := by
            ext i
            simp [Pi.smul_apply, smul_eq_mul, hq.ne']
          simp [f, Ch02.dilateCoeffField, hundilate x, hqx]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (q • x) ∂volume := by simp
    _ = (q ^ d)⁻¹ • ∫ y in q • (Set.univ : Set (Vec d)), f y ∂volume := hcv
    _ = (q ^ d)⁻¹ *
          ∫ y, (vecDot e' (matVecMul (a y) e) *
            φ (((Ch02.triadicDilationFactor n)⁻¹)⁻¹ • y)) ∂volume := by
          simp [f, q, huniv]

private theorem localFiniteTestObservable_dilateCoeffField_int_eq {d : ℕ} {ι : Type}
    (n : ℤ) (I : Finset ι) (e e' : ι → Vec d) (φ : ι → Vec d → ℝ)
    (a : CoeffField d) :
    localFiniteTestObservable I e e' φ (Ch02.dilateCoeffField n a) =
      localFiniteTestObservable I e e'
        (fun k y => (((Ch02.triadicDilationFactor n)⁻¹) ^ d)⁻¹ *
          φ k (((Ch02.triadicDilationFactor n)⁻¹)⁻¹ • y)) a := by
  let q : ℝ := (Ch02.triadicDilationFactor n)⁻¹
  have hq : 0 < q := inv_pos.mpr (Ch02.triadicDilationFactor_pos n)
  let c : ℝ := (q ^ d)⁻¹
  let f : Vec d → ℝ := fun y =>
    ∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) * φ k (q⁻¹ • y)
  have hcv := Ch01.setIntegral_comp_smul_of_pos
    (d := d) (E := ℝ) (r := q) hq Set.univ f
  have huniv : q • (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨q⁻¹ • y, trivial, ?_⟩
      ext i
      simp [Pi.smul_apply, smul_eq_mul, hq.ne']
  have hundilate : ∀ x : Vec d, Ch02.undilateVec n x = q • x := by
    intro x
    ext i
    simp [Ch02.undilateVec, q, Pi.smul_apply, smul_eq_mul]
  unfold localFiniteTestObservable
  calc
    ∫ x, (∑ k ∈ I,
        vecDot (e' k) (matVecMul (Ch02.dilateCoeffField n a x) (e k)) * φ k x) ∂volume
        = ∫ x, f (q • x) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          have hqx : q⁻¹ • (q • x) = x := by
            ext i
            simp [Pi.smul_apply, smul_eq_mul, hq.ne']
          simp [f, Ch02.dilateCoeffField, hundilate x, hqx]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (q • x) ∂volume := by simp
    _ = (q ^ d)⁻¹ • ∫ y in q • (Set.univ : Set (Vec d)), f y ∂volume := hcv
    _ = c * ∫ y, f y ∂volume := by simp [c, huniv]
    _ = ∫ y, c * f y ∂volume := by
          exact (integral_const_mul c f).symm
    _ = ∫ y, (∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) *
        ((((Ch02.triadicDilationFactor n)⁻¹) ^ d)⁻¹ *
          φ k (((Ch02.triadicDilationFactor n)⁻¹)⁻¹ • y))) ∂volume := by
          apply integral_congr_ae
          filter_upwards with y
          simp [f, c, q, Finset.mul_sum]
          ring_nf

/-- The carrier triadic rescaling is a measurable equivalence, with inverse the
carrier dilation by the positive scale. -/
private noncomputable def rescaleRegMeasurableEquiv {d : ℕ} (k : ℕ) :
    RegCoeffField d ≃ᵐ RegCoeffField d where
  toEquiv :=
    { toFun := rescaleReg k
      invFun := dilateReg (k : ℤ)
      left_inv := by
        intro a
        apply RegCoeffField.ext
        intro x
        simp only [dilateReg_apply, rescaleReg_apply, smul_smul]
        rw [zpow_natCast, mul_inv_cancel₀ (by positivity : ((3 : ℝ) ^ k) ≠ 0), one_smul]
      right_inv := by
        intro a
        apply RegCoeffField.ext
        intro x
        simp only [dilateReg_apply, rescaleReg_apply, smul_smul]
        rw [zpow_natCast, inv_mul_cancel₀ (by positivity : ((3 : ℝ) ^ k) ≠ 0), one_smul] }
  measurable_toFun := measurable_rescaleReg k
  measurable_invFun := measurable_dilateReg (d := d) (k : ℤ)

private theorem nullMeasurableSet_map_of_preimage_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {s : Set β}
    (hs : NullMeasurableSet (e ⁻¹' s) μ) :
    NullMeasurableSet s (Measure.map e μ) := by
  rcases hs with ⟨t, ht, hst⟩
  refine ⟨e '' t, e.measurableEmbedding.measurableSet_image' ht, ?_⟩
  unfold Filter.EventuallyEq
  rw [e.measurableEmbedding.ae_map_iff]
  filter_upwards [hst] with a ha
  apply propext
  constructor
  · intro hs_ea
    exact ⟨a, ha.mp hs_ea, rfl⟩
  · rintro ⟨b, hb, hbeq⟩
    have hb_eq : b = a := e.injective hbeq
    subst hb_eq
    exact ha.mpr hb

private theorem indep_map_measurableEquiv
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {m1 m2 : MeasurableSpace β}
    (h : @ProbabilityTheory.Indep α
      (MeasurableSpace.comap (fun x : α => e x) m1)
      (MeasurableSpace.comap (fun x : α => e x) m2) mα μ) :
    @ProbabilityTheory.Indep β m1 m2 mβ
      (@Measure.map α β mα mβ (fun x : α => e x) μ) := by
  refine (ProbabilityTheory.Indep_iff
    (m₁ := m1) (m₂ := m2) (_mΩ := mβ)
    (μ := (@Measure.map α β mα mβ (fun x : α => e x) μ))).2 ?_
  intro s t hs ht
  have hemb : @MeasurableEmbedding α β mα mβ (fun x : α => e x) := by
    exact @MeasurableEquiv.measurableEmbedding α β mα mβ e
  have h_ind := (ProbabilityTheory.Indep_iff
    (m₁ := MeasurableSpace.comap (fun x : α => e x) m1)
    (m₂ := MeasurableSpace.comap (fun x : α => e x) m2)
    (_mΩ := mα) (μ := μ)).1 h
  have hspre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m1)
      ((fun x : α => e x) ⁻¹' s) := by
    exact ⟨s, hs, rfl⟩
  have htpre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m2)
      ((fun x : α => e x) ⁻¹' t) := by
    exact ⟨t, ht, rfl⟩
  have hst := h_ind ((fun x : α => e x) ⁻¹' s)
    ((fun x : α => e x) ⁻¹' t) hspre htpre
  have hmap_inter :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t) =
        μ ((fun x : α => e x) ⁻¹' (s ∩ t)) := by
    exact @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ (s ∩ t)
  have hmap_s :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) s =
        μ ((fun x : α => e x) ⁻¹' s) := by
    exact @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ s
  have hmap_t :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) t =
        μ ((fun x : α => e x) ⁻¹' t) := by
    exact @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ t
  calc
    (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t)
        = μ ((fun x : α => e x) ⁻¹' (s ∩ t)) := hmap_inter
    _ = μ (((fun x : α => e x) ⁻¹' s) ∩
          ((fun x : α => e x) ⁻¹' t)) := by rfl
    _ = μ ((fun x : α => e x) ⁻¹' s) *
          μ ((fun x : α => e x) ⁻¹' t) := hst
    _ = (@Measure.map α β mα mβ (fun x : α => e x) μ) s *
          (@Measure.map α β mα mβ (fun x : α => e x) μ) t := by
          rw [hmap_s, hmap_t]

private theorem dist_triadicDilateVec {d : ℕ} (k : ℕ) (x y : Vec d) :
    dist (triadicDilateVec k x) (triadicDilateVec k y) =
      ((3 : ℝ) ^ k) * dist x y := by
  let r : ℝ := (3 : ℝ) ^ k
  have hr : 0 ≤ r := by positivity
  have hsub : triadicDilateVec k x - triadicDilateVec k y = r • (x - y) := by
    ext i
    simp only [triadicDilateVec, r, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dist_eq_norm, dist_eq_norm, hsub, norm_smul_of_nonneg hr]

private theorem AreUnitSeparated.triadicDilateSet {d : ℕ} {U V : Set (Vec d)}
    (hUV : AreUnitSeparated U V) (k : ℕ) :
    AreUnitSeparated (triadicDilateSet k U) (triadicDilateSet k V) := by
  intro x y hx hy
  rcases hx with ⟨x0, hx0, rfl⟩
  rcases hy with ⟨y0, hy0, rfl⟩
  rw [dist_triadicDilateVec]
  have hsep : 1 ≤ dist x0 y0 := hUV hx0 hy0
  have hscale : 1 ≤ ((3 : ℝ) ^ k) := by
    exact (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) : 1 ≤ (3 : ℝ) ^ k)
  have hmul : (1 : ℝ) * 1 ≤ ((3 : ℝ) ^ k) * dist x0 y0 := by
    exact mul_le_mul hscale hsep zero_le_one (by positivity)
  simpa using hmul

namespace RestrictionUnitRangeDependentLaw

/-- Restriction-unit-range dependence is preserved by triadic
scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : RestrictionUnitRangeDependentLaw P) (k : ℕ) :
    RestrictionUnitRangeDependentLaw (restrictionScaleNormalizedLaw k P) := by
  intro U V hU hV hUV
  let e := rescaleRegMeasurableEquiv (d := d) k
  have hIndepDilated : ProbabilityTheory.Indep
      (RestrictionSigmaR (triadicDilateSet k U) (measurableSet_triadicDilateSet k hU))
      (RestrictionSigmaR (triadicDilateSet k V) (measurableSet_triadicDilateSet k hV)) P :=
    hP (triadicDilateSet k U) (triadicDilateSet k V)
      (measurableSet_triadicDilateSet k hU) (measurableSet_triadicDilateSet k hV)
      (AreUnitSeparated.triadicDilateSet hUV k)
  have hU_le : MeasurableSpace.comap
      (fun a : RegCoeffField d => rescaleReg k a) (RestrictionSigmaR U hU) ≤
        RestrictionSigmaR (triadicDilateSet k U) (measurableSet_triadicDilateSet k hU) := by
    exact (measurable_rescaleReg_restrictionSigmaR (d := d) k U hU).comap_le
  have hV_le : MeasurableSpace.comap
      (fun a : RegCoeffField d => rescaleReg k a) (RestrictionSigmaR V hV) ≤
        RestrictionSigmaR (triadicDilateSet k V) (measurableSet_triadicDilateSet k hV) := by
    exact (measurable_rescaleReg_restrictionSigmaR (d := d) k V hV).comap_le
  have hComap : ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun a : RegCoeffField d => rescaleReg k a) (RestrictionSigmaR U hU))
      (MeasurableSpace.comap
        (fun a : RegCoeffField d => rescaleReg k a) (RestrictionSigmaR V hV)) P :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hIndepDilated hU_le) hV_le
  have hmap := indep_map_measurableEquiv (μ := P) e
    (m1 := RestrictionSigmaR U hU) (m2 := RestrictionSigmaR V hV) hComap
  simpa [restrictionScaleNormalizedLaw_eq_map_rescaleReg, e] using! hmap

end RestrictionUnitRangeDependentLaw

private theorem dilatedCoeffFamily_coeffOn_ae_eq_rescaleCoeffField
    {d : ℕ} {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ) (Q : TriadicCube d) :
    ((Ch02.TriadicCoeffFamily.dilate (-(k : ℤ))
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)).coeffOn Q).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet Q)]
        (rescaleReg k a).toFun := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hD :=
    Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F Qsrc
  have hcoeff' :
      ((Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F).coeffOn
          (Ch02.dilateCube (-(k : ℤ)) Qsrc)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
          Ch02.dilateCoeffField (-(k : ℤ)) a.toFun := by
    simpa [F, Qsrc, htarget] using hD.coeff_ae_eq
  have hcast := hcoeff'
  rw [htarget] at hcast
  simpa [F, rescaleReg_toFun, rescaleCoeffField_eq_dilateCoeffField_neg_nat k] using hcast

namespace AELocallyUniformlyEllipticField

/-- Locally a.e.-uniform ellipticity is preserved by triadic rescaling of the
carrier coefficient field. -/
theorem of_rescaleCoeffField {d : ℕ} {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ) :
    AELocallyUniformlyEllipticField (Homogenization.rescaleReg k a) := by
  intro Q
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let bQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := B.coeffOn Q
  have hcoeff :
      bQ.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)]
        (Homogenization.rescaleReg k a).toFun := by
    simpa [bQ, B] using dilatedCoeffFamily_coeffOn_ae_eq_rescaleCoeffField ha k Q
  refine ⟨bQ.lam, bQ.Lam, bQ.lam_pos, bQ.lam_le_Lam, ?_⟩
  refine ⟨measurableSet_openCubeSet Q, ?_, ?_⟩
  · intro i j
    refine (bQ.aeStronglyMeasurable i j).congr ?_
    filter_upwards [hcoeff] with x hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [restrictCoeffField, hxQ, hx]
    · simp [restrictCoeffField, hxQ]
  · filter_upwards [bQ.aeElliptic, hcoeff] with x hxEll hx
    simpa [hx] using hxEll

end AELocallyUniformlyEllipticField

namespace AELocallyUniformlyEllipticLaw

/-- A locally a.e.-uniformly elliptic law remains so after triadic
scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : AELocallyUniformlyEllipticLaw P) (k : ℕ) :
    AELocallyUniformlyEllipticLaw (restrictionScaleNormalizedLaw k P) := by
  rw [restrictionScaleNormalizedLaw_eq_map_rescaleReg]
  exact ((rescaleRegMeasurableEquiv (d := d) k).measurableEmbedding.ae_map_iff).2 <| by
    filter_upwards [hP] with a ha
    exact ha.of_rescaleCoeffField k

end AELocallyUniformlyEllipticLaw

namespace RestrictionLawCarrier

/-- The Chapter 4 law carrier is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : RestrictionLawCarrier P) (k : ℕ) :
    RestrictionLawCarrier (restrictionScaleNormalizedLaw k P) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let : IsProbabilityMeasure (restrictionScaleNormalizedLaw k P) :=
    isProbabilityMeasure_restrictionScaleNormalizedLaw k P
  exact lawCarrier_of_aeLocallyUniformlyElliptic
    (hP.ae_locally_uniformly_elliptic.scaleNormalized k)

end RestrictionLawCarrier

theorem triadicCoeffFamily_rescaleCoeffField_aeeq_dilate
    {d : ℕ} {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ) :
    Ch02.TriadicCoeffFamily.AEEq
      (triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (rescaleReg k a) (ha.of_rescaleCoeffField k))
      (Ch02.TriadicCoeffFamily.dilate (-(k : ℤ))
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)) := by
  intro Q
  change
    (rescaleReg k a).toFun
      =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
        ((Ch02.TriadicCoeffFamily.dilate (-(k : ℤ))
          (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)).coeffOn Q).toCoeffField
  simpa [Ch02.cubeDomain_coe] using
    (dilatedCoeffFamily_coeffOn_ae_eq_rescaleCoeffField ha k Q).symm

theorem LambdaSqCoeffField_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ)
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent) :
    LambdaSqCoeffField Q s q (rescaleReg k a) =
      LambdaSqCoeffField (Ch02.dilateCube (k : ℤ) Q) s q a := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (rescaleReg k a) (ha.of_rescaleCoeffField k)
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F] using triadicCoeffFamily_rescaleCoeffField_aeeq_dilate ha k
  have hAEEq := Ch02.LambdaSq_eq_ofAEEq hGB Q s q
  have hdilate :=
    Ch02.LambdaSq_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F) Qsrc s q
  calc
    LambdaSqCoeffField Q s q (rescaleReg k a)
        = Ch02.LambdaSq Q s q G := by
          simp [LambdaSqCoeffField, G, ha.of_rescaleCoeffField k]
    _ = Ch02.LambdaSq Q s q B := hAEEq
    _ = Ch02.LambdaSq Qsrc s q F := by
          simpa [Qsrc, htarget, B] using hdilate
    _ = LambdaSqCoeffField Qsrc s q a := by
          simp [LambdaSqCoeffField, F, ha]

theorem lambdaSqCoeffField_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ)
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent) :
    lambdaSqCoeffField Q s q (rescaleReg k a) =
      lambdaSqCoeffField (Ch02.dilateCube (k : ℤ) Q) s q a := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (rescaleReg k a) (ha.of_rescaleCoeffField k)
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F] using triadicCoeffFamily_rescaleCoeffField_aeeq_dilate ha k
  have hAEEq := Ch02.lambdaSq_eq_ofAEEq hGB Q s q
  have hdilate :=
    Ch02.lambdaSq_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F) Qsrc s q
  calc
    lambdaSqCoeffField Q s q (rescaleReg k a)
        = Ch02.lambdaSq Q s q G := by
          simp [lambdaSqCoeffField, G, ha.of_rescaleCoeffField k]
    _ = Ch02.lambdaSq Q s q B := hAEEq
    _ = Ch02.lambdaSq Qsrc s q F := by
          simpa [Qsrc, htarget, B] using hdilate
    _ = lambdaSqCoeffField Qsrc s q a := by
          simp [lambdaSqCoeffField, F, ha]

@[simp] theorem dilateCube_originCube_nat {d : ℕ} (k m : ℕ) :
    Ch02.dilateCube (k : ℤ) (originCube d (m : ℤ)) =
      originCube d ((k + m : ℕ) : ℤ) := by
  simp [Ch02.dilateCube, originCube, add_comm]

theorem LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ)
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    LambdaSqCoeffField (originCube d (m : ℤ)) s q (rescaleReg k a) =
      LambdaSqCoeffField (originCube d ((k + m : ℕ) : ℤ)) s q a := by
  simpa using
    LambdaSqCoeffField_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k (originCube d (m : ℤ)) s q

theorem lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ)
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    lambdaSqCoeffField (originCube d (m : ℤ)) s q (rescaleReg k a) =
      lambdaSqCoeffField (originCube d ((k + m : ℕ) : ℤ)) s q a := by
  simpa using
    lambdaSqCoeffField_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k (originCube d (m : ℤ)) s q

/-- The ambient coarse block matrix rescales by shifting the origin-cube
scale. -/
theorem coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ) :
    coarseBlockMatrix (cubeSet (originCube d (m : ℤ))) (rescaleReg k a).toFun =
      coarseBlockMatrix (cubeSet (originCube d ((k + m : ℕ) : ℤ))) a.toFun := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (rescaleReg k a) (ha.of_rescaleCoeffField k)
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let Q : TriadicCube d := originCube d (m : ℤ)
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F] using triadicCoeffFamily_rescaleCoeffField_aeeq_dilate ha k
  have hAEEq := Ch02.coarseBlockMatrix_eq_ofAEEq (hGB Q)
  have hdilate :=
    Ch02.coarseBlockMatrix_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F Qsrc)
  have hdilate' :
      Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (B.coeffOn Q) =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) := by
    rw [htarget] at hdilate
    simpa [B] using hdilate
  calc
    coarseBlockMatrix (cubeSet (originCube d (m : ℤ))) (rescaleReg k a).toFun
        = Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (G.coeffOn Q) := by
          simpa [Q, G] using
            RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
              (ha.of_rescaleCoeffField k) Q
    _ = Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (B.coeffOn Q) := hAEEq
    _ = Ch02.coarseBlockMatrix (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) := hdilate'
    _ = coarseBlockMatrix (cubeSet Qsrc) a.toFun :=
          (RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
            ha Qsrc).symm
    _ = coarseBlockMatrix (cubeSet (originCube d ((k + m : ℕ) : ℤ))) a.toFun := by
          simp [Qsrc, Q]
/-- Scalar response observables rescale by shifting the origin-cube scale. -/
theorem restrictionResponseJObservableCubeSet_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ) (p q : Vec d) :
    restrictionResponseJObservableCubeSet (originCube d (m : ℤ)) p q (rescaleReg k a) =
      restrictionResponseJObservableCubeSet (originCube d ((k + m : ℕ) : ℤ)) p q a := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (rescaleReg k a) (ha.of_rescaleCoeffField k)
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let Q : TriadicCube d := originCube d (m : ℤ)
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F] using triadicCoeffFamily_rescaleCoeffField_aeeq_dilate ha k
  have hAEEq : Ch02.responseJ (Ch02.cubeDomain Q) (G.coeffOn Q) p q =
      Ch02.responseJ (Ch02.cubeDomain Q) (B.coeffOn Q) p q :=
    Ch02.responseJ_eq_ofAEEq (hGB Q) p q
  have hdilate :=
    Ch02.responseJ_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F Qsrc) p q
  have hdilate' :
      Ch02.responseJ (Ch02.cubeDomain Q) (B.coeffOn Q) p q =
        Ch02.responseJ (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q := by
    rw [htarget] at hdilate
    simpa [B] using hdilate
  calc
    restrictionResponseJObservableCubeSet (originCube d (m : ℤ)) p q (rescaleReg k a)
        = Ch02.responseJ (Ch02.cubeDomain Q) (G.coeffOn Q) p q := by
          symm
          calc
            Ch02.responseJ (Ch02.cubeDomain Q) (G.coeffOn Q) p q =
                ResponseJ (openCubeSet Q) p q (rescaleReg k a).toFun := by
                  simpa [G, Q, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                    coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                      (Ch02.cubeDomain Q) (G.coeffOn Q) p q
            _ = restrictionResponseJObservableCubeSet (originCube d (m : ℤ)) p q
                  (rescaleReg k a) := by
                  rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q
                    (rescaleReg k a).toFun]
                  rfl
    _ = Ch02.responseJ (Ch02.cubeDomain Q) (B.coeffOn Q) p q := hAEEq
    _ = Ch02.responseJ (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q := hdilate'
    _ = restrictionResponseJObservableCubeSet Qsrc p q a := by
          calc
            Ch02.responseJ (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q =
                ResponseJ (openCubeSet Qsrc) p q a.toFun := by
                  simpa [F, Qsrc, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                    coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                      (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q
            _ = restrictionResponseJObservableCubeSet Qsrc p q a := by
                  rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Qsrc p q a.toFun]
                  rfl
    _ = restrictionResponseJObservableCubeSet (originCube d ((k + m : ℕ) : ℤ)) p q a := by
          simp [Qsrc, Q]

/-- Scalar response observables under the dilation defining `restrictionScaleNormalizedLaw`. -/
theorem restrictionResponseJObservableCubeSet_originCube_dilateCoeffField_neg_nat_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ) (p q : Vec d) :
    restrictionResponseJObservableCubeSet (originCube d (m : ℤ)) p q
        (dilateReg (-(k : ℤ)) a) =
      restrictionResponseJObservableCubeSet (originCube d ((k + m : ℕ) : ℤ)) p q a := by
  rw [← rescaleReg_eq_dilateReg_neg_nat]
  exact restrictionResponseJObservableCubeSet_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    ha k m p q
/-- Upper multiscale ellipticity moments shift under scale-normalization of the
law. -/
theorem LambdaMomentAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (k m : ℕ) {s : ℝ} (hs : 0 < s) (ξ : ℕ) :
    LambdaMomentAtScale (restrictionScaleNormalizedLaw k P) (m : ℤ) s ξ =
      LambdaMomentAtScale P ((k + m : ℕ) : ℤ) s ξ := by
  unfold LambdaMomentAtScale annealedMomentRoot
  rw [integral_restrictionScaleNormalizedLaw]
  · apply congrArg (fun x : ℝ => x ^ (1 / (ξ : ℝ)))
    apply integral_congr_ae
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    rw [← rescaleReg_eq_dilateReg_neg_nat k]
    rw [LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k m s (.finite 1)]
  · exact ((hP.scaleNormalized k).aemeasurable_LambdaSqCoeffField_finite_one
      (originCube d (m : ℤ)) hs).pow_const ξ |>.aestronglyMeasurable

/-- Lower inverse multiscale ellipticity moments shift under
scale-normalization of the law. -/
theorem lambdaInvMomentAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (k m : ℕ) {s : ℝ} (hs : 0 < s) (ξ : ℕ) :
    lambdaInvMomentAtScale (restrictionScaleNormalizedLaw k P) (m : ℤ) s ξ =
      lambdaInvMomentAtScale P ((k + m : ℕ) : ℤ) s ξ := by
  unfold lambdaInvMomentAtScale annealedMomentRoot
  rw [integral_restrictionScaleNormalizedLaw]
  · apply congrArg (fun x : ℝ => x ^ (1 / (ξ : ℝ)))
    apply integral_congr_ae
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    rw [← rescaleReg_eq_dilateReg_neg_nat k]
    rw [lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k m s (.finite 1)]
  · exact ((hP.scaleNormalized k).aemeasurable_lambdaSqCoeffField_finite_one_inv
      (originCube d (m : ℤ)) hs).pow_const ξ |>.aestronglyMeasurable

/-- The enhanced ellipticity moment contrast shifts under scale-normalization
of the law. -/
theorem widetildeThetaAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (k m : ℕ) {sUpper sLower : ℝ} (hsUpper : 0 < sUpper)
    (hsLower : 0 < sLower) (ξ : ℕ) :
    widetildeThetaAtScale (restrictionScaleNormalizedLaw k P) (m : ℤ) sUpper sLower ξ =
      widetildeThetaAtScale P ((k + m : ℕ) : ℤ) sUpper sLower ξ := by
  simp [widetildeThetaAtScale,
    LambdaMomentAtScale_restrictionScaleNormalizedLaw hP k m hsUpper ξ,
    lambdaInvMomentAtScale_restrictionScaleNormalizedLaw hP k m hsLower ξ]

private theorem smul_one_mat_eq_scalar_eq {d : ℕ} [NeZero d] {r s : ℝ}
    (h : r • (1 : Mat d) = s • (1 : Mat d)) : r = s := by
  classical
  let i : Fin d := Classical.choice (Fin.pos_iff_nonempty.mp (NeZero.pos d))
  have hentry := congrArg (fun M : Mat d => M i i) h
  simpa [Pi.smul_apply, Matrix.one_apply, i] using hentry

/-- The annealed full coarse block matrix shifts under scale-normalization of
the law. -/
theorem annealedBlockMatrixAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (k m : ℕ) :
    annealedBlockMatrixAtScale (restrictionScaleNormalizedLaw k P) (m : ℤ) =
      annealedBlockMatrixAtScale P ((k + m : ℕ) : ℤ) := by
  unfold annealedBlockMatrixAtScale annealedBlockMatrix
  refine Eq.mpr (BlockMat.mk.injEq _ _ _ _ _ _ _ _) ?_
  constructor
  · ext i j
    rw [integral_restrictionScaleNormalizedLaw]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      rw [← rescaleReg_eq_dilateReg_neg_nat k]
      rw [coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic ha k m]
    · exact ((hP.scaleNormalized k).aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
        (originCube d (m : ℤ)) i j).aestronglyMeasurable
  constructor
  · ext i j
    rw [integral_restrictionScaleNormalizedLaw]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      rw [← rescaleReg_eq_dilateReg_neg_nat k]
      rw [coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic ha k m]
    · exact ((hP.scaleNormalized k).aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet
        (originCube d (m : ℤ)) i j).aestronglyMeasurable
  constructor
  · ext i j
    rw [integral_restrictionScaleNormalizedLaw]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      rw [← rescaleReg_eq_dilateReg_neg_nat k]
      rw [coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic ha k m]
    · exact ((hP.scaleNormalized k).aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
        (originCube d (m : ℤ)) i j).aestronglyMeasurable
  · ext i j
    rw [integral_restrictionScaleNormalizedLaw]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      rw [← rescaleReg_eq_dilateReg_neg_nat k]
      rw [coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic ha k m]
    · exact ((hP.scaleNormalized k).aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
        (originCube d (m : ℤ)) i j).aestronglyMeasurable

/-- The annealed upper-left scalar block shifts under scale-normalization of
the law. -/
theorem annealedBAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (k m : ℕ) :
    annealedBAtScale (restrictionScaleNormalizedLaw k P) (m : ℤ) =
      annealedBAtScale P ((k + m : ℕ) : ℤ) := by
  simpa [annealedBAtScale, annealedB, annealedBlockMatrixAtScale] using
    congrArg BlockMat.upperLeft (annealedBlockMatrixAtScale_restrictionScaleNormalizedLaw hP k m)

/-- The annealed inverse-star scalar block shifts under scale-normalization of
the law. -/
theorem annealedSigmaStarInvAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (k m : ℕ) :
    annealedSigmaStarInvAtScale (restrictionScaleNormalizedLaw k P) (m : ℤ) =
      annealedSigmaStarInvAtScale P ((k + m : ℕ) : ℤ) := by
  simpa [annealedSigmaStarInvAtScale, annealedSigmaStarInv, annealedBlockMatrixAtScale] using
    congrArg BlockMat.lowerRight (annealedBlockMatrixAtScale_restrictionScaleNormalizedLaw hP k m)

namespace RestrictionStationaryLaw

/-- Commutation of integer translation with carrier triadic rescaling: rescaling
after translating by `z` equals translating by the `3^k`-scaled integer shift
after rescaling. -/
private theorem translateReg_comp_rescaleReg {d : ℕ} (k : ℕ) (z : Fin d → ℤ) :
    translateReg (intVecToRealVec z) ∘ rescaleReg k
      = rescaleReg k ∘ translateReg (intVecToRealVec (triadicScaleIntShift k z)) := by
  funext a
  apply RegCoeffField.ext
  intro x
  simp only [Function.comp_apply, translateReg_apply, rescaleReg_apply]
  congr 1
  funext i
  simp only [intVecToRealVec, triadicScaleIntShift, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  push_cast
  ring

/-- Stationarity is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : RestrictionStationaryLaw P) (k : ℕ) :
    RestrictionStationaryLaw (restrictionScaleNormalizedLaw k P) := by
  intro z
  rw [restrictionScaleNormalizedLaw_eq_map_rescaleReg,
    Measure.map_map (measurable_translateReg (intVecToRealVec z)) (measurable_rescaleReg k),
    translateReg_comp_rescaleReg k z,
    ← Measure.map_map (measurable_rescaleReg k)
      (measurable_translateReg (intVecToRealVec (triadicScaleIntShift k z))),
    hP (triadicScaleIntShift k z)]

end RestrictionStationaryLaw

namespace RestrictionIsotropicLaw

/-- Commutation of signed-permutation rotation with carrier triadic rescaling. -/
private theorem rotateReg_comp_rescaleReg {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (k : ℕ) :
    rotateReg R hR ∘ rescaleReg k = rescaleReg k ∘ rotateReg R hR := by
  funext a
  apply RegCoeffField.ext
  intro x
  simp only [Function.comp_apply, rotateReg_apply, rescaleReg_apply, matVecMul_smul]

/-- Isotropy under signed permutations is preserved by triadic
scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : RestrictionIsotropicLaw P) (k : ℕ) :
    RestrictionIsotropicLaw (restrictionScaleNormalizedLaw k P) := by
  intro R hR
  rw [restrictionScaleNormalizedLaw_eq_map_rescaleReg,
    Measure.map_map (measurable_rotateReg R hR) (measurable_rescaleReg k),
    rotateReg_comp_rescaleReg R hR k,
    ← Measure.map_map (measurable_rescaleReg k) (measurable_rotateReg R hR),
    hP R hR]

end RestrictionIsotropicLaw

namespace RestrictionAdjointInvariantLaw

/-- Commutation of the entrywise adjoint with carrier triadic rescaling. -/
private theorem adjointReg_comp_rescaleReg {d : ℕ} (k : ℕ) :
    adjointReg ∘ rescaleReg (d := d) k = rescaleReg k ∘ adjointReg := by
  funext a
  apply RegCoeffField.ext
  intro x
  simp only [Function.comp_apply, adjointReg_apply, rescaleReg_apply]

/-- Adjoint invariance is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : RestrictionAdjointInvariantLaw P) (k : ℕ) :
    RestrictionAdjointInvariantLaw (restrictionScaleNormalizedLaw k P) := by
  show Measure.map adjointReg (restrictionScaleNormalizedLaw k P) = restrictionScaleNormalizedLaw k P
  rw [restrictionScaleNormalizedLaw_eq_map_rescaleReg,
    Measure.map_map measurable_adjointReg (measurable_rescaleReg k),
    adjointReg_comp_rescaleReg k,
    ← Measure.map_map (measurable_rescaleReg k) measurable_adjointReg,
    hP]

end RestrictionAdjointInvariantLaw

namespace RestrictionStructuralLaw

/-- The full structural law package is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : RestrictionCoeffLaw d}
    (hP : RestrictionStructuralLaw P) (k : ℕ) :
    RestrictionStructuralLaw (restrictionScaleNormalizedLaw k P) where
  stationary := hP.stationary.scaleNormalized k
  unit_range := RestrictionUnitRangeDependentLaw.scaleNormalized hP.unit_range k
  isotropic := hP.isotropic.scaleNormalized k
  adjoint_invariant := hP.adjoint_invariant.scaleNormalized k

end RestrictionStructuralLaw

namespace RestrictionLawCarrier

/-- The primitive upper-left structural scalar shifts under
scale-normalization. -/
theorem barBAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).barBAtScale (hStruct.scaleNormalized k) (m : ℤ) =
      hP.barBAtScale hStruct ((k + m : ℕ) : ℤ) := by
  apply smul_one_mat_eq_scalar_eq (d := d)
  calc
    (hP.scaleNormalized k).barBAtScale (hStruct.scaleNormalized k) (m : ℤ) • (1 : Mat d)
        = annealedBAtScale (restrictionScaleNormalizedLaw k P) (m : ℤ) :=
          ((hP.scaleNormalized k).annealedBAtScale_eq_barBAtScale
            (hStruct.scaleNormalized k) (m : ℤ)).symm
    _ = annealedBAtScale P ((k + m : ℕ) : ℤ) :=
          annealedBAtScale_restrictionScaleNormalizedLaw hP k m
    _ = hP.barBAtScale hStruct ((k + m : ℕ) : ℤ) • (1 : Mat d) :=
          hP.annealedBAtScale_eq_barBAtScale hStruct ((k + m : ℕ) : ℤ)

/-- The primitive inverse-star structural scalar shifts under
scale-normalization. -/
theorem barSigmaStarInvAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).barSigmaStarInvAtScale
        (hStruct.scaleNormalized k) (m : ℤ) =
      hP.barSigmaStarInvAtScale hStruct ((k + m : ℕ) : ℤ) := by
  apply smul_one_mat_eq_scalar_eq (d := d)
  calc
    (hP.scaleNormalized k).barSigmaStarInvAtScale
          (hStruct.scaleNormalized k) (m : ℤ) • (1 : Mat d)
        = annealedSigmaStarInvAtScale (restrictionScaleNormalizedLaw k P) (m : ℤ) :=
          ((hP.scaleNormalized k).annealedSigmaStarInvAtScale_eq_barSigmaStarInvAtScale
            (hStruct.scaleNormalized k) (m : ℤ)).symm
    _ = annealedSigmaStarInvAtScale P ((k + m : ℕ) : ℤ) :=
          annealedSigmaStarInvAtScale_restrictionScaleNormalizedLaw hP k m
    _ = hP.barSigmaStarInvAtScale hStruct ((k + m : ℕ) : ℤ) • (1 : Mat d) :=
          hP.annealedSigmaStarInvAtScale_eq_barSigmaStarInvAtScale hStruct
            ((k + m : ℕ) : ℤ)

/-- The structural-law scalar `\bar\sigma` shifts under scale-normalization. -/
theorem barSigmaAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).barSigmaAtScale (hStruct.scaleNormalized k) (m : ℤ) =
      hP.barSigmaAtScale hStruct ((k + m : ℕ) : ℤ) := by
  calc
    (hP.scaleNormalized k).barSigmaAtScale (hStruct.scaleNormalized k) (m : ℤ)
        = (hP.scaleNormalized k).barBAtScale (hStruct.scaleNormalized k) (m : ℤ) :=
          (hP.scaleNormalized k).barSigmaAtScale_eq_barBAtScale
            (hStruct.scaleNormalized k) (m : ℤ)
    _ = hP.barBAtScale hStruct ((k + m : ℕ) : ℤ) :=
          hP.barBAtScale_restrictionScaleNormalizedLaw hStruct k m
    _ = hP.barSigmaAtScale hStruct ((k + m : ℕ) : ℤ) :=
          (hP.barSigmaAtScale_eq_barBAtScale hStruct ((k + m : ℕ) : ℤ)).symm

/-- The structural-law scalar `\bar\sigma_*` shifts under scale-normalization. -/
theorem barSigmaStarAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).barSigmaStarAtScale
        (hStruct.scaleNormalized k) (m : ℤ) =
      hP.barSigmaStarAtScale hStruct ((k + m : ℕ) : ℤ) := by
  calc
    (hP.scaleNormalized k).barSigmaStarAtScale (hStruct.scaleNormalized k) (m : ℤ)
        = ((hP.scaleNormalized k).barSigmaStarInvAtScale
            (hStruct.scaleNormalized k) (m : ℤ))⁻¹ :=
          (hP.scaleNormalized k).barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale
            (hStruct.scaleNormalized k) (m : ℤ)
    _ = (hP.barSigmaStarInvAtScale hStruct ((k + m : ℕ) : ℤ))⁻¹ := by
          rw [hP.barSigmaStarInvAtScale_restrictionScaleNormalizedLaw hStruct k m]
    _ = hP.barSigmaStarAtScale hStruct ((k + m : ℕ) : ℤ) :=
          (hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct
            ((k + m : ℕ) : ℤ)).symm

/-- The structural-law contrast `\Theta` shifts under scale-normalization. -/
theorem thetaAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).thetaAtScale (hStruct.scaleNormalized k) (m : ℤ) =
      hP.thetaAtScale hStruct ((k + m : ℕ) : ℤ) := by
  simp [RestrictionLawCarrier.thetaAtScale,
    hP.barSigmaAtScale_restrictionScaleNormalizedLaw hStruct k m,
    hP.barSigmaStarAtScale_restrictionScaleNormalizedLaw hStruct k m]

end RestrictionLawCarrier

end

end Ch04
end Book
end Homogenization
