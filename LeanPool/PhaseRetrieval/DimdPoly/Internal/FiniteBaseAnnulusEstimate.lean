/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.FiniteBaseCircleEstimate
import LeanPool.PhaseRetrieval.DimdPoly.Internal.ProductAnnulusLocalization
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ProductAnnulusCircle

/-! # FiniteBaseAnnulusEstimate -/


noncomputable section

open MeasureTheory

namespace DimdPolyLEAN

/-!
# FiniteBaseAnnulusEstimate

Finite annulus-side transfer theorem for a normalized base point in `Pkappa`.
-/

private theorem lowAnnulusMass_nonneg_wip
    {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Skappa d kappa) :
    0 <= lowAnnulusMass J F := by
  unfold lowAnnulusMass annulusMass
  refine Finset.sum_nonneg ?_
  intro j hj
  exact MeasureTheory.integral_nonneg fun z => by
    by_cases hz : z ∈ productAnnulus j
    · simp [Set.indicator, hz]
    · simp [Set.indicator, hz]

private theorem annulusMass_nonneg_annulus
    {d : Nat} {kappa : MultiIndex d} (j : Idx d) (F : Skappa d kappa) :
    0 <= annulusMass j F := by
  unfold annulusMass
  exact MeasureTheory.integral_nonneg fun z => by
    by_cases hz : z ∈ productAnnulus j
    · simp [Set.indicator, hz]
    · simp [Set.indicator, hz]

private theorem highAnnulusMass_le_norm_sq_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (H : Pkappa d kappa) :
    highAnnulusMass J (ofPkappa kappa H) <= ‖H‖ ^ 2 := by
  have hpart := annulusMassPartition hd kappa J H
  have hlow : 0 <= lowAnnulusMass J (ofPkappa kappa H) :=
    lowAnnulusMass_nonneg_wip J (ofPkappa kappa H)
  linarith

private theorem defect_nonneg_annulus
    {d : Nat} {kappa : MultiIndex d} (F G : Pkappa d kappa) :
    0 <= defect F G := by
  exact Real.sqrt_nonneg _

private theorem toFun_ofPkappa_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa F) = evalPkappa kappa F := by
  let _ := hd
  ext z
  rw [toFun, evalPkappa, Finsupp.sum]
  have hzero :
      ∀ alpha ∉ F.support,
        coeffSkappa (ofPkappa kappa F) alpha * Phi kappa alpha z = 0 := by
    intro alpha halpha
    simp [coeffSkappa, ofPkappa, Finsupp.notMem_support_iff.mp halpha]
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [coeffSkappa, ofPkappa]

private lemma continuous_Phi_annulus
    {d : Nat} (kappa alpha : MultiIndex d) :
    Continuous (Phi kappa alpha) := by
  unfold Phi phi1D complexHermite
  continuity

private lemma continuous_evalPkappa_annulus
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Continuous (evalPkappa kappa F) := by
  unfold evalPkappa
  refine continuous_finsetSum _ ?_
  intro alpha halpha
  exact continuous_const.mul (continuous_Phi_annulus kappa alpha)

private lemma measurableSet_productAnnulus_annulus
    {d : Nat} (j : Idx d) :
    MeasurableSet (productAnnulus j) := by
  have h :
      MeasurableSet
        (⋂ q : Fin d,
          {z : Cd d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1}) := by
    refine MeasurableSet.iInter (ι := Fin d) ?_
    intro q
    have hge :
        MeasurableSet {z : Cd d | (j q : ℝ) ≤ ‖z q‖} := by
      exact measurableSet_le measurable_const
        (measurable_norm.comp (continuous_apply q).measurable)
    have hlt :
        MeasurableSet {z : Cd d | ‖z q‖ < (j q : ℝ) + 1} := by
      exact measurableSet_lt
        (measurable_norm.comp (continuous_apply q).measurable) measurable_const
    simpa [Set.setOf_and] using hge.inter hlt
  simpa [productAnnulus, Set.setOf_forall] using h

private def mulCircleLIE_annulus (ω : _root_.Circle) : ℂ ≃ₗᵢ[ℝ] ℂ := by
  refine LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective
      (LinearMap.mulLeft ℝ ((ω : ℂ)))
      ?_)
    ?_
  · refine ⟨?inj, ?surj⟩
    · intro x y hxy
      exact mul_left_cancel₀ (Circle.coe_ne_zero ω) (by simpa using hxy)
    · intro z
      refine ⟨((ω⁻¹ : _root_.Circle) : ℂ) * z, ?_⟩
      simp
  · intro z
    simp

private lemma productAnnulus_rotate_one_iff_annulus
    {d : Nat} (j : Idx d) (q0 : Fin d) (ω : _root_.Circle) (z : Cd d) :
    Function.update z q0 ((ω : ℂ) * z q0) ∈ productAnnulus j ↔
      z ∈ productAnnulus j := by
  have hω : ‖(ω : ℂ)‖ = 1 := _root_.Circle.norm_coe ω
  constructor <;> intro hz <;> intro q
  · by_cases hq : q = q0
    · subst hq
      simpa [productAnnulus, Function.update, Complex.norm_mul, hω] using hz q
    · simpa [productAnnulus, Function.update, hq] using hz q
  · by_cases hq : q = q0
    · subst hq
      simpa [productAnnulus, Function.update, Complex.norm_mul, hω] using hz q
    · simpa [productAnnulus, Function.update, hq] using hz q

private lemma rotate_one_volume_preserving_annulus
    {d : Nat} (q0 : Fin d) (ω : _root_.Circle) :
    MeasurePreserving
      (fun z : Cd d => Function.update z q0 ((ω : ℂ) * z q0))
      (volume : Measure (Cd d)) (volume : Measure (Cd d)) := by
  classical
  let f : Fin d → ℂ → ℂ := fun i => if h : i = q0 then fun z => (ω : ℂ) * z else id
  have hf : ∀ i : Fin d, MeasurePreserving (f i) (volume : Measure ℂ) (volume : Measure ℂ) := by
    intro i
    by_cases h : i = q0
    · subst h
      have hmp := (mulCircleLIE_annulus ω).measurePreserving
      have hfeq : ⇑(mulCircleLIE_annulus ω) = f i := by
        funext z
        simp only [f, dite_true]
        rfl
      rw [hfeq] at hmp
      exact hmp
    · simpa [f, h] using
        (show MeasurePreserving (id : ℂ → ℂ) (volume : Measure ℂ) (volume : Measure ℂ) from
          ⟨measurable_id, by simp⟩)
  have hpi :
      MeasurePreserving
        (fun z : Cd d => fun i => f i (z i))
        (volume : Measure (Cd d)) (volume : Measure (Cd d)) := by
    simpa [MeasureTheory.Measure.pi, f] using
      (MeasureTheory.volume_preserving_pi (f := f) hf)
  have hfun :
      (fun z : Cd d => fun i => f i (z i)) =
        fun z => Function.update z q0 ((ω : ℂ) * z q0) := by
    funext z i
    by_cases h : i = q0
    · subst h
      simp [f]
    · simp [f, h]
  simpa [hfun] using hpi

private lemma rotate_one_measurableEmbedding_annulus
    {d : Nat} (q0 : Fin d) (ω : _root_.Circle) :
    MeasurableEmbedding (fun z : Cd d => Function.update z q0 ((ω : ℂ) * z q0)) := by
  classical
  let f : Cd d → Cd d := fun z => Function.update z q0 ((ω : ℂ) * z q0)
  let g : Cd d → Cd d := fun z => Function.update z q0 (((ω⁻¹ : _root_.Circle) : ℂ) * z q0)
  have hf : Measurable f := by
    fun_prop
  have hcont : Continuous f := by
    fun_prop
  have hgf : Function.LeftInverse g f := by
    intro z
    funext q
    by_cases hq : q = q0
    · subst hq
      simp [f, g, Function.update]
    · simp [f, g, Function.update, hq]
  have hrange : MeasurableSet (Set.range f) :=
    MeasureTheory.measurableSet_range_of_continuous_injective hcont hgf.injective
  exact MeasurableEmbedding.of_measurable_inverse hf hrange (by fun_prop) hgf

private lemma rotate_one_gamma_preserving_annulus
    {d : Nat} (q0 : Fin d) (ω : _root_.Circle) :
    MeasurePreserving
      (fun z : Cd d => Function.update z q0 ((ω : ℂ) * z q0))
      (gammaD d) (gammaD d) := by
  classical
  let dens : Cd d → ENNReal := fun z => ENNReal.ofReal (gaussianDensity d z)
  let f : Cd d → Cd d := fun z => Function.update z q0 ((ω : ℂ) * z q0)
  have hvol : MeasurePreserving f (volume : Measure (Cd d)) (volume : Measure (Cd d)) := by
    simpa [f] using (rotate_one_volume_preserving_annulus (q0 := q0) (ω := ω))
  have hmeas : MeasurableEmbedding f :=
    rotate_one_measurableEmbedding_annulus (q0 := q0) (ω := ω)
  have hdens : ∀ z : Cd d, dens (f z) = dens z := by
    intro z
    have hsum :
        ∑ q : Fin d, ‖Function.update z q0 ((ω : ℂ) * z q0) q‖ ^ 2 =
          ∑ q : Fin d, ‖z q‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      by_cases h : q = q0
      · subst h
        simp [Function.update]
      · simp [Function.update, h]
    simp [dens, f, gaussianDensity, hsum]
  have hmap : Measure.map f (gammaD d) = gammaD d := by
    change Measure.map f (volume.withDensity dens) = volume.withDensity dens
    ext s hs
    have hs' : MeasurableSet (f ⁻¹' s) := by
      exact measurableSet_preimage hmeas.measurable hs
    rw [Measure.map_apply_of_aemeasurable hmeas.measurable.aemeasurable hs,
      withDensity_apply _ hs', withDensity_apply _ hs]
    rw [← MeasureTheory.lintegral_indicator (hs := hs')]
    rw [← MeasureTheory.lintegral_indicator (hs := hs)]
    simpa [Set.preimage, Set.indicator, Set.mem_setOf_eq, dens, f, hdens] using
      (hvol.lintegral_comp_emb hmeas (fun x => if x ∈ s then dens x else 0))
  exact ⟨hmeas.measurable, hmap⟩

private lemma gamma_lintegral_rotate_one_eq_annulus
    {d : Nat} (q0 : Fin d) (ω : _root_.Circle) (g : Cd d → ENNReal) :
    ∫⁻ z : Cd d, g (Function.update z q0 ((ω : ℂ) * z q0)) ∂ gammaD d =
      ∫⁻ z : Cd d, g z ∂ gammaD d := by
  have hgauss := rotate_one_gamma_preserving_annulus (d := d) (q0 := q0) (ω := ω)
  have hmeas := rotate_one_measurableEmbedding_annulus (d := d) (q0 := q0) (ω := ω)
  simpa using hgauss.lintegral_comp_emb hmeas g

private theorem annulusCoordinateRotationAveraging
    {d : Nat} (j : Idx d) (q0 : Fin d) (F : Cd d → ENNReal) (hF : Measurable F) :
    by
      classical
      exact
        ∫⁻ z : Cd d,
            if z ∈ productAnnulus j then
              ∫⁻ x : Circle,
                  F (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))
                ∂ AddCircle.haarAddCircle
            else 0
          ∂ gammaD d =
        ∫⁻ z : Cd d, if z ∈ productAnnulus j then F z else 0 ∂ gammaD d := by
  classical
  let G : Cd d → ENNReal := fun z => if z ∈ productAnnulus j then F z else 0
  have hG : Measurable G := by
    refine hF.piecewise (measurableSet_productAnnulus_annulus j) measurable_const
  letI : MeasureTheory.SFinite (gammaD d) := by
    change MeasureTheory.SFinite
      ((volume : Measure (Cd d)).withDensity (fun z => ENNReal.ofReal (gaussianDensity d z)))
    infer_instance
  calc
    ∫⁻ z : Cd d,
        if z ∈ productAnnulus j then
          ∫⁻ x : Circle,
              F (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))
            ∂ AddCircle.haarAddCircle
        else 0
      ∂ gammaD d
      = ∫⁻ z : Cd d,
          ∫⁻ x : Circle,
              G (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))
            ∂ AddCircle.haarAddCircle
          ∂ gammaD d := by
            refine lintegral_congr_ae ?_
            filter_upwards with z
            by_cases hz : z ∈ productAnnulus j
            · simp only [hz, ↓reduceIte, fourier_apply, one_smul]
              refine lintegral_congr_ae ?_
              filter_upwards with x
              have hrot :
                  Function.update z q0
                      (((AddCircle.toCircle x : _root_.Circle) : ℂ) * z q0) ∈
                    productAnnulus j :=
                (productAnnulus_rotate_one_iff_annulus (j := j) (q0 := q0)
                  (ω := AddCircle.toCircle x) (z := z)).2 hz
              have hrot' :
                  Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0) ∈
                    productAnnulus j := by
                simpa [fourier_one] using hrot
              simp only [G]
              split_ifs with hmem
              · rfl
              · exact (hmem hrot).elim
            · have hzero :
                ∫⁻ x : Circle,
                    G (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))
                  ∂ AddCircle.haarAddCircle = 0 := by
                    calc
                      ∫⁻ x : Circle,
                          G (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))
                        ∂ AddCircle.haarAddCircle
                        = ∫⁻ x : Circle, (0 : ENNReal) ∂ AddCircle.haarAddCircle := by
                            refine lintegral_congr_ae ?_
                            filter_upwards with x
                            have hrot :
                                Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0) ∉
                                  productAnnulus j := by
                                    intro hz'
                                    have hz'' :
                                        Function.update z q0
                                            (((AddCircle.toCircle x : _root_.Circle) : ℂ) *
                                              z q0) ∈ productAnnulus j := by
                                          simpa [fourier_one] using hz'
                                    exact hz
                                      ((productAnnulus_rotate_one_iff_annulus (j := j) (q0 := q0)
                                        (ω := AddCircle.toCircle x) (z := z)).1 hz'')
                            simp only [G]
                            split_ifs with hmem
                            · exact (hrot hmem).elim
                            · rfl
                      _ = 0 := by simp
              simpa [hz] using hzero.symm
    _ = ∫⁻ x : Circle,
          ∫⁻ z : Cd d,
              G (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))
            ∂ gammaD d
        ∂ AddCircle.haarAddCircle := by
          rw [MeasureTheory.lintegral_lintegral_swap]
          have hpair :
              Measurable (fun p : Cd d × Circle =>
                G (Function.update p.1 q0 ((fourier (1 : Int) p.2 : ℂ) * p.1 q0))) := by
            refine hG.comp ?_
            fun_prop
          exact hpair.aemeasurable
    _ = ∫⁻ x : Circle,
          ∫⁻ z : Cd d, G z ∂ gammaD d
        ∂ AddCircle.haarAddCircle := by
          refine lintegral_congr_ae ?_
          filter_upwards with x
          simpa [fourier_one] using
            (gamma_lintegral_rotate_one_eq_annulus
              (d := d) (q0 := q0) (ω := AddCircle.toCircle x) (g := G))
    _ = ∫⁻ z : Cd d, G z ∂ gammaD d := by
          rw [lintegral_const]
          simp
    _ = ∫⁻ z : Cd d, if z ∈ productAnnulus j then F z else 0 ∂ gammaD d := by
          rfl

private theorem exists_maxCoord_annulus
    {d : Nat} (hd : 0 < d) (j : Idx d) :
    ∃ q0 : Fin d, ∀ q : Fin d, j q ≤ j q0 := by
  let q0 : Fin d := ⟨0, hd⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨q0, Finset.mem_univ q0⟩
  rcases Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d))) hne
      (f := fun q : Fin d => j q) with ⟨qmax, hqmax, hsup⟩
  refine ⟨qmax, ?_⟩
  intro q
  have hq_le : j q ≤ (Finset.univ : Finset (Fin d)).sup (fun r : Fin d => j r) :=
    Finset.le_sup (s := Finset.univ) (f := fun r : Fin d => j r) (by simp)
  simpa [hsup] using hq_le

private noncomputable def maxCoordAnnulus
    {d : Nat} (hd : 0 < d) (j : Idx d) : Fin d :=
  Classical.choose (exists_maxCoord_annulus hd j)

private theorem maxCoordAnnulus_spec
    {d : Nat} (hd : 0 < d) (j : Idx d) :
    ∀ q : Fin d, j q ≤ j (maxCoordAnnulus hd j) :=
  Classical.choose_spec (exists_maxCoord_annulus hd j)

private def annulusBandStart
    {d : Nat} (j : Idx d) (q : Fin d) (M : Nat) : Nat :=
  (max (j q) M - M) ^ 2

private def annulusBandLength
    {d : Nat} (j : Idx d) (q : Fin d) (M : Nat) : Nat :=
  (j q + M + 1) ^ 2 - annulusBandStart j q M

private theorem annulusBandStart_le_top
    {d : Nat} (j : Idx d) (q : Fin d) (M : Nat) :
    annulusBandStart j q M ≤ (j q + M + 1) ^ 2 := by
  unfold annulusBandStart
  have hbase : max (j q) M - M ≤ j q + M + 1 := by
    omega
  exact Nat.pow_le_pow_left hbase 2

private theorem annulusBandStart_add_length
    {d : Nat} (j : Idx d) (q : Fin d) (M : Nat) :
    annulusBandStart j q M + annulusBandLength j q M = (j q + M + 1) ^ 2 := by
  unfold annulusBandLength
  exact Nat.add_sub_of_le (annulusBandStart_le_top j q M)

private theorem annulusBandLength_pos
    {d : Nat} (j : Idx d) (q : Fin d) (M : Nat) :
    1 ≤ annulusBandLength j q M := by
  unfold annulusBandLength annulusBandStart
  have hbase_lt : max (j q) M - M < j q + M + 1 := by
    omega
  have hsq_lt :
      (max (j q) M - M) ^ 2 < (j q + M + 1) ^ 2 :=
    Nat.pow_lt_pow_left hbase_lt (by norm_num : 2 ≠ 0)
  have hsub_pos :
      0 < (j q + M + 1) ^ 2 - (max (j q) M - M) ^ 2 :=
    Nat.sub_pos_of_lt hsq_lt
  omega

private theorem norm_nonneg_pkappa_annulus
    {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) :
    0 ≤ ‖F‖ := by
  exact Real.sqrt_nonneg _

private theorem norm_ne_zero_of_ne_zero_pkappa_annulus
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF : F ≠ 0) :
    ‖F‖ ≠ 0 := by
  intro hnorm
  apply hF
  ext alpha
  by_cases hmem : alpha ∈ F.support
  · have hcoeff_ne : F alpha ≠ 0 := Finsupp.mem_support_iff.mp hmem
    have hle :
        ‖F alpha‖ ^ 2 ≤ Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) := by
      simpa using
        (Finset.single_le_sum
          (f := fun a : Idx d => ‖F a‖ ^ 2) (s := F.support) (a := alpha)
          (fun a _ => by positivity) hmem)
    have hterm_pos : 0 < ‖F alpha‖ ^ 2 := by
      have hnorm_pos : 0 < ‖F alpha‖ := norm_pos_iff.mpr hcoeff_ne
      nlinarith
    have hsum_pos : 0 < Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) :=
      lt_of_lt_of_le hterm_pos hle
    change Real.sqrt (Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2)) = 0 at hnorm
    have hsqrt_pos :
        0 < Real.sqrt (Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2)) :=
      Real.sqrt_pos.mpr hsum_pos
    linarith
  · exact Finsupp.notMem_support_iff.mp hmem

private theorem integrable_evalPkappa_sq_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Integrable (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
  by_cases hF : F = 0
  · subst hF
    simp [evalPkappa]
  · have hmeas :
        AEStronglyMeasurable (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) :=
      ((continuous_evalPkappa_annulus kappa F).norm.pow 2).stronglyMeasurable.aestronglyMeasurable
    by_contra hInt
    have hundef :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = 0 :=
      MeasureTheory.integral_undef hInt
    have hmass :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = ‖F‖ ^ 2 :=
      evalPkappa_total_mass hd kappa F
    have hnorm_ne : ‖F‖ ≠ 0 := norm_ne_zero_of_ne_zero_pkappa_annulus hF
    have hpos : 0 < ‖F‖ ^ 2 := by
      have hnorm_pos : 0 < ‖F‖ :=
        lt_of_le_of_ne (norm_nonneg_pkappa_annulus F) hnorm_ne.symm
      nlinarith
    linarith

private theorem evalPkappa_add_apply_annulus
    {d : Nat} (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa (F + G) z = evalPkappa kappa F z + evalPkappa kappa G z := by
  unfold evalPkappa
  rw [Finsupp.sum_add_index'] <;> simp [add_mul]

private theorem integrable_coordFiber_evalPkappa_sq_annulus
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (H : Pkappa d kappa) (z : Cd d) :
    Integrable
      (fun x : Circle =>
        ‖evalPkappa kappa H
          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ ^ 2)
      AddCircle.haarAddCircle := by
  have hcont_update :
      Continuous (fun x : Circle =>
        Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) := by
    fun_prop
  have hcont :
      Continuous (fun x : Circle =>
        ‖evalPkappa kappa H
          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ ^ 2) :=
    (((continuous_evalPkappa_annulus kappa H).comp hcont_update).norm.pow 2)
  exact integrableOn_univ.mp
    (hcont.continuousOn.integrableOn_compact (μ := AddCircle.haarAddCircle) isCompact_univ)

private theorem coordFiber_mass_lintegral_annulus
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (H : Pkappa d kappa) (z : Cd d) :
    ∫⁻ x : Circle,
        ENNReal.ofReal
          (‖evalPkappa kappa H
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ ^ 2)
        ∂ AddCircle.haarAddCircle =
      ENNReal.ofReal
        (circleL2Sq
          (fun x : Circle =>
            evalPkappa kappa H
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)))) := by
  rw [circleL2Sq]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_coordFiber_evalPkappa_sq_annulus (kappa := kappa) (q0 := q0) H z)
    (ae_of_all _ (fun x => sq_nonneg _))).symm

private theorem annulusMass_eq_coordFiber_average_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (j : Idx d) (q0 : Fin d) (H : Pkappa d kappa) :
    ENNReal.ofReal (annulusMass j (ofPkappa kappa H)) =
      ∫⁻ z : Cd d,
        Set.indicator (productAnnulus j)
          (fun z =>
            ENNReal.ofReal
              (circleL2Sq
                (fun x : Circle =>
                  evalPkappa kappa H
                    (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))))) z
        ∂ gammaD d := by
  classical
  have hmass_int :
      Integrable
        ((productAnnulus j).indicator
          (fun z : Cd d => ‖evalPkappa kappa H z‖ ^ 2))
        (gammaD d) :=
    (integrable_evalPkappa_sq_annulus hd kappa H).indicator
      (measurableSet_productAnnulus_annulus j)
  have hmass0 :
      ENNReal.ofReal (annulusMass j (ofPkappa kappa H)) =
        ∫⁻ z : Cd d,
          ENNReal.ofReal
            ((productAnnulus j).indicator
              (fun z : Cd d => ‖evalPkappa kappa H z‖ ^ 2) z)
        ∂ gammaD d := by
    simpa [annulusMass, toFun_ofPkappa_annulus hd kappa H, Set.indicator] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmass_int
        (ae_of_all _ (by
          intro z
          by_cases hz : z ∈ productAnnulus j <;> simp [Set.indicator, hz])))
  have hFmass :
      Measurable (fun z : Cd d => ENNReal.ofReal (‖evalPkappa kappa H z‖ ^ 2)) := by
    exact ENNReal.measurable_ofReal.comp
      ((continuous_evalPkappa_annulus kappa H).norm.pow 2).measurable
  have havg :=
    annulusCoordinateRotationAveraging (j := j) (q0 := q0)
      (F := fun z : Cd d => ENNReal.ofReal (‖evalPkappa kappa H z‖ ^ 2)) hFmass
  have hmass_indicator :
      ∫⁻ z : Cd d,
          ENNReal.ofReal
            ((productAnnulus j).indicator
              (fun z : Cd d => ‖evalPkappa kappa H z‖ ^ 2) z)
        ∂ gammaD d
        =
      ∫⁻ z : Cd d,
          if z ∈ productAnnulus j then
            ENNReal.ofReal (‖evalPkappa kappa H z‖ ^ 2)
          else 0
        ∂ gammaD d := by
    refine lintegral_congr_ae ?_
    filter_upwards with z
    by_cases hz : z ∈ productAnnulus j <;> simp [Set.indicator, hz]
  calc
    ENNReal.ofReal (annulusMass j (ofPkappa kappa H))
        =
      ∫⁻ z : Cd d,
          if z ∈ productAnnulus j then
            ∫⁻ x : Circle,
              ENNReal.ofReal
                (‖evalPkappa kappa H
                  (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ ^ 2)
            ∂ AddCircle.haarAddCircle
          else 0
        ∂ gammaD d := by
          rw [hmass0]
          rw [hmass_indicator]
          exact havg.symm
    _ = ∫⁻ z : Cd d,
          Set.indicator (productAnnulus j)
            (fun z =>
              ENNReal.ofReal
                (circleL2Sq
                  (fun x : Circle =>
                    evalPkappa kappa H
                      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))))) z
        ∂ gammaD d := by
          refine lintegral_congr_ae ?_
          filter_upwards with z
          by_cases hz : z ∈ productAnnulus j
          · simpa [Set.indicator, hz] using
              (coordFiber_mass_lintegral_annulus (kappa := kappa) (q0 := q0) H z)
          · simp [Set.indicator, hz]

private def localPartPkappa
    {d : Nat} {kappa : MultiIndex d}
    (j : Idx d) (M : Nat) (G : Pkappa d kappa) : Pkappa d kappa :=
  (Hermite1DimdLEAN.localPart j M ⟨G⟩).coeff

private def remainderPartPkappa
    {d : Nat} {kappa : MultiIndex d}
    (j : Idx d) (M : Nat) (G : Pkappa d kappa) : Pkappa d kappa :=
  (Hermite1DimdLEAN.remainderPart j M ⟨G⟩).coeff

private theorem localPartPkappa_add_remainderPart
    {d : Nat} {kappa : MultiIndex d} (j : Idx d) (M : Nat)
    (G : Pkappa d kappa) :
    localPartPkappa j M G + remainderPartPkappa j M G = G := by
  ext alpha
  unfold localPartPkappa remainderPartPkappa
  unfold Hermite1DimdLEAN.localPart Hermite1DimdLEAN.remainderPart
  by_cases hdist :
      Hermite1DimdLEAN.blockDistance j (Hermite1DimdLEAN.blockIndexMulti alpha) ≤ M
  · have hnlt :
        ¬ M < Hermite1DimdLEAN.blockDistance j
            (Hermite1DimdLEAN.blockIndexMulti alpha) := by
      omega
    simp [Hermite1DimdLEAN.localCoeffSet, Hermite1DimdLEAN.farCoeffSet,
      Hermite1DimdLEAN.FiniteHermiteSum.support, hdist, hnlt]
  · have hlt :
        M < Hermite1DimdLEAN.blockDistance j
            (Hermite1DimdLEAN.blockIndexMulti alpha) :=
      Nat.lt_of_not_ge hdist
    simp [Hermite1DimdLEAN.localCoeffSet, Hermite1DimdLEAN.farCoeffSet,
      Hermite1DimdLEAN.FiniteHermiteSum.support, hdist, hlt]

private theorem localPart_add_remainderPart_evalPkappa
    {d : Nat} {kappa : MultiIndex d} (j : Idx d) (M : Nat)
    (G : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa (localPartPkappa j M G) z +
        evalPkappa kappa (remainderPartPkappa j M G) z =
      evalPkappa kappa G z := by
  rw [← evalPkappa_add_apply_annulus kappa (localPartPkappa j M G)
    (remainderPartPkappa j M G) z]
  rw [localPartPkappa_add_remainderPart]

private theorem localPartPkappa_support_blockDistance_le
    {d : Nat} {kappa : MultiIndex d} {j : Idx d} {M : Nat}
    {G : Pkappa d kappa} {alpha : Idx d}
    (halpha : alpha ∈ (localPartPkappa j M G).support) :
    Hermite1DimdLEAN.blockDistance j (Hermite1DimdLEAN.blockIndexMulti alpha) ≤ M := by
  have hsupport :
      (Hermite1DimdLEAN.localPart j M ⟨G⟩).support =
        Hermite1DimdLEAN.localCoeffSet j M ⟨G⟩ :=
    (Hermite1DimdLEAN.explicitLocalAndFarSupport (j := j) (M := M) (G := ⟨G⟩)).2.2.1
  have halpha_local :
      alpha ∈ Hermite1DimdLEAN.localCoeffSet j M ⟨G⟩ := by
    have halpha_support :
        alpha ∈ (Hermite1DimdLEAN.localPart j M ⟨G⟩).support := by
      simpa [localPartPkappa, Hermite1DimdLEAN.FiniteHermiteSum.support] using halpha
    simpa [hsupport] using halpha_support
  exact (Finset.mem_filter.mp halpha_local).2

private theorem localPartPkappa_coord_band
    {d : Nat} {kappa : MultiIndex d} {j : Idx d} {M : Nat}
    {G : Pkappa d kappa} {alpha : Idx d}
    (halpha : alpha ∈ (localPartPkappa j M G).support) (q : Fin d) :
    annulusBandStart j q M ≤ alpha q ∧
      alpha q < annulusBandStart j q M + annulusBandLength j q M := by
  have hdist :
      Hermite1DimdLEAN.blockDistance j (Hermite1DimdLEAN.blockIndexMulti alpha) ≤ M :=
    localPartPkappa_support_blockDistance_le (j := j) (M := M) (G := G) halpha
  have hqdist :
      Nat.dist (j q) (Hermite1DimdLEAN.blockIndexMulti alpha q) ≤ M := by
    have hle :
        Nat.dist (j q) (Hermite1DimdLEAN.blockIndexMulti alpha q) ≤
          Hermite1DimdLEAN.blockDistance j (Hermite1DimdLEAN.blockIndexMulti alpha) := by
      dsimp [Hermite1DimdLEAN.blockDistance]
      exact Finset.le_sup (s := Finset.univ)
        (f := fun q : Fin d =>
          Nat.dist (j q) (Hermite1DimdLEAN.blockIndexMulti alpha q)) (by simp)
    exact le_trans hle hdist
  have hidx_upper : Hermite1DimdLEAN.blockIndexMulti alpha q ≤ j q + M := by
    have htri :
        Hermite1DimdLEAN.blockIndexMulti alpha q ≤
          j q + Nat.dist (Hermite1DimdLEAN.blockIndexMulti alpha q) (j q) :=
      Nat.dist_tri_right' (Hermite1DimdLEAN.blockIndexMulti alpha q) (j q)
    have hdist' : Nat.dist (Hermite1DimdLEAN.blockIndexMulti alpha q) (j q) ≤ M := by
      simpa [Nat.dist_comm] using hqdist
    exact le_trans htri (Nat.add_le_add_left hdist' _)
  have hidx_lower : j q ≤ Hermite1DimdLEAN.blockIndexMulti alpha q + M := by
    have htri :
        j q ≤ Hermite1DimdLEAN.blockIndexMulti alpha q +
          Nat.dist (j q) (Hermite1DimdLEAN.blockIndexMulti alpha q) :=
      Nat.dist_tri_right' (j q) (Hermite1DimdLEAN.blockIndexMulti alpha q)
    exact le_trans htri (Nat.add_le_add_left hqdist _)
  constructor
  · unfold annulusBandStart
    by_cases hjm : j q ≤ M
    · simp [hjm]
    · have hjgt : M < j q := lt_of_not_ge hjm
      have hidx : j q - M ≤ Hermite1DimdLEAN.blockIndexMulti alpha q := by
        omega
      have hsq : (j q - M) ^ 2 ≤ (Hermite1DimdLEAN.blockIndexMulti alpha q) ^ 2 := by
        exact Nat.pow_le_pow_left hidx 2
      have hsqrt : (Hermite1DimdLEAN.blockIndexMulti alpha q) ^ 2 ≤ alpha q := by
        simpa [Hermite1DimdLEAN.blockIndexMulti, HermiteLEAN.blockIndex, pow_two]
          using Nat.sqrt_le' (alpha q)
      have hle : (j q - M) ^ 2 ≤ alpha q := hsq.trans hsqrt
      simpa [max_eq_left (le_of_lt hjgt)] using hle
  · rw [annulusBandStart_add_length]
    have hlt : alpha q < (Hermite1DimdLEAN.blockIndexMulti alpha q + 1) ^ 2 := by
      simpa [Hermite1DimdLEAN.blockIndexMulti, HermiteLEAN.blockIndex, pow_two]
        using Nat.lt_succ_sqrt' (alpha q)
    have hmono :
        (Hermite1DimdLEAN.blockIndexMulti alpha q + 1) ^ 2 ≤ (j q + M + 1) ^ 2 := by
      exact Nat.pow_le_pow_left (Nat.succ_le_succ hidx_upper) 2
    exact lt_of_lt_of_le hlt hmono

private theorem annulusBandSeparation_of_large_coord
    {d : Nat} (D M : Nat) (j : Idx d) (q : Fin d)
    (hlarge : M + 4 * circleGap D * (2 * M + 1) * (M + 1) ≤ j q) :
    circleGap D * annulusBandLength j q M ≤ annulusBandStart j q M := by
  let R : Nat := j q
  let K : Nat := circleGap D
  let A : Nat := R - M
  have hM : M ≤ R := by
    dsimp [R] at hlarge ⊢
    omega
  have hA_large : 4 * K * (2 * M + 1) * (M + 1) ≤ A := by
    dsimp [A, R, K] at hlarge ⊢
    omega
  have hstart : annulusBandStart j q M = A ^ 2 := by
    dsimp [annulusBandStart, A, R]
    rw [max_eq_left hM]
  have hlength :
      annulusBandLength j q M = (2 * M + 1) * (2 * R + 1) := by
    dsimp [annulusBandLength, R]
    rw [hstart]
    change (R + M + 1) ^ 2 - A ^ 2 = (2 * M + 1) * (2 * R + 1)
    have hAsum : A + M = R := by
      dsimp [A]
      exact Nat.sub_add_cancel hM
    have hA_le : A ≤ R + M + 1 := by
      dsimp [A]
      omega
    have hsq_le : A ^ 2 ≤ (R + M + 1) ^ 2 := Nat.pow_le_pow_left hA_le 2
    have hint :
        (((R + M + 1) ^ 2 - A ^ 2 : Nat) : ℤ) =
          ((2 * M + 1) * (2 * R + 1) : ℤ) := by
      rw [Nat.cast_sub hsq_le]
      have hRInt : (R : ℤ) = (A : ℤ) + (M : ℤ) := by
        exact_mod_cast hAsum.symm
      norm_num [pow_two]
      rw [hRInt]
      ring
    exact_mod_cast hint
  rw [hstart, hlength]
  have hK_ge : 1 ≤ K := by
    dsimp [K]
    exact circleGap_pos D
  have hR : R = A + M := by
    dsimp [A]
    omega
  have hA_ge_2M : 2 * M + 1 ≤ A := by
    have hstep : 2 * M + 1 ≤ 4 * K * (2 * M + 1) * (M + 1) := by
      have hfactor : 1 ≤ 4 * K * (M + 1) := by
        nlinarith
      have hmul := Nat.mul_le_mul_right (2 * M + 1) hfactor
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact le_trans hstep hA_large
  have hA_ge_3K : 3 * K * (2 * M + 1) ≤ A := by
    have hstep : 3 * K * (2 * M + 1) ≤ 4 * K * (2 * M + 1) * (M + 1) := by
      have hfactor : 3 ≤ 4 * (M + 1) := by
        nlinarith
      have hmul := Nat.mul_le_mul_right (K * (2 * M + 1)) hfactor
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact le_trans hstep hA_large
  have htwo : 2 * R + 1 ≤ 3 * A := by
    nlinarith
  change K * ((2 * M + 1) * (2 * R + 1)) ≤ A ^ 2
  nlinarith

private theorem highAnnulusBandSeparation_annulus
    {d : Nat} (hd : 0 < d) (D M : Nat) :
    ∃ Jsep : Nat, ∀ j : Idx d,
      Jsep ≤ j (maxCoordAnnulus hd j) ->
        (let q := maxCoordAnnulus hd j
         circleGap D * annulusBandLength j q M ≤ annulusBandStart j q M) := by
  refine ⟨M + 4 * circleGap D * (2 * M + 1) * (M + 1), ?_⟩
  intro j hlarge
  exact annulusBandSeparation_of_large_coord D M j (maxCoordAnnulus hd j) hlarge

private theorem local_remainder_eval_sub
    {d : Nat} {kappa : MultiIndex d} (j : Idx d) (M : Nat)
    (G : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa (localPartPkappa j M G) z - evalPkappa kappa G z =
      -evalPkappa kappa (remainderPartPkappa j M G) z := by
  have h := localPart_add_remainderPart_evalPkappa (j := j) (M := M) (G := G) z
  rw [← h]
  ring

private theorem annulus_mass_split_pointwise
    {d : Nat} {kappa : MultiIndex d} (j : Idx d) (M : Nat)
    (G : Pkappa d kappa) (z : Cd d) :
    Set.indicator (productAnnulus j) (fun w => ‖evalPkappa kappa G w‖ ^ 2) z ≤
      (2 : ℝ) * Set.indicator (productAnnulus j)
          (fun w => ‖evalPkappa kappa (localPartPkappa j M G) w‖ ^ 2) z +
        (2 : ℝ) * Set.indicator (productAnnulus j)
          (fun w => ‖evalPkappa kappa (remainderPartPkappa j M G) w‖ ^ 2) z := by
  by_cases hz : z ∈ productAnnulus j
  · have hsplit := localPart_add_remainderPart_evalPkappa (j := j) (M := M) (G := G) z
    simp only [Set.indicator, hz, ↓reduceIte, ge_iff_le]
    rw [← hsplit]
    have hnorm :
        ‖evalPkappa kappa (localPartPkappa j M G) z +
            evalPkappa kappa (remainderPartPkappa j M G) z‖ ≤
          ‖evalPkappa kappa (localPartPkappa j M G) z‖ +
            ‖evalPkappa kappa (remainderPartPkappa j M G) z‖ :=
      norm_add_le _ _
    have hsq :
        ‖evalPkappa kappa (localPartPkappa j M G) z +
            evalPkappa kappa (remainderPartPkappa j M G) z‖ ^ 2 ≤
          2 * ‖evalPkappa kappa (localPartPkappa j M G) z‖ ^ 2 +
            2 * ‖evalPkappa kappa (remainderPartPkappa j M G) z‖ ^ 2 := by
      have hsq_norm :
          ‖evalPkappa kappa (localPartPkappa j M G) z +
              evalPkappa kappa (remainderPartPkappa j M G) z‖ ^ 2 ≤
            (‖evalPkappa kappa (localPartPkappa j M G) z‖ +
              ‖evalPkappa kappa (remainderPartPkappa j M G) z‖) ^ 2 := by
        apply (sq_le_sq).2
        simpa
          [abs_of_nonneg (norm_nonneg _),
            abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using
          hnorm
      have hxy :
          2 * ‖evalPkappa kappa (localPartPkappa j M G) z‖ *
              ‖evalPkappa kappa (remainderPartPkappa j M G) z‖ ≤
            ‖evalPkappa kappa (localPartPkappa j M G) z‖ ^ 2 +
              ‖evalPkappa kappa (remainderPartPkappa j M G) z‖ ^ 2 := by
        nlinarith [sq_nonneg
          (‖evalPkappa kappa (localPartPkappa j M G) z‖ -
            ‖evalPkappa kappa (remainderPartPkappa j M G) z‖)]
      nlinarith
    exact hsq
  · simp [Set.indicator, hz]

private theorem annulus_mass_split
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (j : Idx d) (M : Nat) (G : Pkappa d kappa) :
    annulusMass j (ofPkappa kappa G) ≤
      2 * annulusMass j (ofPkappa kappa (localPartPkappa j M G)) +
        2 * annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) := by
  classical
  have hIntG :
      Integrable (fun z : Cd d => ‖evalPkappa kappa G z‖ ^ 2) (gammaD d) := by
    exact integrable_evalPkappa_sq_annulus hd kappa G
  have hIntLocal :
      Integrable
        (fun z : Cd d => ‖evalPkappa kappa (localPartPkappa j M G) z‖ ^ 2)
        (gammaD d) := by
    exact integrable_evalPkappa_sq_annulus hd kappa (localPartPkappa j M G)
  have hIntRem :
      Integrable
        (fun z : Cd d => ‖evalPkappa kappa (remainderPartPkappa j M G) z‖ ^ 2)
        (gammaD d) := by
    exact integrable_evalPkappa_sq_annulus hd kappa (remainderPartPkappa j M G)
  calc
    annulusMass j (ofPkappa kappa G)
        = ∫ z : Cd d,
            Set.indicator (productAnnulus j) (fun w => ‖evalPkappa kappa G w‖ ^ 2) z
            ∂ gammaD d := by
          simp [annulusMass, toFun_ofPkappa_annulus hd kappa G]
    _ ≤ ∫ z : Cd d,
          (2 : ℝ) * Set.indicator (productAnnulus j)
              (fun w => ‖evalPkappa kappa (localPartPkappa j M G) w‖ ^ 2) z +
            (2 : ℝ) * Set.indicator (productAnnulus j)
              (fun w => ‖evalPkappa kappa (remainderPartPkappa j M G) w‖ ^ 2) z
          ∂ gammaD d := by
        refine MeasureTheory.integral_mono_ae
          (hIntG.indicator (measurableSet_productAnnulus_annulus j)) ?_ ?_
        · exact
            (hIntLocal.indicator (measurableSet_productAnnulus_annulus j)).const_mul 2 |>.add
              ((hIntRem.indicator (measurableSet_productAnnulus_annulus j)).const_mul 2)
        · filter_upwards with z
          exact annulus_mass_split_pointwise (j := j) (M := M) (G := G) z
    _ = 2 * annulusMass j (ofPkappa kappa (localPartPkappa j M G)) +
          2 * annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) := by
        rw [MeasureTheory.integral_add]
        · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          simp [annulusMass, toFun_ofPkappa_annulus hd kappa (localPartPkappa j M G),
            toFun_ofPkappa_annulus hd kappa (remainderPartPkappa j M G)]
        · exact
            (hIntLocal.indicator (measurableSet_productAnnulus_annulus j)).const_mul 2
        · exact (hIntRem.indicator (measurableSet_productAnnulus_annulus j)).const_mul 2

private theorem local_defect_pointwise_bound
    {d : Nat} {kappa : MultiIndex d} (j : Idx d) (M : Nat)
    (F G : Pkappa d kappa) (z : Cd d) :
    (‖evalPkappa kappa F z + evalPkappa kappa (localPartPkappa j M G) z‖ -
        ‖evalPkappa kappa F z‖) ^ 2 ≤
      2 * (‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
        ‖evalPkappa kappa F z‖) ^ 2 +
      2 * ‖evalPkappa kappa (remainderPartPkappa j M G) z‖ ^ 2 := by
  have hρ := Hermite1DimdLEAN.rhoPointwiseSq
    (a := evalPkappa kappa F z)
    (u := evalPkappa kappa (localPartPkappa j M G) z)
    (v := evalPkappa kappa G z)
  have hsub := local_remainder_eval_sub (j := j) (M := M) (G := G) z
  rw [hsub] at hρ
  simpa [Hermite1DimdLEAN.rho, norm_neg] using hρ

private def baseDefectAnnulusMass
    {d : Nat} (kappa : MultiIndex d) (j : Idx d)
    (F G : Pkappa d kappa) : ℝ :=
  ∫ z, Set.indicator (productAnnulus j)
    (fun w => (‖evalPkappa kappa F w + evalPkappa kappa G w‖ -
      ‖evalPkappa kappa F w‖) ^ 2) z ∂ gammaD d

private theorem integrable_baseDefectSq_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    Integrable
      (fun z : Cd d =>
        (‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
          ‖evalPkappa kappa F z‖) ^ 2)
      (gammaD d) := by
  have hplus_int :
      Integrable (fun z : Cd d => 2 * ‖evalPkappa kappa (F + G) z‖ ^ 2) (gammaD d) := by
    exact (integrable_evalPkappa_sq_annulus hd kappa (F + G)).const_mul 2
  have hbase_int :
      Integrable (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
    exact (integrable_evalPkappa_sq_annulus hd kappa F).const_mul 2
  have hsq :
      Integrable
        (fun z : Cd d =>
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 +
            2 * ‖evalPkappa kappa F z‖ ^ 2)
        (gammaD d) := hplus_int.add hbase_int
  have hmeasSq :
      AEStronglyMeasurable
        (fun z : Cd d =>
          (‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
            ‖evalPkappa kappa F z‖) ^ 2)
        (gammaD d) := by
    exact
      (((continuous_evalPkappa_annulus kappa F).add
        (continuous_evalPkappa_annulus kappa G)).norm.sub
          (continuous_evalPkappa_annulus kappa F).norm).pow 2
        |>.stronglyMeasurable.aestronglyMeasurable
  have hbound :
      ∀ᵐ z ∂ gammaD d,
        ‖(‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
            ‖evalPkappa kappa F z‖) ^ 2‖ ≤
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 +
            2 * ‖evalPkappa kappa F z‖ ^ 2 := by
    filter_upwards with z
    have hsqz :
        (‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
            ‖evalPkappa kappa F z‖) ^ 2 ≤
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 +
            2 * ‖evalPkappa kappa F z‖ ^ 2 := by
      rw [evalPkappa_add_apply_annulus kappa F G z]
      nlinarith
        [sq_nonneg (‖evalPkappa kappa F z + evalPkappa kappa G z‖ +
          ‖evalPkappa kappa F z‖)]
    have hnonneg :
        0 ≤
          (‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
            ‖evalPkappa kappa F z‖) ^ 2 := by
      positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hsqz
  simpa [Real.norm_eq_abs, abs_of_nonneg] using
    MeasureTheory.Integrable.mono' hsq hmeasSq hbound

private theorem integrable_coordFiber_baseDefectSq_annulus
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (F H : Pkappa d kappa) (z : Cd d) :
    Integrable
      (fun x : Circle =>
        (‖evalPkappa kappa F
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
            evalPkappa kappa H
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
          ‖evalPkappa kappa F
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2)
      AddCircle.haarAddCircle := by
  have hcont_update :
      Continuous (fun x : Circle =>
        Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) := by
    fun_prop
  have hcont :
      Continuous (fun x : Circle =>
        (‖evalPkappa kappa F
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
            evalPkappa kappa H
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
          ‖evalPkappa kappa F
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2) :=
    ((((continuous_evalPkappa_annulus kappa F).comp hcont_update).add
      ((continuous_evalPkappa_annulus kappa H).comp hcont_update)).norm.sub
        (((continuous_evalPkappa_annulus kappa F).comp hcont_update).norm)).pow 2
  exact integrableOn_univ.mp
    (hcont.continuousOn.integrableOn_compact (μ := AddCircle.haarAddCircle) isCompact_univ)

private theorem coordFiber_baseDefect_lintegral_annulus
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (F H : Pkappa d kappa) (z : Cd d) :
    ∫⁻ x : Circle,
        ENNReal.ofReal
          ((‖evalPkappa kappa F
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
              evalPkappa kappa H
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
            ‖evalPkappa kappa F
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2)
        ∂ AddCircle.haarAddCircle =
      ENNReal.ofReal
        (∫ x : Circle,
          (‖evalPkappa kappa F
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
              evalPkappa kappa H
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
            ‖evalPkappa kappa F
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
          ∂ AddCircle.haarAddCircle) := by
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_coordFiber_baseDefectSq_annulus (kappa := kappa) (q0 := q0) F H z)
    (ae_of_all _ (fun x => sq_nonneg _))).symm

private theorem baseDefectAnnulusMass_eq_coordFiber_average_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (j : Idx d) (q0 : Fin d) (F H : Pkappa d kappa) :
    ENNReal.ofReal (baseDefectAnnulusMass kappa j F H) =
      ∫⁻ z : Cd d,
        Set.indicator (productAnnulus j)
          (fun z =>
            ENNReal.ofReal
              (∫ x : Circle,
                (‖evalPkappa kappa F
                      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
                    evalPkappa kappa H
                      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
                  ‖evalPkappa kappa F
                      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
                ∂ AddCircle.haarAddCircle)) z
        ∂ gammaD d := by
  classical
  have hdef_int :
      Integrable
        ((productAnnulus j).indicator
          (fun z : Cd d =>
            (‖evalPkappa kappa F z + evalPkappa kappa H z‖ -
              ‖evalPkappa kappa F z‖) ^ 2))
        (gammaD d) :=
    (integrable_baseDefectSq_annulus hd kappa F H).indicator
      (measurableSet_productAnnulus_annulus j)
  have hdef0 :
      ENNReal.ofReal (baseDefectAnnulusMass kappa j F H) =
        ∫⁻ z : Cd d,
          ENNReal.ofReal
            ((productAnnulus j).indicator
              (fun z : Cd d =>
                (‖evalPkappa kappa F z + evalPkappa kappa H z‖ -
                  ‖evalPkappa kappa F z‖) ^ 2) z)
        ∂ gammaD d := by
    simpa [baseDefectAnnulusMass, Set.indicator] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hdef_int
        (ae_of_all _ (by
          intro z
          by_cases hz : z ∈ productAnnulus j
          · simp [Set.indicator, hz, sq_nonneg]
          · simp [Set.indicator, hz])))
  have hFdef :
      Measurable (fun z : Cd d => ENNReal.ofReal
        ((‖evalPkappa kappa F z + evalPkappa kappa H z‖ -
          ‖evalPkappa kappa F z‖) ^ 2)) := by
    exact ENNReal.measurable_ofReal.comp
      ((((continuous_evalPkappa_annulus kappa F).add
        (continuous_evalPkappa_annulus kappa H)).norm.sub
          (continuous_evalPkappa_annulus kappa F).norm).pow 2).measurable
  have havg :=
    annulusCoordinateRotationAveraging (j := j) (q0 := q0)
      (F := fun z : Cd d => ENNReal.ofReal
        ((‖evalPkappa kappa F z + evalPkappa kappa H z‖ -
          ‖evalPkappa kappa F z‖) ^ 2)) hFdef
  have hdef_indicator :
      ∫⁻ z : Cd d,
          ENNReal.ofReal
            ((productAnnulus j).indicator
              (fun z : Cd d =>
                (‖evalPkappa kappa F z + evalPkappa kappa H z‖ -
                  ‖evalPkappa kappa F z‖) ^ 2) z)
        ∂ gammaD d
        =
      ∫⁻ z : Cd d,
          if z ∈ productAnnulus j then
            ENNReal.ofReal
              ((‖evalPkappa kappa F z + evalPkappa kappa H z‖ -
                ‖evalPkappa kappa F z‖) ^ 2)
          else 0
        ∂ gammaD d := by
    refine lintegral_congr_ae ?_
    filter_upwards with z
    by_cases hz : z ∈ productAnnulus j <;> simp [Set.indicator, hz]
  calc
    ENNReal.ofReal (baseDefectAnnulusMass kappa j F H)
        =
      ∫⁻ z : Cd d,
          if z ∈ productAnnulus j then
            ∫⁻ x : Circle,
              ENNReal.ofReal
                ((‖evalPkappa kappa F
                      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
                    evalPkappa kappa H
                      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
                  ‖evalPkappa kappa F
                      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2)
            ∂ AddCircle.haarAddCircle
          else 0
        ∂ gammaD d := by
          rw [hdef0]
          rw [hdef_indicator]
          exact havg.symm
    _ = ∫⁻ z : Cd d,
          Set.indicator (productAnnulus j)
            (fun z =>
              ENNReal.ofReal
                (∫ x : Circle,
                  (‖evalPkappa kappa F
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
                      evalPkappa kappa H
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
                    ‖evalPkappa kappa F
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
                  ∂ AddCircle.haarAddCircle)) z
        ∂ gammaD d := by
          refine lintegral_congr_ae ?_
          filter_upwards with z
          by_cases hz : z ∈ productAnnulus j
          · simpa [Set.indicator, hz] using
              (coordFiber_baseDefect_lintegral_annulus
                (kappa := kappa) (q0 := q0) F H z)
          · simp [Set.indicator, hz]

private theorem local_defect_annulus_bound
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (j : Idx d) (M : Nat) (F G : Pkappa d kappa) :
    baseDefectAnnulusMass kappa j F (localPartPkappa j M G) ≤
      2 * baseDefectAnnulusMass kappa j F G +
        2 * annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) := by
  classical
  have hmeas := measurableSet_productAnnulus_annulus j
  have hleft :
      Integrable
        (fun z : Cd d =>
          Set.indicator (productAnnulus j)
            (fun w =>
              (‖evalPkappa kappa F w + evalPkappa kappa (localPartPkappa j M G) w‖ -
                ‖evalPkappa kappa F w‖) ^ 2) z)
        (gammaD d) := by
    exact
      (integrable_baseDefectSq_annulus hd kappa F (localPartPkappa j M G)).indicator hmeas
  have hrightDef :
      Integrable
        (fun z : Cd d =>
          2 * Set.indicator (productAnnulus j)
            (fun w =>
              (‖evalPkappa kappa F w + evalPkappa kappa G w‖ -
                ‖evalPkappa kappa F w‖) ^ 2) z)
        (gammaD d) := by
    exact ((integrable_baseDefectSq_annulus hd kappa F G).indicator hmeas).const_mul 2
  have hrightMass :
      Integrable
        (fun z : Cd d =>
          2 * Set.indicator (productAnnulus j)
            (fun w => ‖evalPkappa kappa (remainderPartPkappa j M G) w‖ ^ 2) z)
        (gammaD d) := by
    exact
      ((integrable_evalPkappa_sq_annulus hd kappa (remainderPartPkappa j M G)).indicator
          hmeas).const_mul 2
  unfold baseDefectAnnulusMass
  calc
    ∫ z : Cd d,
        Set.indicator (productAnnulus j)
          (fun w =>
            (‖evalPkappa kappa F w + evalPkappa kappa (localPartPkappa j M G) w‖ -
              ‖evalPkappa kappa F w‖) ^ 2) z ∂ gammaD d
        ≤
        ∫ z : Cd d,
          2 * Set.indicator (productAnnulus j)
              (fun w =>
                (‖evalPkappa kappa F w + evalPkappa kappa G w‖ -
                  ‖evalPkappa kappa F w‖) ^ 2) z +
            2 * Set.indicator (productAnnulus j)
              (fun w => ‖evalPkappa kappa (remainderPartPkappa j M G) w‖ ^ 2) z
          ∂ gammaD d := by
          refine MeasureTheory.integral_mono_ae hleft (hrightDef.add hrightMass) ?_
          filter_upwards with z
          by_cases hz : z ∈ productAnnulus j
          · simp only [Set.indicator, hz, ↓reduceIte]
            exact local_defect_pointwise_bound (j := j) (M := M) (F := F) (G := G) z
          · simp [Set.indicator, hz]
    _ = 2 * (∫ z : Cd d,
          Set.indicator (productAnnulus j)
            (fun w =>
              (‖evalPkappa kappa F w + evalPkappa kappa G w‖ -
                ‖evalPkappa kappa F w‖) ^ 2) z ∂ gammaD d) +
        2 * (∫ z : Cd d,
          Set.indicator (productAnnulus j)
            (fun w => ‖evalPkappa kappa (remainderPartPkappa j M G) w‖ ^ 2) z
          ∂ gammaD d) := by
          rw [MeasureTheory.integral_add hrightDef hrightMass,
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = 2 * (∫ z : Cd d,
          Set.indicator (productAnnulus j)
            (fun w =>
              (‖evalPkappa kappa F w + evalPkappa kappa G w‖ -
                ‖evalPkappa kappa F w‖) ^ 2) z ∂ gammaD d) +
        2 * annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) := by
          simp [annulusMass, toFun_ofPkappa_annulus hd kappa (remainderPartPkappa j M G)]

private theorem productAnnulus_eq_of_mem_annulus
    {d : Nat} {j ℓ : Idx d} {z : Cd d}
    (hj : z ∈ productAnnulus j) (hℓ : z ∈ productAnnulus ℓ) :
    j = ℓ := by
  funext q
  rcases hj q with ⟨hj_lower, hj_upper⟩
  rcases hℓ q with ⟨hℓ_lower, hℓ_upper⟩
  refine le_antisymm ?_ ?_
  · by_contra hlt
    have hlt' : ℓ q + 1 ≤ j q := Nat.succ_le_of_lt (Nat.lt_of_not_ge hlt)
    have hlt_real : ((ℓ q : Nat) : ℝ) + 1 ≤ j q := by
      exact_mod_cast hlt'
    linarith
  · by_contra hlt
    have hlt' : j q + 1 ≤ ℓ q := Nat.succ_le_of_lt (Nat.lt_of_not_ge hlt)
    have hlt_real : ((j q : Nat) : ℝ) + 1 ≤ ℓ q := by
      exact_mod_cast hlt'
    linarith

private theorem sum_indicator_productAnnulus_le_annulus
    {d : Nat} (s : Finset (Idx d)) (z : Cd d) (a : ℝ)
    (ha : 0 ≤ a) :
    ∑ j ∈ s, Set.indicator (productAnnulus j) (fun _ : Cd d => a) z ≤ a := by
  classical
  by_cases hs : ∃ j ∈ s, z ∈ productAnnulus j
  · rcases hs with ⟨j0, hj0s, hj0z⟩
    have hsum :
        ∑ j ∈ s, Set.indicator (productAnnulus j) (fun _ : Cd d => a) z =
          Set.indicator (productAnnulus j0) (fun _ : Cd d => a) z := by
      exact Finset.sum_eq_single_of_mem j0 hj0s (fun j hjs hjne => by
        have hjz : z ∉ productAnnulus j := by
          intro hjz
          have heq := productAnnulus_eq_of_mem_annulus hjz hj0z
          exact hjne heq
        simp [Set.indicator, hjz])
    rw [hsum]
    simp [Set.indicator, hj0z]
  · have hzero : ∀ j ∈ s, z ∉ productAnnulus j := by
      intro j hjs
      by_contra hjz
      exact hs ⟨j, hjs, hjz⟩
    rw [Finset.sum_eq_zero]
    · linarith
    · intro j hj
      simp [Set.indicator, hzero j hj]

private theorem defect_sq_eq_baseDefectIntegral_annulus
    {d : Nat} {kappa : MultiIndex d} (F G : Pkappa d kappa) :
    defect F G ^ 2 =
      ∫ z : Cd d,
        (‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
          ‖evalPkappa kappa F z‖) ^ 2 ∂ gammaD d := by
  unfold defect
  rw [Real.sq_sqrt]
  · refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with z
    rw [evalPkappa_add_apply_annulus]
  · exact MeasureTheory.integral_nonneg fun z => sq_nonneg _

private theorem finite_sum_baseDefectAnnulusMass_le
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (s : Finset (Idx d)) :
    ∑ j ∈ s, baseDefectAnnulusMass kappa j F G ≤ defect F G ^ 2 := by
  classical
  have hIntGlobal :
      Integrable
        (fun z : Cd d =>
          (‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
            ‖evalPkappa kappa F z‖) ^ 2)
        (gammaD d) :=
    integrable_baseDefectSq_annulus hd kappa F G
  have hIntSum :
      Integrable
        (fun z : Cd d =>
          ∑ j ∈ s, Set.indicator (productAnnulus j)
            (fun w =>
              (‖evalPkappa kappa F w + evalPkappa kappa G w‖ -
                ‖evalPkappa kappa F w‖) ^ 2) z)
        (gammaD d) := by
    refine MeasureTheory.integrable_finsetSum _ ?_
    intro j hj
    exact hIntGlobal.indicator (measurableSet_productAnnulus_annulus j)
  calc
    ∑ j ∈ s, baseDefectAnnulusMass kappa j F G
        = ∫ z : Cd d,
            ∑ j ∈ s, Set.indicator (productAnnulus j)
              (fun w =>
                (‖evalPkappa kappa F w + evalPkappa kappa G w‖ -
                  ‖evalPkappa kappa F w‖) ^ 2) z ∂ gammaD d := by
          rw [MeasureTheory.integral_finsetSum]
          · simp [baseDefectAnnulusMass]
          · intro j hj
            exact hIntGlobal.indicator (measurableSet_productAnnulus_annulus j)
    _ ≤ ∫ z : Cd d,
          (‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
            ‖evalPkappa kappa F z‖) ^ 2 ∂ gammaD d := by
          refine MeasureTheory.integral_mono_ae hIntSum hIntGlobal ?_
          filter_upwards with z
          simpa [Set.indicator] using
            sum_indicator_productAnnulus_le_annulus s z
              ((‖evalPkappa kappa F z + evalPkappa kappa G z‖ -
                ‖evalPkappa kappa F z‖) ^ 2)
              (by positivity)
    _ = defect F G ^ 2 := by
          rw [← defect_sq_eq_baseDefectIntegral_annulus (kappa := kappa) F G]

private theorem finite_sum_annulusMass_le_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (G : Pkappa d kappa) (s : Finset (Idx d)) :
    ∑ j ∈ s, annulusMass j (ofPkappa kappa G) ≤ ‖G‖ ^ 2 := by
  classical
  have hInt :
      Integrable
        (fun z : Cd d =>
          ∑ j ∈ s, Set.indicator (productAnnulus j)
            (fun w => ‖evalPkappa kappa G w‖ ^ 2) z)
        (gammaD d) := by
    refine MeasureTheory.integrable_finsetSum _ ?_
    intro j hj
    exact (integrable_evalPkappa_sq_annulus hd kappa G).indicator
      (measurableSet_productAnnulus_annulus j)
  have hnorm :
      Integrable (fun z : Cd d => ‖evalPkappa kappa G z‖ ^ 2) (gammaD d) :=
    integrable_evalPkappa_sq_annulus hd kappa G
  calc
    ∑ j ∈ s, annulusMass j (ofPkappa kappa G)
        = ∫ z : Cd d,
            ∑ j ∈ s, Set.indicator (productAnnulus j)
              (fun w => ‖evalPkappa kappa G w‖ ^ 2) z ∂ gammaD d := by
          rw [MeasureTheory.integral_finsetSum]
          · simp [annulusMass, toFun_ofPkappa_annulus hd kappa G]
          · intro j hj
            exact (integrable_evalPkappa_sq_annulus hd kappa G).indicator
              (measurableSet_productAnnulus_annulus j)
    _ ≤ ∫ z : Cd d, ‖evalPkappa kappa G z‖ ^ 2 ∂ gammaD d := by
          refine MeasureTheory.integral_mono_ae hInt hnorm ?_
          filter_upwards with z
          simpa [Set.indicator] using
            sum_indicator_productAnnulus_le_annulus s z
              (‖evalPkappa kappa G z‖ ^ 2) (by positivity)
    _ = ‖G‖ ^ 2 := by
          simpa using evalPkappa_total_mass hd kappa G

private theorem phi1D_eq_oneDimPhi_annulus
    (k n : Nat) (z : ℂ) :
    phi1D k n z = Hermite1DimdLEAN.oneDimPhi k n z := by
  unfold phi1D complexHermite Hermite1DimdLEAN.oneDimPhi
  congr 1
  · simp [one_div, mul_comm]
  · rw [Nat.min_comm k n]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j ≤ min n k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjn : j ≤ n := le_trans hj' (Nat.min_le_left _ _)
    have hfac_ne : (Nat.factorial (n - j) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - j)
    have hfactor :
        (Nat.factorial j : ℂ) * (Nat.choose n j : ℂ) =
          (Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) := by
      apply mul_right_cancel₀ hfac_ne
      calc
        ((Nat.factorial j : ℂ) * (Nat.choose n j : ℂ)) * (Nat.factorial (n - j) : ℂ)
            = (Nat.choose n j : ℂ) * (Nat.factorial j : ℂ) *
                (Nat.factorial (n - j) : ℂ) := by ring
        _ = (Nat.factorial n : ℂ) := by
            exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
        _ = ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              (Nat.factorial (n - j) : ℂ) := by
            field_simp [hfac_ne]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      congrArg
        (fun x : ℂ =>
          ((-1 : ℂ) ^ j) * x * (Nat.choose k j : ℂ) * z ^ (n - j) * (star z) ^ (k - j))
        hfactor

private theorem Phi_eq_PhiKappaAlpha_annulus
    {d : Nat} (kappa alpha : MultiIndex d) (z : Cd d) :
    Phi kappa alpha z = Hermite1DimdLEAN.PhiKappaAlpha kappa alpha z := by
  unfold Phi Hermite1DimdLEAN.PhiKappaAlpha
  refine Finset.prod_congr rfl ?_
  intro q hq
  exact phi1D_eq_oneDimPhi_annulus (kappa q) (alpha q) (z q)

private lemma oneDimPhi_phaseLaw_annulus
    (k n : Nat) (t : ℝ) (z : ℂ) :
    Hermite1DimdLEAN.oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
        Hermite1DimdLEAN.oneDimPhi k n z := by
  obtain ⟨radial, hradial⟩ := Hermite1DimdLEAN.oneVariableAngularFactorization k n
  have hz : ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) = z := by
    simp [mul_comm Complex.I (z.arg : ℂ), Complex.norm_mul_exp_arg_mul_I z]
  have hrot :
      Complex.exp (Complex.I * t) * z =
        ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
    calc
      Complex.exp (Complex.I * t) * z =
          Complex.exp (Complex.I * t) * ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) := by
            rw [hz]
      _ = ((‖z‖ : ℂ) * Complex.exp (Complex.I * t)) * Complex.exp (Complex.I * z.arg) := by
            ring_nf
      _ = (‖z‖ : ℂ) * (Complex.exp (Complex.I * t) * Complex.exp (Complex.I * z.arg)) := by
            rw [mul_assoc]
      _ = ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
            rw [← Complex.exp_add]
            congr 1
            ring_nf
  have hleft :
      Hermite1DimdLEAN.oneDimPhi k n ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by
    simpa using hradial ‖z‖ (t + z.arg)
  have hright :
      Hermite1DimdLEAN.oneDimPhi k n z =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by
    simpa [hz] using hradial ‖z‖ z.arg
  have hexp :
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) := by
    rw [show Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * t)) +
          Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) by ring_nf]
    rw [Complex.exp_add]
  calc
    Hermite1DimdLEAN.oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
        Hermite1DimdLEAN.oneDimPhi k n
          ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
          rw [hrot]
    _ = Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := hleft
    _ = Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Hermite1DimdLEAN.oneDimPhi k n z := by
          rw [hexp, hright]
          ring_nf

private theorem Phi_rotate_one_exp_annulus
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d) (t : ℝ) (z : Cd d) :
    Phi kappa alpha (Function.update z q0 (Complex.exp (Complex.I * t) * z q0)) =
      Complex.exp (Complex.I * (((alpha q0 : ℤ) - (kappa q0 : ℤ) : ℂ) * t)) *
        Phi kappa alpha z := by
  classical
  rw [Phi_eq_PhiKappaAlpha_annulus, Phi_eq_PhiKappaAlpha_annulus]
  unfold Hermite1DimdLEAN.PhiKappaAlpha
  have hupdate :
      (fun q : Fin d =>
        Hermite1DimdLEAN.oneDimPhi (kappa q) (alpha q)
          (Function.update z q0 (Complex.exp (Complex.I * t) * z q0) q)) =
        Function.update
          (fun q : Fin d => Hermite1DimdLEAN.oneDimPhi (kappa q) (alpha q) (z q))
          q0
          (Hermite1DimdLEAN.oneDimPhi (kappa q0) (alpha q0)
            (Complex.exp (Complex.I * t) * z q0)) := by
    funext q
    by_cases hq : q = q0
    · subst hq
      simp
    · simp [Function.update, hq]
  rw [hupdate]
  rw [Finset.prod_update_of_mem (s := Finset.univ) (i := q0) (by simp)]
  rw [oneDimPhi_phaseLaw_annulus]
  conv_rhs =>
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (s := Finset.univ) (i := q0) (by simp)]
  ring_nf

private lemma fourier_mk_eq_exp_annulus
    (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : Circle) : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * θ) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

private theorem Phi_rotateCoord_circle_phase_annulus
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d)
    (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
    (fourier ((alpha q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha z := by
  induction x using Quotient.inductionOn with
  | h θ =>
      rw [fourier_mk_eq_exp_annulus ((kappa q0 : Nat) : Int) θ]
      rw [fourier_mk_eq_exp_annulus ((alpha q0 : Nat) : Int) θ]
      rw [fourier_mk_eq_exp_annulus (1 : Int) θ]
      have hone :
        Complex.exp (Complex.I * ((1 : ℤ) : ℂ) * θ) =
            Complex.exp (Complex.I * θ) := by
        congr 1
        ring_nf
      rw [hone]
      rw [Phi_rotate_one_exp_annulus]
      have hphase :
          Complex.exp (Complex.I * (((kappa q0 : Nat) : Int) : ℂ) * θ) *
              (Complex.exp (Complex.I * (((alpha q0 : ℤ) - (kappa q0 : ℤ) : ℂ) * θ)) *
                Phi kappa alpha z) =
            Complex.exp (Complex.I * (((alpha q0 : Nat) : Int) : ℂ) * θ) *
              Phi kappa alpha z := by
        rw [← mul_assoc, ← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      exact hphase

private def fiberIndexLow
    {d : Nat} (q0 : Fin d) (D : Nat) (alpha : Idx d) : Fin (D + 1) :=
  if h : alpha q0 ≤ D then ⟨alpha q0, Nat.lt_succ_of_le h⟩ else 0

private noncomputable def fiberCoeffLow
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (D : Nat) (F : Pkappa d kappa) (z : Cd d) :
    Fin (D + 1) → ℂ :=
  fun n =>
    ∑ alpha ∈ F.support.filter (fun alpha => fiberIndexLow q0 D alpha = n),
      F alpha * Phi kappa alpha z

private noncomputable def baseCoordDegree
    {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : Nat :=
  F.support.sup fun alpha => (Finset.univ : Finset (Fin d)).sup fun q => alpha q

private theorem baseCoordDegree_spec
    {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa)
    {alpha : Idx d} (halpha : alpha ∈ F.support) (q : Fin d) :
    alpha q ≤ baseCoordDegree F := by
  have hq :
      alpha q ≤ (Finset.univ : Finset (Fin d)).sup (fun r => alpha r) :=
    Finset.le_sup (s := Finset.univ) (f := fun r : Fin d => alpha r) (by simp)
  have halpha_sup :
      (Finset.univ : Finset (Fin d)).sup (fun r => alpha r) ≤ baseCoordDegree F := by
    unfold baseCoordDegree
    exact Finset.le_sup
      (s := F.support)
      (f := fun beta : Idx d => (Finset.univ : Finset (Fin d)).sup fun q => beta q)
      halpha
  exact le_trans hq halpha_sup

private theorem evalPkappa_rotateCoord_circle_phase_sum_annulus
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (F : Pkappa d kappa) (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      evalPkappa kappa F
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
      ∑ alpha ∈ F.support,
        F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
  classical
  unfold evalPkappa
  rw [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  have hphase :=
    Phi_rotateCoord_circle_phase_annulus
      (kappa := kappa) (alpha := alpha) (q0 := q0) x z
  have hchar : circleChar (alpha q0) x = (fourier ((alpha q0 : Nat) : Int) x : ℂ) :=
    circleChar_eq_fourier_nat (alpha q0) x
  calc
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
        (F alpha *
          Phi kappa alpha
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)))
      = F alpha *
          ((fourier ((kappa q0 : Nat) : Int) x : ℂ) *
            Phi kappa alpha
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) := by
          ring_nf
    _ = F alpha * ((fourier ((alpha q0 : Nat) : Int) x : ℂ) * Phi kappa alpha z) := by
          rw [hphase]
    _ = F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
          rw [hchar]
          ring_nf

private theorem lowPoly_fiberCoeffLow_eq_sum_annulus
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (D : Nat) (F : Pkappa d kappa) (z : Cd d)
    (x : Circle)
    (hD : ∀ alpha ∈ F.support, alpha q0 ≤ D) :
    lowPoly (fiberCoeffLow q0 D F z) x =
      ∑ alpha ∈ F.support,
        F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
  classical
  let g : Idx d → Fin (D + 1) := fiberIndexLow q0 D
  let A : Idx d → ℂ := fun alpha => F alpha * Phi kappa alpha z
  have hdecomp :=
    Finset.sum_fiberwise_of_maps_to
      (s := F.support) (t := Finset.univ) (g := g)
      (h := fun alpha halpha => by simp) (f := fun alpha => A alpha * circleChar (g alpha).1 x)
  calc
    lowPoly (fiberCoeffLow q0 D F z) x
        = ∑ n : Fin (D + 1),
            (∑ alpha ∈ F.support.filter (fun alpha => g alpha = n), A alpha) *
              circleChar n.1 x := by
          simp [lowPoly, fiberCoeffLow, g, A]
    _ = ∑ n : Fin (D + 1),
            ∑ alpha ∈ F.support.filter (fun alpha => g alpha = n),
              A alpha * circleChar (g alpha).1 x := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro alpha halpha
          have hg : g alpha = n := (Finset.mem_filter.mp halpha).2
          rw [hg]
    _ = ∑ alpha ∈ F.support, A alpha * circleChar (g alpha).1 x := by
          simpa using hdecomp
    _ = ∑ alpha ∈ F.support, A alpha * circleChar (alpha q0) x := by
          refine Finset.sum_congr rfl ?_
          intro alpha halpha
          have hgval : (g alpha).1 = alpha q0 := by
            simp [g, fiberIndexLow, hD alpha halpha]
          rw [hgval]
    _ = ∑ alpha ∈ F.support,
          F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
          simp [A]

private theorem corrected_base_fiber_eq_lowPoly_annulus
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (D : Nat) (F : Pkappa d kappa) (z : Cd d)
    (hD : ∀ alpha ∈ F.support, alpha q0 ≤ D) :
    (fun x : Circle =>
      (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
        evalPkappa kappa F
          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) =
    lowPoly (fiberCoeffLow q0 D F z) := by
  funext x
  rw [evalPkappa_rotateCoord_circle_phase_sum_annulus]
  exact (lowPoly_fiberCoeffLow_eq_sum_annulus q0 D F z x hD).symm

private def fiberIndexBand
    {d : Nat} (q0 : Fin d) (N L : Nat) (hL : 1 ≤ L) (alpha : Idx d) : Fin L :=
  if h : alpha q0 < N + L then
    ⟨alpha q0 - N, by omega⟩
  else
    ⟨0, by omega⟩

private noncomputable def fiberCoeffBand
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (N L : Nat) (hL : 1 ≤ L) (H : Pkappa d kappa) (z : Cd d) :
    Fin L → ℂ :=
  fun m =>
    ∑ alpha ∈ H.support.filter (fun alpha => fiberIndexBand q0 N L hL alpha = m),
      H alpha * Phi kappa alpha z

private theorem bandPoly_fiberCoeffBand_eq_sum_annulus
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (N L : Nat) (hL : 1 ≤ L)
    (H : Pkappa d kappa) (z : Cd d) (x : Circle)
    (hband : ∀ alpha ∈ H.support, N ≤ alpha q0 ∧ alpha q0 < N + L) :
    bandPoly N (fiberCoeffBand q0 N L hL H z) x =
      ∑ alpha ∈ H.support,
        H alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
  classical
  let g : Idx d → Fin L := fiberIndexBand q0 N L hL
  let A : Idx d → ℂ := fun alpha => H alpha * Phi kappa alpha z
  have hdecomp :=
    Finset.sum_fiberwise_of_maps_to
      (s := H.support) (t := Finset.univ) (g := g)
      (h := fun alpha halpha => by simp)
      (f := fun alpha => A alpha * circleChar (N + (g alpha).1) x)
  calc
    bandPoly N (fiberCoeffBand q0 N L hL H z) x
        = ∑ m : Fin L,
            (∑ alpha ∈ H.support.filter (fun alpha => g alpha = m), A alpha) *
              circleChar (N + m.1) x := by
          simp [bandPoly, fiberCoeffBand, g, A]
    _ = ∑ m : Fin L,
            ∑ alpha ∈ H.support.filter (fun alpha => g alpha = m),
              A alpha * circleChar (N + (g alpha).1) x := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro alpha halpha
          have hg : g alpha = m := (Finset.mem_filter.mp halpha).2
          rw [hg]
    _ = ∑ alpha ∈ H.support, A alpha * circleChar (N + (g alpha).1) x := by
          simpa using hdecomp
    _ = ∑ alpha ∈ H.support, A alpha * circleChar (alpha q0) x := by
          refine Finset.sum_congr rfl ?_
          intro alpha halpha
          have hlt : alpha q0 < N + L := (hband alpha halpha).2
          have hle : N ≤ alpha q0 := (hband alpha halpha).1
          have hgval : N + (g alpha).1 = alpha q0 := by
            simp [g, fiberIndexBand, hlt]
            omega
          rw [hgval]
    _ = ∑ alpha ∈ H.support,
          H alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
          simp [A]

private theorem corrected_local_fiber_eq_bandPoly_annulus
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (N L : Nat) (hL : 1 ≤ L)
    (H : Pkappa d kappa) (z : Cd d)
    (hband : ∀ alpha ∈ H.support, N ≤ alpha q0 ∧ alpha q0 < N + L) :
    (fun x : Circle =>
      (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
        evalPkappa kappa H
          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) =
    bandPoly N (fiberCoeffBand q0 N L hL H z) := by
  funext x
  rw [evalPkappa_rotateCoord_circle_phase_sum_annulus]
  exact (bandPoly_fiberCoeffBand_eq_sum_annulus q0 N L hL H z x hband).symm

private theorem corrected_fiber_circle_estimate_annulus
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (D N L : Nat)
    (F H : Pkappa d kappa) (z : Cd d)
    (hL : 1 ≤ L)
    (hsep : circleGap D * L ≤ N)
    (hD : ∀ alpha ∈ F.support, alpha q0 ≤ D)
    (hband : ∀ alpha ∈ H.support, N ≤ alpha q0 ∧ alpha q0 < N + L) :
    circleL2Sq
      (fun x : Circle =>
        (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
          evalPkappa kappa H
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) ≤
    circleConst D *
      defectSq
        (fun x : Circle =>
          (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
            evalPkappa kappa F
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)))
        (fun x : Circle =>
          (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
            evalPkappa kappa H
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) := by
  have hF := corrected_base_fiber_eq_lowPoly_annulus
    (q0 := q0) (D := D) (F := F) (z := z) hD
  have hH := corrected_local_fiber_eq_bandPoly_annulus
    (q0 := q0) (N := N) (L := L) (hL := hL) (H := H) (z := z) hband
  rw [hH, hF]
  exact finite_base_circle_estimate D hL hsep
    (fiberCoeffLow q0 D F z) (fiberCoeffBand q0 N L hL H z)

private theorem corrected_fiber_circleL2Sq_eq_uncorrected_annulus
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (H : Pkappa d kappa) (z : Cd d) :
    circleL2Sq
      (fun x : Circle =>
        (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
          evalPkappa kappa H
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) =
    circleL2Sq
      (fun x : Circle =>
        evalPkappa kappa H
          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) := by
  unfold circleL2Sq
  congr
  ext x
  simp

private theorem corrected_fiber_defectSq_eq_uncorrected_annulus
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (F H : Pkappa d kappa) (z : Cd d) :
    defectSq
      (fun x : Circle =>
        (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
          evalPkappa kappa F
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)))
      (fun x : Circle =>
        (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
          evalPkappa kappa H
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) =
    ∫ x : Circle,
      (‖evalPkappa kappa F
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
          evalPkappa kappa H
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
        ‖evalPkappa kappa F
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
      ∂AddCircle.haarAddCircle := by
  unfold defectSq
  congr
  ext x
  let phase : ℂ := fourier ((kappa q0 : Nat) : Int) x
  let Fz : ℂ :=
    evalPkappa kappa F
      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))
  let Hz : ℂ :=
    evalPkappa kappa H
      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))
  have hphase_norm : ‖phase‖ = 1 := by
    simp [phase]
  have hadd : phase * Fz + phase * Hz = phase * (Fz + Hz) := by
    ring_nf
  calc
    (‖phase * Fz + phase * Hz‖ - ‖phase * Fz‖) ^ 2
        = (‖phase * (Fz + Hz)‖ - ‖phase * Fz‖) ^ 2 := by
          rw [hadd]
    _ = (‖Fz + Hz‖ - ‖Fz‖) ^ 2 := by
          rw [norm_mul, norm_mul, hphase_norm]
          norm_num

private theorem fiber_circle_estimate_uncorrected_annulus
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (D N L : Nat)
    (F H : Pkappa d kappa) (z : Cd d)
    (hL : 1 ≤ L)
    (hsep : circleGap D * L ≤ N)
    (hD : ∀ alpha ∈ F.support, alpha q0 ≤ D)
    (hband : ∀ alpha ∈ H.support, N ≤ alpha q0 ∧ alpha q0 < N + L) :
    circleL2Sq
      (fun x : Circle =>
        evalPkappa kappa H
          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) ≤
    circleConst D *
      ∫ x : Circle,
        (‖evalPkappa kappa F
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
            evalPkappa kappa H
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
          ‖evalPkappa kappa F
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
        ∂AddCircle.haarAddCircle := by
  have hcorr := corrected_fiber_circle_estimate_annulus
    (q0 := q0) (D := D) (N := N) (L := L)
    (F := F) (H := H) (z := z) hL hsep hD hband
  rw [corrected_fiber_circleL2Sq_eq_uncorrected_annulus
      (q0 := q0) (H := H) (z := z)] at hcorr
  rw [corrected_fiber_defectSq_eq_uncorrected_annulus
      (q0 := q0) (F := F) (H := H) (z := z)] at hcorr
  exact hcorr

private theorem localPartPkappa_fiber_circle_estimate_annulus
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (D : Nat) (F G : Pkappa d kappa)
    (j : Idx d) (M : Nat) (z : Cd d)
    (hD : ∀ alpha ∈ F.support, alpha q0 ≤ D)
    (hsep :
      circleGap D * annulusBandLength j q0 M ≤ annulusBandStart j q0 M) :
    circleL2Sq
      (fun x : Circle =>
        evalPkappa kappa (localPartPkappa j M G)
          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) ≤
    circleConst D *
      ∫ x : Circle,
        (‖evalPkappa kappa F
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
            evalPkappa kappa (localPartPkappa j M G)
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
          ‖evalPkappa kappa F
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
        ∂AddCircle.haarAddCircle := by
  refine fiber_circle_estimate_uncorrected_annulus
    (q0 := q0) (D := D) (N := annulusBandStart j q0 M)
    (L := annulusBandLength j q0 M)
    (F := F) (H := localPartPkappa j M G) (z := z)
    (annulusBandLength_pos j q0 M) hsep hD ?_
  intro alpha halpha
  exact localPartPkappa_coord_band (j := j) (M := M) (G := G) halpha q0

private theorem exists_high_localPartPkappa_fiber_circle_estimate_annulus
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (F G : Pkappa d kappa) (M : Nat) :
    ∃ Jsep : Nat, ∀ (j : Idx d) (z : Cd d),
      Jsep ≤ j (maxCoordAnnulus hd j) ->
        circleL2Sq
          (fun x : Circle =>
            evalPkappa kappa (localPartPkappa j M G)
              (Function.update z (maxCoordAnnulus hd j)
                ((fourier (1 : Int) x : ℂ) * z (maxCoordAnnulus hd j)))) ≤
        circleConst (baseCoordDegree F) *
          ∫ x : Circle,
            (‖evalPkappa kappa F
                  (Function.update z (maxCoordAnnulus hd j)
                    ((fourier (1 : Int) x : ℂ) * z (maxCoordAnnulus hd j))) +
                evalPkappa kappa (localPartPkappa j M G)
                  (Function.update z (maxCoordAnnulus hd j)
                    ((fourier (1 : Int) x : ℂ) * z (maxCoordAnnulus hd j)))‖ -
              ‖evalPkappa kappa F
                  (Function.update z (maxCoordAnnulus hd j)
                    ((fourier (1 : Int) x : ℂ) * z (maxCoordAnnulus hd j)))‖) ^ 2
            ∂AddCircle.haarAddCircle := by
  obtain ⟨Jsep, hJsep⟩ :=
    highAnnulusBandSeparation_annulus hd (baseCoordDegree F) M
  refine ⟨Jsep, ?_⟩
  intro j z hlarge
  let q0 : Fin d := maxCoordAnnulus hd j
  have hsep :
      circleGap (baseCoordDegree F) * annulusBandLength j q0 M ≤
        annulusBandStart j q0 M := by
    simpa [q0] using hJsep j hlarge
  exact localPartPkappa_fiber_circle_estimate_annulus
    (q0 := q0) (D := baseCoordDegree F) (F := F) (G := G)
    (j := j) (M := M) (z := z)
    (fun alpha halpha => baseCoordDegree_spec F halpha q0) hsep

private theorem baseDefectAnnulusMass_nonneg_annulus
    {d : Nat} (kappa : MultiIndex d) (j : Idx d)
    (F H : Pkappa d kappa) :
    0 ≤ baseDefectAnnulusMass kappa j F H := by
  unfold baseDefectAnnulusMass
  exact MeasureTheory.integral_nonneg fun z => by
    by_cases hz : z ∈ productAnnulus j
    · simp [Set.indicator, hz, sq_nonneg]
    · simp [Set.indicator, hz]

private theorem high_localPart_annulus_estimate_annulus
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (F : Pkappa d kappa) (M : Nat) :
    ∃ Jloc : Nat, ∃ C : ℝ, C = circleConst (baseCoordDegree F) ∧ 0 < C ∧
      ∀ (j : Idx d) (G : Pkappa d kappa),
        Jloc ≤ j (maxCoordAnnulus hd j) ->
          annulusMass j (ofPkappa kappa (localPartPkappa j M G)) ≤
            C * baseDefectAnnulusMass kappa j F (localPartPkappa j M G) := by
  classical
  let D : Nat := baseCoordDegree F
  let C : ℝ := circleConst D
  obtain ⟨Jloc, hJloc⟩ := highAnnulusBandSeparation_annulus hd D M
  refine ⟨Jloc, C, rfl, circleConst_pos D, ?_⟩
  intro j G hlarge
  let q0 : Fin d := maxCoordAnnulus hd j
  let H : Pkappa d kappa := localPartPkappa j M G
  have hCpos : 0 < C := circleConst_pos D
  have hCnonneg : 0 ≤ C := le_of_lt hCpos
  have hsep :
      circleGap D * annulusBandLength j q0 M ≤ annulusBandStart j q0 M := by
    simpa [D, q0] using hJloc j hlarge
  have hpoint : ∀ z : Cd d,
      circleL2Sq
        (fun x : Circle =>
          evalPkappa kappa H
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) ≤
      C *
        ∫ x : Circle,
          (‖evalPkappa kappa F
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
              evalPkappa kappa H
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
            ‖evalPkappa kappa F
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
          ∂AddCircle.haarAddCircle := by
    intro z
    simpa [D, C, H, q0] using
      localPartPkappa_fiber_circle_estimate_annulus
        (q0 := q0) (D := D) (F := F) (G := G)
        (j := j) (M := M) (z := z)
        (fun alpha halpha => by
          simpa [D] using baseCoordDegree_spec F halpha q0)
        hsep
  have hmassAvg :=
    annulusMass_eq_coordFiber_average_annulus
      (hd := hd) (kappa := kappa) (j := j) (q0 := q0) (H := H)
  have hdefAvg :=
    baseDefectAnnulusMass_eq_coordFiber_average_annulus
      (hd := hd) (kappa := kappa) (j := j) (q0 := q0) (F := F) (H := H)
  have hmono :
      (∫⁻ z : Cd d,
        Set.indicator (productAnnulus j)
          (fun z =>
            ENNReal.ofReal
              (circleL2Sq
                (fun x : Circle =>
                  evalPkappa kappa H
                    (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))))) z
        ∂ gammaD d)
        ≤
      (∫⁻ z : Cd d,
        ENNReal.ofReal C *
          Set.indicator (productAnnulus j)
            (fun z =>
              ENNReal.ofReal
                (∫ x : Circle,
                  (‖evalPkappa kappa F
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
                      evalPkappa kappa H
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
                    ‖evalPkappa kappa F
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
                  ∂ AddCircle.haarAddCircle)) z
        ∂ gammaD d) := by
    refine lintegral_mono ?_
    intro z
    by_cases hz : z ∈ productAnnulus j
    · simpa only [Set.indicator_of_mem hz] using
        (calc
          ENNReal.ofReal
              (circleL2Sq
                (fun x : Circle =>
                  evalPkappa kappa H
                    (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))))
              ≤
            ENNReal.ofReal
              (C *
                ∫ x : Circle,
                  (‖evalPkappa kappa F
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
                      evalPkappa kappa H
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
                    ‖evalPkappa kappa F
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
                  ∂ AddCircle.haarAddCircle) := by
              exact ENNReal.ofReal_le_ofReal (hpoint z)
          _ =
            ENNReal.ofReal C *
              ENNReal.ofReal
                (∫ x : Circle,
                  (‖evalPkappa kappa F
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
                      evalPkappa kappa H
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
                    ‖evalPkappa kappa F
                        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
                  ∂ AddCircle.haarAddCircle) := by
              rw [ENNReal.ofReal_mul hCnonneg])
    · simp only [Set.indicator_of_notMem hz, mul_zero, zero_le]
  have hofReal_le :
      ENNReal.ofReal (annulusMass j (ofPkappa kappa H)) ≤
        ENNReal.ofReal
          (C * baseDefectAnnulusMass kappa j F H) := by
    calc
      ENNReal.ofReal (annulusMass j (ofPkappa kappa H))
          =
        ∫⁻ z : Cd d,
          Set.indicator (productAnnulus j)
            (fun z =>
              ENNReal.ofReal
                (circleL2Sq
                  (fun x : Circle =>
                    evalPkappa kappa H
                      (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))))) z
          ∂ gammaD d := hmassAvg
      _ ≤
        ∫⁻ z : Cd d,
          ENNReal.ofReal C *
            Set.indicator (productAnnulus j)
              (fun z =>
                ENNReal.ofReal
                  (∫ x : Circle,
                    (‖evalPkappa kappa F
                          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
                        evalPkappa kappa H
                          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
                      ‖evalPkappa kappa F
                          (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
                    ∂ AddCircle.haarAddCircle)) z
          ∂ gammaD d := hmono
      _ =
          ENNReal.ofReal C *
            ∫⁻ z : Cd d,
              Set.indicator (productAnnulus j)
                (fun z =>
                  ENNReal.ofReal
                    (∫ x : Circle,
                      (‖evalPkappa kappa F
                            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) +
                          evalPkappa kappa H
                            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖ -
                        ‖evalPkappa kappa F
                            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))‖) ^ 2
                      ∂ AddCircle.haarAddCircle)) z
            ∂ gammaD d := by
            rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal C)]
            simp
      _ = ENNReal.ofReal C *
          ENNReal.ofReal (baseDefectAnnulusMass kappa j F H) := by
            rw [← hdefAvg]
      _ = ENNReal.ofReal
          (C * baseDefectAnnulusMass kappa j F H) := by
            rw [ENNReal.ofReal_mul hCnonneg]
  have hdef_nonneg : 0 ≤ baseDefectAnnulusMass kappa j F H :=
    baseDefectAnnulusMass_nonneg_annulus kappa j F H
  have hrhs_nonneg : 0 ≤ C * baseDefectAnnulusMass kappa j F H :=
    mul_nonneg hCnonneg hdef_nonneg
  exact (ENNReal.ofReal_le_ofReal_iff hrhs_nonneg).mp hofReal_le

private theorem high_annulus_coercive_step_annulus
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (F : Pkappa d kappa) (M Jloc : Nat) (C : ℝ) (hCnonneg : 0 ≤ C)
    (hlocal :
      ∀ (j : Idx d) (G : Pkappa d kappa),
        Jloc ≤ j (maxCoordAnnulus hd j) ->
          annulusMass j (ofPkappa kappa (localPartPkappa j M G)) ≤
            C * baseDefectAnnulusMass kappa j F (localPartPkappa j M G))
    (j : Idx d) (G : Pkappa d kappa)
    (hlarge : Jloc ≤ j (maxCoordAnnulus hd j)) :
    annulusMass j (ofPkappa kappa G) ≤
      4 * C * baseDefectAnnulusMass kappa j F G +
        (4 * C + 2) *
          annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) := by
  have hsplit := annulus_mass_split hd j M G
  have hloc := hlocal j G hlarge
  have hdef := local_defect_annulus_bound hd j M F G
  have hrem_nonneg :
      0 ≤ annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) :=
    annulusMass_nonneg_annulus j (ofPkappa kappa (remainderPartPkappa j M G))
  have hbase_nonneg :
      0 ≤ baseDefectAnnulusMass kappa j F G :=
    baseDefectAnnulusMass_nonneg_annulus kappa j F G
  nlinarith

private theorem evalPkappa_eq_evalHermiteSum_annulus
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    evalPkappa kappa F = Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ := by
  ext z
  unfold evalPkappa Hermite1DimdLEAN.evalHermiteSum Hermite1DimdLEAN.FiniteHermiteSum.support
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [Phi_eq_PhiKappaAlpha_annulus]

private theorem annulusMass_ofPkappa_eq_hermite_annulusMass
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (j : Idx d) (F : Pkappa d kappa) :
    annulusMass j (ofPkappa kappa F) =
      Hermite1DimdLEAN.annulusMass j (Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩) := by
  classical
  have hgauss : gammaD d = Hermite1DimdLEAN.gaussianMeasure d := by
    unfold gammaD Hermite1DimdLEAN.gaussianMeasure
    congr 1
  have hleft :
      annulusMass j (ofPkappa kappa F) =
        ∫ z : Cd d,
          if z ∈ productAnnulus j then ‖Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ z‖ ^ 2 else 0
          ∂ Hermite1DimdLEAN.gaussianMeasure d := by
    simp [annulusMass, hgauss,
      toFun_ofPkappa_annulus hd kappa F, evalPkappa_eq_evalHermiteSum_annulus kappa F,
      Set.indicator]
  have hright :
      Hermite1DimdLEAN.annulusMass j (Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩) =
        ∫ z : Cd d,
          if z ∈ productAnnulus j then ‖Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ z‖ ^ 2 else 0
          ∂ Hermite1DimdLEAN.gaussianMeasure d := by
    unfold Hermite1DimdLEAN.annulusMass
    change
      (∫ z : Cd d,
          if z ∈ productAnnulus j then ‖Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ z‖ ^ 2 else 0
          ∂ Hermite1DimdLEAN.gaussianMeasure d) =
        (∫ z : Cd d,
          if z ∈ productAnnulus j then ‖Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ z‖ ^ 2 else 0
          ∂ Hermite1DimdLEAN.gaussianMeasure d)
    simp [productAnnulus]
  rw [hleft, hright]

private theorem hermiteNormSq_ofPkappa_eq_norm_sq_annulus
    {d : Nat} {kappa : MultiIndex d} (G : Pkappa d kappa) :
    Hermite1DimdLEAN.hermiteNormSq kappa ⟨G⟩ = ‖G‖ ^ 2 := by
  have hparseval :
      Hermite1DimdLEAN.hermiteNormSq kappa ⟨G⟩ =
        Finset.sum G.support (fun alpha => ‖G alpha‖ ^ 2) := by
    exact Hermite1DimdLEAN.finiteParseval kappa ⟨G⟩
  rw [hparseval]
  change Finset.sum G.support (fun alpha => ‖G alpha‖ ^ 2) =
    (Real.sqrt (Finset.sum G.support (fun alpha => ‖G alpha‖ ^ 2))) ^ 2
  symm
  rw [Real.sq_sqrt]
  positivity

private theorem annulusMass_tsum_eq_norm_sq_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (G : Pkappa d kappa) :
    ‖G‖ ^ 2 = ∑' j : Idx d, annulusMass j (ofPkappa kappa G) := by
  classical
  have hgauss : gammaD d = Hermite1DimdLEAN.gaussianMeasure d := by
    unfold gammaD Hermite1DimdLEAN.gaussianMeasure
    congr 1
  have heval := evalPkappa_eq_evalHermiteSum_annulus kappa G
  have hInt :
      Integrable
        (fun z : Cd d =>
          ‖Hermite1DimdLEAN.evalHermiteSum kappa ⟨G⟩ z‖ ^ 2)
        (Hermite1DimdLEAN.gaussianMeasure d) := by
    have hInt' := integrable_evalPkappa_sq_annulus hd kappa G
    simpa [← hgauss, ← heval] using hInt'
  have hpart :=
    Hermite1DimdLEAN.partitionOfGaussianNorm
      (F := Hermite1DimdLEAN.evalHermiteSum kappa ⟨G⟩) hInt
  calc
    ‖G‖ ^ 2 = Hermite1DimdLEAN.hermiteNormSq kappa ⟨G⟩ := by
          rw [hermiteNormSq_ofPkappa_eq_norm_sq_annulus]
    _ = Hermite1DimdLEAN.gaussianL2NormSq
          (Hermite1DimdLEAN.evalHermiteSum kappa ⟨G⟩) := rfl
    _ = ∑' j : Idx d,
          Hermite1DimdLEAN.annulusMass j
            (Hermite1DimdLEAN.evalHermiteSum kappa ⟨G⟩) := hpart
    _ = ∑' j : Idx d, annulusMass j (ofPkappa kappa G) := by
          refine tsum_congr ?_
          intro j
          exact (annulusMass_ofPkappa_eq_hermite_annulusMass hd kappa j G).symm

private theorem summable_annulusMass_ofPkappa_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (G : Pkappa d kappa) :
    Summable (fun j : Idx d => annulusMass j (ofPkappa kappa G)) := by
  exact summable_of_sum_le
    (fun j => annulusMass_nonneg_annulus j (ofPkappa kappa G))
    (fun s => by
      simpa using finite_sum_annulusMass_le_annulus hd kappa G s)

private theorem mem_lowAnnuli_iff_annulus
    {d J : Nat} {j : Idx d} :
    j ∈ lowAnnuli d J ↔ ∀ q : Fin d, j q < J := by
  simp [lowAnnuli]

private theorem not_mem_lowAnnuli_iff_maxCoordAnnulus
    {d : Nat} (hd : 0 < d) (J : Nat) (j : Idx d) :
    j ∉ lowAnnuli d J ↔ J ≤ j (maxCoordAnnulus hd j) := by
  constructor
  · intro hnot
    by_contra hlt
    have hmem : j ∈ lowAnnuli d J := by
      rw [mem_lowAnnuli_iff_annulus]
      intro q
      exact lt_of_le_of_lt (maxCoordAnnulus_spec hd j q) (Nat.lt_of_not_ge hlt)
    exact hnot hmem
  · intro hlarge hmem
    have hlt := (mem_lowAnnuli_iff_annulus.mp hmem) (maxCoordAnnulus hd j)
    exact (not_le_of_gt hlt) hlarge

private theorem highAnnulusMass_eq_tsum_high_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (G : Pkappa d kappa) :
    highAnnulusMass J (ofPkappa kappa G) =
      ∑' j : Idx d,
        if J ≤ j (maxCoordAnnulus hd j) then
          annulusMass j (ofPkappa kappa G)
        else 0 := by
  classical
  let a : Idx d → ℝ := fun j => annulusMass j (ofPkappa kappa G)
  have hsumm : Summable a := summable_annulusMass_ofPkappa_annulus hd kappa G
  have hsplit := hsumm.sum_add_tsum_subtype_compl (lowAnnuli d J)
  have hsub :
      (∑' j : {j // j ∉ lowAnnuli d J}, a j) =
        ∑' j : Idx d, Set.indicator {j : Idx d | j ∉ lowAnnuli d J} a j := by
    simpa using
      (tsum_subtype (s := {j : Idx d | j ∉ lowAnnuli d J}) (f := a))
  have htail_max :
      (∑' j : Idx d, Set.indicator {j : Idx d | j ∉ lowAnnuli d J} a j) =
        ∑' j : Idx d,
          if J ≤ j (maxCoordAnnulus hd j) then a j else 0 := by
    refine tsum_congr ?_
    intro j
    by_cases hlarge : J ≤ j (maxCoordAnnulus hd j)
    · have hnot : j ∉ lowAnnuli d J :=
        (not_mem_lowAnnuli_iff_maxCoordAnnulus hd J j).mpr hlarge
      simp [Set.indicator, hlarge, hnot]
    · have hmem : j ∈ lowAnnuli d J := by
        by_contra hnot
        exact hlarge ((not_mem_lowAnnuli_iff_maxCoordAnnulus hd J j).mp hnot)
      simp [Set.indicator, hlarge, hmem]
  have htotal := annulusMass_tsum_eq_norm_sq_annulus hd kappa G
  have htotal_int :
      (∫ z : Cd d, ‖toFun kappa (ofPkappa kappa G) z‖ ^ 2 ∂ gammaD d) = ‖G‖ ^ 2 := by
    simpa [toFun_ofPkappa_annulus hd kappa G] using evalPkappa_total_mass hd kappa G
  have htail_eq :
      (∑' j : Idx d, Set.indicator {j : Idx d | j ∉ lowAnnuli d J} a j) =
        ‖G‖ ^ 2 - ∑ j ∈ lowAnnuli d J, a j := by
    rw [← hsub]
    dsimp [a] at hsplit htotal
    linarith
  unfold highAnnulusMass lowAnnulusMass
  rw [htotal_int, ← htail_max]
  exact htail_eq.symm

private theorem finitePartialLeakage_remainderPartPkappa_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      Filter.Tendsto
        (fun M : Nat => Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M)
        Filter.atTop (nhds 0) ∧
      ∀ (s : Finset (Idx d)) (M : Nat) (G : Pkappa d kappa),
        ∑ j ∈ s, annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) ≤
          Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M * ‖G‖ ^ 2 := by
  obtain ⟨C, c, B, hCpos, hcpos, hBnonneg, htail, hpartial⟩ :=
    Hermite1DimdLEAN.finitePartialLeakage (κ := kappa)
  refine ⟨C, c, B, hCpos, hcpos, hBnonneg, htail, ?_⟩
  intro s M G
  have hleft :
      ∑ j ∈ s, annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) =
        ∑ j ∈ s,
          Hermite1DimdLEAN.annulusMass j
            (Hermite1DimdLEAN.evalHermiteSum kappa
              (Hermite1DimdLEAN.remainderPart j M ⟨G⟩)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simpa [remainderPartPkappa] using
      annulusMass_ofPkappa_eq_hermite_annulusMass hd kappa j (remainderPartPkappa j M G)
  calc
    ∑ j ∈ s, annulusMass j (ofPkappa kappa (remainderPartPkappa j M G))
        =
        ∑ j ∈ s,
          Hermite1DimdLEAN.annulusMass j
            (Hermite1DimdLEAN.evalHermiteSum kappa
              (Hermite1DimdLEAN.remainderPart j M ⟨G⟩)) := hleft
    _ ≤ Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M *
          Hermite1DimdLEAN.hermiteNormSq kappa ⟨G⟩ := by
        exact hpartial s M ⟨G⟩
    _ = Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M * ‖G‖ ^ 2 := by
        rw [hermiteNormSq_ofPkappa_eq_norm_sq_annulus]

private theorem evalPkappa_smul_real_annulus
    {d : Nat} (kappa : MultiIndex d) (t : ℝ) (H : Pkappa d kappa) :
    evalPkappa kappa (t • H) = fun z => (t : ℂ) * evalPkappa kappa H z := by
  ext z
  by_cases ht : t = 0
  · subst t
    simp [evalPkappa]
  · unfold evalPkappa
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq ht, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    rw [Finsupp.smul_apply]
    change ((t : ℂ) * H alpha) * Phi kappa alpha z =
      (t : ℂ) * (H alpha * Phi kappa alpha z)
    ring

private theorem toFun_ofPkappa_smul_real_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (t : ℝ) (H : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa (t • H)) =
      fun z => (t : ℂ) * toFun kappa (ofPkappa kappa H) z := by
  rw [toFun_ofPkappa_annulus hd kappa (t • H), toFun_ofPkappa_annulus hd kappa H]
  exact evalPkappa_smul_real_annulus kappa t H

private theorem totalMass_ofPkappa_smul_real_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (t : ℝ) (H : Pkappa d kappa) :
    (∫ z, ‖toFun kappa (ofPkappa kappa (t • H)) z‖ ^ 2 ∂ gammaD d) =
      t ^ 2 * (∫ z, ‖toFun kappa (ofPkappa kappa H) z‖ ^ 2 ∂ gammaD d) := by
  rw [toFun_ofPkappa_smul_real_annulus hd kappa t H]
  have hfun :
      (fun z : Cd d => ‖(t : ℂ) * toFun kappa (ofPkappa kappa H) z‖ ^ 2) =
        fun z : Cd d => t ^ 2 * ‖toFun kappa (ofPkappa kappa H) z‖ ^ 2 := by
    ext z
    simp [Real.norm_eq_abs, sq_abs, mul_pow]
  rw [hfun, MeasureTheory.integral_const_mul]

private theorem annulusMass_ofPkappa_smul_real_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (j : Idx d) (t : ℝ) (H : Pkappa d kappa) :
    annulusMass j (ofPkappa kappa (t • H)) =
      t ^ 2 * annulusMass j (ofPkappa kappa H) := by
  unfold annulusMass
  rw [toFun_ofPkappa_smul_real_annulus hd kappa t H]
  have hfun :
      (fun z : Cd d =>
          Set.indicator (productAnnulus j)
            (fun w => ‖(t : ℂ) * toFun kappa (ofPkappa kappa H) w‖ ^ 2) z) =
        fun z : Cd d =>
          t ^ 2 * Set.indicator (productAnnulus j)
            (fun w => ‖toFun kappa (ofPkappa kappa H) w‖ ^ 2) z := by
    ext z
    by_cases hz : z ∈ productAnnulus j
    · simp [Set.indicator, hz, Real.norm_eq_abs, sq_abs, mul_pow]
    · simp [Set.indicator, hz]
  rw [hfun, MeasureTheory.integral_const_mul]

private theorem lowAnnulusMass_ofPkappa_smul_real_annulus
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (t : ℝ) (H : Pkappa d kappa) :
    lowAnnulusMass J (ofPkappa kappa (t • H)) =
      t ^ 2 * lowAnnulusMass J (ofPkappa kappa H) := by
  unfold lowAnnulusMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact annulusMass_ofPkappa_smul_real_annulus hd kappa j t H

private theorem highAnnulusMass_ofPkappa_smul_real
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (t : ℝ) (H : Pkappa d kappa) :
    highAnnulusMass J (ofPkappa kappa (t • H)) =
      t ^ 2 * highAnnulusMass J (ofPkappa kappa H) := by
  unfold highAnnulusMass
  rw [totalMass_ofPkappa_smul_real_annulus hd kappa t H,
    lowAnnulusMass_ofPkappa_smul_real_annulus hd kappa J t H]
  ring

private theorem norm_smul_pkappa_real_sq_annulus
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (t : ℝ) (H : Pkappa d kappa) :
    ‖t • H‖ ^ 2 = t ^ 2 * ‖H‖ ^ 2 := by
  let _ := hd
  by_cases ht : t = 0
  · subst t
    have hzero_norm : ‖(0 : Pkappa d kappa)‖ = 0 := by
      change
        Real.sqrt
          (Finset.sum (0 : Pkappa d kappa).support
            (fun alpha => ‖(0 : Pkappa d kappa) alpha‖ ^ 2)) = 0
      simp
    simp [hzero_norm]
  · change
      (Real.sqrt (Finset.sum (t • H).support (fun alpha => ‖(t • H) alpha‖ ^ 2))) ^ 2 =
        t ^ 2 * (Real.sqrt (Finset.sum H.support (fun alpha => ‖H alpha‖ ^ 2))) ^ 2
    rw [Finsupp.support_smul_eq ht]
    have hsum :
        Finset.sum H.support (fun alpha => ‖(t • H) alpha‖ ^ 2) =
          t ^ 2 * Finset.sum H.support (fun alpha => ‖H alpha‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro alpha halpha
      simp [Finsupp.smul_apply, Real.norm_eq_abs, sq_abs, mul_pow]
    rw [hsum]
    rw [Real.sq_sqrt (mul_nonneg (sq_nonneg t) (by positivity))]
    rw [Real.sq_sqrt (by positivity)]

private theorem finite_base_product_annulus_estimate_large_eps
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (_hF : basePointNormalized F)
    (eps : ℝ) (_h_eps : 0 < eps) (h_eps_large : 1 <= eps) :
    ∃ J : Nat, ∃ M : Nat, 1 <= M ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ G : Pkappa d kappa,
        highAnnulusMass J (ofPkappa kappa G)
          <= C * defect F G ^ 2 + eps * ‖G‖ ^ 2 := by
  refine ⟨0, 1, by norm_num, 1, by norm_num, ?_⟩
  intro G
  have hhigh_le : highAnnulusMass 0 (ofPkappa kappa G) <= ‖G‖ ^ 2 :=
    highAnnulusMass_le_norm_sq_wip hd kappa 0 G
  have hnorm_sq_nonneg : 0 <= ‖G‖ ^ 2 := by positivity
  have hdef_sq_nonneg : 0 <= defect F G ^ 2 := by positivity
  nlinarith

theorem finite_base_product_annulus_estimate
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF : basePointNormalized F) :
    ∀ eps : ℝ, 0 < eps ->
      ∃ J : Nat, ∃ M : Nat, 1 <= M ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ G : Pkappa d kappa,
          highAnnulusMass J (ofPkappa kappa G)
            <= C * defect F G ^ 2 + eps * ‖G‖ ^ 2 := by
  let _ := hd
  /-
  Proof-sketch-facing product-annulus theorem. The current downstream
  normalized theorem below is a corollary of this unnormalized finite-shell
  estimate after applying it to `G = t • H` and dividing by `t ^ 2`.
  -/
  intro eps h_eps
  by_cases heps_large : 1 <= eps
  · exact finite_base_product_annulus_estimate_large_eps hd kappa F hF eps h_eps heps_large
  · obtain ⟨Cleak, cleak, Bleak, hCleak_pos, hcleak_pos, hBleak_nonneg,
      htail, hpartial⟩ :=
      finitePartialLeakage_remainderPartPkappa_annulus hd kappa
    let Cloc : ℝ := circleConst (baseCoordDegree F)
    let Crem : ℝ := 4 * Cloc + 2
    have hCloc_pos : 0 < Cloc := by
      dsimp [Cloc]
      exact circleConst_pos (baseCoordDegree F)
    have hCloc_nonneg : 0 ≤ Cloc := le_of_lt hCloc_pos
    have hCrem_pos : 0 < Crem := by
      dsimp [Crem]
      nlinarith
    have hCrem_nonneg : 0 ≤ Crem := le_of_lt hCrem_pos
    have hprod_tend :
        Filter.Tendsto
          (fun M : Nat =>
            Crem *
              Hermite1DimdLEAN.localizationLeakageCoefficient Cleak cleak Bleak d M)
          Filter.atTop (nhds 0) := by
      simpa [Crem] using (tendsto_const_nhds.mul htail)
    have hsmall_event :
        ∀ᶠ M : Nat in Filter.atTop,
          Crem *
            Hermite1DimdLEAN.localizationLeakageCoefficient Cleak cleak Bleak d M < eps := by
      exact hprod_tend.eventually (Iio_mem_nhds h_eps)
    rw [Filter.eventually_atTop] at hsmall_event
    obtain ⟨M0, hM0⟩ := hsmall_event
    let M : Nat := max 1 M0
    have hM_one : 1 ≤ M := by
      dsimp [M]
      exact le_max_left 1 M0
    have hM_ge : M0 ≤ M := by
      dsimp [M]
      exact le_max_right 1 M0
    let L : ℝ := Hermite1DimdLEAN.localizationLeakageCoefficient Cleak cleak Bleak d M
    have hleak_small : Crem * L < eps := by
      dsimp [L]
      exact hM0 M hM_ge
    obtain ⟨Jloc, Cgot, hCgot_eq, hCgot_pos, hlocal_got⟩ :=
      high_localPart_annulus_estimate_annulus (hd := hd) (F := F) (M := M)
    have hlocal :
        ∀ (j : Idx d) (G : Pkappa d kappa),
          Jloc ≤ j (maxCoordAnnulus hd j) ->
            annulusMass j (ofPkappa kappa (localPartPkappa j M G)) ≤
              Cloc * baseDefectAnnulusMass kappa j F (localPartPkappa j M G) := by
      intro j G hlarge
      simpa [Cloc, hCgot_eq] using hlocal_got j G hlarge
    refine ⟨Jloc, M, hM_one, 4 * Cloc, by nlinarith, ?_⟩
    intro G
    have htail_eq := highAnnulusMass_eq_tsum_high_annulus hd kappa Jloc G
    have htail_bound :
        (∑' j : Idx d,
          if Jloc ≤ j (maxCoordAnnulus hd j) then
            annulusMass j (ofPkappa kappa G)
          else 0) ≤
        4 * Cloc * defect F G ^ 2 + (Crem * L) * ‖G‖ ^ 2 := by
      refine Real.tsum_le_of_sum_le ?_ ?_
      · intro j
        by_cases hlarge : Jloc ≤ j (maxCoordAnnulus hd j)
        · simp [hlarge, annulusMass_nonneg_annulus]
        · simp [hlarge]
      · intro s
        have hpoint :
            ∀ j ∈ s,
              (if Jloc ≤ j (maxCoordAnnulus hd j) then
                annulusMass j (ofPkappa kappa G)
              else 0) ≤
                4 * Cloc * baseDefectAnnulusMass kappa j F G +
                  Crem *
                    annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) := by
          intro j hj
          by_cases hlarge : Jloc ≤ j (maxCoordAnnulus hd j)
          · have hstep :=
              high_annulus_coercive_step_annulus
                (hd := hd) (F := F) (M := M) (Jloc := Jloc)
                (C := Cloc) hCloc_nonneg hlocal j G hlarge
            simpa [Crem, hlarge, mul_assoc, mul_left_comm, mul_comm,
              add_assoc, add_left_comm, add_comm] using hstep
          · have hrem_nonneg :
                0 ≤ annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) :=
              annulusMass_nonneg_annulus j (ofPkappa kappa (remainderPartPkappa j M G))
            have hbase_nonneg :
                0 ≤ baseDefectAnnulusMass kappa j F G :=
              baseDefectAnnulusMass_nonneg_annulus kappa j F G
            have hrhs_nonneg :
                0 ≤
                  4 * Cloc * baseDefectAnnulusMass kappa j F G +
                    Crem *
                      annulusMass j (ofPkappa kappa (remainderPartPkappa j M G)) := by
              nlinarith
            simpa [hlarge] using hrhs_nonneg
        calc
          ∑ j ∈ s,
              (if Jloc ≤ j (maxCoordAnnulus hd j) then
                annulusMass j (ofPkappa kappa G)
              else 0)
              ≤
            ∑ j ∈ s,
              (4 * Cloc * baseDefectAnnulusMass kappa j F G +
                Crem *
                  annulusMass j (ofPkappa kappa (remainderPartPkappa j M G))) := by
              exact Finset.sum_le_sum hpoint
          _ =
            4 * Cloc *
                (∑ j ∈ s, baseDefectAnnulusMass kappa j F G) +
              Crem *
                (∑ j ∈ s,
                  annulusMass j (ofPkappa kappa (remainderPartPkappa j M G))) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ ≤
            4 * Cloc * defect F G ^ 2 +
              Crem * (L * ‖G‖ ^ 2) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left
                  (finite_sum_baseDefectAnnulusMass_le hd kappa F G s)
                  (by nlinarith))
                (mul_le_mul_of_nonneg_left
                  (by
                    dsimp [L]
                    exact hpartial s M G)
                  hCrem_nonneg)
          _ = 4 * Cloc * defect F G ^ 2 + (Crem * L) * ‖G‖ ^ 2 := by
              ring
    calc
      highAnnulusMass Jloc (ofPkappa kappa G)
          ≤ 4 * Cloc * defect F G ^ 2 + (Crem * L) * ‖G‖ ^ 2 := by
            rw [htail_eq]
            exact htail_bound
      _ ≤ 4 * Cloc * defect F G ^ 2 + eps * ‖G‖ ^ 2 := by
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_right (le_of_lt hleak_small) (by positivity))

theorem finite_base_annulus_estimate
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF : basePointNormalized F) :
    ∀ eps : ℝ, 0 < eps ->
      ∃ J : Nat, ∃ C : ℝ, 0 < C ∧
        ∀ {H : Pkappa d kappa} {t eta : ℝ},
          ‖H‖ = 1 ->
          0 < t ->
          t <= 4 ->
          0 <= eta ->
          defect F (t • H) <= eta * t ->
          highAnnulusMass J (ofPkappa kappa H) <= C * eta ^ 2 + eps := by
  let _ := hd
  /-
  Scaffolding contract:
  normalized finite-shell form of the product-annulus estimate. The scalar
  `eta` is an explicit upper bound for the divided defect `defect F (t • H) / t`.
  Completion, subsequences, and shell extraction remain hidden behind this
  finite theorem.
  -/
  intro eps h_eps
  by_cases heps_large : 1 <= eps
  · refine ⟨0, 1, by norm_num, ?_⟩
    intro H t eta hH_norm ht_pos ht_le_four heta_nonneg hdefect
    have hhigh_le : highAnnulusMass 0 (ofPkappa kappa H) <= ‖H‖ ^ 2 :=
      highAnnulusMass_le_norm_sq_wip hd kappa 0 H
    have hH_sq : ‖H‖ ^ 2 = 1 := by
      nlinarith [hH_norm]
    nlinarith [sq_nonneg eta]
  · obtain ⟨J, M, hM, C, hC_pos, hann⟩ :=
      finite_base_product_annulus_estimate hd kappa F hF eps h_eps
    refine ⟨J, C, hC_pos, ?_⟩
    intro H t eta hH_norm ht_pos ht_le_four heta_nonneg hdefect
    have hprod := hann (t • H)
    rw [highAnnulusMass_ofPkappa_smul_real hd kappa J t H,
      norm_smul_pkappa_real_sq_annulus hd t H] at hprod
    have ht_sq_pos : 0 < t ^ 2 := by positivity
    have hH_sq : ‖H‖ ^ 2 = 1 := by nlinarith [hH_norm]
    have hdef_nonneg : 0 <= defect F (t • H) := defect_nonneg_annulus F (t • H)
    have hdef_sq : defect F (t • H) ^ 2 <= (eta * t) ^ 2 := by
      exact sq_le_sq' (by nlinarith [heta_nonneg, ht_pos]) hdefect
    have hdef_mul : C * defect F (t • H) ^ 2 <= C * (eta * t) ^ 2 :=
      mul_le_mul_of_nonneg_left hdef_sq (le_of_lt hC_pos)
    have hscaled :
        t ^ 2 * highAnnulusMass J (ofPkappa kappa H) <=
          t ^ 2 * (C * eta ^ 2 + eps) := by
      calc
        t ^ 2 * highAnnulusMass J (ofPkappa kappa H)
            <= C * defect F (t • H) ^ 2 + eps * (t ^ 2 * ‖H‖ ^ 2) := hprod
        _ <= C * (eta * t) ^ 2 + eps * (t ^ 2 * ‖H‖ ^ 2) := by
          exact add_le_add hdef_mul (le_refl _)
        _ = t ^ 2 * (C * eta ^ 2 + eps) := by
          rw [hH_sq]
          ring
    nlinarith

theorem highAnnulusControl
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1) :
    ∃ J : Nat, ∃ delta_high : ℝ, 0 < delta_high ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        defect F (t • H) <= delta_high * t ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by
  let _ := hd
  obtain ⟨J, C, hC_pos, hann⟩ :=
    finite_base_annulus_estimate hd kappa F ⟨hF_ne, hF_norm⟩ (1 / 8) (by norm_num)
  let delta_high : ℝ := min 1 (1 / (8 * C))
  have hdelta_high_pos : 0 < delta_high := by
    dsimp [delta_high]
    exact lt_min zero_lt_one (one_div_pos.mpr (mul_pos (by norm_num) hC_pos))
  refine ⟨J, delta_high, hdelta_high_pos, ?_⟩
  intro H t horth hH_norm ht_pos ht_le_four hdefect
  let _ := horth
  have hdelta_nonneg : 0 <= delta_high := le_of_lt hdelta_high_pos
  have hdelta_le_one : delta_high <= 1 := by
    dsimp [delta_high]
    exact min_le_left _ _
  have hdelta_le_inv : delta_high <= 1 / (8 * C) := by
    dsimp [delta_high]
    exact min_le_right _ _
  have hCdelta_le : C * delta_high <= 1 / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hdelta_le_inv (le_of_lt hC_pos)
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    have hcalc : C * (1 / (8 * C)) = 1 / 8 := by
      field_simp [hC_ne]
    nlinarith
  have hdelta_sq_le : delta_high ^ 2 <= delta_high := by
    nlinarith [sq_nonneg delta_high]
  have hCdelta_sq_le : C * delta_high ^ 2 <= 1 / 8 := by
    calc
      C * delta_high ^ 2 <= C * delta_high := by
        exact mul_le_mul_of_nonneg_left hdelta_sq_le (le_of_lt hC_pos)
      _ <= 1 / 8 := hCdelta_le
  have hhigh :
      highAnnulusMass J (ofPkappa kappa H) <= C * delta_high ^ 2 + 1 / 8 :=
    hann hH_norm ht_pos ht_le_four hdelta_nonneg hdefect
  nlinarith

end DimdPolyLEAN
