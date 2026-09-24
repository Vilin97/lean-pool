/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SupportRestrict
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIdentity
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Setting.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianRepresentation

/-!
# Decomposition

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN
/-- Partially centered velocity tensor with the sign convention for the pressure decomposition. -/
def pressureUTensor (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (z : ParabolicPoint) (i j : Fin 3) : ℝ :=
  -u z i * (u z j - c z.2 j)
private theorem decomposition_spatial_box
    {Ω : Set Vec3} {η ψ : Vec3 → ℝ}
    (hΩ : IsOpen Ω) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) :
    ∃ Ω' : Set Vec3, IsOpen Ω' ∧ tsupport η ⊆ Ω' ∧ tsupport ψ ⊆ Ω' ∧
      IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω := by
  let K : Set Vec3 := tsupport η ∪ tsupport ψ
  have hK : IsCompact K := hηc.isCompact.union hψc.isCompact
  obtain ⟨V₀, hV₀open, hKV₀, hV₀compact⟩ :=
    exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨V₁, hV₁open, hKV₁, hV₁Ω⟩ :=
    hK.exists_isOpen_closure_subset ((hΩ.mem_nhdsSet).2 (union_subset hηΩ hψΩ))
  let Ω' := V₀ ∩ V₁
  have hΩ'open : IsOpen Ω' := hV₀open.inter hV₁open
  have hKΩ' : K ⊆ Ω' := fun x hx => ⟨hKV₀ hx, hKV₁ hx⟩
  have hclV₀ : closure Ω' ⊆ closure V₀ := closure_mono inter_subset_left
  have hclV₁ : closure Ω' ⊆ closure V₁ := closure_mono inter_subset_right
  have hΩ'compact : IsCompact (closure Ω') :=
    hV₀compact.of_isClosed_subset isClosed_closure hclV₀
  have hΩ'Ω : closure Ω' ⊆ Ω := hclV₁.trans hV₁Ω
  exact ⟨Ω', hΩ'open, fun x hx => hKΩ' (Or.inl hx),
    fun x hx => hKΩ' (Or.inr hx), hΩ'compact, hΩ'Ω⟩
private theorem decomposition_restrict_isFiniteMeasure {K : Set Vec3} {J : Set ℝ}
    (hK : IsCompact (closure K)) (hJ : IsCompact (closure J)) :
    IsFiniteMeasure (volume.restrict (spaceTimeSet K J)) := by
  let L : Set ParabolicPoint :=
    parabolicHomeomorph ⁻¹' (closure K ×ˢ closure J)
  have hLtop : volume L < ⊤ := by
    change (volume : Measure (Vec3 × ℝ)) (closure K ×ˢ closure J) < ⊤
    exact (hK.prod hJ).measure_lt_top
  have hsub : spaceTimeSet K J ⊆ L := by
    intro z hz
    change z.1 ∈ closure K ∧ z.2 ∈ closure J
    exact ⟨subset_closure hz.1, subset_closure hz.2⟩
  apply isFiniteMeasure_restrict.mpr
  exact (lt_of_le_of_lt (measure_mono (μ := volume) hsub) hLtop).ne
/-- Slice integrability of a compactly supported test pair on a slightly larger set. -/
theorem decomposition_slice_integrability
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η ψ : Vec3 → ℝ} (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) :
    ∃ Ω' : Set Vec3, IsOpen Ω' ∧ tsupport η ⊆ Ω' ∧ tsupport ψ ⊆ Ω' ∧
      IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω ∧
      ∀ᵐ s ∂volume.restrict I,
        MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        Integrable (fun x : Vec3 => p (x, s)) (volume.restrict Ω') ∧
        Integrable (fun x : Vec3 => f (x, s)) (volume.restrict Ω') := by
  classical
  have hΩ : IsOpen Ω := h.1
  have hI : IsOpen I := h.2.1
  have exists_time_radius : ∀ s ∈ I, ∃ r : ℝ, 0 < r ∧ closedBall s r ⊆ I := by
    intro s hs
    obtain ⟨ε, hε, hεI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hs)
    refine ⟨ε / 2, by linarith only [hε], ?_⟩
    exact (closedBall_subset_ball (by linarith only [hε])).trans hεI
  obtain ⟨Ω', hΩ'open, hηΩ', hψΩ', hΩ'compact, hΩ'Ω⟩ :=
    decomposition_spatial_box hΩ hηc hηΩ hψc hψΩ
  let r : ℝ → ℝ := fun s => if hs : s ∈ I then
    Classical.choose (exists_time_radius s hs) else 1
  have hr_pos : ∀ s ∈ I, 0 < r s := by
    intro s hs
    simp only [r, dite_eq_left hs]
    exact (Classical.choose_spec (exists_time_radius s hs)).1
  have hr_sub : ∀ s ∈ I, closedBall s (r s) ⊆ I := by
    intro s hs
    simp only [r, dite_eq_left hs]
    exact (Classical.choose_spec (exists_time_radius s hs)).2
  let V : ℝ → Set ℝ := fun s => ball s (r s)
  obtain ⟨T, hTsub, hTcount, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin
      (s := I) (f := V) (by
        intro s hs
        refine mem_nhdsWithin.mpr ⟨V s, isOpen_ball, mem_ball_self (hr_pos s hs), ?_⟩
        exact inter_subset_left)
  have hlocal : ∀ s ∈ T, ∀ᵐ t ∂volume.restrict (closedBall s (r s)),
      MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω') ∧ Integrable
      (fun x : Vec3 => p (x, t)) (volume.restrict Ω') ∧ Integrable
      (fun x : Vec3 => f (x, t)) (volume.restrict Ω') := by
    intro s hs
    have hsI : s ∈ I := hTsub hs
    let J : Set ℝ := closedBall s (r s)
    have hJsub : J ⊆ I := hr_sub s hsI
    have hJcompact : IsCompact (closure J) := by
      simpa only [J, Metric.closure_closedBall] using ProperSpace.isCompact_closedBall s (r s)
    have hJord : J.OrdConnected := by
      rw [show J = Icc (s - r s) (s + r s) by
        ext t
        simp only [J, mem_closedBall, Real.dist_eq, mem_Icc, abs_le]
        constructor
        · rintro ⟨h₁, h₂⟩
          constructor <;> linarith only [h₁, h₂]
        · rintro ⟨h₁, h₂⟩
          constructor <;> linarith only [h₁, h₂]]
      exact ordConnected_Icc
    have hJsub' : closure J ⊆ I := by
      simpa only [J, Metric.closure_closedBall] using hJsub
    let hbox : localBox Ω I Ω' J :=
      ⟨hΩ'open, hΩ'compact, hΩ'Ω, hJord, hJcompact, hJsub'⟩
    obtain ⟨hu, _hDu, _hpmeas, _hfmeas, _hsup, _henergy, hp, hf, _hgrad⟩ :=
      h.2.2.2.2.2.1 Ω' J hbox
    let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
    have : IsFiniteMeasure μ := decomposition_restrict_isFiniteMeasure hΩ'compact hJcompact
    have hpInt : Integrable p μ := hp.integrable (by norm_num)
    have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
      rw [ENNReal.one_le_ofReal]
      linarith only [h.2.2.2.1]
    have hfInt : Integrable f μ := hf.integrable hqE
    have hpInt' : Integrable p (((volume : Measure Vec3).restrict Ω').prod
        (volume.restrict J)) := by
      rw [Measure.prod_restrict Ω' J]
      exact hpInt
    have hfInt' : Integrable f (((volume : Measure Vec3).restrict Ω').prod
        (volume.restrict J)) := by
      rw [Measure.prod_restrict Ω' J]
      exact hfInt
    have hu' : ∀ᵐ t ∂volume.restrict J, MemLp (fun x : Vec3 => u (x, t)) 2
        (volume.restrict Ω') := by
      filter_upwards [slice_memLp_ae_of_sws h hbox] with t ht
      exact ht.1
    have hp' :=
      hpInt'.prod_left_ae
    have hf' :=
      hfInt'.prod_left_ae
    filter_upwards [hu', hp', hf'] with t htu htp htf
    exact ⟨htu, htp, htf⟩
  have hlocal_ball : ∀ s ∈ T, ∀ᵐ t ∂volume.restrict (V s),
      MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω') ∧ Integrable
      (fun x : Vec3 => p (x, t)) (volume.restrict Ω') ∧ Integrable
      (fun x : Vec3 => f (x, t)) (volume.restrict Ω') := by
    intro s hs
    exact ae_restrict_of_ae_restrict_of_subset
      (by simpa only [V] using (Metric.ball_subset_closedBall :
        ball s (r s) ⊆ closedBall s (r s))) (hlocal s hs)
  have hunion :=
    (ae_restrict_biUnion_iff V hTcount _).2 hlocal_ball
  refine ⟨Ω', hΩ'open, hηΩ', hψΩ', hΩ'compact, hΩ'Ω, ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset hcover hunion
private theorem decomposition_support_spatialDeriv_subset {φ : Vec3 → ℝ} (i : Fin 3) :
    Function.support (spatialDeriv φ i) ⊆ tsupport φ := by
  intro x hx
  by_contra hxt
  exact hx (by simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt])
private theorem decomposition_ts_support_spatialDeriv_subset {φ : Vec3 → ℝ} (i : Fin 3) :
    tsupport (spatialDeriv φ i) ⊆ tsupport φ :=
  closure_minimal (decomposition_support_spatialDeriv_subset i) (isClosed_tsupport φ)
private theorem decomposition_support_mixedSecond_subset {φ : Vec3 → ℝ} (i j : Fin 3) :
    Function.support (mixedSecond φ i j) ⊆ tsupport φ :=
  (decomposition_support_spatialDeriv_subset (φ := spatialDeriv φ j) i).trans
    (decomposition_ts_support_spatialDeriv_subset j)
private theorem decomposition_ts_support_mixedSecond_subset {φ : Vec3 → ℝ} (i j : Fin 3) :
    tsupport (mixedSecond φ i j) ⊆ tsupport φ :=
  closure_minimal (decomposition_support_mixedSecond_subset i j) (isClosed_tsupport φ)
private theorem decomposition_hasCompactSupport_spatialDeriv {φ : Vec3 → ℝ}
    (hφc : HasCompactSupport φ) (i : Fin 3) : HasCompactSupport (spatialDeriv φ i) :=
  HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    (decomposition_support_spatialDeriv_subset i)
private theorem decomposition_hasCompactSupport_mixedSecond {φ : Vec3 → ℝ}
    (hφc : HasCompactSupport φ) (i j : Fin 3) : HasCompactSupport (mixedSecond φ i j) :=
  HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    (decomposition_support_mixedSecond_subset i j)
private theorem decomposition_spatial_restrict_isFiniteMeasure {K : Set Vec3}
    (hK : IsCompact (closure K)) : IsFiniteMeasure (volume.restrict K) := by
  apply isFiniteMeasure_restrict.mpr
  exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
    hK.measure_lt_top).ne
private lemma pressure_laplace_cutoff_identity_ae_hfInt_1 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
      (Ω' : Set Vec3) (s : ℝ),
      MemLp (ε := Vec3) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => u (x, s))
            (2 : ℝ≥0∞) (Measure.restrict volume Ω') ∧
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => p (x, s))
              (Measure.restrict volume Ω') ∧
            @Integrable Vec3 _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s))
              (Measure.restrict volume Ω') →
        ∀ (i : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s) i)
            (Measure.restrict volume Ω')
    := by
  intro u p f Ω' s hLp_s i
  apply hLp_s.2.2.mono
    ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      hLp_s.2.2.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖f (x, s) i‖ ≤ ‖f (x, s)‖
  rw [Pi.norm_def]
  simpa only [coe_nnnorm] using
    (NNReal.coe_le_coe.mpr
      (Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
        (f := fun b => ‖f (x, s) b‖₊) (Finset.mem_univ i)))

private lemma pressure_laplace_cutoff_identity_ae_hscalar_2 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} (Ω' : Set Vec3) (s : ℝ),
      MemLp (ε := Vec3) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => u (x, s))
            (2 : ℝ≥0∞) (Measure.restrict volume Ω') ∧
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => p (x, s))
              (Measure.restrict volume Ω') ∧
            @Integrable Vec3 _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s))
              (Measure.restrict volume Ω') →
        ∀ {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => p (x, s) * g x) Ω volume
    := by
  intro Ω u p f Ω' s hLp_s g hg hgc hgΩ
  exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
    hLp_s.2.1 hg hgc hgΩ).integrableOn

private lemma pressure_laplace_cutoff_identity_ae_huScalar_3 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} (Ω' : Set Vec3) (s : ℝ),
      (∀ (i : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => u (x, s) i)
            (Measure.restrict volume Ω')) →
        ∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => u (x, s) i * g x) Ω volume
    := by
  intro Ω u Ω' s huInt i g hg hgc hgΩ
  exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
    (huInt i) hg hgc hgΩ).integrableOn

private lemma pressure_laplace_cutoff_identity_ae_huuScalar_4 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} (Ω' : Set Vec3) (s : ℝ),
      (∀ (i : Fin (3 : ℕ)),
          MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => u (x, s) i)
            (2 : ℝ≥0∞) (Measure.restrict volume Ω')) →
        ∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => u (x, s) i * u (x, s) j * g x) Ω volume
    := by
  intro Ω u Ω' s huComp i j g hg hgc hgΩ
  exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
    ((huComp i).integrable_mul (huComp j)) hg hgc hgΩ).integrableOn

private lemma pressure_laplace_cutoff_identity_ae_hfScalar_5 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} (Ω' : Set Vec3) (s : ℝ),
      (∀ (i : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s) i)
            (Measure.restrict volume Ω')) →
        ∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => f (x, s) i * g x) Ω volume
    := by
  intro Ω f Ω' s hfInt i g hg hgc hgΩ
  exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
    (hfInt i) hg hgc hgΩ).integrableOn

private lemma pressure_laplace_cutoff_identity_ae_hLapExpand_6 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        ∀ {ψ : Vec3 → ℝ},
          ContDiff ℝ (⊤ : ℕ∞) ψ →
            ∀ (s : ℝ),
              IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => p (x, s) * (η x * spatialLaplacian ψ x)) Ω volume →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => p (x, s) * (ψ x * spatialLaplacian η x)) Ω volume →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                      (fun (x : Vec3) => p (x, s) * spatialGradDot η ψ x) Ω volume →
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                        fun (x : Vec3) =>
                        p (x, s) * spatialLaplacian (fun (y : Vec3) => η y * ψ y) x) =
                      ((@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                            fun (x : Vec3) => p (x, s) * (η x * spatialLaplacian ψ x)) +
                          (2 : ℝ) *
                            @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                              (Measure.restrict volume Ω) fun (x : Vec3) =>
                              spatialGradDot η ψ x * p (x, s)) +
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                          fun (x : Vec3) => p (x, s) * (ψ x * spatialLaplacian η x)
    := by
  intro Ω p η hη ψ hψ s hp0 hp1 hgradSum
  have hpt : ∀ x, p (x, s) * spatialLaplacian (fun y => η y * ψ y) x =
      p (x, s) * (η x * spatialLaplacian ψ x) +
        2 * (p (x, s) * spatialGradDot η ψ x) +
        p (x, s) * (ψ x * spatialLaplacian η x) := by
    intro x
    rw [congrFun (spatialLaplacian_mul_smooth hη hψ) x]
    ring
  calc
    (∫ x in Ω, p (x, s) * spatialLaplacian (fun y => η y * ψ y) x) =
        ∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) +
          2 * (p (x, s) * spatialGradDot η ψ x) +
          p (x, s) * (ψ x * spatialLaplacian η x) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x)) +
        ∫ x in Ω, 2 * (p (x, s) * spatialGradDot η ψ x)) +
        ∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x) := by
      calc
        (∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) +
            2 * (p (x, s) * spatialGradDot η ψ x) +
            p (x, s) * (ψ x * spatialLaplacian η x)) =
            (∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) +
              2 * (p (x, s) * spatialGradDot η ψ x)) +
              ∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x) := by
          simpa only [Pi.add_apply] using
            (integral_add (hp0.add (hgradSum.const_mul 2)) hp1)
        _ = ((∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x)) +
            ∫ x in Ω, 2 * (p (x, s) * spatialGradDot η ψ x)) +
            ∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x) := by
          rw [integral_add hp0 (hgradSum.const_mul 2)]
    _ = (∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x)) +
        2 * (∫ x in Ω, spatialGradDot η ψ x * p (x, s)) +
        ∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x) := by
      have hcomm : (∫ x in Ω, p (x, s) * spatialGradDot η ψ x) =
          ∫ x in Ω, spatialGradDot η ψ x * p (x, s) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      rw [integral_const_mul, hcomm]

private lemma pressure_laplace_cutoff_identity_ae_hConvExpand_7 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        ∀ {ψ : Vec3 → ℝ},
          ContDiff ℝ (⊤ : ℕ∞) ψ →
            ∀ (s : ℝ),
              IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) =>
                    ∑ i : Fin (3 : ℕ),
                      ∑ j : Fin (3 : ℕ), u (x, s) i * u (x, s) j * (η x * mixedSecond ψ i j x))
                  Ω volume →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) =>
                      ∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ), u (x, s) i * u (x, s) j * (mixedSecond η i j x * ψ x))
                    Ω volume →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                      (fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ),
                          ∑ j : Fin (3 : ℕ),
                            u (x, s) i * u (x, s) j * (spatialDeriv η j x * spatialDeriv ψ i x))
                      Ω volume →
                    IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) =>
                          ∑ i : Fin (3 : ℕ),
                            ∑ j : Fin (3 : ℕ),
                              u (x, s) i * u (x, s) j * (spatialDeriv η i x * spatialDeriv ψ j x))
                        Ω volume →
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                          fun (x : Vec3) =>
                          ∑ i : Fin (3 : ℕ),
                            ∑ j : Fin (3 : ℕ),
                              u (x, s) i * u (x, s) j *
                                mixedSecond (fun (y : Vec3) => η y * ψ y) i j x) =
                        (HAdd.hAdd (α := ℝ)
                              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume Ω) fun (x : Vec3) =>
                                ∑ i : Fin (3 : ℕ),
                                  ∑ j : Fin (3 : ℕ),
                                    u (x, s) i * u (x, s) j * (η x * mixedSecond ψ i j x))
                              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume Ω) fun (x : Vec3) =>
                                ∑ i : Fin (3 : ℕ),
                                  ∑ j : Fin (3 : ℕ),
                                    u (x, s) i * u (x, s) j * (mixedSecond η i j x * ψ x)) +
                            @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                              (Measure.restrict volume Ω) fun (x : Vec3) =>
                              ∑ i : Fin (3 : ℕ),
                                ∑ j : Fin (3 : ℕ),
                                  u (x, s) i * u (x, s) j *
                                    (spatialDeriv η j x * spatialDeriv ψ i x)) +
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                            (Measure.restrict volume Ω) fun (x : Vec3) =>
                            ∑ i : Fin (3 : ℕ),
                              ∑ j : Fin (3 : ℕ),
                                u (x, s) i * u (x, s) j * (spatialDeriv η i x * spatialDeriv ψ j x)
    := by
  intro Ω u η hη ψ hψ s hUU0Sum hUU1Sum hUU2Sum hUU3Sum
  let A : Vec3 → ℝ := fun x => ∑ i, ∑ j,
    u (x, s) i * u (x, s) j * (η x * mixedSecond ψ i j x)
  let B : Vec3 → ℝ := fun x => ∑ i, ∑ j,
    u (x, s) i * u (x, s) j * (mixedSecond η i j x * ψ x)
  let C : Vec3 → ℝ := fun x => ∑ i, ∑ j,
    u (x, s) i * u (x, s) j *
      (spatialDeriv η j x * spatialDeriv ψ i x)
  let D : Vec3 → ℝ := fun x => ∑ i, ∑ j,
    u (x, s) i * u (x, s) j *
      (spatialDeriv η i x * spatialDeriv ψ j x)
  have hA : IntegrableOn A Ω volume := by
    simpa [A] using hUU0Sum
  have hB : IntegrableOn B Ω volume := by
    simpa [B] using hUU1Sum
  have hC : IntegrableOn C Ω volume := by
    simpa [C] using hUU2Sum
  have hD : IntegrableOn D Ω volume := by
    simpa [D] using hUU3Sum
  have hpt : ∀ x, (∑ i, ∑ j, u (x, s) i * u (x, s) j *
      mixedSecond (fun y => η y * ψ y) i j x) =
      A x + B x + C x + D x := by
    intro x
    simp only [A, B, C, D]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [spatialSecondDeriv_mul_smooth hη hψ i j x]
    ring
  calc
    (∫ x in Ω, ∑ i, ∑ j,
      u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x) =
        ∫ x in Ω, A x + B x + C x + D x := by
      exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ x in Ω, (A x + B x) + (C x + D x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (∫ x in Ω, A x + B x) + (∫ x in Ω, C x + D x) := by
      simpa only [Pi.add_apply] using
        (integral_add (hA.add hB) (hC.add hD))
    _ = ((∫ x in Ω, A x) + (∫ x in Ω, B x)) +
        ((∫ x in Ω, C x) + (∫ x in Ω, D x)) := by
      rw [integral_add hA hB]
      rw [integral_add hC hD]
    _ = (∫ x in Ω, ∑ i, ∑ j,
        u (x, s) i * u (x, s) j * (η x * mixedSecond ψ i j x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j * (mixedSecond η i j x * ψ x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j *
            (spatialDeriv η i x * spatialDeriv ψ j x)) := by
      simp only [A, B, C, D]
      ring

private lemma pressure_laplace_cutoff_identity_ae_hForceExpand_8 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        ∀ {ψ : Vec3 → ℝ},
          ContDiff ℝ (⊤ : ℕ∞) ψ →
            ∀ (s : ℝ),
              IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => ∑ i : Fin (3 : ℕ), f (x, s) i * (η x * spatialDeriv ψ i x)) Ω
                  volume →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => ∑ i : Fin (3 : ℕ), f (x, s) i * (ψ x * spatialDeriv η i x)) Ω
                    volume →
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                      fun (x : Vec3) =>
                      ∑ i : Fin (3 : ℕ),
                        f (x, s) i * spatialDeriv (fun (y : Vec3) => η y * ψ y) i x) =
                    HAdd.hAdd (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                        fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ), f (x, s) i * (η x * spatialDeriv ψ i x))
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                        fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ), f (x, s) i * (ψ x * spatialDeriv η i x))
    := by
  intro Ω f η hη ψ hψ s hf0Sum hf1Sum
  have hpt : ∀ x, (∑ i, f (x, s) i * spatialDeriv (fun y => η y * ψ y) i x) =
      (∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) +
        (∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)) := by
    intro x
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [spatialDeriv_mul (hη.differentiable (by simp) x)
      (hψ.differentiable (by simp) x) i]
    ring
  calc
    (∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv (fun y => η y * ψ y) i x) =
        ∫ x in Ω, (∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) +
          (∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x in Ω, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) +
        ∫ x in Ω, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x) := by
      rw [integral_add hf0Sum hf1Sum]

private lemma pressure_laplace_cutoff_identity_ae_hCorrZero_9 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {c : ℝ → Vec3} {ψ : Vec3 → ℝ}
      (s : ℝ),
      (∀ (j : Fin (3 : ℕ)),
          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
            (fun (x : Vec3) =>
              c s j *
                ∑ i : Fin (3 : ℕ), u (x, s) i * mixedSecond (fun (y : Vec3) => η y * ψ y) i j x)
            Ω volume) →
        (∀ (j : Fin (3 : ℕ)),
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                fun (x : Vec3) =>
                ∑ i : Fin (3 : ℕ), u (x, s) i * mixedSecond (fun (y : Vec3) => η y * ψ y) i j x) =
              (0 : ℝ)) →
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
              fun (x : Vec3) =>
              ∑ j : Fin (3 : ℕ),
                c s j *
                  ∑ i : Fin (3 : ℕ), u (x, s) i * mixedSecond (fun (y : Vec3) => η y * ψ y) i j x) =
            (0 : ℝ)
    := by
  intro Ω u η c ψ s hCorrInner hdivProd
  calc
    (∫ x in Ω, ∑ j, c s j * ∑ i, u (x, s) i *
        mixedSecond (fun y => η y * ψ y) i j x) =
        ∑ j, ∫ x in Ω, c s j * ∑ i, u (x, s) i *
          mixedSecond (fun y => η y * ψ y) i j x := by
      simpa using integral_finsetSum (μ := volume.restrict Ω)
        (Finset.univ : Finset (Fin 3)) (fun j _ => hCorrInner j)
    _ = ∑ j, c s j * (∫ x in Ω, ∑ i, u (x, s) i *
        mixedSecond (fun y => η y * ψ y) i j x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hdivProd j]
      simp

private lemma pressure_laplace_cutoff_identity_ae_hBalance_10 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {c : ℝ → Vec3} {ψ : Vec3 → ℝ}
      (s : ℝ),
      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
          (fun (x : Vec3) =>
            ∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                u (x, s) i * u (x, s) j * mixedSecond (fun (y : Vec3) => η y * ψ y) i j x)
          Ω volume →
        IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
            (fun (x : Vec3) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  pressureUTensor u c (x, s) i j * mixedSecond (fun (y : Vec3) => η y * ψ y) i j x)
            Ω volume →
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                fun (x : Vec3) =>
                ∑ j : Fin (3 : ℕ),
                  c s j *
                    ∑ i : Fin (3 : ℕ),
                      u (x, s) i * mixedSecond (fun (y : Vec3) => η y * ψ y) i j x) =
              (0 : ℝ) →
            HAdd.hAdd (α := ℝ)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                  fun (x : Vec3) =>
                  ∑ i : Fin (3 : ℕ),
                    ∑ j : Fin (3 : ℕ),
                      pressureUTensor u c (x, s) i j *
                        mixedSecond (fun (y : Vec3) => η y * ψ y) i j x)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                  fun (x : Vec3) =>
                  ∑ i : Fin (3 : ℕ),
                    ∑ j : Fin (3 : ℕ),
                      u (x, s) i * u (x, s) j * mixedSecond (fun (y : Vec3) => η y * ψ y) i j x) =
              (0 : ℝ)
    := by
  intro Ω u η c ψ s hUUprodSum hUProdSum hCorrZero
  have hpoint : ∀ x, (∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * mixedSecond (fun y => η y * ψ y) i j x) +
        (∑ i, ∑ j,
          u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x) =
      ∑ j, c s j * ∑ i, u (x, s) i *
        mixedSecond (fun y => η y * ψ y) i j x := by
    intro x
    calc
      (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          mixedSecond (fun y => η y * ψ y) i j x) +
          (∑ i, ∑ j, u (x, s) i * u (x, s) j *
            mixedSecond (fun y => η y * ψ y) i j x) =
          ∑ i, ∑ j, ((pressureUTensor u c (x, s) i j *
            mixedSecond (fun y => η y * ψ y) i j x) +
            (u (x, s) i * u (x, s) j *
              mixedSecond (fun y => η y * ψ y) i j x)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib]
      _ = ∑ i, ∑ j, c s j * (u (x, s) i *
          mixedSecond (fun y => η y * ψ y) i j x) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [pressureUTensor]
        ring
      _ = ∑ j, ∑ i, c s j * (u (x, s) i *
          mixedSecond (fun y => η y * ψ y) i j x) := by
        rw [Finset.sum_comm]
      _ = ∑ j, c s j * ∑ i, u (x, s) i *
          mixedSecond (fun y => η y * ψ y) i j x := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.mul_sum]
  calc
    (∫ x in Ω, ∑ i, ∑ j,
        pressureUTensor u c (x, s) i j * mixedSecond (fun y => η y * ψ y) i j x) +
        ∫ x in Ω, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x =
        ∫ x in Ω, (∑ i, ∑ j,
          pressureUTensor u c (x, s) i j * mixedSecond (fun y => η y * ψ y) i j x) +
          (∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x) := by
      simpa only [Pi.add_apply] using
        (integral_add hUProdSum hUUprodSum).symm
    _ = ∫ x in Ω, ∑ j, c s j * ∑ i, u (x, s) i *
        mixedSecond (fun y => η y * ψ y) i j x :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = 0 := hCorrZero

private lemma pressure_laplace_cutoff_identity_ae_hUExpand_11 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        ∀ {c : ℝ → Vec3} {ψ : Vec3 → ℝ},
          ContDiff ℝ (⊤ : ℕ∞) ψ →
            ∀ (s : ℝ),
              IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) =>
                    ∑ i : Fin (3 : ℕ),
                      ∑ j : Fin (3 : ℕ),
                        pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x))
                  Ω volume →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) =>
                      ∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x))
                    Ω volume →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                      (fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ),
                          ∑ j : Fin (3 : ℕ),
                            pressureUTensor u c (x, s) i j *
                              (spatialDeriv η i x * spatialDeriv ψ j x))
                      Ω volume →
                    IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) =>
                          ∑ i : Fin (3 : ℕ),
                            ∑ j : Fin (3 : ℕ),
                              pressureUTensor u c (x, s) i j *
                                (spatialDeriv η j x * spatialDeriv ψ i x))
                        Ω volume →
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                          fun (x : Vec3) =>
                          ∑ i : Fin (3 : ℕ),
                            ∑ j : Fin (3 : ℕ),
                              pressureUTensor u c (x, s) i j *
                                mixedSecond (fun (y : Vec3) => η y * ψ y) i j x) =
                        (HAdd.hAdd (α := ℝ)
                              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume Ω) fun (x : Vec3) =>
                                ∑ i : Fin (3 : ℕ),
                                  ∑ j : Fin (3 : ℕ),
                                    pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x))
                              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume Ω) fun (x : Vec3) =>
                                ∑ i : Fin (3 : ℕ),
                                  ∑ j : Fin (3 : ℕ),
                                    pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) +
                            @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                              (Measure.restrict volume Ω) fun (x : Vec3) =>
                              ∑ i : Fin (3 : ℕ),
                                ∑ j : Fin (3 : ℕ),
                                  pressureUTensor u c (x, s) i j *
                                    (spatialDeriv η j x * spatialDeriv ψ i x)) +
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                            (Measure.restrict volume Ω) fun (x : Vec3) =>
                            ∑ i : Fin (3 : ℕ),
                              ∑ j : Fin (3 : ℕ),
                                pressureUTensor u c (x, s) i j *
                                  (spatialDeriv η i x * spatialDeriv ψ j x)
    := by
  intro Ω u η hη c ψ hψ s hU0Sum hU1Sum hU2Sum hU3Sum
  have hpt : ∀ x : Vec3, (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
      mixedSecond (fun y => η y * ψ y) i j x) =
      (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (η x * mixedSecond ψ i j x)) +
        (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (mixedSecond η i j x * ψ x)) +
        (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (spatialDeriv η j x * spatialDeriv ψ i x)) +
        (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (spatialDeriv η i x * spatialDeriv ψ j x)) := by
    intro x
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [spatialSecondDeriv_mul_smooth hη hψ i j x]
    ring
  calc
    (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        mixedSecond (fun y => η y * ψ y) i j x) =
        ∫ x in Ω, (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (η x * mixedSecond ψ i j x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (mixedSecond η i j x * ψ x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η i x * spatialDeriv ψ j x)) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ x in Ω, ((∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (η x * mixedSecond ψ i j x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (mixedSecond η i j x * ψ x))) +
          ((∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η i x * spatialDeriv ψ j x))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (∫ x in Ω, (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (η x * mixedSecond ψ i j x)) +
        (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (mixedSecond η i j x * ψ x))) +
        (∫ x in Ω, (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (spatialDeriv η j x * spatialDeriv ψ i x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η i x * spatialDeriv ψ j x))) := by
      simpa only [Pi.add_apply] using
        (integral_add (hU0Sum.add hU1Sum) (hU3Sum.add hU2Sum))
    _ = ((∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (η x * mixedSecond ψ i j x)) +
        (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (mixedSecond η i j x * ψ x))) +
        ((∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (spatialDeriv η j x * spatialDeriv ψ i x)) +
        (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (spatialDeriv η i x * spatialDeriv ψ j x))) := by
      rw [integral_add hU0Sum hU1Sum]
      rw [integral_add hU3Sum hU2Sum]
    _ = (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (η x * mixedSecond ψ i j x)) +
        (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (mixedSecond η i j x * ψ x)) +
        (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (spatialDeriv η j x * spatialDeriv ψ i x)) +
        (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (spatialDeriv η i x * spatialDeriv ψ j x)) := by
      ring

private lemma pressure_laplace_cutoff_identity_ae_hdiv_1 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {η ψ : Vec3 → ℝ},
          (ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (x : Vec3) => η x * ψ x) →
            (HasCompactSupport (β := ℝ) fun (x : Vec3) => η x * ψ x) →
              (tsupport (α := ℝ) fun (x : Vec3) => η x * ψ x) ⊆ Ω →
                ∀ᵐ (s : ℝ) ∂Measure.restrict volume I,
                  ∀ (j : Fin (3 : ℕ)),
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                        fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ),
                          u (x, s) i *
                            spatialDeriv (spatialDeriv (fun (y : Vec3) => η y * ψ y) j) i x) =
                      (0 : ℝ)
    := by
  intro Ω I q u Du p f h η ψ hprod hprodc hprodΩ
  rw [ae_all_iff]
  intro j
  have hd := divfree_slice_weak_of_suitable h
    (spatialDeriv (fun y => η y * ψ y) j)
    (contDiff_spatialDeriv_smooth hprod j)
    (hprodc.fderiv_apply (𝕜 := ℝ) (basisVec j))
    ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hprodΩ)
  filter_upwards [hd] with s hs
  simpa only [spatialDeriv] using hs

private lemma pressure_laplace_cutoff_identity_ae_hUScalar_2 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} (Ω' : Set Vec3) (s : ℝ),
      (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => u (x, s) i * g x) Ω volume) →
        (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
            Continuous g →
              HasCompactSupport g →
                tsupport g ⊆ Ω' →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => u (x, s) i * u (x, s) j * g x) Ω volume) →
          ∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
            Continuous g →
              HasCompactSupport g →
                tsupport g ⊆ Ω' →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume
    := by
  intro Ω u c Ω' s huScalar huuScalar i j g hg hgc hgΩ
  have hraw := huuScalar (i := i) (j := j) hg hgc hgΩ
  have hlin := huScalar (i := i) hg hgc hgΩ
  have hsum : IntegrableOn
      (fun x => -(u (x, s) i * u (x, s) j * g x) +
        c s j * (u (x, s) i * g x)) Ω volume :=
    hraw.neg.add (hlin.const_mul (c s j))
  exact hsum.congr (Filter.Eventually.of_forall fun x => by
    simp only [pressureUTensor]
    ring)

private lemma pressure_laplace_cutoff_identity_ae_hfinite_3 :
    ∀ {Ω : Set Vec3} {g : Fin (3 : ℕ) → Vec3 → ℝ},
      (∀ (i : Fin (3 : ℕ)), IntegrableOn (mα := MeasureSpace.toMeasurableSpace) (g i) Ω volume) →
        IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
          (fun (x : Vec3) => ∑ i : Fin (3 : ℕ), g i x) Ω volume
    := by
  intro Ω g hg
  have hs := integrable_finsetSum' (Finset.univ : Finset (Fin 3)) (fun i _ => hg i)
  have heq : (fun x => ∑ i, g i x) = ∑ i, (fun x => g i x) := by
    funext x; simp only [Finset.sum_apply]
  change Integrable (fun x => ∑ i, g i x) (volume.restrict Ω)
  rw [heq]
  exact hs

theorem pressure_laplace_cutoff_identity_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I,
      ∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) =
        (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)
          ) + (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)
          ) + (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j *
              (spatialDeriv η i x * spatialDeriv ψ j x)
          ) + (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j *
              (spatialDeriv η j x * spatialDeriv ψ i x)
          ) - (∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x))
          - 2 * (∫ x in Ω, (spatialGradDot η ψ x) * p (x, s))
          - (∫ x in Ω, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x))
          - (∫ x in Ω, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)) := by
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * ψ x) := hη.mul hψ
  have hprodc : HasCompactSupport (fun x => η x * ψ x) :=
    hηc.mul_right (f' := ψ)
  have hprodΩ : tsupport (fun x => η x * ψ x) ⊆ Ω :=
    (tsupport_mul_subset_left (f := η) (g := ψ)).trans hηΩ
  have hbase := pressure_slice_identity_ae h hprod hprodc hprodΩ
  have hdiv := @pressure_laplace_cutoff_identity_ae_hdiv_1 Ω I q u Du p f h η ψ hprod hprodc hprodΩ
  obtain ⟨Ω', hΩ'open, hηΩ', hψΩ', hΩ'compact, hΩ'Ω, hLp⟩ :=
    decomposition_slice_integrability h hηc hηΩ hψc hψΩ
  have : IsFiniteMeasure (volume.restrict Ω') :=
    decomposition_spatial_restrict_isFiniteMeasure hΩ'compact
  filter_upwards [hbase, hdiv, hLp] with s hbase_s hdiv_s hLp_s
  have huComp (i : Fin 3) :=
    hLp_s.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have huInt (i : Fin 3) :=
    huComp i |>.integrable (by norm_num)
  have hfInt (i : Fin 3) := @pressure_laplace_cutoff_identity_ae_hfInt_1 u p f Ω' s hLp_s i
  have hscalar {g : Vec3 → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
      (hgΩ : tsupport g ⊆ Ω') := @pressure_laplace_cutoff_identity_ae_hscalar_2 Ω u p f Ω' s hLp_s
        g hg hgc hgΩ
  have huScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :=
        @pressure_laplace_cutoff_identity_ae_huScalar_3 Ω u Ω' s huInt i g hg hgc hgΩ
  have huuScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :=
        @pressure_laplace_cutoff_identity_ae_huuScalar_4 Ω u Ω' s huComp i j g hg hgc hgΩ
  have hfScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :=
        @pressure_laplace_cutoff_identity_ae_hfScalar_5 Ω f Ω' s hfInt i g hg hgc hgΩ
  have hUScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :=
        @pressure_laplace_cutoff_identity_ae_hUScalar_2 Ω u c Ω' s huScalar huuScalar i j g hg hgc
        hgΩ
  have hprodΩ' : tsupport (fun x => η x * ψ x) ⊆ Ω' :=
    (tsupport_mul_subset_left (f := η) (g := ψ)).trans hηΩ'
  have hηd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) :=
    contDiff_spatialDeriv_smooth hη i
  have hψd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i) :=
    contDiff_spatialDeriv_smooth hψ i
  have hηm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) :=
    contDiff_mixedSecond_smooth hη i j
  have hψm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have hηdc (i : Fin 3) : HasCompactSupport (spatialDeriv η i) :=
    decomposition_hasCompactSupport_spatialDeriv hηc i
  have hp0 : IntegrableOn (fun x => p (x, s) * (η x * spatialLaplacian ψ x)) Ω volume :=
    hscalar (hη.mul (contDiff_spatialLaplacian_smooth hψ)).continuous
      (hηc.mul_right (f' := spatialLaplacian ψ))
      ((tsupport_mul_subset_left (f := η) (g := spatialLaplacian ψ)).trans hηΩ')
  have hp1 : IntegrableOn (fun x => p (x, s) * (ψ x * spatialLaplacian η x)) Ω volume :=
    hscalar (hψ.mul (contDiff_spatialLaplacian_smooth hη)).continuous
      (hψc.mul_right (f' := spatialLaplacian η))
      ((tsupport_mul_subset_left (f := ψ) (g := spatialLaplacian η)).trans hψΩ')
  have hpgrad (j : Fin 3) :=
    hscalar ((hηd j).mul (hψd j)).continuous
      ((hηdc j).mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ j)).trans
        ((decomposition_ts_support_spatialDeriv_subset j).trans hηΩ'))
  have hUU (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      mixedSecond (fun y => η y * ψ y) i j x) Ω volume :=
    huuScalar (contDiff_mixedSecond_smooth hprod i j).continuous
      (decomposition_hasCompactSupport_mixedSecond hprodc i j)
      ((decomposition_ts_support_mixedSecond_subset i j).trans hprodΩ')
  have hUU0 (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      (η x * mixedSecond ψ i j x)) Ω volume :=
    huuScalar ((hη.mul (hψm i j)).continuous)
      (hηc.mul_right (f' := mixedSecond ψ i j))
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')
  have hUU1 (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      (mixedSecond η i j x * ψ x)) Ω volume :=
    huuScalar ((hηm i j).mul hψ).continuous
      (hψc.mul_left (f := mixedSecond η i j))
      ((tsupport_mul_subset_right (f := mixedSecond η i j) (g := ψ)).trans hψΩ')
  have hUU2 (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      (spatialDeriv η j x * spatialDeriv ψ i x)) Ω volume :=
    huuScalar ((hηd j).mul (hψd i)).continuous
      ((hηdc j).mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ i)).trans
        ((decomposition_ts_support_spatialDeriv_subset j).trans hηΩ'))
  have hUU3 (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      (spatialDeriv η i x * spatialDeriv ψ j x)) Ω volume :=
    huuScalar ((hηd i).mul (hψd j)).continuous
      ((hηdc i).mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := spatialDeriv η i)
        (g := spatialDeriv ψ j)).trans
        ((decomposition_ts_support_spatialDeriv_subset i).trans hηΩ'))
  have hU0 (i j : Fin 3) : IntegrableOn
      (fun x => pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) Ω volume :=
    hUScalar ((hη.mul (hψm i j)).continuous)
      (hηc.mul_right (f' := mixedSecond ψ i j))
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')
  have hU1 (i j : Fin 3) : IntegrableOn (fun x => pressureUTensor u c (x, s) i j *
      (mixedSecond η i j x * ψ x)) Ω volume :=
    hUScalar ((hηm i j).mul hψ).continuous
      (hψc.mul_left (f := mixedSecond η i j))
      ((tsupport_mul_subset_right (f := mixedSecond η i j) (g := ψ)).trans hψΩ')
  have hU2 (i j : Fin 3) : IntegrableOn (fun x => pressureUTensor u c (x, s) i j *
      (spatialDeriv η i x * spatialDeriv ψ j x)) Ω volume :=
    hUScalar ((hηd i).mul (hψd j)).continuous
      ((hηdc i).mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := spatialDeriv η i)
        (g := spatialDeriv ψ j)).trans
        ((decomposition_ts_support_spatialDeriv_subset i).trans hηΩ'))
  have hU3 (i j : Fin 3) : IntegrableOn (fun x => pressureUTensor u c (x, s) i j *
      (spatialDeriv η j x * spatialDeriv ψ i x)) Ω volume :=
    hUScalar ((hηd j).mul (hψd i)).continuous
      ((hηdc j).mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ i)).trans
        ((decomposition_ts_support_spatialDeriv_subset j).trans hηΩ'))
  have hf0 (i : Fin 3) : IntegrableOn
      (fun x => f (x, s) i * (η x * spatialDeriv ψ i x)) Ω volume :=
    hfScalar ((hη.mul (hψd i)).continuous)
      (hηc.mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηΩ')
  have hf1 (i : Fin 3) : IntegrableOn
      (fun x => f (x, s) i * (ψ x * spatialDeriv η i x)) Ω volume :=
    hfScalar ((hψ.mul (hηd i)).continuous)
      (hψc.mul_right (f' := spatialDeriv η i))
      ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η i)).trans hψΩ')
  have hfinite {g : Fin 3 → Vec3 → ℝ} (hg : ∀ i, IntegrableOn (g i) Ω volume) :=
    @pressure_laplace_cutoff_identity_ae_hfinite_3 Ω g hg
  have hpgsum :=
    hfinite (fun j => hpgrad j)
  have hUUprodSum :=
    hfinite (fun i => hfinite (fun j => hUU i j))
  have hUU0Sum :=
    hfinite (fun i => hfinite (fun j => hUU0 i j))
  have hUU1Sum :=
    hfinite (fun i => hfinite (fun j => hUU1 i j))
  have hUU2Sum :=
    hfinite (fun i => hfinite (fun j => hUU2 i j))
  have hUU3Sum :=
    hfinite (fun i => hfinite (fun j => hUU3 i j))
  have hU0Sum :=
    hfinite (fun i => hfinite (fun j => hU0 i j))
  have hU1Sum :=
    hfinite (fun i => hfinite (fun j => hU1 i j))
  have hU2Sum :=
    hfinite (fun i => hfinite (fun j => hU2 i j))
  have hU3Sum :=
    hfinite (fun i => hfinite (fun j => hU3 i j))
  have hf0Sum :=
    hfinite (fun i => hf0 i)
  have hf1Sum :=
    hfinite (fun i => hf1 i)
  have hgradSum : IntegrableOn
      (fun x => p (x, s) * spatialGradDot η ψ x) Ω volume := by
    apply hpgsum.congr
    filter_upwards [] with x
    simp only [spatialGradDot]
    rw [Finset.mul_sum]
  have hLapExpand := @pressure_laplace_cutoff_identity_ae_hLapExpand_6 Ω p η hη ψ hψ s hp0 hp1
    hgradSum
  have hConvExpand := @pressure_laplace_cutoff_identity_ae_hConvExpand_7 Ω u η hη ψ hψ s hUU0Sum
    hUU1Sum hUU2Sum hUU3Sum
  have hForceExpand := @pressure_laplace_cutoff_identity_ae_hForceExpand_8 Ω f η hη ψ hψ s hf0Sum
    hf1Sum
  have hUProd (i j : Fin 3) : IntegrableOn
      (fun x => pressureUTensor u c (x, s) i j *
        mixedSecond (fun y => η y * ψ y) i j x)
      Ω volume :=
    hUScalar (contDiff_mixedSecond_smooth hprod i j).continuous
      (decomposition_hasCompactSupport_mixedSecond hprodc i j)
      ((decomposition_ts_support_mixedSecond_subset i j).trans hprodΩ')
  have hUProdSum :=
    hfinite (fun i => hfinite (fun j => hUProd i j))
  have huProd (i j : Fin 3) : IntegrableOn
      (fun x => u (x, s) i * mixedSecond (fun y => η y * ψ y) i j x)
      Ω volume :=
    huScalar (contDiff_mixedSecond_smooth hprod i j).continuous
      (decomposition_hasCompactSupport_mixedSecond hprodc i j)
      ((decomposition_ts_support_mixedSecond_subset i j).trans hprodΩ')
  have hCorrInner (j : Fin 3) :=
    (hfinite (fun i => huProd i j)).const_mul (c s j)
  have hdivProd (j : Fin 3) : ∫ x in Ω, ∑ i, u (x, s) i * mixedSecond (fun y => η y * ψ y) i j x =
    0 := by
    simpa only [mixedSecond] using hdiv_s j
  have hCorrZero := @pressure_laplace_cutoff_identity_ae_hCorrZero_9 Ω u η c ψ s hCorrInner hdivProd
  have hBalance := @pressure_laplace_cutoff_identity_ae_hBalance_10 Ω u η c ψ s hUUprodSum
    hUProdSum hCorrZero
  have hUExpand := @pressure_laplace_cutoff_identity_ae_hUExpand_11 Ω u η hη c ψ hψ s hU0Sum
    hU1Sum hU2Sum hU3Sum
  linarith only [hbase_s, hLapExpand, hConvExpand, hForceExpand, hBalance, hUExpand]
end CKN
