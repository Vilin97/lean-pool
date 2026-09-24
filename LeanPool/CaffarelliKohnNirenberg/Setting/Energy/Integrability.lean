/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball

/-!
# Integrability

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

private lemma ofReal_vec3EuclideanNorm_pow_two_le_energy (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) ≤ 3 * ‖v‖ₑ ^ (2 : ℝ) := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤
      (Real.sqrt 3 * ‖v‖) ^ 2 := by
    rw [show (vec3EuclideanNorm v) ^ 2 = ∑ i, v i ^ 2 by
      rw [vec3EuclideanNorm, Real.sq_sqrt]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg (v i))]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      ∑ i, v i ^ 2 ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2n : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2n]
  have hle : vec3EuclideanNorm v ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
    simpa [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using hsq
  calc
    ENNReal.ofReal (vec3EuclideanNorm v) ^ ((2 : ℕ) : ℝ) =
        ENNReal.ofReal (vec3EuclideanNorm v ^ ((2 : ℕ) : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg v) (by norm_num)
    _ = ENNReal.ofReal (vec3EuclideanNorm v ^ 2) := by
      rw [Real.rpow_natCast]
    _ ≤ ENNReal.ofReal (3 * ‖v‖ ^ 2) := ENNReal.ofReal_le_ofReal hle
    _ = 3 * ‖v‖ₑ ^ ((2 : ℕ) : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        show ENNReal.ofReal (3 : ℝ) = 3 by norm_num,
        show ‖v‖ₑ ^ ((2 : ℕ) : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) from by
          rw [ENNReal.rpow_natCast,
            show ‖v‖ₑ = ENNReal.ofReal ‖v‖ from (ofReal_norm v).symm,
            ← ENNReal.ofReal_pow (norm_nonneg v)]]

private theorem exists_localBox_of_compact_subset
    {Ω : Set Vec3} {I : Set ℝ} {K : Set ParabolicPoint}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hIord : I.OrdConnected)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    ∃ Ω' J, localBox Ω I Ω' J ∧ K ⊆ spaceTimeSet Ω' J := by
  by_cases hKne : K.Nonempty
  · let Kx : Set Vec3 := Prod.fst '' K
    let Kt : Set ℝ := Prod.snd '' K
    have hKx : IsCompact Kx := by
      exact hK.image continuous_fst_parabolicPoint
    have hKt : IsCompact Kt := by
      exact hK.image continuous_snd_parabolicPoint
    have hKxsub : Kx ⊆ Ω := by
      rintro x ⟨z, hz, rfl⟩
      exact (hKsub hz).1
    have hKtsub : Kt ⊆ I := by
      rintro t ⟨z, hz, rfl⟩
      exact (hKsub hz).2
    obtain ⟨δE, hδE, hδEsub⟩ :=
      hKx.exists_cthickening_subset_open hΩ hKxsub
    obtain ⟨a, ha⟩ := hKt.exists_isLeast (hKne.image Prod.snd)
    obtain ⟨b, hb⟩ := hKt.exists_isGreatest (hKne.image Prod.snd)
    obtain ⟨la, ua, hau, hlua⟩ :=
      (mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds (hKtsub ha.1)))
    obtain ⟨lb, ub, hbu, hlub⟩ :=
      (mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds (hKtsub hb.1)))
    let l' : ℝ := (la + a) / 2
    let u' : ℝ := (b + ub) / 2
    have hll' : la < l' := by
      dsimp [l']
      linarith only [hau.1]
    have hla' : l' < a := by
      dsimp [l']
      linarith only [hau.1]
    have hbu' : b < u' := by
      dsimp [u']
      linarith only [hbu.2]
    have huub' : u' < ub := by
      dsimp [u']
      linarith only [hbu.2]
    have hlaI : l' ∈ I := hlua ⟨hll', hla'.trans hau.2⟩
    have hubI : u' ∈ I := hlub ⟨hbu.1.trans hbu', huub'⟩
    let Ω' : Set Vec3 := Metric.thickening (δE / 2) Kx
    let J : Set ℝ := Ioo l' u'
    have hΩ'open : IsOpen Ω' := by
      exact Metric.isOpen_thickening
    have hΩ'compact : IsCompact (closure Ω') := by
      apply (hKx.cthickening).of_isClosed_subset isClosed_closure
      exact Metric.closure_thickening_subset_cthickening _ _
    have hΩ'sub : closure Ω' ⊆ Ω := by
      exact (Metric.closure_thickening_subset_cthickening _ _).trans
        ((Metric.cthickening_mono (by linarith only [hδE]) _).trans hδEsub)
    have hJord : J.OrdConnected := ordConnected_Ioo
    have hJcompact : IsCompact (closure J) := by
      have hab : l' < u' := lt_of_lt_of_le hla' (ha.2 hb.1) |>.trans hbu'
      rw [show closure J = Icc l' u' from closure_Ioo hab.ne]
      exact isCompact_Icc
    have hJsub : closure J ⊆ I := by
      have hab : l' < u' := lt_of_lt_of_le hla' (ha.2 hb.1) |>.trans hbu'
      rw [show closure J = Icc l' u' from closure_Ioo hab.ne]
      exact hIord.out hlaI hubI
    refine ⟨Ω', J, ⟨hΩ'open, hΩ'compact, hΩ'sub, hJord, hJcompact, hJsub⟩, ?_⟩
    rintro ⟨x, s⟩ hz
    refine ⟨?_, ?_⟩
    · exact Metric.self_subset_thickening (half_pos hδE) _ ⟨(x, s), hz, rfl⟩
    · exact ⟨hla'.trans_le (ha.2 ⟨(x, s), hz, rfl⟩),
        (hb.2 ⟨(x, s), hz, rfl⟩).trans_lt hbu'⟩
  · refine ⟨∅, ∅, ?_, ?_⟩
    · exact ⟨isOpen_empty, by simpa only [closure_empty] using isCompact_empty,
        by simpa only [closure_empty] using (empty_subset Ω), ordConnected_empty,
        by simpa only [closure_empty] using isCompact_empty,
        by simpa only [closure_empty] using (empty_subset I)⟩
    · have hKeq : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
      rw [hKeq]
      exact empty_subset _

private lemma u_sq_integrable_on_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J) :
    IntegrableOn (fun z => (vec3EuclideanNorm (u z)) ^ 2)
      (spaceTimeSet Ω' J) volume := by
  obtain ⟨hmeasU, -, -, -, -, henergy, -, -, -⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  have hu_ae : AEStronglyMeasurable u μ := hmeasU
  have hvec_cont : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hvec_ae : AEMeasurable (fun z => vec3EuclideanNorm (u z)) μ :=
    hvec_cont.measurable.comp_aemeasurable hu_ae.aemeasurable
  have hsq_ae : AEStronglyMeasurable
      (fun z => (vec3EuclideanNorm (u z)) ^ (2 : ℕ)) μ := by
    exact hvec_ae.aestronglyMeasurable.pow 2
  have hsq_pointwise (v : Vec3) :
      (vec3EuclideanNorm v) ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
    rw [show (vec3EuclideanNorm v) ^ 2 = ∑ i, v i ^ 2 by
      rw [vec3EuclideanNorm, Real.sq_sqrt]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg (v i))]
    calc
      ∑ i, v i ^ 2 ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hbound : ∫⁻ z in spaceTimeSet Ω' J,
      ENNReal.ofReal ((vec3EuclideanNorm (u z)) ^ 2) ≤
        3 * ∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ) := by
    calc
      ∫⁻ z in spaceTimeSet Ω' J,
          ENNReal.ofReal ((vec3EuclideanNorm (u z)) ^ 2) ≤
          ∫⁻ z in spaceTimeSet Ω' J, 3 * ‖u z‖ₑ ^ (2 : ℝ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [] with z
        calc
          ENNReal.ofReal ((vec3EuclideanNorm (u z)) ^ 2) ≤
              ENNReal.ofReal (3 * ‖u z‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal (hsq_pointwise (u z))
          _ = 3 * ‖u z‖ₑ ^ (2 : ℝ) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
              show ENNReal.ofReal (3 : ℝ) = 3 by norm_num]
            congr 1
            calc
              ENNReal.ofReal (‖u z‖ ^ (2 : ℕ)) =
                  ENNReal.ofReal (‖u z‖ ^ (2 : ℝ)) := by
                    norm_num [Real.rpow_natCast]
              _ = ENNReal.ofReal ‖u z‖ ^ (2 : ℝ) :=
                (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (u z)) (by norm_num)).symm
              _ = ‖u z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
      _ = 3 * ∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_const_mul' 3 _ (by norm_num)]
  have hfinite : ∫⁻ z, ENNReal.ofReal ((vec3EuclideanNorm (u z)) ^ 2) ∂μ ≠ ⊤ := by
    change ∫⁻ z in spaceTimeSet Ω' J,
      ENNReal.ofReal ((vec3EuclideanNorm (u z)) ^ 2) ≠ ⊤
    exact ne_of_lt (lt_of_le_of_lt hbound (by
      apply ENNReal.mul_lt_top
      · norm_num
      · exact lt_of_le_of_lt (lintegral_mono (fun z => le_add_right le_rfl)) henergy))
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hsq_ae
    (Filter.Eventually.of_forall fun z => sq_nonneg _)).mp hfinite

/-- The squared velocity times a compactly supported test function is integrable. -/
lemma u_sq_mul_test_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Integrable (fun z => (vec3EuclideanNorm (u z)) ^ 2 * ψ z) volume := by
  rcases hψ with ⟨hψ_diff, hψ_compact, hψ_support⟩
  let K : Set ParabolicPoint := (fun q : Vec3 × ℝ => (q.1, q.2)) '' tsupport ψ
  have hKpar : IsCompact K := by
    exact hψ_compact.image continuous_prod_to_parabolicPoint
  have hKsub : K ⊆ spaceTimeSet Ω I := by
    rintro z ⟨q, hq, rfl⟩
    exact hψ_support hq
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    exists_localBox_of_compact_subset hsol.1 hsol.2.1
      (hsol.2.2.1) hKpar hKsub
  have hu : IntegrableOn (fun z => (vec3EuclideanNorm (u z)) ^ 2)
      (spaceTimeSet Ω' J) volume := u_sq_integrable_on_localBox hsol hbox
  obtain ⟨C, hC⟩ := hψ_compact.exists_bound_of_continuous hψ_diff.continuous
  have hmul : IntegrableOn
      (fun z => (vec3EuclideanNorm (u z)) ^ 2 * ψ z)
      (spaceTimeSet Ω' J) volume := by
    change Integrable
      (fun z => (vec3EuclideanNorm (u z)) ^ 2 * ψ z)
      (volume.restrict (spaceTimeSet Ω' J))
    exact hu.mul_bdd hψ_diff.continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hC z)
  apply MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero hmul
  intro z hz
  have hψ_zero : ψ z = 0 := by
    by_contra hne
    apply hz
    apply hKbox
    exact ⟨z, (subset_tsupport (f := ψ)) ((Function.mem_support).2 hne), rfl⟩
  simp [hψ_zero]

/-! ### Compact rectangular time-slice bounds -/

/-- The velocity time-slice energy is essentially bounded on a compact
rectangular portion of the open space-time carrier. -/
theorem sws_timeSliceBallEnergy_essSup_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {R a b : ℝ} (hR : 0 < R) (hab : a < b)
    (hrect : euclideanClosedBall x₀ R ×ˢ Icc a b ⊆ spaceTimeSet Ω I) :
    essSup
        (timeSliceBallEnergy x₀ R ·
          (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc a b)) < ⊤ := by
  let K : Set ParabolicPoint :=
    parabolicHomeomorph ⁻¹' (euclideanClosedBall x₀ R ×ˢ Icc a b)
  have hK : IsCompact K := by
    exact parabolicHomeomorph.isCompact_preimage.2
      ((isCompact_euclideanClosedBall x₀ hR.le).prod isCompact_Icc)
  have hKsub : K ⊆ spaceTimeSet Ω I := by
    intro z hz
    exact hrect hz
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    exists_localBox_of_compact_subset hsol.1 hsol.2.1 hsol.2.2.1 hK hKsub
  obtain ⟨-, -, -, -, hEssSup, -, -, -, -⟩ := hsol.2.2.2.2.2.1 Ω' J hbox
  have hball : vec3Ball x₀ R ⊆ Ω' := by
    intro x hx
    have hxclosed : x ∈ euclideanClosedBall x₀ R := by
      have heq : vecEuclideanNorm (x - x₀) = vec3EuclideanNorm (x - x₀) := by
        simp only [vecEuclideanNorm, vecNormSq, vecDot, Pi.sub_apply, vec3EuclideanNorm]
        apply congrArg Real.sqrt
        apply Finset.sum_congr rfl
        intro i hi
        ring
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).2
        (by rw [heq]; exact (mem_vec3Ball.mp hx).le)
    have hboxmem : ((x, (a : ℝ)) : ParabolicPoint) ∈ K := by
      change x ∈ euclideanClosedBall x₀ R ∧ a ∈ Icc a b
      exact ⟨hxclosed, ⟨le_rfl, hab.le⟩⟩
    exact (hKbox hboxmem).1
  have hIoc : Ioc a b ⊆ J := by
    intro s hs
    have hx : x₀ ∈ euclideanClosedBall x₀ R := by
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).2
        (by simpa [vecEuclideanNorm, vecNormSq, vecDot] using hR.le)
    have hboxmem : ((x₀, s) : ParabolicPoint) ∈ K := by
      change x₀ ∈ euclideanClosedBall x₀ R ∧ s ∈ Icc a b
      exact ⟨hx, ⟨hs.1.le, hs.2⟩⟩
    exact (hKbox hboxmem).2
  have hpoint : ∀ s, timeSliceBallEnergy x₀ R s
        (fun w => vec3EuclideanNorm (u w)) ≤
      3 * ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ) := by
    intro s
    unfold timeSliceBallEnergy
    calc
      ∫⁻ y in vec3Ball x₀ R,
          ‖vec3EuclideanNorm (u (y, s))‖ₑ ^ (2 : ℝ) =
          ∫⁻ y in vec3Ball x₀ R,
            ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) :=
        lintegral_congr (fun y => by
          rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)])
      _ ≤ ∫⁻ y in vec3Ball x₀ R, 3 * ‖u (y, s)‖ₑ ^ (2 : ℝ) :=
        lintegral_mono
          (fun y => ofReal_vec3EuclideanNorm_pow_two_le_energy (u (y, s)))
      _ = 3 * ∫⁻ y in vec3Ball x₀ R, ‖u (y, s)‖ₑ ^ (2 : ℝ) :=
        lintegral_const_mul' 3 _ (by norm_num)
      _ ≤ 3 * ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set hball) (by positivity)
  have hmono := essSup_mono_measure_and_ae
    (μ := volume.restrict (Ioc a b))
    (ν := volume.restrict J)
    (Measure.restrict_mono hIoc le_rfl)
    (Filter.Eventually.of_forall hpoint)
  rw [ENNReal.essSup_const_mul] at hmono
  exact lt_of_le_of_lt hmono (ENNReal.mul_lt_top (by norm_num) hEssSup)

end CKN
