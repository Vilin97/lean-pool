/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.Variance
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.Recombination
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.AeBridge
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.CarrierObservable

/-!
# The fixed-phase variance (Proposition 4.3), final assembly

This file closes `p.fixed.phase.variance`.  It supplies the two remaining
statement-plumbing inputs and chains them with the landed mathematics:

* **Joint measurability** (Obstruction 2).
  `aestronglyMeasurable_phaseObservable_patchCore` shows the two-field resampled
  observable `(a, a') ↦ F_σ(patchCore k a a')` is a.e.-strongly-measurable for the
  product law `L ⊗ L`.  The approach is the one already used in `EfronSteinPhase`:
  `clampedPhaseObservable` is genuinely measurable on the product tuple space,
  the resampling-update map is measurable, and the exact update identity
  `update_restrict_eq_restrict_patchCore` together with the a.s. field congruence
  `clampedPhaseObservable_restrict_eq_of_field` (applied at the patched field,
  which is entrywise-measurable + a.e.-elliptic when both draws are) transfers
  measurability across the a.e. equality.  The diagonal term `a ↦ F_σ(a)` gets the
  same treatment (`aestronglyMeasurable_phaseObservable_of_thetaLaw`).

* **Uniform deterministic bound** (Obstruction 1, consumed).
  `summed_sq_le_of_ellipticFieldOn_uniform` (a single dimensional constant `B`,
  independent of the realization pair and the core family) is applied a.s. after a
  C2-bridge of each realization to everywhere-elliptic representatives; the
  fixed-phase observable is unchanged under the bridge
  (`phaseObservable_congr_ae`).

The chain is `efronStein_phaseObservable` → integrable per-core terms (bounded
a.s. by the uniform `B`-term + AESM) → sum/integral exchange (`integral_prod`,
`integral_finset_sum`) → `∫∫ Σ ≤ B`-term.
-/

@[expose] public section

open Homogenization MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Homogenization

variable {d : ℕ}

/-! ## a.e.-congruence of the fixed-phase observable -/

/-- The fixed-phase observable depends on the coefficient field only through a
null-set: if `b =ᵐ b'` on the cube, the observables agree. -/
theorem phaseObservable_congr_ae {ℓ : ℝ} {σ : Vec d} {m : ℤ} {P : BlockVec d}
    {b b' : CoeffField d}
    (hbb' : b =ᵐ[volume.restrict (cubeSet (originCube d m))] b') :
    phaseObservable ℓ σ m P b = phaseObservable ℓ σ m P b' := by
  have hcorr : corridorField ℓ σ b
      =ᵐ[volume.restrict (cubeSet (originCube d m))] corridorField ℓ σ b' := by
    filter_upwards [hbb'] with x hx
    by_cases hxc : x ∈ corridorSet ℓ σ
    · rw [corridorField_apply_of_mem hxc, corridorField_apply_of_mem hxc]
    · rw [corridorField_apply_of_not_mem hxc, corridorField_apply_of_not_mem hxc, hx]
  unfold phaseObservable
  rw [coarseBlockMatrix_congr_of_ae_eq hcorr]

/-! ## Obstruction 2 — joint measurability -/

/-- The single-field fixed-phase observable is a.e.-strongly-measurable under any
`Θ`-elliptic law (via the genuinely measurable clamped observable on the diagonal
restriction tuple). -/
theorem aestronglyMeasurable_phaseObservable_of_thetaLaw [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ) (P : BlockVec d)
    {L : Measure (RegCoeffField d)} (hLaw : ThetaEllipticLaw Θ L) (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K) :
    AEStronglyMeasurable (fun a => phaseObservable ℓ σ m P a.toFun) L := by
  classical
  have hmeas : Measurable (fun a : RegCoeffField d =>
      clampedPhaseObservableR ℓ σ Θ m P K
        (fun k : {k // k ∈ K} =>
          restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) a)) :=
    (measurable_clampedPhaseObservableR hΘ P K).comp
      (measurable_pi_iff.2 (fun k =>
        measurable_restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val)))
  refine hmeas.aestronglyMeasurable.congr ?_
  filter_upwards [hLaw] with a ha
  exact clampedPhaseObservableR_restrict_eq_of_field hℓ hΘ P K hK a ha

/-- **Obstruction 2 — joint measurability for the sum/integral exchange.**  For
each core `k`, the two-field resampled observable
`(a, a') ↦ F_σ(patchCore k a a')` is a.e.-strongly-measurable for the product law
`L ⊗ L`. -/
theorem aestronglyMeasurable_phaseObservable_patchCore [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ) (P : BlockVec d)
    {L : Measure (RegCoeffField d)} [IsProbabilityMeasure L] (hLaw : ThetaEllipticLaw Θ L)
    (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K)
    (k : {k // k ∈ K}) :
    AEStronglyMeasurable
      (fun p : RegCoeffField d × RegCoeffField d =>
        phaseObservable ℓ σ m P (patchCore ℓ σ k.val p.1.toFun p.2.toFun)) (L.prod L) := by
  classical
  have hRmeas : Measurable
      (fun a : RegCoeffField d => fun k' : {k // k ∈ K} =>
        restrictReg (coreBox ℓ σ k'.val) (measurableSet_coreBox ℓ σ k'.val) a) :=
    measurable_pi_iff.2 (fun k' =>
      measurable_restrictReg (coreBox ℓ σ k'.val) (measurableSet_coreBox ℓ σ k'.val))
  have hi_meas : Measurable
      (fun p : RegCoeffField d × RegCoeffField d =>
        Function.update
          (fun k' : {k // k ∈ K} => restrictReg (coreBox ℓ σ k'.val)
            (measurableSet_coreBox ℓ σ k'.val) p.1) k
          (restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) p.2)) :=
    (measurable_update' (a := k)).comp
      ((hRmeas.comp measurable_fst).prodMk
        ((measurable_restrictReg (coreBox ℓ σ k.val)
          (measurableSet_coreBox ℓ σ k.val)).comp measurable_snd))
  have hmeasG : Measurable
      (fun p : RegCoeffField d × RegCoeffField d =>
        clampedPhaseObservableR ℓ σ Θ m P K
          (Function.update
            (fun k' : {k // k ∈ K} => restrictReg (coreBox ℓ σ k'.val)
              (measurableSet_coreBox ℓ σ k'.val) p.1) k
            (restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) p.2))) :=
    (measurable_clampedPhaseObservableR hΘ P K).comp hi_meas
  exact hmeasG.aestronglyMeasurable.congr
    (clampedPhaseObservableR_update_ae hℓ hΘ P hLaw K hK k)

/-! ## The fixed-phase variance (Proposition 4.3) -/

/-- **`p.fixed.phase.variance` (Proposition 4.3).**  Under a
restriction-unit-range-dependent, `Θ`-elliptic probability law, the variance
of the fixed-phase observable obeys the `O((ℓ/3^m)^{d−2})` bound with a single
dimensional constant. -/
theorem fixed_phase_variance [NeZero d] (hd : 3 ≤ d) {m : ℤ} {ℓ Θ : ℝ} {σ : Vec d}
    (hℓ4 : 4 ≤ ℓ) (hℓL : ℓ ≤ (3 : ℝ) ^ m) (hΘ : 1 ≤ Θ) (P : BlockVec d)
    {L : Measure (RegCoeffField d)} [IsProbabilityMeasure L]
    (hURD : IsRestrictionUnitRangeDependentR L) (hLaw : ThetaEllipticLaw Θ L) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      Var[fun a => phaseObservable ℓ σ m P a.toFun; L]
        ≤ Cd * Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2)
            * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2 := by
  classical
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hU : MeasurableSet (cubeSet (originCube d m)) := measurableSet_cubeSet (originCube d m)
  -- the finite core family meeting the cube, and its covering property
  set K : Finset (Fin d → ℤ) :=
    coreMeetsFinset hℓ0 σ (isBounded_cubeSet (originCube d m)) with hKdef
  have hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K := by
    intro k hne
    rw [hKdef, mem_coreMeetsFinset]; exact hne
  -- the uniform deterministic bound
  obtain ⟨B, hB0, hsummedU⟩ := summed_sq_le_of_ellipticFieldOn_uniform (d := d) hd
  set Bterm : ℝ := B * Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2)
      * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2 with hBtermdef
  have hBterm0 : (0 : ℝ) ≤ Bterm := by
    rw [hBtermdef]; positivity
  -- the two-field resampled squared deviation as a product-space function
  set g : {k // k ∈ K} → RegCoeffField d × RegCoeffField d → ℝ :=
    fun k p => (phaseObservable ℓ σ m P (patchCore ℓ σ k.val p.1.toFun p.2.toFun)
      - phaseObservable ℓ σ m P p.1.toFun) ^ 2 with hgdef
  -- a.e. (over L ⊗ L) summed bound, via the C2 bridge to everywhere-elliptic reps
  have haeBound : ∀ᵐ p ∂(L.prod L), ∑ k : {k // k ∈ K}, g k p ≤ Bterm := by
    have hL1 : ∀ᵐ p ∂(L.prod L),
        ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (p.1 x) :=
      (Measure.quasiMeasurePreserving_fst).ae hLaw
    have hL2 : ∀ᵐ p ∂(L.prod L),
        ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (p.2 x) :=
      (Measure.quasiMeasurePreserving_snd).ae hLaw
    filter_upwards [hL1, hL2] with p hp1 hp2
    -- bridge each draw to an everywhere-elliptic representative on the cube
    have hmeasA1 : Measurable (fun x => fun i j => if x ∈ cubeSet (originCube d m)
        then p.1 x i j else 0) := by
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      simpa only [Set.indicator] using! (p.1.entry_measurable i j).indicator hU
    have hmeasA2 : Measurable (fun x => fun i j => if x ∈ cubeSet (originCube d m)
        then p.2 x i j else 0) := by
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      simpa only [Set.indicator] using! (p.2.entry_measurable i j).indicator hU
    obtain ⟨ā1, hEll1, hā1ae, _, _⟩ :=
      exists_ellipticFieldOn_ae_eq hU hΘ hmeasA1 (ae_restrict_of_ae hp1)
    obtain ⟨ā2, hEll2, hā2ae, _, _⟩ :=
      exists_ellipticFieldOn_ae_eq hU hΘ hmeasA2 (ae_restrict_of_ae hp2)
    -- the fixed-phase observable is unchanged under the bridge
    have hphase_a : phaseObservable ℓ σ m P p.1.toFun = phaseObservable ℓ σ m P ā1 :=
      (phaseObservable_congr_ae hā1ae.symm)
    have hpatch_ae : ∀ k : Fin d → ℤ, (patchCore ℓ σ k p.1.toFun p.2.toFun)
        =ᵐ[volume.restrict (cubeSet (originCube d m))] (patchCore ℓ σ k ā1 ā2) := by
      intro k
      filter_upwards [hā1ae, hā2ae] with x hx1 hx2
      by_cases hc : x ∈ coreBox ℓ σ k
      · rw [patchCore_apply_of_mem hc, patchCore_apply_of_mem hc, hx2]
      · rw [patchCore_apply_of_not_mem hc, patchCore_apply_of_not_mem hc, hx1]
    have hphase_patch : ∀ k : {k // k ∈ K},
        phaseObservable ℓ σ m P (patchCore ℓ σ k.val p.1.toFun p.2.toFun)
          = phaseObservable ℓ σ m P (patchCore ℓ σ k.val ā1 ā2) :=
      fun k => phaseObservable_congr_ae (hpatch_ae k.val)
    have hsum_eq : (∑ k : {k // k ∈ K}, g k p)
        = ∑ k : {k // k ∈ K}, (phaseObservable ℓ σ m P (patchCore ℓ σ k.val ā1 ā2)
            - phaseObservable ℓ σ m P ā1) ^ 2 := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hgdef]; simp only [hphase_patch k, hphase_a]
    rw [hsum_eq, hBtermdef]
    exact hsummedU hΘ hℓ4 hℓL σ P hEll1 hEll2 K
  -- AESM of each product-space term
  have hAESM_diag : AEStronglyMeasurable
      (fun p : RegCoeffField d × RegCoeffField d =>
        phaseObservable ℓ σ m P p.1.toFun) (L.prod L) :=
    (aestronglyMeasurable_phaseObservable_of_thetaLaw hℓ0 hΘ P hLaw K hK).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst)
  have hAESM_g : ∀ k : {k // k ∈ K}, AEStronglyMeasurable (g k) (L.prod L) := by
    intro k
    have hpatch := aestronglyMeasurable_phaseObservable_patchCore hℓ0 hΘ P hLaw K hK k
    have hsub := hpatch.sub hAESM_diag
    rw [hgdef]
    simpa only [pow_two] using! hsub.mul hsub
  -- integrability of each product-space term
  have hg_int : ∀ k : {k // k ∈ K}, Integrable (g k) (L.prod L) := by
    intro k
    refine (integrable_const Bterm).mono' (hAESM_g k) ?_
    filter_upwards [haeBound] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hgdef]; exact sq_nonneg _)]
    have hle : g k p ≤ ∑ k' : {k // k ∈ K}, g k' p :=
      Finset.single_le_sum (f := fun k' => g k' p)
        (fun k' _ => by rw [hgdef]; exact sq_nonneg _) (Finset.mem_univ k)
    linarith [hle, hp]
  -- the sum/integral exchange and bound
  have hexchange : (∑ k : {k // k ∈ K}, ∫ p, g k p ∂(L.prod L))
      = ∫ p, ∑ k : {k // k ∈ K}, g k p ∂(L.prod L) :=
    (integral_finsetSum Finset.univ (fun k _ => hg_int k)).symm
  have hint_le : (∫ p, ∑ k : {k // k ∈ K}, g k p ∂(L.prod L)) ≤ Bterm := by
    calc (∫ p, ∑ k : {k // k ∈ K}, g k p ∂(L.prod L))
        ≤ ∫ _p, Bterm ∂(L.prod L) :=
          integral_mono_ae (integrable_finsetSum _ (fun k _ => hg_int k))
            (integrable_const _) haeBound
      _ = Bterm := by rw [integral_const]; simp
  -- relate the Efron–Stein iterated integrals to the product integrals
  have hRHS_eq : (∑ k : {k // k ∈ K},
        ∫ a, ∫ a', (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a.toFun a'.toFun)
          - phaseObservable ℓ σ m P a.toFun) ^ 2 ∂L ∂L)
      = ∑ k : {k // k ∈ K}, ∫ p, g k p ∂(L.prod L) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgdef]
    exact (integral_prod _ (hg_int k)).symm
  -- assemble
  refine ⟨B / 2, by linarith [hB0], ?_⟩
  calc Var[fun a => phaseObservable ℓ σ m P a.toFun; L]
      ≤ (1 / 2) * ∑ k : {k // k ∈ K},
          ∫ a, ∫ a', (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a.toFun a'.toFun)
            - phaseObservable ℓ σ m P a.toFun) ^ 2 ∂L ∂L :=
        efronStein_phaseObservable hℓ0 hΘ P hURD hLaw K hK
    _ = (1 / 2) * ∑ k : {k // k ∈ K}, ∫ p, g k p ∂(L.prod L) := by rw [hRHS_eq]
    _ = (1 / 2) * ∫ p, ∑ k : {k // k ∈ K}, g k p ∂(L.prod L) := by rw [hexchange]
    _ ≤ (1 / 2) * Bterm :=
        mul_le_mul_of_nonneg_left hint_le (by norm_num)
    _ = B / 2 * Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2)
          * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2 := by rw [hBtermdef]; ring

end Homogenization
