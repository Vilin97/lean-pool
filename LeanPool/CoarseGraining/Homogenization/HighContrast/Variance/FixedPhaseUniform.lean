/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.VarianceFinal

/-!
# Uniform-constant fixed-phase variance

`Corridor/FixedPhase/VarianceFinal.lean` proves `fixed_phase_variance` in the
form `∀ params, ∃ Cd, 0 ≤ Cd ∧ bound`.  The main theorem `t.block.variance`
needs the dimensional constant `Cd` pulled *outside* the field quantifiers, so
that a single constant serves every scale, contrast, law, and block vector.

The witness of `fixed_phase_variance` is already uniform: it is `B/2` where `B`
comes from `summed_sq_le_of_ellipticFieldOn_uniform` (which quantifies over all
of `m, Θ, ℓ, σ, P` under a single `B`).  We therefore reproduce the assembly of
`fixed_phase_variance` with the `obtain B` hoisted above the `∀`, yielding the
`∃ Cd, ∀ params` form directly.
-/

namespace Homogenization

open Homogenization MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- **Uniform-constant fixed-phase variance.**  The constant `Cd = B/2` is
independent of `m, ℓ, Θ, σ, P, L`. -/
theorem fixed_phase_variance_uniform [NeZero d] (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ {m : ℤ} {ℓ Θ : ℝ} {σ : Vec d} (_hℓ4 : 4 ≤ ℓ) (_hℓL : ℓ ≤ (3 : ℝ) ^ m)
        (_hΘ : 1 ≤ Θ) (P : BlockVec d) {L : Measure (RegCoeffField d)}
        [IsProbabilityMeasure L] (_hURD : IsRestrictionUnitRangeDependentR L)
        (_hLaw : ThetaEllipticLaw Θ L),
      Var[fun a => phaseObservable ℓ σ m P a.toFun; L]
        ≤ Cd * Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2)
            * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2 := by
  classical
  obtain ⟨B, hB0, hsummedU⟩ := summed_sq_le_of_ellipticFieldOn_uniform (d := d) hd
  refine ⟨B / 2, by linarith, ?_⟩
  intro m ℓ Θ σ hℓ4 hℓL hΘ P L _ hURD hLaw
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hU : MeasurableSet (cubeSet (originCube d m)) := measurableSet_cubeSet (originCube d m)
  set K : Finset (Fin d → ℤ) :=
    coreMeetsFinset hℓ0 σ (isBounded_cubeSet (originCube d m)) with hKdef
  have hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K := by
    intro k hne
    rw [hKdef, mem_coreMeetsFinset]; exact hne
  set Bterm : ℝ := B * Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2)
      * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2 with hBtermdef
  have hBterm0 : (0 : ℝ) ≤ Bterm := by
    rw [hBtermdef]; positivity
  set g : {k // k ∈ K} → RegCoeffField d × RegCoeffField d → ℝ :=
    fun k p => (phaseObservable ℓ σ m P (patchCore ℓ σ k.val p.1.toFun p.2.toFun)
      - phaseObservable ℓ σ m P p.1.toFun) ^ 2 with hgdef
  have haeBound : ∀ᵐ p ∂(L.prod L), ∑ k : {k // k ∈ K}, g k p ≤ Bterm := by
    have hL1 : ∀ᵐ p ∂(L.prod L),
        ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (p.1 x) :=
      (Measure.quasiMeasurePreserving_fst).ae hLaw
    have hL2 : ∀ᵐ p ∂(L.prod L),
        ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (p.2 x) :=
      (Measure.quasiMeasurePreserving_snd).ae hLaw
    filter_upwards [hL1, hL2] with p hp1 hp2
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
  have hg_int : ∀ k : {k // k ∈ K}, Integrable (g k) (L.prod L) := by
    intro k
    refine (integrable_const Bterm).mono' (hAESM_g k) ?_
    filter_upwards [haeBound] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hgdef]; exact sq_nonneg _)]
    have hle : g k p ≤ ∑ k' : {k // k ∈ K}, g k' p :=
      Finset.single_le_sum (f := fun k' => g k' p)
        (fun k' _ => by rw [hgdef]; exact sq_nonneg _) (Finset.mem_univ k)
    linarith [hle, hp]
  have hexchange : (∑ k : {k // k ∈ K}, ∫ p, g k p ∂(L.prod L))
      = ∫ p, ∑ k : {k // k ∈ K}, g k p ∂(L.prod L) :=
    (integral_finsetSum Finset.univ (fun k _ => hg_int k)).symm
  have hint_le : (∫ p, ∑ k : {k // k ∈ K}, g k p ∂(L.prod L)) ≤ Bterm := by
    calc (∫ p, ∑ k : {k // k ∈ K}, g k p ∂(L.prod L))
        ≤ ∫ _p, Bterm ∂(L.prod L) :=
          integral_mono_ae (integrable_finsetSum _ (fun k _ => hg_int k))
            (integrable_const _) haeBound
      _ = Bterm := by rw [integral_const]; simp
  have hRHS_eq : (∑ k : {k // k ∈ K},
        ∫ a, ∫ a', (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a.toFun a'.toFun)
          - phaseObservable ℓ σ m P a.toFun) ^ 2 ∂L ∂L)
      = ∑ k : {k // k ∈ K}, ∫ p, g k p ∂(L.prod L) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgdef]
    exact (integral_prod _ (hg_int k)).symm
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
