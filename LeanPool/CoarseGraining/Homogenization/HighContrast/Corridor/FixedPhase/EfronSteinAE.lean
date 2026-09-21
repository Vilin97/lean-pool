/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.EfronStein.Transfer

/-!
# The a.e.-measurable Efron–Stein transfer wrapper

The landed `efronStein_transfer_restriction` requires a *genuinely measurable* bounded
observable `G`.  The fixed-phase observable of Proposition 4.3, being a coarse
quadratic, is only *a.e.-strongly-measurable* under the resampled product law
`Π := Measure.pi (fun i => P.map (restrictReg (C i) (hC i)))`.  This file relaxes
the measurability hypothesis to `AEStronglyMeasurable G Π`, keeping the identical
Efron–Stein conclusion.

The plumbing:
* clamp a measurable modification `Gt` of `G` (via `hG.mk`) to `[-M, M]`, so it is
  measurable, everywhere bounded by `M`, and `Gt =ᵐ[Π] G`;
* run the landed `efronStein_transfer_restriction` on `Gt`;
* transfer the variance (LHS) and each resampling energy (RHS) back to `G` using
  the pushforward identities `Measure.map R P = Π`,
  `Measure.map (·.1 ↦ R) (P ⊗ P) = Π`, and the update-resample identity
  `map_update_prod_pi`.

The single genuinely new measure-theoretic input is `map_update_prod_pi`: updating
one coordinate of `Measure.pi μ` by an independent `μ i`-draw preserves `Measure.pi μ`.
-/

open Homogenization
open scoped MeasureTheory ProbabilityTheory BigOperators
open MeasureTheory ProbabilityTheory

namespace Homogenization

variable {d : ℕ}

/-! ## The update-resample pushforward -/

/-- Updating coordinate `i` of a product measure `Measure.pi μ` by an independent
`μ i`-distributed draw preserves the product measure. -/
theorem map_update_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    Measure.map (fun p : (∀ j, α j) × α i => Function.update p.1 i p.2)
        ((Measure.pi μ).prod (μ i)) = Measure.pi μ := by
  classical
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply (measurable_update' (a := i)) (MeasurableSet.univ_pi hs)]
  have hpre :
      (fun p : (∀ j, α j) × α i => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s)
        = (Set.univ.pi (Function.update s i Set.univ)) ×ˢ (s i) := by
    ext p
    obtain ⟨x, y⟩ := p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · simp only [Function.update_self]; exact Set.mem_univ _
        · simp only [Function.update_of_ne hj]; have hj2 := h j
          simpa only [Function.update_of_ne hj] using hj2
      · have hi2 := h i; simpa only [Function.update_self] using hi2
    · rintro ⟨hx, hy⟩ j
      rcases eq_or_ne j i with rfl | hj
      · simpa only [Function.update_self] using hy
      · simp only [Function.update_of_ne hj]; have hxj := hx j
        simpa only [Function.update_of_ne hj] using hxj
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have h1 : (fun j => μ j (Function.update s i Set.univ j))
      = Function.update (fun j => μ j (s j)) i 1 := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp [Function.update_self, measure_univ]
    · simp [Function.update_of_ne hj]
  rw [h1, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    Finset.sdiff_singleton_eq_erase, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

/-! ## The a.e.-measurable Efron–Stein transfer -/

/-- **Restriction Efron–Stein transfer (a.e. variant).**  Identical to
`efronStein_transfer_restriction`, but the observable `G` need only be
`AEStronglyMeasurable` under the
resampled product law `Π := Measure.pi (fun i => P.map (restrictReg (C i) (hC i)))`,
not genuinely measurable.  This is the form consumed by the fixed-phase variance
step, whose coarse observable is only a.e.-measurable under a `RestrictionLawCarrier`. -/
theorem efronStein_transfer_ae_restriction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : ι → Set (Vec d)} (hC : ∀ i, MeasurableSet (C i))
    (hsep : Pairwise fun i j => AreUnitSeparated (C i) (C j))
    {P : Measure (RegCoeffField d)} [IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependentR P)
    {G : (ι → RegCoeffField d) → ℝ}
    (hG : AEStronglyMeasurable G (Measure.pi (fun i => P.map (restrictReg (C i) (hC i)))))
    {M : ℝ} (hMG : ∀ x, |G x| ≤ M)
    (R : RegCoeffField d → (ι → RegCoeffField d))
    (hRdef : R = fun a i => restrictReg (C i) (hC i) a) :
    Var[G ∘ R; P]
      ≤ (1 / 2) * ∑ i, ∫ a, ∫ a',
          (G (Function.update (R a) i (restrictReg (C i) (hC i) a')) - G (R a)) ^ 2 ∂P ∂P := by
  classical
  set μ : ι → Measure (RegCoeffField d) := fun i => P.map (restrictReg (C i) (hC i)) with hμ
  have hμprob : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_restrictReg (C i) (hC i)).aemeasurable
  have hRmeas : Measurable R := by
    rw [hRdef]; exact measurable_pi_iff.2 (fun i => measurable_restrictReg (C i) (hC i))
  -- Map identity `Measure.map R P = Measure.pi μ` (re-derived via the carrier bridge).
  have hmap : Measure.map R P = Measure.pi μ := by
    set X : ι → RegCoeffField d → RegCoeffField d :=
      fun i => restrictObservable (C i) (hC i) with hX
    have hf : ∀ i, AEMeasurable (fun a => X i a) P := fun i =>
      (measurable_restrictObservable (C i) (hC i)).aemeasurable
    have hindep : ProbabilityTheory.iIndepFun X P :=
      Book.Ch04.iIndepFun_of_restrictionUnitRangeDependentLaw_of_pairwise_separated
        (P := P) (U := C) (X := X) hC hP
        (fun i => isRestrictionLocalRandomVariable_restrictObservable (C i) (hC i)) hsep
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hf).1 hindep
    rw [hRdef]; exact h
  -- Clamp a measurable modification of `G` to `[-M, M]`.
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hMG (fun _ => (0 : RegCoeffField d)))
  have hG'meas : Measurable (hG.mk G) := hG.stronglyMeasurable_mk.measurable
  have hGG' : G =ᵐ[Measure.pi μ] hG.mk G := hG.ae_eq_mk
  set Gt : (ι → RegCoeffField d) → ℝ := fun x => max (-M) (min M (hG.mk G x)) with hGtdef
  have hGtmeas : Measurable Gt :=
    measurable_const.max (measurable_const.min hG'meas)
  have hGtbound : ∀ x, |Gt x| ≤ M := by
    intro x
    rw [hGtdef]
    refine abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hGtG : Gt =ᵐ[Measure.pi μ] G := by
    filter_upwards [hGG'] with x hx
    rw [hGtdef]
    dsimp only
    rw [← hx, min_eq_right (abs_le.1 (hMG x)).2, max_eq_right (abs_le.1 (hMG x)).1]
  -- Run the landed transfer on the measurable, bounded `Gt`.
  have key := efronStein_transfer_restriction hC hsep hP hGtmeas hGtbound R hRdef
  -- LHS: `Var[G ∘ R] = Var[Gt ∘ R]`.
  have hLHS : Var[G ∘ R; P] = Var[Gt ∘ R; P] := by
    refine variance_congr ?_
    have hae : ∀ᵐ b ∂(Measure.map R P), G b = Gt b := by rw [hmap]; exact hGtG.symm
    exact ae_of_ae_map hRmeas.aemeasurable hae
  -- RHS: each resampling energy transfers back to `G`.
  have hRHS : ∀ i,
      (∫ a, ∫ a',
        (Gt (Function.update (R a) i (restrictReg (C i) (hC i) a')) - Gt (R a)) ^ 2 ∂P ∂P)
        = ∫ a, ∫ a',
            (G (Function.update (R a) i (restrictReg (C i) (hC i) a')) - G (R a)) ^ 2 ∂P ∂P := by
    intro i
    -- Pushforward of the resampling map `p ↦ update (R p.1) i (restrict p.2)`.
    have hi_meas :
        Measurable (fun p : RegCoeffField d × RegCoeffField d =>
          Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) :=
      (measurable_update' (a := i)).comp
        ((hRmeas.comp measurable_fst).prodMk
          ((measurable_restrictReg (C i) (hC i)).comp measurable_snd))
    have hpairmeas : Measurable (Prod.map R (restrictReg (C i) (hC i))) :=
      hRmeas.prodMap (measurable_restrictReg (C i) (hC i))
    have hmap_hi :
        Measure.map (fun p : RegCoeffField d × RegCoeffField d =>
          Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) (P.prod P)
          = Measure.pi μ := by
      have hpair :
          Measure.map (Prod.map R (restrictReg (C i) (hC i))) (P.prod P)
            = (Measure.pi μ).prod (μ i) := by
        rw [← Measure.map_prod_map P P hRmeas (measurable_restrictReg (C i) (hC i)), hmap]
      have hcomp :
          (fun p : RegCoeffField d × RegCoeffField d =>
            Function.update (R p.1) i (restrictReg (C i) (hC i) p.2))
            = (fun q : (ι → RegCoeffField d) × RegCoeffField d => Function.update q.1 i q.2)
                ∘ (Prod.map R (restrictReg (C i) (hC i))) := rfl
      rw [hcomp, ← Measure.map_map (measurable_update' (a := i)) hpairmeas,
        hpair, map_update_prod_pi μ i]
    -- Pushforward of the outer map `p ↦ R p.1`.
    have hfst : Measure.map (R ∘ Prod.fst) (P.prod P) = Measure.pi μ := by
      rw [← Measure.map_map hRmeas measurable_fst, Measure.map_fst_prod, measure_univ,
        one_smul, hmap]
    -- a.e. equalities of the two evaluation points
    have hAe_hi : ∀ᵐ p ∂(P.prod P),
        Gt (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2))
          = G (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) :=
      ae_of_ae_map hi_meas.aemeasurable (by rw [hmap_hi]; exact hGtG)
    have hAe_R : ∀ᵐ p ∂(P.prod P), Gt (R p.1) = G (R p.1) :=
      ae_of_ae_map ((hRmeas.comp measurable_fst).aemeasurable) (by rw [hfst]; exact hGtG)
    -- integrand a.e. equal on the product
    have hInteg :
        (fun p : RegCoeffField d × RegCoeffField d =>
          (Gt (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) - Gt (R p.1)) ^ 2)
          =ᵐ[P.prod P]
        (fun p : RegCoeffField d × RegCoeffField d =>
          (G (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) - G (R p.1)) ^ 2) := by
      filter_upwards [hAe_hi, hAe_R] with p h1 h2
      rw [h1, h2]
    -- integrability of the (bounded, measurable) truncated integrand
    have hFt_meas :
        Measurable (fun p : RegCoeffField d × RegCoeffField d =>
          (Gt (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) - Gt (R p.1)) ^ 2) :=
      ((hGtmeas.comp hi_meas).sub (hGtmeas.comp (hRmeas.comp measurable_fst))).pow_const 2
    have hFt_int :
        Integrable (fun p : RegCoeffField d × RegCoeffField d =>
          (Gt (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) - Gt (R p.1)) ^ 2)
          (P.prod P) := by
      refine (integrable_const ((2 * M) ^ 2)).mono' hFt_meas.aestronglyMeasurable ?_
      filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb : |Gt (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) - Gt (R p.1)|
          ≤ 2 * M := by
        have h := abs_add_le (Gt (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)))
          (-(Gt (R p.1)))
        rw [← sub_eq_add_neg, abs_neg] at h
        have := h.trans (add_le_add (hGtbound _) (hGtbound _)); linarith
      nlinarith [hb, abs_nonneg (Gt (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2))
        - Gt (R p.1)),
        sq_abs (Gt (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) - Gt (R p.1))]
    have hFg_int :
        Integrable (fun p : RegCoeffField d × RegCoeffField d =>
          (G (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2)) - G (R p.1)) ^ 2)
          (P.prod P) := hFt_int.congr hInteg
    calc (∫ a, ∫ a',
            (Gt (Function.update (R a) i (restrictReg (C i) (hC i) a')) - Gt (R a)) ^ 2 ∂P ∂P)
        = ∫ p, (Gt (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2))
            - Gt (R p.1)) ^ 2 ∂(P.prod P) := (integral_prod _ hFt_int).symm
      _ = ∫ p, (G (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2))
            - G (R p.1)) ^ 2 ∂(P.prod P) := integral_congr_ae hInteg
      _ = ∫ a, ∫ a',
            (G (Function.update (R a) i (restrictReg (C i) (hC i) a')) - G (R a)) ^ 2 ∂P ∂P :=
          integral_prod _ hFg_int
  -- Assemble.
  rw [hLHS]
  refine le_trans key (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hRHS i)

end Homogenization
