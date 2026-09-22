/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.EfronStein.Fin
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.RestrictionIndependence
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Efron–Stein transfer to coefficient-field laws

This file transfers the abstract product-space Efron–Stein inequality
(`Homogenization.efronStein_pi`) to a *single* restriction-unit-range-dependent
probability measure `P` on the honest-fields carrier `RegCoeffField d`,
resampled through a family of restriction endomorphisms.

Fix a `Fintype ι` and a family of pairwise `AreUnitSeparated` measurable regions
`C : ι → Set (Vec d)` (the `MeasurableSet` side-conditions are the D7-approved
refinement making the carrier restriction σ-algebra `RestrictionSigmaR` well
defined).  Writing `R a i := restrictReg (C i) (hC i) a` for the joint
restriction map, each coordinate is a restriction-local random variable for
`RestrictionSigmaR (C i) (hC i)`, so the family is independent under a
restriction-unit-range-dependent `P` and the pushforward `P.map R` factors as the product
measure `Measure.pi (fun i => P.map (restrictReg (C i) (hC i)))`.  Efron–Stein
on that product, transported back through the map identity, yields the variance
bound for a bounded measurable observable `G` of the restricted fields.

The single resampling coordinate is `restrictReg (C i) (hC i) a'`: an
independent copy of `P` re-drawn only on `C i`.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Homogenization

variable {d : ℕ}

/-- The restriction endomorphism `restrictReg U hU`, bundled as the identity
observable on the `U`-restricted field.  This is the family fed to the carrier
independence bridge in the Efron–Stein transfer. -/
noncomputable def restrictObservable (U : Set (Vec d)) (hU : MeasurableSet U) :
    RegCoeffField d → RegCoeffField d :=
  restrictReg U hU

@[simp] theorem restrictObservable_apply (U : Set (Vec d)) (hU : MeasurableSet U)
    (a : RegCoeffField d) :
    restrictObservable U hU a = restrictReg U hU a := rfl

/-- The restriction observable is (globally) measurable on the carrier. -/
theorem measurable_restrictObservable (U : Set (Vec d)) (hU : MeasurableSet U) :
    Measurable (restrictObservable U hU) :=
  measurable_restrictReg U hU

/-- The restriction observable is a restriction-local random variable on its
observation set: it is measurable for the carrier restriction σ-algebra
`RestrictionSigmaR U hU`. -/
theorem isRestrictionLocalRandomVariable_restrictObservable (U : Set (Vec d))
    (hU : MeasurableSet U) :
    Book.Ch04.IsRestrictionLocalRandomVariable U hU (restrictObservable U hU) :=
  measurable_restrictReg_restrictionSigmaR U hU

/-- **Restriction Efron–Stein transfer.**  For a finite family of pairwise
`AreUnitSeparated` measurable regions `C i`, a restriction-unit-range-dependent
probability measure `P` on the carrier `RegCoeffField d`, and a bounded
measurable observable `G` of the jointly restricted fields
`R a = fun i => restrictReg (C i) (hC i) a`, the variance of `G ∘ R` is
controlled by the sum of single-region resampling energies, each an independent
copy of `P` re-drawn only on `C i`. -/
theorem efronStein_transfer_restriction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : ι → Set (Vec d)} (hC : ∀ i, MeasurableSet (C i))
    (hsep : Pairwise fun i j => AreUnitSeparated (C i) (C j))
    {P : MeasureTheory.Measure (RegCoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependentR P)
    {G : (ι → RegCoeffField d) → ℝ} (hG : Measurable G) {M : ℝ} (hMG : ∀ x, |G x| ≤ M)
    (R : RegCoeffField d → (ι → RegCoeffField d))
    (hRdef : R = fun a i => restrictReg (C i) (hC i) a) :
    Var[G ∘ R; P]
      ≤ (1 / 2) * ∑ i, ∫ a, ∫ a',
          (G (Function.update (R a) i (restrictReg (C i) (hC i) a')) - G (R a)) ^ 2 ∂P ∂P := by
  classical
  -- Restriction observables and the resampled per-region laws.
  set X : ι → RegCoeffField d → RegCoeffField d :=
    fun i => restrictObservable (C i) (hC i) with hX
  set μ : ι → MeasureTheory.Measure (RegCoeffField d) :=
    fun i => MeasureTheory.Measure.map (restrictReg (C i) (hC i)) P with hμ
  have hμprob : ∀ i, MeasureTheory.IsProbabilityMeasure (μ i) := fun i =>
    (MeasureTheory.Measure.isProbabilityMeasure_map_iff
      (measurable_restrictReg (C i) (hC i)).aemeasurable).mpr inferInstance
  -- Measurability of the joint restriction map.
  have hRmeas : Measurable R := by
    rw [hRdef]; exact measurable_pi_iff.2 (fun i => measurable_restrictReg (C i) (hC i))
  -- Independence (carrier independence bridge) and the product-measure
  -- factorisation `P.map R = pi μ`.
  have hf : ∀ i, AEMeasurable (fun a => X i a) P :=
    fun i => (measurable_restrictObservable (C i) (hC i)).aemeasurable
  have hindep : ProbabilityTheory.iIndepFun X P :=
    Book.Ch04.iIndepFun_of_restrictionUnitRangeDependentLaw_of_pairwise_separated
      (P := P) (U := C) (X := X) hC hP
      (fun i => isRestrictionLocalRandomVariable_restrictObservable (C i) (hC i)) hsep
  have hmap : MeasureTheory.Measure.map R P = MeasureTheory.Measure.pi μ := by
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hf).1 hindep
    rw [hRdef]; exact h
  -- Left-hand side: `Var[G ∘ R; P] = Var[G; pi μ]`.
  have hLHS : Var[G ∘ R; P] = Var[G; MeasureTheory.Measure.pi μ] := by
    rw [← ProbabilityTheory.variance_map (X := G) hG.aemeasurable hRmeas.aemeasurable, hmap]
  -- Right-hand side: each resampling term pulled back to a double `P`-integral.
  have hRHS : ∀ i,
      (∫ x, ∫ y, (G (Function.update x i y) - G x) ^ 2 ∂(μ i) ∂(MeasureTheory.Measure.pi μ))
        = ∫ a, ∫ a',
            (G (Function.update (R a) i (restrictReg (C i) (hC i) a')) - G (R a)) ^ 2 ∂P ∂P := by
    intro i
    -- Inner integral: resample the `i`-th coordinate from `P` through `restrictReg (C i)`.
    have hinner : ∀ x : ι → RegCoeffField d,
        (∫ y, (G (Function.update x i y) - G x) ^ 2 ∂(μ i))
          = ∫ a', (G (Function.update x i (restrictReg (C i) (hC i) a')) - G x) ^ 2 ∂P := by
      intro x
      have hg : Measurable
          (fun y : RegCoeffField d => (G (Function.update x i y) - G x) ^ 2) :=
        ((hG.comp (measurable_update x)).sub measurable_const).pow measurable_const
      simp only [hμ]
      rw [MeasureTheory.integral_map (measurable_restrictReg (C i) (hC i)).aemeasurable
        hg.aestronglyMeasurable]
    simp_rw [hinner]
    -- Outer integral: pull the free field `x` back to `R a` under `P`.
    have hjoint : Measurable
        (fun p : (ι → RegCoeffField d) × RegCoeffField d =>
          (G (Function.update p.1 i (restrictReg (C i) (hC i) p.2)) - G p.1) ^ 2) := by
      have hupd : Measurable
          (fun p : (ι → RegCoeffField d) × RegCoeffField d =>
            Function.update p.1 i (restrictReg (C i) (hC i) p.2)) :=
        (measurable_update' (a := i)).comp
          (measurable_fst.prodMk
            ((measurable_restrictReg (C i) (hC i)).comp measurable_snd))
      exact ((hG.comp hupd).sub (hG.comp measurable_fst)).pow measurable_const
    have houter : MeasureTheory.StronglyMeasurable
        (fun x : ι → RegCoeffField d =>
          ∫ a', (G (Function.update x i (restrictReg (C i) (hC i) a')) - G x) ^ 2 ∂P) :=
      hjoint.stronglyMeasurable.integral_prod_right'
    rw [← hmap, MeasureTheory.integral_map hRmeas.aemeasurable houter.aestronglyMeasurable]
  -- Assemble.
  rw [hLHS]
  refine le_trans (Homogenization.efronStein_pi μ hG (M := M) hMG) ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact le_of_eq (Finset.sum_congr rfl (fun i _ => hRHS i))

end Homogenization
