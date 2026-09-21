/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Examples.HeatSemigroup
import Mathlib.Probability.HasLaw

/-!
# The process of the heat semigroup is a Brownian motion

The continuous-path process `brownianMotion` of `MarkovProcess.Examples.HeatSemigroup` is
identified as a Brownian motion on the line: recentred at its starting point it has centred
Gaussian marginals of variance the elapsed time, independent increments over the consecutive
intervals of every finite monotone family of times, and continuous trajectories.

The engine is the simple Markov property in joint-law form
(`brownianMotion_map_prodMk_shift`): the law of the pair consisting of the position at a time and
the path shifted by that time is the composition-product of the position law with the process.
Iterating it identifies the law of the vector of increments of a monotone family of times as a
product of centred Gaussians, and independence follows from the product form.

Main results:

* `brownianMotion_map_prodMk_shift`: the simple Markov property in joint-law form.
* `brownianMotion_map_incrementsMap`, `brownianMotion_map_increments`: the joint law of the
  increments is a product of centred Gaussians.
* `HasIndepIncrements`, `hasIndepIncrements_brownianMotion`: independence of the increments.
* `IsBrownianReal`, `isBrownianReal_brownianMotion`: the identification.

`HasIndepIncrements` copies the definition of Mathlib's
`Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.lean`; `IsBrownianReal` is
the form that Mathlib's `Mathlib/Probability/BrownianMotion/Basic.lean` proves equivalent to its
own definition of `IsBrownianReal` (`HasIndepIncrements.isPreBrownianReal_of_hasLaw` and the
converse lemmas `IsPreBrownianReal.hasLaw_eval`, `IsPreBrownianReal.hasIndepIncrements`).
Neither is available at the pinned revision, and `IsBrownianReal` here is stated through Gaussian
marginals and independent increments, not through a projective family.  Only one space dimension
    is treated, and no
Levy characterization, quadratic variation, or stochastic integral is asserted.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

section

section MarkovProperty

/-- A joint law factorizes through a kernel as soon as the law of the second variable, after
restriction to every event determined by the first, is the kernel composed with that restriction.
This is the converse of `restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd`; both directions
are the same computation on rectangles. -/
private theorem map_prodMk_eq_compProd_of_restrict_map
    {Omega beta gamma : Type*} {mOmega : MeasurableSpace Omega}
    {mBeta : MeasurableSpace beta} {mGamma : MeasurableSpace gamma}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → beta) (hX : Measurable X)
    (Y : Omega → gamma) (hY : Measurable Y)
    (kappa : Kernel beta gamma) [IsMarkovKernel kappa]
    (hrestrict : ∀ C : Set beta, MeasurableSet C →
      (mu.restrict (X ⁻¹' C)).map Y = kappa.comap X hX ∘ₘ (mu.restrict (X ⁻¹' C))) :
    mu.map (fun omega ↦ (X omega, Y omega)) = (mu.map X) ⊗ₘ kappa := by
  have : IsProbabilityMeasure (mu.map (fun omega ↦ (X omega, Y omega))) :=
    inferInstance
  have : IsProbabilityMeasure (mu.map X) := inferInstance
  refine MeasureTheory.ext_of_generate_finite _ generateFrom_prod.symm
    isPiSystem_prod ?_ ?_
  · rintro _ ⟨C, hC, B, hB, rfl⟩
    have hleft : mu.map (fun omega ↦ (X omega, Y omega)) (C ×ˢ B)
        = ∫⁻ omega in X ⁻¹' C, kappa (X omega) B ∂mu := by
      rw [Measure.map_apply (hX.prodMk hY) (hC.prod hB), Set.mk_preimage_prod,
        Set.inter_comm, ← Measure.restrict_apply (hY hB), ← Measure.map_apply hY hB,
        hrestrict C hC, Measure.bind_apply hB (Kernel.aemeasurable _)]
      simp_rw [Kernel.comap_apply]
    rw [hleft, Measure.compProd_apply_prod hC hB, setLIntegral_map hC (kappa.measurable_coe hB) hX]
  · rw [measure_univ, measure_univ]

/-- **The simple Markov property of Brownian motion, in joint-law form.** -/
theorem brownianMotion_map_prodMk_shift (x : ℝ) (s : NNReal) :
    (brownianMotion x).map (fun omega ↦ (omega s, ContinuousPath.shift s omega)) =
      (gaussianReal x s) ⊗ₘ brownianMotion := by
  have hX : Measurable (fun omega : ContinuousPath ℝ ↦ omega s) :=
    ContinuousPath.measurable_coordinateProcess s
  have hY : Measurable (ContinuousPath.shift (alpha := ℝ) s) :=
    ContinuousPath.measurable_shift_fixed s
  rw [← brownianMotion_map_eval s x]
  refine map_prodMk_eq_compProd_of_restrict_map (brownianMotion x) _ hX _ hY brownianMotion ?_
  intro C hC
  have hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℝ) s]
      ((fun omega : ContinuousPath ℝ ↦ omega s) ⁻¹' C) :=
    ContinuousPath.measurable_coordinateProcess_canonicalFiltration s hC
  exact SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift
    heatSemigroup isConservative_heatSemigroup isFellerKernelSemigroup_heatSemigroup
    kolmogorovRegular_heatSemigroup x s _ hA

end MarkovProperty

section Increments

/-- The increments of a finite coordinate path, the first one measured from a base point. -/
def incrementsMap : {n : ℕ} → ℝ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, _, _ => fun i ↦ i.elim0
  | _ + 1, x, path => Fin.cons (path 0 - x) (incrementsMap (path 0) (Fin.tail path))

/-- The recursion defining the increments: the first one is measured from the base point, the
remaining ones are the increments of the tail measured from the first coordinate. -/
theorem incrementsMap_succ {n : ℕ} (x : ℝ) (path : Fin (n + 1) → ℝ) :
    incrementsMap x path = Fin.cons (path 0 - x) (incrementsMap (path 0) (Fin.tail path)) :=
  rfl

/-- The first increment is the displacement from the base point. -/
@[simp]
theorem incrementsMap_zero_apply {n : ℕ} (x : ℝ) (path : Fin (n + 1) → ℝ) :
    incrementsMap x path 0 = path 0 - x := rfl

/-- Every increment after the first is the difference of two consecutive coordinates. -/
theorem incrementsMap_succ_apply : ∀ {n : ℕ} (x : ℝ) (path : Fin (n + 1) → ℝ) (i : Fin n),
    incrementsMap x path i.succ = path i.succ - path i.castSucc := by
  intro n
  induction n with
  | zero => exact fun _ _ i ↦ i.elim0
  | succ n ih =>
    intro x path i
    rw [incrementsMap_succ, Fin.cons_succ]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [incrementsMap_zero_apply]
      rfl
    · rw [ih (path 0) (Fin.tail path) j, Fin.tail, Fin.tail, ← Fin.succ_castSucc]

/-- The increments of a finite coordinate path, in closed form. -/
theorem incrementsMap_eq_cons {n : ℕ} (x : ℝ) (path : Fin (n + 1) → ℝ) :
    incrementsMap x path =
      Fin.cons (path 0 - x) (fun i : Fin n ↦ path i.succ - path i.castSucc) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [incrementsMap_zero_apply, Fin.cons_zero]
  · rw [incrementsMap_succ_apply, Fin.cons_succ]

/-- Taking increments is measurable, jointly in the base point and the path. -/
theorem measurable_incrementsMap {n : ℕ} :
    Measurable (fun p : ℝ × (Fin n → ℝ) ↦ incrementsMap p.1 p.2) := by
  cases n with
  | zero => exact Measurable.of_eval fun i ↦ i.elim0
  | succ n =>
    simp_rw [incrementsMap_eq_cons]
    refine measurable_pi_iff.mpr fun i ↦ ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cons_zero]
      fun_prop
    · simp only [Fin.cons_succ]
      fun_prop

/-- The successive time increments of a finite family of times, the first one measured from
time zero. -/
def timeIncrements : {n : ℕ} → (Fin n → NNReal) → (Fin n → NNReal)
  | 0, _ => fun i ↦ i.elim0
  | _ + 1, s => Fin.cons (s 0) (timeIncrements (fun i ↦ s i.succ - s 0))

/-- The recursion defining the time increments. -/
theorem timeIncrements_succ {n : ℕ} (s : Fin (n + 1) → NNReal) :
    timeIncrements s = Fin.cons (s 0) (timeIncrements (fun i ↦ s i.succ - s 0)) := rfl

/-- The first time increment is the first time itself. -/
@[simp]
theorem timeIncrements_zero_apply {n : ℕ} (s : Fin (n + 1) → NNReal) :
    timeIncrements s 0 = s 0 := rfl

/-- For a monotone family of times, every time increment after the first is the length of the
corresponding interval. -/
theorem timeIncrements_succ_apply : ∀ {n : ℕ} {s : Fin (n + 1) → NNReal}, Monotone s →
    ∀ i : Fin n, timeIncrements s i.succ = s i.succ - s i.castSucc := by
  intro n
  induction n with
  | zero => exact fun _ i ↦ i.elim0
  | succ n ih =>
    intro s hs i
    have hs' : Monotone (fun i : Fin (n + 1) ↦ s i.succ - s 0) := fun a b hab ↦
      tsub_le_tsub_right (hs (Fin.succ_le_succ_iff.mpr hab)) _
    rw [timeIncrements_succ, Fin.cons_succ]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [timeIncrements_zero_apply]
      rfl
    · rw [ih hs' j]
      rw [← Fin.succ_castSucc,
        tsub_tsub_tsub_cancel_right (hs (Fin.zero_le _))]

/-- Reading a path at a finite family of times and taking increments is measurable. -/
theorem measurable_incrementsMap_eval {n : ℕ} (s : Fin n → NNReal) (x : ℝ) :
    Measurable (fun omega : ContinuousPath ℝ ↦ incrementsMap x (fun i ↦ omega (s i))) :=
  measurable_incrementsMap.comp (measurable_const.prodMk
    (Measurable.of_eval fun i ↦ ContinuousPath.measurable_coordinateProcess (s i)))

/-- **The joint law of the increments of Brownian motion is a product of centred Gaussians.**
Reading the path of `brownianMotion x` at a monotone family of times and taking the increments,
the first one measured from the starting point `x`, gives independent centred Gaussians of
variances the successive time increments. -/
theorem brownianMotion_map_incrementsMap : ∀ {n : ℕ} {s : Fin n → NNReal}, Monotone s → ∀ x : ℝ,
    (brownianMotion x).map (fun omega ↦ incrementsMap x (fun i ↦ omega (s i))) =
      Measure.pi (fun i ↦ gaussianReal 0 (timeIncrements s i)) := by
  intro n
  induction n with
  | zero =>
    intro s _ x
    have : IsProbabilityMeasure ((brownianMotion x).map
        (fun omega ↦ incrementsMap x (fun i ↦ omega (s i)))) :=
      inferInstance
    exact (Measure.pi_eq fun A _ ↦ by
      have hpi : Set.univ.pi A = Set.univ := by
        ext p
        simp [Set.mem_pi]
      simp [hpi]).symm
  | succ n ih =>
    intro s hs x
    have hs' : Monotone (fun i : Fin n ↦ s i.succ - s 0) := fun a b hab ↦
      tsub_le_tsub_right (hs (Fin.succ_le_succ_iff.mpr hab)) _
    have hPhi : Measurable (fun p : ℝ × ContinuousPath ℝ ↦
        @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
          (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) := by
      refine measurable_finCons.comp ((measurable_fst.sub measurable_const).prodMk ?_)
      exact measurable_incrementsMap.comp (measurable_fst.prodMk
        (Measurable.of_eval fun i ↦
          (ContinuousPath.measurable_coordinateProcess (s i.succ - s 0)).comp measurable_snd))
    have hpair : Measurable (fun omega : ContinuousPath ℝ ↦
        (omega (s 0), ContinuousPath.shift (s 0) omega)) :=
      (ContinuousPath.measurable_coordinateProcess (s 0)).prodMk
        (ContinuousPath.measurable_shift_fixed (s 0))
    have hfactor : (fun omega : ContinuousPath ℝ ↦ incrementsMap x (fun i ↦ omega (s i))) =
        (fun p : ℝ × ContinuousPath ℝ ↦
            @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
              (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ∘
          (fun omega ↦ (omega (s 0), ContinuousPath.shift (s 0) omega)) := by
      funext omega
      have harg : (fun i : Fin n ↦ (ContinuousPath.shift (s 0) omega) (s i.succ - s 0)) =
          Fin.tail (fun i ↦ omega (s i)) := by
        funext i
        change omega (s 0 + (s i.succ - s 0)) = omega (s i.succ)
        rw [add_tsub_cancel_of_le (hs (Fin.zero_le _))]
      change incrementsMap x (fun i ↦ omega (s i)) =
        Fin.cons (omega (s 0) - x)
          (incrementsMap (omega (s 0))
            (fun i : Fin n ↦ (ContinuousPath.shift (s 0) omega) (s i.succ - s 0)))
      rw [incrementsMap_succ, harg]
    rw [hfactor, ← Measure.map_map hPhi hpair, brownianMotion_map_prodMk_shift]
    refine (Measure.pi_eq fun A hA ↦ ?_).symm
    have hpiA : MeasurableSet (Set.univ.pi A) := MeasurableSet.univ_pi hA
    rw [Measure.map_apply hPhi hpiA, Measure.compProd_apply (hPhi hpiA)]
    have hsplit : ∀ y : ℝ, brownianMotion y (Prod.mk y ⁻¹'
          ((fun p : ℝ × ContinuousPath ℝ ↦
            @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
              (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) =
        Set.indicator ((fun u : ℝ ↦ u - x) ⁻¹' (A 0))
          (fun _ ↦ ∏ i : Fin n,
            gaussianReal 0 (timeIncrements (fun i : Fin n ↦ s i.succ - s 0) i) (A i.succ)) y := by
      intro y
      have hmem : ∀ eta : ContinuousPath ℝ,
          (Prod.mk y eta ∈ ((fun p : ℝ × ContinuousPath ℝ ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
                (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) ↔
            (y - x ∈ A 0 ∧
              incrementsMap y (fun i : Fin n ↦ eta (s i.succ - s 0)) ∈
                Set.univ.pi (fun i : Fin n ↦ A i.succ)) := by
        intro eta
        simp only [Set.mem_preimage, Set.mem_univ_pi]
        rw [Fin.forall_fin_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      by_cases hy : y - x ∈ A 0
      · have hy' : y ∈ (fun u : ℝ ↦ u - x) ⁻¹' (A 0) := hy
        rw [Set.indicator_of_mem hy']
        have hset : (Prod.mk y ⁻¹'
            ((fun p : ℝ × ContinuousPath ℝ ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
                (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) =
            (fun eta : ContinuousPath ℝ ↦
              incrementsMap y (fun i : Fin n ↦ eta (s i.succ - s 0))) ⁻¹'
              (Set.univ.pi (fun i : Fin n ↦ A i.succ)) := by
          ext eta
          rw [Set.mem_preimage, hmem eta]
          simp only [Set.mem_preimage, hy, true_and]
        rw [hset, ← Measure.map_apply
          (measurable_incrementsMap_eval (fun i : Fin n ↦ s i.succ - s 0) y)
          (MeasurableSet.univ_pi fun i ↦ hA i.succ), ih hs' y, Measure.pi_pi]
      · have hy' : y ∉ (fun u : ℝ ↦ u - x) ⁻¹' (A 0) := hy
        rw [Set.indicator_of_notMem hy']
        have hset : (Prod.mk y ⁻¹'
            ((fun p : ℝ × ContinuousPath ℝ ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
                (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) =
            (∅ : Set (ContinuousPath ℝ)) := by
          ext eta
          rw [Set.mem_preimage, hmem eta]
          simp only [Set.mem_empty_iff_false, iff_false, not_and, hy, IsEmpty.forall_iff]
        rw [hset, measure_empty]
    have hsub : Measurable (fun u : ℝ ↦ u - x) := by fun_prop
    simp_rw [hsplit]
    rw [lintegral_indicator (hsub (hA 0)), setLIntegral_const,
      ← Measure.map_apply hsub (hA 0),
      gaussianReal_map_sub_const x, sub_self, Fin.prod_univ_succ, timeIncrements_zero_apply]
    exact mul_comm _ _

end Increments

section IndependentIncrements

/-- Dropping the first coordinate of a finite coordinate path is measurable. -/
theorem measurable_finTail {n : ℕ} :
    Measurable (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
  Measurable.of_eval fun i ↦ measurable_pi_apply i.succ

/-- Dropping the first coordinate of a product of probability measures gives the product of the
remaining ones. -/
theorem map_finTail_pi {n : ℕ} (nu : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (nu i)] :
    (Measure.pi nu).map Fin.tail = Measure.pi (fun i : Fin n ↦ nu i.succ) := by
  refine (Measure.pi_eq fun A hA ↦ ?_).symm
  have hpre : (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' (Set.univ.pi A)
      = Set.univ.pi (@Fin.cons n (fun _ ↦ Set ℝ) Set.univ A) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    rw [Fin.forall_fin_succ]
    simp [Fin.tail]
  rw [Measure.map_apply measurable_finTail (MeasurableSet.univ_pi hA), hpre, Measure.pi_pi,
    Fin.prod_univ_succ]
  simp

/-- **The increments of Brownian motion over a monotone family of times are independent
centred Gaussians.** -/
theorem brownianMotion_map_increments {n : ℕ} {t : Fin (n + 1) → NNReal} (ht : Monotone t)
    (x : ℝ) :
    (brownianMotion x).map
        (fun (omega : ContinuousPath ℝ) (i : Fin n) ↦ omega (t i.succ) - omega (t i.castSucc)) =
      Measure.pi (fun i : Fin n ↦ gaussianReal 0 (t i.succ - t i.castSucc)) := by
  have hfac : (fun (omega : ContinuousPath ℝ) (i : Fin n) ↦
      omega (t i.succ) - omega (t i.castSucc)) =
      Fin.tail ∘ (fun omega ↦ incrementsMap x (fun i ↦ omega (t i))) := by
    funext omega i
    exact (incrementsMap_succ_apply x (fun j ↦ omega (t j)) i).symm
  rw [hfac, ← Measure.map_map measurable_finTail (measurable_incrementsMap_eval t x),
    brownianMotion_map_incrementsMap ht x, map_finTail_pi]
  congr 1
  funext i
  rw [timeIncrements_succ_apply ht i]

/-- Every increment of Brownian motion is a centred Gaussian of variance the elapsed time. -/
theorem brownianMotion_map_increment (x : ℝ) (a b : NNReal) (hab : a ≤ b) :
    (brownianMotion x).map (fun omega ↦ omega b - omega a) = gaussianReal 0 (b - a) := by
  have ht : Monotone (![a, b]) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := brownianMotion_map_increments (n := 1) (t := ![a, b]) ht x
  have hmeas : Measurable (fun (omega : ContinuousPath ℝ) (i : Fin 1) ↦
      omega ((![a, b] : Fin 2 → NNReal) i.succ) - omega ((![a, b] : Fin 2 → NNReal) i.castSucc)) :=
    Measurable.of_eval fun i ↦
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
  have hproj := congrArg (fun mu : Measure (Fin 1 → ℝ) ↦ mu.map (Function.eval (0 : Fin 1))) h
  have hpres := measurePreserving_eval (fun i : Fin 1 ↦ gaussianReal 0
    ((![a, b] : Fin 2 → NNReal) i.succ - (![a, b] : Fin 2 → NNReal) i.castSucc)) 0
  rw [Measure.map_map (measurable_pi_apply _) hmeas, hpres.map_eq] at hproj
  exact hproj

/-- A process has independent increments when, for every finite monotone family of times, the
increments over the consecutive intervals of that family are independent. -/
def HasIndepIncrements {T Omega E : Type*} [Preorder T] [MeasurableSpace Omega]
    [MeasurableSpace E] [Sub E] (X : T → Omega → E) (P : Measure Omega) : Prop :=
  ∀ (n : ℕ) (t : Fin (n + 1) → T), Monotone t →
    iIndepFun (fun (i : Fin n) (omega : Omega) ↦ X (t i.succ) omega - X (t i.castSucc) omega) P

/-- **Brownian motion has independent increments.** -/
theorem hasIndepIncrements_brownianMotion (x : ℝ) :
    HasIndepIncrements (fun (t : NNReal) (omega : ContinuousPath ℝ) ↦ omega t - x)
      (brownianMotion x) := by
  intro n t ht
  have hsimp : (fun (i : Fin n) (omega : ContinuousPath ℝ) ↦
      (omega (t i.succ) - x) - (omega (t i.castSucc) - x)) =
      fun (i : Fin n) (omega : ContinuousPath ℝ) ↦ omega (t i.succ) - omega (t i.castSucc) := by
    funext i omega
    ring
  change iIndepFun (fun (i : Fin n) (omega : ContinuousPath ℝ) ↦
    (omega (t i.succ) - x) - (omega (t i.castSucc) - x)) (brownianMotion x)
  rw [hsimp]
  have hmeasi : ∀ i : Fin n, Measurable (fun omega : ContinuousPath ℝ ↦
      omega (t i.succ) - omega (t i.castSucc)) := fun i ↦
    (ContinuousPath.measurable_coordinateProcess _).sub
      (ContinuousPath.measurable_coordinateProcess _)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hmeasi i).aemeasurable),
    brownianMotion_map_increments ht x]
  congr 1
  funext i
  exact (brownianMotion_map_increment x _ _ (ht (Fin.castSucc_lt_succ (i := i)).le)).symm

end IndependentIncrements

section Identification

/-- A real process is a Brownian motion when its one-time marginals are the centred Gaussians of
variance the elapsed time, it has independent increments, and almost every path is continuous.

This is the characterization of a Brownian motion by Gaussian marginals and independent
increments, which Mathlib proves equivalent to its projective-family definition of
`IsBrownianReal` (`HasIndepIncrements.isPreBrownianReal_of_hasLaw` and its converse lemmas);
that definition is not available at the pinned revision. -/
structure IsBrownianReal {Omega : Type*} [MeasurableSpace Omega]
    (X : NNReal → Omega → ℝ) (P : Measure Omega) : Prop where
  /-- At every time the value has the centred Gaussian law of variance that time. -/
  hasLaw_eval : ∀ t : NNReal, HasLaw (X t) (gaussianReal 0 t) P
  /-- The increments over disjoint consecutive intervals are independent. -/
  hasIndepIncrements : HasIndepIncrements X P
  /-- Almost every trajectory is continuous. -/
  cont : ∀ᵐ omega ∂P, Continuous fun t ↦ X t omega

/-- **The canonical process under `brownianMotion x`, recentred at its starting point, is a
Brownian motion.** -/
theorem isBrownianReal_brownianMotion (x : ℝ) :
    IsBrownianReal (fun (t : NNReal) (omega : ContinuousPath ℝ) ↦ omega t - x)
      (brownianMotion x) where
  hasLaw_eval t := by
    refine ⟨((ContinuousPath.measurable_coordinateProcess t).sub measurable_const).aemeasurable, ?_⟩
    have hmeas : Measurable (fun omega : ContinuousPath ℝ ↦ omega t) :=
      ContinuousPath.measurable_coordinateProcess t
    have hsub : Measurable (fun u : ℝ ↦ u - x) := by fun_prop
    rw [show (fun omega : ContinuousPath ℝ ↦ omega t - x)
        = (fun u : ℝ ↦ u - x) ∘ (fun omega : ContinuousPath ℝ ↦ omega t) from rfl,
      ← Measure.map_map hsub hmeas, brownianMotion_map_eval, gaussianReal_map_sub_const x,
      sub_self]
  hasIndepIncrements := hasIndepIncrements_brownianMotion x
  cont := Filter.Eventually.of_forall fun omega ↦ omega.continuous.sub continuous_const

end Identification

end

end MarkovProcess

end PortComputability
