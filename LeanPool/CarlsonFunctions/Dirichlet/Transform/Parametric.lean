/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Transform
public import LeanPool.CarlsonFunctions.Dirichlet.Complex.Parametric

/-!
# Dirichlet continuation with holomorphic auxiliary parameters

Complexifying the simplex coordinates makes tangential differentiation compatible with
holomorphic dependence on auxiliary variables. The finite parameter-shift construction
can therefore be used jointly, rather than independently for each auxiliary parameter.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Metric
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

open scoped Classical in
/-- A tangential derivative in the complexified simplex coordinates, leaving the
auxiliary parameter block fixed. -/
def complexSimplexTangentDeriv (j i : ι)
    (H : ((κ → ℂ) × (ι → ℂ)) → ℂ) (p : (κ → ℂ) × (ι → ℂ)) : ℂ :=
  fderiv ℂ H p (0, Pi.single j 1 - Pi.single i 1)

open scoped Classical in
/-- Complex tangential differentiation preserves joint analyticity. -/
theorem analyticOnNhd_complexSimplexTangentDeriv
    {W : Set ((κ → ℂ) × (ι → ℂ))} {H : ((κ → ℂ) × (ι → ℂ)) → ℂ}
    (hH : AnalyticOnNhd ℂ H W) (j i : ι) :
    AnalyticOnNhd ℂ (complexSimplexTangentDeriv j i H) W := by
  unfold complexSimplexTangentDeriv
  exact (ContinuousLinearMap.apply ℂ ℂ
    ((0, Pi.single j 1 - Pi.single i 1) : (κ → ℂ) × (ι → ℂ))).comp_analyticOnNhd hH.fderiv

/-- Restriction of a holomorphic kernel is smooth near the real simplex. -/
theorem contDiffNearStdSimplex_complexKernel
    {W : Set ((κ → ℂ) × (ι → ℂ))} (hWo : IsOpen W)
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (z : κ → ℂ) (hW : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W) (N : ℕ) :
    ContDiffNearStdSimplex N (fun u => H (z, fun i => (u i : ℂ))) := by
  let e := fun u : ι → ℝ => (z, fun i => (u i : ℂ))
  have he : ContDiff ℝ N e := contDiff_const.prodMk (contDiff_pi.mpr fun i =>
    Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff)
  exact ⟨e ⁻¹' W, hWo.preimage he.continuous, hW,
    (hH.contDiffOn_of_completeSpace.restrict_scalars ℝ).comp he.contDiffOn (fun _ h => h)⟩

open scoped Classical in
/-- The complexified tangent derivative agrees with the real tangent derivative used
in the simplex integration-by-parts theorem. -/
theorem complexSimplexTangentDeriv_eq_real
    {W : Set ((κ → ℂ) × (ι → ℂ))} {H : ((κ → ℂ) × (ι → ℂ)) → ℂ}
    (hH : AnalyticOnNhd ℂ H W) (z : κ → ℂ) {u : ι → ℝ}
    (hu : (z, fun i => (u i : ℂ)) ∈ W) (j i : ι) :
    complexSimplexTangentDeriv j i H (z, fun k => (u k : ℂ)) =
      stdSimplexTangentDeriv j i (fun v => H (z, fun k => (v k : ℂ))) u := by
  let e : (ι → ℝ) →L[ℝ] (ι → ℂ) := ContinuousLinearMap.pi
    (fun k => Complex.ofRealCLM.comp (ContinuousLinearMap.proj k))
  have hd := ((hH _ hu).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp u
    ((hasFDerivAt_const z u).prodMk e.hasFDerivAt)
  unfold stdSimplexTangentDeriv
  change _ = (fderiv ℝ (H ∘ fun v => (z, e v)) u) (stdSimplexTangentVector j i)
  rw [hd.fderiv]
  have heV : e (stdSimplexTangentVector j i) = Pi.single j 1 - Pi.single i 1 := by
    ext k
    simp only [e, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, stdSimplexTangentVector,
      Pi.sub_apply, Pi.single_apply]
    split_ifs <;> norm_num
  change (fderiv ℂ H (z, fun k => (u k : ℂ))) (0, Pi.single j 1 - Pi.single i 1) =
    (fderiv ℂ H (z, fun k => (u k : ℂ))) (0, e (stdSimplexTangentVector j i))
  rw [heV]

open scoped Classical in
/-- Tangential parameter shifts, retaining a jointly holomorphic kernel. -/
def shiftedComplexKernelIntegral (i : ι) : List {j : ι // j ≠ i} →
    (((κ → ℂ) × (ι → ℂ)) → ℂ) → ((ι → ℂ) × (κ → ℂ)) → ℂ
  | [], H, p => regDirichletIntegral p.1 (fun u => H (p.2, fun k => (u k : ℂ)))
  | j :: l, H, p =>
      shiftedComplexKernelIntegral i l H (p.1 + Pi.single (j : ι) 1 - Pi.single i 1, p.2) -
        shiftedComplexKernelIntegral i l (complexSimplexTangentDeriv j i H)
          (p.1 + Pi.single (j : ι) 1, p.2)

open scoped Classical in
/-- Every finite shift expression is jointly holomorphic on its convergence region. -/
theorem analyticOnNhd_shiftedComplexKernelIntegral
    {U : Set (κ → ℂ)} (hU : IsOpen U) {W : Set ((κ → ℂ) × (ι → ℂ))}
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W) (i : ι) (l : List {j : ι // j ≠ i}) :
    AnalyticOnNhd ℂ (shiftedComplexKernelIntegral i l H) (shiftRegion i l ×ˢ U) := by
  induction l generalizing H with
  | nil =>
      apply (analyticOnNhd_regDirichletIntegral_kernel_joint hU hH hW).mono
      intro p hp
      refine ⟨?_, hp.2⟩
      intro j
      by_cases hji : j = i
      · subst j; simpa [shiftRegion] using hp.1.1
      · simpa using hp.1.2 ⟨j, hji⟩
  | cons j l ih =>
      intro p hp
      obtain ⟨h0, h1⟩ := shiftRegion_cons i j l hp.1
      exact (((ih hH) (p.1 + Pi.single (j : ι) 1 - Pi.single i 1, p.2) ⟨h0, hp.2⟩).comp_of_eq
        (((analyticAt_fst.add analyticAt_const).sub analyticAt_const).prod analyticAt_snd) rfl).sub
        (((ih (analyticOnNhd_complexSimplexTangentDeriv hH j i))
          (p.1 + Pi.single (j : ι) 1, p.2) ⟨h1, hp.2⟩).comp_of_eq
          ((analyticAt_fst.add analyticAt_const).prod analyticAt_snd) rfl)

open scoped Classical in
/-- The finite shift expression agrees with the native integral sufficiently far inside
the convergence region. This is the integration-by-parts identification used for gluing. -/
theorem shiftedComplexKernelIntegral_eq
    {W : Set ((κ → ℂ) × (ι → ℂ))} (hWo : IsOpen W)
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (z : κ → ℂ) (hW : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W) (i : ι) (l : List {j : ι // j ≠ i})
    {b : ι → ℂ} (hb : ∀ k, (l.length : ℝ) + 2 < (b k).re) :
    shiftedComplexKernelIntegral i l H (b, z) =
      regDirichletIntegral b (fun u => H (z, fun k => (u k : ℂ))) := by
  induction l generalizing H b with
  | nil => rfl
  | cons j l ih =>
      have hshift (k : ι) : (l.length : ℝ) + 2 < ((b + Pi.single (j : ι) 1 : ι → ℂ) k).re := by
        have hk := hb k
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
        by_cases hkj : k = j
        · subst k; simp; linarith
        · simpa [Pi.single_eq_of_ne hkj] using (by linarith : (l.length : ℝ) + 2 < (b k).re)
      have hshift' (k : ι) :
          (l.length : ℝ) + 2 < ((b + Pi.single (j : ι) 1 - Pi.single i 1 : ι → ℂ) k).re := by
        by_cases hki : k = i
        · subst k
          have hk := hb i
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
          simp [Pi.single_eq_of_ne j.property.symm]
          linarith
        · simpa [Pi.single_eq_of_ne hki] using hshift k
      rw [shiftedComplexKernelIntegral, ih hH hshift',
        ih (analyticOnNhd_complexSimplexTangentDeriv hH j i) hshift]
      have hf := contDiffNearStdSimplex_complexKernel hWo hH z hW 1
      have hdiff : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
          DifferentiableAt ℝ (fun u => H (z, fun k => (u k : ℂ))) u := by
        obtain ⟨V, hV, hsub, hfV⟩ := hf
        intro u hu
        exact (hfV.contDiffAt (hV.mem_nhds (hsub hu))).differentiableAt (by simp)
      have hcont : ContinuousOn
          (stdSimplexTangentDeriv (j : ι) i (fun u => H (z, fun k => (u k : ℂ))))
          (Convexity.StdSimplex.coordinateSet ℝ ι) :=
        (hf.tangentDeriv j i).continuousOn
      have hIBP := regDirichletIntegral_tangent_ibp i j (b + Pi.single (j : ι) 1)
        (fun k => lt_of_le_of_lt
          (by have := Nat.cast_nonneg (α := ℝ) l.length; linarith : (2 : ℝ) ≤ l.length + 2)
          (hshift k)) hdiff hcont
      rw [add_sub_cancel_right] at hIBP
      have heq := regDirichletIntegral_congr (b + Pi.single (j : ι) 1)
        (fun u hu => complexSimplexTangentDeriv_eq_real hH z (hW u hu) j i)
      rw [heq]
      change _ - regDirichletIntegral (b + Pi.single (j : ι) 1)
        (fun u => fderiv ℝ (fun v => H (z, fun k => (v k : ℂ))) u
          (Pi.single (j : ι) 1 - Pi.single i 1)) = _
      rw [hIBP]
      ring

open scoped Classical in
/-- Finite-order continuation, jointly in Dirichlet and auxiliary parameters. -/
theorem exists_joint_regDirichletContinuation_kernel
    (N : ℕ) {U : Set (κ → ℂ)} (hU : IsOpen U)
    {W : Set ((κ → ℂ) × (ι → ℂ))} (hWo : IsOpen W)
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W) :
    ∃ F : ((ι → ℂ) × (κ → ℂ)) → ℂ,
      AnalyticOnNhd ℂ F (dirichletConvergenceRegion N ×ˢ U) ∧
      ∀ z ∈ U, Set.EqOn (fun b => F (b, z))
        (fun b => regDirichletIntegral b (fun u => H (z, fun i => (u i : ℂ)))) mvBetaConvergent :=
          by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun _ => 0, analyticOnNhd_const, ?_⟩
    intro z hz b hb
    simp [regDirichletIntegral, stdSimplexMeasure_empty]
  let L := (Fintype.card ι - 1) * N
  let M := L + N
  let d := fun p : (κ → ℂ) × (ι → ℂ) => ∑ i, p.2 i ^ M
  have hd : AnalyticOnNhd ℂ d univ := by
    intro p _
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.2).comp_of_eq
      analyticAt_snd rfl).pow M
  let V := W ∩ {p | d p ≠ 0}
  have hV : IsOpen V := hWo.inter
    (isOpen_ne_fun (continuousOn_univ.mp hd.continuousOn) continuous_const)
  let J := fun p => H p / d p
  have hJ : AnalyticOnNhd ℂ J V :=
    (hH.mono inter_subset_left).div (hd.mono (subset_univ _)) (fun _ hp => hp.2)
  have hVK : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ V := by
    intro z hz u hu
    exact ⟨hW z hz u hu, powerPartitionDenom_ne_zero M hu⟩
  let F := fun p : (ι → ℂ) × (κ → ℂ) => ∑ i, (ascPochhammer ℂ M).eval (p.1 i) *
    shiftedComplexKernelIntegral i (shiftList i N) J (p.1 + Pi.single i (M : ℂ), p.2)
  have hF : AnalyticOnNhd ℂ F (dirichletConvergenceRegion N ×ˢ U) := by
    intro p hp
    apply Finset.analyticAt_fun_sum
    intro i _
    have hbi : p.1 + Pi.single i (M : ℂ) ∈ shiftRegion i (shiftList i N) := by
      constructor
      · simp only [shiftList_length, Pi.add_apply, Pi.single_eq_same, add_re, natCast_re]
        have hi := hp.1 i
        dsimp [M, L]
        push_cast
        linarith
      · intro j
        simp only [Pi.add_apply, Pi.single_eq_of_ne j.property, add_zero, shiftList_count]
        have hj := hp.1 j
        linarith
    have hpoly : AnalyticAt ℂ (fun p : (ι → ℂ) × (κ → ℂ) =>
        (ascPochhammer ℂ M).eval (p.1 i)) p :=
      ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (ascPochhammer ℂ M)) _ (mem_univ _)).comp_of_eq
        (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp_of_eq analyticAt_fst
          rfl) rfl
    exact hpoly.mul (((analyticOnNhd_shiftedComplexKernelIntegral hU hJ hVK i (shiftList i N))
      (p.1 + Pi.single i (M : ℂ), p.2) ⟨hbi, hp.2⟩).comp_of_eq
        ((analyticAt_fst.add analyticAt_const).prod analyticAt_snd) rfl)
  refine ⟨F, hF, ?_⟩
  intro z hz
  have hFb : AnalyticOnNhd ℂ (fun b => F (b, z)) mvBetaConvergent := by
    intro b hb
    exact (hF _ ⟨mvBetaConvergent_subset_dirichletConvergenceRegion N hb, hz⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  have hf := contDiffNearStdSimplex_complexKernel hWo hH z (hW z hz) 0
  have hnative := isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
    (regDirichletIntegral_analyticOn hf.continuousOn)
  let b₀ : ι → ℂ := fun _ => (L + 3 : ℕ)
  have hb₀ : b₀ ∈ mvBetaConvergent := by
    intro i
    change 0 < ((L + 3 : ℕ) : ℝ)
    positivity
  apply hFb.eqOn_of_preconnected_of_eventuallyEq hnative
    (by simpa using isPreconnected_dirichletConvergenceRegion (ι := ι) 0) hb₀
  have hev : ∀ᶠ b : ι → ℂ in nhds b₀, ∀ i, (L : ℝ) + 2 < (b i).re := by
    apply Filter.eventually_all.mpr
    intro i
    apply (isOpen_lt (continuous_const : Continuous fun _ : ι → ℂ => (L : ℝ) + 2)
      (Complex.continuous_re.comp (continuous_apply i))).eventually_mem
    dsimp [b₀]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    linarith
  filter_upwards [hev] with b hb
  have hbpos : b ∈ mvBetaConvergent := by
    intro i
    have := hb i
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  change (∑ i, (ascPochhammer ℂ M).eval (b i) *
    shiftedComplexKernelIntegral i (shiftList i N) J (b + Pi.single i (M : ℂ), z)) = _
  rw [regDirichletIntegral_power_partition hbpos hf.continuousOn M]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply shiftedComplexKernelIntegral_eq hV hJ z (hVK z hz) i (shiftList i N)
  intro k
  rw [shiftList_length]
  by_cases hki : k = i
  · subst k
    simp only [Pi.add_apply, Pi.single_eq_same, add_re, natCast_re]
    have := hb i
    have := Nat.cast_nonneg (α := ℝ) M
    change (L : ℝ) + 2 < (b i).re + M
    linarith
  · simpa only [Pi.add_apply, Pi.single_eq_of_ne hki, add_zero] using hb k

open scoped Classical in
/-- The finite shift constructions glue to a continuation entire in the Dirichlet
parameters and jointly holomorphic with the auxiliary parameters. -/
theorem exists_entire_joint_regDirichletContinuation_kernel
    {U : Set (κ → ℂ)} (hU : IsOpen U)
    {W : Set ((κ → ℂ) × (ι → ℂ))} (hWo : IsOpen W)
    {H : ((κ → ℂ) × (ι → ℂ)) → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W) :
    ∃ F : ((ι → ℂ) × (κ → ℂ)) → ℂ,
      AnalyticOnNhd ℂ F (univ ×ˢ U) ∧
      ∀ z ∈ U, Set.EqOn (fun b => F (b, z))
        (fun b => regDirichletIntegral b (fun u => H (z, fun i => (u i : ℂ)))) mvBetaConvergent :=
          by
  choose Φ hΦ using fun N => exists_joint_regDirichletContinuation_kernel N hU hWo hH hW
  have hexists (b : ι → ℂ) : ∃ N, b ∈ dirichletConvergenceRegion N := by
    choose n hn using fun i => exists_nat_gt (-(b i).re)
    refine ⟨∑ i, n i, fun i => ?_⟩
    have hni : (n i : ℝ) ≤ (∑ j, n j : ℕ) := by
      exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    have hlt : -(n i : ℝ) < (b i).re := by linarith [hn i]
    linarith
  let order := fun b : ι → ℂ => Nat.find (hexists b)
  have horder (b : ι → ℂ) : b ∈ dirichletConvergenceRegion (order b) := Nat.find_spec (hexists b)
  have hslice (N : ℕ) {z : κ → ℂ} (hz : z ∈ U) :
      AnalyticOn ℂ (fun b => Φ N (b, z)) (dirichletConvergenceRegion N) := by
    intro b hb
    exact (((hΦ N).1 (b, z) ⟨hb, hz⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl).analyticWithinAt
  let F := fun p : (ι → ℂ) × (κ → ℂ) => Φ (order p.1) p
  refine ⟨F, ?_, fun z hz b hb => (hΦ (order b)).2 z hz hb⟩
  intro p hp
  let N := order p.1
  have hpN : p ∈ dirichletConvergenceRegion N ×ˢ U := ⟨horder p.1, hp.2⟩
  apply ((hΦ N).1 p hpN).congr
  filter_upwards [((isOpen_dirichletConvergenceRegion N).prod hU).eventually_mem hpN] with q hq
  let m := min N (order q.1)
  have hqm : q.1 ∈ dirichletConvergenceRegion m := by
    change q.1 ∈ dirichletConvergenceRegion (min N (order q.1))
    by_cases hle : N ≤ order q.1
    · rw [Nat.min_eq_left hle]; exact hq.1
    · rw [Nat.min_eq_right (Nat.le_of_not_ge hle)]; exact horder q.1
  have heq : Set.EqOn (fun b => Φ N (b, q.2))
      (fun b => Φ (order q.1) (b, q.2)) (dirichletConvergenceRegion m) := by
    apply eqOn_dirichletContinuation
      ((hslice N hq.2).mono (dirichletConvergenceRegion_mono (Nat.min_le_left _ _)))
      ((hslice (order q.1) hq.2).mono (dirichletConvergenceRegion_mono (Nat.min_le_right _ _)))
    intro b hb
    exact ((hΦ N).2 q.2 hq.2 hb).trans ((hΦ (order q.1)).2 q.2 hq.2 hb).symm
  exact heq hqm

end DirichletTransform
end
