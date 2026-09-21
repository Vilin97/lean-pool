/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LocalizedWeakJetFourier
public import LeanPool.PoincareGeometry.AlmostSchur.CoordinateFourierWeight

/-! # Whole-space derivative identities for localized weak jets

The cutoff Leibniz expansion is differentiated using only valid local weak
identities. Mixed derivatives are kept in their original order.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators FourierTransform
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The recursive Leibniz list really is the sum of the two product-rule terms. -/
theorem localizedWeakJet_cons {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (χ : E → ℝ) (i : ι) (w : List ι) (x : E) :
    localizedWeakJet J χ (i :: w) x = ((cutoffJetTerms w).map (fun p =>
      cutoffJetTerm J χ (i :: p.1, p.2) x + cutoffJetTerm J χ (p.1, i :: p.2) x)).sum := by
  simp [localizedWeakJet, cutoffJetTerms, List.map_map, List.sum_map_add, Function.comp_def]

/-- The localized finite jet obeys whole-space weak derivative identities
against every smooth real test, with no support condition on the test. -/
theorem localizedWeakJet_weak_derivative {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) {χ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ K)
    (w : List ι) (hw : w.length < n) (i : ι) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    (∫ x, localizedWeakJet J χ w x * fderiv ℝ φ x (b i)) =
      -(∫ x, localizedWeakJet J χ (i :: w) x * φ x) := by
  let A := fun p : List ι × List ι => cutoffJetTerm J χ p
  let D := fun p : List ι × List ι => fun x =>
    cutoffJetTerm J χ (i :: p.1, p.2) x + cutoffJetTerm J χ (p.1, i :: p.2) x
  have hint (p : List ι × List ι) (ψ : E → ℝ) (hψ : Continuous ψ) :
      Integrable (fun x => A p x * ψ x) volume :=
    integrable_compact_coefficient_mul_test (Lp.memLp (J.value p.2))
      (cutoff_iterate_properties b hχ hcχ p.1).1.continuous
      (cutoff_iterate_properties b hχ hcχ p.1).2.1 hψ
  have hdint (p : List ι × List ι) : Integrable (fun x => D p x * φ x) volume := by
    apply ((hint (i :: p.1, p.2) φ hφ.continuous).add
      (hint (p.1, i :: p.2) φ hφ.continuous)).congr
    filter_upwards [] with x
    change A (i :: p.1, p.2) x * φ x + A (p.1, i :: p.2) x * φ x = D p x * φ x
    dsimp [A, D]
    ring
  have he (p : List ι × List ι) (hp : p ∈ cutoffJetTerms w) :
      (∫ x, A p x * fderiv ℝ φ x (b i)) = -(∫ x, D p x * φ x) := by
    have hplen : p.2.length < n := by have := cutoffJetTerms_length hp; omega
    exact weak_derivative_compact_localization (b i)
      (Lp.memLp (J.value p.2)) (Lp.memLp (J.value (i :: p.2)))
      (J.weak p.2 hplen i) (cutoff_iterate_properties b hχ hcχ p.1).1
      (cutoff_iterate_properties b hχ hcχ p.1).2.1
      ((cutoff_iterate_properties b hχ hcχ p.1).2.2.trans hsχ) φ hφ
  calc
    _ = ((cutoffJetTerms w).map (fun p => ∫ x, A p x * fderiv ℝ φ x (b i))).sum := by
      simp only [localizedWeakJet, ← List.sum_map_mul_right]
      exact integral_list_sum _ _ (fun p _ =>
        hint p _ (contDiff_smooth_test_derivative hφ (b i)).continuous)
    _ = ((cutoffJetTerms w).map (fun p => -(∫ x, D p x * φ x))).sum := by
      congr 1
      exact List.map_congr_left he
    _ = -(∫ x, ((cutoffJetTerms w).map (fun p => D p x)).sum * φ x) := by
      have hn (l : List (List ι × List ι)) (f : (List ι × List ι) → ℝ) :
          (l.map (fun p => -f p)).sum = -(l.map f).sum := by
        induction l with
        | nil => simp
        | cons p l ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          ring
      rw [hn]
      congr 1
      simp only [← List.sum_map_mul_right]
      exact (integral_list_sum _ _ (fun p _ => hdint p)).symm
    _ = _ := by
      simp only [localizedWeakJet_cons, D]

/-- The localized finite jet supplies the actual weighted Fourier L² bound.
All support, L¹/L² and weak multiplier hypotheses are discharged here. -/
theorem localizedWeakJet_weighted_fourier {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) {χ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ K) :
    MemLp (fun ξ => (1 + ‖ξ‖) ^ n *
      ‖𝓕 (fun x => (localizedWeakJet J χ [] x : ℂ)) ξ‖) 2 volume :=
  weak_jet_weighted_fourier b n (localizedWeakJet J χ)
    (fun w _ => (localizedWeakJet_properties J hχ hcχ w).2.1)
    (fun w _ => (localizedWeakJet_properties J hχ hcχ w).1)
    (fun w hw i φ hφ => localizedWeakJet_weak_derivative J hχ hcχ hsχ w hw i φ hφ)

/-- A cutoff equal to one on an inner open set turns a sufficiently high
finite local weak L² jet into an actual C^k representative there. The output
is globally C^k because it represents the localized field; equality with the
original zeroth field is claimed only on the inner set. -/
theorem local_weak_jet_exists_contDiff_representative {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {K O : Set E} {n k : ℕ}
    (J : LocalL2DerivativeJet b K n)
    (hn : (Module.finrank ℝ E : ℝ) < 2 * ((n : ℝ) - k))
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ interior K) (hO : IsOpen O) (hχ1 : ∀ x ∈ O, χ x = 1) :
    ∃ g : E → ℝ, ContDiff ℝ k g ∧ g =ᵐ[volume.restrict O] (J.value [] : E → ℝ) := by
  obtain ⟨g, hg, hge⟩ := weak_jet_exists_contDiff_representative b n k hn
    (localizedWeakJet J χ)
    (fun w _ => (localizedWeakJet_properties J hχ hcχ w).2.1)
    (fun w _ => (localizedWeakJet_properties J hχ hcχ w).1)
    (fun w hw i φ hφ => localizedWeakJet_weak_derivative J hχ hcχ
      (hsχ.trans interior_subset) w hw i φ hφ)
  refine ⟨g, hg, ?_⟩
  filter_upwards [hge.filter_mono ae_restrict_le, ae_restrict_mem hO.measurableSet] with x hx hxO
  simpa [localizedWeakJet, cutoffJetTerms, cutoffJetTerm, localDirectionalIterate, hχ1 x hxO] using hx

/-- All finite local weak jets with the same zeroth L² field give a smooth
representative on the inner set. No compatibility of arbitrary chosen
representatives across orders is assumed: the common zeroth field fixes the
single inverse Fourier integral used by the proof. -/
theorem local_weak_jets_exists_smooth_representative {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {K O : Set E}
    (J : ∀ n : ℕ, LocalL2DerivativeJet b K n) (u : Lp ℝ 2 (volume : Measure E))
    (hroot : ∀ n, (J n).value [] = u)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ interior K) (hO : IsOpen O) (hχ1 : ∀ x ∈ O, χ x = 1) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ g =ᵐ[volume.restrict O] (u : E → ℝ) := by
  have hi : Integrable (fun x => χ x * u x) volume :=
    integrable_compact_coefficient_mul (Lp.memLp u) hχ.continuous hcχ
  have hw : ∀ k : ℕ, ∃ s : ℝ, (Module.finrank ℝ E : ℝ) < 2 * (s - k) ∧
      MemLp (fun ξ => (1 + ‖ξ‖) ^ s * ‖𝓕 (fun x => ((χ x * u x : ℝ) : ℂ)) ξ‖) 2 volume := by
    intro k
    let n := Module.finrank ℝ E + k + 1
    refine ⟨(n : ℝ), ?_, ?_⟩
    · have hd : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
      dsimp [n]
      push_cast
      linarith
    · have hm := localizedWeakJet_weighted_fourier b (J n) hχ hcχ (hsχ.trans interior_subset)
      simpa only [localizedWeakJet, cutoffJetTerms, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, cutoffJetTerm, localDirectionalIterate, hroot,
        Real.rpow_natCast] using hm
  obtain ⟨g, hg, hge⟩ := exists_smooth_representative_of_all_weighted_fourier hi.ofReal hw
  refine ⟨fun x => (g x).re, Complex.reCLM.contDiff.comp hg, ?_⟩
  filter_upwards [hge.filter_mono ae_restrict_le, ae_restrict_mem hO.measurableSet] with x hx hxO
  simpa [hχ1 x hxO] using congrArg Complex.re hx

end AlmostSchur
