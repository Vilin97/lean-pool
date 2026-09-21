/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakPoissonSecondDerivatives
public import LeanPool.PoincareGeometry.AlmostSchur.PostH2Bootstrap

/-! # An actual order-two local L² derivative jet for weak Poisson

The empty and singleton words use the constructed global graph representatives.
The word `[k,i]` is the extracted weak derivative in direction k of component i.
Identities are retained for C¹ compact tests, stronger than the jet's smooth
test interface. No classical differentiability or smoothness is asserted.
-/

@[expose] public noncomputable section
open Set Bundle MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

/-- Construct a genuine order-two jet, retaining actual level-zero/one
identifications, a uniform second-level norm bound, and all C¹ weak identities. -/
theorem exists_weakPoisson_local_L2_jet_two
    (b : OrthonormalBasis ι ℝ E) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (hconv : Convex ℝ K)
    {S : Set E} (hS : IsCompact S) (hSK : S ⊆ interior K)
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0) :
    ∃ J : LocalL2DerivativeJet (fun i => b i) S 2, ∃ C : ℝ, 0 ≤ C ∧
      (J.value [] =ᵐ[(volume : Measure E).restrict S]
        (fun x => energyCompletionToL2 (weakPoissonSolution f) ((extChartAt I c).symm x))) ∧
      (∀ i, J.value [i] =ᵐ[(volume : Measure E).restrict S]
        (fun x => energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) x)) ∧
      (∀ i k, ‖J.value [k, i]‖ ≤ C) ∧
      ∀ (w : List ι), w.length < 2 → ∀ i (φ : E → ℝ),
        ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ S →
          (∫ x in S, J.value w x * fderiv ℝ φ x (b i)) =
            -(∫ x in S, J.value (i :: w) x * φ x) := by
  obtain ⟨χ, O, ε, hχ, hcχ, hsχ, hrχ, hO, hSO, hOW, hχ1, hε, hmargin⟩ :=
    exists_smooth_compact_plateau hS isOpen_interior hSK
  obtain ⟨P, Q, hgraph, hP, hQ, hquot⟩ := exists_energyCutoffGraph_plateau (I := I)
    (fun i => b i) c hK hKt χ (hχ.of_le (by norm_num)) hcχ
    (hsχ.trans interior_subset) hO hχ1
  let u := weakPoissonSolution f
  have hP0 : P u =ᵐ[(volume : Measure E).restrict S]
      (fun x => energyCompletionToL2 u ((extChartAt I c).symm x)) := by
    filter_upwards [ae_restrict_of_ae (hP u), ae_restrict_mem hS.measurableSet] with x hp hx
    exact hp (hSO hx)
  have hQ1 (i : ι) : Q i u =ᵐ[(volume : Measure E).restrict S]
      (fun x => energyChartDerivative c hK hKt (b i) u x) := by
    filter_upwards [ae_restrict_of_ae (hQ u i), ae_restrict_mem hS.measurableSet] with x hq hx
    exact hq (hSO hx)
  obtain ⟨C, hC, hsecond⟩ := exists_weakPoisson_second_derivatives_on_compact b c hK hKt hconv hS hSK f hf
  choose g hg hgw using hsecond
  have hfirst (i : ι) (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
      (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ S) :
      (∫ x in S, P u x * fderiv ℝ φ x (b i)) = -(∫ x in S, Q i u x * φ x) := by
    have hSK' : S ⊆ K := hSK.trans interior_subset
    have hweak := setIntegral_energyChartDerivative c hK hKt (b i) u φ hφ hcφ (hsφ.trans hSK')
    have hzero (x : E) (hx : x ∉ S) : fderiv ℝ φ x (b i) = 0 := by
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun hh => hx (hsφ hh))]
      rfl
    have hleft : (∫ x in K, energyCompletionToL2 u ((extChartAt I c).symm x) * fderiv ℝ φ x (b i)) =
        ∫ x in S, P u x * fderiv ℝ φ x (b i) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
        (fun x hx => by rw [hzero x (fun hh => hx (hSK' hh)), mul_zero])]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
        (fun x hx => by rw [hzero x hx, mul_zero])]
      apply integral_congr_ae
      filter_upwards [hP0] with x hx
      rw [hx]
    have hright : (∫ x in K, energyChartDerivative c hK hKt (b i) u x * φ x) =
        ∫ x in S, Q i u x * φ x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hSK' (hsφ hh))), mul_zero])]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hsφ hh)), mul_zero])]
      apply integral_congr_ae
      filter_upwards [hQ1 i] with x hx
      rw [hx]
    rwa [hleft, hright] at hweak
  have hsecondQ (i k : ι) (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
      (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ S) :
      (∫ x in S, Q i u x * fderiv ℝ φ x (b k)) = -(∫ x in S, g i k x * φ x) := by
    rw [show (∫ x in S, Q i u x * fderiv ℝ φ x (b k)) =
        (∫ x in S, energyChartDerivative c hK hKt (b i) u x * fderiv ℝ φ x (b k)) from by
      apply integral_congr_ae
      filter_upwards [hQ1 i] with x hx
      rw [hx]]
    exact hgw i k φ hφ hcφ hsφ
  let V : List ι → Lp ℝ 2 (volume : Measure E)
    | [] => P u
    | [i] => Q i u
    | [k, i] => g i k
    | _ => 0
  have hV : ∀ (w : List ι), w.length < 2 → ∀ i (φ : E → ℝ),
      ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ S →
        (∫ x in S, V w x * fderiv ℝ φ x (b i)) = -(∫ x in S, V (i :: w) x * φ x) := by
    intro w hw i φ hφ hc hs
    cases w with
    | nil => exact hfirst i φ hφ hc hs
    | cons j t =>
      cases t with
      | nil => exact hsecondQ j i φ hφ hc hs
      | cons k t => simp only [List.length_cons] at hw; omega
  let J : LocalL2DerivativeJet (fun i => b i) S 2 :=
    ⟨V, fun w hw i φ hφ hc hs => hV w hw i φ (hφ.of_le (by decide)) hc hs⟩
  exact ⟨J, C, hC, hP0, hQ1, hg, hV⟩

end AlmostSchur
