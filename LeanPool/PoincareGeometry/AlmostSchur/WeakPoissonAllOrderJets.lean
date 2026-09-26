/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakPoissonDifferentiatedEquation
public import LeanPool.PoincareGeometry.AlmostSchur.MixedWeakDerivative

/-! # The precise remaining estimate for all-order weak Poisson jets

This module is conditional. It does NOT establish all-order elliptic regularity.
The missing estimate must construct suitable whole-space lifts of the top
derivatives and bound their actual difference quotients. Merely retaining
arbitrary lifts is not sufficient: the local identities do not control their
behavior outside the coordinate set. The replacement jet below may therefore
change the lifts, while preserving the represented solution locally.

The actual order-two solution jet supplies the base case. The proved gain
criterion then supplies the induction step once that estimate is discharged.
No classical regularity of the solution is used.
-/
@[expose] public noncomputable section
open Set Bundle MeasureTheory Filter
open scoped Manifold ContDiff Topology
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Explicit induction interface: the required bounded replacement is a
hypothesis, not a consequence of a weak jet or a differentiated equation. -/
theorem exists_all_order_jets_of_bounded_replacements
    {ι : Type*} {b : ι → E} {S : Set E} (u : E → ℝ)
    (J₂ : LocalL2DerivativeJet b S 2)
    (h₂ : (J₂.value [] : E → ℝ) =ᵐ[volume.restrict S] u)
    (hestimate : ∀ n : ℕ, 2 ≤ n → ∀ J : LocalL2DerivativeJet b S n,
      (J.value [] : E → ℝ) =ᵐ[volume.restrict S] u →
      ∃ L : LocalL2DerivativeJet b S n,
        ((L.value [] : E → ℝ) =ᵐ[volume.restrict S] u) ∧
        ∀ w : List ι, w.length = n → ∀ i : ι, ∃ C : ℝ,
          ∀ᶠ h in 𝓝[≠] (0 : ℝ),
            ‖directionalDifferenceQuotient (L.value w) (b i) h‖ ≤ C) :
    ∀ n : ℕ, ∃ J : LocalL2DerivativeJet b S n,
      (J.value [] : E → ℝ) =ᵐ[volume.restrict S] u := by
  have hj : ∀ m : ℕ, ∃ J : LocalL2DerivativeJet b S (m + 2),
      (J.value [] : E → ℝ) =ᵐ[volume.restrict S] u := by
    intro m
    induction m with
    | zero => exact ⟨J₂, h₂⟩
    | succ m ih =>
      obtain ⟨J, hJ⟩ := ih
      obtain ⟨L, hL, hb⟩ := hestimate (m + 2) (by omega) J hJ
      obtain ⟨Q, hQ⟩ := L.gain_of_bounded_differenceQuotients hb
      have hroot : (Q.value [] : E → ℝ) =ᵐ[volume.restrict S] u := by
        rw [hQ [] (by simp)]
        exact hL
      convert (show ∃ Q : LocalL2DerivativeJet b S ((m + 2) + 1),
        (Q.value [] : E → ℝ) =ᵐ[volume.restrict S] u from ⟨Q, hroot⟩) using 1
  intro n
  obtain ⟨J, hJ⟩ := hj n
  exact ⟨⟨J.value, fun w hw i => J.weak w (by omega) i⟩, hJ⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

/-- The actual weak Poisson solution supplies the base of the all-order
induction. The localization/quotient estimate is deliberately explicit. -/
theorem exists_weakPoisson_all_order_jets_of_bounded_replacements
    (b : OrthonormalBasis ι ℝ E) (c : M) {K S : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (hconv : Convex ℝ K)
    (hS : IsCompact S) (hSK : S ⊆ interior K)
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0)
    (hestimate : ∀ n : ℕ, 2 ≤ n → ∀ J : LocalL2DerivativeJet (fun i => b i) S n,
      ((J.value [] : E → ℝ) =ᵐ[volume.restrict S] (fun z =>
        energyCompletionToL2 (weakPoissonSolution f) ((extChartAt I c).symm z))) →
      ∃ L : LocalL2DerivativeJet (fun i => b i) S n,
        ((L.value [] : E → ℝ) =ᵐ[volume.restrict S] (fun z =>
          energyCompletionToL2 (weakPoissonSolution f) ((extChartAt I c).symm z))) ∧
        ∀ w : List ι, w.length = n → ∀ i : ι, ∃ C : ℝ,
          ∀ᶠ h in 𝓝[≠] (0 : ℝ),
            ‖directionalDifferenceQuotient (L.value w) (b i) h‖ ≤ C) :
    ∀ n : ℕ, ∃ J : LocalL2DerivativeJet (fun i => b i) S n,
      (J.value [] : E → ℝ) =ᵐ[volume.restrict S] (fun z =>
        energyCompletionToL2 (weakPoissonSolution f) ((extChartAt I c).symm z)) := by
  obtain ⟨J, C, hC, hroot, hfirst, hsecond, hsymm⟩ :=
    exists_weakPoisson_local_L2_jet_two_symmetric b c hK hKt hconv hS hSK f hf
  exact exists_all_order_jets_of_bounded_replacements _ J hroot hestimate

end AlmostSchur
