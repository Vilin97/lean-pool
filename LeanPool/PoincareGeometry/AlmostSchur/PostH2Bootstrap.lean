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

public import LeanPool.PoincareGeometry.AlmostSchur.WeakDerivativeBootstrap
public import LeanPool.PoincareGeometry.AlmostSchur.OpenDomainIntegration
public import LeanPool.PoincareGeometry.AlmostSchur.DifferenceQuotientWeakDerivative

/-! # Post-H² weak differentiation

Classical local forcing has genuine weak derivatives. The coefficient bridge
consumes actual L² weak second derivatives. The finite-order gain criterion
below requires difference-quotient estimates; it does not assert those estimates
for differentiated elliptic equations, or a smooth representative.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Restricting a whole-space test identity loses no boundary term when the
test's topological support lies in the integration set. -/
theorem hasWeakDirectionalDerivativeOn_of_global_test_identity
    (K : Set E) (v : E) (u du : E → ℝ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∫ z, u z * fderiv ℝ φ z v) = -(∫ z, du z * φ z)) :
    HasWeakDirectionalDerivativeOn K v u du := by
  intro φ hφ hc hs
  have hl : ∀ z ∉ K, u z * fderiv ℝ φ z v = 0 := by
    intro z hz
    simp [fderiv_of_notMem_tsupport ℝ (fun hh => hz (hs hh))]
  have hr : ∀ z ∉ K, du z * φ z = 0 := by
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport (fun hh => hz (hs hh))]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hl,
    setIntegral_eq_integral_of_forall_compl_eq_zero hr]
  exact h φ hφ hc hs

/-- A locally C¹ forcing term has its classical directional derivative as a
genuine weak derivative; no global smooth extension of the forcing is needed. -/
theorem hasWeakDirectionalDerivativeOn_of_contDiffOn
    {K W : Set E} (hW : IsOpen W) (hKW : K ⊆ W)
    {f : E → ℝ} (hf : ContDiffOn ℝ 1 f W) (v : E) :
    HasWeakDirectionalDerivativeOn K v f (fun z => fderiv ℝ f z v) := by
  apply hasWeakDirectionalDerivativeOn_of_global_test_identity
  intro φ hφ hc hs
  exact integral_mul_fderiv_openDomain hW f φ hf (hφ.of_le (by decide)) hc
    (hs.trans hKW) v

/-- Smooth local forcing supplies the weak derivative required by the
coefficient-commutator identity, directly from integration by parts. -/
theorem weak_divergence_coefficient_derivative_smooth_forcing
    {ι : Type*} [Fintype ι] (b : ι → E)
    {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (v : E) (A : E → ι → ι → ℝ) (D dD : ι → E → ℝ) (F : E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hD : ∀ i, MemLp (D i) 2 ((volume : Measure E).restrict K))
    (hdD : ∀ i, MemLp (dD i) 2 ((volume : Measure E).restrict K))
    (hweak : ∀ i, HasWeakDirectionalDerivativeOn K v (D i) (dD i))
    (hF : ContDiffOn ℝ 1 F W)
    (hPDE : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * D i z) * fderiv ℝ φ z (b j)) =
        -(∫ z in K, F z * φ z)) :
    (∀ j, MemLp (fun z => ∑ i,
      (fderiv ℝ (fun y => A y i j) z v * D i z + A z i j * dD i z)) 2
      ((volume : Measure E).restrict K)) ∧
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i,
        (fderiv ℝ (fun y => A y i j) z v * D i z + A z i j * dD i z)) *
          fderiv ℝ φ z (b j)) = -(∫ z in K, fderiv ℝ F z v * φ z) :=
  weak_divergence_coefficient_derivative b hK hW hKW v A D dD F _ hA hD hdD hweak
    (hasWeakDirectionalDerivativeOn_of_contDiffOn hW hKW hF v) hPDE

/-- Actual bounded L² difference quotients provide the local weak identity
consumed by the coefficient bridge, with the extracted norm bound retained. -/
theorem exists_local_weakDerivative_of_bounded_differenceQuotient
    (K : Set E) (u : Lp ℝ 2 (volume : Measure E)) (v : E) (C : ℝ)
    (hb : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖directionalDifferenceQuotient u v h‖ ≤ C) :
    ∃ g : Lp ℝ 2 (volume : Measure E), ‖g‖ ≤ C ∧
      HasWeakDirectionalDerivativeOn K v u g := by
  obtain ⟨g, hg, hw⟩ := exists_weakDerivative_of_bounded_differenceQuotient u v C hb
  refine ⟨g, hg, hasWeakDirectionalDerivativeOn_of_global_test_identity K v u g ?_⟩
  intro φ hφ hc _
  exact hw φ (hφ.of_le (by decide)) hc

/-- Iterated classical directional derivatives, with the outermost derivative
at the head of the word. -/
def localDirectionalIterate {ι : Type*} (b : ι → E) (f : E → ℝ) : List ι → E → ℝ
  | [] => f
  | i :: w => fun z => fderiv ℝ (localDirectionalIterate b f w) z (b i)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every finite directional derivative of smooth local forcing is locally smooth. -/
theorem contDiffOn_localDirectionalIterate {ι : Type*} (b : ι → E)
    {W : Set E} (hW : IsOpen W) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f W)
    (w : List ι) : ContDiffOn ℝ ∞ (localDirectionalIterate b f w) W := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact (ih.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const

/-- All orders of smooth local forcing have genuine weak derivatives. -/
theorem hasWeakDirectionalDerivativeOn_localDirectionalIterate
    {ι : Type*} (b : ι → E) {K W : Set E} (hW : IsOpen W) (hKW : K ⊆ W)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f W) (w : List ι) (i : ι) :
    HasWeakDirectionalDerivativeOn K (b i) (localDirectionalIterate b f w)
      (localDirectionalIterate b f (i :: w)) :=
  hasWeakDirectionalDerivativeOn_of_contDiffOn hW hKW
    ((contDiffOn_localDirectionalIterate b hW hf w).of_le (by decide)) (b i)

/-- All finite forcing derivatives are L² on compact subsets of their smooth
domain, including the derivatives appearing on the differentiated right side. -/
theorem memLp_localDirectionalIterate_on_compact
    {ι : Type*} (b : ι → E) {K W : Set E} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f W)
    (w : List ι) :
    MemLp (localDirectionalIterate b f w) 2 ((volume : Measure E).restrict K) := by
  let : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  simpa using memLp_mul_coefficient_on_compact hK
    ((contDiffOn_localDirectionalIterate b hW hf w).continuousOn.mono hKW)
    (memLp_const (1 : ℝ) : MemLp (fun _ : E => (1 : ℝ)) 2 (volume.restrict K))

/-- A finite-order local L² derivative jet represented by whole-space L² lifts.
Only words of length at most k have meaning; other values are placeholders.
The whole-space lifts allow use of actual translation/difference-quotient
operators. This is not an assertion that extension by zero preserves H^k. -/
structure LocalL2DerivativeJet {ι : Type*} (b : ι → E) (K : Set E) (k : ℕ) where
  value : List ι → Lp ℝ 2 (volume : Measure E)
  weak : ∀ (w : List ι), w.length < k → ∀ i,
    HasWeakDirectionalDerivativeOn K (b i) (value w) (value (i :: w))

/-- An iterable finite-order gain criterion: actual bounded difference
quotients of all order-k lifts produce an order-(k+1) local L² jet, preserving
every lower-order lift. The bounds are hypotheses, not a claimed elliptic
regularity estimate. For a spanning coordinate frame this is the derivative
data underlying the H^k to H^(k+1) step. -/
theorem LocalL2DerivativeJet.gain_of_bounded_differenceQuotients
    {ι : Type*} {b : ι → E} {K : Set E} {k : ℕ}
    (J : LocalL2DerivativeJet b K k)
    (hb : ∀ w : List ι, w.length = k → ∀ i : ι, ∃ C : ℝ,
      ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖directionalDifferenceQuotient (J.value w) (b i) h‖ ≤ C) :
    ∃ J' : LocalL2DerivativeJet b K (k + 1),
      ∀ w : List ι, w.length ≤ k → J'.value w = J.value w := by
  classical
  have hex (w : List ι) (i : ι) : ∃ g : Lp ℝ 2 (volume : Measure E),
      w.length = k → HasWeakDirectionalDerivativeOn K (b i) (J.value w) g := by
    by_cases hw : w.length = k
    · obtain ⟨C, hC⟩ := hb w hw i
      obtain ⟨g, _, hg⟩ := exists_local_weakDerivative_of_bounded_differenceQuotient
        K (J.value w) (b i) C hC
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun hh => (hw hh).elim⟩
  choose g hg using hex
  let V : List ι → Lp ℝ 2 (volume : Measure E) := fun w =>
    match w with
    | [] => J.value []
    | i :: t => if t.length = k then g t i else J.value (i :: t)
  have hV (w : List ι) (hw : w.length ≤ k) : V w = J.value w := by
    cases w with
    | nil => rfl
    | cons i t =>
      have ht : t.length ≠ k := by simp only [List.length_cons] at hw; omega
      simp [V, ht]
  refine ⟨⟨V, ?_⟩, hV⟩
  intro w hw i
  have hwle : w.length ≤ k := by omega
  rw [hV w hwle]
  by_cases he : w.length = k
  · have hv : V (i :: w) = g w i := by simp [V, he]
    rw [hv]
    exact hg w i he
  · have hwl : w.length < k := by omega
    have hv : V (i :: w) = J.value (i :: w) := by simp [V, he]
    rw [hv]
    exact J.weak w hwl i

/-- At every valid jet level, genuine next derivatives enter the coefficient
commutator equation. In particular an order-two jet supplies the weak second
derivatives at w = []; no classical second derivative is assumed. -/
theorem LocalL2DerivativeJet.coefficient_derivative
    {ι : Type*} [Fintype ι] {b : ι → E} {K W : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (w : List ι) (hw : w.length + 1 < n)
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (k : ι) (A : E → ι → ι → ℝ) (F : E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hF : ContDiffOn ℝ 1 F W)
    (hPDE : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i, A z i j * J.value (i :: w) z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K, F z * φ z)) :
    (∀ j, MemLp (fun z => ∑ i,
      (fderiv ℝ (fun y => A y i j) z (b k) * J.value (i :: w) z +
        A z i j * J.value (k :: i :: w) z)) 2 ((volume : Measure E).restrict K)) ∧
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      (∑ j, ∫ z in K, (∑ i,
        (fderiv ℝ (fun y => A y i j) z (b k) * J.value (i :: w) z +
          A z i j * J.value (k :: i :: w) z)) * fderiv ℝ φ z (b j)) =
        -(∫ z in K, fderiv ℝ F z (b k) * φ z) := by
  apply weak_divergence_coefficient_derivative_smooth_forcing b hK hW hKW (b k) A
    (fun i => J.value (i :: w)) (fun i => J.value (k :: i :: w)) F hA
    (fun i => (Lp.memLp (J.value (i :: w))).restrict K)
    (fun i => (Lp.memLp (J.value (k :: i :: w))).restrict K) ?_ hF hPDE
  intro i
  exact J.weak (i :: w) (by simpa using hw) k

end AlmostSchur
