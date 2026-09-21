/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Basic

/-!
# Coordinate derivatives of holomorphic functions

Coordinate differentiation is defined using one-variable slices, and identified with
evaluation of the Fréchet derivative on a coordinate vector. Holomorphy of derivatives
is inherited from Mathlib's general Fréchet derivative theorem.
-/

@[expose] public noncomputable section

open Complex Filter Function Set
open scoped Topology

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

open scoped Classical in
/-- Differentiate in coordinate `i`, holding all other coordinates fixed. -/
def partialDeriv (i : ι) (f : (ι → ℂ) → F) (z : ι → ℂ) : F :=
  deriv (fun w => f (update z i w)) (z i)

open scoped Classical in
/-- The derivative of a coordinate slice is the corresponding Fréchet derivative value. -/
theorem hasDerivAt_update_of_differentiableAt {f : (ι → ℂ) → F} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (i : ι) :
    HasDerivAt (fun w => f (update z i w)) (fderiv ℂ f z (Pi.single i 1)) (z i) := by
  have hf' : HasFDerivAt f (fderiv ℂ f z) (update z i (z i)) := by simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (z i) (hasDerivAt_update z i (z i))

open scoped Classical in
/-- Coordinate derivatives are Fréchet derivatives evaluated on coordinate vectors. -/
theorem partialDeriv_eq_fderiv {f : (ι → ℂ) → F} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (i : ι) :
    partialDeriv i f z = fderiv ℂ f z (Pi.single i 1) :=
  (hasDerivAt_update_of_differentiableAt hf i).deriv

open scoped Classical in
/-- A coordinate derivative only depends on the germ of the function. -/
theorem partialDeriv_congr {f g : (ι → ℂ) → F} {z : ι → ℂ}
    (hfg : f =ᶠ[𝓝 z] g) (i : ι) : partialDeriv i f z = partialDeriv i g z := by
  apply Filter.EventuallyEq.deriv_eq
  have ht : Tendsto (update z i) (𝓝 (z i)) (𝓝 z) := by
    simpa using (hasDerivAt_update z i (z i)).continuousAt.tendsto
  exact hfg.comp_tendsto ht

open scoped Classical in
/-- The Fréchet derivative is recovered from the coordinate derivatives. -/
theorem fderiv_eq_sum_partialDeriv {f : (ι → ℂ) → F} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (v : ι → ℂ) :
    fderiv ℂ f z v = ∑ i, v i • partialDeriv i f z := by
  simp_rw [partialDeriv_eq_fderiv hf, ← map_smul, ← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply]

/-- Coordinate differentiation respects subtraction at differentiability points. -/
theorem partialDeriv_sub {f g : (ι → ℂ) → F} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) (i : ι) :
    partialDeriv i (f - g) z = partialDeriv i f z - partialDeriv i g z := by
  exact deriv_sub (hasDerivAt_update_of_differentiableAt hf i).differentiableAt
    (hasDerivAt_update_of_differentiableAt hg i).differentiableAt

open scoped Classical in
/-- Holomorphy restricts to each coordinate slice. -/
theorem _root_.AnalyticOnNhd.analyticAt_update {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {z : ι → ℂ} (hz : z ∈ U) (i : ι) :
    AnalyticAt ℂ (fun w => f (update z i w)) (z i) := by
  have hu : AnalyticAt ℂ (update z i) (z i) :=
    analyticAt_iff_eventually_differentiableAt.mpr
      (Eventually.of_forall fun w => (hasDerivAt_update z i w).differentiableAt)
  exact (hf z hz).comp_of_eq hu (update_eq_self i z)

/-- Coordinate differentiation commutes with a finite sum of differentiable functions. -/
theorem partialDeriv_finset_sum {α : Type*} {f : α → (ι → ℂ) → F}
    (t : Finset α) {z : ι → ℂ} (hf : ∀ a ∈ t, DifferentiableAt ℂ (f a) z) (i : ι) :
    partialDeriv i (fun w => ∑ a ∈ t, f a w) z = ∑ a ∈ t, partialDeriv i (f a) z := by
  exact deriv_fun_sum fun a ha => (hasDerivAt_update_of_differentiableAt (hf a ha) i).differentiableAt

variable [CompleteSpace F]

open scoped Classical in
/-- Every coordinate derivative of an analytic function is analytic. -/
theorem _root_.AnalyticOnNhd.partialDeriv {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) (i : ι) :
    AnalyticOnNhd ℂ (partialDeriv i f) U := by
  intro z hz
  have ha : AnalyticAt ℂ (fun w => fderiv ℂ f w (Pi.single i 1)) z := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using!
      ((ContinuousLinearMap.apply ℂ F (Pi.single i (1 : ℂ))).analyticAt
        (fderiv ℂ f z)).comp_of_eq (hf z hz).fderiv rfl
  apply ha.congr
  filter_upwards [hU.eventually_mem hz] with w hw
  exact (partialDeriv_eq_fderiv (hf w hw).differentiableAt i).symm

/-- Repeated coordinate differentiation, with the leftmost coordinate acting last. -/
def iteratedPartialDeriv : List ι → ((ι → ℂ) → F) → (ι → ℂ) → F
  | [], f => f
  | i :: is, f => partialDeriv i (iteratedPartialDeriv is f)

open scoped Classical in
/-- Differentiate a coordinate derivative by composing the second Fréchet derivative
with evaluation on its coordinate vector. -/
theorem hasFDerivAt_partialDeriv {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) {z : ι → ℂ} (hz : z ∈ U) (i : ι) :
    HasFDerivAt (partialDeriv i f)
      ((ContinuousLinearMap.apply ℂ F (Pi.single i 1)).comp
        (fderiv ℂ (fderiv ℂ f) z)) z := by
  have H := (ContinuousLinearMap.apply ℂ F (Pi.single i (1 : ℂ))).hasFDerivAt.comp z
    (hf z hz).fderiv.differentiableAt.hasFDerivAt
  apply H.congr_of_eventuallyEq
  filter_upwards [hU.eventually_mem hz] with w hw
  exact partialDeriv_eq_fderiv (hf w hw).differentiableAt i

open scoped Classical in
/-- Mixed coordinate derivatives commute for a holomorphic function. -/
theorem partialDeriv_partialDeriv_comm {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) {z : ι → ℂ} (hz : z ∈ U) (i j : ι) :
    partialDeriv i (partialDeriv j f) z = partialDeriv j (partialDeriv i f) z := by
  rw [partialDeriv_eq_fderiv (hasFDerivAt_partialDeriv hf hU hz j).differentiableAt,
    partialDeriv_eq_fderiv (hasFDerivAt_partialDeriv hf hU hz i).differentiableAt,
    (hasFDerivAt_partialDeriv hf hU hz j).fderiv,
    (hasFDerivAt_partialDeriv hf hU hz i).fderiv]
  exact (hf z hz).contDiffAt.isSymmSndFDerivAt_of_omega (Pi.single i 1) (Pi.single j 1)

/-- All iterated coordinate derivatives are holomorphic on the original open domain. -/
theorem _root_.AnalyticOnNhd.iteratedPartialDeriv {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) (is : List ι) :
    AnalyticOnNhd ℂ (iteratedPartialDeriv is f) U := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact ih.partialDeriv hU i

/-- Iterated coordinate derivatives depend only on the multiplicity of each coordinate,
not on their order in the differentiation list. -/
theorem iteratedPartialDeriv_perm {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) {is js : List ι} (h : is.Perm js) :
    EqOn (iteratedPartialDeriv is f) (iteratedPartialDeriv js f) U := by
  induction h with
  | nil => intro z hz; rfl
  | cons i h ih =>
      intro z hz
      apply partialDeriv_congr
      filter_upwards [hU.eventually_mem hz] with w hw
      exact ih hw
  | swap i j is =>
      intro z hz
      exact partialDeriv_partialDeriv_comm (hf.iteratedPartialDeriv hU is) hU hz j i
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

omit [CompleteSpace F] in
/-- Iterated coordinate derivatives agree on an open set where the original functions agree. -/
theorem iteratedPartialDeriv_congrOn {U : Set (ι → ℂ)} {f g : (ι → ℂ) → F}
    (hU : IsOpen U) (hfg : EqOn f g U) (is : List ι) :
    EqOn (iteratedPartialDeriv is f) (iteratedPartialDeriv is g) U := by
  induction is with
  | nil => exact hfg
  | cons i is ih =>
    intro z hz
    apply partialDeriv_congr
    filter_upwards [hU.eventually_mem hz] with w hw
    exact ih hw

/-- Mixed coordinate differentiation commutes with finite sums of holomorphic functions. -/
theorem iteratedPartialDeriv_finset_sum {α : Type*} {U : Set (ι → ℂ)}
    {f : α → (ι → ℂ) → F} (t : Finset α) (hf : ∀ a ∈ t, AnalyticOnNhd ℂ (f a) U)
    (hU : IsOpen U) (is : List ι) :
    EqOn (iteratedPartialDeriv is (fun z => ∑ a ∈ t, f a z))
      (fun z => ∑ a ∈ t, iteratedPartialDeriv is (f a) z) U := by
  induction is with
  | nil => intro z hz; rfl
  | cons i is ih =>
    intro z hz
    change partialDeriv i (iteratedPartialDeriv is (fun w => ∑ a ∈ t, f a w)) z = _
    have heq : iteratedPartialDeriv is (fun w => ∑ a ∈ t, f a w) =ᶠ[𝓝 z]
        (fun w => ∑ a ∈ t, iteratedPartialDeriv is (f a) w) :=
      (hU.eventually_mem hz).mono (fun w hw => ih hw)
    rw [partialDeriv_congr heq i]
    exact partialDeriv_finset_sum t
      (fun a ha => ((hf a ha).iteratedPartialDeriv hU is z hz).differentiableAt) i

/-- The complex Jacobian in the standard coordinate bases. -/
def complexJacobian {κ : Type*} (f : (ι → ℂ) → (κ → ℂ)) (z : ι → ℂ) : Matrix κ ι ℂ :=
  fun j i => partialDeriv i (fun w => f w j) z

open scoped Classical in
/-- Entries of the complex Jacobian are the coordinate entries of the Fréchet derivative. -/
theorem complexJacobian_apply {κ : Type*} 
    {f : (ι → ℂ) → (κ → ℂ)} {z : ι → ℂ} (hf : DifferentiableAt ℂ f z)
    (j : κ) (i : ι) : complexJacobian f z j i = fderiv ℂ f z (Pi.single i 1) j := by
  rw [complexJacobian, partialDeriv_eq_fderiv (differentiableAt_pi.mp hf j), fderiv_apply hf j]
  rfl

omit [CompleteSpace F] in
/-- The coordinate chain rule, with an arbitrary complex normed outer target. -/
theorem partialDeriv_comp {κ : Type*} [Fintype κ]
    {f : (ι → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → F} {z : ι → ℂ}
    (hg : DifferentiableAt ℂ g (f z)) (hf : DifferentiableAt ℂ f z) (i : ι) :
    partialDeriv i (g ∘ f) z = ∑ j, complexJacobian f z j i • partialDeriv j g (f z) := by
  rw [partialDeriv_eq_fderiv (hg.comp z hf), fderiv_comp z hg hf]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_eq_sum_partialDeriv hg]
  simp_rw [complexJacobian_apply hf]

/-- Jacobians compose by matrix multiplication. -/
theorem complexJacobian_comp {κ ν : Type*} [Fintype κ] 
    {f : (ι → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → (ν → ℂ)} {z : ι → ℂ}
    (hg : DifferentiableAt ℂ g (f z)) (hf : DifferentiableAt ℂ f z) :
    complexJacobian (g ∘ f) z = complexJacobian g (f z) * complexJacobian f z := by
  ext j i
  change partialDeriv i ((fun w => g w j) ∘ f) z = _
  rw [partialDeriv_comp (differentiableAt_pi.mp hg j) hf]
  simp [Matrix.mul_apply, complexJacobian, smul_eq_mul, mul_comm]

end SeveralComplexVariables

end
