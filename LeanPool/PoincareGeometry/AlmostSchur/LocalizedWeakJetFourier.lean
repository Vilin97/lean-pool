/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.PostH2Bootstrap
public import LeanPool.PoincareGeometry.AlmostSchur.WeakJetFourierRepresentative

/-! # Cutoff localization of finite weak L² jets

All functions below are actual representatives. A smooth compact coefficient
localizes each L² field to L¹ ∩ L². Testing against the cutoff times an arbitrary
smooth function upgrades the local weak identity to a whole-space identity;
no extension-by-zero regularity is assumed.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators FourierTransform
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Multiplying an L² field by a continuous compact coefficient gives global L². -/
theorem memLp_compact_coefficient_mul {u a : E → ℝ}
    (hu : MemLp u 2 volume) (ha : Continuous a) (hca : HasCompactSupport a) :
    MemLp (fun x => a x * u x) 2 volume :=
  hu.mul' (ha.memLp_top_of_hasCompactSupport hca volume)

/-- The same localized field is L¹, by Cauchy--Schwarz. -/
theorem integrable_compact_coefficient_mul {u a : E → ℝ}
    (hu : MemLp u 2 volume) (ha : Continuous a) (hca : HasCompactSupport a) :
    Integrable (fun x => a x * u x) volume :=
  (ha.memLp_of_hasCompactSupport hca : MemLp a 2 volume).integrable_mul hu

/-- Smooth tests need not have compact support after the coefficient has
localized the integrand. -/
theorem integrable_compact_coefficient_mul_test {u a φ : E → ℝ}
    (hu : MemLp u 2 volume) (ha : Continuous a) (hca : HasCompactSupport a)
    (hφ : Continuous φ) : Integrable (fun x => a x * u x * φ x) volume := by
  have hi := integrable_compact_coefficient_mul hu (ha.mul hφ) hca.mul_right
  convert hi using 1
  funext x
  simp only [Pi.mul_apply]
  ring

/-- The genuine whole-space Leibniz identity for a compactly localized weak
derivative, valid for arbitrary smooth (not necessarily compact) real tests. -/
theorem weak_derivative_compact_localization
    {K : Set E} {u du a : E → ℝ} (v : E)
    (hu : MemLp u 2 volume) (hdu : MemLp du 2 volume)
    (hw : HasWeakDirectionalDerivativeOn K v u du)
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) (hs : tsupport a ⊆ K)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    (∫ x, (a x * u x) * fderiv ℝ φ x v) =
      -(∫ x, (fderiv ℝ a x v * u x + a x * du x) * φ x) := by
  let ψ : E → ℝ := fun x => a x * φ x
  have hψ : ContDiff ℝ ∞ ψ := ha.mul hφ
  have hcψ : HasCompactSupport ψ := hca.mul_right
  have hsψ : tsupport ψ ⊆ K := tsupport_mul_subset_left.trans hs
  have he := hw ψ hψ hcψ hsψ
  have hl : ∀ x ∉ K, u x * fderiv ℝ ψ x v = 0 := by
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (hsψ hh))]
    simp
  have hr : ∀ x ∉ K, du x * ψ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hsψ hh))]
    simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hl,
    setIntegral_eq_integral_of_forall_compl_eq_zero hr] at he
  have hd (x : E) : fderiv ℝ ψ x v =
      fderiv ℝ a x v * φ x + a x * fderiv ℝ φ x v := by
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v)
      (fderiv_mul (ha.differentiable (by simp) x) (hφ.differentiable (by simp) x))
    change fderiv ℝ (a * φ) x v = _
    simpa [mul_comm, add_comm] using hh
  have hda := contDiff_smooth_test_derivative ha v
  have hdφ := contDiff_smooth_test_derivative hφ v
  have hi₁ := integrable_compact_coefficient_mul_test hu hda.continuous
    (hca.fderiv_apply ℝ v) hφ.continuous
  have hi₂ := integrable_compact_coefficient_mul_test hu ha.continuous hca hdφ.continuous
  have hi₃ := integrable_compact_coefficient_mul_test hdu ha.continuous hca hφ.continuous
  have he' : (∫ x, fderiv ℝ a x v * u x * φ x) +
      (∫ x, a x * u x * fderiv ℝ φ x v) = -(∫ x, a x * du x * φ x) := by
    rw [← integral_add hi₁ hi₂]
    convert he using 1
    · congr 1
      funext x
      rw [hd]
      ring
    · congr 2
      funext x
      dsimp [ψ]
      ring
  have hr' : (∫ x, (fderiv ℝ a x v * u x + a x * du x) * φ x) =
      (∫ x, fderiv ℝ a x v * u x * φ x) + (∫ x, a x * du x * φ x) := by
    rw [← integral_add hi₁ hi₃]
    congr 1
    funext x
    ring
  rw [hr']
  linarith

/-- Ordered Leibniz terms, retaining multiplicities without assuming weak
mixed derivatives commute. First word differentiates the cutoff; second word
selects the weak jet field. -/
def cutoffJetTerms {ι : Type*} : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | i :: w => (cutoffJetTerms w).map (fun p => (i :: p.1, p.2)) ++
      (cutoffJetTerms w).map (fun p => (p.1, i :: p.2))

/-- No Leibniz term requests more jet derivatives than the original word. -/
theorem cutoffJetTerms_length {ι : Type*} {w : List ι} {p : List ι × List ι}
    (hp : p ∈ cutoffJetTerms w) : p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil =>
    have hp' : p = ([], []) := by simpa [cutoffJetTerms] using hp
    subst p
    simp
  | cons i w ih =>
    simp only [cutoffJetTerms, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;>
      simp only [List.length_cons, Prod.fst, Prod.snd] <;>
      have := ih hq <;> omega

/-- Iterated cutoff derivatives stay smooth and supported in the original cutoff. -/
theorem cutoff_iterate_properties {ι : Type*} (b : ι → E)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (w : List ι) :
    ContDiff ℝ ∞ (localDirectionalIterate b χ w) ∧
      HasCompactSupport (localDirectionalIterate b χ w) ∧
      tsupport (localDirectionalIterate b χ w) ⊆ tsupport χ := by
  induction w with
  | nil => exact ⟨hχ, hcχ, Subset.rfl⟩
  | cons i w ih =>
    exact ⟨contDiff_smooth_test_derivative ih.1 (b i), ih.2.1.fderiv_apply ℝ (b i),
      (tsupport_fderiv_apply_subset ℝ (b i)).trans ih.2.2⟩

/-- One concrete Leibniz term in a localized jet. -/
def cutoffJetTerm {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (χ : E → ℝ) (p : List ι × List ι) (x : E) : ℝ :=
  localDirectionalIterate b χ p.1 x * J.value p.2 x

/-- The localized derivative fields, as actual functions rather than quotient choices. -/
def localizedWeakJet {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (χ : E → ℝ) (w : List ι) (x : E) : ℝ :=
  ((cutoffJetTerms w).map (fun p => cutoffJetTerm J χ p x)).sum

/-- Finite list sums preserve L², including repeated Leibniz terms. -/
theorem memLp_list_sum {α : Type*} (l : List α) (f : α → E → ℝ)
    (hf : ∀ a ∈ l, MemLp (f a) 2 volume) :
    MemLp (fun x => (l.map (fun a => f a x)).sum) 2 volume := by
  induction l with
  | nil => simpa using (memLp_zero : MemLp (fun _ : E => (0 : ℝ)) 2 volume)
  | cons a l ih =>
    change MemLp (f a + fun x => (l.map (fun a => f a x)).sum) 2 volume
    exact (hf a (by simp)).add (ih (fun b hb => hf b (by simp [hb])))

/-- Finite list sums of integrable functions are integrable. -/
theorem integrable_list_sum {α : Type*} (l : List α) (f : α → E → ℝ)
    (hf : ∀ a ∈ l, Integrable (f a) volume) :
    Integrable (fun x => (l.map (fun a => f a x)).sum) volume := by
  induction l with
  | nil => simpa using (integrable_zero : Integrable (fun _ : E => (0 : ℝ)) volume)
  | cons a l ih =>
    change Integrable (f a + fun x => (l.map (fun a => f a x)).sum) volume
    exact (hf a (by simp)).add (ih (fun b hb => hf b (by simp [hb])))

/-- Integration commutes with the finite Leibniz list sum. -/
theorem integral_list_sum {α : Type*} (l : List α) (f : α → E → ℝ)
    (hf : ∀ a ∈ l, Integrable (f a) volume) :
    (∫ x, (l.map (fun a => f a x)).sum) = (l.map (fun a => ∫ x, f a x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ht : ∀ b ∈ l, Integrable (f b) volume := fun b hb => hf b (by simp [hb])
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hf a (by simp)) (integrable_list_sum l f ht), ih ht]

/-- Every localized field is globally L¹ ∩ L² and supported in the cutoff. -/
theorem localizedWeakJet_properties {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) {χ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (w : List ι) :
    MemLp (localizedWeakJet J χ w) 2 volume ∧
      Integrable (localizedWeakJet J χ w) volume ∧
      tsupport (localizedWeakJet J χ w) ⊆ tsupport χ := by
  have hm (p : List ι × List ι) := cutoff_iterate_properties b hχ hcχ p.1
  refine ⟨memLp_list_sum _ _ (fun p _ =>
    memLp_compact_coefficient_mul (Lp.memLp (J.value p.2)) (hm p).1.continuous (hm p).2.1),
    integrable_list_sum _ _ (fun p _ => integrable_compact_coefficient_mul
      (Lp.memLp (J.value p.2)) (hm p).1.continuous (hm p).2.1), ?_⟩
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz (p : List ι × List ι) : cutoffJetTerm J χ p x = 0 := by
    have hxp : x ∉ tsupport (localDirectionalIterate b χ p.1) := fun hh => hn ((hm p).2.2 hh)
    simp [cutoffJetTerm, image_eq_zero_of_notMem_tsupport hxp]
  have he : localizedWeakJet J χ w x = 0 := by simp [localizedWeakJet, hz]
  exact hx he

/-- Every localized field can be integrated against arbitrary smooth tests. -/
theorem integrable_localizedWeakJet_mul_test {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) {χ φ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hφ : Continuous φ) (w : List ι) :
    Integrable (fun x => localizedWeakJet J χ w x * φ x) volume := by
  have hi := integrable_list_sum (cutoffJetTerms w)
    (fun p x => cutoffJetTerm J χ p x * φ x) (fun p _ =>
      integrable_compact_coefficient_mul_test (Lp.memLp (J.value p.2))
        (cutoff_iterate_properties b hχ hcχ p.1).1.continuous
        (cutoff_iterate_properties b hχ hcχ p.1).2.1 hφ)
  simpa only [List.sum_map_mul_right, localizedWeakJet] using hi

end AlmostSchur
