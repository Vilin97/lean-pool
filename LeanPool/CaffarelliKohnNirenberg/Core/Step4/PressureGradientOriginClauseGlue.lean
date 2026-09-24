/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSided

/-!
# The space-time weak pressure gradient on a whole time interval

The measurable selection of a space-time weak spatial derivative from
slice-wise weak derivatives is carried out on a product box whose time factor
carries an integrable datum.  The time set of a suitable weak solution is only
an open interval, so the datum need not be integrable there; the selection is
therefore made on each member of a countable increasing family of time windows
and the resulting fields are assembled into a single one.

The assembled field is unambiguous because the slice-wise weak derivative is
unique almost everywhere on the inner spatial set: two selections made on
overlapping windows agree with the same slice derivative at almost every time.
This module records the gluing construction and the geometric facts about the
unit domain hypothesis of the one-sided pressure estimate.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-- The unit domain hypothesis gives the closed unit spatial ball inside `Ω`
and the closed unit time window inside `I`. -/
theorem originClauseUnitBall_subset_of_dom {Ω : Set Vec3} {I : Set ℝ}
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ CKN.spaceTimeSet Ω I) :
    {y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1} ⊆ Ω ∧ Icc (-1 : ℝ) 0 ⊆ I := by
  rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)] at hdom
  constructor
  · intro y hy
    have hmem : ((y, (0 : ℝ)) : ParabolicPoint) ∈
        ({y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1} ×ˢ Icc ((0 : ℝ) - 1 ^ 2) 0) := by
      refine ⟨hy, ?_⟩
      constructor <;> norm_num
    exact (hdom hmem).1
  · intro t ht
    have hmem : (((0 : Vec3), t) : ParabolicPoint) ∈
        ({y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1} ×ˢ Icc ((0 : ℝ) - 1 ^ 2) 0) := by
      refine ⟨by simp [vec3EuclideanNorm_zero], ?_⟩
      refine ⟨?_, ht.2⟩
      have h1 := ht.1
      norm_num
      linarith only [h1]
    exact (hdom hmem).2

/-- The closure of a Euclidean spatial ball of positive radius is compact. -/
theorem originClauseIsCompact_closure_vec3Ball {x : Vec3} {r : ℝ} (hr : 0 < r) :
    IsCompact (closure (vec3Ball x r)) := by
  rw [closure_vec3Ball hr]
  have hcompact := vec3Homeomorph.isCompact_preimage.mpr
    (isCompact_closedBall (vec3Homeomorph x) r)
  convert hcompact using 1
  ext y
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall,
    vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
    ← vec3EuclideanNorm_eq_l2]

/-- The outer spatial ball of the origin construction is a local box together
with any compact order-connected time set inside `I`. -/
theorem originClauseLocalBox_of_time {Ω : Set Vec3} {I : Set ℝ} {R₀ : ℝ}
    (hR₀ : 0 < R₀) (hR₀one : R₀ < 1)
    (hΩ : {y : Vec3 | vec3EuclideanNorm (y - 0) ≤ 1} ⊆ Ω)
    {J : Set ℝ} (hJord : J.OrdConnected) (hJcompact : IsCompact J)
    (hJI : J ⊆ I) :
    CKN.localBox Ω I (vec3Ball (0 : Vec3) R₀) J := by
  refine ⟨isOpen_vec3Ball _ _, originClauseIsCompact_closure_vec3Ball hR₀, ?_,
    hJord, ?_, ?_⟩
  · rw [closure_vec3Ball hR₀]
    intro y hy
    exact hΩ (le_trans hy hR₀one.le)
  · rw [hJcompact.isClosed.closure_eq]
    exact hJcompact
  · rw [hJcompact.isClosed.closure_eq]
    exact hJI

open scoped Classical in
/-- The space-time field assembled from a family of fields indexed by a
pairwise disjoint decomposition of the time axis. -/
def originClauseGluedField (D : ℕ → ParabolicPoint → ℝ) (A : ℕ → Set ℝ) :
    ParabolicPoint → ℝ :=
  fun z => if h : ∃ n, z.2 ∈ A n then D (Nat.find h) z else 0

/-- On the `n`-th piece of the decomposition the glued field is the `n`-th field. -/
theorem originClauseGluedField_eq_of_mem {D : ℕ → ParabolicPoint → ℝ} {A : ℕ → Set ℝ}
    (hdisj : Pairwise (Function.onFun Disjoint A))
    {n : ℕ} {z : ParabolicPoint} (hz : z.2 ∈ A n) :
    originClauseGluedField D A z = D n z := by
  classical
  have hex : ∃ m, z.2 ∈ A m := ⟨n, hz⟩
  have hfind : Nat.find hex = n := by
    by_contra hne
    have hmem := Nat.find_spec hex
    have hdis := hdisj hne
    exact (Set.disjoint_left.mp hdis) hmem hz
  rw [originClauseGluedField, dite_eq_left_of_eq_true (eq_true hex)]
  simp only [hfind]

/-- Off the decomposition the glued field vanishes. -/
theorem originClauseGluedField_eq_zero {D : ℕ → ParabolicPoint → ℝ} {A : ℕ → Set ℝ}
    {z : ParabolicPoint} (hz : ∀ n, z.2 ∉ A n) :
    originClauseGluedField D A z = 0 := by
  classical
  have hnot : ¬ ∃ n, z.2 ∈ A n := fun ⟨n, hn⟩ => hz n hn
  rw [originClauseGluedField, dite_eq_right_of_eq_false (eq_false hnot)]

/-- The space-time weak spatial derivative on a countable increasing union of
time windows.  The four conclusions are joint measurability on the inner box,
identification with every slice weak derivative at almost every time, the
iterated integration-by-parts identity on each window, and vanishing off the
time set. -/
theorem originClauseWeakGradient_on_time_union (k : Fin 3)
    {B B' : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ}
    (hB : IsOpen B) (hB' : MeasurableSet B') (hB'c : IsCompact (closure B'))
    (hB'B : closure B' ⊆ B)
    {J : ℕ → Set ℝ} (hJmeas : ∀ n, MeasurableSet (J n))
    (hJI : (⋃ n, J n) = I)
    (hp : ∀ n, IntegrableOn p (B ×ˢ J n) volume)
    (hslice : ∀ᵐ t ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume ∧
      HasWeakPartialDerivOn B k (fun x => p (x, t)) g) :
    ∃ D : ParabolicPoint → ℝ,
      AEMeasurable D (volume.restrict (B' ×ˢ I)) ∧
      (∀ᵐ t ∂(volume.restrict I), ∀ g : Vec3 → ℝ,
        LocallyIntegrableOn g B volume →
        HasWeakPartialDerivOn B k (fun x => p (x, t)) g →
        (fun x => D (x, t)) =ᵐ[volume.restrict B'] g) ∧
      (∀ n : ℕ, ∀ Ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ →
        tsupport Ψ ⊆ B' ×ˢ J n →
        (∫ t in J n, ∫ x in B', p (x, t) * spatialPartial Ψ k (x, t)) =
          -∫ t in J n, ∫ x in B', D (x, t) * Ψ (x, t)) ∧
      (∀ z : ParabolicPoint, z.2 ∉ I → D z = 0) := by
  classical
  set A : ℕ → Set ℝ := disjointed J with hAdef
  have hAsub : ∀ n, A n ⊆ J n := fun n => disjointed_subset J n
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n => MeasurableSet.disjointed hJmeas n
  have hAdisj : Pairwise (Function.onFun Disjoint A) := disjoint_disjointed J
  have hAI : (⋃ n, A n) = I := by rw [hAdef, iUnion_disjointed, hJI]
  have hJsub : ∀ n, J n ⊆ I := by
    intro n
    rw [← hJI]
    exact subset_iUnion J n
  have hsel : ∀ n : ℕ, ∃ Dn : ParabolicPoint → ℝ,
      AEMeasurable Dn (volume.restrict (B' ×ˢ J n)) ∧
      (∀ᵐ t ∂(volume.restrict (J n)), ∀ g : Vec3 → ℝ,
        LocallyIntegrableOn g B volume →
        HasWeakPartialDerivOn B k (fun x => p (x, t)) g →
        (fun x => Dn (x, t)) =ᵐ[volume.restrict B'] g) ∧
      (∀ Ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ →
        tsupport Ψ ⊆ B' ×ˢ J n →
        (∫ t in J n, ∫ x in B', p (x, t) * spatialPartial Ψ k (x, t)) =
          -∫ t in J n, ∫ x in B', Dn (x, t) * Ψ (x, t)) := by
    intro n
    obtain ⟨Dn, h1, h2, h3, _h4⟩ :=
      exists_spacetime_weak_gradient_of_slices k hB hB' hB'c hB'B (hp n)
        (ae_restrict_of_ae_restrict_of_subset (hJsub n) hslice)
    exact ⟨Dn, h1, h2, h3⟩
  choose Dn hDnmeas hDnuniq hDnpair using hsel
  have hcong : ∀ n, (fun z : ParabolicPoint => originClauseGluedField Dn A z)
      =ᵐ[volume.restrict (B' ×ˢ A n)] Dn n := by
    intro n
    refine (ae_restrict_iff' (hB'.prod (hAmeas n))).mpr (Eventually.of_forall ?_)
    intro z hz
    exact originClauseGluedField_eq_of_mem hAdisj hz.2
  have huniq : ∀ᵐ t ∂(volume.restrict I), ∀ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume →
      HasWeakPartialDerivOn B k (fun x => p (x, t)) g →
      (fun x => originClauseGluedField Dn A (x, t)) =ᵐ[volume.restrict B'] g := by
    rw [← hAI, ae_restrict_iUnion_iff]
    intro n
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hAsub n) (hDnuniq n),
      ae_restrict_mem (hAmeas n)] with t ht htmem g hg hgw
    have heq : (fun x => originClauseGluedField Dn A (x, t)) = fun x => Dn n (x, t) := by
      funext x
      exact originClauseGluedField_eq_of_mem hAdisj htmem
    rw [heq]
    exact ht g hg hgw
  refine ⟨originClauseGluedField Dn A, ?_, huniq, ?_, ?_⟩
  · rw [show B' ×ˢ I = ⋃ n, B' ×ˢ A n by rw [← hAI, prod_iUnion]]
    refine aemeasurable_iUnion_iff.mpr ?_
    intro n
    refine AEMeasurable.congr ?_ (hcong n).symm
    exact (hDnmeas n).mono_measure
      (Measure.restrict_mono_set volume (Set.prod_mono (subset_refl B') (hAsub n)))
  · intro n Ψ hΨ hΨc hsupp
    have hDeq : ∀ᵐ t ∂(volume.restrict (J n)),
        (fun x => originClauseGluedField Dn A (x, t))
          =ᵐ[volume.restrict B'] (fun x => Dn n (x, t)) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hJsub n) huniq,
        hDnuniq n, ae_restrict_of_ae_restrict_of_subset (hJsub n) hslice]
        with t h1 h2 h3
      obtain ⟨g, hg, hgw⟩ := h3
      exact (h1 g hg hgw).trans (h2 g hg hgw).symm
    have hint : (∫ t in J n, ∫ x in B', originClauseGluedField Dn A (x, t) * Ψ (x, t)) =
        ∫ t in J n, ∫ x in B', Dn n (x, t) * Ψ (x, t) := by
      refine integral_congr_ae ?_
      filter_upwards [hDeq] with t ht
      exact integral_congr_ae (ht.mul (Filter.EventuallyEq.refl _ _))
    rw [hint]
    exact hDnpair n Ψ hΨ hΨc hsupp
  · intro z hz
    refine originClauseGluedField_eq_zero (fun n hn => hz ?_)
    rw [← hAI]
    exact mem_iUnion.mpr ⟨n, hn⟩

end CKN.Core.Step4
