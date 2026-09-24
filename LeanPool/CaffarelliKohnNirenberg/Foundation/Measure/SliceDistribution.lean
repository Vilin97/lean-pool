/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionCore
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Space-time distributional identities restricted to time slices

Testing a space-time distributional identity against a product `ψ(x)θ(t)` of a
spatial test function and a time cutoff and separating the variables gives, for
each fixed `ψ`, a slice identity valid for almost every time.  The exceptional
null set produced this way depends on `ψ`.

This file removes that dependence.  Starting from the family of slice
identities indexed by `ψ`, the countable subfamily indexed by the mollifier
bumps centred at the points of a countable dense set yields a single null set,
and `slice_pairing_zero_of_mollifier_family` upgrades the countable family back
to every test function.  The result is the almost-everywhere slice statement
used in `paper/ckn.tex`: for almost every time, the slice is divergence free in
the sense of distributions, with one null set serving every test function.

The pairing covered is the spatial divergence pairing `∑ᵢ fᵢ ∂ᵢψ`.  Its
full-space form is exactly the slice hypothesis consumed by the pressure
module's force-cancellation results.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Almost every time satisfies the slice property simultaneously for every
mollifier bump centred at a point of a countable set.  This is the countable
intersection step: each bump contributes one null set, and countably many null
sets have null union. -/
private theorem ae_forall_mollifier_bump {d : ℕ} {Ω : Set (Vec d)} {I : Set ℝ}
    {Q : Set (Vec d)} (hQcount : Q.Countable)
    {p : (Vec d → ℝ) → ℝ → Prop}
    (hp : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      ∀ᵐ s ∂(MeasureTheory.volume.restrict I), p ψ s) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict I), ∀ y ∈ Q, ∀ n : ℕ,
      closedBall y (sliceRadius n) ⊆ Ω →
      p (fun z : Vec d =>
        mollifier (d := d) (sliceRadius n) (sliceRadius_pos n) (z - y)) s := by
  classical
  haveI : Countable Q := hQcount.to_subtype
  have h : ∀ᵐ s ∂(MeasureTheory.volume.restrict I), ∀ q : Q × ℕ,
      closedBall (q.1 : Vec d) (sliceRadius q.2) ⊆ Ω →
      p (fun z : Vec d => mollifier (d := d) (sliceRadius q.2)
        (sliceRadius_pos q.2) (z - (q.1 : Vec d))) s := by
    rw [MeasureTheory.ae_all_iff]
    rintro ⟨y, n⟩
    by_cases hb : closedBall ((y : Vec d)) (sliceRadius n) ⊆ Ω
    · have hts : tsupport (fun z : Vec d =>
          mollifier (d := d) (sliceRadius n) (sliceRadius_pos n)
            (z - (y : Vec d))) ⊆ Ω := by
        rw [tsupport_mollifier_sub_eq]
        exact hb
      filter_upwards [hp _ (contDiff_mollifier_sub (sliceRadius_pos n) (y : Vec d))
        (hasCompactSupport_mollifier_sub (sliceRadius_pos n) (y : Vec d)) hts]
        with s hs _
      exact hs
    · filter_upwards with s hcon
      exact absurd hcon hb
  filter_upwards [h] with s hs y hy n hn
  exact hs (⟨y, hy⟩, n) hn

/-- One null set for every test function, divergence form.  If for each smooth
compactly supported `ψ` supported in the open set `Ω` the slice divergence
pairing of `f` vanishes for almost every time, and almost every slice of `f` is
locally integrable on `Ω`, then for almost every time the slice divergence
pairing vanishes for *every* such `ψ`. -/
theorem ae_slice_divergence_zero_of_forall_test
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) {f : ParabolicPoint → Vec3}
    (hloc : ∀ᵐ s ∂(MeasureTheory.volume.restrict I), ∀ i : Fin 3,
      MeasureTheory.LocallyIntegrableOn (fun x : Vec3 => f (x, s) i) Ω
        MeasureTheory.volume)
    (hslice : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      ∀ᵐ s ∂(MeasureTheory.volume.restrict I),
        ∫ x in Ω, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i)
          ∂MeasureTheory.volume = 0) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict I), ∀ ψ : Vec3 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∫ x in Ω, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i)
        ∂MeasureTheory.volume = 0 := by
  classical
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense Vec3
  have hfam := ae_forall_mollifier_bump (Ω := Ω) (I := I) hQcount
    (p := fun ψ s => ∫ x in Ω, ∑ i : Fin 3, f (x, s) i *
      (fderiv ℝ ψ x) (basisVec i) ∂MeasureTheory.volume = 0) hslice
  filter_upwards [hfam, hloc] with s hs hgloc
  intro ψ hψ hψc hψΩ
  exact slice_divergence_zero_of_mollifier_family hΩ hQdense hgloc
    (fun y hy n hn => hs y hy n hn) hψ hψc hψΩ

/-- The full-space divergence statement.  For almost every time the slice
`f(·, s)` is divergence free in the sense of distributions, tested against every
smooth compactly supported spatial test function.  The conclusion is stated in
the unfolded form used by the pressure module: it reads
`∀ᵐ s, DistributionalDivergenceFree (fun x => f (x, s))`. -/
theorem ae_distributional_divergence_free_of_forall_test
    {I : Set ℝ} {f : ParabolicPoint → Vec3}
    (hloc : ∀ᵐ s ∂(MeasureTheory.volume.restrict I), ∀ i : Fin 3,
      MeasureTheory.LocallyIntegrable (fun x : Vec3 => f (x, s) i)
        MeasureTheory.volume)
    (hslice : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ᵐ s ∂(MeasureTheory.volume.restrict I),
        ∫ x, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i)
          ∂MeasureTheory.volume = 0) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict I), ∀ ψ : Vec3 → ℝ,
      ((∀ n : ℕ, ContDiff ℝ (n : ℕ∞) ψ) ∧ HasCompactSupport ψ) →
      ∫ x, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i)
        ∂MeasureTheory.volume = 0 := by
  have hloc' : ∀ᵐ s ∂(MeasureTheory.volume.restrict I), ∀ i : Fin 3,
      MeasureTheory.LocallyIntegrableOn (fun x : Vec3 => f (x, s) i)
        Set.univ MeasureTheory.volume := by
    filter_upwards [hloc] with s hs i
    exact MeasureTheory.locallyIntegrableOn_univ.2 (hs i)
  have hslice' : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.univ →
      ∀ᵐ s ∂(MeasureTheory.volume.restrict I),
        ∫ x in Set.univ, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i)
          ∂MeasureTheory.volume = 0 := by
    intro ψ h1 h2 _
    filter_upwards [hslice ψ h1 h2] with s hs
    rw [MeasureTheory.setIntegral_univ]
    exact hs
  filter_upwards [ae_slice_divergence_zero_of_forall_test isOpen_univ hloc' hslice']
    with s hs ψ hψ
  have hfin := hs ψ (contDiff_infty.2 hψ.1) hψ.2 (Set.subset_univ _)
  rwa [MeasureTheory.setIntegral_univ] at hfin

end CKN

end
