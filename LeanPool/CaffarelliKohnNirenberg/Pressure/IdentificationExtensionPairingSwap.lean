/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingKernel
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingSource
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionCore

/-!
# One null set for every second-order test pairing

A second-order distributional identity on time slices is first obtained one test
function at a time, and the exceptional set of times then depends on the test
function.  Testing instead against the countable family of mollifier bumps
centred at the points of a countable dense set produces a single null set, and
the mollifier-bump upgrade recovers every smooth compactly supported test
function from that countable family.  This is the second-order counterpart of
the divergence-form and multiplication-form upgrades used for the slice
identities.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The second-order instance of the mollifier-bump family upgrade.  If the
second-order pairing of a locally integrable matrix field `G` vanishes against
the mixed second derivatives of every mollifier bump centred at a point of a
dense set, then it vanishes against the mixed second derivatives of every smooth
compactly supported test function. -/
theorem slice_second_pairing_zero_of_mollifier_family
    {Q : Set Vec3} (hQ : Dense Q) {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j : Fin 3, LocallyIntegrable (G i j) volume)
    (hzero : ∀ y ∈ Q, ∀ n : ℕ,
      ∫ x, ∑ i, ∑ j, G i j x * mixedSecond (fun z : Vec3 =>
        mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n) (z - y)) i j x = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, ∑ i, ∑ j, G i j x * mixedSecond ψ i j x = 0 := by
  classical
  have hmain : ∫ x in (Set.univ : Set Vec3),
      ∑ q : Fin 3 × Fin 3, G q.1 q.2 x * mixedSecond ψ q.1 q.2 x = 0 := by
    refine slice_pairing_zero_of_mollifier_family (d := 3) (ι := Fin 3 × Fin 3)
      (g := fun x q => G q.1 q.2 x)
      (κ := fun n q => mixedSecond
        (mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n)) q.1 q.2)
      (T := fun q => mixedSecond ψ q.1 q.2)
      isOpen_univ hQ
      (fun q => (MeasureTheory.locallyIntegrableOn_univ).2 (hG q.1 q.2))
      (fun n q => continuous_mixedSecond_mollifier (sliceRadius_pos n) q.1 q.2)
      (fun n q z hz => mixedSecond_mollifier_eq_zero (sliceRadius_pos n) q.1 q.2 hz)
      hψ.continuous hψc (Set.subset_univ _)
      (fun q => (contDiff_mixedSecond_smooth hψ q.1 q.2).continuous)
      (fun q x hx => ?_)
      (fun n q x => integral_mul_mixedSecond_mollifier_sub hψ q.1 q.2
        (sliceRadius_pos n) x)
      (fun y hy n _hn => ?_)
    · exact image_eq_zero_of_notMem_tsupport
        (fun h => hx (pressureCutoff_tsupport_mixedSecond_subset ψ q.1 q.2 h))
    · have h := hzero y hy n
      rw [MeasureTheory.setIntegral_univ, ← h]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mixedSecond_sub_const (mollifier_contDiff (d := 3) (n := ⊤)
        (sliceRadius_pos n)) y x i j]
  rw [MeasureTheory.setIntegral_univ] at hmain
  rw [← hmain]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Fintype.sum_prod_type]

/-- One null set for every test function, second-order form.  If for each smooth
compactly supported `ψ` the second-order slice pairing vanishes for almost every
time, and almost every slice of the matrix field is locally integrable, then for
almost every time the pairing vanishes for *every* such `ψ`. -/
theorem ae_slice_second_pairing_zero_of_forall_test
    {I : Set ℝ} {G : ℝ → Fin 3 → Fin 3 → Vec3 → ℝ}
    (hloc : ∀ᵐ s ∂volume.restrict I,
      ∀ i j : Fin 3, LocallyIntegrable (G s i j) volume)
    (hzero : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ᵐ s ∂volume.restrict I,
        ∫ x, ∑ i, ∑ j, G s i j x * mixedSecond ψ i j x = 0) :
    ∀ᵐ s ∂volume.restrict I, ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      ∫ x, ∑ i, ∑ j, G s i j x * mixedSecond ψ i j x = 0 := by
  classical
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense Vec3
  have : Countable Q := hQcount.to_subtype
  have hfam : ∀ᵐ s ∂volume.restrict I, ∀ q : Q × ℕ,
      ∫ x, ∑ i, ∑ j, G s i j x * mixedSecond (fun z : Vec3 =>
        mollifier (d := 3) (sliceRadius q.2) (sliceRadius_pos q.2)
          (z - (q.1 : Vec3))) i j x = 0 := by
    rw [MeasureTheory.ae_all_iff]
    rintro ⟨y, n⟩
    exact hzero _ (contDiff_mollifier_sub (sliceRadius_pos n) (y : Vec3))
      (hasCompactSupport_mollifier_sub (sliceRadius_pos n) (y : Vec3))
  filter_upwards [hfam, hloc] with s hs hgloc
  intro ψ hψ hψc
  exact slice_second_pairing_zero_of_mollifier_family hQdense hgloc
    (fun y hy n => hs (⟨y, hy⟩, n)) hψ hψc

end CKN

end
