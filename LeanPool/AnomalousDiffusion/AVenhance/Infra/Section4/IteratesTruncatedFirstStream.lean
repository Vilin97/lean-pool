/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedStreamFull
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFirstStreamSum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFirstStreamFactorials
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordGrouping

/-! Exact first stream multiplicity and analytic radius gain at every terminal time. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- One actual first stream-jet pairing uses only preceding derivative-order
 gradient energies. Joint smoothness discharges all time integrability. -/
theorem iterate_truncated_first_stream_time_pairing_bound
    {φ u : ℝ → Vec 2 → ℝ} {H M : ℝ} (hH : 0 < H)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => φ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hφp : ∀ t, 0 < t → IsZ2Periodic (φ t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t))
    (i j : Fin 2) (w q : List (Fin 2)) (hq : q.length = w.length)
    (hjet : ∀ t x k, |spaceGrad (fun y => spaceGrad (φ t) y j) x k| ≤ H)
    (hM : ∀ r : List (Fin 2), r.length = w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord r (u t))) ≤ M) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord (i :: w) (u z.1)) z.2)
      ((spaceGrad (φ z.1) z.2 j • sigmaMat).mulVec
        (spaceGrad (iterateSpatialWord q (u z.1)) z.2))| ≤ 2 * H * M := by
  have hs {f : ℝ → Vec 2 → ℝ}
      (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => f z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (t : ℝ) (ht : 0 < t) :
      ContDiff ℝ (⊤ : ℕ∞) (f t) :=
    hf.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
      (fun _ => ⟨ht.le, Set.mem_univ _⟩)
  have hψ := iterateSpatialWord_smooth_up_to_initial hφ [j]
  have hw := iterateSpatialWord_smooth_up_to_initial hu (i :: w)
  have hv := iterateSpatialWord_smooth_up_to_initial hu q
  have ht := iterate_truncated_stream_pairing_bound_full hH hψ hw hv hs0 hs1
    (fun t ht => iterateSpatialWord_periodic (hs hφ t ht) (hφp t ht) [j])
    (fun t ht => iterateSpatialWord_periodic (hs hu t ht) (hup t ht) (i :: w))
    (fun t ht => iterateSpatialWord_periodic (hs hu t ht) (hup t ht) q) hjet
  have hi : IntegrableOn (fun z : AmnrSpace => iterateSpatialWord (i :: w) (u z.1) z.2 ^ 2)
      timeCube := iterate_timeCube_integrable_of_continuousOn (hw.continuousOn.pow 2)
  have hm := integral_mono hi (iterate_word_gradient_energy_integrable hu w)
    (fun z => iterateSpatialWord_sq_le_tail_gradient (u z.1) i w z.2)
  have he : (∫ z in timeCube, iterateSpatialWord (i :: w) (u z.1) z.2 ^ 2) ≤ M :=
    hm.trans (hM w rfl)
  have hvE := hM q hq
  have hh := mul_le_mul_of_nonneg_left (add_le_add he hvE) hH.le
  exact ht.trans (by convert hh using 1; ring)

theorem IteratesTruncatedFirstStream.first_stream_time_abs_sum {α : Type*} (P : List α) (f : α →
    ℝ) :
    |(P.map f).sum| ≤ (P.map (fun p => |f p|)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

/-- Every first coefficient derivative uses the same preceding derivative
energy. Exact ordered multiplicity supplies n, including repeated letters. -/
theorem iterate_truncated_first_stream_time_sum_bound
    {φ u : ℝ → Vec 2 → ℝ} {H M : ℝ} (hH : 0 < H)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => φ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hφp : ∀ t, 0 < t → IsZ2Periodic (φ t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t))
    (i : Fin 2) (w : List (Fin 2))
    (hjet : ∀ t x j k, |spaceGrad (fun y => spaceGrad (φ t) y j) x k| ≤ H)
    (hM : ∀ q : List (Fin 2), q.length = w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (u t))) ≤ M) :
    |(((iterateSpatialSplits (i :: w)).filter (fun p => p.1.length == 1)).map
      (fun p => ∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord (i :: w) (u
          z.1)) z.2)
        ((iterateSpatialWord p.1 (φ z.1) z.2 • sigmaMat).mulVec
          (spaceGrad (iterateSpatialWord p.2 (u z.1)) z.2)))).sum| ≤
      2 * H * ((w.length + 1 : ℕ) : ℝ) * M := by
  let P := (iterateSpatialSplits (i :: w)).filter (fun p => p.1.length == 1)
  let f := fun p : List (Fin 2) × List (Fin 2) =>
    ∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord (i :: w) (u z.1)) z.2)
      ((iterateSpatialWord p.1 (φ z.1) z.2 • sigmaMat).mulVec (spaceGrad (iterateSpatialWord p.2
          (u z.1)) z.2))
  have ht : ∀ p ∈ P, |f p| ≤ 2 * H * M := by
    intro p hp
    have hs := List.mem_filter.mp hp
    have hl : p.1.length = 1 := by simpa using hs.2
    obtain ⟨j, hj⟩ := List.length_eq_one_iff.mp hl
    have ho := iterateSpatialSplits_orders (i :: w) hs.1
    have hq : p.2.length = w.length := by simp only [List.length_cons] at ho; omega
    have h := iterate_truncated_first_stream_time_pairing_bound
      hH hφ hu hs0 hs1 hφp hup i j w p.2 hq (fun t x k => hjet t x j k) hM
    simpa only [f, hj, iterateSpatialWord] using h
  have hc : P.length = w.length + 1 := by
    change ((iterateSpatialSplits (i :: w)).filter (fun p => p.1.length == 1)).length = _
    rw [← List.countP_eq_length_filter, iterateSpatialSplits_count]
    simp
  change |(P.map f).sum| ≤ _
  calc
    _ ≤ (P.map (fun p => |f p|)).sum := IteratesTruncatedFirstStream.first_stream_time_abs_sum P f
    _ ≤ (P.map (fun _ => 2 * H * M)).sum := List.sum_le_sum ht
    _ = _ := by simp [hc]; ring

/-- The full first stream-jet contribution has precisely the n-1 norm
 squared and one squared radius gain; multiplicity causes no order loss. -/
theorem iterate_truncated_first_stream_time_analytic_bound
    {φ u : ℝ → Vec 2 → ℝ} {H B L d : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => φ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hφp : ∀ t, 0 < t → IsZ2Periodic (φ t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t)) (j : Fin 2) (w : List (Fin 2)) (i : ℕ)
    (hjet : ∀ t x j k, |spaceGrad (fun y => spaceGrad (φ t) y j) x k| ≤ H)
    (hM : ∀ q : List (Fin 2), q.length = w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (u t))) ≤
        B ^ 2 * (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 * d ^ 2) :
    |(((iterateSpatialSplits (j :: w)).filter (fun p => p.1.length == 1)).map
      (fun p => ∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord (j :: w) (u
          z.1)) z.2)
        ((iterateSpatialWord p.1 (φ z.1) z.2 • sigmaMat).mulVec
          (spaceGrad (iterateSpatialWord p.2 (u z.1)) z.2)))).sum| ≤
      2 * H * B ^ 2 / L ^ 2 *
        (((w.length + 1 + 2 * i).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 * d ^ 2 := by
  have ht := iterate_truncated_first_stream_time_sum_bound hH hφ hu hs0 hs1 hφp hup j w hjet hM
  have hs := iterate_first_stream_analytic_weight_le (w.length + 1) i (by omega) hL
  simp only [Nat.add_sub_cancel] at hs
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * H * B ^ 2 * d ^ 2)
  apply ht.trans
  calc
    _ = (2 * H * B ^ 2 * d ^ 2) * ((w.length + 1 : ℕ) : ℝ) *
        (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 := by ring
    _ ≤ (2 * H * B ^ 2 * d ^ 2) *
        ((((w.length + 1 + 2 * i).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 / L ^ 2) := by
      simpa only [mul_assoc] using hm
    _ = _ := by ring

end AVenhance.Infra.Section4
