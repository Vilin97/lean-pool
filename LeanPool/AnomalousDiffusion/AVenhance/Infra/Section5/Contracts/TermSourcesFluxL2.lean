/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing

/-! # Space-time `L²` transfer for the flux source contracts

Generic measure-theoretic step: if the pointwise squared norm of a flux is dominated by a finite
nonnegative combination of squared norms of fields `V j` that are continuous on `[0,1] × ℝ²`, then
the time-`L²`-of-space-`L²` norm of the flux (the left side of the `*SourceContract`s) is bounded by
the square root of the same combination of the space-time `L²` norms of the `V j`.

Only the slices `F t`, `t ∈ (0,1)`, of the flux are required to be continuous: the flux itself
needs no joint regularity. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

/-- The left side of the `Twistie3SourceContract`, `Normie1SourceContract`,
`Normie2SourceContract`. -/
def saTimeL2 (F : ℝ → Vec 2 → Vec 2) : ENNReal :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (gradNormSq (F t))) ^ 2) ^ (1 / 2 : ℝ)

theorem sa_gradNormSq_nonneg (F : Vec 2 → Vec 2) : 0 ≤ gradNormSq F := by
  unfold gradNormSq
  exact integral_nonneg fun x => vecNormSq_nonneg (F x)

theorem sa_lintegrand_eq (F : Vec 2 → Vec 2) :
    ENNReal.ofReal (Real.sqrt (gradNormSq F)) ^ 2 = ENNReal.ofReal (gradNormSq F) := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt (sa_gradNormSq_nonneg F)]

/-- Joint continuity of the components gives continuity of the squared norm. -/
theorem sa_continuousOn_vecNormSq {V : ℝ → Vec 2 → Vec 2} {s : Set (ℝ × Vec 2)}
    (hV : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2 i) s) :
    ContinuousOn (fun p : ℝ × Vec 2 => vecNormSq (V p.1 p.2)) s :=
  LeftToShow.continuous_vecNormSq_two.comp_continuousOn (continuousOn_pi.2 hV)

/-- The slice energy of a field continuous on `[0,1] × ℝ²` is continuous in time. -/
theorem sa_sliceEnergy_continuousOn {V : ℝ → Vec 2 → Vec 2}
    (hV : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :
    ContinuousOn (fun t => gradNormSq (V t)) (Set.Icc (0 : ℝ) 1) :=
  LeftToShow.continuousOn_integral_unitCube (h := fun t x => vecNormSq (V t x))
    (sa_continuousOn_vecNormSq hV)

/-- Fubini: the space-time norm is the time integral of the slice energies. -/
theorem sa_spaceTime_eq_integral {V : ℝ → Vec 2 → Vec 2}
    (hV : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :
    spaceTimeGradNormSq V = ∫ t in Set.Ioo (0 : ℝ) 1, gradNormSq (V t) := by
  calc
    spaceTimeGradNormSq V = ∫ t in (0 : ℝ)..1, ∫ x in unitCube, vecNormSq (V t x) :=
      LeftToShow.spaceTimeGradNormSq_eq_intervalIntegral (continuousOn_pi.2 hV)
    _ = ∫ t in Set.Ioo (0 : ℝ) 1, gradNormSq (V t) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
      rfl

theorem sa_slice_integrableOn {V : ℝ → Vec 2 → Vec 2}
    (hV : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (fun x => vecNormSq (V t x)) unitCube := by
  refine LeftToShow.integrableOn_unitCube_of_continuous ?_
  have hmap : Continuous (fun x : Vec 2 => (t, x)) := by fun_prop
  have := (sa_continuousOn_vecNormSq hV).comp_continuous hmap (fun x => ⟨ht, Set.mem_univ x⟩)
  exact this

/-- **Generic space-time transfer.** -/
theorem saTimeL2_le {F : ℝ → Vec 2 → Vec 2} {V : Fin 3 → ℝ → Vec 2 → Vec 2} {c : Fin 3 → ℝ}
    (hc : ∀ j, 0 ≤ c j)
    (hV : ∀ j (i : Fin 2), ContinuousOn (fun p : ℝ × Vec 2 => V j p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    (hFc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Continuous (F t))
    (hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x,
      vecNormSq (F t x) ≤ ∑ j, c j * vecNormSq (V j t x)) :
    saTimeL2 F ≤ ENNReal.ofReal (Real.sqrt (∑ j, c j * spaceTimeGradNormSq (V j))) := by
  have hgcont (j : Fin 3) := sa_sliceEnergy_continuousOn (hV j)
  have hgint (j : Fin 3) : IntegrableOn (fun t => gradNormSq (V j t)) (Set.Ioo (0 : ℝ) 1) :=
    ((hgcont j).integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hsum_int : IntegrableOn (fun t => ∑ j, c j * gradNormSq (V j t)) (Set.Ioo (0 : ℝ) 1) :=
    integrable_finsetSum _ fun j _ => (hgint j).const_mul (c j)
  -- slice comparison
  have hslice : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      gradNormSq (F t) ≤ ∑ j, c j * gradNormSq (V j t) := by
    intro t ht
    have hFi : IntegrableOn (fun x => vecNormSq (F t x)) unitCube :=
      LeftToShow.integrableOn_unitCube_of_continuous
        (LeftToShow.continuous_vecNormSq_two.comp (hFc t ht))
    have hVi (j : Fin 3) : IntegrableOn (fun x => c j * vecNormSq (V j t x)) unitCube :=
      (sa_slice_integrableOn (hV j) (Set.Ioo_subset_Icc_self ht)).const_mul (c j)
    calc gradNormSq (F t) ≤ ∫ x in unitCube, ∑ j, c j * vecNormSq (V j t x) := by
          unfold gradNormSq
          exact integral_mono hFi (integrable_finsetSum _ fun j _ => hVi j) (hpt t ht)
      _ = ∑ j, c j * gradNormSq (V j t) := by
          rw [integral_finsetSum _ fun j _ => hVi j]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_const_mul]
          rfl
  have hnn : ∀ t, 0 ≤ ∑ j, c j * gradNormSq (V j t) := fun t =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (sa_gradNormSq_nonneg _)
  have hint : ∫ t in Set.Ioo (0 : ℝ) 1, ∑ j, c j * gradNormSq (V j t) =
      ∑ j, c j * spaceTimeGradNormSq (V j) := by
    rw [integral_finsetSum _ fun j _ => (hgint j).const_mul (c j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, sa_spaceTime_eq_integral (hV j)]
  have hS_nn : 0 ≤ ∑ j, c j * spaceTimeGradNormSq (V j) := by
    rw [← hint]
    exact integral_nonneg fun t => hnn t
  have hlin : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (gradNormSq (F t))) ^ 2) ≤
      ENNReal.ofReal (∑ j, c j * spaceTimeGradNormSq (V j)) := by
    calc _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (gradNormSq (F t)) := by
          refine lintegral_congr fun t => ?_
          exact sa_lintegrand_eq (F t)
      _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (∑ j, c j * gradNormSq (V j t)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          exact ENNReal.ofReal_le_ofReal (hslice t ht)
      _ = ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, ∑ j, c j * gradNormSq (V j t)) :=
          (ofReal_integral_eq_lintegral_ofReal hsum_int (ae_of_all _ hnn)).symm
      _ = _ := by rw [hint]
  unfold saTimeL2
  calc _ ≤ (ENNReal.ofReal (∑ j, c j * spaceTimeGradNormSq (V j))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hlin (by norm_num)
    _ = ENNReal.ofReal ((∑ j, c j * spaceTimeGradNormSq (V j)) ^ (1 / 2 : ℝ)) :=
        (ENNReal.ofReal_rpow_of_nonneg hS_nn (by norm_num : (0 : ℝ) ≤ 1 / 2))
    _ = _ := by rw [← Real.sqrt_eq_rpow]

theorem sa_spaceTimeGradNormSq_nonneg (V : ℝ → Vec 2 → Vec 2) : 0 ≤ spaceTimeGradNormSq V := by
  unfold spaceTimeGradNormSq
  exact integral_nonneg fun p => vecNormSq_nonneg _

/-- **Three-field form** of the space-time transfer. -/
theorem saTimeL2_le_of_pointwise {F V₀ V₁ V₂ : ℝ → Vec 2 → Vec 2} {k₀ k₁ k₂ : ℝ}
    (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (h₀ : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V₀ p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    (h₁ : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V₁ p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    (h₂ : ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V₂ p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    (hFc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Continuous (F t))
    (hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x, vecNormSq (F t x) ≤
      k₀ ^ 2 * vecNormSq (V₀ t x) + k₁ ^ 2 * vecNormSq (V₁ t x) +
        k₂ ^ 2 * vecNormSq (V₂ t x)) :
    saTimeL2 F ≤ ENNReal.ofReal (k₀ * Real.sqrt (spaceTimeGradNormSq V₀) +
      k₁ * Real.sqrt (spaceTimeGradNormSq V₁) + k₂ * Real.sqrt (spaceTimeGradNormSq V₂)) := by
  have hmain := saTimeL2_le (F := F) (V := ![V₀, V₁, V₂]) (c := ![k₀ ^ 2, k₁ ^ 2, k₂ ^ 2])
    (by intro j; fin_cases j <;> simp only [Fin.reduceFinMk, Matrix.cons_val] <;> positivity)
    (by intro j i; fin_cases j <;> simp [h₀ i, h₁ i, h₂ i]) hFc
    (by
      intro t ht x
      simpa [Fin.sum_univ_three] using hpt t ht x)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have e0 := sa_spaceTimeGradNormSq_nonneg V₀
  have e1 := sa_spaceTimeGradNormSq_nonneg V₁
  have e2 := sa_spaceTimeGradNormSq_nonneg V₂
  have q0 := Real.sq_sqrt e0
  have q1 := Real.sq_sqrt e1
  have q2 := Real.sq_sqrt e2
  have p0 := Real.sqrt_nonneg (spaceTimeGradNormSq V₀)
  have p1 := Real.sqrt_nonneg (spaceTimeGradNormSq V₁)
  have p2 := Real.sqrt_nonneg (spaceTimeGradNormSq V₂)
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have r0 : k₀ ^ 2 * spaceTimeGradNormSq V₀ = (k₀ * Real.sqrt (spaceTimeGradNormSq V₀)) ^ 2 := by
    rw [mul_pow, q0]
  have r1 : k₁ ^ 2 * spaceTimeGradNormSq V₁ = (k₁ * Real.sqrt (spaceTimeGradNormSq V₁)) ^ 2 := by
    rw [mul_pow, q1]
  have r2 : k₂ ^ 2 * spaceTimeGradNormSq V₂ = (k₂ * Real.sqrt (spaceTimeGradNormSq V₂)) ^ 2 := by
    rw [mul_pow, q2]
  rw [r0, r1, r2]
  nlinarith [mul_nonneg (mul_nonneg hk₀ p0) (mul_nonneg hk₁ p1),
    mul_nonneg (mul_nonneg hk₀ p0) (mul_nonneg hk₂ p2),
    mul_nonneg (mul_nonneg hk₁ p1) (mul_nonneg hk₂ p2)]

end AVenhance.Infra.Section5.Contracts
end
