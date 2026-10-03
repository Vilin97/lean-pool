/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Local integrability from the data clauses alone

The data clauses of `def:sws` bound the fields on every local box `Ω' × J`.  A
compact subset of the space-time carrier always sits inside such a box
(`CKN.caccioppoli_localBox_of_compact_subset`), so each of those bounds
transfers to an arbitrary compact set, and that is the form in which the
integrability clauses of `def:sws` need them: they are all stated on the
closed support of a test function, which is compact.

Every statement here takes `CKN.IsSuitableWeakSolutionData` and not the full
class.  The same facts already exist in the tree stated with the full class -
`CKN.spatialGradientSq_integrableOn_compact` is the closest one - but a lemma
of that shape cannot be used while establishing the class's own integrability
clauses, since it would assume what is being proved.  The proofs below use
nothing beyond the data clauses.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- A measurable field whose squared extended norm has finite integral on a set
is square integrable there. -/
private theorem memLp_two_of_lintegral_enorm_sq_lt_top {E : Type}
    [NormedAddCommGroup E] {S : Set ParabolicPoint} {v : ParabolicPoint → E}
    (hv : AEStronglyMeasurable v (volume.restrict S))
    (hvlt : (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp v 2 (volume.restrict S) := by
  refine (memLp_two_iff_integrable_sq_norm hv).2 ?_
  have hvmeas : AEStronglyMeasurable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict S) := hv.norm.pow 2
  have hvfin : (∫⁻ z in S, ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ))) ≠ ⊤ := by
    refine ne_of_lt ?_
    refine lt_of_le_of_lt (le_of_eq ?_) hvlt
    refine lintegral_congr fun z => ?_
    calc
      ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ))
          = ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℝ)) := by
            norm_num [Real.rpow_natCast]
      _ = ENNReal.ofReal ‖v z‖ ^ (2 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)).symm
      _ = ‖v z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
  exact (lintegral_ofReal_ne_top_iff_integrable hvmeas
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hvfin

/-- A compact subset of the space-time carrier lies in a local box of the
carrier.  This is the geometric step behind every lemma in this file. -/
private theorem localBox_of_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    ∃ Ω' J, localBox Ω I Ω' J ∧ K ⊆ spaceTimeSet Ω' J :=
  caccioppoli_localBox_of_compact_subset hdata.isOpen_space hdata.isOpen_time
    hdata.ordConnected_time hK hKsub

/-- The velocity is square integrable on every compact subset of the carrier. -/
theorem velocity_memLp_two_on_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    MemLp u 2 (volume.restrict K) := by
  obtain ⟨Ω', J, hbox, hKbox⟩ := localBox_of_compact_of_data hdata hK hKsub
  have hbase : MemLp u 2 (volume.restrict (spaceTimeSet Ω' J)) :=
    memLp_two_of_lintegral_enorm_sq_lt_top (hdata.aestronglyMeasurable_velocity hbox)
      (lt_of_le_of_lt (lintegral_mono fun _ => le_add_right le_rfl)
        (hdata.energy_lintegral_lt_top hbox))
  exact hbase.mono_measure (Measure.restrict_mono hKbox le_rfl)

/-- The velocity gradient is square integrable on every compact subset of the
carrier. -/
theorem gradient_memLp_two_on_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    MemLp Du 2 (volume.restrict K) := by
  obtain ⟨Ω', J, hbox, hKbox⟩ := localBox_of_compact_of_data hdata hK hKsub
  have hbase : MemLp Du 2 (volume.restrict (spaceTimeSet Ω' J)) :=
    memLp_two_of_lintegral_enorm_sq_lt_top (hdata.aestronglyMeasurable_gradient hbox)
      (lt_of_le_of_lt (lintegral_mono fun _ => le_add_left le_rfl)
        (hdata.energy_lintegral_lt_top hbox))
  exact hbase.mono_measure (Measure.restrict_mono hKbox le_rfl)

/-- The pressure is `L^{3/2}` on every compact subset of the carrier. -/
theorem pressure_memLp_threeHalves_on_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict K) := by
  obtain ⟨Ω', J, hbox, hKbox⟩ := localBox_of_compact_of_data hdata hK hKsub
  exact (hdata.memLp_pressure hbox).mono_measure (Measure.restrict_mono hKbox le_rfl)

/-- The force is `L^q` on every compact subset of the carrier. -/
theorem force_memLp_on_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    MemLp f (ENNReal.ofReal q) (volume.restrict K) := by
  obtain ⟨Ω', J, hbox, hKbox⟩ := localBox_of_compact_of_data hdata hK hKsub
  exact (hdata.memLp_force hbox).mono_measure (Measure.restrict_mono hKbox le_rfl)

/-- The squared spatial-gradient density is bounded by nine times the squared
supremum norm of the gradient, in extended arithmetic. -/
private theorem ofReal_spatialGradientSq_le (z : ParabolicPoint) :
    ENNReal.ofReal (spatialGradientSq u Du z) ≤ 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
  have hterm : ∀ i : Fin 3, ∀ j : Fin 3, (Du z i j) ^ (2 : ℕ) ≤ ‖Du z‖ ^ (2 : ℕ) := by
    intro i j
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (le_trans (norm_le_pi_norm (Du z i) j) (norm_le_pi_norm (Du z) i)) 2
  have hsum : spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ (2 : ℕ) := by
    have hbound : spatialGradientSq u Du z ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ (2 : ℕ) := by
      unfold spatialGradientSq
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    calc
      spatialGradientSq u Du z ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ (2 : ℕ) := hbound
      _ = 9 * ‖Du z‖ ^ (2 : ℕ) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  calc
    ENNReal.ofReal (spatialGradientSq u Du z)
        ≤ ENNReal.ofReal (9 * ‖Du z‖ ^ (2 : ℕ)) := ENNReal.ofReal_le_ofReal hsum
    _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
        show ENNReal.ofReal (9 : ℝ) = 9 by norm_num]
      congr 1
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      norm_num [Real.rpow_natCast]

/-- The Dirichlet density of the velocity is integrable on every compact subset
of the carrier.  This is the data-clause form of
`CKN.spatialGradientSq_integrableOn_compact`. -/
theorem spatialGradientSq_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun z => spatialGradientSq u Du z) K volume := by
  obtain ⟨Ω', J, hbox, hKbox⟩ := localBox_of_compact_of_data hdata hK hKsub
  have hDu : AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) :=
    hdata.aestronglyMeasurable_gradient hbox
  have hmeas : AEStronglyMeasurable (fun z : ParabolicPoint => spatialGradientSq u Du z)
      (volume.restrict K) := by
    have hcont : Continuous
        (fun v : Fin 3 → Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ)) := by
      fun_prop
    exact (hcont.comp_aestronglyMeasurable hDu).mono_measure
      (Measure.restrict_mono hKbox le_rfl)
  have henergy : (∫⁻ z in K, ‖Du z‖ₑ ^ (2 : ℝ)) ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (hdata.energy_lintegral_lt_top hbox))
    calc
      (∫⁻ z in K, ‖Du z‖ₑ ^ (2 : ℝ))
          ≤ ∫⁻ z in K, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono fun _ => le_add_left le_rfl
      _ ≤ ∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono_set hKbox
  have hfin : (∫⁻ z in K, ENNReal.ofReal (spatialGradientSq u Du z)) ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono ofReal_spatialGradientSq_le) ?_)
    rw [lintegral_const_mul' 9 _ (by norm_num)]
    exact ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr henergy)
  refine (lintegral_ofReal_ne_top_iff_integrable hmeas ?_).mp hfin
  refine Filter.Eventually.of_forall fun z => ?_
  unfold spatialGradientSq
  positivity

end CKN
