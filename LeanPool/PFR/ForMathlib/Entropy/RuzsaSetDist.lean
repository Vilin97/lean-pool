/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import LeanPool.PFR.ForMathlib.Entropy.RuzsaDist

/-!
# Ruzsa distance for finite sets
-/

public section

open scoped ZhangYeungPFR


open MeasureTheory Pointwise Real

namespace ProbabilityTheory

variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

/-- The Ruzsa distance between two subsets `A`, `B` of a group `G` is defined to be the Ruzsa
distance between their uniform probability distributions. Is only intended for use when `A`, `B` are
finite and non-empty. -/
@[expose]
public
noncomputable def setRuzsaDist (A B : Set G) : ℝ := Kernel.rdistm (uniformOn A) (uniformOn B)

@[inherit_doc setRuzsaDist]
notation3:max "dᵤ[" A " # " B "]" => setRuzsaDist A B

/-- Relating Ruzsa distance between sets to Ruzsa distance between random variables -/
public
lemma setRuzsaDist_eq_rdist {A B : Set G} [Finite A] [Finite B]
    {Ω Ω' : Type*} [mΩ : MeasureSpace Ω] [mΩ' : MeasureSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {UA : Ω → G} {UB : Ω' → G} (hUA : IsUniform A UA μ) (hUB : IsUniform B UB μ')
    (hUA_mes : Measurable UA) (hUB_mes : Measurable UB) :
    dᵤ[A # B] = d[UA; μ # UB; μ'] := by
  rw [rdist_eq_rdistm, setRuzsaDist, (isUniform_iff_map_eq_uniformOn μ hUA_mes).mp hUA,
    (isUniform_iff_map_eq_uniformOn μ' hUB_mes).mp hUB]

/-- Ruzsa distance between sets is nonnegative. -/
public
lemma setRuzsaDist_nonneg (A B : Set G) [hA : Finite A] [hB : Finite B] [Nonempty A] [Nonempty B] :
    0 ≤ dᵤ[A # B] := by
  obtain ⟨Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, UA_hfin⟩ :=
    exists_isUniform_measureSpace' A hA .of_subtype
  obtain ⟨Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, UB_hfin⟩ :=
    exists_isUniform_measureSpace' B hB .of_subtype
  rw [setRuzsaDist_eq_rdist hUA_unif hUB_unif hUA_mes hUB_mes]
  exact rdist_nonneg hUA_mes hUB_mes





/-- Ruzsa distance between sets is translation invariant. -/
public
lemma setRuzsaDist_add_const (A B : Set G) [hA : Finite A] [hB : Finite B] [Nonempty A] [Nonempty B]
    (c c' : G) : dᵤ[A + {c} # B + {c'}] = dᵤ[A # B] := by
  obtain ⟨Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, hUA_fin ⟩ :=
    exists_isUniform_measureSpace' A hA .of_subtype
  obtain ⟨Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, hUB_fin ⟩ :=
    exists_isUniform_measureSpace' B hB .of_subtype
  rw [setRuzsaDist_eq_rdist hUA_unif hUB_unif hUA_mes hUB_mes,
    ← rdist_add_const' c c' hUA_mes hUB_mes]
  classical
  have : Finite (A + ({c} : Set G)) := Set.Finite.add hA (Set.finite_singleton c)
  have : Finite (B + ({c'} : Set G)) := Set.Finite.add hB (Set.finite_singleton c')
  convert setRuzsaDist_eq_rdist (A := A+{c}) (B := B+{c'}) (μ := (volume : Measure Ω))
      (μ' := (volume : Measure Ω')) ?_ ?_ ?_ ?_
  · convert! (A.toFinite.coe_toFinset.symm ▸ hUA_unif).comp (add_left_injective c) using 1
    simp
  · convert! (B.toFinite.coe_toFinset.symm ▸ hUB_unif).comp (add_left_injective c') using 1
    simp
  · fun_prop
  · fun_prop

/-- Ruzsa distance between sets is preserved by injective homomorphisms. -/
public
lemma setRuzsaDist_of_inj (A B : Set G) [hA : Finite A] [hB : Finite B] [Nonempty A] [Nonempty B]
    {H : Type*} [hH : MeasurableSpace H] [MeasurableSingletonClass H] [AddCommGroup H]
    [Countable H] {φ : G →+ H} (hφ : Function.Injective φ) :
    dᵤ[φ '' A # φ '' B] = dᵤ[A # B] := by
  obtain ⟨Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, - ⟩ :=
    exists_isUniform_measureSpace' A hA .of_subtype
  obtain ⟨Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, - ⟩ :=
    exists_isUniform_measureSpace' B hB .of_subtype
  rw [setRuzsaDist_eq_rdist hUA_unif hUB_unif hUA_mes hUB_mes, ← rdist_of_inj hUA_mes hUB_mes φ hφ]
  classical
  convert setRuzsaDist_eq_rdist (A := φ '' A) (B := φ '' B) (μ := (volume : Measure Ω))
      (μ' := (volume : Measure Ω')) ?_ ?_ ?_ ?_
  · convert IsUniform.comp (A.toFinite.coe_toFinset.symm ▸ hUA_unif) hφ using 1
    ext x; simp
  · convert IsUniform.comp (B.toFinite.coe_toFinset.symm ▸ hUB_unif) hφ using 1
    ext x; simp
  · fun_prop
  · fun_prop

/-- Ruzsa distance between sets is controlled by the doubling constant. -/
public
lemma setRuzsaDist_le (A B : Set G) [h'A : Finite A] [h'B : Finite B]
    (hA : A.Nonempty) (hB : B.Nonempty) :
    dᵤ[A # B] ≤ log (Nat.card (A-B)) - log (Nat.card A) / 2 - log (Nat.card B) / 2 := by
  have : Finite (A - B) := Set.Finite.sub h'A h'B
  have := hA.to_subtype
  have := hB.to_subtype
  simp_rw [setRuzsaDist, Kernel.rdistm, ProbabilityTheory.entropy_of_uniformOn]
  gcongr
  convert measureEntropy_le_card_aux (A-B).toFinite.toFinset ?_
  · rw [Nat.card_coe_set_eq]
    exact Set.ncard_eq_toFinset_card (A - B)
  · exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable measurable_sub)
  rw [Measure.map_apply measurable_sub .of_discrete]
  apply measure_mono_null (t := (Aᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Bᶜ))
  · intro (x, y)
    contrapose!
    aesop (add safe Set.sub_mem_sub, simp not_or)
  apply measure_union_null
  all_goals simp [uniformOn_apply ‹Finite A›, uniformOn_apply ‹Finite B›]

end ProbabilityTheory
