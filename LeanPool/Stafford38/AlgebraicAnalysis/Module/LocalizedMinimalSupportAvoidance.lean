/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Support


/-!
# Transport of minimal-prime support avoidance through localization

For a finite module, localization commutes with its annihilator.  The reverse
inclusion uses a finite generating set to clear all denominators at once.
Minimal-prime avoidance then follows from the ordinary minimal-prime
correspondence for a localization.
-/

@[expose] public section

namespace AlgebraicAnalysis.LocalizedMinimalSupportAvoidance

noncomputable section

variable {C E : Type*} [CommRing C] [AddCommGroup E] [Module C E]

/-- The annihilator of a finite module commutes with localization. -/
theorem annihilator_localizedModule
    [Module.Finite C E] (S : Submonoid C) :
    Module.annihilator (Localization S) (LocalizedModule S E) =
      Ideal.map (algebraMap C (Localization S)) (Module.annihilator C E) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨⟨c, d⟩, rfl⟩ := IsLocalization.mk'_surjective S z
    obtain ⟨gens, hgens⟩ := (inferInstance : Module.Finite C E)
    have hclear : ∀ e ∈ gens, ∃ u : S, u • (c • e) = 0 := by
      intro e he
      have hzero :
          IsLocalization.mk' (Localization S) c d • LocalizedModule.mk e 1 = 0 :=
        Module.mem_annihilator.mp hz _
      rw [IsLocalizedModule.mk_eq_mk'] at hzero
      rw [IsLocalizedModule.mk'_smul_mk', IsLocalizedModule.mk'_eq_zero'] at hzero
      exact hzero
    choose u hu using hclear
    let t : S := gens.attach.prod fun e => u e e.property
    have htc : (t : C) * c ∈ Module.annihilator C E := by
      rw [Module.mem_annihilator]
      intro e
      refine Submodule.span_induction ?_ (smul_zero _) ?_ ?_
        (show e ∈ Submodule.span C (gens : Set E) by rw [hgens]; trivial)
      · intro e he
        obtain ⟨v, hv⟩ := Finset.dvd_prod_of_mem
          (fun a : gens => u a a.property) (Finset.mem_attach gens ⟨e, he⟩)
        have hue : (((u e he : S) : C) * c) • e = 0 := by
          simpa only [mul_smul, Submonoid.smul_def] using hu e he
        change (((t : S) : C) * c) • e = 0
        rw [show t = gens.attach.prod (fun a => u a a.property) by rfl, hv,
          Submonoid.coe_mul, mul_comm ((u e he : S) : C) (v : C),
          mul_assoc, mul_smul, hue, smul_zero]
      · intro e₁ e₂ _ _ he₁ he₂
        rw [smul_add, he₁, he₂, zero_add]
      · intro a e _ he
        rw [smul_comm, he, smul_zero]
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨t, t.property, htc⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro y
    induction y using LocalizedModule.induction_on with
    | _ e d =>
      rw [IsLocalizedModule.mk_eq_mk']
      rw [← IsLocalization.mk'_one (M := S), IsLocalizedModule.mk'_smul_mk',
        Module.mem_annihilator.mp hc e]
      simp

/-- Minimal-prime avoidance survives localization. -/
theorem localized_minimalPrime_avoids
     [Module.Finite C E]
    (S : Submonoid C) (x : C)
    (havoid : ∀ p ∈ (Module.annihilator C E).minimalPrimes, x ∉ p) :
    ∀ Q ∈ (Module.annihilator (Localization S)
        (LocalizedModule S E)).minimalPrimes,
      algebraMap C (Localization S) x ∉ Q := by
  intro Q hQ
  have hQmap : Q ∈
      (Ideal.map (algebraMap C (Localization S))
        (Module.annihilator C E)).minimalPrimes := by
    rw [← annihilator_localizedModule S]
    exact hQ
  have hQunder :
      Ideal.under C Q ∈ (Module.annihilator C E).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map S
      (Localization S) (Module.annihilator C E)] at hQmap
    exact hQmap
  intro hxQ
  exact havoid (Ideal.under C Q) hQunder hxQ

end

end AlgebraicAnalysis.LocalizedMinimalSupportAvoidance
