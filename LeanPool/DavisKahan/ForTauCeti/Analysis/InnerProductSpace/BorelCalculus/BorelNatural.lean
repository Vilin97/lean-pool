/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagMeasureNatural
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.CyclicDecomposition

/-!
# The bounded Borel calculus is natural under a unitary intertwiner

If a unitary `e` intertwines two normal operators, it intertwines their bounded **Borel**
calculi, not just their continuous ones:

```text
e (f(a) x) = f(b) (e x)   for every bounded Borel `f : ℂ → ℂ`.
```

No monotone-class induction is needed.  The Borel calculus is *defined* by the polarised
diagonal integrals (`pair`), the diagonal measures transport along the unitary by
`map_val_diagMeasure_eq_of_intertwines`, and that is the whole proof: the matrix elements of the
two sides are the same four integrals.

Two points of care, both about types rather than mathematics:

* The symbols of the two calculi live on `spectrum ℂ a` and `spectrum ℂ b`, which are different
  types even though the sets are equal.  Naturality is therefore stated for symbols of the form
  `g ∘ (↑)` with `g : ℂ → ℂ`, and `exists_comp_val_eq` shows this loses nothing: every bounded
  Borel symbol on the spectrum extends to `ℂ` by zero, the spectrum being closed.
* Nothing here compares the spectra of `a` and `b`.  The extension trick quietly sidesteps the
  question, which is why the statement needs no spectral mapping input at all.

On top of naturality, this module transports the objects the uniqueness argument measures:
spectral projections of Borel subsets of `ℂ` (`specProjC`), cyclic subspaces, and the property
of being generated over the calculus by `m` vectors cut to a spectral subset
(`SpectralGeneratedLE`).  That last invariant is the pivot of the level-set half of
Hahn--Hellinger: it transfers along unitaries by this module, and the multiplication model
computes it by counting slices.

## Main results

* `TauCeti.BorelCalculus.exists_comp_val_eq`: every bounded Borel symbol on the spectrum is the
  restriction of a bounded Borel function on `ℂ`.
* `TauCeti.BorelCalculus.borelCalculus_comp_val_of_intertwines`: **naturality of the Borel
  calculus.**
* `TauCeti.BorelCalculus.specProjC` and `specProjC_apply_of_intertwines`: spectral projections
  of Borel subsets of `ℂ`, and their transport.
* `TauCeti.BorelCalculus.apply_mem_cyclicSubspace_of_intertwines`: cyclic subspaces transport.
* `TauCeti.BorelCalculus.SpectralGeneratedLE` and `spectralGeneratedLE_of_intertwines`: **the
  generator-count invariant, and its unitary invariance.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open scoped InnerProductSpace

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {a : H →L[ℂ] H} {b : K →L[ℂ] K}

section Symbols

omit [CompleteSpace H] in
/-- A bounded measurable function on `ℂ`, restricted to the spectrum, is an admissible symbol
for the Borel calculus. -/
theorem isBddMeasurable_comp_val {g : ℂ → ℂ} (hgm : Measurable g) {C : ℝ}
    (hgC : ∀ z, ‖g z‖ ≤ C) :
    IsBddMeasurable (a := a) fun w => g (w : ℂ) :=
  ⟨hgm.comp measurable_subtype_coe,
    ⟨|C|, abs_nonneg C, fun w => (hgC (w : ℂ)).trans (le_abs_self C)⟩⟩

/-- **Every bounded Borel symbol on the spectrum extends to `ℂ`**, keeping its bound: extend by
zero, the spectrum being a closed -- hence measurable -- set.  This is what lets naturality be
stated for symbols pulled back from `ℂ` without losing any generality. -/
theorem exists_comp_val_eq {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) :
    ∃ g : ℂ → ℂ, Measurable g ∧ (∀ z, ‖g z‖ ≤ hf.chooseBound) ∧
      ∀ w : spectrum ℂ a, f w = g (w : ℂ) := by
  have hmeas : MeasurableSet (spectrum ℂ a) := (spectrum.isCompact a).isClosed.measurableSet
  have hemb : MeasurableEmbedding ((↑) : spectrum ℂ a → ℂ) :=
    MeasurableEmbedding.subtype_coe hmeas
  refine ⟨Function.extend Subtype.val f fun _ => 0,
    hemb.measurable_extend hf.measurable measurable_const, ?_, ?_⟩
  · intro z
    by_cases hz : ∃ w : spectrum ℂ a, (w : ℂ) = z
    · obtain ⟨w, hw⟩ := hz
      rw [← hw, Subtype.val_injective.extend_apply]
      exact hf.norm_le_chooseBound w
    · rw [Function.extend_apply' _ _ _ hz]
      simpa using hf.chooseBound_nonneg
  · intro w
    rw [Subtype.val_injective.extend_apply]

end Symbols

section Naturality

/-- The diagonal integral of a symbol pulled back from `ℂ` is carried along by a unitary
intertwiner.  This is `map_val_diagMeasure_eq_of_intertwines`, converted from measures to
integrals. -/
theorem integral_comp_val_diagMeasure_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) {g : ℂ → ℂ} (hgm : Measurable g) (ξ : H) :
    ∫ w, g (w : ℂ) ∂(diagMeasure (isStarNormal_of_intertwines ha e he) (e ξ))
      = ∫ w, g (w : ℂ) ∂(diagMeasure ha ξ) := by
  have hb : IsStarNormal b := isStarNormal_of_intertwines ha e he
  have h1 := integral_map (μ := diagMeasure hb (e ξ)) (φ := (Subtype.val : spectrum ℂ b → ℂ))
    measurable_subtype_coe.aemeasurable (f := g) hgm.aestronglyMeasurable
  have h2 := integral_map (μ := diagMeasure ha ξ) (φ := (Subtype.val : spectrum ℂ a → ℂ))
    measurable_subtype_coe.aemeasurable (f := g) hgm.aestronglyMeasurable
  rw [← h1, ← h2, map_val_diagMeasure_eq_of_intertwines ha e he ξ]

/-- The polarised diagonal integrals of a symbol pulled back from `ℂ` are carried along by a
unitary intertwiner. -/
theorem pair_comp_val_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) {g : ℂ → ℂ} (hgm : Measurable g) (ψ ξ : H) :
    pair (isStarNormal_of_intertwines ha e he) (fun w => g (w : ℂ)) (e ψ) (e ξ)
      = pair ha (fun w => g (w : ℂ)) ψ ξ := by
  rw [pair_def, pair_def, ← map_smul e, ← map_add e, ← map_add e, ← map_sub e, ← map_sub e]
  rw [integral_comp_val_diagMeasure_of_intertwines ha e he hgm (ξ + ψ),
    integral_comp_val_diagMeasure_of_intertwines ha e he hgm (ξ + Complex.I • ψ),
    integral_comp_val_diagMeasure_of_intertwines ha e he hgm (ξ - ψ),
    integral_comp_val_diagMeasure_of_intertwines ha e he hgm (ξ - Complex.I • ψ)]

/-- **The bounded Borel calculus is natural under a unitary intertwiner.**  Stated for symbols
pulled back from `ℂ`, which `exists_comp_val_eq` shows is no restriction. -/
theorem borelCalculus_comp_val_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) {g : ℂ → ℂ} (hgm : Measurable g) {C : ℝ}
    (hgC : ∀ z, ‖g z‖ ≤ C) (ξ : H) :
    e (borelCalculus ha (isBddMeasurable_comp_val hgm hgC) ξ)
      = borelCalculus (isStarNormal_of_intertwines ha e he)
          (isBddMeasurable_comp_val hgm hgC) (e ξ) := by
  have hb : IsStarNormal b := isStarNormal_of_intertwines ha e he
  refine ext_inner_left ℂ fun χ => ?_
  calc ⟪χ, e (borelCalculus ha (isBddMeasurable_comp_val hgm hgC) ξ)⟫_ℂ
      = ⟪e (e.symm χ), e (borelCalculus ha (isBddMeasurable_comp_val hgm hgC) ξ)⟫_ℂ := by
        rw [e.apply_symm_apply]
    _ = ⟪e.symm χ, borelCalculus ha (isBddMeasurable_comp_val hgm hgC) ξ⟫_ℂ :=
        e.inner_map_map _ _
    _ = pair ha (fun w => g (w : ℂ)) (e.symm χ) ξ :=
        inner_borelCalculus ha (isBddMeasurable_comp_val hgm hgC) _ ξ
    _ = pair hb (fun w => g (w : ℂ)) (e (e.symm χ)) (e ξ) :=
        (pair_comp_val_of_intertwines ha e he hgm (e.symm χ) ξ).symm
    _ = pair hb (fun w => g (w : ℂ)) χ (e ξ) := by rw [e.apply_symm_apply]
    _ = ⟪χ, borelCalculus (isStarNormal_of_intertwines ha e he)
          (isBddMeasurable_comp_val hgm hgC) (e ξ)⟫_ℂ :=
        (inner_borelCalculus hb (isBddMeasurable_comp_val hgm hgC) χ (e ξ)).symm

end Naturality

section SpectralProjection

/-- The constant-one indicator of a Borel subset of `ℂ` is measurable. -/
theorem measurable_indicator_one {S : Set ℂ} (hS : MeasurableSet S) :
    Measurable (S.indicator fun _ => (1 : ℂ)) :=
  measurable_const.indicator hS

/-- The constant-one indicator is bounded by one. -/
theorem norm_indicator_one_le {S : Set ℂ} (z : ℂ) :
    ‖S.indicator (fun _ => (1 : ℂ)) z‖ ≤ 1 := by
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz]
    simp
  · rw [Set.indicator_of_notMem hz]
    simp

/-- **The spectral projection of a Borel subset of `ℂ`**: the Borel calculus of its indicator.

The set lives in `ℂ`, not in the spectrum subtype, precisely so that the *same* set can be fed
to the spectral projections of two different operators -- which is what every transport
statement of the uniqueness argument does. -/
noncomputable def specProjC (ha : IsStarNormal a) {S : Set ℂ} (hS : MeasurableSet S) :
    H →L[ℂ] H :=
  borelCalculus ha (isBddMeasurable_comp_val (measurable_indicator_one hS) norm_indicator_one_le)

/-- The spectral projection, unfolded.  Stated so that consumers can rewrite with it without
the definition having to be exposed. -/
theorem specProjC_def (ha : IsStarNormal a) {S : Set ℂ} (hS : MeasurableSet S) :
    specProjC ha hS = borelCalculus ha
      (isBddMeasurable_comp_val (measurable_indicator_one hS) norm_indicator_one_le) := (rfl)

/-- **Spectral projections are natural under a unitary intertwiner.** -/
theorem specProjC_apply_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) {S : Set ℂ} (hS : MeasurableSet S) (x : H) :
    e (specProjC ha hS x) = specProjC (isStarNormal_of_intertwines ha e he) hS (e x) :=
  borelCalculus_comp_val_of_intertwines ha e he (measurable_indicator_one hS)
    norm_indicator_one_le x

end SpectralProjection

section CyclicTransport

/-- **Cyclic subspaces transport along a unitary intertwiner.**  The orbit of `ξ` is carried
into the orbit of `e ξ`: every symbol of `a` extends to `ℂ`, and pulled-back symbols obey
naturality. -/
theorem apply_mem_cyclicSubspace_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) {ξ x : H} (hx : x ∈ cyclicSubspace ha ξ) :
    e x ∈ cyclicSubspace (isStarNormal_of_intertwines ha e he) (e ξ) := by
  have hb : IsStarNormal b := isStarNormal_of_intertwines ha e he
  have hle : cyclicSubspace ha ξ ≤ Submodule.comap (e.toLinearEquiv : H →ₗ[ℂ] K)
      (cyclicSubspace hb (e ξ)) := by
    refine cyclicSubspace_le ha ?_ fun f hf => ?_
    · exact (isClosed_cyclicSubspace hb (e ξ)).preimage e.continuous
    · obtain ⟨g, hgm, hgC, hgeq⟩ := exists_comp_val_eq hf
      have hfeq : f = fun w : spectrum ℂ a => g (w : ℂ) := funext hgeq
      subst hfeq
      have hmem := borelCalculus_apply_mem_cyclicSubspace hb
        (isBddMeasurable_comp_val (a := b) hgm hgC) (e ξ)
      rw [← borelCalculus_comp_val_of_intertwines ha e he hgm hgC ξ] at hmem
      exact hmem
  exact hle hx

/-- The closed span of finitely (or arbitrarily) many cyclic subspaces transports along a
unitary intertwiner. -/
theorem apply_mem_closure_iSup_cyclicSubspace_of_intertwines (ha : IsStarNormal a)
    (e : H ≃ₗᵢ[ℂ] K) (he : ∀ x, e (a x) = b (e x)) {ι : Type*} (v : ι → H) {x : H}
    (hx : x ∈ (⨆ i, cyclicSubspace ha (v i)).topologicalClosure) :
    e x ∈ (⨆ i, cyclicSubspace (isStarNormal_of_intertwines ha e he)
      (e (v i))).topologicalClosure := by
  have hb : IsStarNormal b := isStarNormal_of_intertwines ha e he
  have hle : (⨆ i, cyclicSubspace ha (v i)).topologicalClosure ≤
      Submodule.comap (e.toLinearEquiv : H →ₗ[ℂ] K)
        ((⨆ i, cyclicSubspace hb (e (v i))).topologicalClosure) := by
    refine Submodule.topologicalClosure_minimal _ (iSup_le fun i y hy => ?_) ?_
    · have h1 := apply_mem_cyclicSubspace_of_intertwines ha e he hy
      exact (le_trans (le_iSup (fun i => cyclicSubspace hb (e (v i))) i)
        (Submodule.le_topologicalClosure _)) h1
    · exact (Submodule.isClosed_topologicalClosure _).preimage e.continuous
  exact hle hx

end CyclicTransport

section GeneratedLE

/-- **The generator-count invariant**: the range of the spectral projection of `S` is contained
in the closed calculus-span of `m` vectors.

This is "the part of the operator over `S` is generated by at most `m` vectors", and it is the
quantity the level-set half of Hahn--Hellinger compares between two presentations: a unitary
preserves it (`spectralGeneratedLE_of_intertwines`), and on the multiplication model it counts
the slices that meet `S`. -/
def SpectralGeneratedLE (ha : IsStarNormal a) {S : Set ℂ} (hS : MeasurableSet S)
    (m : ℕ) : Prop :=
  ∃ v : Fin m → H, ∀ x : H,
    specProjC ha hS x ∈ (⨆ i, cyclicSubspace ha (v i)).topologicalClosure

/-- Elimination form of `SpectralGeneratedLE`, so call sites need not unfold the definition. -/
theorem SpectralGeneratedLE.exists_generators {ha : IsStarNormal a} {S : Set ℂ}
    {hS : MeasurableSet S} {m : ℕ} (h : SpectralGeneratedLE ha hS m) :
    ∃ v : Fin m → H, ∀ x : H,
      specProjC ha hS x ∈ (⨆ i, cyclicSubspace ha (v i)).topologicalClosure := h

/-- Introduction form of `SpectralGeneratedLE`. -/
theorem spectralGeneratedLE_of_generators {ha : IsStarNormal a} {S : Set ℂ}
    {hS : MeasurableSet S} {m : ℕ} (v : Fin m → H)
    (hv : ∀ x : H, specProjC ha hS x ∈ (⨆ i, cyclicSubspace ha (v i)).topologicalClosure) :
    SpectralGeneratedLE ha hS m := ⟨v, hv⟩

/-- **The generator count is a unitary invariant.**  If the compression of `a` to the spectral
subset `S` is generated by `m` vectors, so is that of any unitarily conjugate operator. -/
theorem spectralGeneratedLE_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) {S : Set ℂ} {hS : MeasurableSet S} {m : ℕ}
    (h : SpectralGeneratedLE ha hS m) :
    SpectralGeneratedLE (isStarNormal_of_intertwines ha e he) hS m := by
  obtain ⟨v, hv⟩ := h
  refine ⟨fun i => e (v i), fun y => ?_⟩
  have hy := hv (e.symm y)
  have hmem := apply_mem_closure_iSup_cyclicSubspace_of_intertwines ha e he v hy
  rw [specProjC_apply_of_intertwines ha e he hS, e.apply_symm_apply] at hmem
  exact hmem

end GeneratedLE

end BorelCalculus
end TauCeti
