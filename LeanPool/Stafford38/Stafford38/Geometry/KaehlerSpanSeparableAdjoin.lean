/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.SeparableResidueDerivationExtension
public import LeanPool.Stafford38.Stafford38.Geometry.KaehlerVisibleDerivationFrame


/-!
# Kähler span after a separable residue-field extension

Let `k → E → K` be a tower of fields.  If a family `q : ι → E` generates
`E` as an intermediate field over `k`, then its universal differentials span
`Ω[E⁄k]`.  If `K/E` is formally étale, the images of the same differentials
span `Ω[K⁄k]`; separability supplies the formally-étale instance for fields.

For a finite generating family, this also supplies the finite-dimensional
instance needed by `KaehlerVisibleDerivationFrame` and hence a dual visible
derivation frame over `K`.

This file does not construct a projective boundary divisor, prove that the
residue coordinates at a chosen divisor generate an intermediate field, or
produce any completed boundary chart.  Those are separate geometric inputs.
-/

@[expose] public section

namespace Stafford38.Geometry.KaehlerSpanSeparableAdjoin

open TensorProduct

noncomputable section

universe u v

variable {k E K : Type u} [Field k] [Field E] [Field K]
variable [Algebra k E] [Algebra k K] [Algebra E K]
variable [IsScalarTower k E K]

/-- A family that generates a field over the ground field has universal
differentials spanning the full Kähler module. -/
theorem kaehler_span_of_intermediateField_adjoin_eq_top
    {ι : Type v} (q : ι → E)
    (hgen : IntermediateField.adjoin k (Set.range q) = ⊤) :
    Submodule.span E
      (Set.range fun i ↦ KaehlerDifferential.D k E (q i)) = ⊤ := by
  let W : Submodule E (Ω[E⁄k]) :=
    Submodule.span E (Set.range fun i ↦ KaehlerDifferential.D k E (q i))
  have hD (x : E) : KaehlerDifferential.D k E x ∈ W := by
    have hx : x ∈ IntermediateField.adjoin k (Set.range q) := by
      rw [hgen]
      trivial
    apply IntermediateField.adjoin_induction k
        (p := fun y _ ↦ KaehlerDifferential.D k E y ∈ W)
    · intro y hy
      change y ∈ Set.range q at hy
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    · intro a
      simp
    · intro a b _ _ ha hb
      simpa only [map_add] using W.add_mem ha hb
    · intro a _ ha
      rw [Derivation.leibniz_inv]
      exact W.smul_mem _ ha
    · intro a b _ _ ha hb
      rw [Derivation.leibniz]
      exact W.add_mem (W.smul_mem _ hb) (W.smul_mem _ ha)
    · exact hx
  apply top_unique
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hD x

/-- Formally-étale base change transports a field-generating differential
family to a spanning family over the extension field. -/
theorem kaehler_span_of_formallyEtale_adjoin_eq_top
    [Algebra.FormallyEtale E K]
    {ι : Type v} (q : ι → E)
    (hgen : IntermediateField.adjoin k (Set.range q) = ⊤) :
    Submodule.span K
      (Set.range fun i ↦
        KaehlerDifferential.D k K (algebraMap E K (q i))) = ⊤ := by
  let W : Submodule K (Ω[K⁄k]) :=
    Submodule.span K (Set.range fun i ↦
      KaehlerDifferential.D k K (algebraMap E K (q i)))
  have hE : Submodule.span E
      (Set.range fun i ↦ KaehlerDifferential.D k E (q i)) = ⊤ :=
    kaehler_span_of_intermediateField_adjoin_eq_top q hgen
  have hmap (w : Ω[E⁄k]) :
      KaehlerDifferential.map k k E K w ∈ W := by
    have hw : w ∈ Submodule.span E
        (Set.range fun i ↦ KaehlerDifferential.D k E (q i)) := by
      rw [hE]
      trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact W.zero_mem
    | add x y hx hy hx' hy' =>
        simpa only [map_add] using W.add_mem hx' hy'
    | smul a x hx hx' =>
        simpa only [LinearMap.map_smul_of_tower,
          IsScalarTower.algebraMap_smul] using
          W.smul_mem (algebraMap E K a) hx'
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k E K
  have he (y : K ⊗[E] Ω[E⁄k]) : e y ∈ W := by
    induction y using TensorProduct.inductionOn with
    | add x y hx hy =>
        simpa only [map_add] using W.add_mem hx hy
    | tmul a w =>
        rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
          KaehlerDifferential.mapBaseChange_tmul]
        exact W.smul_mem _ (hmap w)
  apply top_unique
  intro z _
  obtain ⟨y, rfl⟩ := e.surjective z
  exact he y

/-- The formally-étale span theorem specialized to a separable extension of
fields.  No finite-degree hypothesis is needed. -/
theorem kaehler_span_of_separable_adjoin_eq_top
    [Algebra.IsSeparable E K]
    {ι : Type v} (q : ι → E)
    (hgen : IntermediateField.adjoin k (Set.range q) = ⊤) :
    Submodule.span K
      (Set.range fun i ↦
        KaehlerDifferential.D k K (algebraMap E K (q i))) = ⊤ := by
  let : Algebra.FormallyEtale E K :=
    Algebra.FormallyEtale.of_isSeparable E K
  exact kaehler_span_of_formallyEtale_adjoin_eq_top q hgen

/-- A finite field-generating family gives a visible dual derivation frame
after separable extension. -/
theorem exists_visible_derivation_frame_of_finite_separable_adjoin
    [Algebra.IsSeparable E K]
    {ι : Type v} [Finite ι] (q : ι → E)
    (hgen : IntermediateField.adjoin k (Set.range q) = ⊤) :
    ∃ (rows : Fin (Module.finrank K (Ω[K⁄k])) ↪ ι)
      (D : Fin (Module.finrank K (Ω[K⁄k])) → Derivation k K K),
      ∀ i j, D j (algebraMap E K (q (rows i))) =
        if i = j then 1 else 0 := by
  classical
  let := Fintype.ofFinite ι
  have hspan := kaehler_span_of_separable_adjoin_eq_top
    (k := k) (E := E) (K := K) q hgen
  let : FiniteDimensional K (Ω[K⁄k]) := by
    let : FiniteDimensional K
        (Submodule.span K (Set.range fun i ↦
          KaehlerDifferential.D k K (algebraMap E K (q i)))) :=
      FiniteDimensional.span_of_finite K (Set.finite_range _)
    let : FiniteDimensional K (⊤ : Submodule K (Ω[K⁄k])) :=
      (LinearEquiv.ofEq _ _ hspan).finiteDimensional
    exact Submodule.topEquiv.finiteDimensional
  exact Geometry.KaehlerVisibleDerivationFrame.exists_visible_derivation_frame_of_kaehler_span
    (fun i ↦ algebraMap E K (q i)) hspan


end

end Stafford38.Geometry.KaehlerSpanSeparableAdjoin
