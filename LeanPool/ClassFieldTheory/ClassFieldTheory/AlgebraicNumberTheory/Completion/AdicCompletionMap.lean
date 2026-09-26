/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
public import Mathlib.NumberTheory.RamificationInertia.Valuation
/-!
# The canonical map between adic completions

A finite place above a base finite place determines the continuous
extension of the number-field algebra map to their concrete adic
completions.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The canonical map between adic completions at a finite place and a
chosen place above it.  It is obtained by completing the algebra map
between the corresponding valued copies of the number fields. -/
noncomputable def finitePlaceAdicCompletionMap
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    w.adicCompletion K →+* W.1.adicCompletion L := by
  letI : W.1.asIdeal.LiesOver w.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  exact
    (HeightOneSpectrum.adicCompletion.equiv L W.1).symm.toRingHom.comp
      ((UniformSpace.Completion.mapRingHom
        (algebraMap
          (WithVal (w.valuation K))
          (WithVal (W.1.valuation L)))
        (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
          K L w W.1).continuous).comp
        (HeightOneSpectrum.adicCompletion.equiv K w).toRingHom)

/-- On the dense copy of the base field, the canonical map of adic
completions is the original field embedding. -/
theorem finitePlaceAdicCompletionMap_coe
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : K) :
    finitePlaceAdicCompletionMap K L w W
        (x : w.adicCompletion K) =
      (algebraMap K L x : W.1.adicCompletion L) := by
  let : W.1.asIdeal.LiesOver w.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  change
    HeightOneSpectrum.adicCompletion.ofCompletion
      (UniformSpace.Completion.mapRingHom
        (algebraMap
          (WithVal (w.valuation K))
          (WithVal (W.1.valuation L)))
        (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
          K L w W.1).continuous
        (algebraMap K (w.valuation K).Completion x)) =
      _
  congr 1
  change
    UniformSpace.Completion.mapRingHom
        (algebraMap
          (WithVal (w.valuation K))
          (WithVal (W.1.valuation L)))
        (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
          K L w W.1).continuous
        ((WithVal.equiv (w.valuation K)).symm x :
          (w.valuation K).Completion) =
      ((algebraMap
        (WithVal (w.valuation K))
        (WithVal (W.1.valuation L)))
        ((WithVal.equiv (w.valuation K)).symm x) :
          (W.1.valuation L).Completion)
  rw [UniformSpace.Completion.mapRingHom_coe]

/-- The canonical map of adic completions is compatible with the original
number-field tower. -/
theorem finitePlaceAdicCompletionMap_isScalarTower
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    letI : Algebra (w.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L w W).toAlgebra
    IsScalarTower K (w.adicCompletion K) (W.1.adicCompletion L) := by
  let : Algebra (w.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L w W).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change
    (algebraMap K (W.1.adicCompletion L)) x =
      finitePlaceAdicCompletionMap K L w W
        (x : w.adicCompletion K)
  rw [finitePlaceAdicCompletionMap_coe K L w W x]
  exact IsScalarTower.algebraMap_apply K L (W.1.adicCompletion L) x

/-- The canonical map between the two adic completions is continuous. -/
theorem finitePlaceAdicCompletionMap_continuous
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    Continuous (finitePlaceAdicCompletionMap K L w W) := by
  let : W.1.asIdeal.LiesOver w.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  unfold finitePlaceAdicCompletionMap
  exact
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L W.1).comp
      (UniformSpace.Completion.continuous_map.comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

/-- The canonical map on a finite-place adic completion induced by the
identity field extension is the identity map. -/
@[simp]
theorem finitePlaceAdicCompletionMap_self_apply
    (W : HeightOneSpectrum (𝓞 K))
    (x : W.adicCompletion K) :
    finitePlaceAdicCompletionMap K K W
        ⟨W, finitePlaceBelow_self W⟩ x =
      x := by
  let P : (W.valuation K).Completion → Prop := fun y =>
    finitePlaceAdicCompletionMap K K W
        ⟨W, finitePlaceBelow_self W⟩
        (HeightOneSpectrum.adicCompletion.ofCompletion y) =
      HeightOneSpectrum.adicCompletion.ofCompletion y
  change P x.toCompletion
  refine UniformSpace.Completion.induction_on
    (α := WithVal (W.valuation K)) x.toCompletion ?_ ?_
  · exact isClosed_eq
      ((finitePlaceAdicCompletionMap_continuous
        K K W ⟨W, finitePlaceBelow_self W⟩).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K W))
      (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K W)
  · intro r
    let k : K := WithVal.equiv (W.valuation K) r
    change
      finitePlaceAdicCompletionMap K K W
          ⟨W, finitePlaceBelow_self W⟩
          (k : W.adicCompletion K) =
        (k : W.adicCompletion K)
    rw [finitePlaceAdicCompletionMap_coe
      K K W ⟨W, finitePlaceBelow_self W⟩ k]
    simp

/-- Canonical maps between concrete adic completions compose in a
number-field tower. -/
theorem finitePlaceAdicCompletionMap_comp
    {M : Type w}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    (vK : HeightOneSpectrum (𝓞 K))
    (vM : HeightOneSpectrum (𝓞 M))
    (vL : HeightOneSpectrum (𝓞 L))
    (hMK : finitePlaceBelow (K := K) vM = vK)
    (hLM : finitePlaceBelow (K := M) vL = vM)
    (hLK : finitePlaceBelow (K := K) vL = vK)
    (x : vK.adicCompletion K) :
    finitePlaceAdicCompletionMap M L vM ⟨vL, hLM⟩
        (finitePlaceAdicCompletionMap K M vK ⟨vM, hMK⟩ x) =
      finitePlaceAdicCompletionMap K L vK ⟨vL, hLK⟩ x := by
  let P : (vK.valuation K).Completion → Prop := fun y =>
    finitePlaceAdicCompletionMap M L vM ⟨vL, hLM⟩
        (finitePlaceAdicCompletionMap K M vK ⟨vM, hMK⟩
          (HeightOneSpectrum.adicCompletion.ofCompletion y)) =
      finitePlaceAdicCompletionMap K L vK ⟨vL, hLK⟩
        (HeightOneSpectrum.adicCompletion.ofCompletion y)
  change P x.toCompletion
  refine UniformSpace.Completion.induction_on
    (α := WithVal (vK.valuation K)) x.toCompletion ?_ ?_
  · exact isClosed_eq
      ((finitePlaceAdicCompletionMap_continuous
          M L vM ⟨vL, hLM⟩).comp
        ((finitePlaceAdicCompletionMap_continuous
            K M vK ⟨vM, hMK⟩).comp
          (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K vK)))
      ((finitePlaceAdicCompletionMap_continuous
          K L vK ⟨vL, hLK⟩).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K vK))
  · intro r
    let k : K := WithVal.equiv (vK.valuation K) r
    change
      finitePlaceAdicCompletionMap M L vM ⟨vL, hLM⟩
          (finitePlaceAdicCompletionMap K M vK ⟨vM, hMK⟩
            (k : vK.adicCompletion K)) =
        finitePlaceAdicCompletionMap K L vK ⟨vL, hLK⟩
          (k : vK.adicCompletion K)
    rw [finitePlaceAdicCompletionMap_coe
        K M vK ⟨vM, hMK⟩ k,
      finitePlaceAdicCompletionMap_coe
        M L vM ⟨vL, hLM⟩ (algebraMap K M k),
      finitePlaceAdicCompletionMap_coe
        K L vK ⟨vL, hLK⟩ k,
      IsScalarTower.algebraMap_apply K M L]
