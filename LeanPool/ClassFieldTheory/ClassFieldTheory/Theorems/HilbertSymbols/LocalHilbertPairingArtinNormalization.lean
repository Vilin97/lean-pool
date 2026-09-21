/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
/-!
# A local Hilbert pairing compatible with arithmetic Artin reciprocity

The pairing and the Artin maps in this theorem are chosen together. The
algebraic pairing laws alone do not determine the values in `μₙ(K)`.
-/

noncomputable section

namespace ClassFieldTheory

/-- One local Hilbert pairing is compatible, at the level of values, with
continuous local Artin maps on its simple Kummer extensions. The first
pairing argument in the displayed action is the Artin input; the second
determines the radical. Thus the symbol with the radical first is the
inverse of the displayed Artin action ratio, by skew-symmetry. This is the
geometric local convention used in the local--global comparison. -/
theorem exists_localHilbertPairing_artinNormalization
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ B : HilbertPairing K n,
      HilbertPairing.IsLocalHilbertPairing B ∧
      ∀ a : Kˣ, ∃ β : SeparableClosure K,
        β ^ (n : ℕ) = algebraMap K (SeparableClosure K) (a : K) ∧
        let E := IntermediateField.adjoin K {β}
        ∃ artin : Kˣ →ₜ* (E ≃ₐ[K] E),
          Function.Surjective artin ∧
          ∀ b : Kˣ,
            artin b
                (⟨β, IntermediateField.subset_adjoin K {β}
                  (Set.mem_singleton β)⟩ : E) =
              algebraMap K E
                  ((B (powerClass K n b) (powerClass K n a)).1 : K) *
                (⟨β, IntermediateField.subset_adjoin K {β}
                  (Set.mem_singleton β)⟩ : E) := by
  let B : HilbertPairing K n := localHilbertPairing K n hnK hmu
  refine ⟨B, localHilbertPairing_isLocalHilbertPairing K n hnK hmu, ?_⟩
  intro a
  let β : SeparableClosure K := KummerTheory.chosenSimpleKummerRoot K n hnK a
  have hβ : β ^ (n : ℕ) = algebraMap K (SeparableClosure K) (a : K) :=
    KummerTheory.chosenSimpleKummerRoot_pow K n hnK a
  refine ⟨β, hβ, ?_⟩
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
  let : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  let artin : Kˣ →ₜ* (E ≃ₐ[K] E) :=
    LocalClassFieldTheory.abelianLocalArtinMap K E
  refine ⟨artin,
    LocalClassFieldTheory.abelianLocalArtinMap_surjective K E, ?_⟩
  intro b
  let βu : Eˣ := KummerTheory.chosenSimpleKummerRootUnit K n hnK a
  let σ : E ≃ₐ[K] E :=
    LocalClassFieldTheory.Kummer.chosenSimpleKummerNormResidueAutomorphism
      K n hnK hmu a b
  have hσ : σ = artin b := by
    change LocalClassFieldTheory.abelianLocalArtinMonoidHom K E b = artin b
    exact (DFunLike.congr_fun
      (LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K E) b).symm
  have hroot :
      Units.map (algebraMap K E).toMonoidHom
          (B (powerClass K n b) (powerClass K n a)).1 =
        KummerTheory.rootQuotient (K := K) (L := E) βu σ := by
    simpa only [B, E, βu, σ] using
      (localHilbertPairing_artin_rootQuotient K n hnK hmu a b)
  have hact : Units.map σ.toMonoidHom βu =
      Units.map (algebraMap K E).toMonoidHom
          (B (powerClass K n b) (powerClass K n a)).1 * βu := by
    calc
      Units.map σ.toMonoidHom βu =
          KummerTheory.rootQuotient (K := K) (L := E) βu σ * βu := by
            simp only [KummerTheory.rootQuotient]
            rw [div_mul_cancel]
            simp only [AlgEquiv.smul_units_def]
            apply Units.ext
            rfl
      _ = _ := by rw [hroot]
  have hfield := congrArg Units.val hact
  change σ
      (⟨β, IntermediateField.subset_adjoin K {β}
        (Set.mem_singleton β)⟩ : E) =
    algebraMap K E
        ((B (powerClass K n b) (powerClass K n a)).1 : K) *
      (⟨β, IntermediateField.subset_adjoin K {β}
        (Set.mem_singleton β)⟩ : E) at hfield
  rw [hσ] at hfield
  exact hfield

end ClassFieldTheory
