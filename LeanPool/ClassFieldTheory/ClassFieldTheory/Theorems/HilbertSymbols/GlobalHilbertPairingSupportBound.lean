/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.FinitePlaceHilbertBadSet
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingProperties
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertComparison
/-!
# An explicit support bound for every local Hilbert-pairing family

The norm-residue criterion determines the zero set of every such family,
even though it does not determine all of its nontrivial values.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- The finite-place factors of a locally Hilbert family are trivial
where the exponent and both arguments are valuation-ring units. -/
theorem globalHilbertPairing_mulSupport_subset_finitePlaceHilbertBadSet
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : GlobalHilbertPairingFamily F n)
    (hB : GlobalHilbertPairingFamily.IsLocallyHilbert F B)
    (a b : Fˣ) :
    Function.mulSupport
        (fun v : HeightOneSpectrum (𝓞 F) =>
          GlobalHilbertPairingFamily.finiteFactor F B hmu v a b) ⊆
      finitePlaceHilbertBadSet F n a b := by
  intro v hv
  by_contra hvBad
  change ¬ (v.valuation F (a : F) ≠ 1 ∨
    v.valuation F (b : F) ≠ 1 ∨
    v.valuation F ((n : ℕ) : F) ≠ 1) at hvBad
  have hva : v.valuation F (a : F) = 1 := by
    by_contra h
    exact hvBad (Or.inl h)
  have hvb : v.valuation F (b : F) = 1 := by
    by_contra h
    exact hvBad (Or.inr (Or.inl h))
  have hvn : v.valuation F ((n : ℕ) : F) = 1 := by
    by_contra h
    exact hvBad (Or.inr (Or.inr h))
  let C := finitePlaceAdicHilbertPairingFamily F n hmu
  have hC : GlobalHilbertPairingFamily.IsLocallyHilbert F C :=
    finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F n hmu
  have hnF : ((n : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  have hsource :
      GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
        F n hnF hmu v a b = 1 :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one
      F n hnF hmu a b v hva hvb hvn
  have hCfactor :
      GlobalHilbertPairingFamily.finiteFactor F C hmu v a b = 1 := by
    rw [finitePlaceAdicHilbertPairingFamily_finiteFactor F n hnF hmu v a b]
    change KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
        F n hnF hmu v a b) = 1
    rw [hsource, map_one]
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e : rootsOfUnity (n : ℕ) F ≃*
      rootsOfUnity (n : ℕ) (v.adicCompletion F) :=
    rootsOfUnityEquivOfPrimitiveRoots
      (algebraMap F (v.adicCompletion F)).injective hmu
  let av : (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let bv : (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b
  have hzero :
      GlobalHilbertPairingFamily.finiteFactor F C hmu v a b = 1 ↔
        GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1 := by
    change e.symm ((C v).symbol av bv) = 1 ↔
      e.symm ((B v).symbol av bv) = 1
    simp only [MulEquiv.map_eq_one_iff]
    exact ((hC v).2.2.2 av bv).trans ((hB v).2.2.2 av bv).symm
  exact hv (hzero.mp hCfactor)

end ClassFieldTheory
