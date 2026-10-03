/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionAutomorphism
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Exact constants after a finite constant extension

Let `N / C` have exact constant field `C`, and let `S / C` be a finite
Galois extension of finite fields.  This file proves that the tensor
compositum `S ⊗[C] N` has exact constant field `S`.

For an element algebraic over `S`, adjoin it to `C` inside the compositum.
This finite field is linearly disjoint from `N`, since its intersection with
`N` is contained in the exact constants `C`.  Its degree over `C` therefore
divides `[S : C]`.  The finite-field embedding criterion supplies an embedding
into `S`; uniqueness of the roots of `X ^ #K - X` inside the common
compositum then shows that the original element already belongs to `S`.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section


universe u v w

variable (C N S : Type*) [Field C] [Field N] [Field S]
  [Algebra C N] [Algebra C S]
  [Finite C] [Finite S]
  [FiniteDimensional C S] [IsGalois C S]

/-- A finite Galois extension of the exact finite constant field remains the
exact constant field after tensor base change. -/
theorem exactConstantExtension_algebraicClosure_eq_bot
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra S (ExactConstantExtension C N S) :=
      Algebra.TensorProduct.leftAlgebra
    algebraicClosure S (ExactConstantExtension C N S) =
      (⊥ : IntermediateField S (ExactConstantExtension C N S)) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra C (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C C N S
  let : SMul C (ExactConstantExtension C N S) := Algebra.toSMul
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  have : IsScalarTower C N (ExactConstantExtension C N S) := by
    exact exactConstantExtensionBaseTower C C N S
  let : Algebra S (ExactConstantExtension C N S) :=
    Algebra.TensorProduct.leftAlgebra
  let : SMul S (ExactConstantExtension C N S) := Algebra.toSMul
  have hSN : algebraMap C (ExactConstantExtension C N S) =
      (algebraMap S (ExactConstantExtension C N S)).comp (algebraMap C S) := by
    ext c
    change (1 : S) ⊗ₜ algebraMap C N c =
      algebraMap C S c ⊗ₜ (1 : N)
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul c).symm
  let : IsScalarTower C S (ExactConstantExtension C N S) :=
    IsScalarTower.of_algebraMap_eq' hSN
  let e := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  let : Module.Finite N (ExactConstantExtension C N S) :=
    Module.Finite.equiv e
  have : IsGalois N (ExactConstantExtension C N S) := by
    exact exactConstantExtension_isGalois C N N S hExact
  apply eq_bot_iff.mpr
  intro z hz
  have hzS : IsAlgebraic S z := mem_algebraicClosure_iff.mp hz
  have hzInt : IsIntegral C z := isIntegral_trans z hzS.isIntegral
  let K : IntermediateField C (ExactConstantExtension C N S) :=
    IntermediateField.adjoin C {z}
  let : FiniteDimensional C K := by
    dsimp [K]
    exact IntermediateField.adjoin.finiteDimensional hzInt
  let : Finite K := Module.finite_of_finite C
  let : Fintype K := Fintype.ofFinite K
  let : Algebra.IsAlgebraic C K := Algebra.IsAlgebraic.of_finite C K
  have : IsGalois C K := inferInstance
  let iN : N →ₐ[C] ExactConstantExtension C N S :=
    IsScalarTower.toAlgHom C N (ExactConstantExtension C N S)
  let N' : IntermediateField C (ExactConstantExtension C N S) :=
    iN.fieldRange
  have hInf : K ⊓ N' =
      (⊥ : IntermediateField C (ExactConstantExtension C N S)) := by
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨n, hn⟩ := hx.2
    have hxAlg : IsAlgebraic C (x : ExactConstantExtension C N S) := by
      have hxK : IsAlgebraic C (⟨x, hx.1⟩ : K) :=
        Algebra.IsAlgebraic.isAlgebraic (R := C) (A := K)
          (⟨x, hx.1⟩ : K)
      exact IsAlgebraic.algHom K.val hxK
    have hnAlg : IsAlgebraic C n := by
      apply (isAlgebraic_algHom_iff iN iN.injective).mp
      change IsAlgebraic C (iN.toRingHom n)
      rw [hn]
      exact hxAlg
    have hnBot : n ∈ (⊥ : IntermediateField C N) := by
      rw [← hExact]
      exact mem_algebraicClosure_iff.mpr hnAlg
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hnBot
    apply IntermediateField.mem_bot.mpr
    refine ⟨c, ?_⟩
    calc
      algebraMap C (ExactConstantExtension C N S) c =
          iN (algebraMap C N c) := (iN.commutes c).symm
      _ = iN n := congrArg iN hc
      _ = x := hn
  have hLD' : K.LinearDisjoint N' :=
    linearDisjoint_of_inf_eq_bot_of_finite_galois_left K N' hInf
  have hLD : K.LinearDisjoint N := by
    change K.toSubalgebra.LinearDisjoint iN.range
    have hLDsub : K.toSubalgebra.LinearDisjoint N'.toSubalgebra :=
      (IntermediateField.linearDisjoint_iff' (A := K) (B := N')).mp hLD'
    simpa only [N', AlgHom.fieldRange_toSubalgebra] using hLDsub
  let A : IntermediateField N (ExactConstantExtension C N S) :=
    IntermediateField.adjoin N (K : Set (ExactConstantExtension C N S))
  have hrank : Module.rank N A = Module.rank C K := by
    simpa [A] using
      hLD.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  have hfinrank : Module.finrank N A = Module.finrank C K := by
    simpa only [Module.finrank] using congrArg Cardinal.toNat hrank
  have hdvdTop : Module.finrank N A ∣
      Module.finrank N (ExactConstantExtension C N S) := by
    simpa using
      (IntermediateField.finrank_dvd_of_le_right
        (show A ≤
          (⊤ : IntermediateField N (ExactConstantExtension C N S)) from le_top))
  have hdvd : Module.finrank C K ∣ Module.finrank C S := by
    rw [← exactConstantExtension_finrank C N S, ← hfinrank]
    exact hdvdTop
  let φ : K →ₐ[C] S :=
    Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd hdvd)
  let iKS : K →ₐ[C] ExactConstantExtension C N S :=
    (IsScalarTower.toAlgHom C S
      (ExactConstantExtension C N S)).comp φ
  let zk : K := ⟨z, IntermediateField.subset_adjoin C {z}
    (Set.mem_singleton z)⟩
  have hzpow : z ^ Fintype.card K = z := by
    calc
      z ^ Fintype.card K = ((zk ^ Fintype.card K : K) :
          ExactConstantExtension C N S) := rfl
      _ = (zk : ExactConstantExtension C N S) :=
        congrArg Subtype.val (FiniteField.pow_card zk)
      _ = z := rfl
  let p : K[X] := Polynomial.X ^ Fintype.card K - Polynomial.X
  have hpSplit : p.Splits := by
    dsimp [p]
    simpa [Nat.card_eq_fintype_card] using
      (Polynomial.splits_X_pow_nat_card_sub_X (K := K))
  have hp0 : p ≠ 0 := by
    dsimp [p]
    exact FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have hroot : (p.map iKS).IsRoot z := by
    simp [p, hzpow]
  obtain ⟨k, hk⟩ := hpSplit.mem_range_of_isRoot hp0 hroot
  apply IntermediateField.mem_bot.mpr
  refine ⟨φ k, ?_⟩
  simpa [iKS] using hk

end

end BGS.HasseWeil
