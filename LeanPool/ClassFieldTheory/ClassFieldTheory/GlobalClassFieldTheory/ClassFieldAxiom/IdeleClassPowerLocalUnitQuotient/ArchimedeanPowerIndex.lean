/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Basic.Sign.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
/-!
# Archimedean power indices in idele class quotients

This file defines the concrete idele-class subgroup attached to local power
conditions and computes its archimedean local indices.
-/

open scoped NumberField NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- The subgroup `C_K(S,T) = h(S,T)Kˣ/Kˣ` inside the idele class
group. -/
def ideleClassPowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleClassGroup K) :=
  (idelePowerLocalUnitSubgroup (K := K) n S T).map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K))

open scoped Classical in
/-- Elementwise form of `C_K(S,T)=h(S,T)Kˣ/Kˣ`. -/
theorem mem_ideleClassPowerLocalUnitSubgroup_iff
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : IdeleClassGroup K) :
    c ∈ ideleClassPowerLocalUnitSubgroup (K := K) n S T ↔
      ∃ a : IdeleGroup K,
        a ∈ idelePowerLocalUnitSubgroup (K := K) n S T ∧
          QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a = c := by
  rfl

open scoped Classical in
/-- The quotient whose cardinality is the index
`[C_K : C_K(S,T)]`. -/
abbrev IdeleClassPowerLocalUnitQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :=
  IdeleClassGroup K ⧸
    ideleClassPowerLocalUnitSubgroup (K := K) n S T

omit [NumberField K] in
open scoped Classical in
/-- If the exponent is even, or the place is complex, every local
`n`-th power is positive in the archimedean sense. -/
theorem nthPowerSubgroup_le_infinitePositiveSubgroup
    (n : ℕ+)
    (w : InfinitePlace K)
    (harch : Even (n : ℕ) ∨ ¬ w.IsReal) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range ≤
      RayClass.infinitePositiveSubgroup w := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := w.Completionˣ)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  intro hw
  rcases harch with hnEven | hwNotReal
  · rcases hnEven with ⟨m, hm⟩
    let emb :=
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    have hyne : emb (y : w.Completion) ≠ 0 := by
      intro hzero
      apply y.ne_zero
      apply emb.injective
      simp at hzero
    change 0 < emb (((y ^ (n : ℕ) : w.Completionˣ) : w.Completion))
    rw [Units.val_pow_eq_pow_val, map_pow, hm, pow_add, ← pow_two]
    exact sq_pos_of_ne_zero (pow_ne_zero m hyne)
  · exact False.elim (hwNotReal hw)

open scoped Classical in
/-- The sign of a unit at a real infinite place. -/
def realInfinitePlaceSignHom
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    w.Completionˣ →* SignTypeˣ :=
  (Units.map
      (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    (Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        hw).toMulEquiv).toMonoidHom

omit [NumberField K] in
open scoped Classical in
/-- The positive subgroup at a real infinite place is exactly the kernel
of the sign homomorphism. -/
theorem realInfinitePlaceSignHom_ker
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    (realInfinitePlaceSignHom w hw).ker =
      RayClass.infinitePositiveSubgroup w := by
  ext x
  change
    realInfinitePlaceSignHom w hw x = 1 ↔
      x ∈ RayClass.infinitePositiveSubgroup w
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  constructor
  · intro hx hw'
    have hxval := congrArg Units.val hx
    have hxsign :
        SignType.sign
          (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
            hw (x : w.Completion)) =
          1 := by
      simpa [realInfinitePlaceSignHom] using hxval
    have hproof : hw' = hw := Subsingleton.elim _ _
    subst hproof
    exact sign_eq_one_iff.mp hxsign
  · intro hx
    have hxsign :
        SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hw (x : w.Completion)) =
          1 :=
      sign_eq_one_iff.mpr (hx hw)
    apply Units.ext
    simpa [realInfinitePlaceSignHom] using hxsign

omit [NumberField K] in
open scoped Classical in
/-- Both signs occur at a real infinite place. -/
theorem realInfinitePlaceSignHom_surjective
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    Function.Surjective (realInfinitePlaceSignHom w hw) := by
  let eu : w.Completionˣ ≃* ℝˣ :=
    Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        hw).toMulEquiv
  intro s
  cases hs : (s : SignType) with
  | zero =>
      exact False.elim (s.ne_zero hs)
  | neg =>
      refine ⟨eu.symm (-1), ?_⟩
      apply Units.ext
      simp [realInfinitePlaceSignHom, eu, hs]
  | pos =>
      refine ⟨eu.symm 1, ?_⟩
      apply Units.ext
      simp [realInfinitePlaceSignHom, eu, hs]

open scoped Classical in
/-- The quotient by positive units at a real place is its two-element
sign group. -/
noncomputable def realInfinitePositiveQuotientEquivSign
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    w.Completionˣ ⧸ RayClass.infinitePositiveSubgroup w ≃*
      SignTypeˣ := by
  rw [← realInfinitePlaceSignHom_ker w hw]
  exact
    QuotientGroup.quotientKerEquivOfSurjective
      (realInfinitePlaceSignHom w hw)
      (realInfinitePlaceSignHom_surjective w hw)

omit [NumberField K] in
open scoped Classical in
/-- The positive-unit quotient at a real place has order two. -/
theorem card_realInfinitePositiveQuotient
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    Nat.card
        (w.Completionˣ ⧸
          RayClass.infinitePositiveSubgroup w) =
      2 := by
  calc
    Nat.card
        (w.Completionˣ ⧸
          RayClass.infinitePositiveSubgroup w) =
        Nat.card SignTypeˣ :=
      Nat.card_congr
        (realInfinitePositiveQuotientEquivSign w hw).toEquiv
    _ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide

omit [NumberField K] in
open scoped Classical in
/-- In the even-real or complex cases, the local power subgroup is
exactly the usual archimedean positive subgroup. -/
theorem nthPowerSubgroup_eq_infinitePositiveSubgroup
    (n : ℕ+)
    (w : InfinitePlace K)
    (harch : Even (n : ℕ) ∨ ¬ w.IsReal) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range =
      RayClass.infinitePositiveSubgroup w := by
  apply le_antisymm
  · exact
      nthPowerSubgroup_le_infinitePositiveSubgroup
        n w harch
  · intro x hx
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos x hx
    exact
      (MonoidHom.mem_range
        (G := w.Completionˣ)).mpr ⟨y, by
          rw [powMonoidHom_apply]
          exact hy⟩

omit [NumberField K] in
open scoped Classical in
/-- At a real place an odd power map on local units is surjective. -/
theorem nthPowerSubgroup_eq_top_of_real_odd
    (n : ℕ+)
    (w : InfinitePlace K)
    (hw : w.IsReal)
    (hn : Odd (n : ℕ)) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range =
      ⊤ := by
  apply top_unique
  intro x hx
  apply
    (MonoidHom.mem_range
      (G := w.Completionˣ)).mpr
  let emb :=
    NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
  have hx0 : emb (x : w.Completion) ≠ 0 := by
    intro hzero
    apply x.ne_zero
    simp at hzero
  by_cases hxpos : 0 < emb (x : w.Completion)
  · have hxPositive :
        x ∈ RayClass.infinitePositiveSubgroup w := by
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hw'
      have hproof : hw' = hw := Subsingleton.elim _ _
      subst hproof
      exact hxpos
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos x hxPositive
    exact ⟨y, by
      rw [powMonoidHom_apply]
      exact hy⟩
  · have hxneg : emb (x : w.Completion) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hxpos) hx0
    have hnegPositive :
        -x ∈ RayClass.infinitePositiveSubgroup w := by
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hw'
      have hproof : hw' = hw := Subsingleton.elim _ _
      subst hproof
      change 0 < emb ((-x : w.Completionˣ) : w.Completion)
      simp [hxneg]
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos (-x) hnegPositive
    refine ⟨-y, ?_⟩
    rw [powMonoidHom_apply, hn.neg_pow, hy]
    simp

omit [NumberField K] in
open scoped Classical in
/-- The archimedean factor in the local power-index product: it is `2`
exactly for an even exponent at a real place, and `1` otherwise. -/
theorem card_infinitePlace_nthPowerQuotient
    (n : ℕ+)
    (w : InfinitePlace K) :
    Nat.card
        (w.Completionˣ ⧸
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range) =
      if w.IsReal ∧ Even (n : ℕ) then 2 else 1 := by
  classical
  by_cases hw : w.IsReal
  · by_cases hn : Even (n : ℕ)
    · rw [
        nthPowerSubgroup_eq_infinitePositiveSubgroup
          n w (Or.inl hn)]
      simpa [hw, hn] using
        card_realInfinitePositiveQuotient w hw
    · have hodd : Odd (n : ℕ) :=
        (Nat.even_or_odd (n : ℕ)).resolve_left hn
      rw [nthPowerSubgroup_eq_top_of_real_odd n w hw hodd]
      let :
          Subsingleton
            (w.Completionˣ ⧸ (⊤ : Subgroup w.Completionˣ)) :=
        QuotientGroup.subsingleton_quotient_top
      simp [hw, hn]
  · have hpower :
        (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range =
          RayClass.infinitePositiveSubgroup w :=
      nthPowerSubgroup_eq_infinitePositiveSubgroup
        n w (Or.inr hw)
    have hpositive :
        RayClass.infinitePositiveSubgroup w = ⊤ := by
      ext x
      simp [RayClass.mem_infinitePositiveSubgroup_iff, hw]
    rw [hpower, hpositive]
    let :
        Subsingleton
          (w.Completionˣ ⧸ (⊤ : Subgroup w.Completionˣ)) :=
      QuotientGroup.subsingleton_quotient_top
    simp [hw]


end GlobalClassFieldTheory.ClassFieldAxiom
