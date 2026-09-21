/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import LeanPool.KaltonPeck.KaltonPeck.Support.CgpBlockExtraction
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularAdd

/-!
# Compact restrictions and upper semi-Fredholm operators

This file develops compact-restriction machinery for failed upper semi-Fredholm operators and
the compact-perturbation argument for the canonical Kalton--Peck space.
-/


namespace KaltonPeck.Support.GraphFredholm

noncomputable section

open Coordinates Symplectic
open Function Set Filter Topology
open StrictlySingular
open scoped ENNReal NNReal Topology lp BigOperators InnerProductSpace

/-- A bounded operator is upper semi-Fredholm when its kernel is finite-dimensional and its
range is closed.
Blueprint label: `def:upper-semi`; audit ID `INF-UPPER-SEMI-FREDHOLM`. -/
def IsUpperSemiFredholm {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : X →L[ℝ] Y) : Prop := by
  exact FiniteDimensional ℝ A.toLinearMap.ker ∧ IsClosed (A.toLinearMap.range : Set Y)

universe uX uY

/-- Upper semi-Fredholm operators are closed under composition.
Blueprint label: `lem:upper-semi-calculus`. -/
theorem IsUpperSemiFredholm.comp
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {A : X →L[ℝ] Y} (hA : IsUpperSemiFredholm A)
    {B : Y →L[ℝ] Z} (hB : IsUpperSemiFredholm B) :
    IsUpperSemiFredholm (B.comp A) := by
  letI : FiniteDimensional ℝ A.toLinearMap.ker := hA.1
  letI : FiniteDimensional ℝ B.toLinearMap.ker := hB.1
  have hker : FiniteDimensional ℝ (B.comp A).toLinearMap.ker := by
    change FiniteDimensional ℝ (B.toLinearMap.comp A.toLinearMap).ker
    rw [LinearMap.ker_comp]
    infer_instance
  refine ⟨hker, ?_⟩
  letI : CompleteSpace B.toLinearMap.range := hB.2.completeSpace_coe
  let f : Y →L[ℝ] B.toLinearMap.range := B.rangeRestrict
  have hfq : Topology.IsQuotientMap f :=
    f.isQuotientMap B.toLinearMap.surjective_rangeRestrict
  have himage : IsClosed
      ((Submodule.map f.toLinearMap A.toLinearMap.range :
        Submodule ℝ B.toLinearMap.range) : Set B.toLinearMap.range) := by
    apply hfq.isClosed_preimage.mp
    change IsClosed
      ((Submodule.comap f.toLinearMap
        (Submodule.map f.toLinearMap A.toLinearMap.range) : Submodule ℝ Y) : Set Y)
    rw [Submodule.comap_map_eq]
    have hfker : f.toLinearMap.ker = B.toLinearMap.ker := by
      simp [f]
    rw [hfker]
    exact Submodule.isClosed_sup_finiteDimensional _ _ hA.2
  have hclosed : IsClosed
      ((fun y : B.toLinearMap.range => (y : Z)) ''
        ((Submodule.map f.toLinearMap A.toLinearMap.range :
          Submodule ℝ B.toLinearMap.range) : Set B.toLinearMap.range)) :=
    hB.2.isClosedMap_subtype_val _ himage
  rw [show ((B.comp A).toLinearMap.range : Set Z) =
      (fun y : B.toLinearMap.range => (y : Z)) ''
        ((Submodule.map f.toLinearMap A.toLinearMap.range :
          Submodule ℝ B.toLinearMap.range) : Set B.toLinearMap.range) by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨f (A x), ?_, rfl⟩
      exact ⟨A x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, ⟨x, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩]
  exact hclosed

/-- An upper semi-Fredholm operator with infinite-dimensional domain is not strictly singular.
Blueprint label: `lem:upper-semi-not-strictly-singular`. -/
theorem IsUpperSemiFredholm.not_isStrictlySingular
    {X : Type uX} {Y : Type uY}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {T : X →L[ℝ] Y} (hT : IsUpperSemiFredholm T)
    (hX : ¬ FiniteDimensional ℝ X) :
    ¬ IsStrictlySingular.{0, uX, uY, uX} T :=
  not_isStrictlySingular_of_finiteDimensional_ker_of_isClosed_range
    hX T hT.1 hT.2

/-- An operator has an infinite-dimensional compact restriction when its restriction to some
closed infinite-dimensional subspace is compact.
Blueprint label: `def:infinite-dimensional-compact-restriction`. -/
def HasInfiniteDimensionalCompactRestriction
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : Prop :=
  ∃ M : Submodule ℝ X, IsClosed (M : Set X) ∧
    ¬ FiniteDimensional ℝ M ∧ IsCompactOperator (T.comp M.subtypeL)

/-- A surjective bounded operator admits uniformly controlled approximation by its kernel.
Blueprint label: `lem:canonical-kernel-approximation`. -/
theorem exists_kernel_approximation_of_surjective
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (q : X →L[ℝ] Y) (hq : Function.Surjective q) :
    ∃ C > 0, ∀ x : X, ∃ y : q.ker,
      ‖x - (y : X)‖ ≤ C * ‖q x‖ := by
  obtain ⟨C, hC, hpre⟩ := q.exists_preimage_norm_le hq
  refine ⟨C, hC, ?_⟩
  intro x
  obtain ⟨z, hz, hznorm⟩ := hpre (q x)
  let y : q.ker := ⟨x - z, by
    change q (x - z) = 0
    rw [map_sub, hz, sub_self]⟩
  refine ⟨y, ?_⟩
  have hxy : x - (y : X) = z := by
    simp [y]
  rw [hxy]
  exact hznorm

/-- The canonical quotient admits uniformly controlled approximation by its kernel.
Blueprint label: `lem:canonical-kernel-approximation`. -/
theorem canonicalL2Quotient_kernel_approximation :
    ∃ C > 0, ∀ z : CanonicalRealKaltonPeck,
      ∃ y : canonicalL2Quotient.ker,
        ‖z - (y : CanonicalRealKaltonPeck)‖ ≤
          C * ‖canonicalL2Quotient z‖ :=
  exists_kernel_approximation_of_surjective canonicalL2Quotient
    canonicalL2Quotient_surjective

variable {X : Type uX} {Y : Type uY}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace Y] in
/-- If an operator is bounded below on the common kernel of finitely many
functionals, it is upper semi-Fredholm. -/
theorem upperSemi_of_antilipschitz_evalKernel
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (T : X →L[ℝ] Y) (f : X →L[ℝ] F)
    (hanti : ∃ K, AntilipschitzWith K (T.domRestrict f.ker)) :
    IsUpperSemiFredholm T := by
  let H : Submodule ℝ X := f.ker
  have hHclosed : IsClosed (H : Set X) := f.isClosed_ker
  letI : CompleteSpace H := hHclosed.completeSpace_coe
  have hfRange : FiniteDimensional ℝ f.range := inferInstance
  let hHcomp : H.ClosedComplemented :=
    f.ker_closedComplemented_of_finiteDimensional_range
  let C : Submodule ℝ X := hHcomp.complement
  have htop : Submodule.IsTopCompl H C :=
    hHcomp.isTopCompl_complement
  have hCfin : FiniteDimensional ℝ C := by
    apply FiniteDimensional.of_injective (f.toLinearMap.domRestrict C)
    intro x y hxy
    apply Subtype.ext
    have hdiffH : (x : X) - (y : X) ∈ H := by
      change f ((x : X) - (y : X)) = 0
      rw [map_sub, sub_eq_zero]
      exact hxy
    have hdiffC : (x : X) - (y : X) ∈ C :=
      C.sub_mem x.property y.property
    have hbot : (x : X) - (y : X) ∈ (⊥ : Submodule ℝ X) :=
      htop.isCompl.disjoint.le_bot ⟨hdiffH, hdiffC⟩
    simpa only [Submodule.mem_bot, sub_eq_zero] using hbot
  letI : FiniteDimensional ℝ C := hCfin
  rcases hanti with ⟨K, hK⟩
  have hTHinj : Function.Injective (T.domRestrict H) := hK.injective
  let p : T.toLinearMap.ker →ₗ[ℝ] C :=
    C.projectionOnto H htop.isCompl.symm ∘ₗ
      T.toLinearMap.ker.subtype
  have hp : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    have hproj :
        C.projectionOnto H htop.isCompl.symm ((x : X) - (y : X)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hxy
    have hdiffH : (x : X) - (y : X) ∈ H := by
      exact
        (Submodule.projectionOnto_apply_eq_zero_iff htop.isCompl.symm).mp hproj
    let z : H := ⟨(x : X) - (y : X), hdiffH⟩
    have hz0 : T.domRestrict H z = 0 := by
      change T ((x : X) - (y : X)) = 0
      rw [map_sub, show T (x : X) = 0 from x.property,
        show T (y : X) = 0 from y.property, sub_zero]
    have : z = 0 := hTHinj (by simpa using hz0)
    exact sub_eq_zero.mp (congrArg Subtype.val this)
  letI : FiniteDimensional ℝ T.toLinearMap.ker :=
    FiniteDimensional.of_injective p hp
  have hTHclosed :
      IsClosed (((T.domRestrict H).toLinearMap.range : Submodule ℝ Y) : Set Y) :=
    hK.isClosed_range (T.domRestrict H).uniformContinuous
  have hRange :
      T.toLinearMap.range =
        (T.domRestrict H).toLinearMap.range ⊔
          Submodule.map T.toLinearMap C := by
    rw [ContinuousLinearMap.toLinearMap_domRestrict, LinearMap.range_domRestrict]
    rw [← Submodule.map_sup]
    rw [htop.isCompl.sup_eq_top]
    exact LinearMap.range_eq_map T.toLinearMap
  refine ⟨inferInstance, ?_⟩
  rw [hRange]
  exact Submodule.isClosed_sup_finiteDimensional _ _ hTHclosed

omit [CompleteSpace Y] in
/-- Failure of upper semi-Fredholmness persists on the common kernel of
finitely many functionals. -/
theorem exists_unit_mem_evalKernel_norm_apply_lt_of_not_upper
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    (f : X →L[ℝ] F) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, f x = 0 ∧ ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  have hnot :
      ¬ ∃ K, AntilipschitzWith K (T.domRestrict f.ker) := by
    intro h
    exact hT (upperSemi_of_antilipschitz_evalKernel T f h)
  obtain ⟨x, hxnorm, hxsmall⟩ :=
    exists_unit_norm_apply_lt_of_not_boundedBelow
      (T.domRestrict f.ker) hnot hε
  exact ⟨x, x.property, hxnorm, hxsmall⟩

omit [CompleteSpace Y] in
/-- Extend a finite biorthogonal family by a vector on which a failed
upper-semi operator is arbitrarily small relative to the new functional. -/
theorem exists_biorthogonal_extension_of_not_upper
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {n : ℕ} (v : Fin n → X) (φ : Fin n → StrongDual ℝ X)
    (hvφ : ∀ i j, φ i (v j) = if i = j then 1 else 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ (x : X) (ψ : StrongDual ℝ X),
      ‖x‖ = 1 ∧
      (∀ i, φ i x = 0) ∧
      (∀ i, ψ (v i) = 0) ∧
      ψ x = 1 ∧
      ‖ψ‖ * ‖T x‖ < η := by
  classical
  let eval : X →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.pi φ
  let P : X →L[ℝ] X := ∑ i, (φ i).smulRight (v i)
  have hPv (j : Fin n) : P (v j) = v j := by
    simp [P, hvφ]
  let C : ℝ := ‖(1 : X →L[ℝ] X) - P‖ + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  obtain ⟨x, hxeval, hxnorm, hxsmall⟩ :=
    exists_unit_mem_evalKernel_norm_apply_lt_of_not_upper
      T hT eval (div_pos hη hC)
  have hxφ (i : Fin n) : φ i x = 0 := by
    have := congr_fun hxeval i
    exact this
  have hPx : P x = 0 := by
    simp [P, hxφ]
  obtain ⟨g, hgnorm, hgx⟩ :=
    exists_dual_vector ℝ x (by simp [hxnorm])
  let ψ : StrongDual ℝ X := g.comp ((1 : X →L[ℝ] X) - P)
  have hψv (i : Fin n) : ψ (v i) = 0 := by
    change g (v i - P (v i)) = 0
    rw [hPv, sub_self, map_zero]
  have hψx : ψ x = 1 := by
    change g (x - P x) = 1
    rw [hPx, sub_zero, hgx, hxnorm]
    norm_num
  have hψnorm : ‖ψ‖ ≤ ‖(1 : X →L[ℝ] X) - P‖ := by
    calc
      ‖ψ‖ ≤ ‖g‖ * ‖(1 : X →L[ℝ] X) - P‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖(1 : X →L[ℝ] X) - P‖ := by rw [hgnorm, one_mul]
  refine ⟨x, ψ, hxnorm, hxφ, hψv, hψx, ?_⟩
  have hTnonneg : 0 ≤ ‖T x‖ := norm_nonneg _
  calc
    ‖ψ‖ * ‖T x‖ ≤ ‖(1 : X →L[ℝ] X) - P‖ * ‖T x‖ :=
      mul_le_mul_of_nonneg_right hψnorm hTnonneg
    _ ≤ C * ‖T x‖ := by
      apply mul_le_mul_of_nonneg_right _ hTnonneg
      dsimp [C]
      linarith
    _ < C * (η / C) := mul_lt_mul_of_pos_left hxsmall hC
    _ = η := by field_simp

/-- Extend a biorthogonal prefix using failure of upper semi-Fredholmness. -/
noncomputable def snocNotUpper
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ}
    (p : BiorthogonalPrefix T η n) :
    BiorthogonalPrefix T η (n + 1) := by
  have hex :
      ∃ (x : X) (ψ : StrongDual ℝ X),
        ‖x‖ = 1 ∧
        (∀ i, p.φ i x = 0) ∧
        (∀ i, ψ (p.v i) = 0) ∧
        ψ x = 1 ∧
        ‖ψ‖ * ‖T x‖ < η n :=
    exists_biorthogonal_extension_of_not_upper
      T hT p.v p.φ p.bio (hη n)
  let x : X := Exists.choose hex
  let hψ := Exists.choose_spec hex
  let ψ : StrongDual ℝ X := Exists.choose hψ
  have hs := Exists.choose_spec hψ
  have hxnorm : ‖x‖ = 1 := hs.1
  have hxφ : ∀ i, p.φ i x = 0 := hs.2.1
  have hψv : ∀ i, ψ (p.v i) = 0 := hs.2.2.1
  have hψx : ψ x = 1 := hs.2.2.2.1
  have hxsmall : ‖ψ‖ * ‖T x‖ < η n := hs.2.2.2.2
  exact
    { v := Fin.snoc p.v x
      φ := Fin.snoc p.φ ψ
      norm_v := by
        intro i
        cases i using Fin.lastCases with
        | last => simpa using hxnorm
        | cast i => simpa using p.norm_v i
      bio := by
        intro i j
        cases i using Fin.lastCases with
        | last =>
            cases j using Fin.lastCases with
            | last => simpa using hψx
            | cast j => simp [hψv, Ne.symm (Fin.castSucc_ne_last j)]
        | cast i =>
            cases j using Fin.lastCases with
            | last => simp [hxφ]
            | cast j => simpa using p.bio i j
      small := by
        intro i
        cases i using Fin.lastCases with
        | last => simpa using hxsmall
        | cast i => simpa using p.small i }

/-- Recursively construct biorthogonal prefixes for an operator which is not upper semi-Fredholm. -/
noncomputable def biorthogonalPrefixNotUpper
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) :
    (n : ℕ) → BiorthogonalPrefix T η n
  | 0 => BiorthogonalPrefix.nil T η
  | n + 1 => snocNotUpper T hT hη (biorthogonalPrefixNotUpper T hT hη n)

omit [CompleteSpace Y] in
theorem snocNotUpper_v_castSucc
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ}
    (p : BiorthogonalPrefix T η n) (i : Fin n) :
    (snocNotUpper T hT hη p).v i.castSucc = p.v i := by
  simp [snocNotUpper]

omit [CompleteSpace Y] in
theorem snocNotUpper_φ_castSucc
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ}
    (p : BiorthogonalPrefix T η n) (i : Fin n) :
    (snocNotUpper T hT hη p).φ i.castSucc = p.φ i := by
  simp [snocNotUpper]

open KaltonPeck.Support.StrictlySingular in
omit [CompleteSpace Y] in
theorem biorthogonalPrefixNotUpper_succ_v_castSucc
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ} (i : Fin n) :
    (biorthogonalPrefixNotUpper T hT hη (n + 1)).v i.castSucc =
      (biorthogonalPrefixNotUpper T hT hη n).v i := by
  rw [biorthogonalPrefixNotUpper]
  exact snocNotUpper_v_castSucc T hT hη _ i

open KaltonPeck.Support.StrictlySingular in
omit [CompleteSpace Y] in
theorem biorthogonalPrefixNotUpper_succ_φ_castSucc
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ} (i : Fin n) :
    (biorthogonalPrefixNotUpper T hT hη (n + 1)).φ i.castSucc =
      (biorthogonalPrefixNotUpper T hT hη n).φ i := by
  rw [biorthogonalPrefixNotUpper]
  exact snocNotUpper_φ_castSucc T hT hη _ i

open KaltonPeck.Support.StrictlySingular in
/-- The newest vector in the biorthogonal prefix associated to a
non-upper-semi-Fredholm operator. -/
noncomputable def notUpperBasicVector
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (n : ℕ) : X :=
  (biorthogonalPrefixNotUpper T hT hη (n + 1)).v (Fin.last n)

open KaltonPeck.Support.StrictlySingular in
/-- The newest functional in the biorthogonal prefix associated to a
non-upper-semi-Fredholm operator. -/
noncomputable def notUpperBasicFunctional
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (n : ℕ) : StrongDual ℝ X :=
  (biorthogonalPrefixNotUpper T hT hη (n + 1)).φ (Fin.last n)

open KaltonPeck.Support.StrictlySingular in
omit [CompleteSpace Y] in
theorem biorthogonalPrefixNotUpper_v_eq_basicVector
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n)
    (n : ℕ) (i : Fin (n + 1)) :
    (biorthogonalPrefixNotUpper T hT hη (n + 1)).v i =
      notUpperBasicVector T hT hη i.val := by
  induction n with
  | zero =>
      have hi : i = Fin.last 0 := by ext; omega
      subst i
      rfl
  | succ n ih =>
      cases i using Fin.lastCases with
      | last => rfl
      | cast i =>
          rw [biorthogonalPrefixNotUpper_succ_v_castSucc T hT hη]
          exact ih i

open KaltonPeck.Support.StrictlySingular in
omit [CompleteSpace Y] in
theorem biorthogonalPrefixNotUpper_φ_eq_basicFunctional
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n)
    (n : ℕ) (i : Fin (n + 1)) :
    (biorthogonalPrefixNotUpper T hT hη (n + 1)).φ i =
      notUpperBasicFunctional T hT hη i.val := by
  induction n with
  | zero =>
      have hi : i = Fin.last 0 := by ext; omega
      subst i
      rfl
  | succ n ih =>
      cases i using Fin.lastCases with
      | last => rfl
      | cast i =>
          rw [biorthogonalPrefixNotUpper_succ_φ_castSucc T hT hη]
          exact ih i

omit [CompleteSpace Y] in
open KaltonPeck.Support.StrictlySingular in
theorem exists_biorthogonal_sequence_summable_of_not_upper
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T) :
    ∃ (v : ℕ → X) (φ : ℕ → StrongDual ℝ X),
      (∀ n, ‖v n‖ = 1) ∧
      (∀ i j, φ i (v j) = if i = j then 1 else 0) ∧
      Summable (fun n => ‖T (v n)‖) ∧
      Summable (fun n => ‖φ n‖ * ‖T (v n)‖) := by
  let η : ℕ → ℝ := fun n => 1 / 2 / 2 ^ n
  have hη (n : ℕ) : 0 < η n := by
    dsimp [η]
    positivity
  let v : ℕ → X := notUpperBasicVector T hT hη
  let φ : ℕ → StrongDual ℝ X := notUpperBasicFunctional T hT hη
  have hvnorm (n : ℕ) : ‖v n‖ = 1 :=
    (biorthogonalPrefixNotUpper T hT hη (n + 1)).norm_v (Fin.last n)
  have hbio (i j : ℕ) : φ i (v j) = if i = j then 1 else 0 := by
    let N := i + j
    let ii : Fin (N + 1) := ⟨i, by dsimp [N]; omega⟩
    let jj : Fin (N + 1) := ⟨j, by dsimp [N]; omega⟩
    have h := (biorthogonalPrefixNotUpper T hT hη (N + 1)).bio ii jj
    rw [biorthogonalPrefixNotUpper_φ_eq_basicFunctional T hT hη N ii,
      biorthogonalPrefixNotUpper_v_eq_basicVector T hT hη N jj] at h
    simpa [φ, v, ii, jj] using h
  have hsmall (n : ℕ) : ‖φ n‖ * ‖T (v n)‖ < η n :=
    (biorthogonalPrefixNotUpper T hT hη (n + 1)).small (Fin.last n)
  have hηsum : Summable η := by
    simpa [η] using summable_geometric_two' (1 : ℝ)
  have hprod :
      Summable (fun n => ‖φ n‖ * ‖T (v n)‖) :=
    hηsum.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => (hsmall n).le)
  have hφnorm (n : ℕ) : 1 ≤ ‖φ n‖ := by
    have happly : ‖φ n (v n)‖ ≤ ‖φ n‖ * ‖v n‖ := (φ n).le_opNorm (v n)
    rw [hbio n n, if_pos rfl, norm_one, hvnorm n, mul_one] at happly
    exact happly
  have hTnorm (n : ℕ) : ‖T (v n)‖ ≤ ‖φ n‖ * ‖T (v n)‖ := by
    nlinarith [hφnorm n, norm_nonneg (T (v n))]
  have hTsum : Summable (fun n => ‖T (v n)‖) :=
    hprod.of_nonneg_of_le (fun n => norm_nonneg _) hTnorm
  exact ⟨v, φ, hvnorm, hbio, hTsum, hprod⟩

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem functional_smulRight_isCompact
    (c : StrongDual ℝ X) (y : Y) :
    IsCompactOperator (c.smulRight y) := by
  have hc : IsCompactOperator c :=
    isCompactOperator_of_locallyCompactSpace_dom c
  change IsCompactOperator
    (fun x => (ContinuousLinearMap.toSpanSingleton ℝ y) (c x))
  exact hc.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ y)

/-- A biorthogonal family with summable weighted images spans a closed
infinite-dimensional subspace on which the operator is compact. -/
theorem hasInfiniteDimensionalCompactRestriction_of_biorthogonal_weighted
    (T : X →L[ℝ] Y)
    (v : ℕ → X) (φ : ℕ → StrongDual ℝ X)
    (hbio : ∀ i j, φ i (v j) = if i = j then 1 else 0)
    (hsum : Summable (fun n => ‖φ n‖ * ‖T (v n)‖)) :
    HasInfiniteDimensionalCompactRestriction T := by
  let R : ℕ → X →L[ℝ] Y :=
    fun n => (φ n).smulRight (T (v n))
  have hRnorm (n : ℕ) :
      ‖R n‖ = ‖φ n‖ * ‖T (v n)‖ := by
    simp [R]
  have hR : Summable R := by
    apply Summable.of_norm
    simpa only [hRnorm] using hsum
  let L : X →L[ℝ] Y := ∑' n, R n
  have hLcompact : IsCompactOperator L := by
    apply isCompactOperator_of_tendsto hR.hasSum.tendsto_sum_nat
    filter_upwards []
    intro n
    induction n with
    | zero =>
        change IsCompactOperator (0 : X →L[ℝ] Y)
        exact isCompactOperator_zero
    | succ n ih =>
        rw [Finset.sum_range_succ]
        exact ih.add (functional_smulRight_isCompact (φ n) (T (v n)))
  have hLv (j : ℕ) : L (v j) = T (v j) := by
    have hEval : HasSum (fun n => R n (v j)) (L (v j)) :=
      hR.hasSum.map (ContinuousLinearMap.apply ℝ Y (v j))
        (ContinuousLinearMap.apply ℝ Y (v j)).continuous
    have hsingle :
        HasSum (fun n => if n = j then T (v j) else 0) (T (v j)) := by
      simpa only [eq_comm] using hasSum_ite_eq j (T (v j))
    apply hEval.unique
    convert hsingle using 1
    ext n
    by_cases hnj : n = j
    · subst n
      simp [R, hbio]
    · simp [R, hbio, hnj]
  let M : Submodule ℝ X :=
    (Submodule.span ℝ (Set.range v)).topologicalClosure
  have hMclosed : IsClosed (M : Set X) :=
    Submodule.isClosed_topologicalClosure _
  have hM : ¬ FiniteDimensional ℝ M :=
    not_finiteDimensional_topologicalClosure_span_of_biorthogonal hbio
  have hEq : L.comp M.subtypeL = T.comp M.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    change L (x : X) = T (x : X)
    exact ContinuousLinearMap.eqOn_closure_span
      (fun _ hz => by
        obtain ⟨j, rfl⟩ := hz
        exact hLv j) x.property
  refine ⟨M, hMclosed, hM, ?_⟩
  rw [← hEq]
  exact hLcompact.comp_clm M.subtypeL

/-- Every failure of upper semi-Fredholmness has an infinite-dimensional
compact restriction. This is the Kato basic-sequence characterization used
implicitly in CGP Proposition 5.3(c). -/
theorem hasInfiniteDimensionalCompactRestriction_of_not_upper
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T) :
    HasInfiniteDimensionalCompactRestriction T := by
  obtain ⟨v, φ, _, hbio, _, hsum⟩ :=
    exists_biorthogonal_sequence_summable_of_not_upper T hT
  exact hasInfiniteDimensionalCompactRestriction_of_biorthogonal_weighted
    T v φ hbio hsum

namespace Canonical

/-- Abbreviation for the canonical real Kalton--Peck space. -/
abbrev KP := CanonicalRealKaltonPeck
/-- Abbreviation for the canonical real Hilbert coordinate space. -/
abbrev H := CanonicalL2

/-- The corrected compact perturbation step in CGP Proposition 5.3(c).
Starting from an infinite-dimensional compact restriction of `B`, it
constructs an infinite-dimensional closed subspace and an embedding into
the canonical kernel along which `B` remains compact. -/
theorem exists_compact_kernel_embedding_of_compactRestriction
    (hq : IsStrictlySingular.{0, 0, 0, 0} canonicalL2Quotient)
    (B : KP →L[ℝ] KP)
    (hB : HasInfiniteDimensionalCompactRestriction B) :
    ∃ (N : Submodule ℝ KP), IsClosed (N : Set KP) ∧
      ¬ FiniteDimensional ℝ N ∧
      ∃ R : N →L[ℝ] H,
        (∃ K, AntilipschitzWith K R) ∧
        IsCompactOperator ((B.comp canonicalL2Inclusion).comp R) := by
  obtain ⟨M, hMclosed, hM, hBMcompact⟩ := hB
  letI : CompleteSpace M := hMclosed.completeSpace_coe
  let qM : M →L[ℝ] H := canonicalL2Quotient.comp M.subtypeL
  have hqMstrict : IsStrictlySingular qM :=
    hq.precomp M.subtypeL
  obtain ⟨v, φ, hvnorm, hbio, _, hprod⟩ :=
    IsStrictlySingular.exists_biorthogonal_sequence_summable hM hqMstrict
  let p : ℕ → ℝ := fun n => ‖φ n‖ * ‖qM (v n)‖
  obtain ⟨C, hC, hkernel⟩ :=
    canonicalL2Quotient_kernel_approximation
  have hptend :
      Tendsto (fun N => ∑' n, p (n + N)) atTop (𝓝 0) :=
    _root_.tendsto_sum_nat_add p
  have hCtend :
      Tendsto (fun N => C * ∑' n, p (n + N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hptend
  have hCevent :
      ∀ᶠ N in atTop, C * ∑' n, p (n + N) < 1 :=
    hCtend.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hCevent
  have htailSmall : C * ∑' n, p (n + N₀) < 1 :=
    hN₀ N₀ le_rfl
  let vt : ℕ → M := fun n => v (n + N₀)
  let φt : ℕ → StrongDual ℝ M := fun n => φ (n + N₀)
  have hvtnorm (n : ℕ) : ‖vt n‖ = 1 := hvnorm (n + N₀)
  have hbiot (i j : ℕ) :
      φt i (vt j) = if i = j then 1 else 0 := by
    simpa [φt, vt] using hbio (i + N₀) (j + N₀)
  have hprodt :
      Summable (fun n => ‖φt n‖ * ‖qM (vt n)‖) := by
    have hpcomp : Summable (fun n => p (n + N₀)) :=
      hprod.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    simpa [p, φt, vt] using hpcomp
  let x : ℕ → KP := fun n => (vt n : KP)
  let y : ℕ → canonicalL2Quotient.ker :=
    fun n => Classical.choose (hkernel (x n))
  have hyclose (n : ℕ) :
      ‖x n - (y n : KP)‖ ≤ C * ‖canonicalL2Quotient (x n)‖ :=
    Classical.choose_spec (hkernel (x n))
  let φe : ℕ → StrongDual ℝ KP :=
    fun n => Classical.choose (exists_extension_norm_eq M (φt n))
  have hφe_apply (n : ℕ) (z : M) :
      φe n (z : KP) = φt n z :=
    (Classical.choose_spec (exists_extension_norm_eq M (φt n))).1 z
  have hφe_norm (n : ℕ) : ‖φe n‖ = ‖φt n‖ :=
    (Classical.choose_spec (exists_extension_norm_eq M (φt n))).2
  let d : ℕ → KP := fun n => x n - (y n : KP)
  let S : ℕ → KP →L[ℝ] KP :=
    fun n => (φe n).smulRight (d n)
  have hSnorm (n : ℕ) : ‖S n‖ = ‖φe n‖ * ‖d n‖ := by
    simp [S]
  have hd_bound (n : ℕ) :
      ‖d n‖ ≤ C * ‖qM (vt n)‖ := by
    simpa [d, x, qM] using hyclose n
  have hSnorm_bound (n : ℕ) :
      ‖S n‖ ≤ C * (‖φt n‖ * ‖qM (vt n)‖) := by
    rw [hSnorm, hφe_norm]
    calc
      ‖φt n‖ * ‖d n‖ ≤
          ‖φt n‖ * (C * ‖qM (vt n)‖) :=
        mul_le_mul_of_nonneg_left (hd_bound n) (norm_nonneg (φt n))
      _ = C * (‖φt n‖ * ‖qM (vt n)‖) := by ring
  have hCprod :
      Summable (fun n => C * (‖φt n‖ * ‖qM (vt n)‖)) :=
    hprodt.mul_left C
  have hSnormSum : Summable (fun n => ‖S n‖) :=
    hCprod.of_nonneg_of_le (fun n => norm_nonneg _) hSnorm_bound
  have hS : Summable S := Summable.of_norm hSnormSum
  let K : KP →L[ℝ] KP := ∑' n, S n
  have hKcompact : IsCompactOperator K := by
    apply isCompactOperator_of_tendsto hS.hasSum.tendsto_sum_nat
    filter_upwards []
    intro n
    induction n with
    | zero =>
        change IsCompactOperator (0 : KP →L[ℝ] KP)
        exact isCompactOperator_zero
    | succ n ih =>
        rw [Finset.sum_range_succ]
        exact ih.add (functional_smulRight_isCompact (φe n) (d n))
  have hKnorm : ‖K‖ < 1 := by
    calc
      ‖K‖ ≤ ∑' n, ‖S n‖ := norm_tsum_le_tsum_norm hSnormSum
      _ ≤ ∑' n, C * (‖φt n‖ * ‖qM (vt n)‖) :=
        hSnormSum.tsum_le_tsum hSnorm_bound hCprod
      _ = C * ∑' n, ‖φt n‖ * ‖qM (vt n)‖ := by
        rw [tsum_mul_left]
      _ = C * ∑' n, p (n + N₀) := by
        congr 1
      _ < 1 := htailSmall
  have hKx (j : ℕ) : K (x j) = d j := by
    have hEval : HasSum (fun n => S n (x j)) (K (x j)) :=
      hS.hasSum.map (ContinuousLinearMap.apply ℝ KP (x j))
        (ContinuousLinearMap.apply ℝ KP (x j)).continuous
    have hsingle :
        HasSum (fun n => if n = j then d j else 0) (d j) := by
      simpa only [eq_comm] using hasSum_ite_eq j (d j)
    apply hEval.unique
    convert hsingle using 1
    ext n
    by_cases hnj : n = j
    · subst n
      simp [S, x, hφe_apply, hbiot]
    · simp [S, x, hφe_apply, hbiot, hnj]
  have hbioe (i j : ℕ) :
      φe i (x j) = if i = j then 1 else 0 := by
    simpa [x] using hφe_apply i (vt j) ▸ hbiot i j
  let N : Submodule ℝ KP :=
    (Submodule.span ℝ (Set.range x)).topologicalClosure
  have hNclosed : IsClosed (N : Set KP) :=
    Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace N := hNclosed.completeSpace_coe
  have hN : ¬ FiniteDimensional ℝ N :=
    not_finiteDimensional_topologicalClosure_span_of_biorthogonal hbioe
  have hNleM : N ≤ M := by
    intro z hz
    have hspan :
        (Submodule.span ℝ (Set.range x) : Set KP) ⊆ (M : Set KP) := by
      exact Submodule.span_le.mpr (by
        rintro _ ⟨n, rfl⟩
        exact (vt n).property)
    exact (hMclosed.closure_subset_iff.2 hspan) hz
  let iNM : N →L[ℝ] M :=
    N.subtypeL.codRestrict M (fun z => hNleM z.property)
  have hBNcompact : IsCompactOperator (B.comp N.subtypeL) := by
    have hc := hBMcompact.comp_clm iNM
    have heq :
        (B.comp M.subtypeL).comp iNM = B.comp N.subtypeL := by
      apply ContinuousLinearMap.ext
      intro z
      rfl
    rw [← heq]
    exact hc
  let J : N →L[ℝ] KP :=
    ((1 : KP →L[ℝ] KP) - K).comp N.subtypeL
  let F : KP →L[ℝ] H :=
    canonicalL2Quotient.comp ((1 : KP →L[ℝ] KP) - K)
  have hFx (j : ℕ) : F (x j) = 0 := by
    change canonicalL2Quotient (x j - K (x j)) = 0
    rw [hKx]
    have hxy : x j - d j = (y j : KP) := by
      simp [d]
    rw [hxy]
    exact (y j).property
  have hJker (z : N) : J z ∈ canonicalL2Quotient.ker := by
    change canonicalL2Quotient (J z) = 0
    change F (z : KP) = 0
    exact ContinuousLinearMap.eqOn_closure_span (f := F) (g := 0)
      (fun _ hz => by
        obtain ⟨j, rfl⟩ := hz
        exact hFx j) z.property
  have hJrange (z : N) : J z ∈ canonicalL2Inclusion.range := by
    rw [canonicalL2Inclusion_range]
    exact hJker z
  let JR : N →L[ℝ] canonicalL2Inclusion.range :=
    J.codRestrict canonicalL2Inclusion.range hJrange
  have hiClosed :
      IsClosed (canonicalL2Inclusion.range : Set KP) := by
    rw [canonicalL2Inclusion_range]
    exact canonicalL2Quotient.isClosed_ker
  let E : H ≃L[ℝ] canonicalL2Inclusion.range :=
    canonicalL2Inclusion.equivRange
      canonicalL2Inclusion_injective hiClosed
  let R : N →L[ℝ] H := E.symm.toContinuousLinearMap.comp JR
  have hiR : canonicalL2Inclusion.comp R = J := by
    apply ContinuousLinearMap.ext
    intro z
    have h := E.apply_symm_apply (JR z)
    exact congrArg Subtype.val h
  have hJlower (z : N) :
      (1 - ‖K‖) * ‖z‖ ≤ ‖J z‖ := by
    change (1 - ‖K‖) * ‖(z : KP)‖ ≤
      ‖(z : KP) - K (z : KP)‖
    calc
      (1 - ‖K‖) * ‖(z : KP)‖ =
          ‖(z : KP)‖ - ‖K‖ * ‖(z : KP)‖ := by ring
      _ ≤ ‖(z : KP)‖ - ‖K (z : KP)‖ :=
        sub_le_sub_left (K.le_opNorm (z : KP)) _
      _ ≤ ‖(z : KP) - K (z : KP)‖ := norm_sub_norm_le _ _
  let c : ℝ := (1 - ‖K‖) / (‖canonicalL2Inclusion‖ + 1)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (sub_pos.mpr hKnorm) (by positivity)
  have hRlower (z : N) : c * ‖z‖ ≤ ‖R z‖ := by
    have hiBound :
        ‖J z‖ ≤ ‖canonicalL2Inclusion‖ * ‖R z‖ := by
      rw [← hiR]
      exact canonicalL2Inclusion.le_opNorm (R z)
    have hden : 0 < ‖canonicalL2Inclusion‖ + 1 := by positivity
    dsimp [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    calc
      (1 - ‖K‖) * ‖z‖ ≤ ‖J z‖ := hJlower z
      _ ≤ ‖canonicalL2Inclusion‖ * ‖R z‖ := hiBound
      _ ≤ (‖canonicalL2Inclusion‖ + 1) * ‖R z‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ = ‖R z‖ * (‖canonicalL2Inclusion‖ + 1) := by ring
  have hRanti : ∃ K₀, AntilipschitzWith K₀ R := by
    rw [antilipschitzWith_iff_exists_mul_le_norm]
    exact ⟨c, hc, hRlower⟩
  have hBKcompact : IsCompactOperator (B.comp K) :=
    hKcompact.clm_comp B
  have hBJNcompact :
      IsCompactOperator (B.comp J) := by
    have hsecond :
        IsCompactOperator ((B.comp K).comp N.subtypeL) :=
      hBKcompact.comp_clm N.subtypeL
    have heq :
        B.comp J =
          B.comp N.subtypeL - (B.comp K).comp N.subtypeL := by
      apply ContinuousLinearMap.ext
      intro z
      change B ((z : KP) - K (z : KP)) =
        B (z : KP) - B (K (z : KP))
      exact map_sub B (z : KP) (K (z : KP))
    rw [heq]
    exact hBNcompact.sub hsecond
  have hBiRcompact :
      IsCompactOperator ((B.comp canonicalL2Inclusion).comp R) := by
    have heq :
        (B.comp canonicalL2Inclusion).comp R = B.comp J := by
      rw [ContinuousLinearMap.comp_assoc, hiR]
    rw [heq]
    exact hBJNcompact
  exact ⟨N, hNclosed, hN, R, hRanti, hBiRcompact⟩

/-- Contrapositive form of the corrected CGP Proposition 5.3(c): if an
operator on the canonical Kalton--Peck space fails to be upper
semi-Fredholm, so does its restriction to the canonical Hilbert kernel. -/
theorem not_upperSemi_comp_canonicalL2Inclusion_of_not_upper
    (hq : IsStrictlySingular.{0, 0, 0, 0} canonicalL2Quotient)
    (B : KP →L[ℝ] KP) (hB : ¬ IsUpperSemiFredholm B) :
    ¬ IsUpperSemiFredholm (B.comp canonicalL2Inclusion) := by
  have hcompactRestriction :
      HasInfiniteDimensionalCompactRestriction B :=
    hasInfiniteDimensionalCompactRestriction_of_not_upper B hB
  obtain ⟨N, hNclosed, hN, R, hRanti, hcompact⟩ :=
    exists_compact_kernel_embedding_of_compactRestriction
      hq B hcompactRestriction
  letI : CompleteSpace N := hNclosed.completeSpace_coe
  rcases hRanti with ⟨K, hK⟩
  have hRinj : Function.Injective R := hK.injective
  have hRker : R.toLinearMap.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hRinj
  have hRkerFinite : FiniteDimensional ℝ R.toLinearMap.ker := by
    rw [hRker]
    infer_instance
  have hRrangeClosed :
      IsClosed (R.toLinearMap.range : Set H) :=
    hK.isClosed_range R.uniformContinuous
  have hRupper : IsUpperSemiFredholm R :=
    ⟨hRkerFinite, hRrangeClosed⟩
  intro hBi
  have hcompUpper :
      IsUpperSemiFredholm ((B.comp canonicalL2Inclusion).comp R) :=
    hRupper.comp hBi
  have hstrict :
      IsStrictlySingular ((B.comp canonicalL2Inclusion).comp R) :=
    isStrictlySingular_of_isCompactOperator _ hcompact
  exact (hcompUpper.not_isStrictlySingular hN) hstrict

/-- The corrected CGP compact-perturbation argument followed by Hilbert block extraction:
failure of upper semi-Fredholmness produces a compact canonical-kernel block. -/
theorem exists_compact_canonicalL2Block_of_not_upper
    (hq : IsStrictlySingular.{0, 0, 0, 0} canonicalL2Quotient)
    (B : KP →L[ℝ] KP) (hB : ¬ IsUpperSemiFredholm B) :
    ∃ w : ℕ → ℕ → ℝ,
      ∃ hw : IsSuccessiveNormalizedBlockSequence w,
        IsCompactOperator
          ((B.comp canonicalL2Inclusion).comp
            (canonicalL2BlockEmbedding w hw)) := by
  have hBi :
      ¬ IsUpperSemiFredholm (B.comp canonicalL2Inclusion) :=
    not_upperSemi_comp_canonicalL2Inclusion_of_not_upper hq B hB
  exact
    CgpBlockExtraction.exists_compact_canonicalL2Block_of_not_upperSemi
      (B.comp canonicalL2Inclusion) hBi

end Canonical

end

end KaltonPeck.Support.GraphFredholm

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
