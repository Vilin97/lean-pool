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
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingular
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Additive calculus for strictly singular operators

This file constructs controlled biorthogonal sequences for strictly singular operators and
proves closure under addition, real scalar multiplication, and negation.
-/


namespace KaltonPeck.Support.StrictlySingular

open Function Set Filter Topology

universe uX uY
universe uV

variable {X : Type uX} {Y : Type uY}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Failure to be bounded below produces a unit vector with arbitrarily small image. -/
theorem exists_unit_norm_apply_lt_of_not_boundedBelow
    (U : X →L[ℝ] Y) (hU : ¬ ∃ K, AntilipschitzWith K U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, ‖x‖ = 1 ∧ ‖U x‖ < ε := by
  rw [antilipschitzWith_iff_exists_mul_le_norm] at hU
  push Not at hU
  obtain ⟨x, hx⟩ := hU ε hε
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp at hx
  refine ⟨(‖x‖⁻¹ : ℝ) • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  rw [mul_comm]
  exact (div_lt_iff₀ (norm_pos_iff.mpr hx0)).2 (by simpa [mul_comm] using hx)

theorem ker_not_finiteDimensional_of_codomain_finiteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [CompleteSpace X]
    (hX : ¬ FiniteDimensional ℝ X) (f : X →L[ℝ] F) :
    ¬ FiniteDimensional ℝ f.toLinearMap.ker := by
  intro hker
  letI : FiniteDimensional ℝ f.toLinearMap.ker := hker
  let hc : f.toLinearMap.ker.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional f.toLinearMap.ker
  let Z : Submodule ℝ X := hc.complement
  have hcompl : Submodule.IsTopCompl f.toLinearMap.ker Z :=
    hc.isTopCompl_complement
  have hinj : Function.Injective (f.toLinearMap.domRestrict Z) := by
    intro z₁ z₂ hz
    apply Subtype.ext
    have hdiffker : (z₁ : X) - (z₂ : X) ∈ f.toLinearMap.ker := by
      change f ((z₁ : X) - (z₂ : X)) = 0
      rw [map_sub, sub_eq_zero]
      exact hz
    have hdiffZ : (z₁ : X) - (z₂ : X) ∈ Z :=
      Z.sub_mem z₁.property z₂.property
    have hdiffbot : (z₁ : X) - (z₂ : X) ∈ (⊥ : Submodule ℝ X) :=
      hcompl.isCompl.disjoint.le_bot ⟨hdiffker, hdiffZ⟩
    simpa only [Submodule.mem_bot, sub_eq_zero] using hdiffbot
  letI : FiniteDimensional ℝ Z :=
    FiniteDimensional.of_injective (f.toLinearMap.domRestrict Z) hinj
  have hprod : FiniteDimensional ℝ (f.toLinearMap.ker × Z) := inferInstance
  letI : FiniteDimensional ℝ X :=
    @LinearEquiv.finiteDimensional ℝ (f.toLinearMap.ker × Z) _ _ _
      X _ _ (Submodule.prodEquivOfIsCompl _ _ hcompl.isCompl) hprod
  exact hX inferInstance

theorem IsStrictlySingular.exists_unit_mem_ker_norm_apply_lt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [CompleteSpace X]
    (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    (f : X →L[ℝ] F) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, f x = 0 ∧ ‖x‖ = 1 ∧ ‖U x‖ < ε := by
  let V : Submodule ℝ X := f.toLinearMap.ker
  have hVclosed : IsClosed (V : Set X) := f.isClosed_ker
  letI : CompleteSpace V := hVclosed.completeSpace_coe
  have hV : ¬ FiniteDimensional ℝ V :=
    ker_not_finiteDimensional_of_codomain_finiteDimensional hX f
  have hsub : ∃ K, AntilipschitzWith K V.subtypeL :=
    ⟨1, by
      simpa [Submodule.subtypeₗᵢ_toContinuousLinearMap] using
        V.subtypeₗᵢ.antilipschitz⟩
  have hnot : ¬ ∃ K, AntilipschitzWith K (U.comp V.subtypeL) :=
    hU V hV V.subtypeL hsub
  obtain ⟨x, hxnorm, hxU⟩ :=
    exists_unit_norm_apply_lt_of_not_boundedBelow (U.comp V.subtypeL) hnot hε
  refine ⟨x, x.property, hxnorm, ?_⟩
  change ‖U (V.subtypeL x)‖ < ε
  simpa only [ContinuousLinearMap.comp_apply] using hxU

theorem IsStrictlySingular.exists_biorthogonal_extension
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {n : ℕ} (v : Fin n → X) (φ : Fin n → StrongDual ℝ X)
    (hvφ : ∀ i j, φ i (v j) = if i = j then 1 else 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ (x : X) (ψ : StrongDual ℝ X),
      ‖x‖ = 1 ∧
      (∀ i, φ i x = 0) ∧
      (∀ i, ψ (v i) = 0) ∧
      ψ x = 1 ∧
      ‖ψ‖ * ‖U x‖ < η := by
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
    IsStrictlySingular.exists_unit_mem_ker_norm_apply_lt
      hX hU eval (div_pos hη hC)
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
      ‖ψ‖ ≤ ‖g‖ * ‖(1 : X →L[ℝ] X) - P‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖(1 : X →L[ℝ] X) - P‖ := by rw [hgnorm, one_mul]
  refine ⟨x, ψ, hxnorm, hxφ, hψv, hψx, ?_⟩
  have hUnonneg : 0 ≤ ‖U x‖ := norm_nonneg _
  calc
    ‖ψ‖ * ‖U x‖ ≤ ‖(1 : X →L[ℝ] X) - P‖ * ‖U x‖ :=
      mul_le_mul_of_nonneg_right hψnorm hUnonneg
    _ ≤ C * ‖U x‖ := by
      apply mul_le_mul_of_nonneg_right _ hUnonneg
      dsimp [C]
      linarith
    _ < C * (η / C) := mul_lt_mul_of_pos_left hxsmall hC
    _ = η := by field_simp

/-- A finite normalized biorthogonal system whose weighted images under `U` are small. -/
structure BiorthogonalPrefix
    (U : X →L[ℝ] Y) (η : ℕ → ℝ) (n : ℕ) where
  /-- The vectors in the finite biorthogonal system. -/
  v : Fin n → X
  /-- The coordinate functionals in the finite biorthogonal system. -/
  φ : Fin n → StrongDual ℝ X
  /-- Every vector in the system is normalized. -/
  norm_v : ∀ i, ‖v i‖ = 1
  /-- The vectors and functionals are biorthogonal. -/
  bio : ∀ i j, φ i (v j) = if i = j then 1 else 0
  /-- Each weighted image is bounded by the prescribed error. -/
  small : ∀ i, ‖φ i‖ * ‖U (v i)‖ < η i

/-- The empty biorthogonal prefix. -/
def BiorthogonalPrefix.nil (U : X →L[ℝ] Y) (η : ℕ → ℝ) :
    BiorthogonalPrefix U η 0 where
  v := Fin.elim0
  φ := Fin.elim0
  norm_v := fun i => Fin.elim0 i
  bio := fun i => Fin.elim0 i
  small := fun i => Fin.elim0 i

/-- Extend a biorthogonal prefix by one vector with a prescribed small image. -/
noncomputable def BiorthogonalPrefix.snoc
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ}
    (p : BiorthogonalPrefix U η n) :
    BiorthogonalPrefix U η (n + 1) := by
  have hex :
      ∃ (x : X) (ψ : StrongDual ℝ X),
        ‖x‖ = 1 ∧
        (∀ i, p.φ i x = 0) ∧
        (∀ i, ψ (p.v i) = 0) ∧
        ψ x = 1 ∧
        ‖ψ‖ * ‖U x‖ < η n :=
    IsStrictlySingular.exists_biorthogonal_extension
      hX hU p.v p.φ p.bio (hη n)
  let x : X := Exists.choose hex
  let hψ := Exists.choose_spec hex
  let ψ : StrongDual ℝ X := Exists.choose hψ
  have hs := Exists.choose_spec hψ
  have hxnorm : ‖x‖ = 1 := hs.1
  have hxφ : ∀ i, p.φ i x = 0 := hs.2.1
  have hψv : ∀ i, ψ (p.v i) = 0 := hs.2.2.1
  have hψx : ψ x = 1 := hs.2.2.2.1
  have hxsmall : ‖ψ‖ * ‖U x‖ < η n := hs.2.2.2.2
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

/-- Recursively construct finite biorthogonal prefixes for a strictly singular operator. -/
noncomputable def biorthogonalPrefix
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) :
    (n : ℕ) → BiorthogonalPrefix U η n
  | 0 => BiorthogonalPrefix.nil U η
  | n + 1 => (biorthogonalPrefix hX hU hη n).snoc hX hU hη

theorem BiorthogonalPrefix.snoc_v_castSucc
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ}
    (p : BiorthogonalPrefix U η n) (i : Fin n) :
    (p.snoc hX hU hη).v i.castSucc = p.v i := by
  simp [BiorthogonalPrefix.snoc]

theorem BiorthogonalPrefix.snoc_φ_castSucc
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ}
    (p : BiorthogonalPrefix U η n) (i : Fin n) :
    (p.snoc hX hU hη).φ i.castSucc = p.φ i := by
  simp [BiorthogonalPrefix.snoc]

theorem biorthogonalPrefix_succ_v_castSucc
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ} (i : Fin n) :
    (biorthogonalPrefix hX hU hη (n + 1)).v i.castSucc =
      (biorthogonalPrefix hX hU hη n).v i := by
  rw [biorthogonalPrefix]
  exact BiorthogonalPrefix.snoc_v_castSucc hX hU hη _ i

theorem biorthogonalPrefix_succ_φ_castSucc
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {n : ℕ} (i : Fin n) :
    (biorthogonalPrefix hX hU hη (n + 1)).φ i.castSucc =
      (biorthogonalPrefix hX hU hη n).φ i := by
  rw [biorthogonalPrefix]
  exact BiorthogonalPrefix.snoc_φ_castSucc hX hU hη _ i

/-- The newest vector in the recursively constructed strictly-singular prefix. -/
noncomputable def strictlySingularBasicVector
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (n : ℕ) : X :=
  (biorthogonalPrefix hX hU hη (n + 1)).v (Fin.last n)

/-- The newest functional in the recursively constructed strictly-singular prefix. -/
noncomputable def strictlySingularBasicFunctional
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (n : ℕ) : StrongDual ℝ X :=
  (biorthogonalPrefix hX hU hη (n + 1)).φ (Fin.last n)

theorem biorthogonalPrefix_v_eq_basicVector
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n)
    (n : ℕ) (i : Fin (n + 1)) :
    (biorthogonalPrefix hX hU hη (n + 1)).v i =
      strictlySingularBasicVector hX hU hη i.val := by
  induction n with
  | zero =>
      have hi : i = Fin.last 0 := by ext; omega
      subst i
      rfl
  | succ n ih =>
      cases i using Fin.lastCases with
      | last => rfl
      | cast i =>
          rw [biorthogonalPrefix_succ_v_castSucc hX hU hη]
          exact ih i

theorem biorthogonalPrefix_φ_eq_basicFunctional
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n)
    (n : ℕ) (i : Fin (n + 1)) :
    (biorthogonalPrefix hX hU hη (n + 1)).φ i =
      strictlySingularBasicFunctional hX hU hη i.val := by
  induction n with
  | zero =>
      have hi : i = Fin.last 0 := by ext; omega
      subst i
      rfl
  | succ n ih =>
      cases i using Fin.lastCases with
      | last => rfl
      | cast i =>
          rw [biorthogonalPrefix_succ_φ_castSucc hX hU hη]
          exact ih i

theorem strictlySingularBasicVector_norm
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (n : ℕ) :
    ‖strictlySingularBasicVector hX hU hη n‖ = 1 := by
  exact (biorthogonalPrefix hX hU hη (n + 1)).norm_v (Fin.last n)

theorem strictlySingularBasic_biorthogonal
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (i j : ℕ) :
    strictlySingularBasicFunctional hX hU hη i
        (strictlySingularBasicVector hX hU hη j) =
      if i = j then 1 else 0 := by
  let N := i + j
  let ii : Fin (N + 1) := ⟨i, by dsimp [N]; omega⟩
  let jj : Fin (N + 1) := ⟨j, by dsimp [N]; omega⟩
  have h := (biorthogonalPrefix hX hU hη (N + 1)).bio ii jj
  rw [biorthogonalPrefix_φ_eq_basicFunctional hX hU hη N ii,
    biorthogonalPrefix_v_eq_basicVector hX hU hη N jj] at h
  simpa [ii, jj] using h

theorem strictlySingularBasic_small
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (n : ℕ) :
    ‖strictlySingularBasicFunctional hX hU hη n‖ *
        ‖U (strictlySingularBasicVector hX hU hη n)‖ < η n := by
  exact (biorthogonalPrefix hX hU hη (n + 1)).small (Fin.last n)

theorem IsStrictlySingular.exists_biorthogonal_sequence_summable
    [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X)
    {U : X →L[ℝ] Y} (hU : IsStrictlySingular.{0, uX, uY, uX} U) :
    ∃ (v : ℕ → X) (φ : ℕ → StrongDual ℝ X),
      (∀ n, ‖v n‖ = 1) ∧
      (∀ i j, φ i (v j) = if i = j then 1 else 0) ∧
      Summable (fun n => ‖U (v n)‖) ∧
      Summable (fun n => ‖φ n‖ * ‖U (v n)‖) := by
  let η : ℕ → ℝ := fun n => 1 / 2 / 2 ^ n
  have hη (n : ℕ) : 0 < η n := by
    dsimp [η]
    positivity
  let v : ℕ → X := strictlySingularBasicVector hX hU hη
  let φ : ℕ → StrongDual ℝ X := strictlySingularBasicFunctional hX hU hη
  have hvnorm (n : ℕ) : ‖v n‖ = 1 :=
    strictlySingularBasicVector_norm hX hU hη n
  have hbio (i j : ℕ) : φ i (v j) = if i = j then 1 else 0 :=
    strictlySingularBasic_biorthogonal hX hU hη i j
  have hsmall (n : ℕ) : ‖φ n‖ * ‖U (v n)‖ < η n :=
    strictlySingularBasic_small hX hU hη n
  have hηsum : Summable η := by
    simpa [η] using summable_geometric_two' (1 : ℝ)
  have hprod :
      Summable (fun n => ‖φ n‖ * ‖U (v n)‖) :=
    hηsum.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => (hsmall n).le)
  have hφnorm (n : ℕ) : 1 ≤ ‖φ n‖ := by
    have happly : ‖φ n (v n)‖ ≤ ‖φ n‖ * ‖v n‖ := (φ n).le_opNorm (v n)
    rw [hbio n n, if_pos rfl, norm_one, hvnorm n, mul_one] at happly
    exact happly
  have hUnorm (n : ℕ) : ‖U (v n)‖ ≤ ‖φ n‖ * ‖U (v n)‖ := by
    nlinarith [hφnorm n, norm_nonneg (U (v n))]
  have hU : Summable (fun n => ‖U (v n)‖) :=
    hprod.of_nonneg_of_le (fun n => norm_nonneg _) hUnorm
  exact ⟨v, φ, hvnorm, hbio, hU, hprod⟩

theorem biorthogonal_finsupp_coefficient
    {v : ℕ → X} {φ : ℕ → StrongDual ℝ X}
    (hbio : ∀ i j, φ i (v j) = if i = j then 1 else 0)
    (a : ℕ →₀ ℝ) (k : ℕ) :
    φ k (a.sum fun i c => c • v i) = a k := by
  classical
  simp [Finsupp.sum, map_sum, map_smul, hbio]
  all_goals aesop

theorem norm_apply_biorthogonal_finsupp_sum_le
    (U : X →L[ℝ] Y) {v : ℕ → X} {φ : ℕ → StrongDual ℝ X}
    (hbio : ∀ i j, φ i (v j) = if i = j then 1 else 0)
    (a : ℕ →₀ ℝ) :
    ‖U (a.sum fun i c => c • v i)‖ ≤
      ‖a.sum fun i c => c • v i‖ *
        ∑ i ∈ a.support, ‖φ i‖ * ‖U (v i)‖ := by
  classical
  let x : X := a.sum fun i c => c • v i
  have hcoeff (i : ℕ) : φ i x = a i :=
    biorthogonal_finsupp_coefficient hbio a i
  calc
    ‖U x‖ = ‖a.sum fun i c => c • U (v i)‖ := by
      congr 1
      simp only [x, map_finsuppSum, map_smul]
    _ ≤ ∑ i ∈ a.support, ‖a i • U (v i)‖ := by
      simp only [Finsupp.sum]
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ a.support, ‖x‖ * (‖φ i‖ * ‖U (v i)‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      have hcoef : |a i| ≤ ‖φ i‖ * ‖x‖ := by
        rw [← hcoeff i, ← Real.norm_eq_abs]
        exact (φ i).le_opNorm x
      calc
        |a i| * ‖U (v i)‖ ≤ (‖φ i‖ * ‖x‖) * ‖U (v i)‖ :=
          mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
        _ = ‖x‖ * (‖φ i‖ * ‖U (v i)‖) := by ring
    _ = ‖x‖ * ∑ i ∈ a.support, ‖φ i‖ * ‖U (v i)‖ := by
      rw [Finset.mul_sum]

theorem norm_apply_mem_topologicalClosure_span_le_tsum
    (U : X →L[ℝ] Y) {v : ℕ → X} {φ : ℕ → StrongDual ℝ X}
    (hbio : ∀ i j, φ i (v j) = if i = j then 1 else 0)
    (hsum : Summable (fun i => ‖φ i‖ * ‖U (v i)‖))
    {x : X} (hx : x ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure) :
    ‖U x‖ ≤ ‖x‖ * ∑' i, ‖φ i‖ * ‖U (v i)‖ := by
  let p : ℕ → ℝ := fun i => ‖φ i‖ * ‖U (v i)‖
  let d : ℝ := ∑' i, p i
  have hp (i : ℕ) : 0 ≤ p i := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hspan :
      (Submodule.span ℝ (Set.range v) : Set X) ⊆
        {z : X | ‖U z‖ ≤ ‖z‖ * d} := by
    intro z hz
    change z ∈ Submodule.span ℝ (Set.range v) at hz
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz
    obtain ⟨a, rfl⟩ := hz
    change ‖U (a.sum fun i c => c • v i)‖ ≤
      ‖a.sum fun i c => c • v i‖ * d
    calc
      ‖U (a.sum fun i c => c • v i)‖ ≤
          ‖a.sum fun i c => c • v i‖ *
            ∑ i ∈ a.support, p i := by
        exact norm_apply_biorthogonal_finsupp_sum_le U hbio a
      _ ≤ ‖a.sum fun i c => c • v i‖ * d := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact hsum.sum_le_tsum a.support (fun i _ => hp i)
  have hclosed : IsClosed {z : X | ‖U z‖ ≤ ‖z‖ * d} := by
    exact isClosed_le U.continuous.norm (continuous_norm.mul continuous_const)
  have hclosure :
      closure (Submodule.span ℝ (Set.range v) : Set X) ⊆
        {z : X | ‖U z‖ ≤ ‖z‖ * d} :=
    hclosed.closure_subset_iff.2 hspan
  exact hclosure hx

theorem linearIndependent_of_biorthogonal
    {v : ℕ → X} {φ : ℕ → StrongDual ℝ X}
    (hbio : ∀ i j, φ i (v j) = if i = j then 1 else 0) :
    LinearIndependent ℝ v := by
  rw [linearIndependent_iff]
  intro a ha
  apply Finsupp.ext
  intro k
  have hk := biorthogonal_finsupp_coefficient hbio a k
  change a.sum (fun i c => c • v i) = 0 at ha
  rw [ha, map_zero] at hk
  exact hk.symm

theorem not_finiteDimensional_topologicalClosure_span_of_biorthogonal
    [CompleteSpace X] {v : ℕ → X} {φ : ℕ → StrongDual ℝ X}
    (hbio : ∀ i j, φ i (v j) = if i = j then 1 else 0) :
    ¬ FiniteDimensional ℝ
      (Submodule.span ℝ (Set.range v)).topologicalClosure := by
  let M : Submodule ℝ X := (Submodule.span ℝ (Set.range v)).topologicalClosure
  let vM : ℕ → M := fun n =>
    ⟨v n, Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range_self n))⟩
  have hv : LinearIndependent ℝ v := linearIndependent_of_biorthogonal hbio
  have hvM : LinearIndependent ℝ vM := by
    apply LinearIndependent.of_comp M.subtype
    convert hv using 1
    funext n
    rfl
  intro hM
  letI : FiniteDimensional ℝ M := hM
  have hcard := hvM.lt_aleph0_of_finiteDimensional
  simp at hcard

/-- Over the real scalars, strictly singular operators are closed under addition. -/
theorem IsStrictlySingular.add
    {S T : X →L[ℝ] Y}
    (hS : IsStrictlySingular.{0, uX, uY, uV} S)
    (hT : IsStrictlySingular.{0, uX, uY, uV} T) :
    IsStrictlySingular.{0, uX, uY, uV} (S + T) := by
  intro Z _ _ _ hZ R _ hsum
  let U : Z →L[ℝ] Y := S.comp R
  let V : Z →L[ℝ] Y := T.comp R
  have hUstrict : IsStrictlySingular.{0, uV, uY, uV} U := by
    exact hS.precomp R
  have hVstrict : IsStrictlySingular.{0, uV, uY, uV} V := by
    exact hT.precomp R
  obtain ⟨v, φ, hvnorm, hbio, hUsum, hprodsum⟩ :=
    IsStrictlySingular.exists_biorthogonal_sequence_summable hZ hUstrict
  rw [antilipschitzWith_iff_exists_mul_le_norm] at hsum
  obtain ⟨c, hc, hsumLower⟩ := hsum
  let p : ℕ → ℝ := fun n => ‖φ n‖ * ‖U (v n)‖
  have hpnonneg (n : ℕ) : 0 ≤ p n :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hptend :
      Tendsto (fun N => ∑' n, p (n + N)) atTop (𝓝 0) :=
    _root_.tendsto_sum_nat_add p
  have hpevent : ∀ᶠ N in atTop, (∑' n, p (n + N)) < c :=
    hptend.eventually (Iio_mem_nhds hc)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hpevent)
  have htail : (∑' n, p (n + N)) < c := hN N le_rfl
  let vt : ℕ → Z := fun n => v (n + N)
  let φt : ℕ → StrongDual ℝ Z := fun n => φ (n + N)
  have hbiot (i j : ℕ) : φt i (vt j) = if i = j then 1 else 0 := by
    simpa [φt, vt] using hbio (i + N) (j + N)
  have hprodtail :
      Summable (fun n => ‖φt n‖ * ‖U (vt n)‖) := by
    have hpcomp : Summable (fun n => p (n + N)) :=
      hprodsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    simpa [p, φt, vt] using hpcomp
  let M : Submodule ℝ Z :=
    (Submodule.span ℝ (Set.range vt)).topologicalClosure
  have hMclosed : IsClosed (M : Set Z) :=
    Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace M := hMclosed.completeSpace_coe
  have hM : ¬ FiniteDimensional ℝ M := by
    exact not_finiteDimensional_topologicalClosure_span_of_biorthogonal hbiot
  have hsub : ∃ K, AntilipschitzWith K M.subtypeL :=
    ⟨1, by
      simpa [Submodule.subtypeₗᵢ_toContinuousLinearMap] using
        M.subtypeₗᵢ.antilipschitz⟩
  let d : ℝ := ∑' n, ‖φt n‖ * ‖U (vt n)‖
  have hdc : d < c := by
    simpa [d, p, φt, vt] using htail
  have hVlower (x : M) : (c - d) * ‖x‖ ≤ ‖V (x : Z)‖ := by
    have htotal := hsumLower (x : Z)
    have htotal' : c * ‖x‖ ≤ ‖U (x : Z) + V (x : Z)‖ := by
      simpa [U, V, ContinuousLinearMap.comp_apply] using htotal
    have htri : ‖U (x : Z) + V (x : Z)‖ ≤
        ‖U (x : Z)‖ + ‖V (x : Z)‖ :=
      norm_add_le _ _
    have hsmall : ‖U (x : Z)‖ ≤ ‖x‖ * d := by
      exact norm_apply_mem_topologicalClosure_span_le_tsum
        U hbiot hprodtail x.property
    nlinarith
  have hVanti : ∃ K, AntilipschitzWith K (V.comp M.subtypeL) := by
    rw [antilipschitzWith_iff_exists_mul_le_norm]
    exact ⟨c - d, sub_pos.mpr hdc, fun x => by
      change (c - d) * ‖x‖ ≤ ‖V (x : Z)‖
      exact hVlower x⟩
  exact hVstrict M hM M.subtypeL hsub hVanti

/-- Real scalar multiplication preserves strict singularity. -/
theorem IsStrictlySingular.smul
    {T : X →L[ℝ] Y} (hT : IsStrictlySingular.{0, uX, uY, uV} T)
    (c : ℝ) : IsStrictlySingular.{0, uX, uY, uV} (c • T) := by
  have h := hT.postcomp (c • (1 : Y →L[ℝ] Y))
  convert h using 1
  ext x
  simp

/-- Negation preserves strict singularity. -/
theorem IsStrictlySingular.neg
    {T : X →L[ℝ] Y} (hT : IsStrictlySingular.{0, uX, uY, uV} T) :
    IsStrictlySingular.{0, uX, uY, uV} (-T) := by
  rw [show -T = (-1 : ℝ) • T by ext x; simp]
  exact hT.smul (-1)

end KaltonPeck.Support.StrictlySingular

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
