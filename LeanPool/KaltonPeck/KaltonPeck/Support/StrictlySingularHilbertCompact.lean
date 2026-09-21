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
import LeanPool.KaltonPeck.KaltonPeck.Support.Symplectic
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularHilbert
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Strict singularity implies compactness on the canonical Hilbert space

This file proves that every strictly singular endomorphism of the canonical real Hilbert space
is compact by approximation with finite-dimensional compressions.
-/


namespace KaltonPeck.Support.StrictlySingular

noncomputable
section

open Coordinates Symplectic
open Function Set Filter Topology
open scoped lp

private structure HilbertLowerPrefix
    (H : CanonicalL2 →L[ℝ] CanonicalL2) (δ : ℝ) (n : ℕ) where
  v : Fin n → CanonicalL2
  norm_v : ∀ i, ‖v i‖ = 1
  orth_v : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0
  lower : ∀ i, δ < ‖H (v i)‖
  orth_map : ∀ i j, i ≠ j → inner ℝ (H (v i)) (H (v j)) = 0

private def HilbertLowerPrefix.nil
    (H : CanonicalL2 →L[ℝ] CanonicalL2) (δ : ℝ) :
    HilbertLowerPrefix H δ 0 where
  v := Fin.elim0
  norm_v := fun i => Fin.elim0 i
  orth_v := fun i => Fin.elim0 i
  lower := fun i => Fin.elim0 i
  orth_map := fun i => Fin.elim0 i

private def constraintSubspace
    {H : CanonicalL2 →L[ℝ] CanonicalL2} {δ : ℝ} {n : ℕ}
    (p : HilbertLowerPrefix H δ n) : Submodule ℝ CanonicalL2 :=
  Submodule.span ℝ (Set.range p.v) ⊔
    Submodule.span ℝ (Set.range fun i => H.adjoint (H (p.v i)))

private instance constraintSubspace_finiteDimensional
    {H : CanonicalL2 →L[ℝ] CanonicalL2} {δ : ℝ} {n : ℕ}
    (p : HilbertLowerPrefix H δ n) :
    FiniteDimensional ℝ (constraintSubspace p) := by
  change FiniteDimensional ℝ ↥
    ((Submodule.span ℝ (Set.range p.v) : Submodule ℝ CanonicalL2) ⊔
      (Submodule.span ℝ (Set.range fun i => H.adjoint (H (p.v i))) :
        Submodule ℝ CanonicalL2))
  have h₁ : FiniteDimensional ℝ (Submodule.span ℝ (Set.range p.v)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have h₂ : FiniteDimensional ℝ
      (Submodule.span ℝ (Set.range fun i => H.adjoint (H (p.v i)))) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  let : FiniteDimensional ℝ (Submodule.span ℝ (Set.range p.v)) := h₁
  let : FiniteDimensional ℝ
      (Submodule.span ℝ (Set.range fun i => H.adjoint (H (p.v i)))) := h₂
  infer_instance

private theorem HilbertLowerPrefix.exists_extension
    {H : CanonicalL2 →L[ℝ] CanonicalL2} {δ : ℝ} {n : ℕ}
    (p : HilbertLowerPrefix H δ n)
    (hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ δ < ‖H (x : CanonicalL2)‖) :
    ∃ x : CanonicalL2,
      ‖x‖ = 1 ∧
      δ < ‖H x‖ ∧
      (∀ i, inner ℝ (p.v i) x = 0) ∧
      (∀ i, inner ℝ (H (p.v i)) (H x) = 0) := by
  let M := constraintSubspace p
  obtain ⟨x, hxnorm, hxlower⟩ :=
    hlarge M (constraintSubspace_finiteDimensional p)
  refine ⟨x, hxnorm, hxlower, ?_, ?_⟩
  · intro i
    apply Submodule.inner_right_of_mem_orthogonal (K := M)
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      exact ⟨i, rfl⟩
    · exact x.property
  · intro i
    rw [← H.adjoint_inner_left]
    apply Submodule.inner_right_of_mem_orthogonal (K := M)
    · apply Submodule.mem_sup_right
      apply Submodule.subset_span
      exact ⟨i, rfl⟩
    · exact x.property

private noncomputable def HilbertLowerPrefix.snoc
    {H : CanonicalL2 →L[ℝ] CanonicalL2} {δ : ℝ} {n : ℕ}
    (p : HilbertLowerPrefix H δ n)
    (hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ δ < ‖H (x : CanonicalL2)‖) :
    HilbertLowerPrefix H δ (n + 1) := by
  let hex := p.exists_extension hlarge
  let x : CanonicalL2 := Classical.choose hex
  have hx := Classical.choose_spec hex
  exact
    { v := Fin.snoc p.v x
      norm_v := by
        intro i
        cases i using Fin.lastCases with
        | last => simpa [x] using hx.1
        | cast i => simpa using p.norm_v i
      orth_v := by
        intro i j hij
        cases i using Fin.lastCases with
        | last =>
            cases j using Fin.lastCases with
            | last => exact (hij rfl).elim
            | cast j =>
                rw [real_inner_comm]
                simpa [x] using hx.2.2.1 j
        | cast i =>
            cases j using Fin.lastCases with
            | last => simpa [x] using hx.2.2.1 i
            | cast j =>
                simp only [Fin.snoc_castSucc]
                apply p.orth_v i j
                intro h
                apply hij
                exact Fin.castSucc_inj.mpr h
      lower := by
        intro i
        cases i using Fin.lastCases with
        | last => simpa [x] using hx.2.1
        | cast i => simpa using p.lower i
      orth_map := by
        intro i j hij
        cases i using Fin.lastCases with
        | last =>
            cases j using Fin.lastCases with
            | last => exact (hij rfl).elim
            | cast j =>
                rw [real_inner_comm]
                simpa [x] using hx.2.2.2 j
        | cast i =>
            cases j using Fin.lastCases with
            | last => simpa [x] using hx.2.2.2 i
            | cast j =>
                simp only [Fin.snoc_castSucc]
                apply p.orth_map i j
                intro h
                apply hij
                exact Fin.castSucc_inj.mpr h }

private noncomputable def hilbertLowerPrefix
    (H : CanonicalL2 →L[ℝ] CanonicalL2) (δ : ℝ)
    (hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ δ < ‖H (x : CanonicalL2)‖) :
    (n : ℕ) → HilbertLowerPrefix H δ n
  | 0 => HilbertLowerPrefix.nil H δ
  | n + 1 => (hilbertLowerPrefix H δ hlarge n).snoc hlarge

private theorem HilbertLowerPrefix.snoc_v_castSucc
    {H : CanonicalL2 →L[ℝ] CanonicalL2} {δ : ℝ} {n : ℕ}
    (p : HilbertLowerPrefix H δ n)
    (hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ δ < ‖H (x : CanonicalL2)‖)
    (i : Fin n) :
    (p.snoc hlarge).v i.castSucc = p.v i := by
  simp [HilbertLowerPrefix.snoc]

private theorem hilbertLowerPrefix_succ_v_castSucc
    {H : CanonicalL2 →L[ℝ] CanonicalL2} {δ : ℝ}
    (hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ δ < ‖H (x : CanonicalL2)‖)
    {n : ℕ} (i : Fin n) :
    (hilbertLowerPrefix H δ hlarge (n + 1)).v i.castSucc =
      (hilbertLowerPrefix H δ hlarge n).v i := by
  rw [hilbertLowerPrefix]
  exact HilbertLowerPrefix.snoc_v_castSucc _ hlarge i

private noncomputable def hilbertLowerVector
    (H : CanonicalL2 →L[ℝ] CanonicalL2) (δ : ℝ)
    (hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ δ < ‖H (x : CanonicalL2)‖)
    (n : ℕ) : CanonicalL2 :=
  (hilbertLowerPrefix H δ hlarge (n + 1)).v (Fin.last n)

private theorem hilbertLowerPrefix_v_eq_vector
    {H : CanonicalL2 →L[ℝ] CanonicalL2} {δ : ℝ}
    (hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ δ < ‖H (x : CanonicalL2)‖)
    (n : ℕ) (i : Fin (n + 1)) :
    (hilbertLowerPrefix H δ hlarge (n + 1)).v i =
      hilbertLowerVector H δ hlarge i.val := by
  induction n with
  | zero =>
      have hi : i = Fin.last 0 := by ext; omega
      subst i
      rfl
  | succ n ih =>
      cases i using Fin.lastCases with
      | last => rfl
      | cast i =>
          rw [hilbertLowerPrefix_succ_v_castSucc hlarge]
          exact ih i

private theorem hilbertLowerVector_spec
    {H : CanonicalL2 →L[ℝ] CanonicalL2} {δ : ℝ}
    (hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ δ < ‖H (x : CanonicalL2)‖) :
    let v := hilbertLowerVector H δ hlarge
    (∀ n, ‖v n‖ = 1) ∧
      (∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0) ∧
      (∀ n, δ < ‖H (v n)‖) ∧
      (∀ i j, i ≠ j → inner ℝ (H (v i)) (H (v j)) = 0) := by
  let v := hilbertLowerVector H δ hlarge
  have hvnorm (n : ℕ) : ‖v n‖ = 1 :=
    (hilbertLowerPrefix H δ hlarge (n + 1)).norm_v (Fin.last n)
  have hvlower (n : ℕ) : δ < ‖H (v n)‖ :=
    (hilbertLowerPrefix H δ hlarge (n + 1)).lower (Fin.last n)
  have hvorth (i j : ℕ) (hij : i ≠ j) :
      inner ℝ (v i) (v j) = 0 := by
    let N := i + j
    let ii : Fin (N + 1) := ⟨i, by dsimp [N]; omega⟩
    let jj : Fin (N + 1) := ⟨j, by dsimp [N]; omega⟩
    have h :=
      (hilbertLowerPrefix H δ hlarge (N + 1)).orth_v ii jj (by
        intro h'
        apply hij
        exact Fin.mk.inj h')
    rw [hilbertLowerPrefix_v_eq_vector hlarge N ii,
      hilbertLowerPrefix_v_eq_vector hlarge N jj] at h
    exact h
  have hHorth (i j : ℕ) (hij : i ≠ j) :
      inner ℝ (H (v i)) (H (v j)) = 0 := by
    let N := i + j
    let ii : Fin (N + 1) := ⟨i, by dsimp [N]; omega⟩
    let jj : Fin (N + 1) := ⟨j, by dsimp [N]; omega⟩
    have h :=
      (hilbertLowerPrefix H δ hlarge (N + 1)).orth_map ii jj (by
        intro h'
        apply hij
        exact Fin.mk.inj h')
    rw [hilbertLowerPrefix_v_eq_vector hlarge N ii,
      hilbertLowerPrefix_v_eq_vector hlarge N jj] at h
    exact h
  exact ⟨hvnorm, hvorth, hvlower, hHorth⟩

private theorem not_strictlySingular_of_uniform_orthogonal_tail
    (H : CanonicalL2 →L[ℝ] CanonicalL2) {δ : ℝ} (hδ : 0 < δ)
    (hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ δ < ‖H (x : CanonicalL2)‖) :
    ¬ IsStrictlySingular.{0, 0, 0, 0} H := by
  let v := hilbertLowerVector H δ hlarge
  have hv := hilbertLowerVector_spec hlarge
  have hvon : Orthonormal ℝ v := ⟨hv.1, hv.2.1⟩
  let a : ℕ → ℝ := fun n => ‖H (v n)‖
  have ha_pos (n : ℕ) : 0 < a n := hδ.trans (hv.2.2.1 n)
  have ha_lower (n : ℕ) : δ < a n := hv.2.2.1 n
  have ha_upper (n : ℕ) : a n ≤ ‖H‖ := by
    dsimp only [a]
    calc
      ‖H (v n)‖ ≤ ‖H‖ * ‖v n‖ := H.le_opNorm _
      _ = ‖H‖ := by rw [hv.1 n, mul_one]
  let u : ℕ → CanonicalL2 := fun n => (a n)⁻¹ • H (v n)
  have hu_norm (n : ℕ) : ‖u n‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (ha_pos n),
      inv_mul_cancel₀ (ha_pos n).ne']
  have hu_orth (i j : ℕ) (hij : i ≠ j) :
      inner ℝ (u i) (u j) = 0 := by
    dsimp only [u]
    rw [inner_smul_left, inner_smul_right, hv.2.2.2 i j hij]
    simp
  have huon : Orthonormal ℝ u := ⟨hu_norm, hu_orth⟩
  let V : ℕ → ℝ →ₗᵢ[ℝ] CanonicalL2 :=
    fun n => LinearIsometry.toSpanSingleton ℝ CanonicalL2 (hvon.1 n)
  let U : ℕ → ℝ →ₗᵢ[ℝ] CanonicalL2 :=
    fun n => LinearIsometry.toSpanSingleton ℝ CanonicalL2 (huon.1 n)
  let Sli : CanonicalL2 →ₗᵢ[ℝ] CanonicalL2 :=
    hvon.orthogonalFamily.linearIsometry
  let Uli : CanonicalL2 →ₗᵢ[ℝ] CanonicalL2 :=
    huon.orthogonalFamily.linearIsometry
  let S : CanonicalL2 →L[ℝ] CanonicalL2 := Sli.toContinuousLinearMap
  let Umap : CanonicalL2 →L[ℝ] CanonicalL2 := Uli.toContinuousLinearMap
  let D : CanonicalL2 →L[ℝ] CanonicalL2 :=
    lp.mapCLM 2 (fun n => ContinuousLinearMap.toSpanSingleton ℝ (a n))
      (norm_nonneg H) (fun n => by
        simpa [abs_of_pos (ha_pos n)] using ha_upper n)
  have hinv_nonneg : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hinv_bound (n : ℕ) :
      ‖ContinuousLinearMap.toSpanSingleton ℝ ((a n)⁻¹)‖ ≤ δ⁻¹ := by
    rw [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs,
      abs_inv, abs_of_pos (ha_pos n)]
    exact (inv_le_inv₀ (ha_pos n) hδ).2 (ha_lower n).le
  let Dinv : CanonicalL2 →L[ℝ] CanonicalL2 :=
    lp.mapCLM 2 (fun n => ContinuousLinearMap.toSpanSingleton ℝ ((a n)⁻¹))
      hinv_nonneg hinv_bound
  have hDinvD : Dinv.comp D = 1 := by
    apply lp.ext_continuousLinearMap (p := (2 : ENNReal)) (by norm_num)
    intro n
    apply ContinuousLinearMap.ext
    intro c
    apply Subtype.ext
    funext k
    by_cases hkn : k = n
    · subst k
      simp [Dinv, D, lp.mapCLM, ContinuousLinearMap.toSpanSingleton_apply,
        lp.single_apply, ha_pos n |>.ne']
    · simp [Dinv, D, lp.mapCLM, ContinuousLinearMap.toSpanSingleton_apply,
        lp.single_apply, hkn]
  have hHS : H.comp S = Umap.comp D := by
    apply lp.ext_continuousLinearMap (p := (2 : ENNReal)) (by norm_num)
    intro n
    apply ContinuousLinearMap.ext
    intro c
    change
      H (Sli (lp.single 2 n c)) =
        Uli (D (lp.single 2 n c))
    rw [show Sli (lp.single 2 n c) = c • v n by
      exact hvon.orthogonalFamily.linearIsometry_apply_single c]
    rw [map_smul]
    have hDsingle :
        D (lp.single 2 n c) = lp.single 2 n (c * a n) := by
      apply Subtype.ext
      funext k
      by_cases hkn : k = n
      · subst k
        simp [D, lp.mapCLM, ContinuousLinearMap.toSpanSingleton_apply,
          lp.single_apply]
      · simp [D, lp.mapCLM, ContinuousLinearMap.toSpanSingleton_apply,
          lp.single_apply, hkn]
    rw [hDsingle]
    rw [show Uli (lp.single 2 n (c * a n)) = (c * a n) • u n by
      exact huon.orthogonalFamily.linearIsometry_apply_single (c * a n)]
    dsimp only [u]
    rw [smul_smul]
    have hainv : a n * (a n)⁻¹ = 1 := mul_inv_cancel₀ (ha_pos n).ne'
    rw [mul_assoc, hainv, mul_one]
  have hUadjU : Umap.adjoint.comp Umap = 1 := by
    exact Uli.adjoint_comp_self
  let L : CanonicalL2 →L[ℝ] CanonicalL2 :=
    Dinv.comp Umap.adjoint
  have hleft : L.comp (H.comp S) = 1 := by
    rw [hHS]
    simp only [L, ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc Umap.adjoint Umap D,
      hUadjU]
    exact hDinvD
  have hSanti : ∃ K, AntilipschitzWith K S :=
    ⟨1, by
      simpa [S, Sli] using Sli.antilipschitz⟩
  have hHSanti : ∃ K, AntilipschitzWith K (H.comp S) := by
    let c : ℝ := (‖L‖ + 1)⁻¹
    have hc : 0 < c := inv_pos.mpr (by positivity)
    rw [antilipschitzWith_iff_exists_mul_le_norm]
    refine ⟨c, hc, ?_⟩
    intro x
    have hx : x = L ((H.comp S) x) := by
      have := DFunLike.congr_fun hleft x
      simpa using this.symm
    have hcL : c * ‖L‖ ≤ 1 := by
      dsimp only [c]
      exact (inv_mul_le_one₀ (by positivity)).2 (by linarith [norm_nonneg L])
    calc
      c * ‖x‖ = c * ‖L ((H.comp S) x)‖ :=
        congrArg (fun y : ℝ => c * y) (congrArg norm hx)
      _ ≤ c * (‖L‖ * ‖(H.comp S) x‖) :=
        mul_le_mul_of_nonneg_left (L.le_opNorm _) hc.le
      _ = (c * ‖L‖) * ‖(H.comp S) x‖ := by ring
      _ ≤ 1 * ‖(H.comp S) x‖ :=
        mul_le_mul_of_nonneg_right hcL (norm_nonneg _)
      _ = ‖(H.comp S) x‖ := one_mul _
  intro hH
  exact hH CanonicalL2 canonicalL2_not_finiteDimensional S hSanti hHSanti

private theorem exists_finiteDimensional_orthogonal_tail_opNorm_lt
    (H : CanonicalL2 →L[ℝ] CanonicalL2)
    (hH : IsStrictlySingular.{0, 0, 0, 0} H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : Submodule ℝ CanonicalL2,
      FiniteDimensional ℝ M ∧ ‖H.domRestrict Mᗮ‖ < ε := by
  by_contra h
  push Not at h
  have hlarge :
      ∀ M : Submodule ℝ CanonicalL2,
        FiniteDimensional ℝ M →
          ∃ x : Mᗮ, ‖x‖ = 1 ∧ ε / 2 < ‖H (x : CanonicalL2)‖ := by
    intro M hM
    have hnorm : ε ≤ ‖H.domRestrict Mᗮ‖ := h M hM
    have hhalf : ε / 2 < ‖H.domRestrict Mᗮ‖ :=
      (half_lt_self hε).trans_le hnorm
    obtain ⟨x, hx⟩ :=
      (H.domRestrict Mᗮ).exists_mul_lt_of_lt_opNorm
        (by positivity : 0 ≤ ε / 2) hhalf
    have hxne : x ≠ 0 := by
      intro hxzero
      subst x
      simp at hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    let y : Mᗮ := ‖x‖⁻¹ • x
    refine ⟨y, ?_, ?_⟩
    · dsimp only [y]
      rw [norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hxpos, inv_mul_cancel₀ hxpos.ne']
    · change ε / 2 < ‖H (‖x‖⁻¹ • (x : CanonicalL2))‖
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hxpos]
      have hquot : ε / 2 < ‖H (x : CanonicalL2)‖ / ‖x‖ :=
        (lt_div_iff₀ hxpos).2 (by simpa [mul_comm] using hx)
      calc
        ε / 2 < ‖H (x : CanonicalL2)‖ / ‖x‖ := hquot
        _ = ‖x‖⁻¹ * ‖H (x : CanonicalL2)‖ := by
          rw [div_eq_mul_inv, mul_comm]
  exact (not_strictlySingular_of_uniform_orthogonal_tail H (half_pos hε) hlarge) hH

private theorem exists_compact_opNorm_approximation
    (H : CanonicalL2 →L[ℝ] CanonicalL2)
    (hH : IsStrictlySingular.{0, 0, 0, 0} H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : CanonicalL2 →L[ℝ] CanonicalL2,
      IsCompactOperator K ∧ dist H K < ε := by
  obtain ⟨M, hM, htail⟩ :=
    exists_finiteDimensional_orthogonal_tail_opNorm_lt H hH hε
  let : FiniteDimensional ℝ M := hM
  let K : CanonicalL2 →L[ℝ] CanonicalL2 :=
    H.comp M.starProjection
  have hproj : IsCompactOperator M.orthogonalProjectionOnto :=
    isCompactOperator_of_locallyCompactSpace_dom M.orthogonalProjectionOnto
  have hK : IsCompactOperator K := by
    exact (hproj.clm_comp M.subtypeL).clm_comp H
  refine ⟨K, hK, ?_⟩
  have hdiff :
      H - K =
        (H.domRestrict Mᗮ).comp Mᗮ.orthogonalProjectionOnto := by
    apply ContinuousLinearMap.ext
    intro x
    change H x - H (M.starProjection x) =
      H (Mᗮ.orthogonalProjectionOnto x)
    rw [← map_sub, Submodule.orthogonalProjectionOnto_orthogonal]
  rw [dist_eq_norm, hdiff]
  calc
    ‖(H.domRestrict Mᗮ).comp Mᗮ.orthogonalProjectionOnto‖ ≤
        ‖H.domRestrict Mᗮ‖ * ‖Mᗮ.orthogonalProjectionOnto‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖H.domRestrict Mᗮ‖ * 1 := by
      gcongr
      exact Mᗮ.orthogonalProjectionOnto_norm_le
    _ < ε := by simpa using htail

/-- On the canonical real Hilbert space, strict singularity implies compactness. -/
theorem canonicalL2_isCompact_of_isStrictlySingular
    (H : CanonicalL2 →L[ℝ] CanonicalL2)
    (hH : IsStrictlySingular.{0, 0, 0, 0} H) :
    IsCompactOperator H := by
  have hclosure :
      H ∈ closure
        {K : CanonicalL2 →L[ℝ] CanonicalL2 | IsCompactOperator K} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨K, hK, hdist⟩ :=
      exists_compact_opNorm_approximation H hH hε
    exact ⟨K, hK, hdist⟩
  exact isClosed_setOfPred_isCompactOperator.closure_subset hclosure

end

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
