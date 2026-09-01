/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.ExactOrder

/-!
# Edge cases of classical complex Weierstrass preparation

The degree-zero case is independent of analytic division: the distinguished
polynomial is `1`, so the original analytic germ is the unit.
-/

open Filter
open scoped Topology


namespace ClassicalComplexWPT

@[simp]
theorem preparedPolynomial_zero {n : ℕ} (a : Fin 0 → Base n → ℂ) (x : Ambient n) :
    preparedPolynomial 0 a x = 1 := by
  simp [preparedPolynomial]

/-- Degree-zero preparation, including uniqueness of the empty coefficient family and the unit. -/
theorem classicalComplexWeierstrassPreparation_zero
    {n : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f 0) :
    ∃ (a : Fin 0 → Base n → ℂ) (u : Ambient n → ℂ),
      IsWeierstrassPreparation f 0 a u ∧
      ∀ (a' : Fin 0 → Base n → ℂ) (u' : Ambient n → ℂ),
        IsWeierstrassPreparation f 0 a' u' →
        (∀ i, a i =ᶠ[𝓝 0] a' i) ∧ u =ᶠ[𝓝 0] u' := by
  refine ⟨fun i ↦ Fin.elim0 i, f, ?_, ?_⟩
  · refine ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, hf, ?_, ?_⟩
    · exact exactOrderInLastVariable_zero_iff.mp horder
    · filter_upwards
      simp
  · intro a' u' hu'
    refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
    simpa using hu'.2.2.2.2

/--
When there are no base variables, preparation is precisely the univariate
exact-order factorization.  This proves the full public existence-and-
uniqueness conclusion for every degree `d` when `n = 0`.
-/
theorem classicalComplexWeierstrassPreparation_noBase
    {d : ℕ} {f : Ambient 0 → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base 0 → ℂ) (u : Ambient 0 → ℂ),
      IsWeierstrassPreparation f d a u ∧
      ∀ (a' : Fin d → Base 0 → ℂ) (u' : Ambient 0 → ℂ),
        IsWeierstrassPreparation f d a' u' →
        (∀ i, a i =ᶠ[𝓝 0] a' i) ∧ u =ᶠ[𝓝 0] u' := by
  obtain ⟨v, hv, hv0, heq⟩ := exists_lastSlice_eq_pow_mul hf horder
  let a : Fin d → Base 0 → ℂ := fun _ _ ↦ 0
  let u : Ambient 0 → ℂ := fun x ↦ v x.2
  have hu : AnalyticAt ℂ u 0 := by
    have hcomp := hv.comp (f := fun x : Ambient 0 ↦ x.2)
      (analyticAt_snd : AnalyticAt ℂ (fun x : Ambient 0 ↦ x.2) 0)
    simpa [u, Function.comp_def] using hcomp
  have heqAmbient : f =ᶠ[𝓝 0] fun x ↦ u x * preparedPolynomial d a x := by
    have hpull := heq.comp_tendsto (continuousAt_snd :
      Tendsto (fun x : Ambient 0 ↦ x.2) (𝓝 0) (𝓝 0))
    filter_upwards [hpull] with x hx
    have hx0 : x.1 = 0 := Subsingleton.elim _ _
    have hxp : x = (0, x.2) := by ext <;> simp [hx0]
    rw [hxp]
    simpa [Function.comp_def, lastSlice, u, a, preparedPolynomial, hx0, mul_comm] using hx
  refine ⟨a, u, ⟨fun _ ↦ analyticAt_const, fun _ ↦ rfl, hu, ?_, heqAmbient⟩, ?_⟩
  · simpa [u] using hv0
  · intro a' u' h'
    have ha'0 := h'.2.1
    have hu' := h'.2.2.1
    have heq' := h'.2.2.2.2
    refine ⟨?_, ?_⟩
    · intro i
      filter_upwards [] with z
      have hz : z = 0 := Subsingleton.elim _ _
      simpa [a, hz] using (ha'0 i).symm
    · let v' : ℂ → ℂ := fun w ↦ u' (0, w)
      have hv' : AnalyticAt ℂ v' 0 := by
        simpa [v'] using hu'.curry_right
      let emb : ℂ → Ambient 0 := fun w ↦ (0, w)
      have hemb : Tendsto emb (𝓝 0) (𝓝 0) := by
        have hc : ContinuousAt emb 0 := by
          simpa [emb] using (continuousAt_const.prodMk continuousAt_id :
            ContinuousAt (fun w : ℂ ↦ ((0 : Base 0), w)) 0)
        rw [show (0 : Ambient 0) = emb 0 by
          apply Prod.ext
          · exact Subsingleton.elim _ _
          · rfl]
        exact hc
      have heq'Slice0 := heq'.comp_tendsto hemb
      have hcoeff : ∀ (i : Fin d) (z : Base 0), a' i z = 0 := by
        intro i z
        rw [Subsingleton.elim z 0]
        exact ha'0 i
      have heq'Slice : lastSlice f =ᶠ[𝓝 0] fun w ↦ v' w * w ^ d := by
        filter_upwards [heq'Slice0] with w hw
        simpa [Function.comp_def, emb, lastSlice, v', preparedPolynomial, hcoeff] using hw
      have hcancel : ∀ᶠ w in 𝓝[≠] 0, v w = v' w := by
        filter_upwards [heq.filter_mono nhdsWithin_le_nhds,
          heq'Slice.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
          with w hw hw' hw0
        have hw_ne : w ≠ 0 := by simpa using hw0
        apply mul_left_cancel₀ (pow_ne_zero d hw_ne)
        calc
          w ^ d * v w = lastSlice f w := hw.symm
          _ = v' w * w ^ d := hw'
          _ = w ^ d * v' w := mul_comm _ _
      have hvv' : v =ᶠ[𝓝 0] v' :=
        (hv.frequently_eq_iff_eventually_eq hv').1 hcancel.frequently
      have hpull := hvv'.comp_tendsto (continuousAt_snd :
        Tendsto (fun x : Ambient 0 ↦ x.2) (𝓝 0) (𝓝 0))
      filter_upwards [hpull] with x hx
      have hx0 : x.1 = 0 := Subsingleton.elim _ _
      have hxp : x = (0, x.2) := by ext <;> simp [hx0]
      rw [hxp]
      simpa [Function.comp_def, u, v', hx0] using hx

end ClassicalComplexWPT
