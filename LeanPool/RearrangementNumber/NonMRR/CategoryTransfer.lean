/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import LeanPool.RearrangementNumber.NonMRR.Category
public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Transferring category from binary sequences to the real line

Binary expansion is a continuous map from the space of binary sequences onto
the unit interval. Each nonempty open set of sequences has an image with
nonempty real interior. This suffices to preserve nonmeagreness of images;
injectivity and an identification of the spaces are unnecessary.
-/

@[expose] public section

open Set Filter Finset Cardinal Topology

namespace NonMRR

universe u

/-- A continuous map whose nonempty open images have nonempty interior pulls
meagre sets back to meagre sets. -/
theorem tendsto_residual_of_image_interior
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    (himage : ∀ U : Set X, IsOpen U → U.Nonempty → (interior (f '' U)).Nonempty) :
    Tendsto f (residual X) (residual Y) := by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro V ⟨hVopen, hVdense⟩
  apply residual_of_dense_open (hVopen.preimage hf)
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨y, hyimage, hyV⟩ :=
    hVdense.inter_open_nonempty (interior (f '' U)) isOpen_interior (himage U hU hUne)
  obtain ⟨x, hxU, rfl⟩ := interior_subset hyimage
  exact ⟨x, hxU, hyV⟩

/-- Category-preserving maps give the corresponding inequality of uniformities. -/
theorem nonMeagreCardinal_le_of_tendsto_residual
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [Nonempty X]
    (f : X → Y) (hf : Tendsto f (residual X) (residual Y)) :
    nonMeagreCardinal Y ≤ nonMeagreCardinal X := by
  obtain ⟨s, hs, hcard⟩ := exists_nonmeagre_minimizer X
  have himage : ¬ IsMeagre (f '' s) := by
    intro h
    have hpre : IsMeagre (f ⁻¹' (f '' s)) := hf h
    exact hs (hpre.mono (subset_preimage_image f s))
  calc
    nonMeagreCardinal Y ≤ #(f '' s) := nonMeagreCardinal_le_mk himage
    _ ≤ #s := Cardinal.mk_image_le
    _ = nonMeagreCardinal X := hcard

/-- Fixing any finite binary prefix still leaves a nondegenerate real interval
in its image under binary expansion. -/
theorem binary_ofDigits_image_interior_nonempty
    (U : Set (ℕ → Fin 2)) (hU : IsOpen U) (hUne : U.Nonempty) :
    (interior (Real.ofDigits '' U)).Nonempty := by
  classical
  obtain ⟨f, hf⟩ := hUne
  obtain ⟨I, v, hv, hsub⟩ := isOpen_pi_iff.mp hU f hf
  let N : ℕ := I.sup id + 1
  let c : ℝ := ∑ i ∈ range N, Real.ofDigitsTerm f i
  let d : ℝ := ((2 : ℝ) ^ N)⁻¹
  have hd : 0 < d := by dsimp [d]; positivity
  have hinterval : Ioo c (c + d) ⊆ Real.ofDigits '' U := by
    intro x hx
    let y : ℝ := (x - c) / d
    have hy : y ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact (div_nonneg (sub_nonneg.mpr hx.1.le) hd.le)
      · exact (div_lt_one hd).mpr (by linarith [hx.2])
    let tail : ℕ → Fin 2 := Real.digits y 2
    have htailValue : Real.ofDigits tail = y :=
      Real.ofDigits_digits (by norm_num) hy
    let a : ℕ → Fin 2 := fun i ↦ if i < N then f i else tail (i - N)
    have haU : a ∈ U := by
      apply hsub
      intro i hi
      have hin : i < N := by
        have hle := Finset.le_sup (f := id) hi
        change i ≤ I.sup id at hle
        dsimp [N]
        omega
      simpa only [a, ite_eq_left hin] using (hv i hi).2
    refine ⟨a, haU, ?_⟩
    have hprefix : ∑ i ∈ range N, Real.ofDigitsTerm a i = c := by
      apply sum_congr rfl
      intro i hi
      simp only [Real.ofDigitsTerm, a, ite_eq_left (mem_range.mp hi)]
    have htail : (fun i ↦ a (i + N)) = tail := by
      funext i
      simp [a]
    rw [Real.ofDigits_eq_sum_add_ofDigits a N, hprefix, htail, htailValue]
    change c + d * ((x - c) / d) = x
    field_simp
    ring
  have hin : Ioo c (c + d) ⊆ interior (Real.ofDigits '' U) :=
    interior_maximal hinterval isOpen_Ioo
  exact ⟨c + d / 2, hin ⟨by linarith, by linarith⟩⟩

/-- The literal real uniformity is at most the uniformity on binary digit space. -/
theorem nonM_le_nonMeagreCardinal_finTwo :
    nonM ≤ nonMeagreCardinal (ℕ → Fin 2) := by
  apply nonMeagreCardinal_le_of_tendsto_residual (Real.ofDigits (b := 2))
  exact tendsto_residual_of_image_interior _ Real.continuous_ofDigits
    binary_ofDigits_image_interior_nonempty

/-- The coordinatewise identification of Boolean sequences with binary digits. -/
def boolSequenceHomeomorphFinTwo : (ℕ → Bool) ≃ₜ (ℕ → Fin 2) :=
  Homeomorph.piCongrRight (fun _ ↦ Homeomorph.ofDiscrete finTwoEquiv.symm)

/-- Category on Cantor space bounds category on the actual real line. -/
theorem nonM_le_nonMeagreCardinal_bool :
    nonM ≤ nonMeagreCardinal (ℕ → Bool) := by
  apply nonM_le_nonMeagreCardinal_finTwo.trans
  apply nonMeagreCardinal_le_of_tendsto_residual boolSequenceHomeomorphFinTwo
  exact tendsto_residual_of_isOpenMap boolSequenceHomeomorphFinTwo.continuous
    boolSequenceHomeomorphFinTwo.isOpenMap

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
