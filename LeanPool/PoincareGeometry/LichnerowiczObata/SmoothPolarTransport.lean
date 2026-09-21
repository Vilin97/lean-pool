/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Propagating a smooth pole germ through smooth radial transport -/

@[expose] public noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {S : Type*} [TopologicalSpace S] [ChartedSpace H' S]

/-- For each finite order one may choose a smaller seed radius. Thus a
smooth germ at the pole, together with a smooth radial transport law,
proves smoothness of the fixed polar map at every regular radius. -/
theorem contMDiffAt_of_smooth_pole_transport
    (ι : S → P) (hι : ContMDiff J 𝓘(ℝ, P) ∞ ι)
    (χ : P → M) (hχ : ContMDiffAt 𝓘(ℝ, P) I ∞ χ 0)
    (Φ : S × ℝ → M) (η : M × ℝ → M) {δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L)
    (hseed : ∀ u s, s ∈ Ioo 0 δ → Φ (u, s) = χ (s • ι u))
    (hreset : ∀ u s r, s ∈ Ioo 0 L → r ∈ Ioo 0 L → Φ (u, r) = η (Φ (u, s), r))
    (hη : ∀ u s r, s ∈ Ioo 0 L → r ∈ Ioo 0 L →
      ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I ∞ η (Φ (u, s), r))
    (u : S) {r : ℝ} (hr : r ∈ Ioo 0 L) :
    ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) I ∞ Φ (u, r) := by
  apply contMDiffAt_iff_nat.mpr
  intro n _
  have hn : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hχn := hχ.of_le hn
  have hχnear : ∀ᶠ z in 𝓝 (0 : P), ContMDiffAt 𝓘(ℝ, P) I n χ z :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hχn
  have hc : Tendsto (fun s : ℝ => s • ι u) (𝓝 0) (𝓝 (0 : P)) := by
    have hh : Continuous (fun s : ℝ => s • ι u) := continuous_id.smul continuous_const
    simpa using hh.tendsto (0 : ℝ)
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp (hc.eventually hχnear)
  let s := min ε (min δ L) / 2
  have hm : 0 < min ε (min δ L) := lt_min hε (lt_min hδ hL)
  have hs : 0 < s := div_pos hm (by norm_num)
  have hsm : s < min ε (min δ L) := by dsimp [s]; linarith
  have hsε : s < ε := hsm.trans_le (min_le_left _ _)
  have hsδ : s < δ := hsm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsL : s < L := hsm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hχs : ContMDiffAt 𝓘(ℝ, P) I n χ (s • ι u) :=
    hsmall (by simpa [Real.dist_eq, abs_of_pos hs] using hsε)
  have hinput : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) n
      (fun q : S × ℝ => s • ι q.1) (u, r) :=
    ((s • ContinuousLinearMap.id ℝ P).contDiff.contMDiff (ι u)).comp (u, r)
      (((hι.of_le hn) u).comp (u, r) contMDiffAt_fst)
  have hχinput : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) I n
      (fun q : S × ℝ => χ (s • ι q.1)) (u, r) := hχs.comp (u, r) hinput
  have hηs : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I n η (χ (s • ι u), r) := by
    rw [← hseed u s ⟨hs, hsδ⟩]
    exact (hη u s r ⟨hs, hsL⟩ hr).of_le hn
  have hh := hηs.comp (u, r) (hχinput.prodMk contMDiffAt_snd)
  apply hh.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : S × ℝ in 𝓝 (u, r), q.2 ∈ Ioo 0 L :=
    continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hr)
  filter_upwards [hnear] with q hq
  exact (hreset q.1 s q.2 ⟨hs, hsL⟩ hq).trans
    (congrArg (fun x => η (x, q.2)) (hseed q.1 s ⟨hs, hsδ⟩))

end LichnerowiczObata
