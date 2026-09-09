/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveEdgeExtension
import LeanPool.NavierStokesAndEuler.NavierStokes.NativeBandExtension
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Literal flat dyadic products from locally bounded interior jets

The unmasked factor is smooth only in the open dyadic band.  Its actual
interior jets are locally bounded at each face.  Flatness of the fixed cutoff
then proves smoothness and vanishing of all jets of the literal product,
without assigning new values to the unmasked factor outside the band.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.FlatDyadicExtension

open Set Function Filter
open WaveEdgeExtension (window windowDomain extension extendedJets)
open scoped Topology ContDiff BigOperators

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

/-- The constant and neighborhood may depend on the face point and finite
jet order.  Values and derivatives of `g` outside the open band are unused. -/
def LocalJetBounds (Ω : Set D) (q : D → ℝ) (g : D → E) : Prop :=
  ∀ x ∈ Ω, q x = 1 / 2 ∨ q x = 2 → ∀ m : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x,
      y ∈ windowDomain Ω q (1 / 2) 2 →
        ∀ j : ℕ, j ≤ m → ‖iteratedFDeriv ℝ j g y‖ ≤ C

theorem tensor_hasFDerivAt {f : D → E} {x : D} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    HasFDerivAt (iteratedFDeriv ℝ n f) (iteratedFDeriv ℝ (n + 1) f x).curryLeft x := by
  have hi : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) x :=
    hf.iteratedFDeriv_right (by exact_mod_cast (le_top : 1 + (n : ℕ∞) ≤ ⊤))
  have hd := (hi.differentiableAt (by simp)).hasFDerivAt
  simp only [fderiv_iteratedFDeriv, Function.comp_apply] at hd
  exact hd

/-- One extra zero tensor makes each flat jet little-o of ambient distance. -/
theorem flat_jet_isLittleO {f : D → E} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    (hz : ∀ n : ℕ, iteratedFDeriv ℝ n f x = 0) (n : ℕ) :
    (iteratedFDeriv ℝ n f) =o[𝓝 x] (fun y => y - x) := by
  have hcurry : (0 : D[×(n + 1)]→L[ℝ] E).curryLeft = 0 := by
    ext u v
    rfl
  have hd : HasFDerivAt (iteratedFDeriv ℝ n f) (0 : D →L[ℝ] (D[×n]→L[ℝ] E)) x := by
    have ht := tensor_hasFDerivAt hf n
    rw [hz (n + 1), hcurry] at ht
    exact ht
  rw [hasFDerivAt_iff_isLittleO] at hd
  simpa only [hz n, _root_.zero_apply, sub_zero] using
    hd

/-- A flat smooth scalar times a factor with locally bounded interior jets
has little-o interior product jets.  Zero extension needs no source values
or source regularity on the other side of the boundary. -/
theorem product_jet_extension_isLittleO {Ω : Set D} (hΩ : IsOpen Ω)
    {q φ : D → ℝ} (hq : ContinuousOn q Ω) (hφ : ContDiffOn ℝ ∞ φ Ω)
    {a b : ℝ} {g : D → E} (hg : ContDiffOn ℝ ∞ g (windowDomain Ω q a b))
    {x : D} (hx : x ∈ Ω) (hflat : ∀ n : ℕ, iteratedFDeriv ℝ n φ x = 0)
    (m : ℕ)
    (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x,
      y ∈ windowDomain Ω q a b → ∀ j : ℕ, j ≤ m → ‖iteratedFDeriv ℝ j g y‖ ≤ C) :
    extension q a b (iteratedFDeriv ℝ m (fun y => φ y • g y))
      =o[𝓝 x] (fun y => y - x) := by
  obtain ⟨C, hC, hb⟩ := hB
  let M : ℝ := C + 1
  have hM : 0 < M := by dsimp [M]; linarith
  have hCM : C ≤ M := by dsimp [M]; linarith
  have hU := WaveEdgeExtension.windowDomain_open hΩ hq a b
  have hφx := hφ.contDiffAt (hΩ.mem_nhds hx)
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let δ : ℝ := ε / ((2 : ℝ) ^ m * M)
  have hden : 0 < (2 : ℝ) ^ m * M := mul_pos (pow_pos (by norm_num) _) hM
  have hδ : 0 < δ := div_pos hε hden
  have hsmall : ∀ᶠ y in 𝓝 x, ∀ j ∈ Finset.range (m + 1),
      ‖iteratedFDeriv ℝ j φ y‖ ≤ δ * ‖y - x‖ :=
    (eventually_all_finset _).2 (fun j _ => (flat_jet_isLittleO hφx hflat j).bound hδ)
  filter_upwards [hΩ.mem_nhds hx, hb, hsmall] with y hyΩ hby hsy
  by_cases hy : y ∈ window q a b
  · rw [WaveEdgeExtension.extension_inside q a b _ hy]
    have hyU : y ∈ windowDomain Ω q a b := ⟨hyΩ, hy⟩
    change IsOpen (Ω ∩ window q a b) at hU
    change y ∈ Ω ∩ window q a b at hyU
    have hprod := norm_iteratedFDerivWithin_smul_le
      (hφ.mono (inter_subset_left (t := window q a b))) hg hU.uniqueDiffOn hyU
      (n := m) (nat_le_infty m)
    simp only [iteratedFDerivWithin_of_isOpen _ hU hyU] at hprod
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j φ y‖ * ‖iteratedFDeriv ℝ (m - j) g y‖ := hprod
      _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (δ * ‖y - x‖) * M := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hsy j hj) (Nat.cast_nonneg _))
          ((hby hyU (m - j) (Nat.sub_le _ _)).trans hCM)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hδ.le (norm_nonneg _)))
      _ = (2 : ℝ) ^ m * (δ * ‖y - x‖) * M := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hchoose : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = (2 : ℝ) ^ m := by
          exact_mod_cast Nat.sum_range_choose m
        rw [hchoose]
      _ = (δ * ((2 : ℝ) ^ m * M)) * ‖y - x‖ := by ring
      _ = ε * ‖y - x‖ := by rw [div_mul_cancel₀ ε hden.ne']
  · rw [WaveEdgeExtension.extension_outside q a b _ hy, norm_zero]
    exact mul_nonneg hε.le (norm_nonneg _)

/-! ## A Taylor family for the literal window extension -/

/-- Small O jets, given by `∀ n : ℕ, ∀ x ∈ Ω, q x = a ∨ q x = b → extension q a b
(iteratedFDeriv ℝ n f) =o[𝓝 x] (fun y => y - x)`. -/
def SmallOJets (Ω : Set D) (q : D → ℝ) (a b : ℝ) (f : D → E) : Prop :=
  ∀ n : ℕ, ∀ x ∈ Ω, q x = a ∨ q x = b →
    extension q a b (iteratedFDeriv ℝ n f) =o[𝓝 x] (fun y => y - x)

theorem hasFDerivAt_extension_zero {q : D → ℝ} {a b : ℝ} {f : D → E} {x : D}
    (hx : x ∉ window q a b)
    (hf : extension q a b f =o[𝓝 x] (fun y => y - x)) :
    HasFDerivAt (extension q a b f) (0 : D →L[ℝ] E) x := by
  rw [hasFDerivAt_iff_isLittleO]
  simpa only [WaveEdgeExtension.extension_outside q a b f hx,
    _root_.zero_apply, sub_zero] using hf

theorem extendedJets_hasFDerivAt {Ω : Set D} (hΩ : IsOpen Ω) {q : D → ℝ}
    (hq : ContinuousOn q Ω) {a b : ℝ} {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω q a b))
    (hB : SmallOJets Ω q a b f) (n : ℕ) {x : D} (hx : x ∈ Ω) :
    HasFDerivAt (fun y => extendedJets q a b f y n)
      (extendedJets q a b f x (n + 1)).curryLeft x := by
  have hqc := (hq x hx).continuousAt (hΩ.mem_nhds hx)
  change HasFDerivAt (extension q a b (iteratedFDeriv ℝ n f))
    (extension q a b (iteratedFDeriv ℝ (n + 1) f) x).curryLeft x
  have hcurry : (0 : D[×(n + 1)]→L[ℝ] E).curryLeft = 0 := by
    ext u v
    rfl
  rcases lt_trichotomy (q x) a with hleft | heq | hleft
  · have hn : x ∉ window q a b := fun h => (not_lt_of_ge hleft.le) h.1
    rw [WaveEdgeExtension.extension_outside q a b _ hn, hcurry]
    exact (hasFDerivAt_const (0 : D[×n]→L[ℝ] E) x).congr_of_eventuallyEq
      (WaveEdgeExtension.extension_germ_left a b _ hqc hleft)
  · have hn : x ∉ window q a b := fun h => (not_lt_of_ge heq.le) h.1
    rw [WaveEdgeExtension.extension_outside q a b _ hn, hcurry]
    exact hasFDerivAt_extension_zero hn (hB n x hx (Or.inl heq))
  · rcases lt_trichotomy (q x) b with hright | heq | hright
    · have hin : x ∈ window q a b := ⟨hleft, hright⟩
      rw [WaveEdgeExtension.extension_inside q a b _ hin]
      have hd := tensor_hasFDerivAt
        (hf.contDiffAt ((WaveEdgeExtension.windowDomain_open hΩ hq a b).mem_nhds ⟨hx, hin⟩)) n
      exact hd.congr_of_eventuallyEq (WaveEdgeExtension.extension_germ_inside a b _ hqc hin)
    · have hn : x ∉ window q a b := fun h => (not_lt_of_ge heq.ge) h.2
      rw [WaveEdgeExtension.extension_outside q a b _ hn, hcurry]
      exact hasFDerivAt_extension_zero hn (hB n x hx (Or.inr heq))
    · have hn : x ∉ window q a b := fun h => (not_lt_of_ge hright.le) h.2
      rw [WaveEdgeExtension.extension_outside q a b _ hn, hcurry]
      exact (hasFDerivAt_const (0 : D[×n]→L[ℝ] E) x).congr_of_eventuallyEq
        (WaveEdgeExtension.extension_germ_right a b _ hqc hright)

theorem hasFTaylorSeriesUpToOn_extension {Ω : Set D} (hΩ : IsOpen Ω) {q : D → ℝ}
    (hq : ContinuousOn q Ω) {a b : ℝ} {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω q a b)) (hB : SmallOJets Ω q a b f) :
    HasFTaylorSeriesUpToOn ∞ (extension q a b f) (extendedJets q a b f) Ω := by
  classical
  constructor
  · intro x hx
    by_cases hi : x ∈ window q a b
    · simp only [extendedJets, extension, ite_eq_left hi]
      rfl
    · simp only [extendedJets, extension, ite_eq_right hi]
      rfl
  · intro n _ x hx
    exact (extendedJets_hasFDerivAt hΩ hq hf hB n hx).hasFDerivWithinAt
  · intro n _ x hx
    exact (extendedJets_hasFDerivAt hΩ hq hf hB n hx).continuousAt.continuousWithinAt

theorem iteratedFDeriv_extension {Ω : Set D} (hΩ : IsOpen Ω) {q : D → ℝ}
    (hq : ContinuousOn q Ω) {a b : ℝ} {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω q a b)) (hB : SmallOJets Ω q a b f)
    (n : ℕ) {x : D} (hx : x ∈ Ω) :
    iteratedFDeriv ℝ n (extension q a b f) x = extension q a b (iteratedFDeriv ℝ n f) x := by
  have h := hasFTaylorSeriesUpToOn_extension hΩ hq hf hB
  have he := (h.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le hΩ.uniqueDiffOn hx).symm
  rwa [iteratedFDerivWithin_of_isOpen n hΩ hx] at he

/-! ## The fixed dyadic cutoff -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem dyadicProduct_eq_extension (q : D → ℝ) (g : D → E) :
    (fun x => SquaredPartition.dyadicProfile (q x) • g x) =
      extension q (1 / 2) 2 (fun x => SquaredPartition.dyadicProfile (q x) • g x) := by
  classical
  funext x
  by_cases hx : x ∈ window q (1 / 2) 2
  · exact (WaveEdgeExtension.extension_inside q (1 / 2) 2
      (fun y => SquaredPartition.dyadicProfile (q y) • g y) hx).symm
  · rw [WaveEdgeExtension.extension_outside q (1 / 2) 2
      (fun y => SquaredPartition.dyadicProfile (q y) • g y) hx]
    have hz : SquaredPartition.dyadicProfile (q x) = 0 := by
      by_contra hn
      have hm : q x ∈ Function.support SquaredPartition.dyadicProfile := hn
      rw [SquaredPartition.dyadicProfile_support] at hm
      exact hx hm
    rw [hz, zero_smul]

/-- Main endpoint: the literal product is smooth on the ambient open domain
and every actual tensor vanishes at either dyadic face. -/
theorem dyadic_product_smooth_and_flat {Ω : Set D} (hΩ : IsOpen Ω)
    {q : D → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) {g : D → E}
    (hg : ContDiffOn ℝ ∞ g (windowDomain Ω q (1 / 2) 2))
    (hB : LocalJetBounds Ω q g) :
    ContDiffOn ℝ ∞ (fun x => SquaredPartition.dyadicProfile (q x) • g x) Ω ∧
      ∀ x ∈ Ω, q x = 1 / 2 ∨ q x = 2 → ∀ n : ℕ,
        iteratedFDeriv ℝ n (fun y => SquaredPartition.dyadicProfile (q y) • g y) x = 0 := by
  let φ : D → ℝ := fun x => SquaredPartition.dyadicProfile (q x)
  let f : D → E := fun x => φ x • g x
  have hφ : ContDiffOn ℝ ∞ φ Ω := SquaredPartition.dyadicProfile_smooth.comp_contDiffOn hq
  have hf : ContDiffOn ℝ ∞ f (windowDomain Ω q (1 / 2) 2) :=
    (hφ.mono (inter_subset_left (t := window q (1 / 2) 2))).smul hg
  have hsmall : SmallOJets Ω q (1 / 2) 2 f := by
    intro n x hx hedge
    have hflat : ∀ j : ℕ, iteratedFDeriv ℝ j φ x = 0 := by
      intro j
      apply NativeBandExtension.flat_comp_jets SquaredPartition.dyadicProfile_smooth
        (hq.contDiffAt (hΩ.mem_nhds hx)) _ j
      intro k
      rcases hedge with he | he
      · rw [he]
        exact (NativeBandExtension.dyadicProfile_endpoint_jets k).1
      · rw [he]
        exact (NativeBandExtension.dyadicProfile_endpoint_jets k).2
    exact product_jet_extension_isLittleO hΩ hq.continuousOn hφ hg hx hflat n (hB x hx hedge n)
  have heq : f = extension q (1 / 2) 2 f := dyadicProduct_eq_extension q g
  constructor
  · change ContDiffOn ℝ ∞ f Ω
    rw [heq]
    exact (hasFTaylorSeriesUpToOn_extension hΩ hq.continuousOn hf hsmall).contDiffOn
  · intro x hx hedge n
    change iteratedFDeriv ℝ n f x = 0
    rw [heq, iteratedFDeriv_extension hΩ hq.continuousOn hf hsmall n hx]
    apply WaveEdgeExtension.extension_outside
    rcases hedge with he | he
    · exact fun hin => (not_lt_of_ge he.le) hin.1
    · exact fun hin => (not_lt_of_ge he.ge) hin.2

theorem dyadic_product_contDiffOn {Ω : Set D} (hΩ : IsOpen Ω)
    {q : D → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) {g : D → E}
    (hg : ContDiffOn ℝ ∞ g (windowDomain Ω q (1 / 2) 2))
    (hB : LocalJetBounds Ω q g) :
    ContDiffOn ℝ ∞ (fun x => SquaredPartition.dyadicProfile (q x) • g x) Ω :=
  (dyadic_product_smooth_and_flat hΩ hq hg hB).1

theorem dyadic_product_face {Ω : Set D} (hΩ : IsOpen Ω)
    {q : D → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) {g : D → E}
    (hg : ContDiffOn ℝ ∞ g (windowDomain Ω q (1 / 2) 2))
    (hB : LocalJetBounds Ω q g) {x : D} (hx : x ∈ Ω) (he : q x = 1 / 2 ∨ q x = 2) :
    ContDiffAt ℝ ∞ (fun y => SquaredPartition.dyadicProfile (q y) • g y) x ∧
      ∀ n : ℕ, iteratedFDeriv ℝ n (fun y => SquaredPartition.dyadicProfile (q y) • g y) x = 0 :=
  ⟨(dyadic_product_contDiffOn hΩ hq hg hB).contDiffAt (hΩ.mem_nhds hx),
    (dyadic_product_smooth_and_flat hΩ hq hg hB).2 x hx he⟩

end NavierStokes.FlatDyadicExtension
