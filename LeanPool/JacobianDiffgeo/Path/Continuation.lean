/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Path.Chain
import Mathlib.Topology.Order.ProjIcc

/-!
# Existence, `pathIntegral`, path algebra and linearity (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §3). Chain-continuation
existence of a primitive along a path (via `ChartChain`), the definition of `pathIntegral`, and
its basic algebra: `trans`/`symm`/`reparam`/`cast` invariance and ℂ-linearity in the form.

Main declarations:
* `RS.IsPrimitiveAlong γ η F`, `RS.exists_isPrimitiveAlong`, `RS.pathIntegral`,
  `RS.IsPrimitiveAlong.pathIntegral_eq`.
* `RS.pathIntegral_refl/symm/trans/reparam/cast`.
* `RS.pathIntegral_add/smul/zero_form`, `RS.pathIntegralₗ`.
-/

open scoped ContDiff Manifold Topology unitInterval
open IsManifold Metric Set Filter

noncomputable section

namespace RS


variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {x y z : X}

/-! ### The real-line clamp to `[0,1]` -/

/-- Clamp a real number into `[0,1]`. -/
def clampI (u : ℝ) : ℝ := max 0 (min u 1)

theorem clampI_mem (u : ℝ) : clampI u ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem continuous_clampI : Continuous clampI :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clampI_zero : clampI 0 = 0 := by
  unfold clampI; rw [min_eq_left zero_le_one, max_eq_right le_rfl]

theorem clampI_one : clampI 1 = 1 := by
  unfold clampI; rw [min_eq_right le_rfl, max_eq_right zero_le_one]

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
/-- `γ.extend` is invariant under clamping its argument into `[0,1]`. -/
theorem extend_clampI (γ : Path x y) (u : ℝ) : γ.extend (clampI u) = γ.extend u := by
  by_cases h0 : u ≤ 0
  · have hc : clampI u = 0 := by
      unfold clampI; rw [min_eq_left (h0.trans zero_le_one), max_eq_left h0]
    rw [hc, γ.extend_zero, γ.extend_of_le_zero h0]
  · replace h0 := not_le.mp h0
    by_cases h1 : u ≤ 1
    · have hc : clampI u = u := by
        unfold clampI; rw [min_eq_left h1, max_eq_right h0.le]
      rw [hc]
    · replace h1 := not_le.mp h1
      have hc : clampI u = 1 := by
        unfold clampI; rw [min_eq_right h1.le, max_eq_right zero_le_one]
      rw [hc, γ.extend_one, γ.extend_of_one_le h1.le]

/-! ### `IsPrimitiveAlong`, existence, `pathIntegral` -/

/-- `F` is a primitive of `η` along the path `γ`. -/
def IsPrimitiveAlong (γ : Path x y) (η : Form1 X) (F : ℝ → ℂ) : Prop :=
  IsPrimitiveAlongMap γ.extend η F Set.univ

/-- Adjacent real intervals `Icc l c`, `Icc c d` cover `𝓝[Icc l c ∪ Icc c d]`-neighborhoods of
every point (the `hcov` discharger for `glue` along a single subdivision breakpoint). -/
private theorem hcov_adjacent {l c d : ℝ} (hlc : l ≤ c) (hcd : c ≤ d) :
    ∀ a ∈ Icc l c ∪ Icc c d,
      Icc l c ∈ 𝓝[Icc l c ∪ Icc c d] a ∨ Icc c d ∈ 𝓝[Icc l c ∪ Icc c d] a ∨
        a ∈ Icc l c ∩ Icc c d := by
  intro a _
  rcases lt_trichotomy a c with hac | hac | hac
  · refine Or.inl ?_
    rw [mem_nhdsWithin]
    refine ⟨Iio c, isOpen_Iio, hac, ?_⟩
    rintro w ⟨hw1, hw2⟩
    rcases hw2 with hw2 | hw2
    · exact hw2
    · exact absurd hw2.1 (not_le.mpr hw1)
  · subst hac
    exact Or.inr (Or.inr ⟨⟨hlc, le_rfl⟩, ⟨le_rfl, hcd⟩⟩)
  · refine Or.inr (Or.inl ?_)
    rw [mem_nhdsWithin]
    refine ⟨Ioi c, isOpen_Ioi, hac, ?_⟩
    rintro w ⟨hw1, hw2⟩
    rcases hw2 with hw2 | hw2
    · exact absurd hw2.2 (not_le.mpr hw1)
    · exact hw2

private theorem isPreconnected_adjacent_inter {l c d : ℝ} (hlc : l ≤ c) (hcd : c ≤ d) :
    IsPreconnected (Icc l c ∩ Icc c d) := by
  have heq : Icc l c ∩ Icc c d = ({c} : Set ℝ) := by
    rw [Icc_inter_Icc, sup_eq_right.mpr hlc, inf_eq_left.mpr hcd, Icc_self]
  rw [heq]; exact isPreconnected_singleton

theorem exists_isPrimitiveAlong (γ : Path x y) (η : Form1 X) :
    ∃ F : ℝ → ℂ, IsPrimitiveAlong γ η F ∧ F 0 = 0 := by
  obtain ⟨C⟩ := exists_chartChain γ
  suffices h : ∀ k : ℕ, ∃ F : ℝ → ℂ, IsPrimitiveAlongMap γ.extend η F (Icc 0 (C.t k)) ∧ F 0 = 0 by
    obtain ⟨F, hF, hF0⟩ := h C.n
    rw [C.ht1 C.n le_rfl] at hF
    have hmapsto : MapsTo clampI Set.univ (Icc (0:ℝ) 1) := fun u _ => clampI_mem u
    have hcomp := hF.comp (φ := clampI) (t := Set.univ) continuous_clampI.continuousOn hmapsto
    have hKeq : Set.EqOn (γ.extend ∘ clampI) γ.extend Set.univ :=
      fun u _ => extend_clampI γ u
    refine ⟨F ∘ clampI, hcomp.congr_map hKeq, ?_⟩
    change F (clampI 0) = 0
    rw [clampI_zero]; exact hF0
  intro k
  induction k with
  | zero =>
    have hmem0 : (0:ℝ) ∈ Icc (C.t 0) (C.t 1) :=
      ⟨C.ht0.le, C.ht0 ▸ C.mono (Nat.zero_le 1)⟩
    have hz₀mem : (C.e 0) (γ.extend 0) ∈ ball (C.c 0) (C.r 0) := (C.maps 0 0 hmem0).2
    obtain ⟨g, hg0, hg⟩ := exists_hasDerivAt_ball (η.analyticOnNhd_coeffIn (C.he 0))
      (C.ball_subset 0) hz₀mem (w := 0)
    refine ⟨fun u => g (C.e 0 (γ.extend u)), ?_, hg0⟩
    apply isPrimitiveAlongMap_of_ball (C.he 0) hg
    intro a ha
    exact C.maps 0 a ⟨C.ht0.le.trans ha.1, ha.2.trans (C.mono (Nat.zero_le 1))⟩
  | succ k ih =>
    obtain ⟨F, hF, hF0⟩ := ih
    obtain ⟨g, _, hg⟩ := exists_hasDerivAt_ball (c := C.c k) (r := C.r k) (z₀ := C.c k) (w := 0)
      (η.analyticOnNhd_coeffIn (C.he k)) (C.ball_subset k) (mem_ball_self (C.hr k))
    have hG : IsPrimitiveAlongMap γ.extend η (fun u => g (C.e k (γ.extend u)))
        (Icc (C.t k) (C.t (k+1))) :=
      isPrimitiveAlongMap_of_ball (C.he k) hg (C.maps k)
    have hG' : IsPrimitiveAlongMap γ.extend η
        (fun u => g (C.e k (γ.extend u)) + (F (C.t k) - g (C.e k (γ.extend (C.t k)))))
        (Icc (C.t k) (C.t (k+1))) := hG.add_const _
    have hval : F (C.t k) =
        g (C.e k (γ.extend (C.t k))) + (F (C.t k) - g (C.e k (γ.extend (C.t k)))) := by ring
    have h0k : (0:ℝ) ≤ C.t k := C.ht0 ▸ C.mono (Nat.zero_le k)
    have hmono : C.t k ≤ C.t (k+1) := C.mono (Nat.le_succ k)
    have hcont : ContinuousOn γ.extend (Icc 0 (C.t k) ∪ Icc (C.t k) (C.t (k+1))) :=
      γ.continuous_extend.continuousOn
    have hL : IsPreconnected (Icc 0 (C.t k) ∩ Icc (C.t k) (C.t (k+1))) :=
      isPreconnected_adjacent_inter h0k hmono
    have ha0 : C.t k ∈ Icc (0:ℝ) (C.t k) ∩ Icc (C.t k) (C.t (k+1)) :=
      ⟨⟨h0k, le_rfl⟩, ⟨le_rfl, hmono⟩⟩
    have hcov := hcov_adjacent (l := (0:ℝ)) (c := C.t k) (d := C.t (k+1)) h0k hmono
    have hglue := hF.glue hcont hG' hL ha0 hval hcov
    rw [Icc_union_Icc_eq_Icc h0k hmono] at hglue
    refine ⟨Set.piecewise (Icc 0 (C.t k)) F
      (fun u => g (C.e k (γ.extend u)) + (F (C.t k) - g (C.e k (γ.extend (C.t k))))), hglue, ?_⟩
    have h0mem : (0:ℝ) ∈ Icc (0:ℝ) (C.t k) := ⟨le_rfl, h0k⟩
    rw [Set.piecewise_eq_of_mem (Icc 0 (C.t k)) F
      (fun u => g (C.e k (γ.extend u)) + (F (C.t k) - g (C.e k (γ.extend (C.t k))))) h0mem]
    exact hF0

/-- The integral of `η` along `γ`, defined via the (well-defined, see `pathIntegral_eq`) chosen
primitive: `pathIntegral γ η = F 1 - F 0`. -/
noncomputable def pathIntegral (γ : Path x y) (η : Form1 X) : ℂ :=
  (exists_isPrimitiveAlong γ η).choose 1

theorem IsPrimitiveAlong.pathIntegral_eq {γ : Path x y} {η : Form1 X} {F : ℝ → ℂ}
    (hF : IsPrimitiveAlong γ η F) : pathIntegral γ η = F 1 - F 0 := by
  obtain ⟨hF', hF'0⟩ := (exists_isPrimitiveAlong γ η).choose_spec
  have h := hF'.sub_eq_sub isPreconnected_univ γ.continuous_extend.continuousOn hF
    (mem_univ (0:ℝ)) (mem_univ (1:ℝ))
  change (exists_isPrimitiveAlong γ η).choose 1 = F 1 - F 0
  rw [hF'0] at h
  linear_combination h

/-! ### Path algebra -/

@[simp]
theorem pathIntegral_refl (x : X) (η : Form1 X) : pathIntegral (Path.refl x) η = 0 := by
  set e := chartAt ℂ x with he_def
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (mem_chart_target ℂ x)
  obtain ⟨g, _, hg⟩ := exists_hasDerivAt_ball (η.analyticOnNhd_coeffIn (chart_mem_maximalAtlas x))
    hball (mem_ball_self hr) (w := 0)
  have hF : IsPrimitiveAlong (Path.refl x) η (fun a => g (e ((Path.refl x).extend a))) := by
    apply isPrimitiveAlongMap_of_ball (chart_mem_maximalAtlas x) hg
    intro a _
    rw [Path.refl_extend]
    exact ⟨mem_chart_source ℂ x, mem_ball_self hr⟩
  rw [hF.pathIntegral_eq]
  simp [Path.refl_extend]

@[simp]
theorem pathIntegral_symm (γ : Path x y) (η : Form1 X) :
    pathIntegral γ.symm η = -pathIntegral γ η := by
  obtain ⟨F, hF, hF0⟩ := exists_isPrimitiveAlong γ η
  have heq : γ.extend ∘ (fun u : ℝ => 1 - u) = γ.symm.extend := by
    funext u; simp [γ.extend_symm_apply]
  have hcomp : IsPrimitiveAlong γ.symm η (F ∘ (fun u : ℝ => 1 - u)) := by
    have hc : Continuous (fun u : ℝ => 1 - u) := by fun_prop
    have := hF.comp (φ := fun u : ℝ => 1 - u) (t := Set.univ) hc.continuousOn (mapsTo_univ _ _)
    rwa [heq] at this
  rw [hcomp.pathIntegral_eq]
  change F (1 - (1:ℝ)) - F (1 - (0:ℝ)) = -pathIntegral γ η
  norm_num
  rw [hF.pathIntegral_eq]
  ring

theorem pathIntegral_trans (γ : Path x y) (γ' : Path y z) (η : Form1 X) :
    pathIntegral (γ.trans γ') η = pathIntegral γ η + pathIntegral γ' η := by
  obtain ⟨H, hH, hH0⟩ := exists_isPrimitiveAlong (γ.trans γ') η
  have hcontγ : Continuous (fun u : ℝ => clampI u / 2) := continuous_clampI.div_const 2
  have hcontγ' : Continuous (fun u : ℝ => (1 + clampI u) / 2) :=
    (continuous_const.add continuous_clampI).div_const 2
  have heqγ : ∀ u : ℝ, (γ.trans γ').extend (clampI u / 2) = γ.extend u := by
    intro u
    rw [γ.extend_trans_of_le_half γ' (by linarith [clampI_mem u |>.1, clampI_mem u |>.2] :
      clampI u / 2 ≤ 1/2)]
    have : (2:ℝ) * (clampI u / 2) = clampI u := by ring
    rw [this, extend_clampI]
  have heqγ' : ∀ u : ℝ, (γ.trans γ').extend ((1 + clampI u) / 2) = γ'.extend u := by
    intro u
    rw [γ.extend_trans_of_half_le γ' (by linarith [clampI_mem u |>.1] :
      (1:ℝ)/2 ≤ (1 + clampI u) / 2)]
    have : (2:ℝ) * ((1 + clampI u) / 2) - 1 = clampI u := by ring
    rw [this, extend_clampI]
  have hcompγ : IsPrimitiveAlong γ η (H ∘ (fun u : ℝ => clampI u / 2)) := by
    have h1 := hH.comp (φ := fun u : ℝ => clampI u / 2) (t := Set.univ)
      hcontγ.continuousOn (mapsTo_univ _ _)
    have hK : Set.EqOn ((γ.trans γ').extend ∘ (fun u : ℝ => clampI u / 2)) γ.extend Set.univ :=
      fun u _ => heqγ u
    exact h1.congr_map hK
  have hcompγ' : IsPrimitiveAlong γ' η (H ∘ (fun u : ℝ => (1 + clampI u) / 2)) := by
    have h1 := hH.comp (φ := fun u : ℝ => (1 + clampI u) / 2) (t := Set.univ)
      hcontγ'.continuousOn (mapsTo_univ _ _)
    have hK : Set.EqOn ((γ.trans γ').extend ∘ (fun u : ℝ => (1 + clampI u) / 2)) γ'.extend
        Set.univ := fun u _ => heqγ' u
    exact h1.congr_map hK
  rw [hH.pathIntegral_eq, hcompγ.pathIntegral_eq, hcompγ'.pathIntegral_eq]
  change H 1 - H 0 =
    H (clampI 1 / 2) - H (clampI 0 / 2) + (H ((1 + clampI 1)/2) - H ((1 + clampI 0)/2))
  rw [clampI_zero, clampI_one]
  norm_num

theorem pathIntegral_reparam (γ : Path x y) {f : I → I} (hf : Continuous f)
    (h₀ : f 0 = 0) (h₁ : f 1 = 1) (η : Form1 X) :
    pathIntegral (γ.reparam f hf h₀ h₁) η = pathIntegral γ η := by
  obtain ⟨F, hF, hF0⟩ := exists_isPrimitiveAlong γ η
  set φ : ℝ → ℝ := fun u => (f (projIcc 0 1 zero_le_one u) : ℝ) with hφ_def
  have hcont : Continuous φ := (continuous_subtype_val.comp hf).comp continuous_projIcc
  have heq : γ.extend ∘ φ = (γ.reparam f hf h₀ h₁).extend := by
    funext u
    by_cases h0 : u ≤ 0
    · have hp : projIcc (0:ℝ) 1 zero_le_one u = 0 := projIcc_of_le_left zero_le_one h0
      change γ.extend (f (projIcc 0 1 zero_le_one u) : ℝ) = _
      rw [hp, h₀, Set.Icc.coe_zero, γ.extend_zero, (γ.reparam f hf h₀ h₁).extend_of_le_zero h0]
    · replace h0 := not_le.mp h0
      by_cases h1 : u ≤ 1
      · have hp : projIcc (0:ℝ) 1 zero_le_one u = ⟨u, ⟨h0.le, h1⟩⟩ :=
          projIcc_of_mem zero_le_one ⟨h0.le, h1⟩
        change γ.extend (f (projIcc 0 1 zero_le_one u) : ℝ) = _
        rw [hp, γ.extend_apply (f ⟨u, ⟨h0.le, h1⟩⟩).2,
          (γ.reparam f hf h₀ h₁).extend_apply ⟨h0.le, h1⟩]
        rfl
      · replace h1 := not_le.mp h1
        have hp : projIcc (0:ℝ) 1 zero_le_one u = 1 := projIcc_of_right_le zero_le_one h1.le
        change γ.extend (f (projIcc 0 1 zero_le_one u) : ℝ) = _
        rw [hp, h₁, Set.Icc.coe_one, γ.extend_one, (γ.reparam f hf h₀ h₁).extend_of_one_le h1.le]
  have hcomp : IsPrimitiveAlong (γ.reparam f hf h₀ h₁) η (F ∘ φ) := by
    have h1 := hF.comp (φ := φ) (t := Set.univ) hcont.continuousOn (mapsTo_univ _ _)
    rwa [heq] at h1
  rw [hcomp.pathIntegral_eq, hF.pathIntegral_eq]
  change F (φ 1) - F (φ 0) = F 1 - F 0
  have hφ1 : φ 1 = 1 := by
    change (f (projIcc 0 1 zero_le_one (1:ℝ)) : ℝ) = 1
    have hp : projIcc (0:ℝ) 1 zero_le_one (1:ℝ) = 1 := projIcc_of_right_le zero_le_one le_rfl
    rw [hp, h₁, Set.Icc.coe_one]
  have hφ0 : φ 0 = 0 := by
    change (f (projIcc 0 1 zero_le_one (0:ℝ)) : ℝ) = 0
    have hp : projIcc (0:ℝ) 1 zero_le_one (0:ℝ) = 0 := projIcc_of_le_left zero_le_one le_rfl
    rw [hp, h₀, Set.Icc.coe_zero]
  rw [hφ1, hφ0]

@[simp]
theorem pathIntegral_cast {x' y' : X} (γ : Path x y) (hx : x' = x) (hy : y' = y) (η : Form1 X) :
    pathIntegral (γ.cast hx hy) η = pathIntegral γ η := by
  subst hx; subst hy
  rw [Path.cast_rfl_rfl]

/-! ### ℂ-linearity in the form -/

theorem pathIntegral_add (γ : Path x y) (η θ : Form1 X) :
    pathIntegral γ (η + θ) = pathIntegral γ η + pathIntegral γ θ := by
  obtain ⟨F, hF, hF0⟩ := exists_isPrimitiveAlong γ η
  obtain ⟨G, hG, hG0⟩ := exists_isPrimitiveAlong γ θ
  have hsum : IsPrimitiveAlong γ (η + θ) (fun u => F u + G u) := by
    intro a _
    obtain ⟨e₁, he₁, hKa1, g₁, hg₁, hF'⟩ := hF a (mem_univ a)
    obtain ⟨g₂, hg₂, hG'⟩ := hG.rechart (mem_univ a)
      γ.continuous_extend.continuousAt.continuousWithinAt he₁ hKa1
    refine ⟨e₁, he₁, hKa1, fun z => g₁ z + g₂ z, ?_, ?_⟩
    · filter_upwards [hg₁, hg₂] with z hz1 hz2
      rw [coeffIn_add]
      exact hz1.add hz2
    · filter_upwards [hF', hG'] with b hb1 hb2 using ⟨hb1.1, by rw [hb1.2, hb2.2]⟩
  rw [hsum.pathIntegral_eq, hF.pathIntegral_eq, hG.pathIntegral_eq]
  ring

theorem pathIntegral_smul (γ : Path x y) (c : ℂ) (η : Form1 X) :
    pathIntegral γ (c • η) = c * pathIntegral γ η := by
  obtain ⟨F, hF, hF0⟩ := exists_isPrimitiveAlong γ η
  have hsmul : IsPrimitiveAlong γ (c • η) (fun u => c * F u) := by
    intro a _
    obtain ⟨e, he, hKa, g, hg, hF'⟩ := hF a (mem_univ a)
    refine ⟨e, he, hKa, fun z => c * g z, ?_, ?_⟩
    · filter_upwards [hg] with z hz
      rw [coeffIn_smul]
      exact hz.const_mul c
    · filter_upwards [hF'] with b hb using ⟨hb.1, by rw [hb.2]⟩
  rw [hsmul.pathIntegral_eq, hF.pathIntegral_eq]
  ring

@[simp]
theorem pathIntegral_zero_form (γ : Path x y) : pathIntegral γ (0 : Form1 X) = 0 := by
  have hz : IsPrimitiveAlong γ (0 : Form1 X) (fun _ => (0:ℂ)) := by
    intro a _
    set e := chartAt ℂ (γ.extend a) with he_def
    refine ⟨e, chart_mem_maximalAtlas _, mem_chart_source ℂ _, fun _ => 0, ?_, ?_⟩
    · filter_upwards with z
      rw [coeffIn_zero]
      exact hasDerivAt_const z 0
    · have hev : ∀ᶠ b in 𝓝 a, γ.extend b ∈ e.source :=
        γ.continuous_extend.continuousAt.eventually
          (e.open_source.mem_nhds (mem_chart_source ℂ _))
      rw [nhdsWithin_univ]
      filter_upwards [hev] with b hb using ⟨hb, rfl⟩
  rw [hz.pathIntegral_eq]
  ring

/-- The integral of a fixed path, as a ℂ-linear map on 1-forms. -/
noncomputable def pathIntegralₗ (γ : Path x y) : Form1 X →ₗ[ℂ] ℂ where
  toFun η := pathIntegral γ η
  map_add' := pathIntegral_add γ
  map_smul' c η := by simpa using pathIntegral_smul γ c η

end RS

end
