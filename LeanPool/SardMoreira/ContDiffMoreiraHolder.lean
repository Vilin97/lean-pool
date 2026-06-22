/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import LeanPool.SardMoreira.ContDiff
import LeanPool.SardMoreira.ContinuousMultilinearMap

/-!
# LeanPool.SardMoreira.ContDiffMoreiraHolder
-/

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A map `f` is `C^{k+(α)}` at a point `a`, meaning it is `C^k` at `a` and its
`k`-th derivative satisfies a pointwise Hölder estimate of exponent `α` at `a`. -/
@[mk_iff]
structure ContDiffMoreiraHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  /-- A `C^{k+(α)}` map is in particular `C^k` at the point. -/
  contDiffAt : ContDiffAt ℝ k f a
  /-- A `C^{k+(α)}` map satisfies `D^k f x - D^k f a = O(‖x - a‖^α)` as `x → a`. -/
  isBigO : (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

theorem ContDiffAt.contDiffMoreiraHolderAt {n : WithTop ℕ∞} {k : ℕ} {f : E → F} {a : E}
    (h : ContDiffAt ℝ n f a) (hk : k < n) (α : I) : ContDiffMoreiraHolderAt k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) <| tendsto_norm_sub_self_nhdsGE a

namespace ContDiffMoreiraHolderAt

theorem continuousAt {k : ℕ} {α : I} {f : E → F} {a : E} (h : ContDiffMoreiraHolderAt k α f a) :
    ContinuousAt f a :=
  h.contDiffAt.continuousAt

theorem differentiableAt {k : ℕ} {α : I} {f : E → F} {a : E} (h : ContDiffMoreiraHolderAt k α f a)
    (hk : k ≠ 0) : DifferentiableAt ℝ f a :=
  h.contDiffAt.differentiableAt <| mod_cast hk

@[simp]
theorem zero_exponent_iff {k : ℕ} {f : E → F} {a : E} :
    ContDiffMoreiraHolderAt k 0 f a ↔ ContDiffAt ℝ k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

theorem zero_left_iff {α : I} {f : E → F} {a : E} :
    ContDiffMoreiraHolderAt 0 α f a ↔
      ContDiffAt ℝ 0 f a ∧ (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) := by
  simp only [contDiffMoreiraHolderAt_iff, Nat.cast_zero, and_congr_right_iff]
  intro hfc
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub]
  rw [← isBigO_norm_left]
  simp_rw [LinearIsometryEquiv.norm_map, isBigO_norm_left]

theorem of_exponent_le {k : ℕ} {f : E → F} {a : E} {α β : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hle : β ≤ α) : ContDiffMoreiraHolderAt k β f a where
  contDiffAt := hf.contDiffAt
  isBigO := hf.isBigO.trans <| by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le_of_imp hle fun hα ↦ ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a

theorem of_lt {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hlt : l < k) : ContDiffMoreiraHolderAt l β f a :=
  hf.contDiffAt.contDiffMoreiraHolderAt (mod_cast hlt) _

theorem of_toLex_le {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hle : toLex (l, β) ≤ toLex (k, α)) : ContDiffMoreiraHolderAt l β f a :=
  (Prod.Lex.le_iff.mp hle).elim hf.of_lt <| by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

theorem of_le {k l : ℕ} {f : E → F} {a : E} {α : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hl : l ≤ k) : ContDiffMoreiraHolderAt l α f a :=
  hf.of_toLex_le <| Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

theorem of_contDiffOn_holderWith {f : E → F} {s : Set E} {k : ℕ} {α : I} {a : E} {C : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv ℝ k f) s) :
    ContDiffMoreiraHolderAt k α f a where
  contDiffAt := hf.contDiffAt hs
  isBigO := .of_bound C <| mem_of_superset hs fun x hx ↦ by
    have hdist := hd.dist_le hx (mem_of_mem_nhds hs)
    have hdist' :
        dist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f a) ≤
          (C : ℝ) * dist x a ^ (α : ℝ) := by
      convert hdist using 2
      rfl
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg] using hdist'

theorem fst {k : ℕ} {α : I} {a : E × F} : ContDiffMoreiraHolderAt k α Prod.fst a :=
  contDiffAt_fst.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

theorem snd {k : ℕ} {α : I} {a : E × F} : ContDiffMoreiraHolderAt k α Prod.snd a :=
  contDiffAt_snd.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

theorem prodMk {k : ℕ} {α : I} {f : E → F} {g : E → G} {a : E}
    (hf : ContDiffMoreiraHolderAt k α f a) (hg : ContDiffMoreiraHolderAt k α g a) :
    ContDiffMoreiraHolderAt k α (fun x ↦ (f x, g x)) a where
  contDiffAt := hf.contDiffAt.prodMk hg.contDiffAt
  isBigO := calc
    _ =ᶠ[𝓝 a] (fun x ↦ (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f a).prod
                (iteratedFDeriv ℝ k g x - iteratedFDeriv ℝ k g a)) := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hg.contDiffAt.eventually (by simp)] with x hfx hgx
      apply DFunLike.ext
      rw [iteratedFDeriv_prodMk _ _ le_rfl, iteratedFDeriv_prodMk _ _ le_rfl] <;>
        simp [hfx, hgx, hf.contDiffAt, hg.contDiffAt]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      refine .of_norm_left ?_
      simp only [ContinuousMultilinearMap.opNorm_prod, ← Prod.norm_mk]
      exact (hf.isBigO.prod_left hg.isBigO).norm_left

theorem comp' {g : F → G} {f : E → F} {a : E} {k : ℕ} {α : I}
    (hg : ContDiffMoreiraHolderAt k α g (f a)) (hf : ContDiffMoreiraHolderAt k α f a)
    (hd : DifferentiableAt ℝ g (f a) ∨ DifferentiableAt ℝ f a) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a where
  contDiffAt := hg.contDiffAt.comp a hf.contDiffAt
  isBigO := calc
    (iteratedFDeriv ℝ k (g ∘ f) · - iteratedFDeriv ℝ k (g ∘ f) a)
      =ᶠ[𝓝 a] fun x ↦ (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) k -
        (ftaylorSeries ℝ g (f a)).taylorComp (ftaylorSeries ℝ f a) k := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hf.continuousAt.eventually (hg.contDiffAt.eventually (by simp))] with x hfx hgx
      rw [iteratedFDeriv_comp hgx hfx le_rfl,
        iteratedFDeriv_comp hg.contDiffAt hf.contDiffAt le_rfl]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
      · intro i hi
        exact ((hg.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).comp hf.continuousAt)
          |>.norm.isBoundedUnder_le
      · intro i hi
        by_cases hfd : DifferentiableAt ℝ f a
        · refine ((hg.of_le hi).isBigO.comp_tendsto hf.continuousAt).trans ?_
          refine .rpow α.2.1 (.of_forall fun _ ↦ norm_nonneg _) <| .norm_norm ?_
          exact hfd.isBigO_sub
        · obtain rfl : k = 0 := by
            contrapose! hfd
            exact hf.differentiableAt hfd
          obtain rfl : i = 0 := by rwa [nonpos_iff_eq_zero] at hi
          refine .of_norm_left ?_
          simp only [ftaylorSeries, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
            LinearIsometryEquiv.norm_map, isBigO_norm_left]
          refine ((hd.resolve_right hfd).isBigO_sub.comp_tendsto hf.continuousAt).trans ?_
          refine .trans (.of_norm_right ?_) hf.isBigO
          simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, LinearIsometryEquiv.norm_map,
            ← map_sub]
          exact isBigO_norm_right.mpr (isBigO_refl _ _)
      · intro i hi
        exact (hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).norm.isBoundedUnder_le
      · exact fun _ _ ↦ isBoundedUnder_const
      · exact fun i hi ↦ (hf.of_le hi).isBigO

theorem comp {g : F → G} {f : E → F} {a : E} {k : ℕ} {α : I}
    (hg : ContDiffMoreiraHolderAt k α g (f a)) (hf : ContDiffMoreiraHolderAt k α f a)
    (hk : k ≠ 0) : ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  hg.comp' hf (.inl <| hg.differentiableAt hk)

theorem _root_.ContinuousLinearMap.contDiffMoreiraHolderAt
    (f : E →L[ℝ] F) {a : E} {k : ℕ} {α : I} :
    ContDiffMoreiraHolderAt k α f a :=
  f.contDiff.contDiffAt.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) _

theorem _root_.ContinuousLinearEquiv.contDiffMoreiraHolderAt
    (f : E ≃L[ℝ] F) {a : E} {k : ℕ} {α : I} :
    ContDiffMoreiraHolderAt k α f a :=
  f.toContinuousLinearMap.contDiffMoreiraHolderAt

theorem continuousLinearMap_comp {f : E → F} {a : E} {k : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (g : F →L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  g.contDiffMoreiraHolderAt.comp' hf <| .inl g.differentiableAt

@[simp]
theorem _root_.ContinuousLinearEquiv.contDiffMoreiraHolderAt_left_comp
    {f : E → F} {a : E} {k : ℕ} {α : I} (g : F ≃L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.continuousLinearMap_comp (g.symm : G →L[ℝ] F),
    fun h ↦ h.continuousLinearMap_comp (g : F →L[ℝ] G)⟩

@[simp]
theorem _root_.LinearIsometryEquiv.contDiffMoreiraHolderAt_left_comp
    {f : E → F} {a : E} {k : ℕ} {α : I} (g : F ≃ₗᵢ[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  g.toContinuousLinearEquiv.contDiffMoreiraHolderAt_left_comp

protected theorem id {k : ℕ} {α : I} {a : E} : ContDiffMoreiraHolderAt k α id a :=
  ContinuousLinearMap.id ℝ E |>.contDiffMoreiraHolderAt

protected theorem const {k : ℕ} {α : I} {a : E} {b : F} :
    ContDiffMoreiraHolderAt k α (Function.const E b) a :=
  contDiffAt_const.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

protected theorem fderiv {f : E → F} {a : E} {k l : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hl : l + 1 ≤ k) :
    ContDiffMoreiraHolderAt l α (fderiv ℝ f) a where
  contDiffAt := hf.contDiffAt.fderiv_right (mod_cast hl)
  isBigO := .of_norm_left <| by
    simpa [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, ← dist_eq_norm_sub]
      using hf.of_le hl |>.isBigO |>.norm_left

protected theorem iteratedFDeriv {f : E → F} {a : E} {k l m : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hl : l + m ≤ k) :
    ContDiffMoreiraHolderAt l α (iteratedFDeriv ℝ m f) a := by
  induction m generalizing l with
  | zero =>
    simpa +unfoldPartialApp [iteratedFDeriv_zero_eq_comp] using hf.of_le hl
  | succ m ihm =>
    rw [← add_assoc, add_right_comm] at hl
    -- TODO: why `simp` fails to apply the lemma? Does it fail to unify some instances?
    -- Does it happen on the latest Mathlib?
    simp +unfoldPartialApp only [iteratedFDeriv_succ_eq_comp_left]
    exact (LinearIsometryEquiv.contDiffMoreiraHolderAt_left_comp
      (continuousMultilinearCurryLeftEquiv ℝ (fun x ↦ E) F).symm).mpr ((ihm hl).fderiv le_rfl)

theorem congr_eventuallyEq {f g : E → F} {a : E} {k : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hfg : f =ᶠ[𝓝 a] g) :
    ContDiffMoreiraHolderAt k α g a where
  contDiffAt := hf.contDiffAt.congr_of_eventuallyEq hfg.symm
  isBigO := by
    refine EventuallyEq.trans_isBigO (.sub ?_ ?_) hf.isBigO
    · exact hfg.symm.iteratedFDeriv ℝ _
    · rw [hfg.symm.iteratedFDeriv ℝ _ |>.self_of_nhds]

end ContDiffMoreiraHolderAt

theorem OpenPartialHomeomorph.contDiffMoreiraHolderAt_symm [CompleteSpace E] {k : ℕ} {α : I}
    (f : OpenPartialHomeomorph E F) {a : F} (ha : a ∈ f.target)
    (hf' : (fderiv ℝ f (f.symm a)).IsInvertible)
    (hf : ContDiffMoreiraHolderAt k α f (f.symm a)) :
    ContDiffMoreiraHolderAt k α f.symm a where
  contDiffAt := contDiffAt_symm' f ha hf' hf.contDiffAt
  isBigO := by
    have hrpow : (‖· - a‖) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      (IsBigO.id_rpow_of_le_one α.2.2).comp_tendsto <| tendsto_norm_sub_self_nhdsGE _
    rcases eq_or_ne k 0 with rfl | hk₀
    · calc
        _ =O[𝓝 a] fun x ↦ f.symm x - f.symm a := by
          refine .of_norm_left ?_
          simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub,
            LinearIsometryEquiv.norm_map]
          exact isBigO_norm_left.mpr (isBigO_refl _ _)
        _ =O[𝓝 a] fun x ↦ ‖f (f.symm x) - f (f.symm a)‖ := by
          have : (· - f.symm a) =O[𝓝 (f.symm a)] (f · - f (f.symm a)) :=
            (hf'.hasFDerivAt.isTheta_sub
              hf'.choose.toHomeomorph.isInducing).symm.isBigO
          simpa [Function.comp_def] using this.comp_tendsto <| f.continuousAt_symm ha
        _ =ᶠ[𝓝 a] fun x ↦ ‖x - a‖ := by
          filter_upwards [f.eventually_right_inverse ha] with x hx
          simp [hx, ha]
        _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := hrpow
    · have hinv : ∀ᶠ x in 𝓝 (f.symm a), (fderiv ℝ f x).IsInvertible :=
        (hf.contDiffAt.continuousAt_fderiv <| mod_cast hk₀).eventually <|
           ContinuousLinearEquiv.isOpen.mem_nhds hf'
      have hinv' : ∀ᶠ x in 𝓝 a, (fderiv ℝ f (f.symm x)).IsInvertible :=
        f.continuousAt_symm ha |>.eventually hinv
      have hfderiv_isBigO :
          (fun x ↦ fderiv ℝ f.symm x - fderiv ℝ f.symm a) =O[𝓝 a]
            fun x ↦ fderiv ℝ f (f.symm x) - fderiv ℝ f (f.symm a) := by
        refine EventuallyEq.trans_isBigO ?_
          (ContinuousLinearMap.isBigO_inverse_sub_inverse hinv' ?_ ?_ ?_)
        · filter_upwards [f.continuousAt_symm ha hinv, f.open_target.mem_nhds ha] with x hfx hx
          rw [f.fderiv_symm hx hfx, f.fderiv_symm ha hf']
        · refine f.contDiffAt_symm' ha hf' hf.contDiffAt |>.continuousAt_fderiv (mod_cast hk₀)
            |>.norm |>.isBoundedUnder_le |>.mono_le ?_
          filter_upwards [hinv', f.open_target.mem_nhds ha] with x hfx hx
          simp [f.fderiv_symm hx hfx]
        · simp [hinv.self_of_nhds]
        · apply isBoundedUnder_const
      have hsymm_isBigO : (f.symm · - f.symm a) =O[𝓝 a] (· - a) := by
        simpa using f.hasFDerivAt_symm ha hf'.hasFDerivAt |>.isBigO_sub
      have hsymm_rpow_isBigO : (‖f.symm · - f.symm a‖ ^ (α : ℝ)) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
        hsymm_isBigO.norm_norm.rpow α.2.1 (by simp [EventuallyLE])
      obtain rfl | hk₁ : k = 1 ∨ 1 < k := by grind
      · calc
          _ =O[𝓝 a] fun x ↦ fderiv ℝ f.symm x - fderiv ℝ f.symm a :=
            .of_norm_left <| by simp [iteratedFDeriv_one_eq, ← map_sub, isBigO_refl]
          _ =O[𝓝 a] fun x ↦ fderiv ℝ f (f.symm x) - fderiv ℝ f (f.symm a) := hfderiv_isBigO
          _ =O[𝓝 a] fun x ↦ ‖f.symm x - f.symm a‖ ^ (α : ℝ) := by
            simpa [iteratedFDeriv_one_eq, ← map_sub, Function.comp_def]
              using hf.isBigO.comp_tendsto (f.continuousAt_symm ha) |>.norm_left
          _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := hsymm_rpow_isBigO
      · calc
          (fun x ↦ iteratedFDeriv ℝ k f.symm x - iteratedFDeriv ℝ k f.symm a)
            =ᶠ[𝓝 a] fun x ↦
              (FormalMultilinearSeries.id ℝ E (f.symm x) k -
                ∑ c ≠ OrderedFinpartition.atomic k,
                  c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm x)
                    (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm x))).compContinuousLinearMap
                      (fun _ ↦ fderiv ℝ f.symm x) -
              (FormalMultilinearSeries.id ℝ E (f.symm a) k -
                ∑ c ≠ OrderedFinpartition.atomic k,
                  c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm a)
                    (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm a))).compContinuousLinearMap
                      (fun _ ↦ fderiv ℝ f.symm a) := by
            rw [← f.symm.symm_map_nhds_eq ha, f.symm_symm, eventuallyEq_map]
            filter_upwards [hf.contDiffAt.eventually (by simp),
              f.open_source.mem_nhds (OpenPartialHomeomorph.mapsTo_symm f ha), hinv]
              with x hx hfx hinv
            simp only [Function.comp_apply]
            rw [f.iteratedFDeriv_symm_eq_rec ha hf.contDiffAt le_rfl (fun _ ↦ hf'),
              f.iteratedFDeriv_symm_eq_rec (f.mapsTo hfx) (by simpa [hfx]) le_rfl (by simp [*])]
          _ = fun x ↦
            -∑ c ≠ OrderedFinpartition.atomic k,
              ((c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm x)
                (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm x))).compContinuousLinearMap
                  (fun _ ↦ fderiv ℝ f.symm x) -
                (c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm a)
                  (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm a))).compContinuousLinearMap
                    (fun _ ↦ fderiv ℝ f.symm a)) := by
            simp only [hk₁, FormalMultilinearSeries.id_apply_of_one_lt, zero_sub, neg_sub_neg,
              Finset.sum_sub_distrib, ContinuousMultilinearMap.compContinuousLinearMap_neg_left,
              ContinuousMultilinearMap.compContinuousLinearMap_sum_left, neg_sub]
          _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := .neg_left <| .sum fun c hc ↦ ?_
        simp only [OrderedFinpartition.compContinuousLinearMap_compAlongOrderedFinpartition_left]
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, ← c.length_lt_iff] at hc
        apply c.compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
        · exact f.contDiffAt_symm' ha hf' hf.contDiffAt
            |>.continuousAt_iteratedFDeriv (mod_cast hc.le) |>.norm |>.isBoundedUnder_le
        · refine .trans (.norm_right ?_) hrpow
          exact f.contDiffAt_symm' ha hf' hf.contDiffAt
            |>.differentiableAt_iteratedFDeriv (mod_cast hc) |>.isBigO_sub
        · intro m
          refine (ContinuousAt.tendsto <| .norm ?_).isBoundedUnder_le
          simp only [← ContinuousMultilinearMap.compContinuousLinearMapL_apply]
          refine .clm_apply ?_ ?_
          · refine map_continuous
              (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ _ _ _)
              |>.continuousAt.comp ?_
            refine continuousAt_pi.2 fun _ ↦ ?_
            exact f.contDiffAt_symm' ha hf' hf.contDiffAt |>.continuousAt_fderiv (mod_cast hk₀)
          · refine hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast c.partSize_le _) |>.comp ?_
            exact f.continuousAt_symm ha
        · exact fun _ ↦ isBoundedUnder_const
        · intro m
          apply ContinuousMultilinearMap.compContinuousLinearMap_sub_compContinuousLinearMap_isBigO
          · apply isBoundedUnder_const
          · exact (hf.of_le (c.partSize_le m) |>.isBigO |>.comp_tendsto <| f.continuousAt_symm ha)
              |>.trans hsymm_rpow_isBigO
          · intro i
            exact f.contDiffAt_symm' ha hf' hf.contDiffAt |>.continuousAt_fderiv (mod_cast hk₀)
              |>.norm |>.isBoundedUnder_le
          · exact fun _ ↦ isBoundedUnder_const
          · refine fun i ↦ hfderiv_isBigO.trans (.trans (.trans ?_ hsymm_isBigO.norm_right) hrpow)
            exact hf.contDiffAt.fderiv_right (mod_cast hk₁) |>.differentiableAt one_ne_zero
              |>.isBigO_sub |>.comp_tendsto <| f.continuousAt_symm ha
