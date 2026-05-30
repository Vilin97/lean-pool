/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Tactic
import LeanPool.SardMoreira.ToMathlib.ContinuousLinearMap

open scoped unitInterval Topology NNReal
open Function Asymptotics Filter Set

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E → F} {s : Set E}

section NWithTopENat
variable {n : WithTop ℕ∞} {k : ℕ} {a : E}

theorem ContDiffOn.continuousAt_iteratedFDerivWithin (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (ha : s ∈ 𝓝 a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDerivWithin 𝕜 k f s) a :=
  (hf.continuousOn_iteratedFDerivWithin hk hs).continuousAt ha

theorem ContDiffAt.eventually_isInvertible_fderiv [CompleteSpace E] (hf : ContDiffAt 𝕜 n f a)
    (ha : (fderiv 𝕜 f a).IsInvertible) (hn : n ≠ 0) :
    ∀ᶠ x in 𝓝 a, (fderiv 𝕜 f x).IsInvertible :=
  ha.eventually <| hf.continuousAt_fderiv hn

end NWithTopENat

namespace OrderedFinpartition

variable {n : ℕ} (c : OrderedFinpartition n)

@[simp]
theorem sum_partSize : ∑ i, c.partSize i = n := calc
  ∑ i, c.partSize i = Fintype.card (Σ i, Fin (c.partSize i)) := by simp
  _ = n := by rw [Fintype.card_congr c.equivSigma, Fintype.card_fin]

@[simp]
theorem length_eq_zero : c.length = 0 ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ nonpos_iff_eq_zero.mp <| h ▸ c.length_le⟩
  rw [← c.sum_partSize, Finset.sum_eq_zero]
  simp [(c.partSize_pos _).ne', h]

@[simp] theorem length_pos_iff : 0 < c.length ↔ 0 < n := by simp [pos_iff_ne_zero]

theorem length_eq_iff : c.length = n ↔ c = atomic n := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have H₀ := c.sum_partSize
  cases c with | _ length partSize partSize_pos emb emb_strictMono parts_strictMono disjoint cover
  dsimp at *
  subst h
  obtain rfl : partSize = fun _ ↦ 1 := by
    suffices ∀ i ∈ Finset.univ, 1 = partSize i by simpa [eq_comm, funext_iff] using this
    rw [← Finset.sum_eq_sum_iff_of_le]
    · simp [H₀]
    · exact fun i _ ↦ partSize_pos i
  obtain rfl : emb = fun i _ ↦ i := by
    suffices ∀ i, emb i 0 = i by
      ext i j : 2
      convert this i
    rw [← funext_iff, ← StrictMono.range_inj, Surjective.range_eq, Surjective.range_eq]
    exacts [surjective_id, Finite.surjective_of_injective parts_strictMono.injective,
      parts_strictMono, strictMono_id]
  rfl

theorem length_lt_iff : c.length < n ↔ c ≠ atomic n := by
  rw [c.length_le.lt_iff_ne]
  exact c.length_eq_iff.not

theorem compContinuousLinearMap_compAlongOrderedFinpartition_left
    {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (f : F [×c.length]→L[𝕜] G) (g : ∀ i, E [×c.partSize i]→L[𝕜] F) (h : H →L[𝕜] E) :
    (c.compAlongOrderedFinpartition f g).compContinuousLinearMap (fun _ ↦ h) =
      c.compAlongOrderedFinpartition f fun i ↦ (g i).compContinuousLinearMap fun _ ↦ h := by
  ext
  simp [applyOrderedFinpartition_apply, Function.comp_def]

variable
    {α : Type*} {l : Filter α} {p₁ p₂ : α → F [×c.length]→L[𝕜] G}
    {q₁ q₂ : α → ∀ m, E [×c.partSize m]→L[𝕜] F} {B : α → ℝ} {i : ℕ}

theorem compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
    (hp_bdd : l.IsBoundedUnder (· ≤ ·) (‖p₁ ·‖))
    (hpB : (fun x ↦ p₁ x - p₂ x) =O[l] B)
    (hq₁_bdd : ∀ m, l.IsBoundedUnder (· ≤ ·) (‖q₁ · m‖))
    (hq₂_bdd : ∀ m, l.IsBoundedUnder (· ≤ ·) (‖q₂ · m‖))
    (hqB : ∀ m, (fun x ↦ q₁ x m - q₂ x m) =O[l] B) :
    (fun x ↦ (c.compAlongOrderedFinpartition (p₁ x) fun m ↦ q₁ x m) -
        c.compAlongOrderedFinpartition (p₂ x) fun m ↦ q₂ x m) =O[l] B := by
  refine .trans (.of_norm_le fun _ ↦
    c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le ..) ?_
  refine .add ?_ ?_
  · simp only [← isBigO_one_iff ℝ, ← isBigO_pi] at *
    have H := ((hq₁_bdd.prod_left hq₂_bdd).norm_left.pow (c.length - 1)).mul hqB.norm_left
    simpa [mul_assoc] using hp_bdd.norm_left.mul <| H.const_mul_left c.length
  · have H₂ : ∀ i, (q₂ · i) =O[l] (1 : α → ℝ) := fun i ↦ (hq₂_bdd i).isBigO_one ℝ
    simpa using hpB.norm_left.mul <| .finsetProd fun i _ ↦ (H₂ i).norm_left

end OrderedFinpartition

namespace FormalMultilinearSeries

/-- The formal Taylor left inverse of a formal multilinear series at a point. -/
noncomputable def taylorLeftInv (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    FormalMultilinearSeries 𝕜 F E := fun n ↦
  FormalMultilinearSeries.id 𝕜 E x n -
    ∑ c : {c : OrderedFinpartition n // c.length < n},
      c.val.compAlongOrderedFinpartition (taylorLeftInv p x c.val.length)
        (fun m ↦ p (c.val.partSize m)) |>.compContinuousLinearMap fun _ ↦
          continuousMultilinearCurryFin1 𝕜 E F (p 1) |>.inverse

@[simp]
theorem taylorLeftInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    p.taylorLeftInv x 0 = .uncurry0 𝕜 F x := by
  have : IsEmpty {c : OrderedFinpartition 0 // c.length < 0} := by constructor; simp
  rw [taylorLeftInv, Fintype.sum_empty]
  ext
  simp

end FormalMultilinearSeries

variable {n : WithTop ℕ∞}

@[simp]
theorem ftaylorSeries_id (x : E) : ftaylorSeries 𝕜 id x = .id 𝕜 E x := by
  unfold ftaylorSeries
  ext (_ | _ | n) v <;> simp [iteratedFDeriv_succ_apply_right, FormalMultilinearSeries.id]

theorem ContinuousLinearMap.IsInvertible.hasFDerivAt {f : E → F} {x : E}
    (h : (fderiv 𝕜 f x).IsInvertible) : HasFDerivAt f (h.choose : E →L[𝕜] F) x := by
  rw [h.choose_spec]
  exact differentiableAt_of_isInvertible_fderiv h |>.hasFDerivAt

theorem OpenPartialHomeomorph.hasFDerivAt_symm_inverse (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    HasFDerivAt f.symm (fderiv 𝕜 f (f.symm y)).inverse y := by
  rw [ContinuousLinearMap.inverse, dif_pos hf']
  exact hf'.hasFDerivAt.of_local_left_inverse (f.symm.continuousAt hy)
    <| f.eventually_right_inverse hy

theorem OpenPartialHomeomorph.fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    fderiv 𝕜 f.symm y = (fderiv 𝕜 f (f.symm y)).inverse :=
  f.hasFDerivAt_symm_inverse hy hf' |>.fderiv

theorem OpenPartialHomeomorph.bijective_fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    Bijective (fderiv 𝕜 f.symm y) := by
  rw [f.fderiv_symm hy hf']
  exact hf'.inverse.bijective

theorem OpenPartialHomeomorph.surjective_fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    Surjective (fderiv 𝕜 f.symm y) :=
  f.bijective_fderiv_symm hy hf' |>.surjective

theorem OpenPartialHomeomorph.injective_fderiv_symm (f : OpenPartialHomeomorph E F) {y : F}
    (hy : y ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    Injective (fderiv 𝕜 f.symm y) :=
  f.bijective_fderiv_symm hy hf' |>.injective

theorem OpenPartialHomeomorph.contDiffAt_symm' [CompleteSpace E] (f : OpenPartialHomeomorph E F)
    {a : F} (ha : a ∈ f.target) (hf' : (fderiv 𝕜 f (f.symm a)).IsInvertible)
    (hf : ContDiffAt 𝕜 n f (f.symm a)) : ContDiffAt 𝕜 n f.symm a := by
  exact f.contDiffAt_symm ha hf'.hasFDerivAt hf

theorem iteratedFDeriv_one_eq (f : E → F) (x : E) :
    iteratedFDeriv 𝕜 1 f x = (continuousMultilinearCurryFin1 𝕜 E F).symm (fderiv 𝕜 f x) := by
  ext; simp

theorem OpenPartialHomeomorph.iteratedFDeriv_symm_eq_rec [CompleteSpace E]
    (f : OpenPartialHomeomorph E F) {y : F} (hy : y ∈ f.target) (hf : ContDiffAt 𝕜 n f (f.symm y))
    {i : ℕ} (hi : i ≤ n) (hf' : 0 < i → (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    iteratedFDeriv 𝕜 i f.symm y =
      (FormalMultilinearSeries.id 𝕜 E (f.symm y) i -
        ∑ c ≠ OrderedFinpartition.atomic i,
          c.compAlongOrderedFinpartition (iteratedFDeriv 𝕜 c.length f.symm y)
            (fun m ↦ iteratedFDeriv 𝕜 (c.partSize m) f (f.symm y))).compContinuousLinearMap
      fun _ ↦ fderiv 𝕜 f.symm y := by
  rcases i.eq_zero_or_pos with rfl | hi₀
  · ext
    simp
  · specialize hf' hi₀
    rcases hf' with ⟨f', hf'⟩
    replace hf' : HasFDerivAt f (f' : E →L[𝕜] F) (f.symm y) :=
      hf' ▸ (hf.of_le hi |>.differentiableAt <| mod_cast hi₀.ne').hasFDerivAt
    have H₁ : f.source ∈ 𝓝 (f.symm y) := f.open_source.mem_nhds <| f.symm_mapsTo hy
    have H₂ : ContDiffAt 𝕜 n f.symm (f (f.symm y)) := by
      rw [f.rightInvOn hy]
      exact f.contDiffAt_symm hy hf' hf
    have H₃ := calc
      (ftaylorSeries 𝕜 f.symm y).taylorComp (ftaylorSeries 𝕜 f (f.symm y)) i
      _ =  iteratedFDeriv 𝕜 i (f.symm ∘ f) (f.symm y) := by
        rw [iteratedFDeriv_comp H₂ hf hi, f.rightInvOn hy]
      _ = iteratedFDeriv 𝕜 i id (f.symm y) := by
        refine (EventuallyEq.iteratedFDeriv _ ?_ _).self_of_nhds
        filter_upwards [H₁] using f.leftInvOn
      _ = FormalMultilinearSeries.id 𝕜 E (f.symm y) i := by
        rw [← ftaylorSeries_id, ftaylorSeries]
    simp only [← H₃, FormalMultilinearSeries.taylorComp,
      FormalMultilinearSeries.compAlongOrderedFinpartition]
    rw [Fintype.sum_eq_add_sum_compl (OrderedFinpartition.atomic i), Finset.compl_singleton]
    ext v
    simp +unfoldPartialApp only [OrderedFinpartition.atomic_length,
      OrderedFinpartition.atomic_partSize, Finset.mem_univ, Finset.sum_erase_eq_sub,
      add_sub_cancel, sub_sub_cancel,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      OrderedFinpartition.compAlongOrderFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition, ftaylorSeries,
      iteratedFDeriv_one_eq, hf'.fderiv, (f.hasFDerivAt_symm hy hf').fderiv,
      Function.comp_def, OrderedFinpartition.atomic_emb]
    refine congrArg (iteratedFDeriv 𝕜 i (↑f.symm) y) (funext fun m ↦ ?_)
    exact (f'.apply_symm_apply _).symm

theorem OpenPartialHomeomorph.iteratedFDeriv_symm_eq_taylorLeftInv [CompleteSpace E]
    (f : OpenPartialHomeomorph E F) {y : F} (hy : y ∈ f.target) (hf : ContDiffAt 𝕜 n f (f.symm y))
    {i : ℕ} (hi : i ≤ n) (hf' : 0 < i → (fderiv 𝕜 f (f.symm y)).IsInvertible) :
    iteratedFDeriv 𝕜 i f.symm y =
      (ftaylorSeries 𝕜 f (f.symm y)).taylorLeftInv (f.symm y) i := by
  fun_induction FormalMultilinearSeries.taylorLeftInv with | case1 i ih => ?_
  have H (c : OrderedFinpartition i) :
      c ∈ Finset.univ.erase (OrderedFinpartition.atomic i) ↔ c.length < i := by
    simp [OrderedFinpartition.length_lt_iff]
  rw [f.iteratedFDeriv_symm_eq_rec hy hf hi hf', Finset.sum_subtype (F := inferInstance) _ H]
  congr 3 with c : 1
  · rw [ih]
    · simp [ftaylorSeries]
    · exact le_trans (mod_cast c.2.le) hi
    · exact fun hc ↦ hf' <| hc.trans c.2
  · simp [ftaylorSeries, iteratedFDeriv_one_eq, f.fderiv_symm hy (hf' c.pos)]

namespace FormalMultilinearSeries

variable
    {α : Type*} {l : Filter α} {p₁ p₂ : α → FormalMultilinearSeries 𝕜 F G}
    {q₁ q₂ : α → FormalMultilinearSeries 𝕜 E F} {B : α → ℝ} {i n : ℕ}

theorem compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
    (hp_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖p₁ · k‖))
    (hpB : ∀ k ≤ n, (fun x ↦ p₁ x k - p₂ x k) =O[l] B)
    (hq₁_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₁ · k‖))
    (hq₂_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₂ · k‖))
    (hqB : ∀ k ≤ n, (fun x ↦ q₁ x k - q₂ x k) =O[l] B)
    (c : OrderedFinpartition n) :
    (fun x ↦ (p₁ x).compAlongOrderedFinpartition (q₁ x) c -
      (p₂ x).compAlongOrderedFinpartition (q₂ x) c) =O[l] B := by
  apply c.compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
  exacts [hp_bdd _ c.length_le, hpB _ c.length_le, fun _ ↦ hq₁_bdd _ (c.partSize_le _),
    fun _ ↦ hq₂_bdd _ (c.partSize_le _), fun _ ↦ hqB _ (c.partSize_le _)]

end FormalMultilinearSeries
