/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.LimitStageCore
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Finite-coordinate truncations in l-one

These are the common finite truncations used in the coherent limit-stage
argument.  They converge to the original vector and never increase pairwise
distance.
-/

namespace ScottishBook155

open ENNReal Filter lp

universe u


/-- Keep exactly the coordinates in a finite set. -/
noncomputable def lpTruncation {ι : Type u} (s : Finset ι) (f : ℓ^1(ι, ℝ)) :
    ℓ^1(ι, ℝ) := by
  classical
  exact ∑ i ∈ s, lp.single 1 i (f i)

open scoped Classical in
theorem lpTruncation_apply {ι : Type u} (s : Finset ι) (f : ℓ^1(ι, ℝ)) (i : ι) :
    lpTruncation s f i = if i ∈ s then f i else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lpTruncation]
  | @insert a s ha ih =>
      rw [lpTruncation, Finset.sum_insert ha, ← lpTruncation]
      by_cases hia : i = a
      · subst a
        simp [ha, ih]
      · simp [hia, ih]

open scoped Classical in
theorem lpTruncation_zero {ι : Type u} (s : Finset ι) :
    lpTruncation s (0 : ℓ^1(ι, ℝ)) = 0 := by
  classical
  ext i
  simp [lpTruncation_apply]

open scoped Classical in
theorem lpTruncation_add {ι : Type u} (s : Finset ι) (f g : ℓ^1(ι, ℝ)) :
    lpTruncation s (f + g) = lpTruncation s f + lpTruncation s g := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [lpTruncation_apply, hi]

open scoped Classical in
theorem lpTruncation_smul {ι : Type u} (s : Finset ι) (c : ℝ) (f : ℓ^1(ι, ℝ)) :
    lpTruncation s (c • f) = c • lpTruncation s f := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [lpTruncation_apply, hi]

open scoped Classical in
theorem lpTruncation_sub {ι : Type u} (s : Finset ι) (f g : ℓ^1(ι, ℝ)) :
    lpTruncation s (f - g) = lpTruncation s f - lpTruncation s g := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [lpTruncation_apply, hi]

/-- Finite-coordinate truncation is contractive in the l-one norm. -/
theorem norm_lpTruncation_le {ι : Type u} (s : Finset ι) (f : ℓ^1(ι, ℝ)) :
    ‖lpTruncation s f‖ ≤ ‖f‖ := by
  classical
  have heq := lp.norm_sum_single (p := (1 : ℝ≥0∞))
    (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (fun i => f i) s
  have hle := lp.sum_rpow_le_norm_rpow
    (by norm_num : 0 < (1 : ℝ≥0∞).toReal) f s
  simpa [lpTruncation] using heq.le.trans hle

theorem dist_lpTruncation_le {ι : Type u} (s : Finset ι) (f g : ℓ^1(ι, ℝ)) :
    dist (lpTruncation s f) (lpTruncation s g) ≤ dist f g := by
  rw [dist_eq_norm, ← lpTruncation_sub, dist_eq_norm]
  exact norm_lpTruncation_le s (f - g)

/-- Finite truncations converge along the directed set of finite subsets. -/
theorem lpTruncation_tendsto {ι : Type u} (f : ℓ^1(ι, ℝ)) :
    Tendsto (fun s : Finset ι => lpTruncation s f) atTop (nhds f) := by
  classical
  simpa only [lpTruncation, HasSum, SummationFilter.unconditional_filter] using
    (lp.hasSum_single (E := fun _ : ι => ℝ) (p := (1 : ℝ≥0∞)) (by simp) f)

/-- Restrict an l-one vector to an arbitrary set of coordinates. -/
noncomputable def lpSetTruncation {ι : Type u} (A : Set ι) (f : ℓ^1(ι, ℝ)) :
    ℓ^1(ι, ℝ) :=
  ⟨A.indicator f, f.2.mono' fun i => by
    by_cases hi : i ∈ A <;> simp [Set.indicator, hi]⟩

@[simp]
theorem lpSetTruncation_apply {ι : Type u} (A : Set ι) (f : ℓ^1(ι, ℝ)) (i : ι) :
    lpSetTruncation A f i = A.indicator f i :=
  rfl

section L1Product

variable {M : Type*}

/-- The l-one sum of a normed space and an l-one coordinate space. -/
abbrev L1ExtensionSpace (M : Type*) (ι : Type u) := WithLp 1 (M × ℓ^1(ι, ℝ))

/-- Leave the first summand fixed and truncate the l-one coordinates. -/
noncomputable def l1ExtensionTruncation {ι : Type u} (s : Finset ι)
    (x : L1ExtensionSpace M ι) : L1ExtensionSpace M ι :=
  WithLp.toLp 1 (x.fst, lpTruncation s x.snd)

/-- Leave the first summand fixed and restrict the l-one tail to an arbitrary
set of coordinates. -/
noncomputable def l1ExtensionSetTruncation {ι : Type u} (A : Set ι)
    (x : L1ExtensionSpace M ι) : L1ExtensionSpace M ι :=
  WithLp.toLp 1 (x.fst, lpSetTruncation A x.snd)

@[simp]
theorem l1ExtensionSetTruncation_fst {ι : Type u} (A : Set ι)
    (x : L1ExtensionSpace M ι) :
    (l1ExtensionSetTruncation A x).fst = x.fst :=
  rfl

@[simp]
theorem l1ExtensionSetTruncation_snd {ι : Type u} (A : Set ι)
    (x : L1ExtensionSpace M ι) :
    (l1ExtensionSetTruncation A x).snd = lpSetTruncation A x.snd :=
  rfl

@[simp]
theorem l1ExtensionTruncation_fst {ι : Type u} (s : Finset ι)
    (x : L1ExtensionSpace M ι) :
    (l1ExtensionTruncation s x).fst = x.fst :=
  rfl

@[simp]
theorem l1ExtensionTruncation_snd {ι : Type u} (s : Finset ι)
    (x : L1ExtensionSpace M ι) :
    (l1ExtensionTruncation s x).snd = lpTruncation s x.snd :=
  rfl

variable [NormedAddCommGroup M]

theorem l1ExtensionTruncation_zero {ι : Type u} (s : Finset ι) :
    l1ExtensionTruncation (M := M) s 0 = 0 := by
  apply WithLp.ofLp_injective 1
  exact Prod.ext (by simp) (lpTruncation_zero s)

theorem l1ExtensionTruncation_add {ι : Type u} (s : Finset ι)
    (x y : L1ExtensionSpace M ι) :
    l1ExtensionTruncation s (x + y) =
      l1ExtensionTruncation s x + l1ExtensionTruncation s y := by
  apply WithLp.ofLp_injective 1
  exact Prod.ext (by simp) (lpTruncation_add s x.snd y.snd)

theorem l1ExtensionTruncation_smul [NormedSpace ℝ M] {ι : Type u}
    (s : Finset ι) (c : ℝ)
    (x : L1ExtensionSpace M ι) :
    l1ExtensionTruncation s (c • x) = c • l1ExtensionTruncation s x := by
  apply WithLp.ofLp_injective 1
  exact Prod.ext (by simp) (lpTruncation_smul s c x.snd)

/-- A common coordinate truncation never increases the distance of two points. -/
theorem dist_l1ExtensionTruncation_le {ι : Type u} (s : Finset ι)
    (x y : L1ExtensionSpace M ι) :
    dist (l1ExtensionTruncation s x) (l1ExtensionTruncation s y) ≤ dist x y := by
  rw [WithLp.prod_dist_eq_of_L1, WithLp.prod_dist_eq_of_L1]
  simp only [l1ExtensionTruncation_fst, l1ExtensionTruncation_snd]
  exact add_le_add (le_refl _) (dist_lpTruncation_le s x.snd y.snd)

/-- Product truncations converge while keeping the first summand fixed. -/
theorem l1ExtensionTruncation_tendsto {ι : Type u} (x : L1ExtensionSpace M ι) :
    Tendsto (fun s : Finset ι => l1ExtensionTruncation s x) atTop (nhds x) := by
  have hprod : Tendsto (fun s : Finset ι => (x.fst, lpTruncation s x.snd)) atTop
      (nhds (x.fst, x.snd)) := by
    rw [nhds_prod_eq]
    exact tendsto_const_nhds.prodMk (lpTruncation_tendsto x.snd)
  have hx : WithLp.toLp 1 (x.fst, x.snd) = x := rfl
  change Tendsto (WithLp.toLp 1 ∘ fun s : Finset ι =>
    (x.fst, lpTruncation s x.snd)) atTop (nhds x)
  rw [← hx]
  exact (WithLp.prod_continuous_toLp (p := (1 : ℝ≥0∞)) M
    (ℓ^1(ι, ℝ))).continuousAt.tendsto.comp hprod

/-- The same directed family of finite sets simultaneously approximates a
pair, with its distance controlled at every stage. -/
theorem l1ExtensionTruncation_common {ι : Type u}
    (x y : L1ExtensionSpace M ι) :
    Tendsto (fun s : Finset ι => l1ExtensionTruncation s x) atTop (nhds x) ∧
    Tendsto (fun s : Finset ι => l1ExtensionTruncation s y) atTop (nhds y) ∧
    ∀ s, dist (l1ExtensionTruncation s x) (l1ExtensionTruncation s y) ≤ dist x y :=
  ⟨l1ExtensionTruncation_tendsto x, l1ExtensionTruncation_tendsto y,
    fun s => dist_l1ExtensionTruncation_le s x y⟩

/-- If a continuous map preserves the distances of every common finite
truncation, then it preserves the corresponding distance in the full l-one
sum. -/
theorem preservesUpTo_of_l1ExtensionTruncations
    {ι : Type u} {N : Type*} [MetricSpace N]
    {V : L1ExtensionSpace M ι → N} {r : ℝ}
    (hV : Continuous V)
    (hfinite : ∀ (s : Finset ι) (x y : L1ExtensionSpace M ι),
      dist (l1ExtensionTruncation s x) (l1ExtensionTruncation s y) ≤ r →
      dist (V (l1ExtensionTruncation s x))
          (V (l1ExtensionTruncation s y)) =
        dist (l1ExtensionTruncation s x) (l1ExtensionTruncation s y)) :
    PreservesUpTo r V := by
  intro x y hxy
  have hx := l1ExtensionTruncation_tendsto x
  have hy := l1ExtensionTruncation_tendsto y
  have himage : Tendsto (fun s : Finset ι =>
      dist (V (l1ExtensionTruncation s x))
        (V (l1ExtensionTruncation s y))) atTop
      (nhds (dist (V x) (V y))) :=
    ((hV.tendsto x).comp hx).dist ((hV.tendsto y).comp hy)
  have hsource : Tendsto (fun s : Finset ι =>
      dist (V (l1ExtensionTruncation s x))
        (V (l1ExtensionTruncation s y))) atTop (nhds (dist x y)) := by
    apply (hx.dist hy).congr'
    filter_upwards [] with s
    exact (hfinite s x y
      ((dist_l1ExtensionTruncation_le s x y).trans hxy)).symm
  exact tendsto_nhds_unique himage hsource

omit [NormedAddCommGroup M] in
/-- Prefix restrictions which eventually contain every coordinate jointly
separate the l-one sum. -/
lemma eq_of_eventually_l1ExtensionSetTruncation_eq
    {ι : Type u} {A : Type*} {l : Filter A} [NeBot l]
    (sets : A → Set ι) (hcover : ∀ i, ∀ᶠ a in l, i ∈ sets a)
    {x y : L1ExtensionSpace M ι}
    (hxy : ∀ᶠ a in l,
      l1ExtensionSetTruncation (sets a) x =
        l1ExtensionSetTruncation (sets a) y) :
    x = y := by
  apply WithLp.ofLp_injective 1
  apply Prod.ext
  · obtain ⟨a, ha⟩ := hxy.exists
    have ha' : (l1ExtensionSetTruncation (sets a) x).fst =
        (l1ExtensionSetTruncation (sets a) y).fst :=
      congrArg (fun z : L1ExtensionSpace M ι => z.fst) ha
    simpa using ha'
  · apply Subtype.ext
    funext i
    obtain ⟨a, ha, hai⟩ := (hxy.and (hcover i)).exists
    have hsnd := congrArg WithLp.snd ha
    have happ := congrArg (fun f : ℓ^1(ι, ℝ) => f i) hsnd
    simpa [lpSetTruncation_apply, Set.indicator_of_mem hai] using happ

end L1Product

end ScottishBook155
