/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhysicalStageBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Topology.ExtendFrom
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialBorelExtension
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Off-plane endpoint extensions from actual raw jets

A compact spacetime localization converts bounds on every actual derivative
in a past half-ball into a genuine smooth extension.  The physical scale is
then localized away from zero, so raw power-logarithmic jet bounds supply
the required estimates without a recursive continuation assumption.
-/

section

/-!
# A dimension-independent smooth extension of a bounded-jet open strip

The endpoint values below are derived from bounds on the actual joint
Frechet derivatives, using completeness and the mean-value theorem. The
normal-jet gluing argument is generalized from `SpacetimeGluing`; no existing
project source is altered and no extension or closed-side regularity is assumed.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.GenericEndpointExtension.Gluing

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- Time vector, given by `(1, 0)`. -/
noncomputable def timeVector : (ℝ × X) := (1, 0)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Directional, given by `fderivWithin ℝ f s z v`. -/
noncomputable def directional (s : Set (ℝ × X)) (f : (ℝ × X) → V) (v : (ℝ × X))
    (z : (ℝ × X)) : V := fderivWithin ℝ f s z v

/-- Normal iter as an element of `ℕ → (ℝ × X) → V | 0 => f | n + 1 => directional s (normalIter
s f n) timeVector`. -/
noncomputable def normalIter (s : Set (ℝ × X)) (f : (ℝ × X) → V) : ℕ → (ℝ × X) → V
  | 0 => f
  | n + 1 => directional s (normalIter s f n) timeVector

omit [FiniteDimensional ℝ X] in
theorem directional_contDiffOn {s : Set (ℝ × X)} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (v : (ℝ × X)) :
    ContDiffOn ℝ ∞ (directional s f v) s :=
  (hf.fderivWithin hs infty_add_one_le).clm_apply contDiffOn_const

omit [FiniteDimensional ℝ X] in
theorem normalIter_contDiffOn {s : Set (ℝ × X)} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (n : ℕ) :
    ContDiffOn ℝ ∞ (normalIter s f n) s := by
  induction n with
  | zero => exact hf
  | succ n ih => exact directional_contDiffOn ih hs timeVector

omit [FiniteDimensional ℝ X] in
/-- Schwarz's theorem commutes two fixed directional derivatives on a
regular closed domain; no symmetry of full higher tensors is assumed. -/
theorem directional_commute {s : Set (ℝ × X)} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s)
    (hregular : s ⊆ closure (interior s)) {z : (ℝ × X)} (hz : z ∈ s)
    (v w : (ℝ × X)) :
    directional s (directional s f v) w z =
      directional s (directional s f w) v z := by
  have hd := ((hf.fderivWithin hs infty_add_one_le).differentiableOn (by simp)) z hz
  have hv := fderivWithin_clm_apply (c := fderivWithin ℝ f s) (u := fun _ => v)
    (hs z hz) hd (differentiableWithinAt_const v)
  have hw := fderivWithin_clm_apply (c := fderivWithin ℝ f s) (u := fun _ => w)
    (hs z hz) hd (differentiableWithinAt_const w)
  unfold directional
  rw [hv, hw]
  simp only [fderivWithin_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact ((hf z hz).isSymmSndFDerivWithinAt
    (by
        rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.natCast_le_of_coe_top_le_withTop
            le_rfl 2)
    hs (hregular hz) hz).eq w v

omit [FiniteDimensional ℝ X] in
/-- Any fixed directional derivative commutes with every normal iterate. -/
theorem normalIter_directional {s : Set (ℝ × X)} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s)
    (hregular : s ⊆ closure (interior s)) (v : (ℝ × X)) (n : ℕ) :
    EqOn (normalIter s (directional s f v) n)
      (directional s (normalIter s f n) v) s := by
  induction n with
  | zero => intro z hz; rfl
  | succ n ih =>
    intro z hz
    change directional s (normalIter s (directional s f v) n) timeVector z =
      directional s (directional s (normalIter s f n) timeVector) v z
    have heq := fderivWithin_congr' (𝕜 := ℝ) ih hz
    change fderivWithin ℝ (normalIter s (directional s f v) n) s z timeVector = _
    rw [heq]
    exact directional_commute (normalIter_contDiffOn hf hs n) hs hregular hz v timeVector

omit [FiniteDimensional ℝ X] in
/-- The joint normal iterates equal the genuine one-dimensional derivatives
of the time slice, including at a one-sided boundary. -/
theorem time_slice_iteratedDerivWithin {I : Set ℝ} {f : (ℝ × X) → V}
    (hI : UniqueDiffOn ℝ I) (hf : ContDiffOn ℝ ∞ f (I ×ˢ univ))
    (x : X) (n : ℕ) :
    EqOn (iteratedDerivWithin n (fun t => f (t, x)) I)
      (fun t => normalIter (I ×ˢ univ) f n (t, x)) I := by
  induction n with
  | zero => simp only [iteratedDerivWithin_zero, normalIter, eqOn_refl]
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih ht)]
    have hsmooth := normalIter_contDiffOn hf (hI.prod uniqueDiffOn_univ) n
    have hdiff := hsmooth.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩
    have hcurve := hdiff.hasFDerivWithinAt.comp t
      (hasFDerivAt_prodMk_left t x).hasFDerivWithinAt
      (fun y hy => show (y, x) ∈ I ×ˢ univ from ⟨hy, mem_univ x⟩)
    have hderiv : HasDerivWithinAt (fun y => normalIter (I ×ˢ univ) f n (y, x))
        (normalIter (I ×ˢ univ) f (n + 1) (t, x)) I t := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply, normalIter, directional, timeVector] using
        hcurve.hasDerivWithinAt
    exact hderiv.derivWithin (hI t ht)

omit [FiniteDimensional ℝ X] in
/-- Matching boundary values gives matching tangential derivatives; together
with the first normal derivative this determines the full Frechet derivative. -/
theorem boundary_fderiv_eq {s t : Set (ℝ × X)} {f g : (ℝ × X) → V} {T : ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g t)
    (hBs : ∀ x : X, (T, x) ∈ s) (hBt : ∀ x : X, (T, x) ∈ t)
    (hvalue : ∀ x : X, f (T, x) = g (T, x))
    (hnormal : ∀ x : X, directional s f timeVector (T, x) =
      directional t g timeVector (T, x)) (x : X) :
    fderivWithin ℝ f s (T, x) = fderivWithin ℝ g t (T, x) := by
  have hfD := (hf.differentiableOn (by simp) (T, x) (hBs x)).hasFDerivWithinAt
  have hgD := (hg.differentiableOn (by simp) (T, x) (hBt x)).hasFDerivWithinAt
  have hftrace : HasFDerivAt (fun y : X => f (T, y))
      ((fderivWithin ℝ f s (T, x)).comp (ContinuousLinearMap.inr ℝ ℝ X)) x := by
    have h := hfD.comp x (s := univ) (hasFDerivAt_prodMk_right T x).hasFDerivWithinAt
      (fun y _ => hBs y)
    simpa only [Function.comp_def, hasFDerivWithinAt_univ] using h
  have hgtrace : HasFDerivAt (fun y : X => g (T, y))
      ((fderivWithin ℝ g t (T, x)).comp (ContinuousLinearMap.inr ℝ ℝ X)) x := by
    have h := hgD.comp x (s := univ) (hasFDerivAt_prodMk_right T x).hasFDerivWithinAt
      (fun y _ => hBt y)
    simpa only [Function.comp_def, hasFDerivWithinAt_univ] using h
  have htan := hftrace.unique (hgtrace.congr_of_eventuallyEq (Eventually.of_forall hvalue))
  apply ContinuousLinearMap.ext
  intro v
  have hspatial := congrArg (fun A : X →L[ℝ] V => A v.2) htan
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hspatial
  have htime : fderivWithin ℝ f s (T, x) timeVector =
      fderivWithin ℝ g t (T, x) timeVector := hnormal x
  have hv : v = v.1 • timeVector + (0, v.2) := by
    ext <;> simp [timeVector]
  rw [hv, map_add, map_add, map_smul, map_smul, htime, hspatial]

omit [FiniteDimensional ℝ X] in
/-- Matching normal trace functions implies matching normal traces after
any directional derivative. The proof derives, rather than assumes, the
necessary tangential and mixed derivative equalities. -/
theorem normal_match_directional {s t : Set (ℝ × X)} {f g : (ℝ × X) → V} {T : ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g t)
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hregularS : s ⊆ closure (interior s)) (hregularT : t ⊆ closure (interior t))
    (hBs : ∀ x : X, (T, x) ∈ s) (hBt : ∀ x : X, (T, x) ∈ t)
    (hmatch : ∀ n : ℕ, ∀ x : X, normalIter s f n (T, x) = normalIter t g n (T, x))
    (v : (ℝ × X)) (n : ℕ) (x : X) :
    normalIter s (directional s f v) n (T, x) =
      normalIter t (directional t g v) n (T, x) := by
  rw [normalIter_directional hf hs hregularS v n (hBs x),
    normalIter_directional hg ht hregularT v n (hBt x)]
  have hD := boundary_fderiv_eq (normalIter_contDiffOn hf hs n)
    (normalIter_contDiffOn hg ht n) hBs hBt (hmatch n) (hmatch (n + 1)) x
  exact congrArg (fun A : (ℝ × X) →L[ℝ] V => A v) hD

/-- Past, given by `Iic T ×ˢ univ`. -/
noncomputable def past (T : ℝ) : Set (ℝ × X) := Iic T ×ˢ univ
/-- Future, given by `Ici T ×ˢ univ`. -/
noncomputable def future (T : ℝ) : Set (ℝ × X) := Ici T ×ˢ univ

omit [FiniteDimensional ℝ X] in
theorem past_uniqueDiff (T : ℝ) : UniqueDiffOn ℝ (past (X := X) T) :=
  (uniqueDiffOn_Iic T).prod uniqueDiffOn_univ

omit [FiniteDimensional ℝ X] in
theorem future_uniqueDiff (T : ℝ) : UniqueDiffOn ℝ (future (X := X) T) :=
  (uniqueDiffOn_Ici T).prod uniqueDiffOn_univ

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem past_regular (T : ℝ) : past (X := X) T ⊆ closure (interior (past T)) := by
  simp only [past, interior_prod_eq, interior_Iic,
    interior_univ, closure_prod_eq, closure_Iio, closure_univ]
  exact Subset.rfl

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem future_regular (T : ℝ) : future (X := X) T ⊆ closure (interior (future T)) := by
  simp only [future, interior_prod_eq, interior_Ici, interior_univ, closure_prod_eq,
    closure_Ioi, closure_univ]
  exact Subset.rfl

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem past_union_future (T : ℝ) : past (X := X) T ∪ future T = univ := by
  ext z
  simp only [past, future, mem_union, mem_prod,
    mem_Iic, mem_Ici, mem_univ, and_true, iff_true]
  exact le_total z.1 T

/-- Glue along the time hyperplane, using the past branch at the join. -/
noncomputable def glue {W : Type*} (T : ℝ) (f g : (ℝ × X) → W) (z : (ℝ × X)) : W :=
  if z.1 ≤ T then f z else g z

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem glue_eqOn_past {W : Type*} (T : ℝ) (f g : (ℝ × X) → W) :
    EqOn (glue T f g) f (past T) := by
  intro z hz
  exact ite_eq_left hz.1

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem glue_eqOn_future {W : Type*} {T : ℝ} {f g : (ℝ × X) → W}
    (hvalue : ∀ x : X, f (T, x) = g (T, x)) :
    EqOn (glue T f g) g (future T) := by
  rintro ⟨t, x⟩ ht
  by_cases h : t ≤ T
  · have heq : t = T := le_antisymm h ht.1
    subst t
    exact (ite_eq_left le_rfl).trans (hvalue x)
  · exact ite_eq_right h

omit [FiniteDimensional ℝ X] in
/-- Actual full Frechet derivatives glue when their boundary values match. -/
theorem hasFDerivAt_glue {T : ℝ} {f g : (ℝ × X) → V}
    {df dg : (ℝ × X) → (ℝ × X) →L[ℝ] V}
    (hf : ∀ z ∈ past T, HasFDerivWithinAt f (df z) (past T) z)
    (hg : ∀ z ∈ future T, HasFDerivWithinAt g (dg z) (future T) z)
    (hvalue : ∀ x : X, f (T, x) = g (T, x))
    (hderiv : ∀ x : X, df (T, x) = dg (T, x)) (z : (ℝ × X)) :
    HasFDerivAt (glue T f g) (glue T df dg z) z := by
  have hL (y : (ℝ × X)) (hy : y ∈ past T) :
      HasFDerivWithinAt (glue T f g) (df y) (past T) y :=
    (hf y hy).congr' (glue_eqOn_past T f g) hy
  have hR (y : (ℝ × X)) (hy : y ∈ future T) :
      HasFDerivWithinAt (glue T f g) (dg y) (future T) y :=
    (hg y hy).congr' (glue_eqOn_future hvalue) hy
  rcases z with ⟨t, x⟩
  rcases lt_trichotomy t T with hlt | heq | hgt
  · have hmem : past T ∈ 𝓝 (t, x) :=
      prod_mem_nhds (Iic_mem_nhds hlt) Filter.univ_mem
    simpa only [glue, ite_eq_left hlt.le] using
      (hL (t, x) ⟨hlt.le, mem_univ x⟩).hasFDerivAt hmem
  · subst t
    have hright : HasFDerivWithinAt (glue T f g) (df (T, x))
        (future T) (T, x) := by
      rw [hderiv x]
      exact hR (T, x) ⟨mem_Ici.mpr (le_refl T), mem_univ x⟩
    have h := (hL (T, x) ⟨mem_Iic.mpr (le_refl T), mem_univ x⟩).union hright
    simpa only [past_union_future, hasFDerivWithinAt_univ, glue, ite_eq_left le_rfl] using h
  · have hmem : future T ∈ 𝓝 (t, x) :=
      prod_mem_nhds (Ici_mem_nhds hgt) Filter.univ_mem
    simpa only [glue, ite_eq_right (not_le_of_gt hgt)] using
      (hR (t, x) ⟨hgt.le, mem_univ x⟩).hasFDerivAt hmem

omit [FiniteDimensional ℝ X] in
/-- First-order joint gluing needs only value and first normal-derivative
matching; spatial derivative matching is a consequence. -/
theorem hasFDerivAt_glue_of_normal {T : ℝ} {f g : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (hg : ContDiffOn ℝ ∞ g (future T))
    (hvalue : ∀ x : X, f (T, x) = g (T, x))
    (hnormal : ∀ x : X, directional (past T) f timeVector (T, x) =
      directional (future T) g timeVector (T, x)) (z : (ℝ × X)) :
    HasFDerivAt (glue T f g)
      (glue T (fderivWithin ℝ f (past T)) (fderivWithin ℝ g (future T)) z) z := by
  apply hasFDerivAt_glue
  · intro y hy
    exact (hf.differentiableOn (by simp) y hy).hasFDerivWithinAt
  · intro y hy
    exact (hg.differentiableOn (by simp) y hy).hasFDerivWithinAt
  · exact hvalue
  · exact boundary_fderiv_eq hf hg (fun x => ⟨mem_Iic.mpr (le_refl T), mem_univ x⟩)
      (fun x => ⟨mem_Ici.mpr (le_refl T), mem_univ x⟩) hvalue hnormal

/-- Finite-order induction from all matching normal jets. The induction
keeps the codomain fixed and differentiates in each spacetime direction. -/
theorem contDiff_glue_finite {T : ℝ} {f g : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (hg : ContDiffOn ℝ ∞ g (future T))
    (hmatch : ∀ n : ℕ, ∀ x : X,
      normalIter (past T) f n (T, x) = normalIter (future T) g n (T, x))
    (m : ℕ) : ContDiff ℝ m (glue T f g) := by
  induction m generalizing f g with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr (fun z =>
      (hasFDerivAt_glue_of_normal hf hg (hmatch 0) (hmatch 1) z).continuousAt))
  | succ m ih =>
    have hD := hasFDerivAt_glue_of_normal hf hg (hmatch 0) (hmatch 1)
    have hsucc : ContDiff ℝ ((m : WithTop ℕ∞) + 1) (glue T f g) := by
      apply contDiff_succ_iff_fderiv_apply.mpr
      refine ⟨fun z => (hD z).differentiableAt, by simp, ?_⟩
      intro v
      have hdirection : (fun z => fderiv ℝ (glue T f g) z v) =
          glue T (directional (past T) f v) (directional (future T) g v) := by
        funext z
        rw [(hD z).fderiv]
        by_cases hz : z.1 ≤ T <;> simp only [glue, directional, hz, ite_true, ite_false]
      rw [hdirection]
      apply ih (directional_contDiffOn hf (past_uniqueDiff T) v)
        (directional_contDiffOn hg (future_uniqueDiff T) v)
      exact normal_match_directional hf hg (past_uniqueDiff T) (future_uniqueDiff T)
        (past_regular T) (future_regular T)
        (fun x => ⟨mem_Iic.mpr (le_refl T), mem_univ x⟩)
        (fun x => ⟨mem_Ici.mpr (le_refl T), mem_univ x⟩) hmatch v
    simpa only [Nat.cast_add, Nat.cast_one] using hsucc

/-- Joint `C∞` gluing, expressed in actual one-sided time-slice jets.
No matching of mixed Frechet tensors is assumed: it is derived from the
normal trace functions and Schwarz's theorem. -/
theorem contDiff_glue {T : ℝ} {f g : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (hg : ContDiffOn ℝ ∞ g (future T))
    (hmatch : ∀ n : ℕ, ∀ x : X,
      iteratedDerivWithin n (fun t => f (t, x)) (Iic T) T =
        iteratedDerivWithin n (fun t => g (t, x)) (Ici T) T) :
    ContDiff ℝ ∞ (glue T f g) := by
  apply contDiff_infty.mpr
  apply contDiff_glue_finite hf hg
  intro n x
  exact (time_slice_iteratedDerivWithin (uniqueDiffOn_Iic T) hf x n
    (mem_Iic.mpr (le_refl T))).symm.trans ((hmatch n x).trans
      (time_slice_iteratedDerivWithin (uniqueDiffOn_Ici T) hg x n
        (mem_Ici.mpr (le_refl T))))

/-- The actual normal jet of a closed-past field, viewed as a spatial
coefficient for the Taylor--Borel construction. -/
noncomputable def normalTrace (T : ℝ) (f : (ℝ × X) → V) (n : ℕ) (x : X) : V :=
  normalIter (past T) f n (T, x)

omit [FiniteDimensional ℝ X] in
theorem normalTrace_contDiff {T : ℝ} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (n : ℕ) :
    ContDiff ℝ ∞ (normalTrace T f n) := by
  exact (normalIter_contDiffOn hf (past_uniqueDiff T) n).comp_contDiff
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun x : X => (T, x)))
    (fun x => show (T, x) ∈ past T from ⟨le_refl T, mem_univ x⟩)

omit [FiniteDimensional ℝ X] in
theorem normalTrace_eq_time_jet {T : ℝ} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (n : ℕ) (x : X) :
    normalTrace T f n x = iteratedDerivWithin n (fun t => f (t, x)) (Iic T) T :=
  (time_slice_iteratedDerivWithin (uniqueDiffOn_Iic T) hf x n
    (mem_Iic.mpr (le_refl T))).symm

omit [FiniteDimensional ℝ X] in
theorem normalTrace_add_period {T : ℝ} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (p : X)
    (hperiod : ∀ t ≤ T, ∀ x : X, f (t, x + p) = f (t, x)) (n : ℕ) (x : X) :
    normalTrace T f n (x + p) = normalTrace T f n x := by
  rw [normalTrace_eq_time_jet hf, normalTrace_eq_time_jet hf]
  exact iteratedDerivWithin_congr (fun t ht => hperiod t ht x) (mem_Iic.mpr (le_refl T))

section Complete

variable [CompleteSpace V]

/-- A constructed global extension: join the closed-past field to the
Taylor--Borel realization of its actual normal jets. -/
noncomputable def smoothExtension (T : ℝ) (f : (ℝ × X) → V) (hf : ContDiffOn ℝ ∞ f (past T)) :
    (ℝ × X) → V :=
  glue T f (SpatialBorelExtension.rightExtension (normalTrace T f)
    (normalTrace_contDiff hf) T)

theorem smoothExtension_contDiff {T : ℝ} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) : ContDiff ℝ ∞ (smoothExtension T f hf) := by
  apply contDiff_glue hf
    (SpatialBorelExtension.rightExtension_contDiff (normalTrace T f)
      (normalTrace_contDiff hf) T).contDiffOn
  intro n x
  rw [SpatialBorelExtension.rightExtension_right_jets]
  exact (normalTrace_eq_time_jet hf n x).symm

omit [CompleteSpace V] in
theorem smoothExtension_eqOn_past {T : ℝ} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) : EqOn (smoothExtension T f hf) f (past T) :=
  glue_eqOn_past T f _

omit [CompleteSpace V] in
theorem smoothExtension_zero_from {T : ℝ} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) {t : ℝ} (ht : T + 1 ≤ t) (x : X) :
    smoothExtension T f hf (t, x) = 0 := by
  have hnot : ¬t ≤ T := by linarith
  simp only [smoothExtension, glue, ite_eq_right hnot]
  exact SpatialBorelExtension.rightExtension_zero_from (normalTrace T f)
    (normalTrace_contDiff hf) T ht x

/-- Every full mixed jet on the past, including the boundary, is preserved. -/
theorem smoothExtension_iteratedFDeriv {T : ℝ} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (n : ℕ) {z : (ℝ × X)} (hz : z ∈ past T) :
    iteratedFDeriv ℝ n (smoothExtension T f hf) z = iteratedFDerivWithin ℝ n f (past T) z := by
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv (past_uniqueDiff T)
    ((smoothExtension_contDiff hf).of_le (nat_le_infty n)).contDiffAt hz]
  exact iteratedFDerivWithin_congr (smoothExtension_eqOn_past hf) hz n

omit [CompleteSpace V] in
theorem smoothExtension_add_period {T : ℝ} {f : (ℝ × X) → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (p : X)
    (hperiod : ∀ t ≤ T, ∀ x : X, f (t, x + p) = f (t, x)) (t : ℝ) (x : X) :
    smoothExtension T f hf (t, x + p) = smoothExtension T f hf (t, x) := by
  by_cases ht : t ≤ T
  · simp only [smoothExtension, glue, ite_eq_left ht]
    exact hperiod t ht x
  · simp only [smoothExtension, glue, ite_eq_right ht]
    exact SpatialBorelExtension.rightExtension_add_period (normalTrace T f)
      (normalTrace_contDiff hf) T p (normalTrace_add_period hf p hperiod) t x

end Complete

end NavierStokes.GenericEndpointExtension.Gluing

namespace NavierStokes.GenericEndpointExtension

open Set Filter
open scoped Topology ContDiff

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

section Closure

variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [NormedSpace ℝ Y] [NormedSpace ℝ V] in
/-- Uniform continuity makes the actual values Cauchy at every point of the
closure. Completeness supplies a limit; it is not an input assumption. -/
theorem exists_limit_of_uniformContinuousOn {s : Set Y} {f : Y → V}
    (hf : UniformContinuousOn f s) {x : Y} (hx : x ∈ closure s) :
    ∃ v : V, Tendsto f (𝓝[s] x) (𝓝 v) := by
  have : (𝓝[s] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  apply cauchy_map_iff_exists_tendsto.mp
  apply cauchy_map_iff'.mpr
  apply hf.mono_left
  refine le_inf (cauchy_nhds.mono nhdsWithin_le_nhds).2 ?_
  have hp : 𝓝[s] x ≤ 𝓟 s := inf_le_right
  simpa only [Filter.prod_principal_principal] using Filter.prod_mono hp hp

omit [CompleteSpace V] in
/-- The genuine joint derivatives are differentiable inside the open set. -/
theorem actualJet_hasFDerivAt {s : Set Y} {f : Y → V}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (n : ℕ) {x : Y} (hx : x ∈ s) :
    HasFDerivAt (iteratedFDeriv ℝ n f)
      (iteratedFDeriv ℝ (n + 1) f x).curryLeft x := by
  have horder : (1 : WithTop ℕ∞) + n ≤ ∞ := by
    simpa only [Nat.cast_add, Nat.cast_one] using nat_le_infty (1 + n)
  have hsm : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) x :=
    ((hf x hx).contDiffAt (hs.mem_nhds hx)).iteratedFDeriv_right horder
  exact (hsm.differentiableAt (by norm_num)).hasFDerivAt

omit [CompleteSpace V] in
/-- A bound for derivative `n+1` controls differences of the actual `n`-th
joint derivative on the convex set. -/
theorem actualJet_uniformContinuousOn {s : Set Y} {f : Y → V}
    (hs : IsOpen s) (hc : Convex ℝ s) (hf : ContDiffOn ℝ ∞ f s)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ s, ‖iteratedFDeriv ℝ n f x‖ ≤ C)
    (n : ℕ) : UniformContinuousOn (iteratedFDeriv ℝ n f) s := by
  obtain ⟨C, hC⟩ := hb (n + 1)
  let K : NNReal := ⟨max C 0, le_max_right _ _⟩
  have hLip : LipschitzOnWith K (iteratedFDeriv ℝ n f) s := by
    apply hc.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x hx => (actualJet_hasFDerivAt hs hf n hx).hasFDerivWithinAt)
    intro x hx
    change ‖(iteratedFDeriv ℝ (n + 1) f x).curryLeft‖₊ ≤ K
    apply NNReal.coe_le_coe.mp
    change ‖(iteratedFDeriv ℝ (n + 1) f x).curryLeft‖ ≤ max C 0
    rw [ContinuousMultilinearMap.curryLeft_norm]
    exact (hC x hx).trans (le_max_left _ _)
  exact hLip.uniformContinuousOn

/-- The continuous completion of an actual joint derivative tensor. -/
noncomputable def closureJet (s : Set Y) (f : Y → V) (n : ℕ) :
    Y → (Y[×n]→L[ℝ] V) := extendFrom s (iteratedFDeriv ℝ n f)

theorem closureJet_limit {s : Set Y} {f : Y → V}
    (hs : IsOpen s) (hc : Convex ℝ s) (hf : ContDiffOn ℝ ∞ f s)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ s, ‖iteratedFDeriv ℝ n f x‖ ≤ C)
    (n : ℕ) {x : Y} (hx : x ∈ closure s) :
    Tendsto (iteratedFDeriv ℝ n f) (𝓝[s] x) (𝓝 (closureJet s f n x)) :=
  tendsto_extendFrom (exists_limit_of_uniformContinuousOn
    (actualJet_uniformContinuousOn hs hc hf hb n) hx)

theorem closureJet_continuousOn {s : Set Y} {f : Y → V}
    (hs : IsOpen s) (hc : Convex ℝ s) (hf : ContDiffOn ℝ ∞ f s)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ s, ‖iteratedFDeriv ℝ n f x‖ ≤ C)
    (n : ℕ) : ContinuousOn (closureJet s f n) (closure s) :=
  continuousOn_extendFrom Subset.rfl (fun _ hx => exists_limit_of_uniformContinuousOn
    (actualJet_uniformContinuousOn hs hc hf hb n) hx)

omit [CompleteSpace V] in
theorem closureJet_eq {s : Set Y} {f : Y → V}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    (n : ℕ) {x : Y} (hx : x ∈ s) : closureJet s f n x = iteratedFDeriv ℝ n f x :=
  extendFrom_extends
    (fun _ hy => (actualJet_hasFDerivAt hs hf n hy).continuousAt.continuousWithinAt) x hx

omit [CompleteSpace V] in
theorem closureJet_eventuallyEq {s : Set Y} {f : Y → V}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    (n : ℕ) {x : Y} (hx : x ∈ s) :
    closureJet s f n =ᶠ[𝓝 x] iteratedFDeriv ℝ n f := by
  filter_upwards [hs.mem_nhds hx] with y hy
  exact closureJet_eq hs hf n hy

/-- The mean-value theorem identifies the derivatives of the completed
tensors on the boundary, including all mixed derivative directions. -/
theorem closureJet_hasFDerivWithinAt {s : Set Y} {f : Y → V}
    (hs : IsOpen s) (hc : Convex ℝ s) (hf : ContDiffOn ℝ ∞ f s)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ s, ‖iteratedFDeriv ℝ n f x‖ ≤ C)
    (n : ℕ) {x : Y} (hx : x ∈ closure s) :
    HasFDerivWithinAt (closureJet s f n)
      (closureJet s f (n + 1) x).curryLeft (closure s) x := by
  have hD (y : Y) (hy : y ∈ s) : HasFDerivAt (closureJet s f n)
      (iteratedFDeriv ℝ (n + 1) f y).curryLeft y :=
    (actualJet_hasFDerivAt hs hf n hy).congr_of_eventuallyEq
      (closureJet_eventuallyEq hs hf n hy)
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt) hc hs
    (fun y hy => (closureJet_continuousOn hs hc hf hb n y hy).mono subset_closure)
  let A : (Y[×(n + 1)]→L[ℝ] V) →L[ℝ] (Y →L[ℝ] (Y[×n]→L[ℝ] V)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Y)
        V).toContinuousLinearEquiv.toContinuousLinearMap
  have hlim := A.continuous.continuousAt.tendsto.comp (closureJet_limit hs hc hf hb (n + 1) hx)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hD y hy).fderiv.symm

/-- Complete the values using the zeroth tensor. -/
noncomputable def closedField (s : Set Y) (f : Y → V) (x : Y) : V :=
  (closureJet s f 0 x).curry0

omit [CompleteSpace V] in
theorem closedField_eq {s : Set Y} {f : Y → V}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) {x : Y} (hx : x ∈ s) :
    closedField s f x = f x := by
  rw [closedField, closureJet_eq hs hf 0 hx]
  rfl

/-- Actual uniform joint derivative bounds give joint smoothness on the
closure. In particular no one-sided trace regularity is assumed. -/
theorem closedField_contDiffOn {s : Set Y} {f : Y → V}
    (hs : IsOpen s) (hc : Convex ℝ s) (hf : ContDiffOn ℝ ∞ f s)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ s, ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ContDiffOn ℝ ∞ (closedField s f) (closure s) := by
  have ht : HasFTaylorSeriesUpToOn ∞ (closedField s f)
      (fun x n => closureJet s f n x) (closure s) := by
    constructor
    · intro x hx
      rfl
    · intro n hn x hx
      exact closureJet_hasFDerivWithinAt hs hc hf hb n hx
    · intro n hn
      exact closureJet_continuousOn hs hc hf hb n
  exact ht.contDiffOn

end Closure

section Strip

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Open strip, given by `Ioo (-1 : ℝ) 1 ×ˢ univ`. -/
def openStrip : Set (ℝ × X) := Ioo (-1 : ℝ) 1 ×ˢ univ
/-- Closed strip, given by `Icc (-1 : ℝ) 1 ×ˢ univ`. -/
def closedStrip : Set (ℝ × X) := Icc (-1 : ℝ) 1 ×ˢ univ

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem openStrip_isOpen : IsOpen (openStrip (X := X)) := isOpen_Ioo.prod isOpen_univ

omit [FiniteDimensional ℝ X] in
theorem openStrip_convex : Convex ℝ (openStrip (X := X)) :=
  (convex_Ioo (-1 : ℝ) 1).prod convex_univ

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem closure_openStrip : closure (openStrip (X := X)) = closedStrip := by
  simp only [openStrip, closedStrip, closure_prod_eq,
    closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), closure_univ]

omit [FiniteDimensional ℝ X] in
theorem stripClosedField_contDiffOn {f : ℝ × X → V}
    (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C) :
    ContDiffOn ℝ ∞ (closedField openStrip f) closedStrip := by
  simpa only [closure_openStrip] using
    closedField_contDiffOn openStrip_isOpen openStrip_convex hf hb

private theorem closedInterval_subset_closure_openInterval :
    Icc (-1 : ℝ) 1 ⊆ closure (Ioo (-1 : ℝ) 1) := by
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

omit [FiniteDimensional ℝ X] in
/-- A fiber that vanishes on the open strip also vanishes at its two completed
endpoints. This follows from continuity, not a support enlargement. -/
theorem stripClosedField_zero {f : ℝ × X → V}
    (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    {x : X} (hz : ∀ t ∈ Ioo (-1 : ℝ) 1, f (t, x) = 0)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : closedField openStrip f (t, x) = 0 := by
  have he : ContinuousOn (fun t : ℝ => closedField openStrip f (t, x)) (Icc (-1 : ℝ) 1) :=
    (stripClosedField_contDiffOn hf hb).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ x⟩)
  have hzero : EqOn (fun t : ℝ => closedField openStrip f (t, x))
      (fun _ => 0) (Ioo (-1 : ℝ) 1) := by
    intro s hs
    change closedField openStrip f (s, x) = 0
    rw [closedField_eq openStrip_isOpen hf (x := (s, x)) ⟨hs, mem_univ x⟩]
    exact hz s hs
  exact hzero.of_subset_closure he continuousOn_const Ioo_subset_Icc_self
    closedInterval_subset_closure_openInterval ht

omit [FiniteDimensional ℝ X] in
/-- Every spatial additive period passes to both completed boundary values. -/
theorem stripClosedField_add_period {f : ℝ × X → V}
    (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    (p : X) (hp : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x : X, f (t, x + p) = f (t, x))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (x : X) :
    closedField openStrip f (t, x + p) = closedField openStrip f (t, x) := by
  have he (y : X) : ContinuousOn (fun t : ℝ => closedField openStrip f (t, y))
      (Icc (-1 : ℝ) 1) :=
    (stripClosedField_contDiffOn hf hb).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ y⟩)
  have hperiod : EqOn (fun t : ℝ => closedField openStrip f (t, x + p))
      (fun t : ℝ => closedField openStrip f (t, x)) (Ioo (-1 : ℝ) 1) := by
    intro s hs
    change closedField openStrip f (s, x + p) = closedField openStrip f (s, x)
    rw [closedField_eq openStrip_isOpen hf (x := (s, x + p)) ⟨hs, mem_univ (x + p)⟩,
      closedField_eq openStrip_isOpen hf (x := (s, x)) ⟨hs, mem_univ x⟩]
    exact hp s hs x
  exact hperiod.of_subset_closure (he (x + p)) (he x) Ioo_subset_Icc_self
    closedInterval_subset_closure_openInterval ht

/-- A fixed smooth retraction of the past into the closed strip, equal to
the identity for `t ≥ -1/2`. -/
noncomputable def lowerClamp (t : ℝ) : ℝ := t * Real.smoothTransition (2 * t + 2)

theorem lowerClamp_contDiff : ContDiff ℝ ∞ lowerClamp :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const))

theorem lowerClamp_eq {t : ℝ} (ht : -1 / 2 ≤ t) : lowerClamp t = t := by
  rw [lowerClamp, Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem lowerClamp_mem {t : ℝ} (ht : t ≤ 1) : lowerClamp t ∈ Icc (-1 : ℝ) 1 := by
  by_cases hlow : t ≤ -1
  · rw [lowerClamp, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]
    norm_num
  · have hgt : -1 < t := lt_of_not_ge hlow
    by_cases hneg : t ≤ 0
    · have ha := Real.smoothTransition.nonneg (2 * t + 2)
      have hb := Real.smoothTransition.le_one (2 * t + 2)
      have hupper := mul_nonpos_of_nonpos_of_nonneg hneg ha
      dsimp only [lowerClamp]
      constructor <;> nlinarith
    · rw [lowerClamp_eq (by linarith)]
      exact ⟨hgt.le, ht⟩

/-- Clamped, given by `f (lowerClamp z.1, z.2)`. -/
noncomputable def clamped (f : ℝ × X → V) (z : ℝ × X) : V :=
  f (lowerClamp z.1, z.2)

omit [FiniteDimensional ℝ X] [CompleteSpace V] in
theorem clamped_contDiffOn {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip) :
    ContDiffOn ℝ ∞ (clamped f) (Gluing.past 1) :=
  hf.comp ((lowerClamp_contDiff.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun z hz => ⟨lowerClamp_mem hz.1, mem_univ z.2⟩)

omit [CompleteSpace V] in
/-- Zero normal coefficients stay zero in the actual Borel series. -/
theorem Gluing.smoothExtension_zero_fiber {T : ℝ} {f : ℝ × X → V}
    (hf : ContDiffOn ℝ ∞ f (Gluing.past T)) {x : X}
    (hz : ∀ t ≤ T, f (t, x) = 0) (t : ℝ) :
    Gluing.smoothExtension T f hf (t, x) = 0 := by
  by_cases ht : t ≤ T
  · rw [Gluing.smoothExtension_eqOn_past hf
      (show (t, x) ∈ Gluing.past T from ⟨ht, mem_univ x⟩)]
    exact hz t ht
  · unfold Gluing.smoothExtension Gluing.glue
    simp only [ite_eq_right ht, SpatialBorelExtension.rightExtension]
    apply SpatialBorelExtension.extension_zero_of_coefficients_zero
    intro n
    rw [Gluing.normalTrace_eq_time_jet hf,
      iteratedDerivWithin_congr (show EqOn (fun s : ℝ => f (s, x)) (fun _ => 0) (Iic T)
        from hz) (mem_Iic.mpr le_rfl)]
    simp only [iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_fun_zero, Pi.zero_apply, _root_.zero_apply]

/-- Upper closed, given by `Gluing.smoothExtension 1 (clamped f) (clamped_contDiffOn hf)`. -/
noncomputable def upperClosed (f : ℝ × X → V) (hf : ContDiffOn ℝ ∞ f closedStrip) :
    ℝ × X → V := Gluing.smoothExtension 1 (clamped f) (clamped_contDiffOn hf)

theorem upperClosed_contDiff {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip) :
    ContDiff ℝ ∞ (upperClosed f hf) := Gluing.smoothExtension_contDiff (clamped_contDiffOn hf)

omit [CompleteSpace V] in
theorem upperClosed_eq {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip)
    {t : ℝ} (hlo : -1 / 2 ≤ t) (hhi : t ≤ 1) (x : X) : upperClosed f hf (t, x) = f (t, x) := by
  rw [upperClosed, Gluing.smoothExtension_eqOn_past (clamped_contDiffOn hf)
    (show (t, x) ∈ Gluing.past 1 from ⟨hhi, mem_univ x⟩)]
  simp only [clamped, lowerClamp_eq hlo]

omit [CompleteSpace V] in
theorem upperClosed_zero {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip)
    {x : X} (hz : ∀ t ∈ Icc (-1 : ℝ) 1, f (t, x) = 0) (t : ℝ) :
    upperClosed f hf (t, x) = 0 :=
  Gluing.smoothExtension_zero_fiber (clamped_contDiffOn hf)
    (fun _ hs => hz _ (lowerClamp_mem hs)) t

omit [CompleteSpace V] in
theorem upperClosed_add_period {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip)
    (p : X) (hp : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x : X, f (t, x + p) = f (t, x))
    (t : ℝ) (x : X) : upperClosed f hf (t, x + p) = upperClosed f hf (t, x) :=
  Gluing.smoothExtension_add_period (clamped_contDiffOn hf) p
    (fun _ hs y => hp _ (lowerClamp_mem hs) y) t x

/-- Reflect, given by `f (-z.1, z.2)`. -/
noncomputable def reflect (f : ℝ × X → V) (z : ℝ × X) : V := f (-z.1, z.2)

omit [FiniteDimensional ℝ X] [CompleteSpace V] in
theorem reflect_contDiff {f : ℝ × X → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (reflect f) := hf.comp (contDiff_fst.neg.prodMk contDiff_snd)

omit [FiniteDimensional ℝ X] [CompleteSpace V] in
theorem reflect_contDiffOn {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip) :
    ContDiffOn ℝ ∞ (reflect f) closedStrip := by
  apply hf.comp (contDiff_fst.neg.prodMk contDiff_snd).contDiffOn
  intro z hz
  refine ⟨?_, mem_univ z.2⟩
  change -1 ≤ -z.1 ∧ -z.1 ≤ 1
  constructor <;> linarith [hz.1.1, hz.1.2]

/-- Lower closed, given by `reflect (upperClosed (reflect f) (reflect_contDiffOn hf))`. -/
noncomputable def lowerClosed (f : ℝ × X → V) (hf : ContDiffOn ℝ ∞ f closedStrip) :
    ℝ × X → V := reflect (upperClosed (reflect f) (reflect_contDiffOn hf))

theorem lowerClosed_contDiff {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip) :
    ContDiff ℝ ∞ (lowerClosed f hf) :=
  reflect_contDiff (upperClosed_contDiff (reflect_contDiffOn hf))

omit [CompleteSpace V] in
theorem lowerClosed_eq {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip)
    {t : ℝ} (hlo : -1 ≤ t) (hhi : t ≤ 1 / 2) (x : X) : lowerClosed f hf (t, x) = f (t, x) := by
  change upperClosed (reflect f) (reflect_contDiffOn hf) (-t, x) = f (t, x)
  rw [upperClosed_eq (reflect_contDiffOn hf) (by linarith) (by linarith)]
  simp only [reflect, neg_neg]

omit [CompleteSpace V] in
theorem lowerClosed_zero {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip)
    {x : X} (hz : ∀ t ∈ Icc (-1 : ℝ) 1, f (t, x) = 0) (t : ℝ) :
    lowerClosed f hf (t, x) = 0 := by
  apply upperClosed_zero (reflect_contDiffOn hf)
  intro s hs
  exact hz (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩

omit [CompleteSpace V] in
theorem lowerClosed_add_period {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip)
    (p : X) (hp : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x : X, f (t, x + p) = f (t, x))
    (t : ℝ) (x : X) : lowerClosed f hf (t, x + p) = lowerClosed f hf (t, x) :=
  upperClosed_add_period (reflect_contDiffOn hf) p
    (fun s hs y => hp (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ y) (-t) x

/-- Use the lower continuation for negative parameters and the upper
continuation for positive ones. They agree on a whole central strip. -/
noncomputable def closedStripExtension (f : ℝ × X → V)
    (hf : ContDiffOn ℝ ∞ f closedStrip) (z : ℝ × X) : V :=
  if z.1 ≤ 0 then lowerClosed f hf z else upperClosed f hf z

omit [CompleteSpace V] in
theorem closedStripExtension_eq {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f closedStrip)
    {z : ℝ × X} (hz : z ∈ closedStrip) : closedStripExtension f hf z = f z := by
  rcases z with ⟨t, x⟩
  by_cases ht : t ≤ 0
  · rw [closedStripExtension, ite_eq_left ht]
    exact lowerClosed_eq hf hz.1.1 (by linarith) x
  · rw [closedStripExtension, ite_eq_right ht]
    exact upperClosed_eq hf (by linarith) hz.1.2 x

theorem closedStripExtension_contDiff {f : ℝ × X → V}
    (hf : ContDiffOn ℝ ∞ f closedStrip) : ContDiff ℝ ∞ (closedStripExtension f hf) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases lt_trichotomy z.1 0 with hneg | hzero | hpos
  · apply (lowerClosed_contDiff hf).contDiffAt.congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto z).eventually (Iio_mem_nhds hneg)] with y hy
    exact ite_eq_left hy.le
  · apply (upperClosed_contDiff hf).contDiffAt.congr_of_eventuallyEq
    have hband : z.1 ∈ Ioo (-1 / 2 : ℝ) (1 / 2) := by rw [hzero]; norm_num
    filter_upwards [(continuous_fst.tendsto z).eventually (isOpen_Ioo.mem_nhds hband)] with y hy
    rw [closedStripExtension_eq hf ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, mem_univ y.2⟩,
      upperClosed_eq hf hy.1.le (by linarith [hy.2]) y.2]
  · apply (upperClosed_contDiff hf).contDiffAt.congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto z).eventually (Ioi_mem_nhds hpos)] with y hy
    exact ite_eq_right (not_le_of_gt hy)

omit [CompleteSpace V] in
theorem closedStripExtension_zero {f : ℝ × X → V}
    (hf : ContDiffOn ℝ ∞ f closedStrip) {x : X}
    (hz : ∀ t ∈ Icc (-1 : ℝ) 1, f (t, x) = 0) (t : ℝ) :
    closedStripExtension f hf (t, x) = 0 := by
  by_cases ht : t ≤ 0
  · rw [closedStripExtension, ite_eq_left ht, lowerClosed_zero hf hz]
  · rw [closedStripExtension, ite_eq_right ht, upperClosed_zero hf hz]

omit [CompleteSpace V] in
theorem closedStripExtension_add_period {f : ℝ × X → V}
    (hf : ContDiffOn ℝ ∞ f closedStrip) (p : X)
    (hp : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x : X, f (t, x + p) = f (t, x))
    (t : ℝ) (x : X) :
    closedStripExtension f hf (t, x + p) = closedStripExtension f hf (t, x) := by
  by_cases ht : t ≤ 0
  · simp only [closedStripExtension, ite_eq_left ht]
    exact lowerClosed_add_period hf p hp t x
  · simp only [closedStripExtension, ite_eq_right ht]
    exact upperClosed_add_period hf p hp t x

omit [CompleteSpace V] in
theorem closedStripExtension_zero_parameter {f : ℝ × X → V}
    (hf : ContDiffOn ℝ ∞ f closedStrip) {t : ℝ} (ht : 2 ≤ |t|) (x : X) :
    closedStripExtension f hf (t, x) = 0 := by
  rcases le_abs.mp ht with hpos | hneg
  · rw [closedStripExtension, ite_eq_right (by linarith : ¬t ≤ 0)]
    exact Gluing.smoothExtension_zero_from (clamped_contDiffOn hf) (by linarith) x
  · rw [closedStripExtension, ite_eq_left (by linarith : t ≤ 0)]
    exact Gluing.smoothExtension_zero_from
      (clamped_contDiffOn (reflect_contDiffOn hf)) (by linarith) x

/-- The constructed extension takes only interior smoothness and bounds on
the actual joint derivatives as inputs. -/
noncomputable def extension (f : ℝ × X → V) (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C) :
    ℝ × X → V := closedStripExtension (closedField openStrip f) (stripClosedField_contDiffOn hf hb)

theorem extension_contDiff {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C) :
    ContDiff ℝ ∞ (extension f hf hb) :=
  closedStripExtension_contDiff (stripClosedField_contDiffOn hf hb)

theorem extension_eq {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    {z : ℝ × X} (hz : z ∈ openStrip) : extension f hf hb z = f z := by
  rw [extension, closedStripExtension_eq (stripClosedField_contDiffOn hf hb)
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩]
  exact closedField_eq openStrip_isOpen hf hz

theorem extension_zero_of_fiber {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    {x : X} (hz : ∀ t ∈ Ioo (-1 : ℝ) 1, f (t, x) = 0) (t : ℝ) :
    extension f hf hb (t, x) = 0 :=
  closedStripExtension_zero (stripClosedField_contDiffOn hf hb)
    (fun _ hs => stripClosedField_zero hf hb hz hs) t

theorem extension_add_period {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    (p : X) (hp : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x : X, f (t, x + p) = f (t, x))
    (t : ℝ) (x : X) : extension f hf hb (t, x + p) = extension f hf hb (t, x) :=
  closedStripExtension_add_period (stripClosedField_contDiffOn hf hb) p
    (fun _ hs y => stripClosedField_add_period hf hb p hp hs y) t x

theorem extension_zero_parameter {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    {t : ℝ} (ht : 2 ≤ |t|) (x : X) : extension f hf hb (t, x) = 0 :=
  closedStripExtension_zero_parameter (stripClosedField_contDiffOn hf hb) ht x

theorem extension_iteratedFDeriv {f : ℝ × X → V} (hf : ContDiffOn ℝ ∞ f openStrip)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ openStrip, ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    (n : ℕ) {z : ℝ × X} (hz : z ∈ openStrip) :
    iteratedFDeriv ℝ n (extension f hf hb) z = iteratedFDeriv ℝ n f z := by
  have heq : extension f hf hb =ᶠ[𝓝 z] f := by
    filter_upwards [openStrip_isOpen.mem_nhds hz] with y hy
    exact extension_eq hf hb hy
  have heq' : extension f hf hb =ᶠ[𝓝[univ] z] f := by simpa using heq
  simpa only [iteratedFDerivWithin_univ] using
    heq'.iteratedFDerivWithin_eq heq.self_of_nhds n

end Strip

end NavierStokes.GenericEndpointExtension

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.OffplaneJetExtensions

open Set Function Filter Metric ProblemStatement
open scoped Topology ContDiff BigOperators

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

/-- Past ball, given by `Metric.ball (1, x) r ∩ SpacetimeEndpoint.openPast 1`. -/
noncomputable def pastBall (x : Space) (r : ℝ) : Set SpaceTime :=
  Metric.ball (1, x) r ∩ SpacetimeEndpoint.openPast 1

theorem pastBall_open (x : Space) (r : ℝ) : IsOpen (pastBall x r) :=
  isOpen_ball.inter (SpacetimeEndpoint.openPast_isOpen 1)

/-- Local bump, bundling `rIn`, `rOut`, `rIn_pos`, `rIn_lt_rOut`. -/
noncomputable def localBump (x : Space) {r : ℝ} (hr : 0 < r) : ContDiffBump ((1 : ℝ), x) where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem localBump_support (x : Space) {r : ℝ} (hr : 0 < r) :
    tsupport (localBump x hr) ⊆ Metric.ball ((1 : ℝ), x) r := by
  rw [(localBump x hr).tsupport_eq]
  exact Metric.closedBall_subset_ball (by change r / 2 < r; linarith)

theorem localBump_jet_bounded (x : Space) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SpaceTime, ‖iteratedFDeriv ℝ m (localBump x hr) w‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((localBump x hr).hasCompactSupport.iteratedFDeriv (𝕜 := ℝ)
      m).exists_bound_of_continuous
    ((localBump x hr).contDiff.continuous_iteratedFDeriv (nat_le_infty m))
  exact ⟨max C 0, le_max_right _ _, fun w => (hC w).trans (le_max_left _ _)⟩

section LocalExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Localized, given by `localBump x hr w • f w`. -/
noncomputable def localized (f : SpaceTime → V) (x : Space) {r : ℝ} (hr : 0 < r)
    (w : SpaceTime) : V := localBump x hr w • f w

theorem localized_zero_germ (f : SpaceTime → V) (x : Space) {r : ℝ} (hr : 0 < r)
    {w : SpaceTime} (hw : w ∉ tsupport (localBump x hr)) :
    localized f x hr =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with z hz
  simp only [localized, hz, Pi.zero_apply, zero_smul]

theorem localized_smooth {f : SpaceTime → V} {x : Space} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (pastBall x r)) :
    ContDiffOn ℝ ∞ (localized f x hr) GenericEndpointExtension.openStrip := by
  intro w hw
  by_cases hs : w ∈ tsupport (localBump x hr)
  · have hlocal : w ∈ pastBall x r :=
      ⟨localBump_support x hr hs, hw.1.2, mem_univ _⟩
    exact (((localBump x hr).contDiff.contDiffAt).smul
      (hf.contDiffAt ((pastBall_open x r).mem_nhds hlocal))).contDiffWithinAt
  · exact ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : SpaceTime => (0 : V))
      w).congr_of_eventuallyEq
      (localized_zero_germ f x hr hs)).contDiffWithinAt

theorem localized_jets_bounded {f : SpaceTime → V} {x : Space} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (pastBall x r))
    (hb : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ pastBall x r, ‖iteratedFDeriv ℝ m f w‖ ≤ C) :
    ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ GenericEndpointExtension.openStrip,
      ‖iteratedFDeriv ℝ m (localized f x hr) w‖ ≤ C := by
  choose A hA using hb
  choose C hC hCb using localBump_jet_bounded x hr
  intro m
  let K : ℝ := ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * C i * max (A (m - i)) 0
  have hK : 0 ≤ K := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (le_max_right _ _)
  refine ⟨K, fun w hw => ?_⟩
  by_cases hs : w ∈ tsupport (localBump x hr)
  · have hlocal : w ∈ pastBall x r :=
      ⟨localBump_support x hr hs, hw.1.2, mem_univ _⟩
    have hprod := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ)
      (localBump x hr).contDiff.contDiffOn hf (pastBall_open x r).uniqueDiffOn
      hlocal (nat_le_infty m)
    simp only [iteratedFDerivWithin_of_isOpen _ (pastBall_open x r) hlocal] at hprod
    apply hprod.trans
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hCb i w) (Nat.cast_nonneg _))
      ((hA (m - i) w hlocal).trans (le_max_left _ _))
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC i))
  · have hz : iteratedFDeriv ℝ m (localized f x hr) w = 0 := by
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
        (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (localized_zero_germ f x hr hs)
            m).self_of_nhds
    rw [hz, norm_zero]
    exact hK

variable [CompleteSpace V]

/-- A local bound for every actual joint derivative supplies an actual
smooth extension. Endpoint derivative limits are constructed by the
generic extension theorem; they are not additional inputs. -/
theorem extension_of_local_jets {f : SpaceTime → V} {x : Space} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (pastBall x r))
    (hb : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ pastBall x r, ‖iteratedFDeriv ℝ m f w‖ ≤ C) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  let g := localized f x hr
  have hg : ContDiffOn ℝ ∞ g GenericEndpointExtension.openStrip := localized_smooth hr hf
  have hgb : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ GenericEndpointExtension.openStrip,
      ‖iteratedFDeriv ℝ m g w‖ ≤ C := localized_jets_bounded hr hf hb
  refine ⟨{
    value := GenericEndpointExtension.extension g hg hgb
    domain := Metric.ball ((1 : ℝ), x) (r / 4) ∩ {w : SpaceTime | -1 < w.1}
    isOpen := isOpen_ball.inter (isOpen_lt continuous_const continuous_fst)
    mem := ⟨Metric.mem_ball_self (by positivity), by norm_num⟩
    smooth := (GenericEndpointExtension.extension_contDiff hg hgb).contDiffOn
    agrees := ?_ }⟩
  intro w hw
  have hstrip : w ∈ GenericEndpointExtension.openStrip :=
    ⟨⟨hw.1.2, hw.2.1⟩, mem_univ _⟩
  rw [GenericEndpointExtension.extension_eq hg hgb hstrip]
  have hc : localBump x hr w = 1 :=
    (localBump x hr).one_of_mem_closedBall (Metric.mem_closedBall.mpr hw.1.1.le)
  simp only [g, localized, hc, one_smul]

end LocalExtension

section PhysicalScale

/-- One neighborhood controls the physical scale for all derivative
orders. Only the actual past coordinate is used in the conclusion. -/
theorem exists_scale_neighborhood {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : Space} (hx : x 2 ≠ 0)
    (hq : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ pastBall x r,
      w ∈ CutStageEstimates.physicalSublevel h qbig ∧
      EndpointCoordinates.endpointRoot (2 * h) (x 2) / 2 < PhysicalWaveSum.physicalQ h w ∧
      |w.1| ≤ 1 := by
  have hp := EndpointCoordinates.endpointRoot_pos (2 * h) hx
  have hlim := MixedDiagonalExtensions.physicalQ_tendsto_endpoint hh hh1 hx
  have he : ∀ᶠ w in 𝓝[SpacetimeEndpoint.openPast 1] (1, x),
      PhysicalWaveSum.physicalQ h w ∈
        Ioo (EndpointCoordinates.endpointRoot (2 * h) (x 2) / 2) qbig :=
    hlim.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, hq⟩)
  obtain ⟨U, hU, hxU, hsub⟩ := mem_nhdsWithin.mp he
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  refine ⟨min r 1, lt_min hr zero_lt_one, ?_⟩
  intro w hw
  have hwU : w ∈ U := hball (ball_subset_ball (min_le_left _ _) hw.1)
  have hscale := hsub ⟨hwU, hw.2⟩
  have hfst : dist w.1 (1 : ℝ) ≤ dist w ((1 : ℝ), x) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hdist : dist w.1 (1 : ℝ) < 1 :=
    hfst.trans_lt (hw.1.trans_le (min_le_right _ _))
  have htime : 0 < w.1 := by
    rw [Real.dist_eq] at hdist
    have hs := (abs_lt.mp hdist).1
    linarith
  exact ⟨⟨hw.2.1, hscale.2⟩, hscale.1,
    by rw [abs_of_pos htime]; exact hw.2.1.le⟩

/-- Arbitrary real powers and logarithmic losses are uniformly bounded
when the scale lies in a fixed compact subinterval of `(0,∞)`. -/
theorem powerLog_bounded {a : ℝ} (ha : 0 < a) (C p e : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ Icc a 1,
      C * (1 + |Real.log q|) ^ p * q ^ e ≤ K := by
  have hne : ∀ q ∈ Icc a (1 : ℝ), q ≠ 0 := fun q hq => (ha.trans_le hq.1).ne'
  have hl : ContinuousOn (fun q : ℝ => 1 + |Real.log q|) (Icc a 1) :=
    continuousOn_const.add ((continuousOn_id.log hne).abs)
  have hlne : ∀ q ∈ Icc a (1 : ℝ), (1 + |Real.log q|) ≠ 0 := by
    intro q _
    positivity
  have hc : ContinuousOn (fun q : ℝ => C * (1 + |Real.log q|) ^ p * q ^ e) (Icc a 1) :=
    (continuousOn_const.mul (hl.rpow_const (fun q hq => Or.inl (hlne q hq)))).mul
      (continuousOn_id.rpow_const (fun q hq => Or.inl (hne q hq)))
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max K 0, le_max_right _ _, fun q hq => ?_⟩
  have hk : |C * (1 + |Real.log q|) ^ p * q ^ e| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK q hq
  exact (le_abs_self _).trans (hk.trans (le_max_left _ _))

end PhysicalScale

section PhysicalExtensions

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A single-field endpoint theorem, including the bounded finite pieces
at stage zero. It assumes only their actual interior jet estimates. -/
theorem extension_of_powerLog_jets {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : qbig ≤ 1) {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ m : ℕ, ∃ C p e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      |w.1| ≤ 1 → PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤
        C * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p *
          PhysicalWaveSum.physicalQ h w ^ e)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  obtain ⟨r, hr, hscale⟩ := exists_scale_neighborhood hh hh1 hx hqx
  apply extension_of_local_jets hr (hf.mono (fun w hw => (hscale w hw).1))
  intro m
  obtain ⟨C, p, e, hm⟩ := hb m
  obtain ⟨K, _, hK⟩ := powerLog_bounded (half_pos (EndpointCoordinates.endpointRoot_pos (2 * h)
      hx)) C p e
  refine ⟨K, fun w hw => ?_⟩
  have hs := hscale w hw
  have hq1 : PhysicalWaveSum.physicalQ h w ≤ 1 := hs.1.2.le.trans hqbig
  exact (hm w hs.1 hs.2.2 hq1).trans (hK _ ⟨hs.2.1.le, hq1⟩)

theorem extension_of_power_jets {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : qbig ≤ 1) {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ m : ℕ, ∃ C e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ e)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  apply extension_of_powerLog_jets hh hh1 hqbig hf _ hx hqx
  intro m
  obtain ⟨C, e, hm⟩ := hb m
  refine ⟨C, 0, e, fun w hw _ hq1 => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hm w hw hq1

/-- Positive raw stages extend directly from `RawStageBounds`. The stage
index hypothesis is retained exactly: no stage-zero estimate is inferred. -/
theorem rawStage_extension {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : qbig ≤ 1) {F : ℕ → SpaceTime → V} {g L : ℕ → ℝ} {C p : ℕ → ℕ → ℝ}
    (hb : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) F g L C p
      (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig))
    {j : ℕ} (hj : 1 ≤ j)
    (hf : ContDiffOn ℝ ∞ (F j) (CutStageEstimates.physicalSublevel h qbig))
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (F j) x) := by
  apply extension_of_powerLog_jets hh hh1 hqbig hf _ hx hqx
  intro m
  exact ⟨C j m, p j m, g j - L m, fun w hw _ hq1 => hb j hj m w ⟨hw.1, hw⟩ hq1⟩

theorem rawStages_extensions {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : qbig ≤ 1) {F : ℕ → SpaceTime → V} {g L : ℕ → ℝ} {C p : ℕ → ℕ → ℝ}
    (hb : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) F g L C p
      (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig))
    (hf : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (F j) (CutStageEstimates.physicalSublevel h qbig))
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    ∀ j, 1 ≤ j → Nonempty (JointResidualLimits.OneSidedExtension (F j) x) :=
  fun j hj => rawStage_extension hh hh1 hqbig hb hj (hf j hj) hx hqx

end PhysicalExtensions

section Assembly

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Combine, for example, the existing base-gauge extension with the
separately derived extension of the finite initial correction. -/
noncomputable def addExtension {f g : SpaceTime → V} {x : Space}
    (ef : JointResidualLimits.OneSidedExtension f x)
    (eg : JointResidualLimits.OneSidedExtension g x) :
    JointResidualLimits.OneSidedExtension (fun w => f w + g w) x where
  value w := ef.value w + eg.value w
  domain := ef.domain ∩ eg.domain
  isOpen := ef.isOpen.inter eg.isOpen
  mem := ⟨ef.mem, eg.mem⟩
  smooth := (ef.smooth.mono inter_subset_left).add (eg.smooth.mono inter_subset_right)
  agrees := fun w hw => by
    change ef.value w + eg.value w = f w + g w
    rw [ef.agrees ⟨hw.1.1, hw.2⟩, eg.agrees ⟨hw.1.2, hw.2⟩]

theorem extension_add {f g : SpaceTime → V} {x : Space}
    (hf : Nonempty (JointResidualLimits.OneSidedExtension f x))
    (hg : Nonempty (JointResidualLimits.OneSidedExtension g x)) :
    Nonempty (JointResidualLimits.OneSidedExtension (fun w => f w + g w) x) :=
  hf.elim fun ef => hg.elim fun eg => ⟨addExtension ef eg⟩

/-- The constructed stage need only agree with the bounded model on its
actual validity region. The positive scale margin supplies the required
past neighborhood automatically. -/
theorem extension_of_eqOn_sublevel {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f g : SpaceTime → V} (he : EqOn f g (CutStageEstimates.physicalSublevel h qbig))
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig)
    (eg : Nonempty (JointResidualLimits.OneSidedExtension g x)) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  obtain ⟨eg⟩ := eg
  apply MixedDiagonalExtensions.extension_of_eventuallyEq _ eg
  filter_upwards [self_mem_nhdsWithin,
    (MixedDiagonalExtensions.physicalQ_tendsto_endpoint hh hh1 hx).eventually (gt_mem_nhds hqx)]
        with w hw hq
  exact he ⟨hw.1, hq⟩

end Assembly

section FiniteInitialPieces

open ActualPhysicalStageBounds

theorem mean_field_extension {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    (hq : qbig ≤ ChartScales.Q M.firstBand) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension M.family.field x) := by
  apply extension_of_power_jets hh hh1 hqbig (M.field_smooth hh hh1 hq) _ hx hqx
  intro m
  obtain ⟨C, _, hb⟩ := M.field_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, hb⟩

theorem mean_angular_extension {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    (hq : qbig ≤ ChartScales.Q M.firstBand) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension M.family.angularField x) := by
  apply extension_of_power_jets hh hh1 hqbig (M.angular_smooth hh hh1 hq) _ hx hqx
  intro m
  obtain ⟨C, _, hb⟩ := M.angular_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, hb⟩

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

/-- The finite initialized potential correction has its own derived
estimate. This theorem does not apply the positive-stage bound to index zero. -/
theorem initialIncrement_extension {h qbig : ℝ}
    (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialIncrement W MT MR) x) := by
  apply extension_of_power_jets hh hh1 hqbig (initialIncrement_smooth W MT MR hh hh1 hqT hqR) _ hx
      hqx
  intro m
  obtain ⟨C, _, hb⟩ := initialIncrement_bound W MT MR hh hh1 hqT hqR m
  exact ⟨C, -InitializedPhysicalBackground.seedPotentialLoss h W.alpha W.shift (min MT.alpha
      MR.alpha) m, hb⟩

theorem initialPressureIncrement_extension {h qbig : ℝ}
    (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    (hq : qbig ≤ ChartScales.Q M.firstBand) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialPressureIncrement W M) x) := by
  apply extension_of_power_jets hh hh1 hqbig (initialPressureIncrement_smooth W M hh hh1 hq) _ hx
      hqx
  intro m
  obtain ⟨C, _, hb⟩ := initialPressureIncrement_bound W M hh hh1 hq m
  exact ⟨C, -initialPressureLoss h W.alpha W.shift M.alpha m, hb⟩

end FiniteInitialPieces

end NavierStokes.OffplaneJetExtensions
