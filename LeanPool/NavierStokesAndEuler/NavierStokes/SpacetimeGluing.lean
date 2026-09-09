/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpacetimeEndpoint
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialBorelExtension

@[expose] public section

/-!
# Joint smooth gluing from matching normal time jets

Normal derivatives below are actual directional derivatives of joint fields.
The final interface uses the actual one-sided `iteratedDerivWithin` of time
slices. Equality of full mixed derivative tensors is not an input assumption.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.SpacetimeGluing

abbrev Space := ProblemStatement.Space
abbrev SpaceTime := ProblemStatement.SpaceTime

noncomputable def timeVector : SpaceTime := (1, 0)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def directional (s : Set SpaceTime) (f : SpaceTime → V) (v : SpaceTime)
    (z : SpaceTime) : V := fderivWithin ℝ f s z v

noncomputable def normalIter (s : Set SpaceTime) (f : SpaceTime → V) : ℕ → SpaceTime → V
  | 0 => f
  | n + 1 => directional s (normalIter s f n) timeVector

theorem directional_contDiffOn {s : Set SpaceTime} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (v : SpaceTime) :
    ContDiffOn ℝ ∞ (directional s f v) s :=
  (hf.fderivWithin hs infty_add_one_le).clm_apply contDiffOn_const

theorem normalIter_contDiffOn {s : Set SpaceTime} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (n : ℕ) :
    ContDiffOn ℝ ∞ (normalIter s f n) s := by
  induction n with
  | zero => exact hf
  | succ n ih => exact directional_contDiffOn ih hs timeVector

/-- Schwarz's theorem commutes two fixed directional derivatives on a
regular closed domain; no symmetry of full higher tensors is assumed. -/
theorem directional_commute {s : Set SpaceTime} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s)
    (hregular : s ⊆ closure (interior s)) {z : SpaceTime} (hz : z ∈ s)
    (v w : SpaceTime) :
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
    (by simp [minSmoothness_of_isRCLikeNormedField, le_rfl])
    hs (hregular hz) hz).eq w v

/-- Any fixed directional derivative commutes with every normal iterate. -/
theorem normalIter_directional {s : Set SpaceTime} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s)
    (hregular : s ⊆ closure (interior s)) (v : SpaceTime) (n : ℕ) :
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

/-- The joint normal iterates equal the genuine one-dimensional derivatives
of the time slice, including at a one-sided boundary. -/
theorem time_slice_iteratedDerivWithin {I : Set ℝ} {f : SpaceTime → V}
    (hI : UniqueDiffOn ℝ I) (hf : ContDiffOn ℝ ∞ f (I ×ˢ univ))
    (x : Space) (n : ℕ) :
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

/-- Matching boundary values gives matching tangential derivatives; together
with the first normal derivative this determines the full Frechet derivative. -/
theorem boundary_fderiv_eq {s t : Set SpaceTime} {f g : SpaceTime → V} {T : ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g t)
    (hBs : ∀ x : Space, (T, x) ∈ s) (hBt : ∀ x : Space, (T, x) ∈ t)
    (hvalue : ∀ x : Space, f (T, x) = g (T, x))
    (hnormal : ∀ x : Space, directional s f timeVector (T, x) =
      directional t g timeVector (T, x)) (x : Space) :
    fderivWithin ℝ f s (T, x) = fderivWithin ℝ g t (T, x) := by
  have hfD := (hf.differentiableOn (by simp) (T, x) (hBs x)).hasFDerivWithinAt
  have hgD := (hg.differentiableOn (by simp) (T, x) (hBt x)).hasFDerivWithinAt
  have hftrace : HasFDerivAt (fun y : Space => f (T, y))
      ((fderivWithin ℝ f s (T, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
    have h := hfD.comp x (s := univ) (hasFDerivAt_prodMk_right T x).hasFDerivWithinAt
      (fun y _ => hBs y)
    simpa only [Function.comp_def, hasFDerivWithinAt_univ] using h
  have hgtrace : HasFDerivAt (fun y : Space => g (T, y))
      ((fderivWithin ℝ g t (T, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
    have h := hgD.comp x (s := univ) (hasFDerivAt_prodMk_right T x).hasFDerivWithinAt
      (fun y _ => hBt y)
    simpa only [Function.comp_def, hasFDerivWithinAt_univ] using h
  have htan := hftrace.unique (hgtrace.congr_of_eventuallyEq (Eventually.of_forall hvalue))
  apply ContinuousLinearMap.ext
  intro v
  have hspatial := congrArg (fun A : Space →L[ℝ] V => A v.2) htan
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hspatial
  have htime : fderivWithin ℝ f s (T, x) timeVector =
      fderivWithin ℝ g t (T, x) timeVector := hnormal x
  have hv : v = v.1 • timeVector + (0, v.2) := by
    ext <;> simp [timeVector]
  rw [hv, map_add, map_add, map_smul, map_smul, htime, hspatial]

/-- Matching normal trace functions implies matching normal traces after
any directional derivative. The proof derives, rather than assumes, the
necessary tangential and mixed derivative equalities. -/
theorem normal_match_directional {s t : Set SpaceTime} {f g : SpaceTime → V} {T : ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g t)
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hregularS : s ⊆ closure (interior s)) (hregularT : t ⊆ closure (interior t))
    (hBs : ∀ x : Space, (T, x) ∈ s) (hBt : ∀ x : Space, (T, x) ∈ t)
    (hmatch : ∀ n : ℕ, ∀ x : Space, normalIter s f n (T, x) = normalIter t g n (T, x))
    (v : SpaceTime) (n : ℕ) (x : Space) :
    normalIter s (directional s f v) n (T, x) =
      normalIter t (directional t g v) n (T, x) := by
  rw [normalIter_directional hf hs hregularS v n (hBs x),
    normalIter_directional hg ht hregularT v n (hBt x)]
  have hD := boundary_fderiv_eq (normalIter_contDiffOn hf hs n)
    (normalIter_contDiffOn hg ht n) hBs hBt (hmatch n) (hmatch (n + 1)) x
  exact congrArg (fun A : SpaceTime →L[ℝ] V => A v) hD

abbrev past (T : ℝ) : Set SpaceTime := SpacetimeEndpoint.closedPast T
def future (T : ℝ) : Set SpaceTime := Ici T ×ˢ univ

theorem past_uniqueDiff (T : ℝ) : UniqueDiffOn ℝ (past T) :=
  SpacetimeEndpoint.closedPast_uniqueDiff T

theorem future_uniqueDiff (T : ℝ) : UniqueDiffOn ℝ (future T) :=
  (uniqueDiffOn_Ici T).prod uniqueDiffOn_univ

theorem past_regular (T : ℝ) : past T ⊆ closure (interior (past T)) := by
  simp only [past, SpacetimeEndpoint.closedPast, interior_prod_eq, interior_Iic,
    interior_univ, closure_prod_eq, closure_Iio, closure_univ]
  exact Subset.rfl

theorem future_regular (T : ℝ) : future T ⊆ closure (interior (future T)) := by
  simp only [future, interior_prod_eq, interior_Ici, interior_univ, closure_prod_eq,
    closure_Ioi, closure_univ]
  exact Subset.rfl

theorem past_union_future (T : ℝ) : past T ∪ future T = univ := by
  ext z
  simp only [past, SpacetimeEndpoint.closedPast, future, mem_union, mem_prod,
    mem_Iic, mem_Ici, mem_univ, and_true, iff_true]
  exact le_total z.1 T

/-- Glue along the time hyperplane, using the past branch at the join. -/
def glue {W : Type*} (T : ℝ) (f g : SpaceTime → W) (z : SpaceTime) : W :=
  if z.1 ≤ T then f z else g z

theorem glue_eqOn_past {W : Type*} (T : ℝ) (f g : SpaceTime → W) :
    EqOn (glue T f g) f (past T) := by
  intro z hz
  exact ite_eq_left hz.1

theorem glue_eqOn_future {W : Type*} {T : ℝ} {f g : SpaceTime → W}
    (hvalue : ∀ x : Space, f (T, x) = g (T, x)) :
    EqOn (glue T f g) g (future T) := by
  rintro ⟨t, x⟩ ht
  by_cases h : t ≤ T
  · have heq : t = T := le_antisymm h ht.1
    subst t
    exact (ite_eq_left le_rfl).trans (hvalue x)
  · exact ite_eq_right h

/-- Actual full Frechet derivatives glue when their boundary values match. -/
theorem hasFDerivAt_glue {T : ℝ} {f g : SpaceTime → V}
    {df dg : SpaceTime → SpaceTime →L[ℝ] V}
    (hf : ∀ z ∈ past T, HasFDerivWithinAt f (df z) (past T) z)
    (hg : ∀ z ∈ future T, HasFDerivWithinAt g (dg z) (future T) z)
    (hvalue : ∀ x : Space, f (T, x) = g (T, x))
    (hderiv : ∀ x : Space, df (T, x) = dg (T, x)) (z : SpaceTime) :
    HasFDerivAt (glue T f g) (glue T df dg z) z := by
  have hL (y : SpaceTime) (hy : y ∈ past T) :
      HasFDerivWithinAt (glue T f g) (df y) (past T) y :=
    (hf y hy).congr' (glue_eqOn_past T f g) hy
  have hR (y : SpaceTime) (hy : y ∈ future T) :
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

/-- First-order joint gluing needs only value and first normal-derivative
matching; spatial derivative matching is a consequence. -/
theorem hasFDerivAt_glue_of_normal {T : ℝ} {f g : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (hg : ContDiffOn ℝ ∞ g (future T))
    (hvalue : ∀ x : Space, f (T, x) = g (T, x))
    (hnormal : ∀ x : Space, directional (past T) f timeVector (T, x) =
      directional (future T) g timeVector (T, x)) (z : SpaceTime) :
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
theorem contDiff_glue_finite {T : ℝ} {f g : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (hg : ContDiffOn ℝ ∞ g (future T))
    (hmatch : ∀ n : ℕ, ∀ x : Space,
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
theorem contDiff_glue {T : ℝ} {f g : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (hg : ContDiffOn ℝ ∞ g (future T))
    (hmatch : ∀ n : ℕ, ∀ x : Space,
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
def normalTrace (T : ℝ) (f : SpaceTime → V) (n : ℕ) (x : Space) : V :=
  normalIter (past T) f n (T, x)

theorem normalTrace_contDiff {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (n : ℕ) :
    ContDiff ℝ ∞ (normalTrace T f n) := by
  exact (normalIter_contDiffOn hf (past_uniqueDiff T) n).comp_contDiff
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun x : Space => (T, x)))
    (fun x => show (T, x) ∈ past T from ⟨le_refl T, mem_univ x⟩)

theorem normalTrace_eq_time_jet {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (n : ℕ) (x : Space) :
    normalTrace T f n x = iteratedDerivWithin n (fun t => f (t, x)) (Iic T) T :=
  (time_slice_iteratedDerivWithin (uniqueDiffOn_Iic T) hf x n
    (mem_Iic.mpr (le_refl T))).symm

theorem normalTrace_add_period {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (p : Space)
    (hperiod : ∀ t ≤ T, ∀ x : Space, f (t, x + p) = f (t, x)) (n : ℕ) (x : Space) :
    normalTrace T f n (x + p) = normalTrace T f n x := by
  rw [normalTrace_eq_time_jet hf, normalTrace_eq_time_jet hf]
  exact iteratedDerivWithin_congr (fun t ht => hperiod t ht x) (mem_Iic.mpr (le_refl T))

section Complete

variable [CompleteSpace V]

/-- A constructed global extension: join the closed-past field to the
Taylor--Borel realization of its actual normal jets. -/
def smoothExtension (T : ℝ) (f : SpaceTime → V) (hf : ContDiffOn ℝ ∞ f (past T)) :
    SpaceTime → V :=
  glue T f (SpatialBorelExtension.rightExtension (normalTrace T f)
    (normalTrace_contDiff hf) T)

theorem smoothExtension_contDiff {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) : ContDiff ℝ ∞ (smoothExtension T f hf) := by
  apply contDiff_glue hf
    (SpatialBorelExtension.rightExtension_contDiff (normalTrace T f)
      (normalTrace_contDiff hf) T).contDiffOn
  intro n x
  rw [SpatialBorelExtension.rightExtension_right_jets]
  exact (normalTrace_eq_time_jet hf n x).symm

omit [CompleteSpace V] in
theorem smoothExtension_eqOn_past {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) : EqOn (smoothExtension T f hf) f (past T) :=
  glue_eqOn_past T f _

omit [CompleteSpace V] in
theorem smoothExtension_zero_from {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) {t : ℝ} (ht : T + 1 ≤ t) (x : Space) :
    smoothExtension T f hf (t, x) = 0 := by
  have hnot : ¬t ≤ T := by linarith
  simp only [smoothExtension, glue, ite_eq_right hnot]
  exact SpatialBorelExtension.rightExtension_zero_from (normalTrace T f)
    (normalTrace_contDiff hf) T ht x

/-- Every full mixed jet on the past, including the boundary, is preserved. -/
theorem smoothExtension_iteratedFDeriv {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (n : ℕ) {z : SpaceTime} (hz : z ∈ past T) :
    iteratedFDeriv ℝ n (smoothExtension T f hf) z = iteratedFDerivWithin ℝ n f (past T) z := by
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv (past_uniqueDiff T)
    ((smoothExtension_contDiff hf).of_le (nat_le_infty n)).contDiffAt hz]
  exact iteratedFDerivWithin_congr (smoothExtension_eqOn_past hf) hz n

omit [CompleteSpace V] in
theorem smoothExtension_add_period {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) (p : Space)
    (hperiod : ∀ t ≤ T, ∀ x : Space, f (t, x + p) = f (t, x)) (t : ℝ) (x : Space) :
    smoothExtension T f hf (t, x + p) = smoothExtension T f hf (t, x) := by
  by_cases ht : t ≤ T
  · simp only [smoothExtension, glue, ite_eq_left ht]
    exact hperiod t ht x
  · simp only [smoothExtension, glue, ite_eq_right ht]
    exact SpatialBorelExtension.rightExtension_add_period (normalTrace T f)
      (normalTrace_contDiff hf) T p (normalTrace_add_period hf p hperiod) t x

omit [CompleteSpace V] in
theorem smoothExtension_unit_periods {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T))
    (hperiod : ProblemStatement.UnitSpatialPeriodsOn (Iic T) f) :
    ProblemStatement.UnitSpatialPeriodsOn univ (smoothExtension T f hf) := by
  intro t _ x i
  exact smoothExtension_add_period hf (ProblemStatement.coordinateVector i)
    (fun s hs y => hperiod s hs y i) t x

/-- A complete constructive endpoint theorem for periodic spacetime fields.
The inputs are derivative recurrence and locally uniform left limits, not
closed-side or global smoothness. The resulting extension is jointly smooth,
retains every mixed boundary jet, and vanishes after `T + 1`. -/
theorem exists_smooth_periodic_extension_of_limits {T : ℝ} {f : SpaceTime → V}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hzero : ∀ z : SpaceTime, z.1 < T → (J z 0).curry0 = f z)
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T))
    (hperiod : ProblemStatement.UnitSpatialPeriodsOn (Iio T) f) :
    ∃ F : SpaceTime → V, ContDiff ℝ ∞ F ∧
      EqOn F f (SpacetimeEndpoint.openPast T) ∧
      ProblemStatement.UnitSpatialPeriodsOn univ F ∧
      (∀ t : ℝ, T + 1 ≤ t → ∀ x : Space, F (t, x) = 0) ∧
      ∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n F (T, x) = L x n := by
  let e := SpacetimeEndpoint.extendTrace T f (fun x => (L x 0).curry0)
  have he : ContDiffOn ℝ ∞ e (past T) :=
    SpacetimeEndpoint.contDiffOn_joint_extension hzero hderiv hlim
  have heperiod : ProblemStatement.UnitSpatialPeriodsOn (Iic T) e := by
    intro t _ x i
    exact SpacetimeEndpoint.unit_periods_joint_extension hzero (hlim 0) hperiod
      t (mem_univ t) x i
  refine ⟨smoothExtension T e he, smoothExtension_contDiff he, ?_,
    smoothExtension_unit_periods he heperiod, ?_, ?_⟩
  · intro z hz
    have hzt : z.1 < T := hz.1
    rw [smoothExtension_eqOn_past he ⟨mem_Iic.mpr hzt.le, hz.2⟩]
    exact SpacetimeEndpoint.extendTrace_of_lt hz.1
  · intro t ht x
    exact smoothExtension_zero_from he ht x
  · intro n x
    rw [smoothExtension_iteratedFDeriv he n ⟨mem_Iic.mpr (le_refl T), mem_univ x⟩]
    exact SpacetimeEndpoint.boundary_jets_eq_limits hzero hderiv hlim n x

end Complete

end NavierStokes.SpacetimeGluing
