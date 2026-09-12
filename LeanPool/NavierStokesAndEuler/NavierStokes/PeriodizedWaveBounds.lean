/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSumBounds

/-!
# Whole-lift bounds from the actual native copies

The copy meeting a point is allowed to depend on both the band and the point.
Closed, locally finite support cells give a genuine zero germ on their
complement, including all derivatives.  Constants in the native estimates
are chosen before the band, copy, and evaluation point.

The Gaussian error is assembled as the sum of cutoff-derivative terms plus
one uncovered-source term.  In particular, the source is never summed once
for every inactive copy.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PeriodizedWaveBounds

open Set Function Filter WeightedClasses
open scoped Topology ContDiff BigOperators

section LocalGluing

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Type*}

/-- Closed support cells, with a unique cell at a point.  Neither a finite
index set nor one cell covering the whole strip is required. -/
structure Cells (D : Type*) [TopologicalSpace D] (I : Type*) where
  /-- Carrier of `Cells`, of type `ℕ → I → Set D`. -/
  carrier : ℕ → I → Set D
  closed : ∀ n i, IsClosed (carrier n i)
  locallyFinite : ∀ n, LocallyFinite (carrier n)
  unique : ∀ n i j x, x ∈ carrier n i → x ∈ carrier n j → i = j

/-- Native estimates on the actual functions.  Smoothness is local at the
closed support cell; no continuation of the uncut function around the torus
is imposed.  The weight is evaluated at the actual global point. -/
structure LocalJets (s : StripData D) (w : ℕ → D → ℝ) (α : ℝ)
    (K : ℕ → I → Set D) (f : ℕ → I → D → E) : Prop where
  smooth : ∀ n i x, x ∈ s.domain → x ∈ K n i → ContDiffAt ℝ ∞ (f n i) x
  bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ n i x, x ∈ s.domain → x ∈ K n i → ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (f n i) x‖ ≤ majorant s w α C p n x

theorem jets_eq_of_germ {f g : D → E} {x : D} (h : f =ᶠ[𝓝 x] g) (m : ℕ) :
    iteratedFDeriv ℝ m f x = iteratedFDeriv ℝ m g x := by
  have hw : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using h
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq h.self_of_nhds m

/-- Gluing uses equality on neighborhoods, rather than equality of values or
pointwise derivative limits. -/
theorem memClass_of_local_germs {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {K : ℕ → I → Set D} {f : ℕ → I → D → E} {F : ℕ → D → E}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) (hlocal : LocalJets s w α K f)
    (hcover : ∀ n x, x ∈ s.domain →
      (∃ i, x ∈ K n i ∧ F n =ᶠ[𝓝 x] f n i) ∨ F n =ᶠ[𝓝 x] fun _ => 0) :
    MemClass s w α F := by
  refine ⟨hw, ?_, ?_⟩
  · intro n
    apply s.isOpen_domain.contDiffOn_iff.mpr
    intro x hx
    rcases hcover n x hx with ⟨i, hxi, hg⟩ | hg
    · exact (hlocal.smooth n i x hx hxi).congr_of_eventuallyEq hg
    · exact contDiffAt_const.congr_of_eventuallyEq hg
  · intro m
    obtain ⟨C, hC, p, hB⟩ := hlocal.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro n x hx j hj
    rcases hcover n x hx with ⟨i, hxi, hg⟩ | hg
    · rw [jets_eq_of_germ hg j]
      exact hB n i x hx hxi j hj
    · simp only [jets_eq_of_germ hg j, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact majorant_nonneg s w α hC p n x (hw n x hx)

/-- The actual locally finite copy sum.  Local finiteness is proved from
support cells below; it is not encoded by replacing the sum with a selector. -/
noncomputable def copySum (f : I → D → E) (x : D) : E := ∑' i, f i x

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem zero_germ_of_support {K : Set D} (hK : IsClosed K) {f : D → E}
    (hf : support f ⊆ K) {x : D} (hx : x ∉ K) : f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
  by_contra hne
  exact hy (hf hne)

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem copySum_germ (K : Cells D I) (n : ℕ) (f : I → D → E)
    (hs : ∀ i, support (f i) ⊆ K.carrier n i) {i : I} {x : D}
    (hx : x ∈ K.carrier n i) : copySum f =ᶠ[𝓝 x] f i := by
  classical
  have hn := (K.locallyFinite n).iInter_compl_mem_nhds (K.closed n) x
  filter_upwards [hn] with y hy
  apply tsum_eq_single i
  intro j hji
  have hxj : x ∉ K.carrier n j := fun hxj => hji (K.unique n j i x hxj hx)
  by_contra hne
  exact (mem_iInter₂.mp hy j hxj) (hs j hne)

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem copySum_zero_germ (K : Cells D I) (n : ℕ) (f : I → D → E)
    (hs : ∀ i, support (f i) ⊆ K.carrier n i) {x : D}
    (hx : ∀ i, x ∉ K.carrier n i) : copySum f =ᶠ[𝓝 x] fun _ => 0 := by
  classical
  have hn := (K.locallyFinite n).iInter_compl_mem_nhds (K.closed n) x
  filter_upwards [hn] with y hy
  have hz : ∀ i, f i y = 0 := by
    intro i
    by_contra hne
    exact (mem_iInter₂.mp hy i (hx i)) (hs i hne)
  simp only [copySum, hz, tsum_zero]

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem copySum_germ_cover (K : Cells D I) (n : ℕ) (f : I → D → E)
    (hs : ∀ i, support (f i) ⊆ K.carrier n i) (x : D) :
    (∃ i, x ∈ K.carrier n i ∧ copySum f =ᶠ[𝓝 x] f i) ∨
      copySum f =ᶠ[𝓝 x] fun _ => 0 := by
  classical
  by_cases h : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := h
    exact Or.inl ⟨i, hi, copySum_germ K n f hs hi⟩
  · exact Or.inr (copySum_zero_germ K n f hs (not_exists.mp h))

theorem copySum_memClass {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    (K : Cells D I) {f : ℕ → I → D → E}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hs : ∀ n i, support (f n i) ⊆ K.carrier n i)
    (hj : LocalJets s w α K.carrier f) :
    MemClass s w α (fun n => copySum (f n)) :=
  memClass_of_local_germs hw hj (fun n x _ => copySum_germ_cover K n (f n) (hs n) x)

/-- The proof also gives the very same prefix constants globally. -/
theorem copySum_jet_bound (K : Cells D I) {s : StripData D} {w : ℕ → D → ℝ}
    {α C : ℝ} {p m : ℕ} (hC : 0 ≤ C) (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    {f : ℕ → I → D → E} (hs : ∀ n i, support (f n i) ⊆ K.carrier n i)
    (hb : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f n i) x‖ ≤ majorant s w α C p n x)
    (n : ℕ) {x : D} (hx : x ∈ s.domain) (j : ℕ) (hj : j ≤ m) :
    ‖iteratedFDeriv ℝ j (copySum (f n)) x‖ ≤ majorant s w α C p n x := by
  rcases copySum_germ_cover K n (f n) (hs n) x with ⟨i, hxi, hg⟩ | hg
  · rw [jets_eq_of_germ hg j]
    exact hb n i x hx hxi j hj
  · simp only [jets_eq_of_germ hg j, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact majorant_nonneg s w α hC p n x (hw n x hx)

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem copySum_support (K : Cells D I) (n : ℕ) (f : I → D → E)
    (hs : ∀ i, support (f i) ⊆ K.carrier n i) :
    support (copySum f) ⊆ ⋃ i, K.carrier n i := by
  intro x hx
  by_contra hn
  have hz := copySum_zero_germ K n f hs (by simpa using hn)
  exact hx hz.self_of_nhds

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem copySum_eventually_finite (K : Cells D I) (n : ℕ) (f : I → D → E)
    (hs : ∀ i, support (f i) ⊆ K.carrier n i) (x : D) :
    ∃ J : Finset I, copySum f =ᶠ[𝓝 x] fun y => ∑ i ∈ J, f i y := by
  classical
  obtain ⟨U, hU, hfin⟩ := K.locallyFinite n x
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [hU] with y hy
  apply tsum_eq_sum
  intro i hi
  by_contra hne
  apply hi
  exact hfin.mem_toFinset.mpr ⟨y, hs i hne, hy⟩

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem copySum_tsupport (K : Cells D I) (n : ℕ) (f : I → D → E)
    (hs : ∀ i, support (f i) ⊆ K.carrier n i) :
    tsupport (copySum f) ⊆ ⋃ i, K.carrier n i :=
  closure_minimal (copySum_support K n f hs) ((K.locallyFinite n).isClosed_iUnion (K.closed n))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem copySum_translate (f : I → D → E) (T : D → D) (e : I ≃ I)
    (h : ∀ i x, f (e i) (T x) = f i x) (x : D) :
    copySum f (T x) = copySum f x := by
  unfold copySum
  calc
    _ = ∑' i, f (e i) (T x) := (e.tsum_eq (fun i => f i (T x))).symm
    _ = _ := tsum_congr (fun i => h i x)

/-- Only the primitive source is estimated on the uncovered set.  This is
useful when coverage gives a small tail instead of an identically zero one. -/
structure ComplementJets (s : StripData D) (w : ℕ → D → ℝ) (α : ℝ)
    (K : ℕ → I → Set D) (f : ℕ → D → E) : Prop where
  smooth : ∀ n x, x ∈ s.domain → (∀ i, x ∉ K n i) → ContDiffAt ℝ ∞ (f n) x
  bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ n x, x ∈ s.domain → (∀ i, x ∉ K n i) → ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤ majorant s w α C p n x

theorem majorant_mono_constant (s : StripData D) (w : ℕ → D → ℝ) (α : ℝ)
    {C B : ℝ} (hCB : C ≤ B) (p n : ℕ) (x : D) (hw : 0 ≤ w n x) :
    majorant s w α C p n x ≤ majorant s w α B p n x := by
  have hnonneg : 0 ≤ s.epsilon n ^ α * s.growth n x ^ p * w n x :=
    mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le
      (pow_nonneg (s.growth_nonneg n x) p)) hw
  simpa only [majorant, mul_assoc] using mul_le_mul_of_nonneg_right hCB hnonneg

theorem memClass_of_local_and_complement_germs
    {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {K : ℕ → I → Set D} {f : ℕ → I → D → E} {f₀ F : ℕ → D → E}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hlocal : LocalJets s w α K f) (houtside : ComplementJets s w α K f₀)
    (hactive : ∀ n i x, x ∈ s.domain → x ∈ K n i → F n =ᶠ[𝓝 x] f n i)
    (hinactive : ∀ n x, x ∈ s.domain → (∀ i, x ∉ K n i) → F n =ᶠ[𝓝 x] f₀ n) :
    MemClass s w α F := by
  classical
  refine ⟨hw, ?_, ?_⟩
  · intro n
    apply s.isOpen_domain.contDiffOn_iff.mpr
    intro x hx
    by_cases h : ∃ i, x ∈ K n i
    · obtain ⟨i, hi⟩ := h
      exact (hlocal.smooth n i x hx hi).congr_of_eventuallyEq (hactive n i x hx hi)
    · exact (houtside.smooth n x hx (not_exists.mp h)).congr_of_eventuallyEq
        (hinactive n x hx (not_exists.mp h))
  · intro m
    obtain ⟨C, hC, p, hB⟩ := hlocal.bounds m
    obtain ⟨C₀, hC₀, p₀, hB₀⟩ := houtside.bounds m
    refine ⟨C + C₀, add_nonneg hC hC₀, max p p₀, ?_⟩
    intro n x hx j hj
    by_cases h : ∃ i, x ∈ K n i
    · obtain ⟨i, hi⟩ := h
      rw [jets_eq_of_germ (hactive n i x hx hi) j]
      exact (hB n i x hx hi j hj).trans
        ((majorant_mono_degree s w α hC (le_max_left _ _) n x (hw n x hx)).trans
          (majorant_mono_constant s w α (le_add_of_nonneg_right hC₀) _ n x (hw n x hx)))
    · rw [jets_eq_of_germ (hinactive n x hx (not_exists.mp h)) j]
      exact (hB₀ n x hx (not_exists.mp h) j hj).trans
        ((majorant_mono_degree s w α hC₀ (le_max_right _ _) n x (hw n x hx)).trans
          (majorant_mono_constant s w α (le_add_of_nonneg_left hC) _ n x (hw n x hx)))

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem source_zero_germ (K : Cells D I) {f : ℕ → D → E}
    (hs : ∀ n, support (f n) ⊆ ⋃ i, K.carrier n i) {n : ℕ} {x : D}
    (hx : ∀ i, x ∉ K.carrier n i) : f n =ᶠ[𝓝 x] fun _ => 0 :=
  zero_germ_of_support ((K.locallyFinite n).isClosed_iUnion (K.closed n)) (hs n)
    (by simpa only [mem_iUnion, not_exists] using hx)

end LocalGluing

section UniformLabels

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L I : Type*}

/-- Native bounds uniform also in an external spatial label.  The lattice
copy remains a separate index, so overlap among different labels is not
mistaken for disjointness of copies of one label. -/
structure UniformLocalJets (s : StripData D) (w : L → ℕ → D → ℝ) (α : ℝ)
    (K : L → ℕ → I → Set D) (f : L → ℕ → I → D → E) : Prop where
  smooth : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → ContDiffAt ℝ ∞ (f l n i) x
  bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ l n i x, x ∈ s.domain → x ∈ K l n i → ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (f l n i) x‖ ≤ majorant s (w l) α C p n x

theorem UniformLocalJets.each {s : StripData D} {w : L → ℕ → D → ℝ} {α : ℝ}
    {K : L → ℕ → I → Set D} {f : L → ℕ → I → D → E}
    (hf : UniformLocalJets s w α K f) (l : L) : LocalJets s (w l) α (K l) (f l) := by
  refine ⟨hf.smooth l, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, hb l⟩

theorem uniformClass_of_local_germs {s : StripData D} {w : L → ℕ → D → ℝ} {α : ℝ}
    {K : L → ℕ → I → Set D} {f : L → ℕ → I → D → E} {F : L → ℕ → D → E}
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x) (hj : UniformLocalJets s w α K f)
    (hcover : ∀ l n x, x ∈ s.domain →
      (∃ i, x ∈ K l n i ∧ F l n =ᶠ[𝓝 x] f l n i) ∨ F l n =ᶠ[𝓝 x] fun _ => 0) :
    LabelSumBounds.UniformClass s w α F := by
  refine ⟨hw, fun l => (memClass_of_local_germs (hw l) (hj.each l) (hcover l)).smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hj.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro l n x hx j hjm
  rcases hcover l n x hx with ⟨i, hi, hg⟩ | hg
  · rw [jets_eq_of_germ hg j]
    exact hb l n i x hx hi j hjm
  · simp only [jets_eq_of_germ hg j, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact majorant_nonneg s (w l) α hC p n x (hw l n x hx)

theorem copySum_uniformClass {s : StripData D} {w : L → ℕ → D → ℝ} {α : ℝ}
    (K : L → Cells D I) {f : L → ℕ → I → D → E}
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hs : ∀ l n i, support (f l n i) ⊆ (K l).carrier n i)
    (hj : UniformLocalJets s w α (fun l => (K l).carrier) f) :
    LabelSumBounds.UniformClass s w α (fun l n => copySum (f l n)) :=
  uniformClass_of_local_germs hw hj (fun l n x _ => copySum_germ_cover (K l) n (f l n) (hs l n) x)

end UniformLabels

section NativeCells

open CommonCoverSolve TorusInverse TorusAverages

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Native cell, given by `{z | g.coordinates k z.2 ∈ K}`. -/
noncomputable def nativeCell (g : Geometry) (K : Set Plane) (k : Frequency) : Set (P × Plane) :=
  {z | g.coordinates k z.2 ∈ K}

omit [NormedSpace ℝ P] in
theorem nativeCell_closed (g : Geometry) {K : Set Plane} (hK : IsClosed K) (k : Frequency) :
    IsClosed (nativeCell (P := P) g K k) :=
  hK.preimage ((g.coordinates_contDiff k).continuous.comp continuous_snd)

omit [NormedSpace ℝ P] in
/-- Compact native cells have a locally finite family of all lattice copies.
This applies to a rectangle as well as the actual closed cutoff support. -/
theorem nativeCell_locallyFinite (g : Geometry) {K : Set Plane} (hK : IsCompact K) :
    LocallyFinite (nativeCell (P := P) g K) := by
  classical
  let κ : Plane → ℝ := K.indicator (fun _ => 1)
  have hκ : HasCompactSupport κ :=
    HasCompactSupport.intro' (K := K) hK hK.isClosed (fun z hz => by simp [κ, hz])
  intro z
  obtain ⟨s, hs⟩ := g.finite_copy_cutoffs hκ (‖z.2‖ + 1)
  refine ⟨{y : P × Plane | ‖y.2‖ < ‖z.2‖ + 1},
    (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (by simp), ?_⟩
  apply s.finite_toSet.subset
  intro k hk
  obtain ⟨y, hy, hnorm⟩ := hk
  by_contra hnot
  have hh := hs y.2 hnorm.le k hnot
  change g.coordinates k y.2 ∈ K at hy
  simp [κ, hy] at hh

/-- Native cells, bundling `carrier`, `closed`, `locallyFinite`, `unique`. -/
noncomputable def nativeCells (g : ℕ → Geometry) (K : ℕ → Set Plane)
    (hK : ∀ n, IsCompact (K n))
    (hinj : ∀ n, InjOn quotientPoint ((fun z => (g n).center + (g n).basis z) '' K n)) :
    Cells (P × Plane) Frequency where
  carrier n := nativeCell (g n) (K n)
  closed n := nativeCell_closed (g n) (hK n).isClosed
  locallyFinite n := nativeCell_locallyFinite (g n) (hK n)
  unique n _ _ _ hi hj := ParticularWaveAssembly.native_copy_unique (g n) (hinj n) hi hj

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem native_cutoff_support (g : Geometry) {K : Set Plane} {κ : Plane → ℝ}
    (hκ : support κ ⊆ K) (k : Frequency) :
    support (fun z : P × Plane => κ (g.coordinates k z.2)) ⊆ nativeCell g K k :=
  fun _ hx => hκ hx

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem native_localized_support (g : Geometry) {K : Set Plane} {κ : Plane → ℝ}
    (hκ : support κ ⊆ K) (f : Frequency → P × Plane → E) (k : Frequency) :
    support (fun z => κ (g.coordinates k z.2) • f k z) ⊆ nativeCell g K k := by
  intro z hz
  apply hκ
  intro he
  exact hz (by simp only [he, zero_smul])

/-- Whole-lift weighted bounds for the literal common-copy sum.  The native
smoothness and all-jet estimates are needed only on their own support cell. -/
theorem periodizedCopies_memClass {s : StripData (P × Plane)} {w : ℕ → P × Plane → ℝ}
    {α : ℝ} (g : ℕ → Geometry) (K : ℕ → Set Plane) (hK : ∀ n, IsCompact (K n))
    (hinj : ∀ n, InjOn quotientPoint ((fun z => (g n).center + (g n).basis z) '' K n))
    (κ : ℕ → Plane → ℝ) (hκ : ∀ n, support (κ n) ⊆ K n)
    (f : ℕ → Frequency → P × Plane → E)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hj : LocalJets s w α (fun n => nativeCell (g n) (K n))
      (fun n k x => κ n ((g n).coordinates k x.2) • f n k x)) :
    MemClass s w α (fun n => ParticularWaveBounds.periodizedCopies (g n) (κ n) (f n)) :=
  copySum_memClass (s := s) (w := w) (α := α) (nativeCells (P := P) g K hK hinj) hw
    (fun n => native_localized_support (g n) (hκ n) (f n)) hj

end NativeCells

section NativeJetOperations

variable {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {I : Type*}

private theorem finite_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

private theorem bilinear_jet_at (L : E →L[ℝ] F →L[ℝ] G)
    {u : D → E} {v : D → F} {x : D} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {m j : ℕ} (hj : j ≤ m)
    (hbu : ∀ k ≤ m, ‖iteratedFDeriv ℝ k u x‖ ≤ A)
    (hbv : ∀ k ≤ m, ‖iteratedFDeriv ℝ k v x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun y => L (u y) (v y)) x‖ ≤ ‖L‖ * (2 : ℝ) ^ m * A * B := by
  obtain ⟨U, hU, huU⟩ := hu.contDiffOn (finite_le_infty j) (by simp)
  obtain ⟨V, hV, hvV⟩ := hv.contDiffOn (finite_le_infty j) (by simp)
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem hU hV)
  have hle := JetBounds.norm_iteratedFDeriv_bilinear_le_on L hO
    (huU.mono (hOsub.trans inter_subset_left))
    (hvV.mono (hOsub.trans inter_subset_right)) hxO (le_refl (j : WithTop ℕ∞))
  have hsum : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
      ‖iteratedFDeriv ℝ k u x‖ * ‖iteratedFDeriv ℝ (j - k) v x‖) ≤ (2 : ℝ) ^ m * A * B := by
    calc
      _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro k hk
        have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hbu k (hkj.trans hj)) (Nat.cast_nonneg _))
          (hbv (j - k) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = (2 : ℝ) ^ j * A * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hchoose : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hchoose]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB
  exact hle.trans (by
    calc
      _ ≤ ‖L‖ * ((2 : ℝ) ^ m * A * B) := mul_le_mul_of_nonneg_left hsum (norm_nonneg L)
      _ = _ := by ring)

namespace LocalJets

variable {s : StripData D} {w v : ℕ → D → ℝ} {α β : ℝ}
  {K : ℕ → I → Set D} {f g : ℕ → I → D → E}

theorem of_memClass {f₀ : ℕ → D → E} (hf : MemClass s w α f₀) :
    LocalJets s w α K (fun n _ => f₀ n) := by
  refine ⟨fun n _ x hx _ => (hf.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun n _ x hx _ j hj => hb n x hx j hj⟩

theorem map (hf : LocalJets s w α K f) (L : E →L[ℝ] F) :
    LocalJets s w α K (fun n i x => L (f n i x)) := by
  refine ⟨fun n i x hx hi => L.contDiff.contDiffAt.comp x (hf.smooth n i x hx hi), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, p, ?_⟩
  intro n i x hx hi j hj
  change ‖iteratedFDeriv ℝ j (L ∘ f n i) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left ((hf.smooth n i x hx hi).of_le (finite_le_infty j)) le_rfl]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (f n i) x‖ := L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L‖ * majorant s w α C p n x := mul_le_mul_of_nonneg_left (hb n i x hx hi j hj)
        (norm_nonneg _)
    _ = _ := by unfold majorant; ring

theorem add (hf : LocalJets s w α K f) (hg : LocalJets s w α K g)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) :
    LocalJets s w α K (fun n i x => f n i x + g n i x) := by
  refine ⟨fun n i x hx hi => (hf.smooth n i x hx hi).add (hg.smooth n i x hx hi), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hg.bounds m
  refine ⟨A + B, add_nonneg hA hB, p + q, ?_⟩
  intro n i x hx hi j hj
  rw [fun_iteratedFDeriv_add_apply ((hf.smooth n i x hx hi).of_le (finite_le_infty j))
    ((hg.smooth n i x hx hi).of_le (finite_le_infty j))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f n i) x‖ + ‖iteratedFDeriv ℝ j (g n i) x‖ := norm_add_le _ _
    _ ≤ majorant s w α A p n x + majorant s w α B q n x :=
      add_le_add (ha n i x hx hi j hj) (hb n i x hx hi j hj)
    _ ≤ majorant s w α A (p + q) n x + majorant s w α B (p + q) n x :=
      add_le_add (majorant_mono_degree s w α hA (Nat.le_add_right _ _) n x (hw n x hx))
        (majorant_mono_degree s w α hB (Nat.le_add_left _ _) n x (hw n x hx))
    _ = _ := by unfold majorant; ring

theorem fderiv (hf : LocalJets s w α K f) :
    LocalJets s w α K (fun n i => _root_.fderiv ℝ (f n i)) := by
  refine ⟨fun n i x hx hi => (hf.smooth n i x hx hi).fderiv_right (by simp), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds (m + 1)
  refine ⟨C, hC, p, ?_⟩
  intro n i x hx hi j hj
  rw [norm_iteratedFDeriv_fderiv]
  exact hb n i x hx hi (j + 1) (Nat.add_le_add_right hj 1)

theorem bilinear {u : ℕ → I → D → F} (hf : LocalJets s w α K f)
    (hu : LocalJets s v β K u) (L : E →L[ℝ] F →L[ℝ] G)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hv : ∀ n x, x ∈ s.domain → 0 ≤ v n x) :
    LocalJets s (fun n x => w n x * v n x) (α + β) K
      (fun n i x => L (f n i x) (u n i x)) := by
  refine ⟨fun n i x hx hi => (L.contDiff.contDiffAt.comp x (hf.smooth n i x hx hi)).clm_apply
    (hu.smooth n i x hx hi), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hu.bounds m
  refine ⟨‖L‖ * (2 : ℝ) ^ m * A * B, by positivity, p + q, ?_⟩
  intro n i x hx hi j hj
  calc
    _ ≤ ‖L‖ * (2 : ℝ) ^ m * majorant s w α A p n x * majorant s v β B q n x :=
      bilinear_jet_at L (hf.smooth n i x hx hi) (hu.smooth n i x hx hi)
        (majorant_nonneg s w α hA p n x (hw n x hx))
        (majorant_nonneg s v β hB q n x (hv n x hx)) hj
        (fun k hk => ha n i x hx hi k hk) (fun k hk => hb n i x hx hi k hk)
    _ = (‖L‖ * (2 : ℝ) ^ m) * (majorant s w α A p n x * majorant s v β B q n x) := by ring
    _ = _ := by rw [majorant_mul]; unfold majorant; ring

theorem smul {r : ℕ → I → D → ℝ} (hr : LocalJets s (fun _ _ => 1) 0 K r)
    (hf : LocalJets s w α K f) (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) :
    LocalJets s w α K (fun n i x => r n i x • f n i x) := by
  have h := hr.bilinear hf (ContinuousLinearMap.lsmul ℝ ℝ) (fun _ _ _ => zero_le_one) hw
  simp only [one_mul, zero_add] at h
  exact h

theorem band_smul {r : ℕ → ℝ} (hf : LocalJets s w α K f)
    (hr : BandBound s 0 r) (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) :
    LocalJets s w α K (fun n i x => r n • f n i x) := by
  have hc : UnweightedClass s 0 (fun n (_ : D) => r n) := by
    have h := (unweighted_const s (1 : ℝ)).band_smul hr
    simpa using h
  exact (LocalJets.of_memClass hc).smul hf hw

end LocalJets

end NativeJetOperations

section NativeGaussianEstimates

open GaussianTailFlat

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Type*}

/-- The Gaussian absorption argument is uniform in the native copy.  Its
only local field estimate is the weighted jet bound before absorption. -/
theorem local_gaussian_tail_bound {s : StripData D} {K : ℕ → I → Set D}
    {W : ℕ → D → ℝ} {α c : ℝ} {f : ℕ → I → D → E}
    (hf : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α K f)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : ℕ → I → D → ℝ) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n, ell * ChartScales.S n ≤ L n) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      W n x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n))
    (hzero : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      |θ n i x - 1 / 2| < 1 / 5 → f n i =ᶠ[𝓝 x] fun _ => 0)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n i x, x ∈ s.domain → x ∈ K n i →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j (f n i) x‖ ≤
        C * (1 + ChartScales.S n) ^ p * Real.exp (-(c * ell / 50) * ChartScales.S n) := by
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  obtain ⟨B, hB, hweight⟩ := edges.uniform_weight p
  have hconstant := scales.constant_one_le
  have hdec : 0 < c * ell / 25 := by positivity
  obtain ⟨C, hC, hgauss⟩ := fixed_power_gaussian_bound hdec (scales.power * α)
  refine ⟨A * B * scales.boundConstant ^ p * C, by positivity, scales.degree * p, ?_⟩
  intro n i x hx hi j hj
  have hQ := ChartScales.Q_pos n
  by_cases hmid : |θ n i x - 1 / 2| < 1 / 5
  · rw [jets_eq_of_germ (hzero n i x hx hi hmid) j]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hS : 0 ≤ ChartScales.S n := sq_nonneg _
    positivity
  have htail : 1 / 5 ≤ |θ n i x - 1 / 2| := le_of_not_gt hmid
  have hsq : (1 / 25 : ℝ) ≤ (θ n i x - 1 / 2) ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) htail 2
    norm_num [sq_abs] at hh ⊢
    exact hh
  have hPg : W n x ≤ Real.exp (-(c * ell / 25) * ChartScales.S n) := by
    apply (hW n i x hx hi).trans
    apply (Real.exp_le_exp.2 ?_).trans (gaussian_length_comparison hc.le (hLell n))
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (hL n).le)]
  have hslow0 : 0 ≤ s.slow n := zero_le_one.trans (s.one_le_slow n)
  have hK0 : 0 ≤ scales.boundConstant := zero_le_one.trans scales.constant_one_le
  have hslowp : s.slow n ^ p ≤
      scales.boundConstant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p) := by
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ hslow0 (scales.slow_le n) p
  have hmajor : majorant s (fun n x => Real.sqrt (s.zeta x) * W n x) α A p n x ≤
      (A * B * scales.boundConstant ^ p) * ChartScales.Q n ^ (scales.power * α) *
        ((1 + ChartScales.S n) ^ (scales.degree * p) *
          Real.exp (-(c * ell / 25) * ChartScales.S n)) := by
    rw [majorant, StripData.growth, mul_pow, scales.epsilon_eq, ← Real.rpow_mul hQ.le]
    calc
      _ = (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) * W n x := by ring
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) *
            Real.exp (-(c * ell / 25) * ChartScales.S n) :=
        mul_le_mul_of_nonneg_left hPg (by positivity)
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) * B *
            Real.exp (-(c * ell / 25) * ChartScales.S n) := by
        gcongr
        exact hweight x hx
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) *
          (scales.boundConstant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p))) * B *
            Real.exp (-(c * ell / 25) * ChartScales.S n) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ majorant s (fun n x => Real.sqrt (s.zeta x) * W n x) α A p n x := hb n i x hx hi j hj
    _ ≤ _ := hmajor
    _ = (A * B * scales.boundConstant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (ChartScales.Q n ^ (scales.power * α) *
          Real.exp (-(c * ell / 25) * ChartScales.S n)) := by ring
    _ ≤ (A * B * scales.boundConstant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (C * Real.exp (-((c * ell / 25) / 2) * ChartScales.S n)) := by
      have hS : 0 ≤ ChartScales.S n := sq_nonneg _
      exact mul_le_mul_of_nonneg_left (hgauss n) (by positivity)
    _ = _ := by
      rw [show c * ell / 25 / 2 = c * ell / 50 by ring]
      ring

theorem local_gaussian_all_gains {s : StripData D} {K : ℕ → I → Set D}
    {W : ℕ → D → ℝ} {α c : ℝ} {f : ℕ → I → D → E}
    (hf : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α K f)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : ℕ → I → D → ℝ) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n, ell * ChartScales.S n ≤ L n) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      W n x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n))
    (hzero : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      |θ n i x - 1 / 2| < 1 / 5 → f n i =ᶠ[𝓝 x] fun _ => 0)
    (β : ℝ) : LocalJets s (fun _ _ => 1) β K f := by
  refine ⟨hf.smooth, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := local_gaussian_tail_bound hf edges scales θ L hL ell hell hLell hc hW
      hzero m
  obtain ⟨B, hB, hflat⟩ := gaussian_beats_Q_power (by
      positivity : 0 < c * ell / 50) p (scales.power * β)
  refine ⟨A * B, mul_nonneg hA hB.le, 0, ?_⟩
  intro n i x hx hi j hj
  have ht := (hb n i x hx hi j hj).trans
    (show A * (1 + ChartScales.S n) ^ p * Real.exp (-(c * ell / 50) * ChartScales.S n) ≤
      (A * B) * ChartScales.Q n ^ (scales.power * β) by
        calc
          _ = A * ((1 + ChartScales.S n) ^ p * Real.exp (-(c * ell / 50) * ChartScales.S n)) := by
              ring
          _ ≤ A * (B * ChartScales.Q n ^ (scales.power * β)) := mul_le_mul_of_nonneg_left (hflat n)
              hA
          _ = _ := by ring)
  simpa only [majorant, pow_zero, mul_one, scales.epsilon_eq,
    ← Real.rpow_mul (ChartScales.Q_pos n).le] using ht

end NativeGaussianEstimates

section DifferentialGerms

open HarmonicCalculus LinearWaveResidual
open CurlClassBounds hiding ComplexVector
open ParticularWaveAssembly

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem principal_germ {a b : D → ComplexVector} {p q : D → ℂ} {x : D}
    (ha : a =ᶠ[𝓝 x] b) (hp : p =ᶠ[𝓝 x] q)
    (ε K : ℝ) (R F G Φ : D → ℝ) (Vr Vθ Vz Vf : D → D) :
    LinearWaveResidual.principal ε K R F G Vr Vθ Vz Vf Φ a p =ᶠ[𝓝 x]
      LinearWaveResidual.principal ε K R F G Vr Vθ Vz Vf Φ b q := by
  have ht (i : Fin 3) := along_germ (ha.fun_comp (fun v => v i)) Vf
  filter_upwards [ha, hp, Filter.eventually_all.mpr ht] with y hay hpy hty
  dsimp only [Function.comp_def] at hty
  funext i
  simp only [LinearWaveResidual.principal, shear, hty, hay, hpy]

theorem remainder_germ {a b : D → ComplexVector} {p q : D → ℂ} {x : D}
    (ha : a =ᶠ[𝓝 x] b) (hp : p =ᶠ[𝓝 x] q)
    (ε K : ℝ) (R B F G Φ : D → ℝ) (Vr Vθ Vz Vf Vs : D → D) :
    LinearWaveResidual.remainder ε K R B F G Vr Vθ Vz Vf Vs Φ a p =ᶠ[𝓝 x]
      LinearWaveResidual.remainder ε K R B F G Vr Vθ Vz Vf Vs Φ b q := by
  have hr (i : Fin 3) := along_germ (ha.fun_comp (fun v => v i)) Vr
  have hz (i : Fin 3) := along_germ (ha.fun_comp (fun v => v i)) Vz
  have hs (i : Fin 3) := along_germ (ha.fun_comp (fun v => v i)) Vs
  have hrr (i : Fin 3) := along_germ (hr i) Vr
  have hzz (i : Fin 3) := along_germ (hz i) Vz
  filter_upwards [ha, Filter.eventually_all.mpr hr, Filter.eventually_all.mpr hz,
    Filter.eventually_all.mpr hs, Filter.eventually_all.mpr hrr, Filter.eventually_all.mpr hzz,
    along_germ hp Vr, along_germ hp Vz] with y hay hry hzy hsy hrry hzzy hpr hpz
  dsimp only [Function.comp_def] at hry hzy hsy hrry hzzy
  funext i
  simp only [LinearWaveResidual.remainder, slowTransport, baseDerivativeRemainder,
    strippedPressureGradient, viscousRemainder, hry, hzy, hsy, hrry, hzzy, hpr, hpz, hay]

theorem curlCorrection_germ {a b : D → ComplexVector} {x : D}
    (ha : a =ᶠ[𝓝 x] b) (K : ℝ) (R Φ : D → ℝ) (Vr Vθ Vz : D → D) :
    curlRemainder K R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ a) =ᶠ[𝓝 x]
      curlRemainder K R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ b) := by
  have hc : coefficient R Vr Vθ Vz Φ a =ᶠ[𝓝 x] coefficient R Vr Vθ Vz Φ b := by
    filter_upwards [ha] with y hy
    simp only [coefficient, hy]
  filter_upwards [curl_germ hc R Vr Vθ Vz] with y hy
  simp only [curlRemainder, hy]

theorem potential_germ {a b : D → ComplexVector} {x : D}
    (ha : a =ᶠ[𝓝 x] b) (K : ℝ) (R Φ : D → ℝ) (Vr Vθ Vz : D → D) :
    vectorPotential K R Vr Vθ Vz Φ a =ᶠ[𝓝 x] vectorPotential K R Vr Vθ Vz Φ b := by
  filter_upwards [ha] with y hy
  ext i
  simp only [vectorPotential, HarmonicCalculus.vectorMode, HarmonicCalculus.mode, coefficient, hy]

theorem divergence_germ {a b : D → ComplexVector} {x : D}
    (ha : a =ᶠ[𝓝 x] b) (R : D → ℝ) (Vr Vθ Vz : D → D) :
    cylindricalDivergence R Vr Vθ Vz a =ᶠ[𝓝 x] cylindricalDivergence R Vr Vθ Vz b := by
  filter_upwards [ha, along_germ (ha.fun_comp (fun v => v 0)) Vr,
    along_germ (ha.fun_comp (fun v => v 1)) Vθ,
    along_germ (ha.fun_comp (fun v => v 2)) Vz] with y hy hr hθ hz
  dsimp only [Function.comp_def] at hr hθ hz
  simp only [cylindricalDivergence, hr, hθ, hz, hy]

@[simp] theorem normalCoefficient_zero (N : RealVector) : normalCoefficient N 0 = 0 := by
  simp [normalCoefficient, normalCross]

@[simp] theorem coefficient_zero (R Φ : D → ℝ) (Vr Vθ Vz : D → D) :
    coefficient R Vr Vθ Vz Φ (fun _ => 0) = fun _ => 0 := by
  funext x
  simp only [coefficient, normalCoefficient_zero]

@[simp] theorem cylindricalCurl_zero (R : D → ℝ) (Vr Vθ Vz : D → D) :
    cylindricalCurl R Vr Vθ Vz (fun _ => 0) = fun _ => 0 := by
  funext x i
  fin_cases i <;> simp [cylindricalCurl, along]

@[simp] theorem curlRemainder_zero (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D) :
    curlRemainder K R Vr Vθ Vz (fun _ => 0) = fun _ => 0 := by
  funext x
  simp only [curlRemainder, cylindricalCurl_zero, smul_zero]

@[simp] theorem realizedCoefficient_zero (K : ℝ) (R Φ : D → ℝ) (Vr Vθ Vz : D → D) :
    realizedCoefficient K R Vr Vθ Vz Φ (fun _ => 0) = fun _ => 0 := by
  funext x
  simp only [realizedCoefficient, coefficient_zero, curlRemainder_zero, add_zero]

@[simp] theorem vectorPotential_zero (K : ℝ) (R Φ : D → ℝ) (Vr Vθ Vz : D → D) :
    vectorPotential K R Vr Vθ Vz Φ (fun _ => 0) = fun _ => 0 := by
  funext x i
  simp [vectorPotential, coefficient_zero, vectorMode, mode]

@[simp] theorem principal_zero (ε K : ℝ) (R F G Φ : D → ℝ) (Vr Vθ Vz Vf : D → D) :
    LinearWaveResidual.principal ε K R F G Vr Vθ Vz Vf Φ
      (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
  funext x i
  fin_cases i <;> simp [LinearWaveResidual.principal, shear, along]

@[simp] theorem along_zero (V : D → D) :
    along V (fun _ : D => (0 : ℂ)) = fun _ => 0 := by
  funext x
  simp [along]

@[simp] theorem remainder_zero (ε K : ℝ) (R B F G Φ : D → ℝ) (Vr Vθ Vz Vf Vs : D → D) :
    LinearWaveResidual.remainder ε K R B F G Vr Vθ Vz Vf Vs Φ
      (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
  funext x i
  fin_cases i <;> simp [LinearWaveResidual.remainder, slowTransport, baseDerivativeRemainder,
    strippedPressureGradient, viscousRemainder, angularGenerator, along_zero, along]

@[simp] theorem linearResidual_zero (ε : ℝ) (R : D → ℝ) (Vr Vθ Vz Vt : D → D)
    (B : D → ComplexVector) :
    linearResidual ε R Vr Vθ Vz Vt B (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
  funext x i
  fin_cases i <;> simp [linearResidual, transport, gradient, cylindricalVectorLaplacian,
    cylindricalLaplacian, angularGenerator, along_zero, along]

@[simp] theorem cylindricalDivergence_zero (R : D → ℝ) (Vr Vθ Vz : D → D) :
    cylindricalDivergence R Vr Vθ Vz (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [cylindricalDivergence, along]

end DifferentialGerms

section WaveData

open HarmonicCalculus LinearWaveBounds
open CurlClassBounds hiding ComplexVector
open ParticularWaveAssembly

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Local raw copies share one physical carrier and background.  Their
amplitudes and pressures may differ in every copy and need not be periodic. -/
structure CopyData (D I : Type) where
  /-- Background of `CopyData`, of type `WaveCoefficients D`. -/
  background : WaveCoefficients D
  /-- Amplitude of `CopyData`, of type `ℕ → I → D → ComplexVector`. -/
  amplitude : ℕ → I → D → ComplexVector
  /-- Pressure field of `CopyData`, of type `ℕ → I → D → ℂ`. -/
  pressure : ℕ → I → D → ℂ
  /-- Cutoff of `CopyData`, of type `ℕ → I → D → ℝ`. -/
  cutoff : ℕ → I → D → ℝ
  /-- Source of `CopyData`, of type `ℕ → D → ComplexVector`. -/
  source : ℕ → D → ComplexVector

namespace CopyData

variable (a : CopyData D I)

/-- Raw, given by `{ a.background with amplitude := fun n => a.amplitude n i pressure := fun n
=> a.pressure n i }`. -/
noncomputable def raw (i : I) : WaveCoefficients D :=
  { a.background with amplitude := fun n => a.amplitude n i
                      pressure := fun n => a.pressure n i }

/-- Localized, given by `(a.raw i).withCutoff (fun n => a.cutoff n i)`. -/
noncomputable def localized (i : I) : WaveCoefficients D :=
  (a.raw i).withCutoff (fun n => a.cutoff n i)

/-- Corrected, given by `(a.raw i).corrected s d (fun n => a.cutoff n i)`. -/
noncomputable def corrected (s : StripData D) (d : GraphDirections D) (i : I) :
    WaveCoefficients D := (a.raw i).corrected s d (fun n => a.cutoff n i)

/-- Local good, given by `(a.raw i).constructedGood s d (fun n => a.cutoff n i) n`. -/
noncomputable def localGood (s : StripData D) (d : GraphDirections D) (n : ℕ) (i : I) :
    D → ComplexVector := (a.raw i).constructedGood s d (fun n => a.cutoff n i) n

/-- Local tail, given by `d.Dfast (fun n => a.cutoff n i) n x • a.amplitude n i x`. -/
noncomputable def localTail (d : GraphDirections D) (n : ℕ) (i : I) (x : D) : ComplexVector :=
  d.Dfast (fun n => a.cutoff n i) n x • a.amplitude n i x

/-- Local gaussian, given by `excludedSlotError d (fun n => a.cutoff n i) (fun n => a.amplitude
n i) a.source n`. -/
noncomputable def localGaussian (d : GraphDirections D) (n : ℕ) (i : I) : D → ComplexVector :=
  excludedSlotError d (fun n => a.cutoff n i) (fun n => a.amplitude n i) a.source n

/-- The single native cutoff is applied before periodization and curl. -/
noncomputable def common : WaveCoefficients D :=
  { a.background with
    amplitude := fun n => copySum (fun i => (a.localized i).amplitude n)
    pressure := fun n => copySum (fun i => (a.localized i).pressure n) }

/-- Common corrected, given by `a.common.addAmplitude (a.common.curlCorrection s d)`. -/
noncomputable def commonCorrected (s : StripData D) (d : GraphDirections D) :
    WaveCoefficients D := a.common.addAmplitude (a.common.curlCorrection s d)

/-- An actual global good coefficient, assembled from the cutoff-and-curl
formula on each native copy. -/
noncomputable def globalGood (s : StripData D) (d : GraphDirections D) (n : ℕ) :
    D → ComplexVector := copySum (a.localGood s d n)

/-- Cutoff sum, given by `copySum (a.cutoff n)`. -/
noncomputable def cutoffSum (n : ℕ) : D → ℝ := copySum (a.cutoff n)

/-- Global tail, given by `copySum (a.localTail d n)`. -/
noncomputable def globalTail (d : GraphDirections D) (n : ℕ) : D → ComplexVector :=
  copySum (a.localTail d n)

/-- The shared source occurs once.  This definition also makes sense off
every native patch and preserves the uncovered-source term there. -/
noncomputable def globalGaussian (d : GraphDirections D) (n : ℕ) (x : D) : ComplexVector :=
  a.globalTail d n x + (1 - a.cutoffSum n x) • a.source n x

theorem localGaussian_eq (d : GraphDirections D) (n : ℕ) (i : I) (x : D) :
    a.localGaussian d n i x = a.localTail d n i x + (1 - a.cutoff n i x) • a.source n x := rfl

omit [NormedSpace ℝ D] in
theorem common_amplitude_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (n : ℕ) {i : I} {x : D} (hx : x ∈ K.carrier n i) :
    a.common.amplitude n =ᶠ[𝓝 x] (a.localized i).amplitude n := by
  apply copySum_germ K n _ _ hx
  intro j y hy
  apply hs n j
  intro he
  exact hy (by simp [localized, raw, WaveCoefficients.withCutoff, he])

omit [NormedSpace ℝ D] in
theorem common_pressure_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (n : ℕ) {i : I} {x : D} (hx : x ∈ K.carrier n i) :
    a.common.pressure n =ᶠ[𝓝 x] (a.localized i).pressure n := by
  apply copySum_germ K n _ _ hx
  intro j y hy
  apply hs n j
  intro he
  exact hy (by simp [localized, raw, WaveCoefficients.withCutoff, he])

theorem commonCorrected_amplitude_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) (n : ℕ) {i : I} {x : D}
    (hx : x ∈ K.carrier n i) :
    (a.commonCorrected s d).amplitude n =ᶠ[𝓝 x] (a.corrected s d i).amplitude n :=
  realizedCoefficient_germ (a.common_amplitude_germ K hs n hx) (a.background.frequency n)
    (a.background.radius n) (d.radialField n) (fun _ => d.angular)
    (d.axialField s n) (a.background.phase n)

theorem commonCorrected_residual_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) (n : ℕ) {i : I} {x : D}
    (hx : x ∈ K.carrier n i) :
    (a.commonCorrected s d).harmonicResidual s d n =ᶠ[𝓝 x]
      (a.corrected s d i).harmonicResidual s d n :=
  linearResidual_germ
    (vectorMode_germ (a.commonCorrected_amplitude_germ K hs s d n hx)
      (a.background.frequency n) (a.background.phase n))
    (mode_germ (a.common_pressure_germ K hs n hx)
      (a.background.frequency n) (a.background.phase n))
    (s.epsilon n) (a.background.radius n) (d.radialField n) (fun _ => d.angular)
    (d.axialField s n)
    (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow))
    (LinearWaveResidual.complexBase (a.background.radius n) (a.background.radialBase n)
      (a.background.frequencyBase n) (a.background.axialBase n))

omit [NormedSpace ℝ D] in
theorem localized_amplitude_support (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i) (n : ℕ) (i : I) :
    support ((a.localized i).amplitude n) ⊆ K.carrier n i := by
  intro x hx
  apply hs n i
  intro hz
  exact hx (by simp [localized, raw, WaveCoefficients.withCutoff, hz])

omit [NormedSpace ℝ D] in
theorem localized_pressure_support (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i) (n : ℕ) (i : I) :
    support ((a.localized i).pressure n) ⊆ K.carrier n i := by
  intro x hx
  apply hs n i
  intro hz
  exact hx (by simp [localized, raw, WaveCoefficients.withCutoff, hz])

omit [NormedSpace ℝ D] in
theorem localized_zero_germs {n : ℕ} {i : I} {x : D}
    (hψ : a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) :
    (a.localized i).amplitude n =ᶠ[𝓝 x] (fun _ => 0) ∧
      (a.localized i).pressure n =ᶠ[𝓝 x] (fun _ => 0) := by
  constructor <;> filter_upwards [hψ] with y hy <;>
    simp [localized, raw, WaveCoefficients.withCutoff, hy]

theorem localized_correction_zero_germ (s : StripData D) (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D} (hψ : a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) :
    (a.localized i).curlCorrection s d n =ᶠ[𝓝 x] fun _ => 0 := by
  have h := curlCorrection_germ (a.localized_zero_germs hψ).1
    (a.background.frequency n) (a.background.radius n) (a.background.phase n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
  simp only [coefficient_zero, curlRemainder_zero] at h
  exact h

theorem corrected_zero_germ (s : StripData D) (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D} (hψ : a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) :
    (a.corrected s d i).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  have h := realizedCoefficient_germ (a.localized_zero_germs hψ).1
    (a.background.frequency n) (a.background.radius n) (d.radialField n)
    (fun _ => d.angular) (d.axialField s n) (a.background.phase n)
  simp only [realizedCoefficient_zero] at h
  exact h

theorem localGood_zero_germ (s : StripData D) (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D} (hψ : a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) :
    a.localGood s d n i =ᶠ[𝓝 x] fun _ => 0 := by
  have hc := a.localized_correction_zero_germ s d hψ
  have hp := principal_germ hc (Filter.EventuallyEq.refl (𝓝 x) (fun _ : D => (0 : ℂ)))
    (s.epsilon n) (a.background.frequency n) (a.background.radius n)
    (a.background.frequencyBase n) (a.background.axialBase n) (a.background.phase n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n) (d.fastField n)
  have hr := remainder_germ (a.corrected_zero_germ s d hψ) (a.localized_zero_germs hψ).2
    (s.epsilon n) (a.background.frequency n) (a.background.radius n)
    (a.background.radialBase n) (a.background.frequencyBase n) (a.background.axialBase n)
    (a.background.phase n) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (d.fastField n) (fun _ => d.slow)
  simp only [principal_zero] at hp
  simp only [remainder_zero] at hr
  filter_upwards [hp, hr] with y hpy hry
  change (a.raw i).principalVelocity s d ((a.localized i).curlCorrection s d) n y +
    (a.corrected s d i).remainder s d n y = 0
  change (a.raw i).principalVelocity s d ((a.localized i).curlCorrection s d) n y = 0 at hpy
  change (a.corrected s d i).remainder s d n y = 0 at hry
  rw [hpy, hry, add_zero]

theorem localTail_zero_germ (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D} (hψ : a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) :
    a.localTail d n i =ᶠ[𝓝 x] fun _ => 0 := by
  have hD := along_germ hψ (d.fastField n)
  filter_upwards [hD] with y hy
  change along (d.fastField n) (a.cutoff n i) y • _ = 0
  rw [hy]
  simp [HarmonicCalculus.along]

theorem localGood_support (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) (n : ℕ) (i : I) :
    support (a.localGood s d n i) ⊆ K.carrier n i := by
  intro x hx
  by_contra hn
  exact hx (a.localGood_zero_germ s d (zero_germ_of_support (K.closed n i) (hs n i)
      hn)).self_of_nhds

theorem localTail_support (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (d : GraphDirections D) (n : ℕ) (i : I) :
    support (a.localTail d n i) ⊆ K.carrier n i := by
  intro x hx
  by_contra hn
  exact hx (a.localTail_zero_germ d (zero_germ_of_support (K.closed n i) (hs n i) hn)).self_of_nhds

theorem corrected_support (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) (n : ℕ) (i : I) :
    support ((a.corrected s d i).amplitude n) ⊆ K.carrier n i := by
  intro x hx
  by_contra hn
  exact hx (a.corrected_zero_germ s d (zero_germ_of_support (K.closed n i) (hs n i)
      hn)).self_of_nhds

omit [NormedSpace ℝ D] in
theorem common_zero_germs (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {n : ℕ} {x : D} (hx : ∀ i, x ∉ K.carrier n i) :
    a.common.amplitude n =ᶠ[𝓝 x] (fun _ => 0) ∧
      a.common.pressure n =ᶠ[𝓝 x] (fun _ => 0) :=
  ⟨copySum_zero_germ K n _ (a.localized_amplitude_support K hs n) hx,
    copySum_zero_germ K n _ (a.localized_pressure_support K hs n) hx⟩

theorem commonCorrected_zero_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) {n : ℕ} {x : D}
    (hx : ∀ i, x ∉ K.carrier n i) :
    (a.commonCorrected s d).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  have h := realizedCoefficient_germ (a.common_zero_germs K hs hx).1
    (a.background.frequency n) (a.background.radius n) (d.radialField n)
    (fun _ => d.angular) (d.axialField s n) (a.background.phase n)
  simp only [realizedCoefficient_zero] at h
  exact h

theorem commonResidual_zero_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) {n : ℕ} {x : D}
    (hx : ∀ i, x ∉ K.carrier n i) :
    (a.commonCorrected s d).harmonicResidual s d n =ᶠ[𝓝 x] fun _ => 0 := by
  have hu : vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.commonCorrected s d).amplitude n) =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [a.commonCorrected_zero_germ K hs s d hx] with y hy
    ext i
    simp only [vectorMode, mode, hy, Pi.zero_apply, zero_mul]
  have hp : mode (a.background.frequency n) (a.background.phase n)
      (a.common.pressure n) =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(a.common_zero_germs K hs hx).2] with y hy
    simp only [mode, hy, zero_mul]
  have h := linearResidual_germ hu hp (s.epsilon n) (a.background.radius n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow))
    (LinearWaveResidual.complexBase (a.background.radius n) (a.background.radialBase n)
      (a.background.frequencyBase n) (a.background.axialBase n))
  simp only [linearResidual_zero] at h
  exact h

theorem globalGood_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) (n : ℕ) {i : I} {x : D}
    (hx : x ∈ K.carrier n i) : a.globalGood s d n =ᶠ[𝓝 x] a.localGood s d n i :=
  copySum_germ K n _ (a.localGood_support K hs s d n) hx

theorem globalGood_zero_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) {n : ℕ} {x : D}
    (hx : ∀ i, x ∉ K.carrier n i) : a.globalGood s d n =ᶠ[𝓝 x] fun _ => 0 :=
  copySum_zero_germ K n _ (a.localGood_support K hs s d n) hx

/-- The global Gaussian field has the full native error as its germ, with
both terms and all cutoff derivatives unchanged. -/
theorem globalGaussian_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (d : GraphDirections D) (n : ℕ) {i : I} {x : D} (hx : x ∈ K.carrier n i) :
    a.globalGaussian d n =ᶠ[𝓝 x] a.localGaussian d n i := by
  have hT := copySum_germ K n _ (a.localTail_support K hs d n) hx
  have hψ := copySum_germ K n (a.cutoff n) (hs n) hx
  filter_upwards [hT, hψ] with y hTy hψy
  change copySum (a.localTail d n) y + (1 - copySum (a.cutoff n) y) • a.source n y =
    a.localTail d n i y + (1 - a.cutoff n i y) • a.source n y
  rw [hTy, hψy]

/-- The exact uncovered-source term persists outside the cutoff cells. -/
theorem globalGaussian_uncovered_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (d : GraphDirections D) {n : ℕ} {x : D} (hx : ∀ i, x ∉ K.carrier n i) :
    a.globalGaussian d n =ᶠ[𝓝 x] a.source n := by
  have hT := copySum_zero_germ K n _ (a.localTail_support K hs d n) hx
  have hψ := copySum_zero_germ K n (a.cutoff n) (hs n) hx
  filter_upwards [hT, hψ] with y hTy hψy
  change copySum (a.localTail d n) y + (1 - copySum (a.cutoff n) y) • a.source n y = _
  rw [hTy, hψy]
  simp only [sub_zero, one_smul, zero_add]

/-- Local native cancellation implies cancellation everywhere on the
whole lift.  The source need not vanish on the uncovered complement. -/
theorem common_cancellation (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D)
    (hlocal : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i →
      (a.corrected s d i).harmonicResidual s d n x +
          (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x) =
        (fun j => (a.localGood s d n i x j + a.localGaussian d n i x j) *
          carrier (a.background.frequency n) (a.background.phase n) x))
    (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    (a.commonCorrected s d).harmonicResidual s d n x +
        (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x) =
      (fun j => (a.globalGood s d n x j + a.globalGaussian d n x j) *
        carrier (a.background.frequency n) (a.background.phase n) x) := by
  classical
  by_cases h : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := h
    rw [(a.commonCorrected_residual_germ K hs s d n hi).self_of_nhds,
      (a.globalGood_germ K hs s d n hi).self_of_nhds,
      (a.globalGaussian_germ K hs d n hi).self_of_nhds]
    exact hlocal n i x hx hi
  · have hn := not_exists.mp h
    rw [(a.commonResidual_zero_germ K hs s d hn).self_of_nhds,
      (a.globalGood_zero_germ K hs s d hn).self_of_nhds,
      (a.globalGaussian_uncovered_germ K hs d hn).self_of_nhds]
    simp only [zero_add, Pi.zero_apply]

/-- Global classes for the actually localized common velocity and pressure.
The input fields need be smooth only at their own native support cells. -/
theorem common_classes (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (ha : LocalJets s w α K.carrier (fun n i => (a.localized i).amplitude n))
    (hp : LocalJets s w β K.carrier (fun n i => (a.localized i).pressure n)) :
    MemClass s w α a.common.amplitude ∧ MemClass s w β a.common.pressure :=
  ⟨copySum_memClass K hw (a.localized_amplitude_support K hs) ha,
    copySum_memClass K hw (a.localized_pressure_support K hs) hp⟩

theorem commonCorrected_class_of_native (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {s : StripData D} (d : GraphDirections D) {w : ℕ → D → ℝ} {α : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (ha : LocalJets s w α K.carrier (fun n i => (a.corrected s d i).amplitude n)) :
    MemClass s w α (a.commonCorrected s d).amplitude := by
  apply memClass_of_local_germs hw ha
  intro n x _
  classical
  by_cases h : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := h
    exact Or.inl ⟨i, hi, a.commonCorrected_amplitude_germ K hs s d n hi⟩
  · exact Or.inr (a.commonCorrected_zero_germ K hs s d (not_exists.mp h))

theorem globalGood_class_of_native (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {s : StripData D} (d : GraphDirections D) {w : ℕ → D → ℝ} {α : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hg : LocalJets s w α K.carrier (a.localGood s d)) :
    MemClass s w α (a.globalGood s d) :=
  copySum_memClass K hw (a.localGood_support K hs s d) hg

/-- If the literal incoming source is supported in the union of native
cores, the global Gaussian error is flat whenever the native error jets
are uniformly flat.  No global error class is assumed. -/
theorem globalGaussian_class_of_covered_source (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (hsource : ∀ n, support (a.source n) ⊆ ⋃ i, K.carrier n i)
    {s : StripData D} (d : GraphDirections D) {w : ℕ → D → ℝ} {α : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hg : LocalJets s w α K.carrier (a.localGaussian d)) :
    MemClass s w α (a.globalGaussian d) := by
  apply memClass_of_local_germs hw hg
  intro n x _
  classical
  by_cases h : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := h
    exact Or.inl ⟨i, hi, a.globalGaussian_germ K hs d n hi⟩
  · have hn := not_exists.mp h
    exact Or.inr ((a.globalGaussian_uncovered_germ K hs d hn).trans (source_zero_germ K hsource hn))

/-- A nonzero uncovered source is retained and estimated from its own
primitive jets on that complement. -/
theorem globalGaussian_class_with_complement (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {s : StripData D} (d : GraphDirections D) {w : ℕ → D → ℝ} {α : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hg : LocalJets s w α K.carrier (a.localGaussian d))
    (hf : ComplementJets s w α K.carrier a.source) :
    MemClass s w α (a.globalGaussian d) :=
  memClass_of_local_and_complement_germs hw hg hf
    (fun n _ _ _ hx => a.globalGaussian_germ K hs d n hx)
    (fun _ _ _ hx => a.globalGaussian_uncovered_germ K hs d hx)

/-- The homogeneous construction has only the periodized derivative tail. -/
theorem globalGaussian_of_source_zero (d : GraphDirections D)
    (hf : a.source = fun _ _ => 0) : a.globalGaussian d = a.globalTail d := by
  funext n x
  simp [globalGaussian, hf]

theorem globalGood_support (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) (n : ℕ) :
    support (a.globalGood s d n) ⊆ ⋃ i, K.carrier n i :=
  copySum_support K n _ (a.localGood_support K hs s d n)

theorem globalGaussian_support (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (hsource : ∀ n, support (a.source n) ⊆ ⋃ i, K.carrier n i)
    (d : GraphDirections D) (n : ℕ) :
    support (a.globalGaussian d n) ⊆ ⋃ i, K.carrier n i := by
  intro x hx
  by_contra h
  have hn : ∀ i, x ∉ K.carrier n i := by simpa only [mem_iUnion, not_exists] using h
  have hz := (a.globalGaussian_uncovered_germ K hs d hn).trans (source_zero_germ K hsource hn)
  exact hx hz.self_of_nhds

/-- The global differential formula corresponding to the sum of native
good terms.  Its equality with that sum is proved from actual germs. -/
noncomputable def differentialGood (s : StripData D) (d : GraphDirections D) (n : ℕ) (x : D) :
    ComplexVector :=
  a.common.principalVelocity s d (a.common.curlCorrection s d) n x +
    (a.commonCorrected s d).remainder s d n x

theorem differentialGood_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) (n : ℕ) {i : I} {x : D}
    (hx : x ∈ K.carrier n i) :
    a.differentialGood s d n =ᶠ[𝓝 x] a.localGood s d n i := by
  have hc := curlCorrection_germ (a.common_amplitude_germ K hs n hx)
    (a.background.frequency n) (a.background.radius n) (a.background.phase n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
  have hp := principal_germ hc (Filter.EventuallyEq.refl (𝓝 x) (fun _ : D => (0 : ℂ)))
    (s.epsilon n) (a.background.frequency n) (a.background.radius n)
    (a.background.frequencyBase n) (a.background.axialBase n) (a.background.phase n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n) (d.fastField n)
  have hr := remainder_germ (a.commonCorrected_amplitude_germ K hs s d n hx)
    (a.common_pressure_germ K hs n hx)
    (s.epsilon n) (a.background.frequency n) (a.background.radius n)
    (a.background.radialBase n) (a.background.frequencyBase n) (a.background.axialBase n)
    (a.background.phase n) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (d.fastField n) (fun _ => d.slow)
  filter_upwards [hp, hr] with y hpy hry
  exact congrArg₂ (· + ·) hpy hry

theorem differentialGood_zero_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) {n : ℕ} {x : D}
    (hx : ∀ i, x ∉ K.carrier n i) :
    a.differentialGood s d n =ᶠ[𝓝 x] fun _ => 0 := by
  have hc := curlCorrection_germ (a.common_zero_germs K hs hx).1
    (a.background.frequency n) (a.background.radius n) (a.background.phase n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
  simp only [coefficient_zero, curlRemainder_zero] at hc
  have hp := principal_germ hc (Filter.EventuallyEq.refl (𝓝 x) (fun _ : D => (0 : ℂ)))
    (s.epsilon n) (a.background.frequency n) (a.background.radius n)
    (a.background.frequencyBase n) (a.background.axialBase n) (a.background.phase n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n) (d.fastField n)
  have hr := remainder_germ (a.commonCorrected_zero_germ K hs s d hx) (a.common_zero_germs K hs
      hx).2
    (s.epsilon n) (a.background.frequency n) (a.background.radius n)
    (a.background.radialBase n) (a.background.frequencyBase n) (a.background.axialBase n)
    (a.background.phase n) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (d.fastField n) (fun _ => d.slow)
  simp only [principal_zero] at hp
  simp only [remainder_zero] at hr
  filter_upwards [hp, hr] with y hpy hry
  exact (congrArg₂ (· + ·) hpy hry).trans (zero_add 0)

theorem globalGood_eq_differentialGood (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) :
    a.globalGood s d = a.differentialGood s d := by
  classical
  funext n x
  by_cases h : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := h
    exact (a.globalGood_germ K hs s d n hi).self_of_nhds.trans
      (a.differentialGood_germ K hs s d n hi).self_of_nhds.symm
  · exact (a.globalGood_zero_germ K hs s d (not_exists.mp h)).self_of_nhds.trans
      (a.differentialGood_zero_germ K hs s d (not_exists.mp h)).self_of_nhds.symm

/-- Only the carrier, geometry, and base fields of this coefficient are
used in the background estimates. -/
noncomputable def backgroundOnly : WaveCoefficients D :=
  { a.background with amplitude := fun _ _ => 0, pressure := fun _ _ => 0 }

theorem common_inputBounds (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {s : StripData D} {d : GraphDirections D} {W : ℕ → D → ℝ} {α κ : ℝ}
    (hb : InputBounds s W α κ d a.backgroundOnly)
    (ha : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α K.carrier
      (fun n i => (a.localized i).amplitude n))
    (hp : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) (α + 1 / 2) K.carrier
      (fun n i => (a.localized i).pressure n)) :
    InputBounds s W α κ d a.common := by
  obtain ⟨hva, hvp⟩ := a.common_classes K hs (hb.amplitude 0).weight_nonneg ha hp
  exact { hb with amplitude := fun i => hva.map (ContinuousLinearMap.proj i), pressure := hvp }

/-- Primitive background estimates and native localized velocity/pressure
jets imply the actual global curl correction and good-remainder classes.
Neither a local nor a global remainder-class hypothesis is used. -/
theorem common_bounds_from_native (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {s : StripData D} {d : GraphDirections D} {W : ℕ → D → ℝ} {α κ : ℝ}
    (hb : InputBounds s W α κ d a.backgroundOnly)
    (ha : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α K.carrier
      (fun n i => (a.localized i).amplitude n))
    (hp : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) (α + 1 / 2) K.carrier
      (fun n i => (a.localized i).pressure n))
    (hκ : κ ≤ 1 / 2) {R : D → ℝ} (hR : a.background.radius = fun _ => R)
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) (a.background.normal s d))
    {b M : ℝ} (hpos : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖a.background.normal s d n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖a.background.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.background.frequency n)) :
    WaveClass s W α a.common.amplitude ∧
    WaveClass s W α (a.commonCorrected s d).amplitude ∧
    WaveClass s W (α + 1 / 2) a.common.pressure ∧
    WaveClass s W (α + 1 / 2 - κ) (a.common.curlCorrection s d) ∧
    WaveClass s W (α + 1 / 2 - 3 * κ) (a.globalGood s d) := by
  have h := a.common_inputBounds K hs hb ha hp
  have hc := h.curlCorrection_class hR hN hpos hlower hupper hK
  have hci i := hc.map (ContinuousLinearMap.proj i)
  have hcorrected := h.add_curl_amplitude hκ hci
  refine ⟨component_classes h.amplitude, component_classes hcorrected.amplitude,
    h.pressure, hc, ?_⟩
  rw [a.globalGood_eq_differentialGood K hs s d]
  exact (h.curl_principal_gain hci).add hcorrected.remainder_class

theorem localGaussian_wave_jets {s : StripData D} (d : GraphDirections D)
    {K : ℕ → I → Set D} {w : ℕ → D → ℝ} {α : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hψ : LocalJets s (fun _ _ => 1) 0 K a.cutoff)
    (hfast : BandBound s 0 d.fastScale)
    (hu : LocalJets s w α K a.amplitude)
    (hf : LocalJets s w α K (fun n _ => a.source n)) :
    LocalJets s w α K (a.localGaussian d) := by
  have hdir := (hψ.fderiv.map (ContinuousLinearMap.apply ℝ ℝ d.fast)).band_smul hfast
    (fun _ _ _ => zero_le_one)
  have hD : LocalJets s (fun _ _ => 1) 0 K
      (fun n i => d.Dfast (fun n => a.cutoff n i) n) := by
    convert! hdir using 1
    funext n i x
    simp [GraphDirections.Dfast, GraphDirections.fastField, HarmonicCalculus.along]
  have hconst : LocalJets s (fun _ _ => 1) 0 K (fun _ _ (_ : D) => (1 : ℝ)) :=
    LocalJets.of_memClass (unweighted_const s 1)
  have hneg := hψ.map (-ContinuousLinearMap.id ℝ ℝ)
  have hminus : LocalJets s (fun _ _ => 1) 0 K (fun n i x => 1 - a.cutoff n i x) := by
    simpa only [_root_.neg_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg] using
      hconst.add hneg (fun _ _ _ => zero_le_one)
  exact (hD.smul hu hw).add (hminus.smul hf hw) hw

theorem localGaussian_zero_of_cutoff_one (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D} (hψ : a.cutoff n i =ᶠ[𝓝 x] fun _ => 1) :
    a.localGaussian d n i =ᶠ[𝓝 x] fun _ => 0 := by
  have hD := along_germ hψ (d.fastField n)
  filter_upwards [hψ, hD] with y hψy hDy
  change along (d.fastField n) (a.cutoff n i) y • _ + (1 - a.cutoff n i y) • _ = 0
  rw [hDy, hψy]
  simp [along]

theorem localGaussian_zero_of_fields (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D}
    (hu : a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) (hf : a.source n =ᶠ[𝓝 x] fun _ => 0) :
    a.localGaussian d n i =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hu, hf] with y huy hfy
  simp only [localGaussian, excludedSlotError, huy, hfy, smul_zero, add_zero]

/-- Primitive native amplitude/source/cutoff jets and a Gaussian envelope
prove flatness of the actual two cutoff products, uniformly over every copy.
The central alternative allows transverse regions where both fields vanish. -/
theorem localGaussian_all_gains_from_native {s : StripData D} (d : GraphDirections D)
    {K : ℕ → I → Set D} {W : ℕ → D → ℝ} {α c : ℝ}
    (hWnonneg : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (hψ : LocalJets s (fun _ _ => 1) 0 K a.cutoff)
    (hfast : BandBound s 0 d.fastScale)
    (hu : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α K a.amplitude)
    (hf : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α K (fun n _ => a.source n))
    (edges : GaussianTailFlat.FlatEdges s) (scales : GaussianTailFlat.BandScaleControl s)
    (θ : ℕ → I → D → ℝ) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n, ell * ChartScales.S n ≤ L n) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      W n x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n))
    (hcentral : ∀ n i x, x ∈ s.domain → x ∈ K n i → |θ n i x - 1 / 2| < 1 / 5 →
      (a.cutoff n i =ᶠ[𝓝 x] fun _ => 1) ∨
        ((a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)))
    (β : ℝ) : LocalJets s (fun _ _ => 1) β K (a.localGaussian d) := by
  have hj := a.localGaussian_wave_jets d
    (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hWnonneg n x hx)) hψ hfast hu hf
  apply local_gaussian_all_gains hj edges scales θ L hL ell hell hLell hc hW _ β
  intro n i x hx hi hmid
  rcases hcentral n i x hx hi hmid with hone | ⟨hu0, hf0⟩
  · exact a.localGaussian_zero_of_cutoff_one d hone
  · exact a.localGaussian_zero_of_fields d hu0 hf0

/-- The whole-lift Gaussian estimate derives every native output jet from
primitive data, then glues using the actual periodized fields and source
coverage.  No Gaussian error class is an input. -/
theorem globalGaussian_all_gains_from_native (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (hsource : ∀ n, support (a.source n) ⊆ ⋃ i, K.carrier n i)
    {s : StripData D} (d : GraphDirections D) {W : ℕ → D → ℝ} {α c : ℝ}
    (hWnonneg : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (hψ : LocalJets s (fun _ _ => 1) 0 K.carrier a.cutoff)
    (hfast : BandBound s 0 d.fastScale)
    (hu : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α K.carrier a.amplitude)
    (hf : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α K.carrier (fun n _ => a.source n))
    (edges : GaussianTailFlat.FlatEdges s) (scales : GaussianTailFlat.BandScaleControl s)
    (θ : ℕ → I → D → ℝ) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n, ell * ChartScales.S n ≤ L n) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i →
      W n x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n))
    (hcentral : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i → |θ n i x - 1 / 2| < 1 / 5 →
      (a.cutoff n i =ᶠ[𝓝 x] fun _ => 1) ∨
        ((a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)))
    (β : ℝ) : UnweightedClass s β (a.globalGaussian d) :=
  a.globalGaussian_class_of_covered_source K hs hsource d (fun _ _ _ => zero_le_one)
    (a.localGaussian_all_gains_from_native d hWnonneg hψ hfast hu hf edges scales θ L hL
      ell hell hLell hc hW hcentral β)

theorem common_potential_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) (n : ℕ) {i : I} {x : D}
    (hx : x ∈ K.carrier n i) :
    a.common.curlPotential s d n =ᶠ[𝓝 x] (a.localized i).curlPotential s d n :=
  potential_germ (a.common_amplitude_germ K hs n hx) (a.background.frequency n)
    (a.background.radius n) (a.background.phase n) (d.radialField n)
    (fun _ => d.angular) (d.axialField s n)

theorem common_potential_zero_germ (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) {n : ℕ} {x : D}
    (hx : ∀ i, x ∉ K.carrier n i) :
    a.common.curlPotential s d n =ᶠ[𝓝 x] fun _ => 0 := by
  have h := potential_germ (a.common_zero_germs K hs hx).1 (a.background.frequency n)
    (a.background.radius n) (a.background.phase n) (d.radialField n)
    (fun _ => d.angular) (d.axialField s n)
  simp only [vectorPotential_zero] at h
  exact h

/-- The globally assembled velocity is the actual curl of the globally
assembled potential whenever the native construction has that identity. -/
theorem common_realizes_curl (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D)
    (hnative : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i →
      cylindricalCurl (a.background.radius n) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) ((a.localized i).curlPotential s d n) x =
      vectorMode (a.background.frequency n) (a.background.phase n)
        ((a.corrected s d i).amplitude n) x)
    (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    cylindricalCurl (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) (a.common.curlPotential s d n) x =
    vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.commonCorrected s d).amplitude n) x := by
  classical
  by_cases h : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := h
    rw [(curl_germ (a.common_potential_germ K hs s d n hi) (a.background.radius n)
      (d.radialField n) (fun _ => d.angular) (d.axialField s n)).self_of_nhds]
    rw [(vectorMode_germ (a.commonCorrected_amplitude_germ K hs s d n hi)
      (a.background.frequency n) (a.background.phase n)).self_of_nhds]
    exact hnative n i x hx hi
  · have hn := not_exists.mp h
    rw [(curl_germ (a.common_potential_zero_germ K hs s d hn) (a.background.radius n)
      (d.radialField n) (fun _ => d.angular) (d.axialField s n)).self_of_nhds]
    rw [(vectorMode_germ (a.commonCorrected_zero_germ K hs s d hn)
      (a.background.frequency n) (a.background.phase n)).self_of_nhds]
    ext i
    simp [cylindricalCurl_zero, HarmonicCalculus.vectorMode, HarmonicCalculus.mode]

/-- A local differential identity is transported through full neighborhood
germs, so the support boundary contributes no extra divergence. -/
theorem common_divergence_zero (K : Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D)
    (hnative : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i →
      cylindricalDivergence (a.background.radius n) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (vectorMode (a.background.frequency n) (a.background.phase n)
          ((a.corrected s d i).amplitude n)) x = 0)
    (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    cylindricalDivergence (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) (vectorMode (a.background.frequency n) (a.background.phase n)
        ((a.commonCorrected s d).amplitude n)) x = 0 := by
  classical
  by_cases h : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := h
    have hg := divergence_germ (vectorMode_germ (a.commonCorrected_amplitude_germ K hs s d n hi)
      (a.background.frequency n) (a.background.phase n)) (a.background.radius n)
      (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    exact hg.self_of_nhds.trans (hnative n i x hx hi)
  · have hu : vectorMode (a.background.frequency n) (a.background.phase n)
        ((a.commonCorrected s d).amplitude n) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [a.commonCorrected_zero_germ K hs s d (not_exists.mp h)] with y hy
      ext i
      simp only [HarmonicCalculus.vectorMode, HarmonicCalculus.mode, hy, Pi.zero_apply, zero_mul]
    have hg := divergence_germ hu (a.background.radius n) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n)
    simpa only [cylindricalDivergence_zero] using hg.self_of_nhds

open CopyAngularInvariance in
theorem common_amplitude_invariant (v : D)
    (hψ : ∀ n i, Invariant v (a.cutoff n i))
    (hu : ∀ n i, Invariant v (a.amplitude n i)) (n : ℕ) :
    Invariant v (a.common.amplitude n) :=
  Invariant.tsum_invariant (fun i => (hψ n i).map₂ (hu n i) (fun r u => r • u))

open CopyAngularInvariance in
theorem common_pressure_invariant (v : D)
    (hψ : ∀ n i, Invariant v (a.cutoff n i))
    (hp : ∀ n i, Invariant v (a.pressure n i)) (n : ℕ) :
    Invariant v (a.common.pressure n) :=
  Invariant.tsum_invariant (fun i => (hψ n i).map₂ (hp n i) (fun r p => (r : ℂ) * p))

open CopyAngularInvariance in
theorem commonCorrected_invariant (s : StripData D) (d : GraphDirections D) (v : D)
    (hψ : ∀ n i, Invariant v (a.cutoff n i))
    (hu : ∀ n i, Invariant v (a.amplitude n i))
    (hR : ∀ n, Invariant v (a.background.radius n))
    (hr : ∀ n, Invariant v (d.radialField n))
    (hz : ∀ n, Invariant v (d.axialField s n))
    (hΦ : ∀ n, ∃ m, AffinePhase v m (a.background.phase n)) (n : ℕ) :
    Invariant v ((a.commonCorrected s d).amplitude n) := by
  obtain ⟨m, hm⟩ := hΦ n
  exact realizedCoefficient_invariant (hR n) (hr n) (Invariant.const _) (hz n) hm
    (a.common_amplitude_invariant v hψ hu n) (a.background.frequency n)

open CopyAngularInvariance in
theorem globalGaussian_invariant (d : GraphDirections D) (v : D)
    (hψ : ∀ n i, Invariant v (a.cutoff n i))
    (hu : ∀ n i, Invariant v (a.amplitude n i))
    (hf : ∀ n, Invariant v (a.source n)) (n : ℕ) :
    Invariant v (a.globalGaussian d n) := by
  have hT : Invariant v (a.globalTail d n) := Invariant.tsum_invariant (fun i =>
    ((hψ n i).along (Invariant.const _)).map₂ (hu n i) (fun r u => r • u))
  have hS : Invariant v (a.cutoffSum n) := Invariant.tsum_invariant (hψ n)
  exact hT.map₂ (hS.map₂ (hf n) (fun r f => (1 - r) • f)) (fun u w => u + w)

open CopyAngularInvariance in
theorem globalGood_invariant (s : StripData D) (d : GraphDirections D)
    (hψ : ∀ n i, Invariant d.angular (a.cutoff n i))
    (hu : ∀ n i, Invariant d.angular (a.amplitude n i))
    (hp : ∀ n i, Invariant d.angular (a.pressure n i))
    (hR : ∀ n, Invariant d.angular (a.background.radius n))
    (hb : ∀ n, Invariant d.angular (a.background.radialBase n))
    (hF : ∀ n, Invariant d.angular (a.background.frequencyBase n))
    (hG : ∀ n, Invariant d.angular (a.background.axialBase n))
    (hr : ∀ n, Invariant d.angular (d.radialField n))
    (hz : ∀ n, Invariant d.angular (d.axialField s n))
    (hΦ : ∀ n, ∃ m, AffinePhase d.angular m (a.background.phase n)) (n : ℕ) :
    Invariant d.angular (a.globalGood s d n) :=
  Invariant.tsum_invariant (fun i => constructedGood_invariant (a := a.raw i)
    (fun n => a.cutoff n i) hR hb hF hG hr hz hΦ (fun n => hu n i) (fun n => hp n i)
    (fun n => hψ n i) n)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Deck reindexing is sufficient for common-field periodicity; individual
uncut copies need not be periodic. -/
theorem common_translate (n : ℕ) (T : D → D) (e : I ≃ I)
    (hψ : ∀ i x, a.cutoff n (e i) (T x) = a.cutoff n i x)
    (hu : ∀ i x, a.amplitude n (e i) (T x) = a.amplitude n i x)
    (hp : ∀ i x, a.pressure n (e i) (T x) = a.pressure n i x) (x : D) :
    a.common.amplitude n (T x) = a.common.amplitude n x ∧
      a.common.pressure n (T x) = a.common.pressure n x := by
  constructor
  · apply copySum_translate _ T e _ x
    intro i y
    change a.cutoff n (e i) (T y) • a.amplitude n (e i) (T y) = _
    rw [hψ, hu]
    rfl
  · apply copySum_translate _ T e _ x
    intro i y
    change (a.cutoff n (e i) (T y) : ℂ) * a.pressure n (e i) (T y) = _
    rw [hψ, hp]
    rfl

theorem globalGaussian_translate (d : GraphDirections D) (n : ℕ) (z : D) (e : I ≃ I)
    (hψ : ∀ i x, a.cutoff n (e i) (x + z) = a.cutoff n i x)
    (hu : ∀ i x, a.amplitude n (e i) (x + z) = a.amplitude n i x)
    (hf : ∀ x, a.source n (x + z) = a.source n x) (x : D) :
    a.globalGaussian d n (x + z) = a.globalGaussian d n x := by
  have hT : a.globalTail d n (x + z) = a.globalTail d n x := by
    apply copySum_translate _ (fun x => x + z) e _ x
    intro i y
    have hD : fderiv ℝ (a.cutoff n (e i)) (y + z) = fderiv ℝ (a.cutoff n i) y := by
      rw [← fderiv_comp_add_right z, show (fun x => a.cutoff n (e i) (x + z)) = a.cutoff n i from
          funext (hψ i)]
    simp only [localTail, GraphDirections.Dfast, HarmonicCalculus.along,
      GraphDirections.fastField, hD, hu]
  have hS : a.cutoffSum n (x + z) = a.cutoffSum n x := copySum_translate _ (fun x => x + z) e hψ x
  simp only [globalGaussian, hT, hS, hf]

end CopyData

end WaveData

section ActualParticularData

open CommonCoverSolve TorusInverse TorusAverages ParticularWaveBounds
open ParticularWaveAssembly HarmonicCalculus LinearWaveBounds
open CorrectionState ErrorHarmonics

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Actual complex copy solves with arbitrary band-dependent entry/exit
times.  In particular, a transported clock may use `exit = length / clock`.
The tangent coefficients, source, geometry, and frequency are the actual
inputs of `complexCopyVelocity` and its projected pressure. -/
noncomputable def complexCopyData (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (entry exit : ℕ → ℝ) (hab : ∀ n, entry n ≤ exit n)
    (κ : ℕ → Plane → ℝ) : CopyData (P × Plane) Frequency where
  background := base
  amplitude n k := complexCopyVelocity (t n) (source n) (g n) (hab n) k
  pressure n k := complexCopyPressure (t n) (source n) (g n) (hab n) k (base.frequency n)
  cutoff n k z := κ n ((g n).coordinates k z.2)
  source := source

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyData_common (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (entry exit : ℕ → ℝ) (hab : ∀ n, entry n ≤ exit n)
    (κ : ℕ → Plane → ℝ) :
    (complexCopyData base t source g entry exit hab κ).common =
      { base with
        amplitude := fun n => commonVelocity (t n) (source n) (g n) (hab n) (κ n)
        pressure := fun n => commonPressure (t n) (source n) (g n) (hab n) (κ n) (base.frequency n)
            } := rfl

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem complexCopyData_common_periodic (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (entry exit : ℕ → ℝ) (hab : ∀ n, entry n ≤ exit n)
    (κ : ℕ → Plane → ℝ) (n : ℕ) (p : P) (hp : PeriodicAt (source n) p) :
    PeriodicAt ((complexCopyData base t source g entry exit hab κ).common.amplitude n) p ∧
    PeriodicAt ((complexCopyData base t source g entry exit hab κ).common.pressure n) p :=
  ⟨commonVelocity_periodic (t n) (source n) (g n) (hab n) (κ n) p hp,
    commonPressure_periodic (t n) (source n) (g n) (hab n) (κ n) (base.frequency n) p hp⟩

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyData_cutoff_support (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (entry exit : ℕ → ℝ) (hab : ∀ n, entry n ≤ exit n)
    (κ : ℕ → Plane → ℝ) (K : ℕ → Set Plane) (hκ : ∀ n, support (κ n) ⊆ K n)
    (n : ℕ) (k : Frequency) :
    support ((complexCopyData base t source g entry exit hab κ).cutoff n k) ⊆
      nativeCell (g n) (K n) k := native_cutoff_support (g n) (hκ n) k

/-- The data-only binding to the actual fixed-reference particular solve.
The source is the literal coefficient of the incoming harmonic residual;
no inverse, output field, or residual witness is supplied separately. -/
noncomputable def particularData (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) : CopyData ((P × ℝ) × Plane) Frequency where
  background := actualCarrier base b j
  amplitude n k := (actualCopyCoefficients r charts c u b G A j base (fun _ => k)).amplitude n
  pressure n k := (actualCopyCoefficients r charts c u b G A j base (fun _ => k)).pressure n
  cutoff n k z := r.cutoff ((bandGeometry r charts n).coordinates k z.2)
  source n := angleLift (residualSource c u b G A j n)

theorem particularData_eq_complexCopyData (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) :
    particularData r charts c u b G A j base =
      complexCopyData (actualCarrier base b j) (fun n => angleTangent (bandTangent r charts j n))
        (fun n => angleLift (residualSource c u b G A j n)) (bandGeometry r charts)
        (fun _ => 0) (fun _ => r.length) (fun _ => r.length_pos.le) (fun _ => r.cutoff) := rfl

theorem particularData_raw (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (k : Frequency) :
    (particularData r charts c u b G A j base).raw k =
      actualCopyCoefficients r charts c u b G A j base (fun _ => k) := rfl

theorem particularData_source (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (n : ℕ) (z : (P × ℝ) × Plane) (i : Fin 3) :
    (particularData r charts c u b G A j base).source n z i =
      (HarmonicResidual.residualBlock c u b G A).velocity n i j (z.1.1, z.2) := rfl

theorem particularData_frequency (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (n : ℕ) :
    (particularData r charts c u b G A j base).background.frequency n = (j : ℝ) * b.frequency n :=
        rfl

theorem particularData_phase (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (n : ℕ) (z : (P × ℝ) × Plane) :
    (particularData r charts c u b G A j base).background.phase n z =
      b.phase n (z.1.1, z.2) + (b.angularFrequency n : ℝ) / b.frequency n * z.1.2 := rfl

theorem particularData_cutoff_support (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (K : ℕ → Set Plane)
    (hK : ∀ n, support r.cutoff ⊆ K n) (n : ℕ) (k : Frequency) :
    support ((particularData r charts c u b G A j base).cutoff n k) ⊆
      nativeCell (bandGeometry r charts n) (K n) k :=
  native_cutoff_support (bandGeometry r charts n) (hK n) k

/-- This is the same actual periodization as `ParticularWaveAssembly`,
with its single physical reference and original source. -/
theorem particularData_common (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) {j : ℤ} (hj : j ≠ 0)
    (hfrequency : ∀ n, b.frequency n ≠ 0)
    (base : WaveCoefficients ((P × ℝ) × Plane)) :
    (particularData r charts c u b G A j base).common =
      actualCommonCoefficients r charts c u b G A j base := by
  let a := particularData r charts c u b G A j base
  have ha : a.common.amplitude = (actualCommonCoefficients r charts c u b G A j base).amplitude :=
      by
    funext n
    rw [actualCommon_amplitude_periodization]
    rfl
  have hp : a.common.pressure = (actualCommonCoefficients r charts c u b G A j base).pressure := by
    funext n
    rw [actualCommon_pressure_periodization r charts c u b G A hj hfrequency]
    rfl
  calc
    a.common = { actualCarrier base b j with amplitude := a.common.amplitude, pressure :=
        a.common.pressure } := rfl
    _ = { actualCarrier base b j with
      amplitude := (actualCommonCoefficients r charts c u b G A j base).amplitude,
      pressure := (actualCommonCoefficients r charts c u b G A j base).pressure } := by rw [ha, hp]
    _ = _ := rfl

theorem particularData_commonCorrected (r : Reference P) (charts : BandCharts P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) {j : ℤ} (hj : j ≠ 0)
    (hfrequency : ∀ n, b.frequency n ≠ 0)
    (base : WaveCoefficients ((P × ℝ) × Plane)) (s : StripData ((P × ℝ) × Plane))
    (d : GraphDirections ((P × ℝ) × Plane)) :
    (particularData r charts c u b G A j base).commonCorrected s d =
      actualCorrectedCommon r charts c u b G A j base s d := by
  unfold CopyData.commonCorrected actualCorrectedCommon
  rw [particularData_common r charts c u b G A hj hfrequency]

end ActualParticularData

end NavierStokes.PeriodizedWaveBounds
