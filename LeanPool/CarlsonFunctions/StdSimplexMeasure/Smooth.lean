/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.CoordinateRealization
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Smooth functions and affine slices on the standard simplex

These geometric and calculus lemmas do not depend on Dirichlet densities or parameters.
The historical `DirichletTransform` namespace is retained for compatibility.
-/

open Complex Set Filter
open scoped Topology

@[expose] public noncomputable section

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- A function has `N` continuous derivatives near the closed standard simplex if it has that
regularity on some open neighborhood of the simplex in the ambient coordinate space. -/
def ContDiffNearStdSimplex (N : ℕ) (f : (ι → ℝ) → ℂ) : Prop :=
  ∃ U : Set (ι → ℝ), IsOpen U ∧ Convexity.StdSimplex.coordinateSet ℝ ι ⊆ U ∧ ContDiffOn ℝ N f U

/-- Having more derivatives near the simplex implies having any smaller number of derivatives
there. -/
theorem ContDiffNearStdSimplex.of_le {N M : ℕ} (hNM : N ≤ M)
    {f : (ι → ℝ) → ℂ} (hf : ContDiffNearStdSimplex M f) :
    ContDiffNearStdSimplex N f := by
  obtain ⟨U, hU, hsub, hf⟩ := hf
  exact ⟨U, hU, hsub, hf.of_le (by exact_mod_cast hNM)⟩

/-- Finite differentiability on a neighborhood implies continuity on the closed simplex. -/
theorem ContDiffNearStdSimplex.continuousOn {N : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex N f) : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι) :=
      by
  obtain ⟨U, hU, hsub, hf⟩ := hf
  exact hf.continuousOn.mono hsub

/-! ### Tangential derivatives -/

open scoped Classical in
/-- The tangent vector to the simplex that increases coordinate `j` and decreases coordinate
`k` at the same rate. -/
def stdSimplexTangentVector (j k : ι) : ι → ℝ :=
  Pi.single j 1 - Pi.single k 1

/-- A simplex tangent vector has coordinate sum zero. -/
@[simp] theorem sum_stdSimplexTangentVector (j k : ι) :
    ∑ i, stdSimplexTangentVector j k i = 0 := by
  simp [stdSimplexTangentVector, Finset.sum_sub_distrib]

omit [Fintype ι] in
/-- Reversing a simplex tangent direction negates it. -/
theorem stdSimplexTangentVector_comm (j k : ι) :
    stdSimplexTangentVector k j = -stdSimplexTangentVector j k := by
  simp [stdSimplexTangentVector, sub_eq_add_neg]

omit [Fintype ι] in
/-- Transferring mass from a coordinate to itself gives the zero tangent vector. -/
@[simp] theorem stdSimplexTangentVector_self (j : ι) :
    stdSimplexTangentVector j j = 0 := by
  simp [stdSimplexTangentVector]

/-- The ambient directional derivative in the tangent direction that transfers mass from
coordinate `k` to coordinate `j`. Unlike a single coordinate derivative, this derivative is
intrinsic to the affine hyperplane containing the simplex. -/
def stdSimplexTangentDeriv (j k : ι) (f : (ι → ℝ) → ℂ) (u : ι → ℝ) : ℂ :=
  fderiv ℝ f u (stdSimplexTangentVector j k)

/-- Taking one tangential derivative consumes one order of differentiability near the
simplex. This is the differential operator used in the boundary integration-by-parts
recursion. -/
theorem ContDiffNearStdSimplex.tangentDeriv {N : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex (N + 1) f) (j k : ι) :
    ContDiffNearStdSimplex N (stdSimplexTangentDeriv j k f) := by
  obtain ⟨U, hU, hsub, hf⟩ := hf
  refine ⟨U, hU, hsub, ?_⟩
  unfold stdSimplexTangentDeriv
  apply ContDiffOn.clm_apply (hf.fderiv_of_isOpen hU ?_) contDiffOn_const
  norm_num

/-! ### Boundary faces -/

/-- Restriction of a function to the face where coordinate `i` is zero. The remaining
coordinates are indexed by `{j // j ≠ i}` and already sum to one on their standard simplex. -/
def stdSimplexFaceRestriction (i : ι) (f : (ι → ℝ) → ℂ) :
    ({j : ι // j ≠ i} → ℝ) → ℂ :=
  f ∘ stdSimplexCoordMap i

open scoped Classical in
/-- The coordinate map sends the smaller standard simplex onto the face where coordinate `i`
is zero. -/
theorem stdSimplexCoordMap_mem_face (i : ι)
    {v : {j : ι // j ≠ i} → ℝ} (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}) :
    stdSimplexCoordMap i v ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
  rw [stdSimplexCoordMap_mem_stdSimplex_iff]
  exact ⟨hv.1, hv.2.le⟩

open scoped Classical in
/-- On the smaller standard simplex, the inserted coordinate of the face map is zero. -/
theorem stdSimplexCoordMap_face_apply_self (i : ι)
    {v : {j : ι // j ≠ i} → ℝ} (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}) :
    stdSimplexCoordMap i v i = 0 := by
  rw [stdSimplexCoordMap_apply_self, hv.2]
  simp

open scoped Classical in
/-- Restricting to a boundary face preserves finite differentiability near the corresponding
lower-dimensional standard simplex. -/
theorem ContDiffNearStdSimplex.faceRestriction {N : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex N f) (i : ι) :
    ContDiffNearStdSimplex N (stdSimplexFaceRestriction i f) := by
  obtain ⟨U, hU, hsub, hf⟩ := hf
  let V : Set ({j : ι // j ≠ i} → ℝ) := stdSimplexCoordMap i ⁻¹' U
  have hcoord : ContDiff ℝ N (stdSimplexCoordMap (R := ℝ) i) := by
    rw [contDiff_pi]
    intro j
    by_cases hji : j = i
    · subst j
      simp_rw [stdSimplexCoordMap_apply_self]
      fun_prop
    · simp_rw [stdSimplexCoordMap_apply_of_ne i j hji]
      fun_prop
  refine ⟨V, hU.preimage (continuous_stdSimplexCoordMap i), ?_, ?_⟩
  · intro v hv
    exact hsub (stdSimplexCoordMap_mem_face i hv)
  · exact hf.comp hcoord.contDiffOn fun _ hv ↦ hv

/-! ### Slice parametrization -/

/-- The affine line from the face `u i = 0` to the vertex `e i`, parametrized so that the
omitted coordinate equals `t`. -/
def stdSimplexSlice (i : ι) (t : ℝ) (f : (ι → ℝ) → ℂ) :
    ({j : ι // j ≠ i} → ℝ) → ℂ :=
  fun v => f (stdSimplexCoordMap i (fun j => (1 - t) * v j))

theorem stdSimplexSlice_zero (i : ι) (f : (ι → ℝ) → ℂ) :
    stdSimplexSlice i 0 f = stdSimplexFaceRestriction i f := by
  funext v
  simp [stdSimplexSlice, stdSimplexFaceRestriction]

open scoped Classical in
/-- On the standard simplex of the complementary coordinates, the scaled chart is the line
from the face point to the vertex `Pi.single i 1`. -/
theorem stdSimplexCoordMap_scale_eq_line (i : ι) (t : ℝ)
    {v : {j : ι // j ≠ i} → ℝ} (hv : ∑ j, v j = 1) :
    stdSimplexCoordMap i (fun j => (1 - t) * v j) =
      (t : ℝ) • Pi.single i (1 : ℝ) + (1 - t) • stdSimplexCoordMap i v := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [stdSimplexCoordMap_apply_self, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_same, stdSimplexCoordMap_apply_self]
    rw [← Finset.mul_sum, hv, mul_one]
    simp
  · rw [stdSimplexCoordMap_apply_of_ne i j hji, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hji, stdSimplexCoordMap_apply_of_ne i j hji]
    simp

open scoped Classical in
theorem hasDerivAt_stdSimplexCoordMap_scale (i : ι) (t : ℝ)
    {v : {j : ι // j ≠ i} → ℝ} (hv : ∑ j, v j = 1) :
    HasDerivAt (fun s : ℝ => stdSimplexCoordMap i (fun j => (1 - s) * v j))
      (Pi.single i (1 : ℝ) - stdSimplexCoordMap i v) t := by
  have heq :
      (fun s : ℝ => stdSimplexCoordMap i (fun j => (1 - s) * v j)) =
        fun s => (s : ℝ) • Pi.single i (1 : ℝ) + (1 - s) • stdSimplexCoordMap i v :=
    funext fun s => stdSimplexCoordMap_scale_eq_line i s hv
  rw [heq]
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) t := by
    simpa using hid.const_sub (1 : ℝ)
  have hderiv :
      (1 : ℝ) • Pi.single i (1 : ℝ) + (-1 : ℝ) • stdSimplexCoordMap i v =
        Pi.single i (1 : ℝ) - stdSimplexCoordMap i v := by
    simp [one_smul, sub_eq_add_neg]
  rw [← hderiv]
  exact (hid.smul_const _).add (h1.smul_const _)

open scoped Classical in
/-- Finite differentiability near the simplex is inherited by every slice. -/
theorem ContDiffNearStdSimplex.slice {N : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex N f) (i : ι)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffNearStdSimplex N (stdSimplexSlice i t f) := by
  obtain ⟨U, hU, hsub, hfU⟩ := hf
  let V : Set ({j : ι // j ≠ i} → ℝ) :=
    (fun v => stdSimplexCoordMap i (fun j => (1 - t) * v j)) ⁻¹' U
  have hmap : ContDiff ℝ N
      (fun v : {j : ι // j ≠ i} → ℝ =>
        stdSimplexCoordMap i (fun j => (1 - t) * v j)) := by
    rw [contDiff_pi]
    intro j
    by_cases hji : j = i
    · subst j
      simp_rw [stdSimplexCoordMap_apply_self]
      fun_prop
    · simp_rw [stdSimplexCoordMap_apply_of_ne i j hji]
      fun_prop
  refine ⟨V, hU.preimage (hmap.continuous), ?_, ?_⟩
  · intro v hv
    have : stdSimplexCoordMap i (fun j => (1 - t) * v j) ∈ Convexity.StdSimplex.coordinateSet ℝ ι
      := by
      rw [stdSimplexCoordMap_mem_stdSimplex_iff]
      refine ⟨fun j => mul_nonneg (sub_nonneg.mpr ht.2) (hv.1 j), ?_⟩
      rw [← Finset.mul_sum, hv.2, mul_one]
      exact sub_le_self _ ht.1
    exact hsub this
  · exact hfU.comp hmap.contDiffOn fun _ hv ↦ hv

open scoped Classical in
/-- Affine slices of a continuous simplex function remain continuous on the opposite face. -/
theorem continuousOn_stdSimplexSlice (i : ι) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {f : (ι → ℝ) → ℂ} (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    ContinuousOn (stdSimplexSlice i t f) (Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i})
      := by
  have hmap : Continuous
      (fun v : {j : ι // j ≠ i} → ℝ =>
        stdSimplexCoordMap i (fun q => (1 - t) * v q)) := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simp_rw [stdSimplexCoordMap_apply_self]
      fun_prop
    · simp_rw [stdSimplexCoordMap_apply_of_ne i j hji]
      fun_prop
  refine hf.comp hmap.continuousOn fun v hv => ?_
  rw [stdSimplexCoordMap_mem_stdSimplex_iff]
  refine ⟨fun j => mul_nonneg (sub_nonneg.mpr ht.2) (hv.1 j), ?_⟩
  rw [← Finset.mul_sum, hv.2, mul_one]
  exact sub_le_self _ ht.1

/-- The identity `1 = ∑ i, u i ^ M / powerPartitionDenom M u` lets each term reserve
enough powers of its omitted coordinate for all the subsequent parameter shifts. -/
def powerPartitionDenom (M : ℕ) (u : ι → ℝ) : ℂ :=
  ∑ j, (u j : ℂ) ^ M

theorem powerPartitionDenom_ne_zero (M : ℕ) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) : powerPartitionDenom M u ≠ 0 := by
  have hex : ∃ j, 0 < u j := by
    by_contra hn
    push Not at hn
    have hz : ∀ j, u j = 0 := fun j => le_antisymm (hn j) (hu.1 j)
    have hs := hu.2
    simp [hz] at hs
  obtain ⟨j, hj⟩ := hex
  have hs : 0 < ∑ k, u k ^ M :=
    Finset.sum_pos' (fun k _ => pow_nonneg (hu.1 k) M)
      ⟨j, Finset.mem_univ j, pow_pos hj M⟩
  have heq : powerPartitionDenom M u = ((∑ k, u k ^ M : ℝ) : ℂ) := by
    simp [powerPartitionDenom]
  rw [heq]
  exact ofReal_ne_zero.mpr hs.ne'

theorem contDiffNear_div_powerPartitionDenom {n : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiffNearStdSimplex n f) (M : ℕ) :
    ContDiffNearStdSimplex n (fun u => f u / powerPartitionDenom M u) := by
  obtain ⟨U, hU, hsub, hfU⟩ := hf
  have hd : ContDiff ℝ n (powerPartitionDenom (ι := ι) M) := by
    unfold powerPartitionDenom
    exact ContDiff.sum fun j _ =>
      (Complex.ofRealCLM.contDiff.comp
        (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).contDiff).pow M
  let V := U ∩ {u | powerPartitionDenom M u ≠ 0}
  refine ⟨V, hU.inter (isOpen_ne_fun hd.continuous continuous_const), ?_, ?_⟩
  · exact fun u hu => ⟨hsub hu, powerPartitionDenom_ne_zero M hu⟩
  · simpa only [div_eq_mul_inv] using!
      (hfU.mono (show V ⊆ U from inter_subset_left)).mul
        (hd.contDiffOn.inv (fun u (hu : u ∈ V) => hu.2))

theorem isClosed_stdSimplexFreeCoords (i : ι) :
    IsClosed (stdSimplexFreeCoords (R := ℝ) i) := by
  have heq : stdSimplexFreeCoords (R := ℝ) i =
      stdSimplexCoordMap i ⁻¹' Convexity.StdSimplex.coordinateSet ℝ ι := by
    ext x
    exact (stdSimplexCoordMap_mem_stdSimplex_iff i x).symm
  rw [heq]
  exact (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).preimage (continuous_stdSimplexCoordMap i)

open scoped Classical in
theorem stdSimplexCoordMap_add_single (i : ι) (j : {j : ι // j ≠ i})
    (x : {j : ι // j ≠ i} → ℝ) (t : ℝ) :
    stdSimplexCoordMap i (x + t • Pi.single j 1) =
      stdSimplexCoordMap i x + t • (Pi.single (j : ι) 1 - Pi.single i 1) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [Finset.sum_add_distrib, Pi.single_eq_of_ne j.property.symm,
      ← Finset.mul_sum]
    ring
  · simp only [stdSimplexCoordMap_apply_of_ne i k hki,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne hki]
    by_cases hkj : k = j
    · subst k; simp
    · have hsub : (⟨k, hki⟩ : {k : ι // k ≠ i}) ≠ j :=
        fun h => hkj (congrArg Subtype.val h)
      simp [Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hsub]

end DirichletTransform

end
