/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.CompactStrongConvergence
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.ResolventComparison

/-!
# The Trotter--Kato theorem

Let `S i` be a family of strongly continuous contraction semigroups on a Banach space, indexed
along a filter, and let `S'` be one more such semigroup.  Convergence of the semigroups and
convergence of their resolvents are equivalent:

* if the resolvents converge strongly at **one** positive shift `μ`, then the semigroups converge
  strongly, uniformly on every bounded interval of times
  (`tendstoUniformlyOn_operator_of_tendsto_resolvent`, `tendsto_operator_of_tendsto_resolvent`);
* conversely, if the orbits converge at every time, then the resolvents converge at every positive
  shift (`tendsto_resolvent_of_tendsto_operator`), by dominated convergence in the Laplace
  transform that defines the resolvent.

The first implication is proved on the range of the twofold resolvent `R'_μ ∘ R'_μ`, which is
dense (`denseRange_resolvent_resolvent`): there the comparison identity of
`Semigroup/ResolventComparison.lean` expresses the difference of the two orbits through the
difference of the two resolvents evaluated along a compact piece of one fixed orbit, where
equibounded strong convergence is uniform (`Semigroup/CompactStrongConvergence.lean`).  The
contraction bound then transports the conclusion from the dense set to the whole space, uniformly
in the time.

Main results: `denseRange_resolvent_resolvent`,
`tendstoUniformlyOn_operator_of_tendsto_resolvent`, `tendsto_operator_of_tendsto_resolvent`,
`tendsto_resolvent_of_tendsto_operator`, `tendsto_resolvent_of_tendsto_resolvent`.

The converse implication, and the transfer of resolvent convergence from one shift to every
shift that goes through it (`tendsto_resolvent_of_tendsto_resolvent`), read the limit under an
integral and therefore assume the index filter countably generated; the direct implication
assumes nothing about the filter.  This is the same-space Trotter--Kato theorem; the version for
semigroups on a sequence of different spaces (Trotter--Kurtz) is not stated.  Nothing is asserted
about convergence in the operator norm, nor about families that are merely uniformly bounded
rather than contractive.
-/

noncomputable section PortComputability

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} {l : Filter ι}

/-- **The twofold resolvent has dense range.**  The range of `R_μ` is dense and `R_μ` is
continuous, so the range of `R_μ ∘ R_μ` is dense as well. -/
theorem denseRange_resolvent_resolvent (S : StronglyContinuousContractionSemigroup E)
    (μ : PositiveShift) : DenseRange fun z ↦ S.resolvent μ (S.resolvent μ z) :=
  (S.denseRange_resolvent μ).comp (S.denseRange_resolvent μ) (S.resolvent μ).continuous

omit [CompleteSpace E] in
/-- Uniform convergence of the orbits on a bounded interval of times extends from a dense set of
vectors to every vector, by the contraction bound. -/
private theorem tendstoUniformlyOn_of_dense
    {S : ι → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {b : NNReal} {D : Set E} (hD : Dense D)
    (hgood : ∀ y ∈ D, TendstoUniformlyOn (fun i (t : NNReal) ↦ (S i) t y)
      (fun t ↦ S' t y) l (Set.Iic b)) (x : E) :
    TendstoUniformlyOn (fun i (t : NNReal) ↦ (S i) t x) (fun t ↦ S' t x) l (Set.Iic b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨y, hyD, hxy⟩ := Metric.mem_closure_iff.mp (hD x) (ε / 3) (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hgood y hyD) (ε / 3) (by positivity)]
    with i hi t ht
  have hyx : dist y x < ε / 3 := by rwa [dist_comm] at hxy
  calc
    dist (S' t x) ((S i) t x) ≤
        dist (S' t x) (S' t y) + dist (S' t y) ((S i) t y) + dist ((S i) t y) ((S i) t x) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 :=
      add_lt_add (add_lt_add (lt_of_le_of_lt (S'.dist_apply_le t x y) hxy) (hi t ht))
        (lt_of_le_of_lt ((S i).dist_apply_le t y x) hyx)
    _ = ε := by ring

/-- On the range of the twofold resolvent of the limit semigroup, strong convergence of the
resolvents forces uniform convergence of the orbits on a bounded interval of times. -/
private theorem tendstoUniformlyOn_resolvent_resolvent
    {S : ι → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {μ : PositiveShift}
    (hres : ∀ y : E, Tendsto (fun i ↦ (S i).resolvent μ y) l (𝓝 (S'.resolvent μ y)))
    (z : E) (b : NNReal) :
    TendstoUniformlyOn (fun i (t : NNReal) ↦ (S i) t (S'.resolvent μ (S'.resolvent μ z)))
      (fun t ↦ S' t (S'.resolvent μ (S'.resolvent μ z))) l (Set.Iic b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set ε₁ : ℝ := ε / (3 * ((b : ℝ) + 1)) with hε₁def
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; positivity
  have key : (b : ℝ) * ε₁ + ε₁ = ε / 3 := by
    rw [hε₁def]
    field_simp
  have hDbound : ∀ i, ‖(S i).resolvent μ - S'.resolvent μ‖ ≤ 2 * (μ : ℝ)⁻¹ := by
    intro i
    calc
      ‖(S i).resolvent μ - S'.resolvent μ‖ ≤ ‖(S i).resolvent μ‖ + ‖S'.resolvent μ‖ :=
        norm_sub_le _ _
      _ ≤ (μ : ℝ)⁻¹ + (μ : ℝ)⁻¹ :=
        add_le_add ((S i).opNorm_resolvent_le μ) (S'.opNorm_resolvent_le μ)
      _ = 2 * (μ : ℝ)⁻¹ := by ring
  have hDzero : ∀ y : E, Tendsto (fun i ↦ ((S i).resolvent μ - S'.resolvent μ) y) l (𝓝 0) := by
    intro y
    simp only [sub_apply]
    simpa using (hres y).sub (tendsto_const_nhds (x := S'.resolvent μ y))
  have hK₁ : IsCompact ((fun u : ℝ ↦ S' (Real.toNNReal u) z) '' Set.Icc (0 : ℝ) (b : ℝ)) :=
    isCompact_Icc.image (S'.continuous_operator_toNNReal z)
  have hK₂ : IsCompact
      ((fun u : ℝ ↦ S' (Real.toNNReal u) (S'.resolvent μ z)) '' Set.Icc (0 : ℝ) (b : ℝ)) :=
    isCompact_Icc.image (S'.continuous_operator_toNNReal (S'.resolvent μ z))
  have h1 := eventually_forall_mem_norm_apply_le_of_isCompact
    (fun i ↦ (S i).resolvent μ - S'.resolvent μ) hDbound hDzero hK₁ hε₁
  have h2 := eventually_forall_mem_norm_apply_le_of_isCompact
    (fun i ↦ (S i).resolvent μ - S'.resolvent μ) hDbound hDzero hK₂ hε₁
  have h3 : ∀ᶠ i in l, ‖(S i).resolvent μ (S'.resolvent μ z) -
      S'.resolvent μ (S'.resolvent μ z)‖ < ε / 3 := by
    have h := NormedAddGroup.tendsto_nhds_zero.mp (hDzero (S'.resolvent μ z)) (ε / 3)
      (by positivity)
    simpa only [sub_apply] using h
  filter_upwards [h1, h2, h3] with i hi1 hi2 hi3 t ht
  have htb : (t : ℝ) ≤ (b : ℝ) := NNReal.coe_le_coe.mpr ht
  have hterm1 : ‖(S i) t (S'.resolvent μ (S'.resolvent μ z)) -
      (S i) t ((S i).resolvent μ (S'.resolvent μ z))‖ < ε / 3 := by
    have hle := (S i).norm_apply_le t
      (S'.resolvent μ (S'.resolvent μ z) - (S i).resolvent μ (S'.resolvent μ z))
    rw [map_sub] at hle
    refine lt_of_le_of_lt hle ?_
    rwa [norm_sub_rev]
  have hterm2 : ‖(S i) t ((S i).resolvent μ (S'.resolvent μ z)) -
      (S i).resolvent μ (S' t (S'.resolvent μ z))‖ ≤ (t : ℝ) * ε₁ := by
    refine norm_operator_resolvent_sub_resolvent_operator_le (S i) S' μ t z ?_
    intro u hu
    have hmem : S' (Real.toNNReal u) z ∈
        (fun u : ℝ ↦ S' (Real.toNNReal u) z) '' Set.Icc (0 : ℝ) (b : ℝ) :=
      ⟨u, ⟨hu.1, hu.2.trans htb⟩, rfl⟩
    simpa only [sub_apply] using hi1 _ hmem
  have hterm3 : ‖(S i).resolvent μ (S' t (S'.resolvent μ z)) -
      S' t (S'.resolvent μ (S'.resolvent μ z))‖ ≤ ε₁ := by
    rw [S'.operator_resolvent μ t (S'.resolvent μ z)]
    have hmem : S' t (S'.resolvent μ z) ∈
        (fun u : ℝ ↦ S' (Real.toNNReal u) (S'.resolvent μ z)) '' Set.Icc (0 : ℝ) (b : ℝ) :=
      ⟨(t : ℝ), ⟨t.coe_nonneg, htb⟩, by simp only [Real.toNNReal_coe]⟩
    simpa only [sub_apply] using hi2 _ hmem
  have htri : ‖(S i) t (S'.resolvent μ (S'.resolvent μ z)) -
      S' t (S'.resolvent μ (S'.resolvent μ z))‖ ≤
      ‖(S i) t (S'.resolvent μ (S'.resolvent μ z)) -
          (S i) t ((S i).resolvent μ (S'.resolvent μ z))‖ +
        ‖(S i) t ((S i).resolvent μ (S'.resolvent μ z)) -
          (S i).resolvent μ (S' t (S'.resolvent μ z))‖ +
        ‖(S i).resolvent μ (S' t (S'.resolvent μ z)) -
          S' t (S'.resolvent μ (S'.resolvent μ z))‖ := by
    simpa only [dist_eq_norm] using
      dist_triangle4 ((S i) t (S'.resolvent μ (S'.resolvent μ z)))
        ((S i) t ((S i).resolvent μ (S'.resolvent μ z)))
        ((S i).resolvent μ (S' t (S'.resolvent μ z)))
        (S' t (S'.resolvent μ (S'.resolvent μ z)))
  have hsplit : (t : ℝ) * ε₁ + ε₁ ≤ ε / 3 := by
    have hmul := mul_le_mul_of_nonneg_right htb hε₁.le
    linarith [key]
  rw [dist_eq_norm, norm_sub_rev]
  linarith [hterm1, hterm2, hterm3, htri]

/-- **The Trotter--Kato theorem.**  If the resolvents of the semigroups `S i` converge strongly to
the resolvent of `S'` at one positive shift, then the orbits converge uniformly on every bounded
interval of times. -/
theorem tendstoUniformlyOn_operator_of_tendsto_resolvent
    {S : ι → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {μ : PositiveShift}
    (hres : ∀ y : E, Tendsto (fun i ↦ (S i).resolvent μ y) l (𝓝 (S'.resolvent μ y)))
    (x : E) (b : NNReal) :
    TendstoUniformlyOn (fun i (t : NNReal) ↦ (S i) t x) (fun t ↦ S' t x) l (Set.Iic b) := by
  refine tendstoUniformlyOn_of_dense (S := S) (S' := S') (b := b)
    (D := Set.range fun z ↦ S'.resolvent μ (S'.resolvent μ z))
    (S'.denseRange_resolvent_resolvent μ) ?_ x
  rintro _ ⟨z, rfl⟩
  exact tendstoUniformlyOn_resolvent_resolvent hres z b

/-- **Strong convergence of the semigroups from strong convergence of the resolvents.** -/
theorem tendsto_operator_of_tendsto_resolvent
    {S : ι → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {μ : PositiveShift}
    (hres : ∀ y : E, Tendsto (fun i ↦ (S i).resolvent μ y) l (𝓝 (S'.resolvent μ y)))
    (x : E) (t : NNReal) : Tendsto (fun i ↦ (S i) t x) l (𝓝 (S' t x)) :=
  (tendstoUniformlyOn_operator_of_tendsto_resolvent hres x t).tendsto_at (Set.mem_Iic.2 le_rfl)

omit [CompleteSpace E] in
/-- **Strong convergence of the resolvents from strong convergence of the semigroups**, by
dominated convergence in the Laplace transform of the orbit. -/
theorem tendsto_resolvent_of_tendsto_operator [l.IsCountablyGenerated]
    {S : ι → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {x : E}
    (hop : ∀ t : NNReal, Tendsto (fun i ↦ (S i) t x) l (𝓝 (S' t x))) (μ : PositiveShift) :
    Tendsto (fun i ↦ (S i).resolvent μ x) l (𝓝 (S'.resolvent μ x)) := by
  simp only [resolvent_apply]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s : ℝ ↦ Real.exp (-(μ : ℝ) * s) * ‖x‖)
    (Eventually.of_forall fun i ↦
      ((S i).continuous_laplaceIntegrand μ x).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun i ↦ Eventually.of_forall fun s ↦
      (S i).norm_laplaceIntegrand_le (μ : ℝ) x s)
    ((exp_neg_integrableOn_Ioi 0 μ.2).mul_const ‖x‖) (Eventually.of_forall fun s ↦ ?_)
  simp only [laplaceIntegrand_apply]
  exact (hop (Real.toNNReal s)).const_smul (Real.exp (-(μ : ℝ) * s))

/-- Strong convergence of the resolvents at one positive shift propagates to every positive
shift. -/
theorem tendsto_resolvent_of_tendsto_resolvent [l.IsCountablyGenerated]
    {S : ι → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {μ : PositiveShift}
    (hres : ∀ y : E, Tendsto (fun i ↦ (S i).resolvent μ y) l (𝓝 (S'.resolvent μ y)))
    (ν : PositiveShift) (x : E) :
    Tendsto (fun i ↦ (S i).resolvent ν x) l (𝓝 (S'.resolvent ν x)) :=
  tendsto_resolvent_of_tendsto_operator
    (fun t ↦ tendsto_operator_of_tendsto_resolvent hres x t) ν

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

end PortComputability
