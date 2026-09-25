/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import Mathlib.Tactic
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrderComplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CanonicalConfiguration
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.Model
/-!
# Topological realization of the Fox--Neuwirth order complex

This file constructs the topological realization of the order complex.  The global carrier
introduced in `OrderComplex` is a closed subspace of the finite standard simplex: the additional
chain-support condition is a finite intersection of unions of coordinate hyperplanes.  Hence the
carrier is compact.

Relabelling acts by permuting barycentric coordinates.  The configuration map is the barycentric
average of the canonical configurations attached to the barred-permutation vertices.  Its
collision-freeness is proved directly from the face order.  For a realization point, choose a
nonzero support cell of minimum dual dimension.  That cell is a face of every other support cell.
If two labels are in different blocks there, their first-coordinate order persists weakly and is
strict at the chosen cell.  If they are in the same block, their common block persists and their
rank order persists strictly.  The barycentric average therefore cannot identify the labels.
-/

@[expose] public section

namespace NRR

open scoped BigOperators

variable {p : Nat}

namespace FoxNeuwirthOrderComplex

/-- Relabelling is an equivalence of the finite barred-permutation vertex set. -/
def relabelEquiv (sigma : Equiv.Perm (Fin p)) :
    BarredPermutation p ≃ BarredPermutation p where
  toFun c := c.relabel sigma
  invFun c := c.relabel sigma.symm
  left_inv c := by
    calc
      (c.relabel sigma).relabel sigma.symm = c.relabel (sigma.symm * sigma) :=
        (BarredPermutation.relabel_mul sigma.symm sigma c).symm
      _ = c.relabel 1 := by
        congr 1
        apply Equiv.ext
        intro i
        exact sigma.symm_apply_apply i
      _ = c := BarredPermutation.relabel_one c
  right_inv c := by
    calc
      (c.relabel sigma.symm).relabel sigma = c.relabel (sigma * sigma.symm) :=
        (BarredPermutation.relabel_mul sigma sigma.symm c).symm
      _ = c.relabel 1 := by
        congr 1
        apply Equiv.ext
        intro i
        exact sigma.apply_symm_apply i
      _ = c := BarredPermutation.relabel_one c

@[simp] theorem relabelEquiv_apply
    (sigma : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    relabelEquiv sigma c = c.relabel sigma :=
  rfl

@[simp] theorem relabel_symm_relabel
    (sigma : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    (c.relabel sigma).relabel sigma.symm = c := by
  exact (relabelEquiv sigma).left_inv c

@[simp] theorem relabel_relabel_symm
    (sigma : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    (c.relabel sigma.symm).relabel sigma = c := by
  exact (relabelEquiv sigma).right_inv c

/-- Two vertices may simultaneously occur in a simplex exactly when they are equal or properly
comparable. -/
def PairCompatible (a b : BarredPermutation p) : Prop :=
  a = b ∨ ProperFace a b ∨ ProperFace b a

noncomputable instance pairCompatibleDecidable (a b : BarredPermutation p) :
    Decidable (PairCompatible a b) :=
  Classical.propDecidable _

/-- Closed coordinate condition attached to a pair of vertices.  For an incompatible pair, at
least one of the two barycentric coordinates must vanish. -/
def pairConstraint (a b : BarredPermutation p) :
    Set (BarredPermutation p → Real) :=
  {weight | PairCompatible a b ∨ weight a = 0 ∨ weight b = 0}

/-- Every pair constraint is closed. -/
theorem isClosed_pairConstraint (a b : BarredPermutation p) :
    IsClosed (pairConstraint a b) := by
  by_cases h : PairCompatible a b
  · simp [pairConstraint, h]
  · have ha : IsClosed {weight : BarredPermutation p → Real | weight a = 0} :=
      isClosed_eq (continuous_apply a) continuous_const
    have hb : IsClosed {weight : BarredPermutation p → Real | weight b = 0} :=
      isClosed_eq (continuous_apply b) continuous_const
    have heq : pairConstraint a b =
        {weight : BarredPermutation p → Real | weight a = 0} ∪
          {weight : BarredPermutation p → Real | weight b = 0} := by
      ext weight
      simp [pairConstraint, h]
    rw [heq]
    exact ha.union hb

/-- Chain support is precisely the intersection of all pair constraints. -/
theorem chainSupported_set_eq :
    {weight : BarredPermutation p → Real | ChainSupported weight} =
      ⋂ a, ⋂ b, pairConstraint a b := by
  ext weight
  constructor
  · intro h
    simp only [Set.mem_iInter]
    intro a b
    change PairCompatible a b ∨ weight a = 0 ∨ weight b = 0
    by_cases ha : weight a = 0
    · exact Or.inr (Or.inl ha)
    by_cases hb : weight b = 0
    · exact Or.inr (Or.inr hb)
    by_cases hab : a = b
    · exact Or.inl (Or.inl hab)
    rcases h ha hb hab with hface | hface
    · exact Or.inl (Or.inr (Or.inl hface))
    · exact Or.inl (Or.inr (Or.inr hface))
  · intro h a b ha hb hab
    have hp := Set.mem_iInter.mp (Set.mem_iInter.mp h a) b
    change PairCompatible a b ∨ weight a = 0 ∨ weight b = 0 at hp
    rcases hp with hcompat | hzeroa | hzerob
    · rcases hcompat with hab' | hface | hface
      · exact (hab hab').elim
      · exact Or.inl hface
      · exact Or.inr hface
    · exact (ha hzeroa).elim
    · exact (hb hzerob).elim

/-- The chain-support condition is closed in the finite coordinate space. -/
theorem isClosed_chainSupported :
    IsClosed {weight : BarredPermutation p → Real | ChainSupported weight} := by
  rw [chainSupported_set_eq]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_pairConstraint a b

/-- The underlying predicate of the realization is the intersection of the standard simplex with
its closed chain-support locus. -/
theorem realization_carrier_eq :
    {weight : BarredPermutation p → Real |
        (∀ c, 0 ≤ weight c) ∧
        (∑ c, weight c = 1) ∧
        ChainSupported weight} =
      SphereOddDegree.finiteSimplex Real (BarredPermutation p) ∩
        {weight | ChainSupported weight} := by
  ext weight
  change
    ((∀ c, 0 ≤ weight c) ∧ (∑ c, weight c = 1) ∧ ChainSupported weight) ↔
      (((∀ c, 0 ≤ weight c) ∧ (∑ c, weight c = 1)) ∧ ChainSupported weight)
  tauto

/-- Compactness of the global barycentric carrier. -/
theorem isCompact_realizationCarrier :
    IsCompact {weight : BarredPermutation p → Real |
      (∀ c, 0 ≤ weight c) ∧
      (∑ c, weight c = 1) ∧
      ChainSupported weight} := by
  rw [realization_carrier_eq]
  have hsimplex : IsCompact (SphereOddDegree.finiteSimplex Real (BarredPermutation p)) :=
    SphereOddDegree.isCompact_finiteSimplex ℝ (BarredPermutation p)
  exact hsimplex.inter_right isClosed_chainSupported

namespace Realization

noncomputable instance instMetricSpace : MetricSpace (Realization p) :=
  MetricSpace.induced Subtype.val Subtype.val_injective inferInstance

instance instNonempty : Nonempty (Realization p) :=
  ⟨vertex ⟨1, ∅⟩⟩

/-- The order-complex realization is compact. -/
noncomputable instance instCompactSpace : CompactSpace (Realization p) :=
  isCompact_iff_compactSpace.mp isCompact_realizationCarrier

/-- The coordinate permutation induced by relabelling. -/
def relabel (sigma : Equiv.Perm (Fin p)) (x : Realization p) : Realization p :=
  ⟨fun c => x (c.relabel sigma.symm), by
    refine ⟨?_, ?_, ?_⟩
    · intro c
      exact x.nonneg (c.relabel sigma.symm)
    · calc
        (∑ c : BarredPermutation p, x (c.relabel sigma.symm)) = ∑ c, x c := by
          simpa using (relabelEquiv sigma.symm).sum_comp (fun c => x c)
        _ = 1 := x.sum_eq_one
    · intro a b ha hb hab
      have hcomp := x.chainSupported ha hb (by
        intro h
        apply hab
        simpa using congrArg (fun c => c.relabel sigma) h)
      rcases hcomp with hface | hface
      · exact Or.inl <| by
          have := (properFace_relabel_iff sigma
            (a.relabel sigma.symm) (b.relabel sigma.symm)).2 hface
          simpa using this
      · exact Or.inr <| by
          have := (properFace_relabel_iff sigma
            (b.relabel sigma.symm) (a.relabel sigma.symm)).2 hface
          simpa using this⟩

@[simp] theorem relabel_apply
    (sigma : Equiv.Perm (Fin p)) (x : Realization p)
    (c : BarredPermutation p) :
    relabel sigma x c = x (c.relabel sigma.symm) :=
  rfl

@[simp] theorem relabel_one (x : Realization p) :
    relabel 1 x = x := by
  ext c
  change x (c.relabel (1 : Equiv.Perm (Fin p)).symm) = x c
  rw [show (1 : Equiv.Perm (Fin p)).symm = 1 by
    apply Equiv.ext
    intro i
    exact (1 : Equiv.Perm (Fin p)).symm_apply_apply i]
  rw [BarredPermutation.relabel_one]

/-- Coordinate relabelling is a left action. -/
theorem relabel_mul
    (sigma tau : Equiv.Perm (Fin p)) (x : Realization p) :
    relabel (sigma * tau) x = relabel sigma (relabel tau x) := by
  ext c
  simp only [relabel_apply]
  exact congrArg x (BarredPermutation.relabel_mul tau.symm sigma.symm c)

instance primeSymmetryAction (p : Nat) :
    MulAction (PrimeSymmetry p) (Realization p) where
  smul g x := relabel (PrimeSymmetry.toPerm p g) x
  one_smul x := relabel_one x
  mul_smul g h x := by
    exact relabel_mul (PrimeSymmetry.toPerm p g)
      (PrimeSymmetry.toPerm p h) x

@[simp] theorem prime_smul_apply
    (p : Nat) (g : PrimeSymmetry p)
    (x : Realization p) (c : BarredPermutation p) :
    (g • x) c = x (c.relabel (PrimeSymmetry.toPerm p g).symm) :=
  rfl

/-- Relabelling is continuous because it merely permutes finitely many coordinates. -/
theorem continuous_relabel (sigma : Equiv.Perm (Fin p)) :
    Continuous fun x : Realization p => relabel sigma x := by
  rw [continuous_induced_rng]
  exact continuous_pi fun c =>
    (continuous_apply (c.relabel sigma.symm)).comp continuous_subtype_val

/-- Every realization point has a nonempty coordinate support. -/
theorem support_nonempty (x : Realization p) :
    x.support.Nonempty := by
  by_contra h
  have hzero : ∀ c, x c = 0 := by
    intro c
    by_contra hc
    exact h ⟨c, (mem_support_iff x c).2 hc⟩
  have : (∑ c, x c) = 0 := by simp [hzero]
  linarith [x.sum_eq_one]

/-- A realization support has a cell that is a face of every other support cell. -/
theorem exists_minimal_support_cell (x : Realization p) :
    ∃ c, c ∈ x.support ∧
      ∀ d, d ∈ x.support → c.IsFace d := by
  classical
  obtain ⟨c, hc, hmin⟩ :=
    Finset.exists_min_image x.support BarredPermutation.dualDimension
      x.support_nonempty
  refine ⟨c, hc, ?_⟩
  intro d hd
  by_cases hcd : c = d
  · simpa [hcd] using BarredPermutation.isFace_refl c
  have hc0 : x c ≠ 0 := (mem_support_iff x c).1 hc
  have hd0 : x d ≠ 0 := (mem_support_iff x d).1 hd
  rcases x.chainSupported hc0 hd0 hcd with hface | hface
  · exact hface.1
  · have hle := hmin d hd
    exact (not_lt_of_ge hle hface.2).elim

/-- First coordinate of the barycentric configuration point. -/
noncomputable def xCoord (x : Realization p) (i : Fin p) : Real :=
  ∑ c, x c * (c.blockIndex i : Real)

/-- Second coordinate of the barycentric configuration point. -/
noncomputable def yCoord (x : Realization p) (i : Fin p) : Real :=
  ∑ c, x c * ((c.rank i).1 : Real)

/-- Barycentric average of the canonical vertex configurations. -/
noncomputable def site (x : Realization p) (i : Fin p) : E2 :=
  !₂[x.xCoord i, x.yCoord i]

@[simp] theorem site_x (x : Realization p) (i : Fin p) :
    x.site i 0 = x.xCoord i := by
  simp [site]

@[simp] theorem site_y (x : Realization p) (i : Fin p) :
    x.site i 1 = x.yCoord i := by
  simp [site]

/-- A minimal support cell forces strict first-coordinate order whenever two labels lie in
separate blocks there. -/
theorem xCoord_lt_of_minimal_block_lt
    (x : Realization p) (c : BarredPermutation p)
    (hc : c ∈ x.support)
    (hface : ∀ d, d ∈ x.support → c.IsFace d)
    {i j : Fin p} (hij : c.blockIndex i < c.blockIndex j) :
    x.xCoord i < x.xCoord j := by
  classical
  unfold xCoord
  apply Finset.sum_lt_sum
  · intro d hd
    by_cases hxd : x d = 0
    · simp [hxd]
    · have hds : d ∈ x.support := (mem_support_iff x d).2 hxd
      have hle := (hface d hds).1 i j (Nat.le_of_lt hij)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (x.nonneg d)
  · refine ⟨c, Finset.mem_univ c, ?_⟩
    have hxc0 : x c ≠ 0 := (mem_support_iff x c).1 hc
    have hxc : 0 < x c := lt_of_le_of_ne (x.nonneg c) (Ne.symm hxc0)
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hxc

/-- A minimal support cell forces equality of first coordinates whenever the labels lie in one
block there. -/
theorem xCoord_eq_of_minimal_sameBlock
    (x : Realization p) (c : BarredPermutation p)
    (hface : ∀ d, d ∈ x.support → c.IsFace d)
    {i j : Fin p} (hij : c.SameBlock i j) :
    x.xCoord i = x.xCoord j := by
  classical
  unfold xCoord
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hxd : x d = 0
  · simp [hxd]
  · have hds : d ∈ x.support := (mem_support_iff x d).2 hxd
    have hf := hface d hds
    have hdij : d.SameBlock i j := by
      apply Nat.le_antisymm
      · exact hf.1 i j (Nat.le_of_eq hij)
      · exact hf.1 j i (Nat.le_of_eq hij.symm)
    rw [hdij]

/-- In a common minimal block, strict rank order persists through the whole support chain. -/
theorem yCoord_lt_of_minimal_rank_lt
    (x : Realization p) (c : BarredPermutation p)
    (hc : c ∈ x.support)
    (hface : ∀ d, d ∈ x.support → c.IsFace d)
    {i j : Fin p} (hblock : c.SameBlock i j)
    (hij : (c.rank i).1 < (c.rank j).1) :
    x.yCoord i < x.yCoord j := by
  classical
  unfold yCoord
  apply Finset.sum_lt_sum
  · intro d hd
    by_cases hxd : x d = 0
    · simp [hxd]
    · have hds : d ∈ x.support := (mem_support_iff x d).2 hxd
      have hlt := ((hface d hds).2.1 i j hblock).1 hij
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast (Nat.le_of_lt hlt)) (x.nonneg d)
  · refine ⟨c, Finset.mem_univ c, ?_⟩
    have hxc0 : x c ≠ 0 := (mem_support_iff x c).1 hc
    have hxc : 0 < x c := lt_of_le_of_ne (x.nonneg c) (Ne.symm hxc0)
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hxc

/-- The barycentric site family is collision-free. -/
theorem site_injective (x : Realization p) :
    Function.Injective x.site := by
  classical
  intro i j hsite
  by_contra hij
  obtain ⟨c, hc, hface⟩ := x.exists_minimal_support_cell
  rcases lt_trichotomy (c.blockIndex i) (c.blockIndex j) with hlt | heq | hgt
  · have hs : x.xCoord i < x.xCoord j :=
      x.xCoord_lt_of_minimal_block_lt c hc hface hlt
    have he : x.xCoord i = x.xCoord j := by
      simpa [site] using congrArg (fun q : E2 => q 0) hsite
    exact (ne_of_lt hs) he
  · have hblock : c.SameBlock i j := heq
    have hrank : c.rank i ≠ c.rank j := by
      intro hrank
      exact hij (c.rank.injective hrank)
    rcases lt_or_gt_of_ne hrank with hlt | hgt
    · have hs : x.yCoord i < x.yCoord j :=
        x.yCoord_lt_of_minimal_rank_lt c hc hface hblock hlt
      have he : x.yCoord i = x.yCoord j := by
        simpa [site] using congrArg (fun q : E2 => q 1) hsite
      exact (ne_of_lt hs) he
    · have hblock' : c.SameBlock j i := hblock.symm
      have hs : x.yCoord j < x.yCoord i :=
        x.yCoord_lt_of_minimal_rank_lt c hc hface hblock' hgt
      have he : x.yCoord j = x.yCoord i := by
        simpa [site] using congrArg (fun q : E2 => q 1) hsite.symm
      exact (ne_of_lt hs) he
  · have hs : x.xCoord j < x.xCoord i :=
      x.xCoord_lt_of_minimal_block_lt c hc hface hgt
    have he : x.xCoord j = x.xCoord i := by
      simpa [site] using congrArg (fun q : E2 => q 0) hsite.symm
    exact (ne_of_lt hs) he

/-- The order-complex realization maps to the labelled configuration space. -/
noncomputable def toConfig (x : Realization p) : Config p :=
  ⟨x.site, x.site_injective⟩

@[simp] theorem toConfig_pts (x : Realization p) (i : Fin p) :
    x.toConfig.pts i = x.site i :=
  rfl

/-- The first barycentric coordinate sum is continuous. -/
theorem continuous_xCoord (i : Fin p) :
    Continuous fun x : Realization p => x.xCoord i := by
  unfold xCoord
  exact continuous_finsetSum _ fun c _ =>
    ((continuous_apply c).comp continuous_subtype_val).mul continuous_const

/-- The second barycentric coordinate sum is continuous. -/
theorem continuous_yCoord (i : Fin p) :
    Continuous fun x : Realization p => x.yCoord i := by
  unfold yCoord
  exact continuous_finsetSum _ fun c _ =>
    ((continuous_apply c).comp continuous_subtype_val).mul continuous_const

/-- The barycentric site map is continuous. -/
theorem continuous_site :
    Continuous fun x : Realization p => x.site := by
  exact continuous_pi fun i => by
    change Continuous fun x : Realization p =>
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm !₂[x.xCoord i, x.yCoord i]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous.comp
    rw [continuous_pi_iff]
    intro j
    fin_cases j
    · exact continuous_xCoord (p := p) i
    · exact continuous_yCoord (p := p) i

/-- The configuration map is continuous. -/
theorem continuous_toConfig :
    Continuous (toConfig : Realization p → Config p) := by
  rw [continuous_induced_rng]
  exact continuous_site

/-- Barycentric first coordinates transform by relabelling. -/
theorem xCoord_relabel
    (sigma : Equiv.Perm (Fin p)) (x : Realization p) (i : Fin p) :
    (relabel sigma x).xCoord i = x.xCoord (sigma.symm i) := by
  classical
  unfold xCoord
  simpa [relabel_apply] using
    (relabelEquiv sigma.symm).sum_comp
      (fun c => x c * (c.blockIndex (sigma.symm i) : Real))

/-- Barycentric second coordinates transform by relabelling. -/
theorem yCoord_relabel
    (sigma : Equiv.Perm (Fin p)) (x : Realization p) (i : Fin p) :
    (relabel sigma x).yCoord i = x.yCoord (sigma.symm i) := by
  classical
  unfold yCoord
  simpa [relabel_apply] using
    (relabelEquiv sigma.symm).sum_comp
      (fun c => x c * ((c.rank (sigma.symm i)).1 : Real))

/-- The barycentric site family is equivariant under all label permutations. -/
theorem site_relabel
    (sigma : Equiv.Perm (Fin p)) (x : Realization p) (i : Fin p) :
    (relabel sigma x).site i = x.site (sigma.symm i) := by
  ext j
  fin_cases j
  · simp [site, xCoord_relabel]
  · simp [site, yCoord_relabel]

/-- The configuration map is equivariant for the selected prime symmetry. -/
theorem toConfig_smul
    (p : Nat) (g : PrimeSymmetry p) (x : Realization p) :
    (g • x).toConfig = g • x.toConfig := by
  apply Subtype.ext
  funext i
  exact site_relabel (PrimeSymmetry.toPerm p g) x i

/-- Prime-symmetry actions on the realization are continuous. -/
theorem continuous_smul
    (p : Nat) (g : PrimeSymmetry p) :
    Continuous fun x : Realization p => g • x :=
  continuous_relabel (PrimeSymmetry.toPerm p g)

/-- The barycentric map agrees with the canonical configuration at every order-complex vertex. -/
theorem toConfig_vertex (c : BarredPermutation p) :
    toConfig (vertex c) = c.canonicalConfig := by
  apply Subtype.ext
  funext i
  ext j
  fin_cases j
  · change (vertex c).xCoord i = c.canonicalPoint i 0
    rw [BarredPermutation.canonicalPoint_x]
    simp [xCoord, vertex_apply]
  · change (vertex c).yCoord i = c.canonicalPoint i 1
    rw [BarredPermutation.canonicalPoint_y]
    simp [yCoord, vertex_apply]

/-- Reference vector obtained from the first coordinates of the barycentric configuration. -/
noncomputable def reference (hp : Nat.Prime p) (x : Realization p) : ZeroSum p :=
  coordinateDeviation hp.pos (fun i => x.xCoord i)

/-- The reference map is continuous. -/
theorem continuous_reference (hp : Nat.Prime p) :
    Continuous (reference hp : Realization p → ZeroSum p) := by
  exact (coordinateDeviation hp.pos).continuous_of_finiteDimensional.comp
    (continuous_pi fun i => continuous_xCoord (p := p) i)

/-- The reference vector is equivariant. -/
theorem reference_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p) (x : Realization p) :
    reference hp (g • x) = g • reference hp x := by
  unfold reference
  have hcoords :
      (fun i => (g • x).xCoord i) = g • (fun i => x.xCoord i) := by
    funext i
    exact xCoord_relabel (PrimeSymmetry.toPerm p g) x i
  rw [hcoords]
  exact coordinateDeviation_prime_smul hp (fun i => x.xCoord i) g

end Realization

/-- The compact equivariant prime configuration model carried by the glued order complex. -/
noncomputable def orderComplexModel (hp : Nat.Prime p) :
    PrimeConfigurationModel hp := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact
    { Point := Realization p
      continuous_smul := Realization.continuous_smul p
      toConfig := ⟨Realization.toConfig, Realization.continuous_toConfig⟩
      toConfig_equivariant := by
        intro g x
        exact Realization.toConfig_smul p g x
      reference := ⟨Realization.reference hp, Realization.continuous_reference hp⟩
      reference_equivariant := by
        intro g x
        exact Realization.reference_smul hp g x }

/-- The order-complex realization produces a compact equivariant configuration model. -/
theorem orderComplexModel_nonempty (hp : Nat.Prime p) :
    Nonempty (PrimeConfigurationModel hp) :=
  ⟨orderComplexModel hp⟩

end FoxNeuwirthOrderComplex

end NRR
