/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.Statement
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Global finiteness of the induced Riemannian distance

The Riemannian distance in pinned Mathlib is an extended distance, since it is
defined as an infimum over smooth path lengths.  On a connected boundaryless
finite-dimensional manifold it is nevertheless finite everywhere.  The proof
below uses only the local chart estimate already proved by Mathlib and the
topological connectedness argument; it does not assume geodesics or compactness.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

private lemma locallyPathConnectedSpace_model (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] :
    LocallyPathConnectedSpace H := by
  letI : LocallyPathConnectedSpace E := inferInstance
  exact I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace

include I
private lemma pathConnectedSpace_manifold : PathConnectedSpace M := by
  letI : LocallyPathConnectedSpace H := locallyPathConnectedSpace_model I
  letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  exact PathConnectedSpace.of_locallyPathConnectedSpace

section

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [IsManifold I 1 M]

variable (I) in
private lemma locallyFinite_riemannianEDist (x : M) :
    ∀ᶠ y in 𝓝 x, riemannianEDist I x y < (⊤ : ℝ≥0∞) := by
  exact eventually_riemannianEDist_lt I x (by simp)

private lemma finite_riemannianEDist_set_clopen (x : M) :
    IsClopen {y : M | riemannianEDist I x y < (⊤ : ℝ≥0∞)} := by
  let s : Set M := {y : M | riemannianEDist I x y < (⊤ : ℝ≥0∞)}
  have hopen : IsOpen s := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hlocal := locallyFinite_riemannianEDist (I := I) y
    have hxy : riemannianEDist I x y < (⊤ : ℝ≥0∞) := hy
    filter_upwards [hlocal] with z hz
    have htri := riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z)
    exact lt_of_le_of_lt htri (by
      exact (ENNReal.add_lt_top).2 ⟨hxy, hz⟩)
  have hclosed : IsClosed s := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyinf : riemannianEDist I x y = (⊤ : ℝ≥0∞) := by
      apply top_unique
      exact not_lt.mp hy
    have hlocal := locallyFinite_riemannianEDist (I := I) y
    filter_upwards [hlocal] with z hz
    intro hzfinite
    have htri := riemannianEDist_triangle (I := I) (x := x) (y := z) (z := y)
    have hzy : riemannianEDist I z y < (⊤ : ℝ≥0∞) := by
      rw [riemannianEDist_comm]
      exact hz
    have hxyfinite : riemannianEDist I x y < (⊤ : ℝ≥0∞) := by
      exact lt_of_le_of_lt htri (by
        exact (ENNReal.add_lt_top).2 ⟨hzfinite, hzy⟩)
    exact (not_lt_of_ge (le_of_eq hyinf.symm)) hxyfinite
  change IsClosed s ∧ IsOpen s
  exact ⟨hclosed, hopen⟩

theorem riemannianEDist_lt_top_of_connected (x y : M) :
    riemannianEDist I x y < (⊤ : ℝ≥0∞) := by
  letI : PathConnectedSpace M := pathConnectedSpace_manifold (I := I)
  have hclopen := finite_riemannianEDist_set_clopen (I := I) x
  have hnonempty : ({z : M | riemannianEDist I x z < (⊤ : ℝ≥0∞)} : Set M).Nonempty :=
    ⟨x, by simp [riemannianEDist_self]⟩
  have heq : {z : M | riemannianEDist I x z < (⊤ : ℝ≥0∞)} = Set.univ := by
    apply hclopen.eq_univ
    exact hnonempty
  have : y ∈ {z : M | riemannianEDist I x z < (⊤ : ℝ≥0∞)} := by
    rw [heq]
    simp
  exact this

theorem exists_smooth_path_length_lt_add (x y : M) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Icc (0 : ℝ) 1] 1 γ ∧
      pathELength I γ 0 1 < riemannianEDist I x y + ε := by
  have hd : riemannianEDist I x y < (⊤ : ℝ≥0∞) :=
    riemannianEDist_lt_top_of_connected (I := I) x y
  have hlt : riemannianEDist I x y <
      riemannianEDist I x y + ε :=
    ENNReal.lt_add_right (ne_of_lt hd) hε.ne'
  exact exists_lt_of_riemannianEDist_lt (I := I) hlt

theorem edist_lt_top_of_connected
    [EMetricSpace M] [IsRiemannianManifold I M] (x y : M) :
    edist x y < (⊤ : ℝ≥0∞) := by
  rw [(inferInstance : IsRiemannianManifold I M).out]
  exact riemannianEDist_lt_top_of_connected (I := I) x y

end

end BonnetMyersEntry
