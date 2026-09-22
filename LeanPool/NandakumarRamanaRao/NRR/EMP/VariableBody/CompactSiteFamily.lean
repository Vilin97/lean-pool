/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Phase1Interface

/-!
# `NRR.EMP.VariableBody.CompactSiteFamily` — uniform bounds and separation

For a compact metric parameter space `X` carrying a continuous configuration family
`sites : SiteFamily X n`, every site position is uniformly bounded, and any two distinct sites are
uniformly separated. We also record a radius bound for the fixed planar parent body `K`.

These uniform quantities are the geometric inputs to the later continuity arguments of the
variable-body power partition: they let one work inside a fixed ball and with a fixed minimal gap,
independently of the parameter.
-/

open NRR NRR.Geometry

namespace NRR.EMP.VariableBody

variable {X : Type*} [MetricSpace X] [CompactSpace X] {n : ℕ}

/-- **Uniform site radius.** Over a compact parameter space, every labelled site of a continuous
configuration family stays inside a common ball; no assumption `0 < n` is needed. -/
theorem exists_siteRadius
    (sites : SiteFamily X n) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ x : X, ∀ i : Fin n, ‖(sites x).pts i‖ ≤ R := by
  -- By definition of `SiteFamily`, each `sites x` is a `Config n`, so we can apply the continuity
  -- of `Config.pts`.
  have h_cont_pts : ∀ i : Fin n, Continuous (fun x : X => ‖(sites x).pts i‖) := by
    intro i
    have h_cont : Continuous (fun x => (sites x).pts i) := by
      exact Continuous.comp ( continuous_apply i ) ( NRR.Config.continuous_pts.comp
        sites.continuous )
    exact h_cont.norm;
  exact ⟨ ∑ i, ( SupSet.sSup ( Set.range fun x => ‖ ( sites x |> Config.pts ) i‖ ) ),
    Finset.sum_nonneg fun _ _ => by
    apply_rules [ Real.sSup_nonneg ]; rintro - ⟨ x, rfl ⟩; positivity, fun x i => by
    exact le_trans ( by
      exact le_csSup ( by
        exact IsCompact.bddAbove ( isCompact_range ( h_cont_pts i ) ) ) ( Set.mem_range_self x )
          ) ( Finset.single_le_sum ( fun i _ => by
      exact ( show 0 ≤ SupSet.sSup ( Set.range fun x => ‖ ( sites x |> Config.pts ) i‖ ) from by
        apply_rules [ Real.sSup_nonneg ]; rintro - ⟨ x, rfl ⟩; positivity ) ) ( Finset.mem_univ
          i ) ) ⟩

/-- **Parent radius.** The fixed planar parent body, being compact, is contained in a ball. -/
theorem exists_parentRadius
    (K : Geometry.ConvexBody Plane) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ y ∈ (K : Set Plane), ‖y‖ ≤ R :=
  ConvexBody.exists_radius_bound K

/-- **Uniform site separation.** Over a compact parameter space, any two distinct labelled sites of
a continuous configuration family stay at least a fixed positive distance apart. -/
theorem exists_uniformSiteSeparation
    (sites : SiteFamily X n) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : X, ∀ i j : Fin n, i ≠ j →
        δ ≤ dist ((sites x).pts i) ((sites x).pts j) := by
  -- Consider the finite index type of ordered distinct pairs `P := {p : Fin n × Fin n // p.1 ≠
  -- p.2}`, a `Fintype`.
  set P := {p : Fin n × Fin n // p.1 ≠ p.2} with hP_def
  have hP_fintype : Fintype P := by
    infer_instance;
  -- For each pair `p = ⟨(i,j), hij⟩ ∈ P`, the map `g p : X → ℝ`, `x ↦ dist ((sites x).pts i)
  -- ((sites x).pts j)`, is continuous.
  have h_cont : ∀ p : P, Continuous (fun x : X => dist ((sites x).pts p.val.1) ((sites x).pts
    p.val.2)) := by
    intro p;
    exact Continuous.dist ( Continuous.comp ( continuous_apply _ ) (
      NRR.Config.continuous_pts.comp sites.continuous ) ) ( Continuous.comp ( continuous_apply _
      ) ( NRR.Config.continuous_pts.comp sites.continuous ) );
  by_cases hX : Nonempty X;
  · -- For each pair `p = ⟨(i,j), hij⟩ ∈ P`, the map `g p : X → ℝ`, `x ↦ dist ((sites x).pts i) ((sites x).pts j)`, attains a minimum at some `x_p`, with value `m p := dist ((sites x_p).pts i) ((sites x_p).pts j)`.
    obtain ⟨m, hm⟩ : ∃ m : P → ℝ, ∀ p : P, ∃ x_p : X, ∀ x : X, m p ≤ dist ((sites x).pts
      p.val.1) ((sites x).pts p.val.2) ∧ m p = dist ((sites x_p).pts p.val.1) ((sites x_p).pts
      p.val.2) := by
      have h_min : ∀ p : P, ∃ x_p : X, ∀ x : X, dist ((sites x_p).pts p.val.1) ((sites x_p).pts
        p.val.2) ≤ dist ((sites x).pts p.val.1) ((sites x).pts p.val.2) := by
        intro p;
        have := IsCompact.exists_isMinOn ( isCompact_univ ) ⟨ hX.some, Set.mem_univ _ ⟩ ( h_cont
          p |> Continuous.continuousOn );
        exact ⟨ this.choose, fun x => this.choose_spec.2 ( Set.mem_univ x ) ⟩;
      exact ⟨ fun p => dist ( ( sites ( Classical.choose ( h_min p ) ) ).pts p.val.1 ) ( ( sites
        ( Classical.choose ( h_min p ) ) ).pts p.val.2 ), fun p => ⟨ Classical.choose ( h_min p
        ), fun x => ⟨ Classical.choose_spec ( h_min p ) x, rfl ⟩ ⟩ ⟩;
    -- Since `i ≠ j` and `(sites x_p).pts` is injective (`(sites x_p).injective_pts`), the two
    -- points are distinct, so `m p > 0` by `dist_pos`.
    have h_pos : ∀ p : P, 0 < m p := by
      intro p
      obtain ⟨x_p, hx_p⟩ := hm p
      have h_dist_pos : 0 < dist ((sites x_p).pts p.val.1) ((sites x_p).pts p.val.2) := by
        exact dist_pos.mpr ( sites x_p |>.injective_pts.ne p.2 )
      exact hx_p x_p |>.2.symm ▸ h_dist_pos;
    -- Set `δ := min over p ∈ P of m p`, e.g. `Finset.univ.inf' (nonempty) m`.
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ p : P, δ ≤ m p := by
      by_cases hP_empty : Nonempty P
      · have hne : (Finset.univ.image m).Nonempty :=
          ⟨m hP_empty.some, Finset.mem_image_of_mem m (Finset.mem_univ hP_empty.some)⟩
        refine ⟨Finset.min' (Finset.univ.image m) hne, ?_, fun p => Finset.min'_le _ _
          (Finset.mem_image_of_mem m (Finset.mem_univ p))⟩
        have hmem := Finset.min'_mem (Finset.univ.image m) hne
        rcases Finset.mem_image.mp hmem with ⟨p, -, hp⟩
        rw [← hp]
        exact h_pos p
      · exact ⟨1, zero_lt_one, fun p => False.elim (hP_empty ⟨p⟩)⟩
    exact ⟨ δ, hδ.1, fun x i j hij => le_trans ( hδ.2 ⟨ ( i, j ), hij ⟩ ) ( hm ⟨ ( i, j ), hij ⟩
      |> Classical.choose_spec |> fun h => h x |> And.left ) ⟩;
  · exact ⟨ 1, zero_lt_one, fun x => False.elim <| hX ⟨ x ⟩ ⟩

/-- The canonical uniform **site radius** of a continuous site family over a compact space. -/
noncomputable def siteRadius (sites : SiteFamily X n) : ℝ :=
  (exists_siteRadius sites).choose

/-- The canonical **parent radius** of a fixed planar parent body. -/
noncomputable def parentRadius (K : Geometry.ConvexBody Plane) : ℝ :=
  (exists_parentRadius K).choose

/-- The canonical uniform **site separation** of a continuous site family over a compact space. -/
noncomputable def siteSeparation (sites : SiteFamily X n) : ℝ :=
  (exists_uniformSiteSeparation sites).choose

theorem siteRadius_nonneg (sites : SiteFamily X n) : 0 ≤ siteRadius sites :=
  (exists_siteRadius sites).choose_spec.1

theorem norm_site_le_siteRadius
    (sites : SiteFamily X n) (x : X) (i : Fin n) :
    ‖(sites x).pts i‖ ≤ siteRadius sites :=
  (exists_siteRadius sites).choose_spec.2 x i

theorem parentRadius_nonneg (K : Geometry.ConvexBody Plane) : 0 ≤ parentRadius K :=
  (exists_parentRadius K).choose_spec.1

theorem norm_mem_parent_le_parentRadius
    (K : Geometry.ConvexBody Plane) {y : Plane} (hy : y ∈ (K : Set Plane)) :
    ‖y‖ ≤ parentRadius K :=
  (exists_parentRadius K).choose_spec.2 y hy

theorem siteSeparation_pos (sites : SiteFamily X n) : 0 < siteSeparation sites :=
  (exists_uniformSiteSeparation sites).choose_spec.1

theorem siteSeparation_le_dist
    (sites : SiteFamily X n) (x : X) {i j : Fin n} (hij : i ≠ j) :
    siteSeparation sites ≤ dist ((sites x).pts i) ((sites x).pts j) :=
  (exists_uniformSiteSeparation sites).choose_spec.2 x i j hij

end NRR.EMP.VariableBody
