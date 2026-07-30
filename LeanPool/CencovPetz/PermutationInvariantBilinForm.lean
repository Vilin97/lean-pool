/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.PermutationInvariance
import LeanPool.CencovPetz.UniformSimplex


/-!
# `CencovPetz.PermutationInvariantBilinForm`

Lemmas about bilinear forms on the finite simplex tangent space that are invariant under
permutations (equivalences) of the underlying finite type.

This is a technical step towards the finite Čencov uniqueness theorem.
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

variable {n : ℕ}

namespace TangentFin

/-- The tangent space to the finite simplex on `Fin n`. -/
abbrev V (n : ℕ) : Type := tangentSpace (α := Fin n)

namespace Basis

/-- The coordinate basis vector on `Fin n`. -/
noncomputable def e (i : Fin n) : Fin n → ℝ := Pi.single i (1 : ℝ)

lemma sum_e (i : Fin n) : (∑ k : Fin n, e (n := n) i k) = 1 := by
  classical
  simp [e]

lemma sum_sub_e (i j : Fin n) : (∑ k : Fin n, (e (n := n) i k - e (n := n) j k)) = 0 := by
  classical
  simp [e]

/-- The tangent vector `e_i - e_j` (sum-zero). -/
noncomputable def dij (i j : Fin n) : V n :=
  ⟨fun k => e (n := n) i k - e (n := n) j k, by
    -- Membership in `tangentSpace` is `∑ = 0`.
    exact (tangentSpace.mem_iff (α := Fin n)
      (u := fun k => e (n := n) i k - e (n := n) j k)).2 (sum_sub_e (n := n) i j)⟩

@[simp] lemma dij_coe (i j : Fin n) (k : Fin n) :
    (dij (n := n) i j : Fin n → ℝ) k = e (n := n) i k - e (n := n) j k :=
  rfl

@[simp] lemma dij_self (i : Fin n) : dij (n := n) i i = 0 := by
  ext k
  simp [dij_coe]

lemma dij_neg (i j : Fin n) : dij (n := n) i j = -dij (n := n) j i := by
  ext k
  simp [dij_coe, sub_eq_add_neg, add_comm]

lemma dij_add (i j k : Fin n) : dij (n := n) i k = dij (n := n) i j + dij (n := n) j k := by
  ext t
  simp [dij_coe, sub_eq_add_neg, add_assoc]

end Basis

namespace Perm

open _root_.LeanPool.CencovPetz.TangentFin.Basis

/-- The deterministic Markov morphism induced by a permutation of `Fin n`. -/
noncomputable abbrev κ (σ : Equiv.Perm (Fin n)) : MarkovMorphism (Fin n) (Fin n) :=
  MarkovMorphism.deterministic (α := Fin n) (β := Fin n) (g := (σ : Fin n → Fin n)) σ.surjective

lemma κ_tangentPushforward_apply (σ : Equiv.Perm (Fin n)) (u : V n) (k : Fin n) :
    ((κ (n := n) σ).tangentPushforward u : Fin n → ℝ) k = (u : Fin n → ℝ) (σ.symm k) := by
  classical
  simpa [κ] using
    (MarkovMorphism.deterministic_tangentPushforward_apply_of_equiv (α := Fin n) (β := Fin n)
      (e := σ) (u := u) (b := k))

lemma κ_pushforward_apply (σ : Equiv.Perm (Fin n)) (p : Simplex (Fin n)) (k : Fin n) :
    ((κ (n := n) σ).pushforward p).p k = p.p (σ.symm k) := by
  classical
  simpa [κ] using
    (MarkovMorphism.deterministic_pushforward_apply_of_equiv (α := Fin n) (β := Fin n)
      (e := σ) (p := p) (b := k))

lemma e_apply_symm (σ : Equiv.Perm (Fin n)) (i k : Fin n) :
    e (n := n) i (σ.symm k) = e (n := n) (σ i) k := by
  classical
  by_cases hk : k = σ i
  · subst hk
    have this : σ.symm (σ i) = i := by simp
    rw [this]
    simp [e, Pi.single_eq_same]
  · have hki : σ.symm k ≠ i := by
      intro h
      apply hk
      simpa using congrArg σ h
    simp [e, hk, hki]

lemma κ_pushforward_uniform {n : ℕ} [Nonempty (Fin n)] (σ : Equiv.Perm (Fin n)) :
    (κ (n := n) σ).pushforward (Simplex.uniform (α := Fin n)) = Simplex.uniform (α := Fin n) := by
  classical
  ext k
  rw [κ_pushforward_apply]
  simp [Simplex.uniform_apply]

lemma κ_tangentPushforward_dij (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (κ (n := n) σ).tangentPushforward (Basis.dij (n := n) i j) =
      Basis.dij (n := n) (σ i) (σ j) := by
  classical
  ext k
  rw [κ_tangentPushforward_apply]
  simp [Basis.dij_coe, e_apply_symm]

lemma metric_uniform_invariant {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]
    (σ : Equiv.Perm (Fin n)) (u v : V n) :
    G.g (α := Fin n) (Simplex.uniform (α := Fin n))
        ((κ (n := n) σ).tangentPushforward u) ((κ (n := n) σ).tangentPushforward v)
      = G.g (α := Fin n) (Simplex.uniform (α := Fin n)) u v := by
  classical
  simpa [κ, κ_pushforward_uniform (σ := σ)] using
    (MonotoneMetricFamily.eq_of_equiv (G := G) (α := Fin n) (β := Fin n) (e := σ)
      (p := Simplex.uniform (α := Fin n)) u v)

end Perm

namespace Bilin

open _root_.LeanPool.CencovPetz.TangentFin.Basis
open Perm

variable {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]

/-- The bilinear form at the uniform simplex point on `Fin n`. -/
noncomputable abbrev B : LinearMap.BilinForm ℝ (V n) :=
  G.g (α := Fin n) (Simplex.uniform (α := Fin n))

lemma B_symm (u v : V n) : B (G := G) (n := n) u v = B (G := G) (n := n) v u := by
  simpa [B] using (G.symm (α := Fin n) (p := Simplex.uniform (α := Fin n)) u v)

lemma B_invariant (σ : Equiv.Perm (Fin n)) (u v : V n) :
    B (G := G) (n := n)
        ((κ (n := n) σ).tangentPushforward u) ((κ (n := n) σ).tangentPushforward v)
      = B (G := G) (n := n) u v := by
  simpa [B] using (Perm.metric_uniform_invariant (G := G) (σ := σ) u v)

lemma B_dij_dij_eq_of_perm (σ : Equiv.Perm (Fin n)) (i j k l : Fin n) :
    B (G := G) (n := n) (dij (n := n) (σ i) (σ j)) (dij (n := n) (σ k) (σ l))
      = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) := by
  classical
  have h := B_invariant (G := G) (n := n) (σ := σ) (u := dij (n := n) i j) (v := dij (n := n) k l)
  simpa [Perm.κ_tangentPushforward_dij] using h

lemma B_dij_dij_eq_zero_of_disjoint (i j k l : Fin n)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) = 0 := by
  classical
  let σ : Equiv.Perm (Fin n) := Equiv.swap k l
  have h := B_invariant (G := G) (n := n) (σ := σ) (u := dij (n := n) i j) (v := dij (n := n) k l)
  have hu :
      (κ (n := n) σ).tangentPushforward (dij (n := n) i j) = dij (n := n) i j := by
    calc
      (κ (n := n) σ).tangentPushforward (dij (n := n) i j)
          = dij (n := n) (σ i) (σ j) := Perm.κ_tangentPushforward_dij (n := n) (σ := σ) i j
      _ = dij (n := n) i j := by
            simp [σ, Equiv.swap_apply_of_ne_of_ne hik hil, Equiv.swap_apply_of_ne_of_ne hjk hjl]
  have hv :
      (κ (n := n) σ).tangentPushforward (dij (n := n) k l) = dij (n := n) l k := by
    simpa [σ] using (Perm.κ_tangentPushforward_dij (n := n) (σ := σ) k l)
  have hEq :
      B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) l k)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) := by
    simpa [hu, hv] using h
  have hneg : dij (n := n) l k = -dij (n := n) k l := by
    simpa using (Basis.dij_neg (n := n) l k)
  have hEq' :
      -B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) := by
    simp_all
  linarith

lemma B_dij_dij_eq_neg_half_self (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) =
      -(1 / 2 : ℝ) * B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
  classical
  have hsymm :
      B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) i j)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) := by
    simpa using (B_symm (G := G) (n := n) (dij (n := n) j k) (dij (n := n) i j))
  have hself_ik :
      B (G := G) (n := n) (dij (n := n) i k) (dij (n := n) i k)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
    have h :=
      B_invariant (G := G) (n := n) (σ := Equiv.swap j k)
        (u := dij (n := n) i j) (v := dij (n := n) i j)
    simpa [Perm.κ_tangentPushforward_dij, Equiv.swap_apply_of_ne_of_ne hij hik] using h
  have hself_jk :
      B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) j k)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
    have h :=
      B_invariant (G := G) (n := n) (σ := Equiv.swap i k)
        (u := dij (n := n) j k) (v := dij (n := n) j k)
    have hj :
        (κ (n := n) (Equiv.swap i k)).tangentPushforward (dij (n := n) j k) = dij (n := n) j i := by
      calc
        (κ (n := n) (Equiv.swap i k)).tangentPushforward (dij (n := n) j k)
            = dij (n := n) ((Equiv.swap i k) j) ((Equiv.swap i k) k) :=
              Perm.κ_tangentPushforward_dij (n := n) (σ := Equiv.swap i k) j k
        _ = dij (n := n) j i := by
              simp [Equiv.swap_apply_of_ne_of_ne hij.symm hjk]
    -- Use `dij j i = - dij i j`.
    have hj' : dij (n := n) j i = -dij (n := n) i j := by
      simpa using (Basis.dij_neg (n := n) j i)
    -- `B (-u) (-u) = B u u` for a bilinear form.
    simp_all
  -- Use `dij i k = dij i j + dij j k` and expand `B (u+v) (u+v)`.
  have hdij : dij (n := n) i k = dij (n := n) i j + dij (n := n) j k := by
    simpa using (Basis.dij_add (n := n) i j k)
  have h_expand :
      B (G := G) (n := n) (dij (n := n) i k) (dij (n := n) i k) =
        (B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j)
            + B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k))
          + (B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) i j)
            + B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) j k)) := by
    -- Bilinearity: expand in the left and right argument once.
    simp_all
  -- Combine invariance + symmetry to solve for the cross term.
  have hEq :
      B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j)
        =
          B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j)
          + 2 * B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k)
          + B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
    -- Start from `B(dij i k, dij i k) = B(dij i j, dij i j)` and expand.
    have h0 : B (G := G) (n := n) (dij (n := n) i k) (dij (n := n) i k)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := hself_ik
    -- Put everything in a shape where `linarith` can read it.
    have hsymm' :
        B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) i j)
          = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) := by
      simpa using hsymm
    -- Rewrite `B(dij j k, dij j k)` as `B(dij i j, dij i j)` and use the expansion.
    -- Then conclude.
    linarith [h0, h_expand, hself_jk, hsymm']
  set a : ℝ := B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) with ha
  set x : ℝ := B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) with hx
  have hEq' : a = a + 2 * x + a := by simpa [a, x] using hEq
  have hx' : x = -(1 / 2 : ℝ) * a := by linarith [hEq']
  simpa [a, x] using hx'

lemma B_dij_dij_eq_half_self (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i k) =
      (1 / 2 : ℝ) * B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
  classical
  have hdij : dij (n := n) i k = dij (n := n) i j + dij (n := n) j k := by
    simpa using (Basis.dij_add (n := n) i j k)
  -- Expand along the right argument and use the `(-1/2)` lemma.
  set a : ℝ := B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) with ha
  have hadd :
      B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i k)
        = a + B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) := by
    -- `B u (u+v) = B u u + B u v`.
    simp_all
  have hx :
      B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) = -(1 / 2 : ℝ) * a := by
    -- Apply the main `(-1/2)` lemma and rewrite `a`.
    simpa [a] using (B_dij_dij_eq_neg_half_self (G := G) (n := n) i j k hij hjk hik)
  -- Now solve `a + (-(1/2)*a) = (1/2)*a`.
  have : a + B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) = (1 / 2 : ℝ) * a := by
    linarith [hx]
  linarith [hadd, this, ha]

end Bilin

end TangentFin
end LeanPool.CencovPetz
