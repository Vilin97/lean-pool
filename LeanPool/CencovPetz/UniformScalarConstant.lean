/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.ReplicationInvariance
import LeanPool.CencovPetz.UniformScalarMultiple


/-!
# `CencovPetz.UniformScalarConstant`

Show that the **uniform-point scalar** from `UniformScalarMultiple` is independent of the simplex
dimension.

At the uniform point on `Fin n`, `UniformScalarMultiple` proves `G = cₙ · Fisher`.  This file shows
`cₙ` is actually a single constant `c` (independent of `n ≥ 2`), using replication isometries.

This is a key step toward a genuinely *unique* finite Čencov/Chentsov statement, rather than a
pointwise scalar multiple with a scalar depending on the point.

## Main results

- `CencovPetz.MonotoneMetricFamily.uniformScalar_eq_of_mul`
- `CencovPetz.MonotoneMetricFamily.uniformScalar_eq_uniformScalar_two`
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

namespace MonotoneMetricFamily

open MarkovMorphism TangentFin

/-- The scalar relating a monotone metric family to Fisher at the uniform simplex
of dimension `n`. -/
noncomputable def uniformScalar (G : MonotoneMetricFamily) (n : ℕ) (hn : 2 ≤ n) : ℝ := by
  classical
  let i0 : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le Nat.one_lt_two hn⟩
  haveI : Nonempty (Fin n) := ⟨i0⟩
  exact
    (TangentFin.Bilin.B (G := G) (n := n) (TangentFin.Basis.dij (n := n) i0 i1)
          (TangentFin.Basis.dij (n := n) i0 i1) /
        (2 * (Fintype.card (Fin n) : ℝ)))

private lemma two_le_card_prod {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) :
    2 ≤ Fintype.card (Fin n × Fin m) := by
  classical
  -- `card (Fin n × Fin m) = n * m`.
  simpa [Fintype.card_prod, Fintype.card_fin] using
    (le_trans hn (Nat.le_mul_of_pos_right n hm))

theorem uniformScalar_eq_of_mul (G : MonotoneMetricFamily) {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) :
    uniformScalar G (Fintype.card (Fin n × Fin m)) (two_le_card_prod (n := n) (m := m) hn hm)
      =
      uniformScalar G n hn := by
  classical
  -- Notation.
  let α := Fin n
  let β := Fin n × Fin m
  have : Nonempty α := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩⟩
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty β := by
    classical
    rcases (inferInstance : Nonempty α) with ⟨a0⟩
    exact ⟨(a0, ⟨0, hm⟩)⟩
  let N : ℕ := Fintype.card β
  have : Nonempty (Fin N) := ⟨⟨0, Fintype.card_pos⟩⟩
  let e : β ≃ Fin N := Fintype.equivFin β
  let κ : MarkovMorphism α β := MarkovMorphism.replicate (α := α) m hm
  let δ : MarkovMorphism β (Fin N) :=
    MarkovMorphism.deterministic (α := β) (β := Fin N) (g := (e : β → Fin N)) e.surjective
  have hκ_uniform : κ.pushforward (Simplex.uniform (α := α)) = Simplex.uniform (α := β) := by
    simpa [κ, β] using MarkovMorphism.replicate_pushforward_uniform (α := α) (m := m) (hm := hm)
  have hδ_uniform : δ.pushforward (Simplex.uniform (α := β)) = Simplex.uniform (α := Fin N) := by
    classical
    ext j
    have hj :
        (δ.pushforward (Simplex.uniform (α := β))).p j =
          (Simplex.uniform (α := β)).p (e.symm j) := by
      simpa [δ] using
        (MarkovMorphism.deterministic_pushforward_apply_of_equiv (α := β) (β := Fin N) (e := e)
          (p := Simplex.uniform (α := β)) (b := j))
    rw [hj]
    simp [Simplex.uniform_apply, Fintype.card_congr e]
  -- The `Fin n` scalar is detected on `dij 0 1`.
  let i0 : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le Nat.one_lt_two hn⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  let u : tangentSpace (α := α) := TangentFin.Basis.dij (n := n) i0 i1
  -- Transport `u` along replicate, then along the equivalence `e : β ≃ Fin N`.
  let v : tangentSpace (α := Fin N) := δ.tangentPushforward (κ.tangentPushforward u)
  -- `u` is nonzero, so Fisher on it is positive.
  have hu0 : u ≠ 0 := by
    intro h
    have h' := congrArg (fun w : tangentSpace (α := α) => (w : α → ℝ) i0) h
    have hu_eval : (u : α → ℝ) i0 = 0 := by
      simpa using h'
    have hu_eval' : (u : α → ℝ) i0 = (1 : ℝ) := by
      simp [u, TangentFin.Basis.dij_coe, TangentFin.Basis.e, hi01]
    simp_all
  have hFpos : 0 < fisherBilin (Simplex.uniform (α := α)) u u :=
    fisherBilin.pos (p := Simplex.uniform (α := α)) u hu0
  have hFne : fisherBilin (Simplex.uniform (α := α)) u u ≠ 0 := ne_of_gt hFpos
  -- Replication + equivalence invariance for `G` and for Fisher.
  have hG :
      G.g (α := Fin N) (Simplex.uniform (α := Fin N)) v v
        = G.g (α := α) (Simplex.uniform (α := α)) u u := by
    -- First reduce from `Fin N` to `β` by `e`.
    have h_equiv :
        G.g (α := Fin N) (δ.pushforward (Simplex.uniform (α := β))) v v
          =
          G.g (α := β) (Simplex.uniform (α := β))
            (κ.tangentPushforward u) (κ.tangentPushforward u) := by
      -- `eq_of_equiv` has the `Fin N` side on the left.
      simpa [v, δ] using
        (MonotoneMetricFamily.eq_of_equiv (G := G) (α := β) (β := Fin N) (e := e)
          (p := Simplex.uniform (α := β))
          (u := κ.tangentPushforward u) (v := κ.tangentPushforward u))
    -- Then reduce from `β` to `α` by replication.
    have h_repl :
        G.g (α := β) (κ.pushforward (Simplex.uniform (α := α)))
            (κ.tangentPushforward u) (κ.tangentPushforward u)
          = G.g (α := α) (Simplex.uniform (α := α)) u u := by
      simpa [κ] using
        (MonotoneMetricFamily.eq_of_replicate (G := G) (α := α) (m := m) (hm := hm)
          (p := Simplex.uniform (α := α)) (u := u) (v := u))
    -- Assemble and rewrite the pushed-forward uniform points.
    simpa [hδ_uniform, hκ_uniform] using (h_equiv.trans (by simpa [hκ_uniform] using h_repl))
  have hF :
      fisherBilin (Simplex.uniform (α := Fin N)) v v
        = fisherBilin (Simplex.uniform (α := α)) u u := by
    -- Same argument with `fisherMetricFamily`.
    have h_equiv :
        fisherBilin (δ.pushforward (Simplex.uniform (α := β))) v v
          =
          fisherBilin (Simplex.uniform (α := β))
            (κ.tangentPushforward u) (κ.tangentPushforward u) := by
      have h :=
        (MonotoneMetricFamily.eq_of_equiv
          (G := fisherMetricFamily) (α := β) (β := Fin N) (e := e)
          (p := Simplex.uniform (α := β))
          (u := κ.tangentPushforward u) (v := κ.tangentPushforward u))
      -- Rewrite the pushed-forward uniform point.
      simpa [fisherMetricFamily, v, δ, hδ_uniform] using h
    have h_repl :
        fisherBilin (κ.pushforward (Simplex.uniform (α := α)))
            (κ.tangentPushforward u) (κ.tangentPushforward u)
          = fisherBilin (Simplex.uniform (α := α)) u u := by
      simpa [κ, fisherMetricFamily] using
        (MonotoneMetricFamily.eq_of_replicate (G := fisherMetricFamily) (α := α) (m := m) (hm := hm)
          (p := Simplex.uniform (α := α)) (u := u) (v := u))
    simpa [hδ_uniform, hκ_uniform] using (h_equiv.trans (by simpa [hκ_uniform] using h_repl))
  -- Apply the uniform-point scalar-multiple identities on `Fin n` and `Fin N`,
  -- then compare scalars.
  have hFinN :
      (TangentFin.Bilin.B (G := G) (n := N))
        =
        (uniformScalar G N (two_le_card_prod (n := n) (m := m) hn hm)) •
          fisherBilin (Simplex.uniform (α := Fin N)) := by
    -- Use `UniformScalarMultiple` at `0,1` on `Fin N`.
    let j0 : Fin N := ⟨0, lt_of_lt_of_le Nat.zero_lt_two (two_le_card_prod (n := n) (m := m) hn hm)⟩
    let j1 : Fin N := ⟨1, lt_of_lt_of_le Nat.one_lt_two (two_le_card_prod (n := n) (m := m) hn hm)⟩
    have hj01 : j0 ≠ j1 := by
      intro h
      exact Nat.zero_ne_one (congrArg Fin.val h)
    simpa [MonotoneMetricFamily.uniformScalar, j0, j1] using
      (TangentFin.Bilin.B_eq_smul_fisherBilin_uniform (G := G) (n := N) (i0 := j0) (i1 := j1) hj01)
  have hFinn :
      (TangentFin.Bilin.B (G := G) (n := n))
        =
        (uniformScalar G n hn) • fisherBilin (Simplex.uniform (α := Fin n)) := by
    -- Use `UniformScalarMultiple` at `0,1` on `Fin n`.
    simpa [MonotoneMetricFamily.uniformScalar, i0, i1, hi01] using
      (TangentFin.Bilin.B_eq_smul_fisherBilin_uniform (G := G) (n := n) (i0 := i0) (i1 := i1) hi01)
  -- Evaluate both bilinear-form identities on `v` / `u` and use the isometry equalities.
  have hFinN_apply :
      G.g (α := Fin N) (Simplex.uniform (α := Fin N)) v v
        = (uniformScalar G N (two_le_card_prod (n := n) (m := m) hn hm)) *
          fisherBilin (Simplex.uniform (α := Fin N)) v v := by
    -- Unfold `B` and apply `hFinN`.
    simp_all
  have hFinn_apply :
      G.g (α := α) (Simplex.uniform (α := α)) u u
        = (uniformScalar G n hn) * fisherBilin (Simplex.uniform (α := α)) u u := by
    have := congrArg (fun B => B u u) hFinn
    simpa [TangentFin.Bilin.B, mul_assoc, α] using this
  -- Compare the two scalar factors using `hG` and `hF`.
  have :
      (uniformScalar G N (two_le_card_prod (n := n) (m := m) hn hm)) *
          fisherBilin (Simplex.uniform (α := α)) u u
        =
        (uniformScalar G n hn) *
          fisherBilin (Simplex.uniform (α := α)) u u := by
    -- Rewrite `hFinN_apply` and `hFinn_apply` using `hG`/`hF`.
    simp_all
  -- Cancel the positive Fisher factor.
  have hscalar :
      uniformScalar G N (two_le_card_prod (n := n) (m := m) hn hm) = uniformScalar G n hn :=
    mul_right_cancel₀ hFne this
  simpa [β, N] using hscalar

theorem uniformScalar_eq_uniformScalar_two (G : MonotoneMetricFamily) {n : ℕ} (hn : 2 ≤ n) :
    uniformScalar G n hn = uniformScalar G 2 (by decide) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn
  have h2n : 2 ≤ Fintype.card (Fin 2 × Fin n) := two_le_card_prod (n := 2) (m := n) (by decide) hn0
  have h2' : 2 ≤ Fintype.card (Fin n × Fin 2) := two_le_card_prod (n := n) (m := 2) hn (by decide)
  -- `c_{2*n} = c_n` via replication on `Fin n`.
  have hn_to :
      uniformScalar G (Fintype.card (Fin n × Fin 2)) h2'
        =
        uniformScalar G n hn :=
    uniformScalar_eq_of_mul (G := G) (n := n) (m := 2) hn (by decide)
  -- `c_{2*n} = c_2` via replication on `Fin 2`.
  have htwo_to :
      uniformScalar G (Fintype.card (Fin 2 × Fin n)) h2n
        =
        uniformScalar G 2 (by decide) :=
    uniformScalar_eq_of_mul (G := G) (n := 2) (m := n) (by decide) hn0
  -- Both cardinals are `2*n`.
  have hcard :
      Fintype.card (Fin n × Fin 2) = Fintype.card (Fin 2 × Fin n) := by
    simp [Nat.mul_comm]
  -- Rewrite the first equality along `hcard` and conclude.
  simp_all

end MonotoneMetricFamily
end LeanPool.CencovPetz
