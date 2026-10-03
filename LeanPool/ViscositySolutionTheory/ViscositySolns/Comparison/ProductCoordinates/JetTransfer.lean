/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProductCoordinates.Embeddings

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Product-coordinate consequences of the semiconvex matrix lemma (JetTransfer)

Part of the product-coordinate development connecting the semiconvex matrix
conclusion on the coordinate space `R^(n+n)` to the block-matrix notation on
`R^n × R^n`. Split from `ProductCoordinates.lean`; see the umbrella module
docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder
open Filter

namespace ViscositySolns

variable {n : Nat}

/--
Vanishing of the mixed bilinear expression gives the selected block diagonal
Hessian.

In standard mathematical terms, let `Z` be a symmetric Hessian matrix on
`R^n × R^n`. Suppose that for all `x, y ∈ R^n`,

`⟪Z(x, 0), (0, y)⟫ + ⟪Z(0, y), (x, 0)⟫ = 0`.

Then the block-coordinate form of `Z` is

`[X 0; 0 -Y]`,

where `X` is the left-left block of `Z` and `Y` is the negative of the
right-right block of `Z`.
-/
theorem pointHessianToBlockHessian_eq_comparisonBlockDiagonal_of_mixed_dot_zero
    {Z : Hessian (n + n)} (hZ : Z.IsHermitian)
    (hmix : ∀ x y : Point n,
      dotProduct (Matrix.mulVec Z (leftPointEmbedding (n := n) x))
          (rightPointEmbedding (n := n) y) +
        dotProduct (Matrix.mulVec Z (rightPointEmbedding (n := n) y))
          (leftPointEmbedding (n := n) x) = 0) :
    pointHessianToBlockHessian (n := n) Z =
      comparisonBlockDiagonal (leftPointHessian (n := n) Z)
        (-rightPointHessian (n := n) Z) := by
  ext a b
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          simp [leftPointHessian, pointHessianToBlockHessian]
      | inr j =>
          have hsym :
              Z (Fin.natAdd n j) (Fin.castAdd n i) =
                Z (Fin.castAdd n i) (Fin.natAdd n j) := by
            have h := congr_fun (congr_fun hZ.eq (Fin.castAdd n i)) (Fin.natAdd n j)
            simpa [Matrix.conjTranspose] using h
          have hzero :
              Z (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
            have h := hmix (Pi.single i (1 : Real)) (Pi.single j (1 : Real))
            rw [dotProduct_mulVec_leftPointEmbedding_rightPointEmbedding,
              dotProduct_mulVec_rightPointEmbedding_leftPointEmbedding] at h
            simp only [leftBlockPoint_single, rightBlockPoint_single] at h
            rw [dotProduct_mulVec_leftBlockPoint_single_rightBlockPoint_single,
              dotProduct_mulVec_rightBlockPoint_single_leftBlockPoint_single] at h
            have hraw :
                Z (Fin.natAdd n j) (Fin.castAdd n i) +
                    Z (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
              simpa [pointHessianToBlockHessian, Fin.natAdd_eq_addNat] using h
            rw [hsym] at hraw
            have h' :
                Z (Fin.castAdd n i) (Fin.natAdd n j) +
                    Z (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
              exact hraw
            linarith
          simpa [pointHessianToBlockHessian, Fin.natAdd_eq_addNat] using hzero
  | inr i =>
      cases b with
      | inl j =>
          have hsym :
              Z (Fin.natAdd n i) (Fin.castAdd n j) =
                Z (Fin.castAdd n j) (Fin.natAdd n i) := by
            have h := congr_fun (congr_fun hZ.eq (Fin.castAdd n j)) (Fin.natAdd n i)
            simpa [Matrix.conjTranspose] using h
          have hzero :
              Z (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
            have h := hmix (Pi.single j (1 : Real)) (Pi.single i (1 : Real))
            rw [dotProduct_mulVec_leftPointEmbedding_rightPointEmbedding,
              dotProduct_mulVec_rightPointEmbedding_leftPointEmbedding] at h
            simp only [leftBlockPoint_single, rightBlockPoint_single] at h
            rw [dotProduct_mulVec_leftBlockPoint_single_rightBlockPoint_single,
              dotProduct_mulVec_rightBlockPoint_single_leftBlockPoint_single] at h
            have hraw :
                Z (Fin.natAdd n i) (Fin.castAdd n j) +
                    Z (Fin.castAdd n j) (Fin.natAdd n i) = 0 := by
              simpa [pointHessianToBlockHessian, Fin.natAdd_eq_addNat] using h
            rw [← hsym] at hraw
            have h' :
                Z (Fin.natAdd n i) (Fin.castAdd n j) +
                    Z (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
              exact hraw
            linarith
          simpa [pointHessianToBlockHessian, Fin.natAdd_eq_addNat] using hzero
      | inr j =>
          simp [rightPointHessian, pointHessianToBlockHessian]

/--
The mixed second difference of a separated function is zero.

In standard mathematical terms, if `F(ξ, η) = G(ξ) - H(η)`, then for every
base point `(ξ₀, η₀)` and all increments `x, y ∈ R^n`,

`F((ξ₀ + x), (η₀ + y)) - F((ξ₀ + x), η₀)
  - F(ξ₀, (η₀ + y)) + F(ξ₀, η₀) = 0`.
-/
theorem separatedFunction_mixed_second_difference_left_right
    (G H : Point n -> Real) (z : Point (n + n)) (x y : Point n) :
    blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))
        (z + leftPointEmbedding (n := n) x + rightPointEmbedding (n := n) y) -
        blockFunctionToPointFunction (n := n)
          (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))
          (z + leftPointEmbedding (n := n) x) -
        blockFunctionToPointFunction (n := n)
          (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))
          (z + rightPointEmbedding (n := n) y) +
        blockFunctionToPointFunction (n := n)
          (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)) z =
      0 := by
  change
    (G (pointLeft (n := n)
          (z + leftPointEmbedding (n := n) x + rightPointEmbedding (n := n) y)) -
        H (pointRight (n := n)
          (z + leftPointEmbedding (n := n) x + rightPointEmbedding (n := n) y))) -
      (G (pointLeft (n := n) (z + leftPointEmbedding (n := n) x)) -
        H (pointRight (n := n) (z + leftPointEmbedding (n := n) x))) -
      (G (pointLeft (n := n) (z + rightPointEmbedding (n := n) y)) -
        H (pointRight (n := n) (z + rightPointEmbedding (n := n) y))) +
      (G (pointLeft (n := n) z) - H (pointRight (n := n) z)) = 0
  have hleftBoth :
      pointLeft (n := n)
          (z + leftPointEmbedding (n := n) x + rightPointEmbedding (n := n) y) =
        pointLeft (n := n) z + x := by
    rw [pointLeft_add_rightPointEmbedding, pointLeft_add_leftPointEmbedding]
  have hrightBoth :
      pointRight (n := n)
          (z + leftPointEmbedding (n := n) x + rightPointEmbedding (n := n) y) =
        pointRight (n := n) z + y := by
    rw [pointRight_add_rightPointEmbedding, pointRight_add_leftPointEmbedding]
  have hleftLeft :
      pointLeft (n := n) (z + leftPointEmbedding (n := n) x) =
        pointLeft (n := n) z + x := by
    rw [pointLeft_add_leftPointEmbedding]
  have hrightLeft :
      pointRight (n := n) (z + leftPointEmbedding (n := n) x) =
        pointRight (n := n) z := by
    rw [pointRight_add_leftPointEmbedding]
  have hleftRight :
      pointLeft (n := n) (z + rightPointEmbedding (n := n) y) =
        pointLeft (n := n) z := by
    rw [pointLeft_add_rightPointEmbedding]
  have hrightRight :
      pointRight (n := n) (z + rightPointEmbedding (n := n) y) =
        pointRight (n := n) z + y := by
    rw [pointRight_add_rightPointEmbedding]
  rw [hleftBoth, hrightBoth, hleftLeft, hrightLeft, hleftRight, hrightRight]
  ring

/--
A second-order expansion of a separated function has zero mixed Hessian
bilinear expression.

In standard mathematical terms, let `F(ξ, η) = G(ξ) - H(η)`. If `F` has a
second-order expansion at `(ξ₀, η₀)` with Hessian `Z`, then for every
`x, y ∈ R^n`,

`⟪Z(x, 0), (0, y)⟫ + ⟪Z(0, y), (x, 0)⟫ = 0`.
-/
theorem mixed_dot_zero_of_hasSecondOrderExpansionWithin_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} {z p Z}
    (hF : HasSecondOrderExpansionWithin Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      z ({ gradient := p, hessian := Z } : Jet (n + n))) :
    ∀ x y : Point n,
      dotProduct (Matrix.mulVec Z (leftPointEmbedding (n := n) x))
          (rightPointEmbedding (n := n) y) +
        dotProduct (Matrix.mulVec Z (rightPointEmbedding (n := n) y))
          (leftPointEmbedding (n := n) x) = 0 := by
  intro x y
  let F : Point (n + n) -> Real :=
    blockFunctionToPointFunction (n := n)
      (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))
  let J : Jet (n + n) := { gradient := p, hessian := Z }
  rcases hF with ⟨rho, hrho, hF_eq⟩
  have hrho_z : rho z = 0 :=
    secondOrderExpansion_remainder_eq_zero_at_base
      (C := Set.univ) (φ := F) (rho := rho) (x0 := z) (J := J)
      (Set.mem_univ _) hF_eq
  let u : Point (n + n) := leftPointEmbedding (n := n) x
  let v : Point (n + n) := rightPointEmbedding (n := n) y
  let B : Real :=
    dotProduct (Matrix.mulVec Z u) v + dotProduct (Matrix.mulVec Z v) u
  have hremLittle : Asymptotics.IsLittleO (nhds (0 : Real))
      (fun t : Real => rho (z + t • u + t • v) - rho (z + t • u) -
        rho (z + t • v) + rho z)
      (fun t : Real => t ^ 2) :=
    semijetRemainder_mixed_along_affine_isLittleO_sq
      (n := n + n) (rho := rho) (z := z) (u := u) (v := v) hrho hrho_z
  let l : Filter Real := nhdsWithin (0 : Real) {t : Real | t ≠ 0}
  have hremTendsto : Tendsto
      (fun t : Real =>
        (rho (z + t • u + t • v) - rho (z + t • u) -
          rho (z + t • v) + rho z) / (t ^ 2))
      l (nhds 0) :=
    hremLittle.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hF_eq_nhds :
      ∀ᶠ w in nhds z, F w = quadraticModel z (F z) p Z w + rho w := by
    simpa [F, J, nhdsWithin_univ] using hF_eq
  have hline_both :
      Tendsto (fun t : Real => z + t • u + t • v) l (nhds z) := by
    have hcont : ContinuousAt (fun t : Real => z + t • u + t • v) 0 :=
      ((continuous_const.add (continuous_id.smul continuous_const)).add
        (continuous_id.smul continuous_const)).continuousAt
    have htend :
        Tendsto (fun t : Real => z + t • u + t • v) (nhds 0)
          (nhds (z + (0 : Real) • u + (0 : Real) • v)) := hcont
    simpa using htend.mono_left nhdsWithin_le_nhds
  have hline_left : Tendsto (fun t : Real => z + t • u) l (nhds z) := by
    have hcont : ContinuousAt (fun t : Real => z + t • u) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    have htend :
        Tendsto (fun t : Real => z + t • u) (nhds 0)
          (nhds (z + (0 : Real) • u)) := hcont
    simpa using htend.mono_left nhdsWithin_le_nhds
  have hline_right : Tendsto (fun t : Real => z + t • v) l (nhds z) := by
    have hcont : ContinuousAt (fun t : Real => z + t • v) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    have htend :
        Tendsto (fun t : Real => z + t • v) (nhds 0)
          (nhds (z + (0 : Real) • v)) := hcont
    simpa using htend.mono_left nhdsWithin_le_nhds
  have hboth_eq :
      ∀ᶠ t in l,
        F (z + t • u + t • v) =
          quadraticModel z (F z) p Z (z + t • u + t • v) +
            rho (z + t • u + t • v) :=
    hline_both.eventually hF_eq_nhds
  have hleft_eq :
      ∀ᶠ t in l,
        F (z + t • u) =
          quadraticModel z (F z) p Z (z + t • u) + rho (z + t • u) :=
    hline_left.eventually hF_eq_nhds
  have hright_eq :
      ∀ᶠ t in l,
        F (z + t • v) =
          quadraticModel z (F z) p Z (z + t • v) + rho (z + t • v) :=
    hline_right.eventually hF_eq_nhds
  have hconst_event :
      (fun _t : Real => (1 / 2 : Real) * B) =ᶠ[l]
        fun t : Real =>
          -((rho (z + t • u + t • v) - rho (z + t • u) -
            rho (z + t • v) + rho z) / (t ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin, hboth_eq, hleft_eq, hright_eq] with
      t ht_ne hboth hleft hright
    have ht_sq_ne : t ^ 2 ≠ 0 := pow_ne_zero 2 ht_ne
    have hsep :
        F (z + t • u + t • v) - F (z + t • u) - F (z + t • v) + F z = 0 := by
      have hraw :=
        separatedFunction_mixed_second_difference_left_right
          (n := n) G H z (t • x) (t • y)
      simpa [F, u, v, leftPointEmbedding_smul, rightPointEmbedding_smul, add_assoc] using hraw
    have hquad :
        quadraticModel z (F z) p Z (z + t • u + t • v) -
            quadraticModel z (F z) p Z (z + t • u) -
            quadraticModel z (F z) p Z (z + t • v) +
            quadraticModel z (F z) p Z z =
          (t ^ 2) * ((1 / 2 : Real) * B) := by
      have hraw :=
        quadraticModel_mixed_second_difference_left_right
          (n := n) z (F z) p Z (t • x) (t • y)
      have hscale :
          (1 / 2 : Real) *
              (dotProduct (Matrix.mulVec Z (leftPointEmbedding (n := n) (t • x)))
                  (rightPointEmbedding (n := n) (t • y)) +
                dotProduct (Matrix.mulVec Z (rightPointEmbedding (n := n) (t • y)))
                  (leftPointEmbedding (n := n) (t • x))) =
            (t ^ 2) * ((1 / 2 : Real) * B) := by
        simp [B, u, v, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
        ring
      rw [hscale] at hraw
      simpa [u, v, leftPointEmbedding_smul, rightPointEmbedding_smul, add_assoc] using hraw
    have hbase :
        F z = quadraticModel z (F z) p Z z + rho z := by
      simp [quadraticModel, hrho_z]
    have hmix :
        (t ^ 2) * ((1 / 2 : Real) * B) +
            (rho (z + t • u + t • v) - rho (z + t • u) -
              rho (z + t • v) + rho z) = 0 := by
      have hqbase : quadraticModel z (F z) p Z z = F z := by
        simp [quadraticModel]
      rw [hboth, hleft, hright] at hsep
      linarith
    have hdiv :
        (1 / 2 : Real) * B +
            (rho (z + t • u + t • v) - rho (z + t • u) -
              rho (z + t • v) + rho z) / (t ^ 2) = 0 := by
      let R : Real :=
        rho (z + t • u + t • v) - rho (z + t • u) - rho (z + t • v) + rho z
      change (1 / 2 : Real) * B + R / (t ^ 2) = 0
      have hrewrite :
          (1 / 2 : Real) * B + R / (t ^ 2) =
            ((t ^ 2) * ((1 / 2 : Real) * B) + R) / (t ^ 2) := by
        field_simp [ht_sq_ne]
      rw [hrewrite]
      change ((t ^ 2) * ((1 / 2 : Real) * B) +
          (rho (z + t • u + t • v) - rho (z + t • u) -
            rho (z + t • v) + rho z)) / (t ^ 2) = 0
      rw [hmix]
      simp
    linarith
  have hconst_to_zero : Tendsto (fun _t : Real => (1 / 2 : Real) * B) l (nhds 0) := by
    have hneg : Tendsto
        (fun t : Real =>
          -((rho (z + t • u + t • v) - rho (z + t • u) -
            rho (z + t • v) + rho z) / (t ^ 2)))
        l (nhds 0) := by
      simpa using hremTendsto.neg
    exact hneg.congr' hconst_event.symm
  have hconst_to_half : Tendsto (fun _t : Real => (1 / 2 : Real) * B) l
      (nhds ((1 / 2 : Real) * B)) :=
    tendsto_const_nhds
  have : NeBot l := by
    simpa [l, Set.compl_singleton_eq] using
      (inferInstance : NeBot (nhdsWithin (0 : Real) ({0}ᶜ : Set Real)))
  have hhalf : (1 / 2 : Real) * B = 0 :=
    tendsto_nhds_unique hconst_to_half hconst_to_zero
  have hB : B = 0 := by
    linarith
  simpa [B, u, v] using hB

/--
Restrict a superjet of a separated difference to the left coordinate slice at
an arbitrary base point.

In standard mathematical terms, if `(p, Z)` is a superjet at `(x0, y0)` of
`(ξ, η) ↦ G(ξ) - H(η)`, then the left component of `p` and the left-left
block of `Z` form a superjet of `G` at `x0`.
-/
theorem superjet_left_of_superjet_blockFunctionToPointFunction_sub_at
    {G H : Point n -> Real} {z : Point (n + n)} {J : Jet (n + n)}
    (hJ : J ∈ Superjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) z) :
    ({ gradient := leftPointGradient (n := n) J.gradient,
       hessian := leftPointHessian (n := n) J.hessian } : Jet n) ∈
      Superjet Set.univ G (pointLeft (n := n) z) := by
  rw [superjet_iff_superjetExcess_secondOrderNonposWithin]
  have hblock :=
    (superjet_iff_superjetExcess_secondOrderNonposWithin (C := Set.univ)
      (u := blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      (x := z) (J := J)).1 hJ
  intro ε hε
  have hleftTendsto :
      Tendsto (pointWithLeft (n := n) z)
        (nhdsWithin (pointLeft (n := n) z) Set.univ)
        (nhdsWithin z Set.univ) := by
    rw [nhdsWithin_univ, nhdsWithin_univ]
    have hcont : ContinuousAt (pointWithLeft (n := n) z) (pointLeft (n := n) z) :=
      (continuous_pointWithLeft (n := n) z).continuousAt
    simpa using hcont.tendsto
  have hb := hleftTendsto.eventually (hblock ε hε)
  filter_upwards [hb] with x hx
  have hexcess :
      SuperjetExcess G (pointLeft (n := n) z)
          ({ gradient := leftPointGradient (n := n) J.gradient,
             hessian := leftPointHessian (n := n) J.hessian } : Jet n) x =
        SuperjetExcess
          (blockFunctionToPointFunction (n := n)
            (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
          z J (pointWithLeft (n := n) z x) := by
    simp only [SuperjetExcess, blockFunctionToPointFunction,
      pointSumEquivBlockPoint_pointWithLeft, quadraticModel_pointWithLeft]
    simp [quadraticModel, pointLeft, pointRight, blockPointLeft, blockPointRight]
    ring
  have hsq :
      ‖pointWithLeft (n := n) z x - z‖ ^ 2 <=
        ‖x - pointLeft (n := n) z‖ ^ 2 := by
    have hnorm := norm_pointWithLeft_sub_self_le (n := n) z x
    have hmul := mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
    simpa [pow_two] using hmul
  have hmul :
      ε * ‖pointWithLeft (n := n) z x - z‖ ^ 2 <=
        ε * ‖x - pointLeft (n := n) z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hε.le
  linarith

/--
Restrict a superjet of a separated difference to the right coordinate slice at
an arbitrary base point.

In standard mathematical terms, if `(p, Z)` is a superjet at `(x0, y0)` of
`(ξ, η) ↦ G(ξ) - H(η)`, then the negative right component of `p` and the
negative right-right block of `Z` form a subjet of `H` at `y0`.
-/
theorem subjet_right_of_superjet_blockFunctionToPointFunction_sub_at
    {G H : Point n -> Real} {z : Point (n + n)} {J : Jet (n + n)}
    (hJ : J ∈ Superjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) z) :
    ({ gradient := -rightPointGradient (n := n) J.gradient,
       hessian := -rightPointHessian (n := n) J.hessian } : Jet n) ∈
      Subjet Set.univ H (pointRight (n := n) z) := by
  let Jr : Jet n :=
    { gradient := rightPointGradient (n := n) J.gradient,
      hessian := rightPointHessian (n := n) J.hessian }
  have hsuperNeg :
      Jr ∈ Superjet Set.univ (fun y => -H y) (pointRight (n := n) z) := by
    rw [superjet_iff_superjetExcess_secondOrderNonposWithin]
    have hblock :=
      (superjet_iff_superjetExcess_secondOrderNonposWithin (C := Set.univ)
        (u := blockFunctionToPointFunction (n := n)
          (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
        (x := z) (J := J)).1 hJ
    intro ε hε
    have hrightTendsto :
        Tendsto (pointWithRight (n := n) z)
          (nhdsWithin (pointRight (n := n) z) Set.univ)
          (nhdsWithin z Set.univ) := by
      rw [nhdsWithin_univ, nhdsWithin_univ]
      have hcont : ContinuousAt (pointWithRight (n := n) z) (pointRight (n := n) z) :=
        (continuous_pointWithRight (n := n) z).continuousAt
      simpa using hcont.tendsto
    have hb := hrightTendsto.eventually (hblock ε hε)
    filter_upwards [hb] with y hy
    have hexcess :
        SuperjetExcess (fun y : Point n => -H y) (pointRight (n := n) z) Jr y =
          SuperjetExcess
            (blockFunctionToPointFunction (n := n)
              (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
            z J (pointWithRight (n := n) z y) := by
      simp only [SuperjetExcess, blockFunctionToPointFunction,
        pointSumEquivBlockPoint_pointWithRight, quadraticModel_pointWithRight]
      simp [quadraticModel, pointLeft, pointRight, blockPointLeft, blockPointRight, Jr]
      ring
    have hsq :
        ‖pointWithRight (n := n) z y - z‖ ^ 2 <=
          ‖y - pointRight (n := n) z‖ ^ 2 := by
      have hnorm := norm_pointWithRight_sub_self_le (n := n) z y
      have hmul := mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
      simpa [pow_two] using hmul
    have hmul :
        ε * ‖pointWithRight (n := n) z y - z‖ ^ 2 <=
          ε * ‖y - pointRight (n := n) z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hε.le
    linarith
  change Jr.neg ∈ Subjet Set.univ H (pointRight (n := n) z)
  simpa using
    (superjet_neg_iff_subjet (C := Set.univ) (u := fun y : Point n => -H y)
      (x := pointRight (n := n) z) (J := Jr)).1 hsuperNeg

/--
Restrict a subjet of a separated difference to the left coordinate slice at
an arbitrary base point.

In standard mathematical terms, if `(p, Z)` is a subjet at `(x0, y0)` of
`(ξ, η) ↦ G(ξ) - H(η)`, then the left component of `p` and the left-left
block of `Z` form a subjet of `G` at `x0`.
-/
theorem subjet_left_of_subjet_blockFunctionToPointFunction_sub_at
    {G H : Point n -> Real} {z : Point (n + n)} {J : Jet (n + n)}
    (hJ : J ∈ Subjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) z) :
    ({ gradient := leftPointGradient (n := n) J.gradient,
       hessian := leftPointHessian (n := n) J.hessian } : Jet n) ∈
      Subjet Set.univ G (pointLeft (n := n) z) := by
  rw [subjet_iff_subjetExcess_secondOrderNonposWithin]
  have hblock :=
    (subjet_iff_subjetExcess_secondOrderNonposWithin (C := Set.univ)
      (u := blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      (x := z) (J := J)).1 hJ
  intro ε hε
  have hleftTendsto :
      Tendsto (pointWithLeft (n := n) z)
        (nhdsWithin (pointLeft (n := n) z) Set.univ)
        (nhdsWithin z Set.univ) := by
    rw [nhdsWithin_univ, nhdsWithin_univ]
    have hcont : ContinuousAt (pointWithLeft (n := n) z) (pointLeft (n := n) z) :=
      (continuous_pointWithLeft (n := n) z).continuousAt
    simpa using hcont.tendsto
  have hb := hleftTendsto.eventually (hblock ε hε)
  filter_upwards [hb] with x hx
  have hexcess :
      SubjetExcess G (pointLeft (n := n) z)
          ({ gradient := leftPointGradient (n := n) J.gradient,
             hessian := leftPointHessian (n := n) J.hessian } : Jet n) x =
        SubjetExcess
          (blockFunctionToPointFunction (n := n)
            (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
          z J (pointWithLeft (n := n) z x) := by
    simp only [SubjetExcess, blockFunctionToPointFunction,
      pointSumEquivBlockPoint_pointWithLeft, quadraticModel_pointWithLeft]
    simp [quadraticModel, pointLeft, pointRight, blockPointLeft, blockPointRight]
    ring
  have hsq :
      ‖pointWithLeft (n := n) z x - z‖ ^ 2 <=
        ‖x - pointLeft (n := n) z‖ ^ 2 := by
    have hnorm := norm_pointWithLeft_sub_self_le (n := n) z x
    have hmul := mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
    simpa [pow_two] using hmul
  have hmul :
      ε * ‖pointWithLeft (n := n) z x - z‖ ^ 2 <=
        ε * ‖x - pointLeft (n := n) z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hε.le
  linarith

/--
Restrict a subjet of a separated difference to the right coordinate slice at
an arbitrary base point.

In standard mathematical terms, if `(p, Z)` is a subjet at `(x0, y0)` of
`(ξ, η) ↦ G(ξ) - H(η)`, then the negative right component of `p` and the
negative right-right block of `Z` form a superjet of `H` at `y0`.
-/
theorem superjet_right_of_subjet_blockFunctionToPointFunction_sub_at
    {G H : Point n -> Real} {z : Point (n + n)} {J : Jet (n + n)}
    (hJ : J ∈ Subjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) z) :
    ({ gradient := -rightPointGradient (n := n) J.gradient,
       hessian := -rightPointHessian (n := n) J.hessian } : Jet n) ∈
      Superjet Set.univ H (pointRight (n := n) z) := by
  let Jr : Jet n :=
    { gradient := -rightPointGradient (n := n) J.gradient,
      hessian := -rightPointHessian (n := n) J.hessian }
  rw [superjet_iff_superjetExcess_secondOrderNonposWithin]
  have hblock :=
    (subjet_iff_subjetExcess_secondOrderNonposWithin (C := Set.univ)
      (u := blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      (x := z) (J := J)).1 hJ
  intro ε hε
  have hrightTendsto :
      Tendsto (pointWithRight (n := n) z)
        (nhdsWithin (pointRight (n := n) z) Set.univ)
        (nhdsWithin z Set.univ) := by
    rw [nhdsWithin_univ, nhdsWithin_univ]
    have hcont : ContinuousAt (pointWithRight (n := n) z) (pointRight (n := n) z) :=
      (continuous_pointWithRight (n := n) z).continuousAt
    simpa using hcont.tendsto
  have hb := hrightTendsto.eventually (hblock ε hε)
  filter_upwards [hb] with y hy
  have hexcess :
      SuperjetExcess H (pointRight (n := n) z) Jr y =
        SubjetExcess
          (blockFunctionToPointFunction (n := n)
            (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
          z J (pointWithRight (n := n) z y) := by
    simp only [SuperjetExcess, SubjetExcess, blockFunctionToPointFunction,
      pointSumEquivBlockPoint_pointWithRight, quadraticModel_pointWithRight]
    simp [quadraticModel, pointLeft, pointRight, blockPointLeft, blockPointRight,
      Jr, Matrix.neg_mulVec, neg_dotProduct]
    ring
  have hsq :
      ‖pointWithRight (n := n) z y - z‖ ^ 2 <=
        ‖y - pointRight (n := n) z‖ ^ 2 := by
    have hnorm := norm_pointWithRight_sub_self_le (n := n) z y
    have hmul := mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
    simpa [pow_two] using hmul
  have hmul :
      ε * ‖pointWithRight (n := n) z y - z‖ ^ 2 <=
        ε * ‖y - pointRight (n := n) z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hε.le
  linarith

/--
Closed-superjet restriction to the left coordinate for a separated difference.

In standard mathematical terms, assume `H` is continuous. If `(p, Z)` belongs
to the closed superjet at `(0, 0)` of `(ξ, η) ↦ G(ξ) - H(η)`, then the left
component of `p` and the left-left block of `Z` belong to the closed superjet
of `G` at `0`.
-/
theorem closedSuperjet_left_of_closedSuperjet_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} (hH : Continuous H) {J : Jet (n + n)}
    (hJ : J ∈ ClosedSuperjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) 0) :
    leftPointJet (n := n) J ∈ ClosedSuperjet Set.univ G 0 := by
  let F : Point (n + n) -> Real :=
    blockFunctionToPointFunction (n := n)
      (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))
  let T : ((Point (n + n) × Real) × Jet (n + n)) -> ((Point n × Real) × Jet n) :=
    fun z => ((pointLeft (n := n) z.1.1, z.1.2 + H (pointRight (n := n) z.1.1)),
      leftPointJet (n := n) z.2)
  have hTcont : Continuous T := by
    have hbase : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) => z.1.1 :=
      continuous_fst.comp continuous_fst
    have hr : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) => z.1.2 :=
      continuous_snd.comp continuous_fst
    have hleftBase : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        pointLeft (n := n) z.1.1 :=
      continuous_pointLeft.comp hbase
    have hrightBase : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        pointRight (n := n) z.1.1 :=
      continuous_pointRight.comp hbase
    have hvalue : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        z.1.2 + H (pointRight (n := n) z.1.1) :=
      hr.add (hH.comp hrightBase)
    have hleft : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        (pointLeft (n := n) z.1.1, z.1.2 + H (pointRight (n := n) z.1.1)) :=
      hleftBase.prodMk hvalue
    have hjet : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        leftPointJet (n := n) z.2 :=
      continuous_leftPointJet.comp continuous_snd
    simpa [T] using hleft.prodMk hjet
  have hT_mem : T ((0, F 0), J) ∈ closure (T '' SuperjetGraph Set.univ F) :=
    image_closure_subset_closure_image hTcont ⟨((0, F 0), J), hJ, rfl⟩
  have hsubset : T '' SuperjetGraph Set.univ F ⊆ SuperjetGraph Set.univ G := by
    intro w hw
    rcases hw with ⟨v, hv, rfl⟩
    rcases v with ⟨⟨z, r⟩, K⟩
    rcases hv with ⟨_hz, hr, hK⟩
    change r = F z at hr
    subst r
    have hleftJet :
        leftPointJet (n := n) K ∈ Superjet Set.univ G (pointLeft (n := n) z) :=
      superjet_left_of_superjet_blockFunctionToPointFunction_sub_at
        (n := n) (G := G) (H := H) (z := z) (J := K) hK
    have hvalue :
        F z + H (pointRight (n := n) z) = G (pointLeft (n := n) z) := by
      simp [F, blockFunctionToPointFunction, pointLeft, pointRight, blockPointLeft,
        blockPointRight]
    exact ⟨Set.mem_univ _, hvalue, hleftJet⟩
  have hclosure : T ((0, F 0), J) ∈ closure (SuperjetGraph Set.univ G) :=
    closure_mono hsubset hT_mem
  have htarget :
      T ((0, F 0), J) = ((0, G 0), leftPointJet (n := n) J) := by
    simp [T, F, blockFunctionToPointFunction, pointLeft, pointRight, blockPointLeft,
      blockPointRight]
  change ((0, G 0), leftPointJet (n := n) J) ∈ closure (SuperjetGraph Set.univ G)
  rw [htarget] at hclosure
  exact hclosure

/--
Closed-subjet restriction to the right coordinate for a separated difference.

In standard mathematical terms, assume `G` is continuous. If `(p, Z)` belongs
to the closed superjet at `(0, 0)` of `(ξ, η) ↦ G(ξ) - H(η)`, then the
negative right component of `p` and the negative right-right block of `Z`
belong to the closed subjet of `H` at `0`.
-/
theorem closedSubjet_right_of_closedSuperjet_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} (hG : Continuous G) {J : Jet (n + n)}
    (hJ : J ∈ ClosedSuperjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) 0) :
    (rightPointJet (n := n) J).neg ∈ ClosedSubjet Set.univ H 0 := by
  let F : Point (n + n) -> Real :=
    blockFunctionToPointFunction (n := n)
      (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))
  let T : ((Point (n + n) × Real) × Jet (n + n)) -> ((Point n × Real) × Jet n) :=
    fun z => ((pointRight (n := n) z.1.1, G (pointLeft (n := n) z.1.1) - z.1.2),
      (rightPointJet (n := n) z.2).neg)
  have hTcont : Continuous T := by
    have hbase : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) => z.1.1 :=
      continuous_fst.comp continuous_fst
    have hr : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) => z.1.2 :=
      continuous_snd.comp continuous_fst
    have hleftBase : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        pointLeft (n := n) z.1.1 :=
      continuous_pointLeft.comp hbase
    have hrightBase : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        pointRight (n := n) z.1.1 :=
      continuous_pointRight.comp hbase
    have hvalue : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        G (pointLeft (n := n) z.1.1) - z.1.2 :=
      (hG.comp hleftBase).sub hr
    have hleft : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        (pointRight (n := n) z.1.1, G (pointLeft (n := n) z.1.1) - z.1.2) :=
      hrightBase.prodMk hvalue
    have hjet : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        (rightPointJet (n := n) z.2).neg := by
      apply continuous_induced_rng.mpr
      change Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
        (((rightPointJet (n := n) z.2).neg).gradient,
          ((rightPointJet (n := n) z.2).neg).hessian)
      have hrightJet : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
          rightPointJet (n := n) z.2 :=
        continuous_rightPointJet.comp continuous_snd
      have hgrad : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
          -((rightPointJet (n := n) z.2).gradient) :=
        (Jet.continuous_gradient.comp hrightJet).neg
      have hhess : Continuous fun z : ((Point (n + n) × Real) × Jet (n + n)) =>
          -((rightPointJet (n := n) z.2).hessian) :=
        (Jet.continuous_hessian.comp hrightJet).neg
      simpa [Jet.neg] using hgrad.prodMk hhess
    simpa [T] using hleft.prodMk hjet
  have hT_mem : T ((0, F 0), J) ∈ closure (T '' SuperjetGraph Set.univ F) :=
    image_closure_subset_closure_image hTcont ⟨((0, F 0), J), hJ, rfl⟩
  have hsubset : T '' SuperjetGraph Set.univ F ⊆ SubjetGraph Set.univ H := by
    intro w hw
    rcases hw with ⟨v, hv, rfl⟩
    rcases v with ⟨⟨z, r⟩, K⟩
    rcases hv with ⟨_hz, hr, hK⟩
    change r = F z at hr
    subst r
    have hrightJet :
        (rightPointJet (n := n) K).neg ∈ Subjet Set.univ H (pointRight (n := n) z) :=
      subjet_right_of_superjet_blockFunctionToPointFunction_sub_at
        (n := n) (G := G) (H := H) (z := z) (J := K) hK
    have hvalue :
        G (pointLeft (n := n) z) - F z = H (pointRight (n := n) z) := by
      simp [F, blockFunctionToPointFunction, pointLeft, pointRight, blockPointLeft,
        blockPointRight]
    exact ⟨Set.mem_univ _, hvalue, hrightJet⟩
  have hclosure : T ((0, F 0), J) ∈ closure (SubjetGraph Set.univ H) :=
    closure_mono hsubset hT_mem
  have htarget :
      T ((0, F 0), J) = ((0, H 0), (rightPointJet (n := n) J).neg) := by
    simp [T, F, blockFunctionToPointFunction, pointLeft, pointRight, blockPointLeft,
      blockPointRight]
  change ((0, H 0), (rightPointJet (n := n) J).neg) ∈ closure (SubjetGraph Set.univ H)
  rw [htarget] at hclosure
  exact hclosure

/--
Separated closed semijets obtained from a selected block diagonal Hessian.

In quantified mathematical form, let `G, H : R^n -> R` be continuous
functions, let `Z` be a Hessian matrix on `R^n × R^n`, and let `X` and `Y` be
Hessian matrices on `R^n`. Suppose that `(0, Z)` belongs to the closed
superjet at `(0, 0)` of

`(ξ, η) ↦ G(ξ) - H(η)`,

and suppose that, after writing `Z` in block coordinates,

`Z = [X 0; 0 -Y]`.

Then `(0, X)` belongs to the closed superjet of `G` at `0`, and `(0, Y)`
belongs to the closed subjet of `H` at `0`.
-/
theorem closedSemijets_of_closedSuperjet_blockFunctionToPointFunction_sub_of_blockDiagonal
    {G H : Point n -> Real} (hG : Continuous G) (hH : Continuous H)
    {Z : Hessian (n + n)} {X Y : Hessian n}
    (hdiag : pointHessianToBlockHessian (n := n) Z = comparisonBlockDiagonal X Y)
    (hJ : ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈ ClosedSuperjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) 0) :
    ({ gradient := 0, hessian := X } : Jet n) ∈ ClosedSuperjet Set.univ G 0 ∧
      ({ gradient := 0, hessian := Y } : Jet n) ∈ ClosedSubjet Set.univ H 0 := by
  let J : Jet (n + n) := { gradient := 0, hessian := Z }
  have hleftHessian : leftPointHessian (n := n) Z = X := by
    ext i j
    have hentry := congr_fun (congr_fun hdiag (Sum.inl i)) (Sum.inl j)
    simpa [leftPointHessian, pointHessianToBlockHessian] using hentry
  have hrightHessian : rightPointHessian (n := n) Z = -Y := by
    ext i j
    have hentry := congr_fun (congr_fun hdiag (Sum.inr i)) (Sum.inr j)
    simpa [rightPointHessian, pointHessianToBlockHessian] using hentry
  have hleftJet :
      leftPointJet (n := n) J = ({ gradient := 0, hessian := X } : Jet n) := by
    apply (Jet.equivProd n).injective
    change (leftPointGradient (n := n) (0 : Point (n + n)), leftPointHessian (n := n) Z) =
      (0, X)
    exact Prod.ext (by ext i; rfl) hleftHessian
  have hrightJet :
      (rightPointJet (n := n) J).neg = ({ gradient := 0, hessian := Y } : Jet n) := by
    apply (Jet.equivProd n).injective
    change (-rightPointGradient (n := n) (0 : Point (n + n)), -rightPointHessian (n := n) Z) =
      (0, Y)
    exact Prod.ext (by ext i; simp [rightPointGradient]) (by simp [hrightHessian])
  have hleftMem :
      leftPointJet (n := n) J ∈ ClosedSuperjet Set.univ G 0 :=
    closedSuperjet_left_of_closedSuperjet_blockFunctionToPointFunction_sub
      (n := n) (G := G) (H := H) hH hJ
  have hrightMem :
      (rightPointJet (n := n) J).neg ∈ ClosedSubjet Set.univ H 0 :=
    closedSubjet_right_of_closedSuperjet_blockFunctionToPointFunction_sub
      (n := n) (G := G) (H := H) hG hJ
  exact ⟨by simpa [hleftJet] using hleftMem, by simpa [hrightJet] using hrightMem⟩

/--
Separated closed semijets together with inherited block matrix bounds.

In quantified mathematical form, let `G, H : R^n -> R` be continuous
functions, let `(0, Z)` belong to the closed superjet at `(0, 0)` of
`(ξ, η) ↦ G(ξ) - H(η)`, and suppose that the block form of `Z` is
`[X 0; 0 -Y]`. If the block form of `Z` lies between matrices `lower` and
`upper` in the Loewner order, then `(0, X)` belongs to the closed superjet of
`G` at `0`, `(0, Y)` belongs to the closed subjet of `H` at `0`, and

`lower ≤ [X 0; 0 -Y] ≤ upper`.
-/
theorem closedSemijets_and_blockBounds_of_blockDiagonal_closedSuperjet
    {G H : Point n -> Real} (hG : Continuous G) (hH : Continuous H)
    {Z : Hessian (n + n)} {X Y : Hessian n} {lower upper : BlockHessian n}
    (hdiag : pointHessianToBlockHessian (n := n) Z = comparisonBlockDiagonal X Y)
    (hlower : lower <= pointHessianToBlockHessian (n := n) Z)
    (hupper : pointHessianToBlockHessian (n := n) Z <= upper)
    (hJ : ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈ ClosedSuperjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) 0) :
    ({ gradient := 0, hessian := X } : Jet n) ∈ ClosedSuperjet Set.univ G 0 ∧
      ({ gradient := 0, hessian := Y } : Jet n) ∈ ClosedSubjet Set.univ H 0 ∧
        lower <= comparisonBlockDiagonal X Y ∧ comparisonBlockDiagonal X Y <= upper := by
  rcases
    closedSemijets_of_closedSuperjet_blockFunctionToPointFunction_sub_of_blockDiagonal
      (n := n) (G := G) (H := H) hG hH hdiag hJ with
    ⟨hsuper, hsub⟩
  exact ⟨hsuper, hsub, by simpa [hdiag] using hlower, by simpa [hdiag] using hupper⟩

end ViscositySolns
