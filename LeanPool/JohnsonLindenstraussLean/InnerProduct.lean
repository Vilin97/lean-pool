import JL.NormPreservation

/-!
# Inner-product preservation (unquantized Gaussian-projection corollary)

Via the polarization identity `⟪u, v⟫ = (‖u+v‖² - ‖u-v‖²)/4`, a *linear* map that
preserves the squared norms of `u+v` and `u-v` to within a relative error `ε` also
preserves the inner product `⟪u, v⟫`:

`|⟪f u, f v⟫ - ⟪u, v⟫| ≤ ε · (‖u‖² + ‖v‖²) / 2`.

This is the *unquantized* inner-product corollary of full-precision Gaussian Johnson–Lindenstrauss:
combined with the distributional norm-preservation bound applied to `u+v` and `u-v`, the Gaussian
projection preserves inner products with high probability. It is the Dasgupta–Gupta baseline that
quantized schemes (QJL / TurboQuant) are motivated by and compared against — it is *not* the
mechanism behind QJL's one-bit guarantee, which instead rests on the asymmetric sign-product
identity (`JL/QJL.lean`).
-/

open scoped RealInnerProductSpace

namespace JL

/-- **Inner-product preservation via polarization.** A linear map `f` preserving the
squared norms of `u+v` and `u-v` within relative error `ε` preserves `⟪u, v⟫` within
`ε · (‖u‖² + ‖v‖²)/2`. -/
theorem inner_product_preservation {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E →ₗ[ℝ] F) (u v : E) {ε : ℝ}
    (hplus : |‖f (u + v)‖ ^ 2 - ‖u + v‖ ^ 2| ≤ ε * ‖u + v‖ ^ 2)
    (hminus : |‖f (u - v)‖ ^ 2 - ‖u - v‖ ^ 2| ≤ ε * ‖u - v‖ ^ 2) :
    |⟪f u, f v⟫ - ⟪u, v⟫| ≤ ε * (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
  have hu : ⟪u, v⟫ = (‖u + v‖ ^ 2 - ‖u - v‖ ^ 2) / 4 := by
    rw [norm_add_sq_real, norm_sub_sq_real]; ring
  have hfu : ⟪f u, f v⟫ = (‖f (u + v)‖ ^ 2 - ‖f (u - v)‖ ^ 2) / 4 := by
    rw [map_add, map_sub, norm_add_sq_real, norm_sub_sq_real]; ring
  have hpar : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    rw [norm_add_sq_real, norm_sub_sq_real]; ring
  have htri :
      |(‖f (u + v)‖ ^ 2 - ‖u + v‖ ^ 2) - (‖f (u - v)‖ ^ 2 - ‖u - v‖ ^ 2)|
        ≤ ε * ‖u + v‖ ^ 2 + ε * ‖u - v‖ ^ 2 := by
    calc |(‖f (u + v)‖ ^ 2 - ‖u + v‖ ^ 2) - (‖f (u - v)‖ ^ 2 - ‖u - v‖ ^ 2)|
        = |(‖f (u + v)‖ ^ 2 - ‖u + v‖ ^ 2) + -(‖f (u - v)‖ ^ 2 - ‖u - v‖ ^ 2)| := by
          rw [sub_eq_add_neg]
      _ ≤ |‖f (u + v)‖ ^ 2 - ‖u + v‖ ^ 2| + |-(‖f (u - v)‖ ^ 2 - ‖u - v‖ ^ 2)| := abs_add_le _ _
      _ = |‖f (u + v)‖ ^ 2 - ‖u + v‖ ^ 2| + |‖f (u - v)‖ ^ 2 - ‖u - v‖ ^ 2| := by rw [abs_neg]
      _ ≤ ε * ‖u + v‖ ^ 2 + ε * ‖u - v‖ ^ 2 := add_le_add hplus hminus
  rw [hfu, hu, show (‖f (u + v)‖ ^ 2 - ‖f (u - v)‖ ^ 2) / 4 - (‖u + v‖ ^ 2 - ‖u - v‖ ^ 2) / 4
      = ((‖f (u + v)‖ ^ 2 - ‖u + v‖ ^ 2) - (‖f (u - v)‖ ^ 2 - ‖u - v‖ ^ 2)) / 4 by ring,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  have hRHS : ε * (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 * 4 = ε * ‖u + v‖ ^ 2 + ε * ‖u - v‖ ^ 2 := by
    rw [show ε * ‖u + v‖ ^ 2 + ε * ‖u - v‖ ^ 2 = ε * (‖u + v‖ ^ 2 + ‖u - v‖ ^ 2) by ring, hpar]
    ring
  rw [hRHS]
  exact htri

end JL
