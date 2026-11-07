# Fixed-point theorems in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-fixed-point/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-fixed-point/actions/workflows/lean_action_ci.yml)

Fixed-point theorems in Lean 4 with Mathlib, as a Lake package meant to be imported by other
projects. It currently proves **Brouwer's fixed-point theorem**: every continuous map of a
nonempty compact convex subset of a finite-dimensional real normed space into itself has a fixed
point; and the **no-retraction theorem** for the closed unit ball. Kakutani's and Schauder's
fixed-point theorems are planned, under `FixedPoint/Kakutani/` and `FixedPoint/Schauder/`.

## What is proved

The declarations are in the namespace `Brouwer`. `E` is a finite-dimensional real inner product
space (`[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`), for instance
`EuclideanSpace ℝ (Fin n)`; `V` is a finite-dimensional real normed space.

- [`Brouwer.exists_fixedPoint`](FixedPoint/Brouwer/Convex.lean#L46), Brouwer's theorem for compact
  convex sets:

  ```lean
  theorem exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
      (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
      ∃ x ∈ s, f x = x
  ```

- [`Brouwer.exists_fixedPoint_continuousMap`](FixedPoint/Brouwer/Convex.lean#L65), the same for
  `C(s, s)`:

  ```lean
  theorem exists_fixedPoint_continuousMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
      (hne : s.Nonempty) (f : C(s, s)) : ∃ x, f x = x
  ```

- [`Brouwer.exists_fixedPoint_closedBall`](FixedPoint/Brouwer/Ball.lean#L130), Brouwer's theorem
  for closed balls:

  ```lean
  theorem exists_fixedPoint_closedBall {c : E} {R : ℝ} (hR : 0 ≤ R) {f : E → E}
      (hmaps : MapsTo f (closedBall c R) (closedBall c R)) (hf : ContinuousOn f (closedBall c R)) :
      ∃ x ∈ closedBall c R, f x = x
  ```

- [`Brouwer.no_retraction`](FixedPoint/Brouwer/Ball.lean#L159), the no-retraction theorem:

  ```lean
  theorem no_retraction :
      ¬ ∃ r : E → E, ContinuousOn r (closedBall 0 1) ∧ MapsTo r (closedBall 0 1) (sphere 0 1) ∧
        ∀ x ∈ sphere (0 : E) 1, r x = x
  ```

On the way, for `C¹` maps:
[`Brouwer.no_contDiffAt_retraction`](FixedPoint/Brouwer/SmoothRetraction.lean#L115) (no map that is
`C¹` at every point of the closed unit ball maps it into the sphere and fixes the sphere) and
[`Brouwer.exists_fixedPoint_of_contDiffAt`](FixedPoint/Brouwer/SmoothFixedPoint.lean#L96) (a map that
is `C¹` at every point of the closed unit ball and maps it into itself has a fixed point there).

There is no `sorry`, `axiom` or `native_decide`. `lake env lean scripts/Audit.lean` prints the
axioms of the main theorems and checks that every declaration of the library depends only on
`propext`, `Classical.choice` and `Quot.sound`; it also checks that the theorems apply in the
forms `∀ s : Set V, Convex ℝ s → IsCompact s → s.Nonempty → ∀ f : V → V, MapsTo f s s →
ContinuousOn f s → ∃ x ∈ s, f x = x` and, for `EuclideanSpace ℝ (Fin n)`, the no-retraction
theorem.

## Method

The proof is analytic, along the lines of Milnor (1978) and Rogers (1980). It uses Mathlib's change
of variables formula, inverse function theorem for Lipschitz perturbations of the identity,
smoothing by convolution and nearest points in convex sets, and needs no homology, degree theory
or simplicial approximation.

1. **No `C¹` retraction** ([`SmoothRetraction.lean`](FixedPoint/Brouwer/SmoothRetraction.lean)).
   Let `r` be `C¹` on the closed unit ball `B̄`, with `r(B̄) ⊆ S` and `r = id` on the sphere `S`.
   Put `g = r - id`, `L`-Lipschitz on `B̄`, and `f_t = id + t g`. For `0 < t < 1/(L + 1)`,
   `f_t` is injective on the open ball `B`, maps it into itself, and has open image
   (`ApproximatesLinearOn.open_image`); since `f_t` fixes `S`, the image is also closed in `B`,
   so `f_t(B) = B`. The change of variables formula
   (`integral_image_eq_integral_abs_det_fderiv_smul`) gives `∫_B det Df_t = vol B`, the
   determinant being positive as `‖t Dg‖ < 1`. The left side is a polynomial in `t`
   ([`DetPolynomial.lean`](FixedPoint/Brouwer/DetPolynomial.lean): `det (1 + t A)` is written by
   Lagrange interpolation through its values at `t = 0, 1, …, dim E`), so it equals `vol B` for
   every `t`. But at `t = 1` it is `∫_B det Dr = 0`, since `‖r‖ = 1` makes the range of `Dr x`
   orthogonal to `r x`.
2. **`C¹` Brouwer** ([`SmoothFixedPoint.lean`](FixedPoint/Brouwer/SmoothFixedPoint.lean)). If a
   `C¹` self-map `q` of `B̄` had no fixed point, the point where the ray from `q x` through `x`
   leaves `B̄`, `x + λ(x) (x - q x)` with `λ` the larger root of a quadratic equation whose
   discriminant is positive on `B̄`, would be a `C¹` retraction onto `S`.
3. **Continuous Brouwer for balls** ([`Ball.lean`](FixedPoint/Brouwer/Ball.lean)). If a continuous
   self-map `f` of `B̄` had no fixed point, `‖f x - x‖ ≥ ε > 0` on `B̄`. Extended to `E` through the
   radial retraction and smoothed by convolution with a bump function
   (`Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`), then divided by `1 + η`, `f`
   is approximated within `ε` by a smooth self-map of `B̄`, whose fixed point would contradict the
   bound. Other balls follow by an affine change of variables, and a retraction `r` onto `S` would
   make `-r` a self-map of `B̄` without fixed point.
4. **Compact convex sets** ([`Convex.lean`](FixedPoint/Brouwer/Convex.lean)). A linear isomorphism
   `V ≃L[ℝ] EuclideanSpace ℝ (Fin n)` reduces to an inner product space. There a nonempty compact
   convex `s` lies in a closed ball `B̄` and is a retract of the space through the `1`-Lipschitz
   nearest-point map `π` ([`NearestPoint.lean`](FixedPoint/Brouwer/NearestPoint.lean)); a fixed point
   `x` of `f ∘ π` on `B̄` lies in `s`, so `π x = x` and `f x = x`.

The library has about 790 lines in six modules, and builds in about 15 seconds once Mathlib is
compiled.

References:

- J. Milnor, *Analytic proofs of the "hairy ball theorem" and the Brouwer fixed point theorem*,
  Amer. Math. Monthly 85 (1978), 521–524.
- C. A. Rogers, *A less strange version of Milnor's proof of Brouwer's fixed-point theorem*,
  Amer. Math. Monthly 87 (1980), 525–527.
- P. D. Lax, *Change of variables in multiple integrals*, Amer. Math. Monthly 106 (1999), 497–501,
  where Brouwer's theorem is a corollary of the change of variables formula.

The full texts of these papers were not available to us; the proof follows the standard argument
that they are known for, and was not compared with them line by line.

## Using it from another Lake project

Add to the `lakefile.toml` of your project:

```toml
[[require]]
name = "FixedPoint"
git = "https://github.com/vltanh/lean4-fixed-point"
rev = "<commit>"
```

and import the modules you need, for instance `public import FixedPoint.Brouwer.Convex` in a
module, or `import FixedPoint` for everything. The package requires Mathlib `v4.36.0-rc2`; your
project should use the same Mathlib version.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build
lake env lean scripts/Audit.lean   # axioms
```

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

## Layout

| Path | Content |
| --- | --- |
| [`FixedPoint.lean`](FixedPoint.lean) | imports the whole library |
| [`FixedPoint/Brouwer.lean`](FixedPoint/Brouwer.lean) | imports Brouwer's theorem and its lemmas |
| [`FixedPoint/Brouwer/DetPolynomial.lean`](FixedPoint/Brouwer/DetPolynomial.lean) | `det (1 + t A)` and its integrals are polynomials in `t`; `det (1 + A) > 0` for `‖A‖ < 1` |
| [`FixedPoint/Brouwer/SmoothRetraction.lean`](FixedPoint/Brouwer/SmoothRetraction.lean) | no `C¹` retraction of the closed unit ball onto the sphere |
| [`FixedPoint/Brouwer/SmoothFixedPoint.lean`](FixedPoint/Brouwer/SmoothFixedPoint.lean) | Brouwer's theorem for `C¹` maps of the closed unit ball |
| [`FixedPoint/Brouwer/Ball.lean`](FixedPoint/Brouwer/Ball.lean) | Brouwer's theorem for closed balls, the no-retraction theorem |
| [`FixedPoint/Brouwer/NearestPoint.lean`](FixedPoint/Brouwer/NearestPoint.lean) | the nearest-point retraction onto a closed convex set |
| [`FixedPoint/Brouwer/Convex.lean`](FixedPoint/Brouwer/Convex.lean) | Brouwer's theorem for compact convex sets |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| `.github/workflows/` | CI: build, audit, line lengths |

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code, at the request of
  The-Anh Vu-Le, on 7 November 2026.
- The proof was written without consulting other formalizations of Brouwer's theorem. No person
  has reviewed the proofs; Lean has checked them.

## License

Apache-2.0; see [LICENSE](LICENSE).
