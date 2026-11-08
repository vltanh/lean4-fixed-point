# Fixed-point theorems in Lean: details

The statements in Lean, what the axiom audit checks, the method of proof step by step, the other
formal proofs of Brouwer's theorem, and the files. The [README](../README.md) has the overview.

- [Statements](#statements)
- [The axiom audit](#the-axiom-audit)
- [Method](#method)
- [Other formalizations](#other-formalizations)
- [Files](#files)

## Statements

The declarations are in the namespace `Brouwer`. `E` is a finite-dimensional real inner product
space (`[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`), for instance
`EuclideanSpace ℝ (Fin n)`; `V` is a finite-dimensional real normed space.

[`Brouwer.exists_fixedPoint`](../FixedPoint/Brouwer/Convex.lean#L46), Brouwer's theorem for
compact convex sets:

```lean
theorem exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x
```

[`Brouwer.exists_fixedPoint_continuousMap`](../FixedPoint/Brouwer/Convex.lean#L65), the same for
`C(s, s)`:

```lean
theorem exists_fixedPoint_continuousMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) (f : C(s, s)) : ∃ x, f x = x
```

[`Brouwer.exists_fixedPoint_closedBall`](../FixedPoint/Brouwer/Ball.lean#L130), Brouwer's theorem
for closed balls:

```lean
theorem exists_fixedPoint_closedBall {c : E} {R : ℝ} (hR : 0 ≤ R) {f : E → E}
    (hmaps : MapsTo f (closedBall c R) (closedBall c R)) (hf : ContinuousOn f (closedBall c R)) :
    ∃ x ∈ closedBall c R, f x = x
```

[`Brouwer.no_retraction`](../FixedPoint/Brouwer/Ball.lean#L159), the no-retraction theorem:

```lean
theorem no_retraction :
    ¬ ∃ r : E → E, ContinuousOn r (closedBall 0 1) ∧ MapsTo r (closedBall 0 1) (sphere 0 1) ∧
      ∀ x ∈ sphere (0 : E) 1, r x = x
```

On the way, for `C¹` maps:

- [`Brouwer.no_contDiffAt_retraction`](../FixedPoint/Brouwer/SmoothRetraction.lean#L115): no map
  that is `C¹` at every point of the closed unit ball maps it into the sphere and fixes the
  sphere;
- [`Brouwer.exists_fixedPoint_of_contDiffAt`](../FixedPoint/Brouwer/SmoothFixedPoint.lean#L96):
  a map that is `C¹` at every point of the closed unit ball and maps it into itself has a fixed
  point there.

## The axiom audit

`lake env lean scripts/Audit.lean` prints the axioms of the main theorems. It checks that they,
the Challenge's theorems as [`FixedPointSolution.lean`](../FixedPointSolution.lean) proves them,
and every declaration of the library depend only on `propext`, `Classical.choice` and
`Quot.sound`.

It also checks that the theorems apply in these forms:

- `∀ s : Set V, Convex ℝ s → IsCompact s → s.Nonempty → ∀ f : V → V, MapsTo f s s →
  ContinuousOn f s → ∃ x ∈ s, f x = x`;
- for `EuclideanSpace ℝ (Fin n)`, Brouwer's theorem for the closed unit ball and the
  no-retraction theorem.

## Method

The proof is analytic, along the lines of Milnor (1978) and Rogers (1980). It uses Mathlib's
change of variables formula, inverse function theorem for Lipschitz perturbations of the
identity, smoothing by convolution and nearest points in convex sets. It needs no homology,
degree theory or simplicial approximation.

1. **No `C¹` retraction** ([`SmoothRetraction.lean`](../FixedPoint/Brouwer/SmoothRetraction.lean)).
   Let `r` be `C¹` on the closed unit ball `B̄`, with `r(B̄) ⊆ S` and `r = id` on the sphere `S`.
   Put `g = r - id`, `L`-Lipschitz on `B̄`, and `f_t = id + t g`.
   - For `0 < t < 1/(L + 1)`, `f_t` is injective on the open ball `B`, maps it into itself, and
     has open image (`ApproximatesLinearOn.open_image`). Since `f_t` fixes `S`, the image is
     also closed in `B`, so `f_t(B) = B`.
   - The change of variables formula (`integral_image_eq_integral_abs_det_fderiv_smul`) gives
     `∫_B det Df_t = vol B`, the determinant being positive as `‖t Dg‖ < 1`.
   - The left side is a polynomial in `t`
     ([`DetPolynomial.lean`](../FixedPoint/Brouwer/DetPolynomial.lean): `det (1 + t A)` is
     written by Lagrange interpolation through its values at `t = 0, 1, …, dim E`), so it equals
     `vol B` for every `t`.
   - But at `t = 1` it is `∫_B det Dr = 0`, since `‖r‖ = 1` makes the range of `Dr x`
     orthogonal to `r x`.
2. **`C¹` Brouwer** ([`SmoothFixedPoint.lean`](../FixedPoint/Brouwer/SmoothFixedPoint.lean)). If a
   `C¹` self-map `q` of `B̄` had no fixed point, the point where the ray from `q x` through `x`
   leaves `B̄` would be a `C¹` retraction onto `S`. That point is `x + λ(x) (x - q x)`, with `λ`
   the larger root of a quadratic equation whose discriminant is positive on `B̄`.
3. **Continuous Brouwer for balls** ([`Ball.lean`](../FixedPoint/Brouwer/Ball.lean)). If a
   continuous self-map `f` of `B̄` had no fixed point, `‖f x - x‖ ≥ ε > 0` on `B̄`.
   - Extend `f` to `E` through the radial retraction, smooth it by convolution with a bump
     function (`Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`), then divide by
     `1 + η`. This approximates `f` within `ε` by a smooth self-map of `B̄`, whose fixed point
     would contradict the bound.
   - Other balls follow by an affine change of variables, and a retraction `r` onto `S` would
     make `-r` a self-map of `B̄` without fixed point.
4. **Compact convex sets** ([`Convex.lean`](../FixedPoint/Brouwer/Convex.lean)). A linear
   isomorphism `V ≃L[ℝ] EuclideanSpace ℝ (Fin n)` reduces to an inner product space. There a
   nonempty compact convex `s` lies in a closed ball `B̄` and is a retract of the space through
   the `1`-Lipschitz nearest-point map `π`
   ([`NearestPoint.lean`](../FixedPoint/Brouwer/NearestPoint.lean)). A fixed point `x` of
   `f ∘ π` on `B̄` lies in `s`, so `π x = x` and `f x = x`.

The proof follows the standard argument that Milnor's and Rogers's papers are known for; it was
not compared with their texts line by line. Brouwer's own proof is topological and is not the one
formalized here.

## Other formalizations

Brouwer's fixed-point theorem has other formal proofs; this one is independent of them. Mathlib
`v4.36.0-rc2` has no Brouwer fixed-point theorem.

- Lean 4 with Mathlib:
  - for nonempty compact convex sets in finite-dimensional real normed spaces, through Kuhn's
    cubical Sperner lemma, together with Kakutani's fixed-point theorem
    ([harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/blob/93a3eed3364281a9dbf9652bb52356a8db65057c/FixedPointTheorems/brouwer.lean),
    MIT licence);
  - in the plane, for nonempty compact convex subsets of `EuclideanSpace ℝ (Fin 2)`, through the
    fundamental group of the circle, as a step towards the Jordan curve theorem
    ([rkirov/jordan_pick](https://github.com/rkirov/jordan_pick/blob/b3c9b7cf7358bf81a077d78ad67e6e8247869ddd/JordanPick/JordanCurve/Brouwer.lean),
    part of the Palomar entry PALOMAR-2026-08-19-000001);
  - for the standard simplex and products of simplices, through Scarf's combinatorial theorem,
    towards Nash equilibria ([math-xmum/Brouwer](https://github.com/math-xmum/Brouwer); Y. Lyu
    and K. Li, [arXiv:2607.05987](https://arxiv.org/abs/2607.05987)).
- Lean 3 with mathlib: for compact convex sets in finite-dimensional real normed spaces, through
  singular homology, by Brendan Seamas Murphy
  ([Shamrock-Frost/BrouwerFixedPoint](https://github.com/Shamrock-Frost/BrouwerFixedPoint)).
- HOL Light: `BROUWER` in John Harrison's Multivariate library, for compact convex sets in
  `real^N`, now derived through the homological degree
  ([`Multivariate/degree.ml`](https://github.com/jrh13/hol-light/blob/master/Multivariate/degree.ml)).
- Isabelle/HOL: `brouwer` in
  [`HOL-Analysis/Brouwer_Fixpoint`](https://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/Brouwer_Fixpoint.html),
  translated from HOL Light by Robert Himmelmann, through Kuhn's combinatorial lemma.
- Mizar: K. Pąk, *Brouwer fixed point theorem in the general case*, Formalized Mathematics 19
  (2011), 151–153 ([doi:10.2478/v10037-011-0024-3](https://doi.org/10.2478/v10037-011-0024-3)),
  for compact convex sets with nonempty interior in `E^n`.
- Coq: the two-dimensional case, through winding numbers, in A. Brunel, *Non-constructive complex
  analysis in Coq*, TYPES 2011
  ([doi:10.4230/LIPIcs.TYPES.2011.1](https://doi.org/10.4230/LIPIcs.TYPES.2011.1)).

## Files

| Path | Content |
| --- | --- |
| [`FixedPoint.lean`](../FixedPoint.lean) | imports the whole library |
| [`FixedPoint/Brouwer.lean`](../FixedPoint/Brouwer.lean) | imports Brouwer's theorem and its lemmas |
| [`FixedPoint/Brouwer/DetPolynomial.lean`](../FixedPoint/Brouwer/DetPolynomial.lean) | `det (1 + t A)` and its integrals are polynomials in `t`; `det (1 + A) > 0` for `‖A‖ < 1` |
| [`FixedPoint/Brouwer/SmoothRetraction.lean`](../FixedPoint/Brouwer/SmoothRetraction.lean) | no `C¹` retraction of the closed unit ball onto the sphere |
| [`FixedPoint/Brouwer/SmoothFixedPoint.lean`](../FixedPoint/Brouwer/SmoothFixedPoint.lean) | Brouwer's theorem for `C¹` maps of the closed unit ball |
| [`FixedPoint/Brouwer/Ball.lean`](../FixedPoint/Brouwer/Ball.lean) | Brouwer's theorem for closed balls, the no-retraction theorem |
| [`FixedPoint/Brouwer/NearestPoint.lean`](../FixedPoint/Brouwer/NearestPoint.lean) | the nearest-point retraction onto a closed convex set |
| [`FixedPoint/Brouwer/Convex.lean`](../FixedPoint/Brouwer/Convex.lean) | Brouwer's theorem for compact convex sets |
| [`FixedPointChallenge.lean`](../FixedPointChallenge.lean), [`FixedPointSolution.lean`](../FixedPointSolution.lean), [`comparator.json`](../comparator.json), [`formalization.yaml`](../formalization.yaml) | Palomar: the statements of record, their proofs, the Comparator configuration, the metadata |
| [`scripts/Audit.lean`](../scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml) | CI: build, audit, import list of the audit, line lengths |
