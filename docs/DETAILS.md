# Fixed-point theorems in Lean: details

The statements in Lean, what the axiom audit checks, the method of proof step by step, where the
proofs depart from the sources, the other formal proofs of the three theorems, and the files. The
[README](../README.md) has the overview.

- [Statements](#statements): [Brouwer](#brouwer), [Kakutani](#kakutani), [Schauder](#schauder)
- [The axiom audit](#the-axiom-audit)
- [Method](#method): [Brouwer](#brouwers-theorem), [Kakutani](#kakutanis-theorem),
  [Schauder](#schauders-theorem)
- [Departures from the sources](#departures-from-the-sources)
- [Other formalizations](#other-formalizations)
- [Files](#files)

## Statements

### Brouwer

The declarations are in the namespace `Brouwer`. `E` is a finite-dimensional real inner product
space (`[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`), for instance
`EuclideanSpace ℝ (Fin n)`; `V` is a finite-dimensional real normed space.

[`Brouwer.exists_fixedPoint`](../FixedPoint/Brouwer/Convex.lean#L54), Brouwer's theorem for
compact convex sets:

```lean
theorem exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x
```

[`Brouwer.exists_fixedPoint_continuousMap`](../FixedPoint/Brouwer/Convex.lean#L64), the same for
`C(s, s)`:

```lean
theorem exists_fixedPoint_continuousMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) (f : C(s, s)) : ∃ x, f x = x
```

[`Brouwer.exists_fixedPoint_closedBall`](../FixedPoint/Brouwer/Ball.lean#L135), Brouwer's theorem
for closed balls:

```lean
theorem exists_fixedPoint_closedBall {c : E} {R : ℝ} (hR : 0 ≤ R) {f : E → E}
    (hmaps : MapsTo f (closedBall c R) (closedBall c R)) (hf : ContinuousOn f (closedBall c R)) :
    ∃ x ∈ closedBall c R, f x = x
```

[`Brouwer.no_retraction`](../FixedPoint/Brouwer/Ball.lean#L164), the no-retraction theorem:

```lean
theorem no_retraction :
    ¬ ∃ r : E → E, ContinuousOn r (closedBall 0 1) ∧ MapsTo r (closedBall 0 1) (sphere 0 1) ∧
      ∀ x ∈ sphere (0 : E) 1, r x = x
```

On the way, for `C¹` maps:

- [`Brouwer.no_contDiffAt_retraction`](../FixedPoint/Brouwer/SmoothRetraction.lean#L120): no map
  that is `C¹` at every point of the closed unit ball maps it into the sphere and fixes the
  sphere;
- [`Brouwer.exists_fixedPoint_of_contDiffAt`](../FixedPoint/Brouwer/SmoothFixedPoint.lean#L101):
  a map that is `C¹` at every point of the closed unit ball and maps it into itself has a fixed
  point there.

A second proof, through the lemma of Knaster, Kuratowski and Mazurkiewicz (KKM):

- [`Brouwer.KKM.exists_fixedPoint`](../FixedPoint/Brouwer/KKM.lean#L190): `Brouwer.exists_fixedPoint`
  again; `Brouwer.KKM.exists_fixedPoint_stdSimplex` for the standard simplex;
- [`Brouwer.KKM.exists_mem_iInter`](../FixedPoint/Brouwer/KKM.lean#L60), the KKM lemma: if closed
  sets `F 0, …, F r` are such that every face of the standard simplex spanned by vertices `e i`,
  `i ∈ I`, is covered by the `F i`, `i ∈ I`, then they have a common point in the simplex:

  ```lean
  theorem exists_mem_iInter {r : ℕ} {F : Fin (r + 1) → Set (Fin (r + 1) → ℝ)}
      (hF : ∀ i, IsClosed (F i))
      (hface : ∀ I : Finset (Fin (r + 1)),
        convexHull ℝ ((fun i ↦ (Pi.single i 1 : Fin (r + 1) → ℝ)) '' I) ⊆ ⋃ i ∈ I, F i) :
      ∃ x ∈ simplex r, ∀ i, x ∈ F i
  ```
- [`Sperner.count_eq_one`](../FixedPoint/Common/Sperner.lean#L399), Sperner's lemma: for a labeling
  of the standard simplex that gives each point `v` a label `i` with `v i ≠ 0`, the simplices of
  the `n`-th barycentric subdivision that carry all the labels are odd in number.

### Kakutani

The declarations are in the namespace `Kakutani`. A set-valued map is a function
`φ : V → Set V`, of which only the values at points of `s` play a part. Its graph over `s`,
`{p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}`, is closed in `V × V` exactly when it is closed in `s × s`
(`s` being closed), and exactly when `φ` is upper semicontinuous in Kakutani's sense: `xₙ → x` in
`s`, `yₙ ∈ φ xₙ` and `yₙ → y` imply `y ∈ φ x`
([`Kakutani.isClosed_graph_iff_seq`](../FixedPoint/Kakutani/Convex.lean#L94)). The values `φ x`
are then closed, and need not be required closed.

[`Kakutani.exists_fixedPoint`](../FixedPoint/Kakutani/Convex.lean#L81), Kakutani's theorem for
compact convex sets of a finite-dimensional real normed space:

```lean
theorem exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s)
    (hφne : ∀ x ∈ s, (φ x).Nonempty) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x
```

On the way:

- [`Kakutani.exists_fixedPoint_simplex`](../FixedPoint/Kakutani/Simplex.lean#L147), Kakutani's
  Theorem 1: the same for a closed simplex `S.closedInterior`, `S : Affine.Simplex ℝ V r`, in a
  real normed space of any dimension;
- [`Kakutani.exists_fixedPoint_stdSimplex`](../FixedPoint/Kakutani/Simplex.lean#L70): the same for
  the standard simplex of `Fin (r + 1) → ℝ`, where Kakutani's proof is carried out;
- [`Kakutani.exists_fixedPoint_convexHull`](../FixedPoint/Kakutani/Simplex.lean#L159): the same
  for the convex hull of a nonempty finite set;
- [`Kakutani.Selection.exists_fixedPoint`](../FixedPoint/Kakutani/Selection.lean#L118):
  `Kakutani.exists_fixedPoint` again, by a second proof;
- [`Kakutani.exists_fixedPoint_of_innerProductSpace`](../FixedPoint/Kakutani/Convex.lean#L53),
  Kakutani's Corollary: the same for a finite-dimensional real inner product space, that is, a
  Euclidean space.

### Schauder

The declarations are in the namespace `Schauder`. `E` is a real normed space of any dimension.

[`Schauder.exists_fixedPoint`](../FixedPoint/Schauder/Convex.lean#L178), Schauder's theorem for
compact convex sets (Satz I); the space need not be complete. Schauder states Satz I for complete
metric linear spaces, which need not be normed ([departures](#departures-from-the-sources)):

```lean
theorem exists_fixedPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty) {f : E → E}
    (hmaps : MapsTo f s s) (hf : ContinuousOn f s) : ∃ x ∈ s, f x = x
```

[`Schauder.exists_fixedPoint_of_isCompact_closure_image`](../FixedPoint/Schauder/CompactImage.lean#L50),
Schauder's theorem for closed convex sets of a Banach space and maps with relatively compact image
(Satz II; Schauder's "kompakt" is Fréchet's, that is, relatively compact):

```lean
theorem exists_fixedPoint_of_isCompact_closure_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {s : Set E} (hconv : Convex ℝ s) (hcl : IsClosed s)
    (hne : s.Nonempty) {f : E → E} (hmaps : MapsTo f s s) (hf : ContinuousOn f s)
    (himg : IsCompact (closure (f '' s))) : ∃ x ∈ s, f x = x
```

On the way:

- [`Schauder.exists_fixedPoint_continuousMap`](../FixedPoint/Schauder/Convex.lean#L187): the first
  form for `f : C(s, s)`;
- [`Schauder.isCompact_closedConvexHull`](../FixedPoint/Schauder/CompactImage.lean#L42), Mazur's
  theorem: in a real Banach space, the closed convex hull of a totally bounded set is compact;
- [`Schauder.Projection.exists_fixedPoint`](../FixedPoint/Schauder/Projection.lean#L65):
  `Schauder.exists_fixedPoint` again, by a second proof;
- [`Brouwer.exists_fixedPoint_convexHull_of_finite`](../FixedPoint/Brouwer/Polytope.lean#L29):
  Brouwer's theorem for the convex hull of a nonempty finite set in a real normed space of any
  dimension, used by the second proof.

## The axiom audit

`lake env lean scripts/Audit.lean` prints the axioms of the main theorems. It checks that they,
the Challenge's theorems as [`FixedPointSolution.lean`](../FixedPointSolution.lean) proves them,
and every declaration of the library depend only on `propext`, `Classical.choice` and
`Quot.sound`.

It also checks that the theorems apply in these forms:

- `∀ s : Set V, Convex ℝ s → IsCompact s → s.Nonempty → ∀ f : V → V, MapsTo f s s →
  ContinuousOn f s → ∃ x ∈ s, f x = x`, for Brouwer's theorem, and the same for a real normed
  space of any dimension, for Schauder's;
- for `EuclideanSpace ℝ (Fin n)`, Brouwer's theorem for the closed unit ball and the
  no-retraction theorem;
- Kakutani's theorem in the form `∀ s, … → ∀ φ, … → ∃ x ∈ s, x ∈ φ x`;
- Schauder's second form for the Hilbert space `ℓ²(ℕ)` (`lp (fun _ : ℕ ↦ ℝ) 2`).

Finally, `#independent` walks through every declaration that a proof uses, and checks that the
proof of Brouwer's theorem through the KKM lemma, and the proofs of Kakutani's and Schauder's
theorems, never use the analytic proof (`Brouwer.no_contDiffAt_retraction`).

## Method

### Brouwer's theorem

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
   ([`NearestPoint.lean`](../FixedPoint/Common/NearestPoint.lean)). A fixed point `x` of
   `f ∘ π` on `B̄` lies in `s`, so `π x = x` and `f x = x`.

The proof follows the standard argument that Milnor's and Rogers's papers are known for; it was
not compared with their texts line by line. Brouwer's own proof is topological and is not the one
formalized here.

**Second proof, through the KKM lemma**, after Knaster, Kuratowski and Mazurkiewicz (1929)
([`Sperner.lean`](../FixedPoint/Common/Sperner.lean), [`KKM.lean`](../FixedPoint/Brouwer/KKM.lean)).
Kakutani and Schauder cite this proof of Brouwer's theorem, and their formal proofs use it.

1. **Sperner's lemma** (`Sperner.count_eq_one`), KKM's Hilfssatz, by their count, mod 2 and by
   induction on the dimension: the pairs of a simplex of the subdivision and a facet labeled
   `0, …, r - 1` are counted by simplices (a simplex labeled `0, …, r` has one such facet; one
   labeled `0, …, r - 1` with a repeated label has two; any other none) and by facets (a facet
   inside the simplex lies in two simplices, one on the boundary in one). The counts are defined
   by recursion on the level of the barycentric subdivision. The facets inside pair up because the
   pieces of the orderings `σ` and `σ * swap k (k + 1)` agree on their `k`-th facet
   (`Sperner.vmap_mul_swap`), and the facets on the boundary form the subdivisions of the faces
   (`Sperner.vmap_pieceOf_facet`). For a Sperner labeling only the face `x r = 0` has facets
   labeled `0, …, r - 1`, which closes the induction.
2. **The KKM lemma** (`Brouwer.KKM.exists_mem_iInter`). Label each point `v` by an `i` with
   `v i ≠ 0` and `v ∈ F i`, which exists by the hypothesis on the face spanned by the `e i` with
   `v i ≠ 0`. Sperner's lemma gives, in each subdivision, a simplex with a vertex in each `F i`;
   along a subsequence they converge to a point of every `F i`.
3. **Brouwer for the simplex** (`Brouwer.KKM.exists_fixedPoint_stdSimplex`), with
   `F i = {x | f x i ≤ x i}`: on the face spanned by the `e i`, `i ∈ I`,
   `∑ i ∈ I, f x i ≤ 1 = ∑ i ∈ I, x i`, so some `f x i ≤ x i`; and at a common point `f x = x`.
4. **Compact convex sets** (`Brouwer.KKM.exists_fixedPoint`). `s` lies in a simplex with
   continuous barycentric coordinates `μ` (`FixedPoint.exists_simplex_coords`) and is a retract
   through the nearest-point map `π`; a fixed point `u` of `u ↦ μ (f (π (∑ u k • v k)))` on the
   standard simplex gives the fixed point `∑ u k • v k` of `f`.

### Kakutani's theorem

Kakutani's proof ([`Subdivision.lean`](../FixedPoint/Common/Subdivision.lean),
[`Limit.lean`](../FixedPoint/Kakutani/Limit.lean),
[`Simplex.lean`](../FixedPoint/Kakutani/Simplex.lean),
[`Convex.lean`](../FixedPoint/Kakutani/Convex.lean)).

1. **Barycentric subdivisions** (`BarycentricSubdivision`). The pieces of the first barycentric
   subdivision of the standard simplex `Δ ⊆ ℝ^{r+1}` are indexed by the orderings `σ` of the
   coordinates: the piece of `σ` holds the points with `x (σ 0) ≥ ⋯ ≥ x (σ r)`, and is the image
   of `Δ` under the linear map `vmap σ` sending `e k` to the barycenter of
   `e (σ 0), …, e (σ k)`. The `n`-th subdivision consists of the images of the pieces of the
   `(n - 1)`-th under these maps. For `x ∈ Δ`, `verts n x` are the vertices of a piece that
   contains `x` and `coords n x` the barycentric coordinates of `x` in it.
   - `interp n g x = ∑ coords n x k • g (verts n x k)` is linear on each piece, with the value
     `g v` at each vertex `v`. It is continuous for every `g` (`continuousOn_interp`): two
     orderings of `x` give the same coordinates, and the same vertices wherever a coordinate is
     not zero, so the formulas on two pieces agree where the pieces meet.
   - The vertices are within `2 (r / (r + 1)) ^ n` of `x` (`dist_verts_le`), as each `vmap σ`
     contracts `ℓ¹` distances in `Δ` by `r / (r + 1)`.
2. **Approximation and Brouwer** (Theorem 1, `Kakutani.exists_fixedPoint_stdSimplex`). Pick
   `y v ∈ φ v` for each `v ∈ Δ`. Kakutani's map `φₙ = interp n y` sends `Δ` continuously into
   itself, so has a fixed point `xₙ` by Brouwer's theorem in KKM's proof, Kakutani's reference [1]. Then `xₙ = ∑ λₙᵢ y (xₙᵢ)`, where `xₙᵢ` are the vertices of
   the piece containing `xₙ` and `λₙ` its coordinates there.
3. **Limit** (`Kakutani.exists_mem_self_of_approx`). Along a subsequence `xₙ → x₀`, `λₙ → λ₀` and
   `y (xₙᵢ) → y₀ᵢ`; the vertices `xₙᵢ` converge to `x₀`, so `y₀ᵢ ∈ φ x₀` as the graph is closed,
   and `x₀ = ∑ λ₀ᵢ y₀ᵢ ∈ φ x₀` as `φ x₀` is convex.
4. **Other simplices** (`Kakutani.exists_fixedPoint_simplex`,
   `Kakutani.exists_fixedPoint_convexHull`). The convex hull of points `v 0, …, v r` is the image
   of `Δ` under `A u = ∑ u k • v k`; Theorem 1 on `Δ` for `u ↦ {u' ∈ Δ | A u' ∈ φ (A u)}` gives it.
5. **Compact convex sets** (Corollary, `Kakutani.exists_fixedPoint_of_innerProductSpace`). In an
   inner product space, `s` lies in a simplex `K`, with vertices `v₀ = -R ∑ bᵢ` and
   `v₀ + 2 d R bᵢ` for an orthonormal basis `b`, `d = dim`, `s ⊆ closedBall 0 R`
   (`Kakutani.exists_subset_convexHull_simplex`), and is a retract of the space through the
   nearest-point map `π`. The map `x ↦ φ (π x)` satisfies the hypotheses on
   `K`, so `x ∈ φ (π x)` for some `x`; then `x ∈ s`, `π x = x` and `x ∈ φ x`. A linear isomorphism
   with `EuclideanSpace ℝ (Fin n)` gives finite-dimensional normed spaces
   (`Kakutani.exists_fixedPoint`).

A second proof, `Kakutani.Selection.exists_fixedPoint`
([`Selection.lean`](../FixedPoint/Kakutani/Selection.lean)), replaces steps 1 and 2
by the average of the values `y c ∈ φ c` at the points `c` of a finite `δ`-net, weighted by the
partition of unity of Schauder's projection, and Carathéodory's theorem; it needs no simplex.

### Schauder's theorem

Schauder's proof ([`Convex.lean`](../FixedPoint/Schauder/Convex.lean),
[`Limit.lean`](../FixedPoint/Schauder/Limit.lean),
[`CompactImage.lean`](../FixedPoint/Schauder/CompactImage.lean)).

1. **An `ε`-net and its hull** (`Schauder.exists_dist_lt`). Take `δ` with `‖f y - f z‖ < ε` for
   `y, z ∈ s` within `δ`, and a finite `ε`-net `ξ 0, …, ξ m` of `s`. Its convex hull `H ⊆ s` is
   the image of the standard simplex `Δ` under `A u = ∑ u k • ξ k`.
2. **Simplicial approximation.** On the `n`-th barycentric subdivision of `Δ`, fine enough that
   `A` maps its simplices to sets of diameter less than `min ε (δ / 2)`, send each vertex `v` to
   the vertex `e j` of `Δ` with `‖ξ j - f (A v)‖ < ε`, and extend linearly on each simplex
   (`BarycentricSubdivision.interp`): through `A`, Schauder's simplicial map of `H` into itself.
3. **Brouwer** in KKM's proof, which Schauder cites, gives a fixed point `u`. If `w k` are the
   vertices of a simplex containing `u` and `λ` its coordinates there,
   `x = A u = ∑ λ k • ξ (j (w k))`.
4. **A vertex moved by less than `3 ε`.** For `d = A (w 0)`: `‖d - x‖ < ε`; each `ξ (j (w k))` is
   within `ε` of `f (A (w k))`, which is within `ε` of `f d`, so `‖x - f d‖ ≤ 2 ε` by convexity;
   hence `‖f d - d‖ < 3 ε`, Schauder's bound, reached by another estimate than his (below).
5. **Fixed point** (`Schauder.exists_fixedPoint_of_forall_dist_lt`). As `ε` is arbitrary, a
   subsequence of such points converges to a fixed point.
6. **Second form** (`Schauder.exists_fixedPoint_of_isCompact_closure_image`). The closed convex
   hull `K` of `f '' s` is compact by Mazur's theorem, lies in `s`, and `f` maps it into
   `f '' s ⊆ K`; Satz I applies to `K`. Completeness is used only by Mazur's theorem.

A second proof, `Schauder.Projection.exists_fixedPoint`
([`Projection.lean`](../FixedPoint/Schauder/Projection.lean)), replaces steps 2 to 4 by Schauder's
projection `P x = (∑ c ∈ t, wᶜ(x))⁻¹ • ∑ c ∈ t, wᶜ(x) • c`, `wᶜ(x) = max 0 (ε - ‖x - c‖)`
([`SchauderProjection.lean`](../FixedPoint/Common/SchauderProjection.lean)): `P ∘ f` maps the hull
of the net into itself, and a fixed point `x` of it has `‖f x - x‖ < ε`.

## Departures from the sources

Statements:

- **Kakutani, Theorem 1.** Kakutani maps the simplex into its closed convex subsets and does not
  say that they are nonempty. His proof picks a point of each value, and the theorem fails when a
  value is empty, so the formalization requires nonempty values, as Kakutani's Theorem 2 states
  explicitly. Closed values follow from the closed graph and are not required. Theorem 1 is proved
  for convex hulls of nonempty finite sets, closed simplices being a special case also stated.
- **Kakutani, Corollary.** Kakutani's "bounded closed convex set in a Euclidean space" is a
  compact convex set of a finite-dimensional real inner product space, required nonempty, which
  Kakutani leaves implicit; `Kakutani.exists_fixedPoint` extends it to finite-dimensional normed
  spaces.
- **Schauder, Satz I.** Schauder states it for complete metric linear spaces (Banach's axioms,
  with a translation-invariant metric), not necessarily locally convex. His proof uses that a
  convex combination of points close to each other stays close to them (his Hilfssatz I), which
  holds in normed and locally convex spaces but not in general; the general case became
  Schauder's problem, Problem 54 of the Scottish Book, with a claimed solution by R. Cauty
  (Fund. Math. 170 (2001), 231–246) in which a gap was found. The formalization states Satz I for
  real normed spaces, complete or not, where Schauder's argument is valid.

- **Schauder, proof of Satz I, estimate (4).** Schauder bounds the distance between the values
  of his simplicial map at `x` and at the vertex `d` by `ε`, from his condition (1) and Hilfssatz
  I. That does not follow as written: the values at the vertices are points of the net within
  `2 ε + min(ε, δ(n, ε))` of each other, not within `δ(n, ε)`. The argument survives with a larger
  constant (in a normed space, `5 ε` instead of `3 ε`); the formalization bounds `‖x - f d‖`
  directly by `2 ε` instead, and reaches Schauder's `3 ε`. The same estimate is where his proof
  needs local convexity.

Proofs:

| Theorem | Source's proof | Formal proof | Reason |
| --- | --- | --- | --- |
| Brouwer | topological (Brouwer 1911/1912) | analytic, Milnor–Rogers | the analytic route uses Mathlib's analysis; Brouwer's own proof is not followed |
| Brouwer, second proof | KKM (1929): Sperner's lemma for any simplicial subdivision of the simplex, whose existence with small mesh is assumed, by counting facets mod 2 (each facet inside in two simplices, asserted); the KKM lemma; `A i = {x \| f x i ≤ x i}` | the same, on the iterated barycentric subdivisions; the two-simplices fact and the subdivision of the faces are replaced, mod 2, by the pairing of the pieces of `σ` and `σ * swap k (k + 1)` and the identification of the boundary facets with the subdivisions of the faces, both proved; Brouwer for compact convex sets through an enclosing simplex | KKM leave the subdivision open; the barycentric one is the one built here |
| Kakutani, Theorem 1 | the `n`-th barycentric subdivision of the simplex `S`, the map linear on its simplices with a point of `φ v` at each vertex `v`, Brouwer, subsequences, the closed graph, convexity | the same, on the standard simplex `Δ`, carried to `S` by the linear map `u ↦ ∑ u k • v k` | none in the argument: the subdivisions of `S` are the images of those of `Δ`; one choice of points of `φ` serves for every `n`, and one subsequence where Kakutani takes them one after the other |
| Kakutani, Corollary | a simplex containing `S` and a retraction onto `S` | the same, with the nearest-point retraction | Kakutani does not specify the retraction |
| Schauder, Satz I | the convex hull `H` of an `ε`-net triangulated finely; `f` approximated by a simplicial map sending each vertex `d` to a point of the net within `ε` of `f d`; Brouwer; a vertex moved by less than `3ε`; compactness | the same, with the triangulation of `H` replaced by the barycentric subdivisions of the simplex whose vertices map to the points of the net, carried onto `H` by `u ↦ ∑ u k • ξ k` | a change of coordinates, which gives Schauder's triangulation of `H` when the points of the net are affinely independent, and degenerate simplices of `H` otherwise. The second proof uses Schauder's projection instead, which is not in the paper |
| Schauder, Satz II | Mazur's theorem (Schauder's Hilfssatz II), then Satz I on the closed convex hull of `f(H)` | the same | none |

Kakutani's, Schauder's and KKM's papers were read from scans of the printed pages and compared
with the formalization; Milnor's and Rogers's papers were not compared line by line.

Not formalized: KKM's sharpened fixed-point theorem (maps of the simplex into Euclidean space
that send its boundary into it) and the remarks of their §4; Kakutani's Theorem 2 (von Neumann's intersection lemma) and Theorem 3 (the
minimax theorem), which he derives from the Corollary; Schauder's Satz III (weakly continuous
maps of weakly compact convex sets in separable Banach spaces) and Satz I beyond locally convex
spaces.

## Other formalizations

### Brouwer's theorem

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

### The KKM lemma and Sperner's lemma

- Lean 4 with Mathlib: the KKM lemma, through Sperner's lemma on iterated barycentric
  subdivisions
  ([facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean/blob/18d1aa399b6ebaa8cd9c4a48795b43f6734c3785/MathlibExt/Analysis/Convex/KKM.lean),
  `kkm_lemma`), without a derivation of Brouwer's theorem; Kuhn's cubical Sperner lemma
  (harfe/fixed-point-theorems-lean4, above). Other Lean 4 projects derive the KKM lemma from
  Brouwer's theorem, the converse direction.
- Isabelle/HOL: Kuhn's combinatorial lemma, in the proof of Brouwer's theorem above.
- Mizar: K. Pąk, *Sperner's Lemma*, Formalized Mathematics 18 (2010), 189–196
  ([doi:10.2478/v10037-010-0022-x](https://doi.org/10.2478/v10037-010-0022-x)), for barycentric
  subdivisions, used for Brouwer's theorem for simplices (Formalized Mathematics 19 (2011),
  145–150).

This proof does not use or adapt them.

### Kakutani's theorem

No formal proof of Kakutani's theorem was found outside Lean 4. Mathlib `v4.36.0-rc2` has none.
This proof is independent of the following ones, all in Lean 4 with Mathlib, which it does not
use or adapt.

- For compact convex sets in finite-dimensional real normed spaces, closed graph (in `s × V`) and
  nonempty convex values, by a continuous selection from a partition of unity, Brouwer's theorem
  through Kuhn's cubical Sperner lemma, Carathéodory's theorem and a limit
  ([harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/blob/93a3eed3364281a9dbf9652bb52356a8db65057c/FixedPointTheorems/kakutani.lean#L196),
  `kakutani_fixed_point`, MIT licence).
- In finite dimension, and the Fan–Glicksberg theorem in Hausdorff locally convex spaces
  ([danlyng/Econlib](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Math/Topology/Kakutani.lean#L241),
  `kakutaniFixedPoint`, `fanGlicksbergFixedPoint`).
- In Hausdorff locally convex spaces, for upper hemicontinuous maps with compact convex nonempty
  values, through Scarf's lemma
  ([matheconlib](https://github.com/matheconlib/matheconlib/blob/212e924aab86ef196ed36886594c3ebf98654888/MathEconLib/ForMathlib/Kakutani.lean#L211),
  `kakutaniGlicksbergFan`).
- In finite dimension, in closed-graph and upper hemicontinuous forms, through a vector Scarf
  lemma
  ([lyw-ops/General_Scarf](https://github.com/lyw-ops/General_Scarf/blob/9b784ba0e81ca3a2f1126c1087fdf7f2d03e16e0/BeyondSperner/FixedPoint/CompactConvexKakutani.lean)).
- In finite dimension at least `2`, closed graph, compact convex nonempty values
  ([RitinkarDB/eco-lean](https://github.com/RitinkarDB/eco-lean/blob/487060fb2ff5e04bf195c73913948ab5f548259d/EcoLean/MathematicalMiscellany/Kakutani.lean#L735)).

### Schauder's theorem

Mathlib `v4.36.0-rc2` has no Schauder fixed-point theorem; its list of 1000+ theorems has an
entry for it without a declaration. This proof is independent of the following ones, which it
does not use or adapt.

- HOL Light: `SCHAUDER` in John Harrison's Multivariate library, for `real^N` (finite dimension):
  a continuous map of a nonempty convex set into a compact subset of it has a fixed point; proved
  through absolute retracts
  ([`Multivariate/degree.ml`](https://github.com/jrh13/hol-light/blob/078839ea84531bd6c6cec9a58ebf69ba37149e0e/Multivariate/degree.ml#L7757)).
  Its automatic translation to Coq states the theorem as an axiom.
- Lean 4 with Mathlib:
  - for compact convex sets of real normed spaces, and for closed convex sets and maps with
    relatively compact image without completeness, with the Leray–Schauder and Schaefer theorems,
    through a partition-of-unity projection and Brouwer's theorem by singular homology
    ([TauCeti](https://github.com/TauCetiProject/TauCeti/blob/686d0d7f4390d0e8d6185114e99e90b74c599656/TauCeti/Analysis/Convex/SchauderFixedPoint.lean));
  - for compact convex sets of real normed spaces, through the Schauder projection, and
    Tychonoff's theorem in Hausdorff locally convex spaces
    ([danlyng/Econlib](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Math/Topology/Schauder.lean#L328));
  - in Hausdorff locally convex spaces, through Scarf's lemma
    ([matheconlib](https://github.com/matheconlib/matheconlib/blob/3cd66229d3630b46c17ebf16059beb6b8a9c2b2f/MathEconLib/ForMathlib/Schauder.lean#L4246));
  - for compact convex sets, and for closed convex sets of Banach spaces with relatively compact
    image through Mazur's theorem
    ([LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming/blob/9ae902b518234a376d07af7a7be9437b5e491700/RecursiveMethods/EquilibriaWithDistortions/EquilibriaWithDistortions/Schauder.lean));
  - for compact convex sets of real normed spaces, through harfe's Brouwer theorem
    ([elazarg/UniformEquilibrium](https://github.com/elazarg/UniformEquilibrium/blob/22f6ed14afb62eac34b679ada02b63fae9869693/MathUE/SchauderFixedPoint.lean#L225)).

No formal proof was found in Isabelle/HOL (distribution and AFP), Mizar, Metamath, HOL4 or
native Coq/Rocq.

## Files

| Path | Content |
| --- | --- |
| [`FixedPoint.lean`](../FixedPoint.lean) | imports the whole library |
| [`FixedPoint/Common/ContinuousMap.lean`](../FixedPoint/Common/ContinuousMap.lean) | the `C(s, s)` form of a fixed-point theorem for maps continuous on `s` |
| [`FixedPoint/Common/EnclosingSimplex.lean`](../FixedPoint/Common/EnclosingSimplex.lean) | a simplex containing a bounded set, with continuous barycentric coordinates |
| [`FixedPoint/Common/Euclidean.lean`](../FixedPoint/Common/Euclidean.lean) | fixed-point theorems for Euclidean space carried to finite-dimensional normed spaces |
| [`FixedPoint/Common/NearestPoint.lean`](../FixedPoint/Common/NearestPoint.lean) | the nearest-point retraction onto a closed convex set |
| [`FixedPoint/Common/SchauderProjection.lean`](../FixedPoint/Common/SchauderProjection.lean) | Schauder's projection and its partition of unity |
| [`FixedPoint/Common/Sperner.lean`](../FixedPoint/Common/Sperner.lean) | Sperner's lemma for the iterated barycentric subdivisions |
| [`FixedPoint/Common/Subdivision.lean`](../FixedPoint/Common/Subdivision.lean) | iterated barycentric subdivisions of the standard simplex: piecewise-linear interpolation, its continuity, the mesh |
| [`FixedPoint/Brouwer/DetPolynomial.lean`](../FixedPoint/Brouwer/DetPolynomial.lean) | `det (1 + t A)` and its integrals are polynomials in `t`; `det (1 + A) > 0` for `‖A‖ < 1` |
| [`FixedPoint/Brouwer/SmoothRetraction.lean`](../FixedPoint/Brouwer/SmoothRetraction.lean) | no `C¹` retraction of the closed unit ball onto the sphere |
| [`FixedPoint/Brouwer/SmoothFixedPoint.lean`](../FixedPoint/Brouwer/SmoothFixedPoint.lean) | Brouwer's theorem for `C¹` maps of the closed unit ball |
| [`FixedPoint/Brouwer/Ball.lean`](../FixedPoint/Brouwer/Ball.lean) | Brouwer's theorem for closed balls, the no-retraction theorem |
| [`FixedPoint/Brouwer/Convex.lean`](../FixedPoint/Brouwer/Convex.lean) | Brouwer's theorem for compact convex sets |
| [`FixedPoint/Brouwer/KKM.lean`](../FixedPoint/Brouwer/KKM.lean) | the KKM lemma; Brouwer's theorem through it |
| [`FixedPoint/Brouwer/Polytope.lean`](../FixedPoint/Brouwer/Polytope.lean) | Brouwer's theorem for convex hulls of finite sets in a normed space of any dimension |
| [`FixedPoint/Kakutani/Limit.lean`](../FixedPoint/Kakutani/Limit.lean) | the limit in Kakutani's proof |
| [`FixedPoint/Kakutani/Simplex.lean`](../FixedPoint/Kakutani/Simplex.lean) | Kakutani's Theorem 1, by his proof: the standard simplex, simplices, convex hulls of finite sets |
| [`FixedPoint/Kakutani/Selection.lean`](../FixedPoint/Kakutani/Selection.lean) | a second proof of Kakutani's theorem, through a partition of unity |
| [`FixedPoint/Kakutani/Convex.lean`](../FixedPoint/Kakutani/Convex.lean) | Kakutani's theorem for compact convex sets; closed graph and upper semicontinuity |
| [`FixedPoint/Schauder/Limit.lean`](../FixedPoint/Schauder/Limit.lean) | the limit in Schauder's proof |
| [`FixedPoint/Schauder/Convex.lean`](../FixedPoint/Schauder/Convex.lean) | Schauder's theorem for compact convex sets, by his proof |
| [`FixedPoint/Schauder/Projection.lean`](../FixedPoint/Schauder/Projection.lean) | a second proof of Schauder's theorem, through Schauder's projection |
| [`FixedPoint/Schauder/CompactImage.lean`](../FixedPoint/Schauder/CompactImage.lean) | Mazur's theorem; Schauder's theorem for closed convex sets and maps with relatively compact image |
| [`FixedPointChallenge.lean`](../FixedPointChallenge.lean), [`FixedPointSolution.lean`](../FixedPointSolution.lean), [`comparator.json`](../comparator.json), [`formalization.yaml`](../formalization.yaml) | Palomar: the statements of record, their proofs, the Comparator configuration, the metadata |
| [`scripts/Audit.lean`](../scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml) | CI: build, audit, import list of the audit, line lengths |
