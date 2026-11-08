# Fixed-point theorems in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-fixed-point/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-fixed-point/actions/workflows/lean_action_ci.yml)

Fixed-point theorems in Lean 4 with Mathlib, each for a nonempty compact convex set `s`:

- **Brouwer's theorem**: a continuous map of `s` into itself has a fixed point, in a
  finite-dimensional real normed space; with the no-retraction theorem. Two proofs: an analytic
  one, and one through Sperner's lemma and the lemma of Knaster, Kuratowski and Mazurkiewicz.
- **Kakutani's theorem**: a set-valued map `φ` that sends each point of `s` to a nonempty convex
  subset of `s`, and has a closed graph, has a point `x ∈ φ x`, in a finite-dimensional real
  normed space.
- **Schauder's theorem**: a continuous map of `s` into itself has a fixed point, in a real normed
  space of any dimension; and the same for closed convex sets of Banach spaces and maps with
  relatively compact image.

There is no `axiom` or `native_decide`, and no `sorry` outside the statements of
[`FixedPointChallenge.lean`](FixedPointChallenge.lean).

## Main results

`V` is a finite-dimensional real normed space, `E` a real normed space of any dimension. All
statements in Lean, the method step by step and the departures from the sources are in
[docs/DETAILS.md](docs/DETAILS.md).

| Theorem | Lean | Statement | Source |
| --- | --- | --- | --- |
| Brouwer | [`Brouwer.exists_fixedPoint`](FixedPoint/Brouwer/Convex.lean#L54) | a map of a nonempty compact convex `s ⊆ V` into itself that is continuous on `s` has a fixed point in `s` | Brouwer (1911/1912) |
| | [`Brouwer.exists_fixedPoint_closedBall`](FixedPoint/Brouwer/Ball.lean#L135) | the same for a closed ball of a finite-dimensional real inner product space | Brouwer (1911/1912) |
| | [`Brouwer.no_retraction`](FixedPoint/Brouwer/Ball.lean#L164) | no map is continuous on the closed unit ball of a finite-dimensional real inner product space, maps it into the unit sphere and fixes every point of the sphere | equivalent to Brouwer's theorem |
| | [`Brouwer.KKM.exists_fixedPoint`](FixedPoint/Brouwer/KKM.lean#L190) | the same, by the second proof | Knaster, Kuratowski, Mazurkiewicz (1929) |
| | [`Brouwer.KKM.exists_mem_iInter`](FixedPoint/Brouwer/KKM.lean#L60) | the KKM lemma: closed sets covering each face `[e i, i ∈ I]` of the standard simplex by the `F i`, `i ∈ I`, have a common point | Knaster, Kuratowski, Mazurkiewicz (1929) |
| Kakutani | [`Kakutani.exists_fixedPoint`](FixedPoint/Kakutani/Convex.lean#L81) | if `φ : V → Set V` sends each point of a nonempty compact convex `s ⊆ V` to a nonempty convex subset of `s`, and its graph over `s` is closed, then `x ∈ φ x` for some `x ∈ s` | Kakutani (1941), Corollary |
| | [`Kakutani.exists_fixedPoint_simplex`](FixedPoint/Kakutani/Simplex.lean#L147) | the same for a closed simplex | Kakutani (1941), Theorem 1 |
| Schauder | [`Schauder.exists_fixedPoint`](FixedPoint/Schauder/Convex.lean#L178) | a map of a nonempty compact convex `s ⊆ E` into itself that is continuous on `s` has a fixed point in `s` | Schauder (1930), Satz I |
| | [`Schauder.exists_fixedPoint_of_isCompact_closure_image`](FixedPoint/Schauder/CompactImage.lean#L50) | the same for a nonempty closed convex `s` of a Banach space and a map `f` with `f '' s` relatively compact | Schauder (1930), Satz II |

The three theorems for compact convex sets:

```lean
theorem Brouwer.exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x

theorem Kakutani.exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s)
    (hφne : ∀ x ∈ s, (φ x).Nonempty) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x

theorem Schauder.exists_fixedPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty) {f : E → E}
    (hmaps : MapsTo f s s) (hf : ContinuousOn f s) : ∃ x ∈ s, f x = x
```

## How the proofs relate to the sources

| Theorem | Proof | Departure from the source |
| --- | --- | --- |
| Brouwer | Milnor–Rogers: no `C¹` retraction, by the change of variables formula; then smoothing, and the nearest-point retraction for compact convex sets | the whole proof: Brouwer's own is topological |
| Brouwer, second proof | Knaster–Kuratowski–Mazurkiewicz: Sperner's lemma, the KKM lemma, then Brouwer for the simplex; an enclosing simplex for compact convex sets | KKM subdivide the simplex in any fine way; here, barycentric subdivisions |
| Kakutani | Kakutani's: piecewise-linear maps on barycentric subdivisions of a simplex, Brouwer (KKM's proof, which he cites), a limit; an enclosing simplex and a retraction for compact convex sets. A second proof replaces the subdivisions by a partition of unity | none in the argument: the subdivisions are built on the standard simplex and carried to other simplices by a linear map, and the retraction, which Kakutani leaves open, is the nearest-point map |
| Schauder | Schauder's: a simplicial approximation of `f` on a fine triangulation of the convex hull of a finite `ε`-net, Brouwer (KKM's proof, which he cites), a vertex moved by less than `3ε`, compactness; Mazur's theorem for the second form. A second proof uses Schauder's projection | the triangulation is carried from a simplex onto the hull by a linear map; Satz I is stated for normed spaces, not Schauder's complete metric linear spaces |

Reasons, and the results of the three papers that are not formalized:
[docs/DETAILS.md](docs/DETAILS.md#departures-from-the-sources).

## Lean statement of record

[`FixedPointChallenge.lean`](FixedPointChallenge.lean) states, with `sorry` and in Mathlib's
vocabulary, six theorems in the namespace `FixedPointChallenge`: `brouwer`, `brouwer_closedBall`,
`no_retraction`, `kakutani`, `schauder` and `schauder_of_isCompact_closure_image`. It defines
nothing, so it carries no copy of the library's definitions; its module docstring explains every
convention it uses.

[`FixedPointSolution.lean`](FixedPointSolution.lean) restates them word for word and proves them
from the library; [`comparator.json`](comparator.json) configures Palomar's Comparator.

## Using it from another Lake project

Add to the `lakefile.toml` of your project:

```toml
[[require]]
name = "FixedPoint"
git = "https://github.com/vltanh/lean4-fixed-point"
rev = "<commit>"
```

and import the modules you need, for instance `public import FixedPoint.Kakutani.Convex` in a
module, or `import FixedPoint` for everything. The package requires Lean and Mathlib
`v4.36.0-rc2`; your project should use the same Mathlib version.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build                         # the library, the Challenge and the Solution
lake env lean scripts/Audit.lean   # axioms
lake env lake comparator --config=comparator.json   # needs bubblewrap; expect "Your solution is okay!"
```

- The library has about 3,200 lines in 23 modules, and builds in about 30 seconds once Mathlib is
  compiled.
- The audit checks that the main theorems and every declaration of the library use only the
  standard axioms ([what it checks](docs/DETAILS.md#the-axiom-audit)).

## Layout

| Path | Content |
| --- | --- |
| [`FixedPoint.lean`](FixedPoint.lean) | imports the whole library ([each module](docs/DETAILS.md#files)) |
| [`FixedPoint/Common/`](FixedPoint/Common) | shared tools: `ContinuousMap` (the `C(s, s)` form of a fixed-point theorem), `EnclosingSimplex` (a simplex around a bounded set), `Euclidean` (from Euclidean to normed spaces), `NearestPoint` (the nearest-point retraction), `SchauderProjection` (Schauder's projection and its partition of unity), `Subdivision` (iterated barycentric subdivisions of the standard simplex), `Sperner` (Sperner's lemma) |
| [`FixedPoint/Brouwer/`](FixedPoint/Brouwer) | Brouwer's theorem: `DetPolynomial`, `SmoothRetraction`, `SmoothFixedPoint`, `Ball`, `Convex` (compact convex sets), `Polytope` (convex hulls of finite sets, any dimension), `KKM` (the second proof) |
| [`FixedPoint/Kakutani/`](FixedPoint/Kakutani) | Kakutani's theorem: `Limit`, `Simplex` (Theorem 1), `Convex` (compact convex sets), `Selection` (a second proof) |
| [`FixedPoint/Schauder/`](FixedPoint/Schauder) | Schauder's theorem: `Limit`, `Convex` (compact convex sets), `Projection` (a second proof), `CompactImage` (relatively compact image) |
| [`FixedPointChallenge.lean`](FixedPointChallenge.lean), [`FixedPointSolution.lean`](FixedPointSolution.lean), [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml) | Palomar: the statements of record, their proofs, the Comparator configuration, the metadata |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/`](.github/workflows) | CI: build, audit, import list of the audit, line lengths |

## Other formalizations

Mathlib `v4.36.0-rc2` has none of the three theorems; this work is independent of the other
formal proofs ([the lists, with methods and links](docs/DETAILS.md#other-formalizations)).

| Theorem | Other formal proofs |
| --- | --- |
| Brouwer | Lean 4, Lean 3, HOL Light, Isabelle/HOL, Mizar, Coq (the plane); the KKM lemma in Lean 4, Sperner's lemma in Mizar |
| Kakutani | Lean 4 |
| Schauder | Lean 4; HOL Light (finite dimension) |

## References

Brouwer:

- L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, Math. Ann. 71 (1911/1912), 97–115,
  [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931).
- J. Milnor, *Analytic proofs of the "hairy ball theorem" and the Brouwer fixed point theorem*,
  Amer. Math. Monthly 85 (1978), 521–524,
  [doi:10.1080/00029890.1978.11994635](https://doi.org/10.1080/00029890.1978.11994635).
- C. A. Rogers, *A less strange version of Milnor's proof of Brouwer's fixed-point theorem*,
  Amer. Math. Monthly 87 (1980), 525–527,
  [doi:10.1080/00029890.1980.11995082](https://doi.org/10.1080/00029890.1980.11995082).
- P. D. Lax, *Change of variables in multiple integrals*, Amer. Math. Monthly 106 (1999), 497–501,
  [doi:10.1080/00029890.1999.12005078](https://doi.org/10.1080/00029890.1999.12005078).
- E. Sperner, *Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes*, Abh. Math.
  Sem. Univ. Hamburg 6 (1928), 265–272,
  [doi:10.1007/BF02940617](https://doi.org/10.1007/BF02940617).
- B. Knaster, C. Kuratowski, S. Mazurkiewicz, *Ein Beweis des Fixpunktsatzes für n-dimensionale
  Simplexe*, Fund. Math. 14 (1929), 132–137,
  [doi:10.4064/fm-14-1-132-137](https://doi.org/10.4064/fm-14-1-132-137).

Kakutani:

- S. Kakutani, *A generalization of Brouwer's fixed point theorem*, Duke Math. J. 8 (1941),
  457–459, [doi:10.1215/S0012-7094-41-00838-4](https://doi.org/10.1215/S0012-7094-41-00838-4).

Schauder:

- J. Schauder, *Der Fixpunktsatz in Funktionalräumen*, Studia Math. 2 (1930), 171–180,
  [doi:10.4064/sm-2-1-171-180](https://doi.org/10.4064/sm-2-1-171-180).
- S. Mazur, *Über die kleinste konvexe Menge, die eine gegebene kompakte Menge enthält*, Studia
  Math. 2 (1930), 7–9, [doi:10.4064/sm-2-1-7-9](https://doi.org/10.4064/sm-2-1-7-9).

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## License

Apache-2.0; see [LICENSE](LICENSE).
