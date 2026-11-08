# Fixed-point theorems in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-fixed-point/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-fixed-point/actions/workflows/lean_action_ci.yml)

Fixed-point theorems in Lean 4 with Mathlib. The package proves **Brouwer's fixed-point theorem**,
for every nonempty compact convex subset of a finite-dimensional real normed space, and the
**no-retraction theorem** for the closed unit ball. The proof is analytic, along the lines of
Milnor (1978) and Rogers (1980), and needs no homology, degree theory or simplicial approximation.

There is no `axiom` or `native_decide`, and no `sorry` outside the statements of
[`FixedPointChallenge.lean`](FixedPointChallenge.lean). Kakutani's and Schauder's fixed-point
theorems are planned, under `FixedPoint/Kakutani/` and `FixedPoint/Schauder/`.

## Main results

The declarations are in the namespace `Brouwer`. `V` is a finite-dimensional real normed space;
`E` is a finite-dimensional real inner product space, for instance `EuclideanSpace ℝ (Fin n)`.
All statements in Lean and the method step by step are in [docs/DETAILS.md](docs/DETAILS.md).

| Lean | Statement | Source |
| --- | --- | --- |
| [`exists_fixedPoint`](FixedPoint/Brouwer/Convex.lean#L46) | a map of a nonempty compact convex `s ⊆ V` into itself that is continuous on `s` has a fixed point in `s` | Brouwer (1911/1912) |
| [`exists_fixedPoint_continuousMap`](FixedPoint/Brouwer/Convex.lean#L65) | the same for `f : C(s, s)` | Brouwer (1911/1912) |
| [`exists_fixedPoint_closedBall`](FixedPoint/Brouwer/Ball.lean#L130) | the same for a closed ball `closedBall c R` of `E`, `R ≥ 0` | Brouwer (1911/1912) |
| [`no_retraction`](FixedPoint/Brouwer/Ball.lean#L159) | no map is continuous on the closed unit ball of `E`, maps it into the unit sphere and fixes every point of the sphere | equivalent to Brouwer's theorem |
| [`no_contDiffAt_retraction`](FixedPoint/Brouwer/SmoothRetraction.lean#L115) | the same for maps that are `C¹` at every point of the closed unit ball | Milnor (1978), Rogers (1980) |
| [`exists_fixedPoint_of_contDiffAt`](FixedPoint/Brouwer/SmoothFixedPoint.lean#L96) | a map that is `C¹` at every point of the closed unit ball of `E` and maps it into itself has a fixed point there | the ray construction |

```lean
theorem exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x
```

## Lean statement of record

[`FixedPointChallenge.lean`](FixedPointChallenge.lean) states, with `sorry` and in Mathlib's
vocabulary, `BrouwerChallenge.exists_fixedPoint`, `exists_fixedPoint_closedBall` and
`no_retraction`, the theorems of the same names above. It defines nothing, so it carries no copy
of the library's definitions; its module docstring explains every convention it uses.

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

and import the modules you need, for instance `public import FixedPoint.Brouwer.Convex` in a
module, or `import FixedPoint` for everything. The package requires Lean and Mathlib
`v4.36.0-rc2`; your project should use the same Mathlib version.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build                         # the library, the Challenge and the Solution
lake env lean scripts/Audit.lean   # axioms
lake env lake comparator --config=comparator.json   # needs bubblewrap; expect "Your solution is okay!"
```

- The library has about 790 lines in six modules, and builds in about 15 seconds once Mathlib is
  compiled.
- The audit checks that the main theorems and every declaration of the library use only the
  standard axioms ([what it checks](docs/DETAILS.md#the-axiom-audit)).

## Layout

| Path | Content |
| --- | --- |
| [`FixedPoint.lean`](FixedPoint.lean), [`FixedPoint/Brouwer.lean`](FixedPoint/Brouwer.lean) | import the whole library; Brouwer's theorem and its lemmas |
| [`FixedPoint/Brouwer/`](FixedPoint/Brouwer) | the proof, in six modules: `DetPolynomial`, `SmoothRetraction`, `SmoothFixedPoint`, `Ball`, `NearestPoint`, `Convex` ([each module](docs/DETAILS.md#files)) |
| [`FixedPointChallenge.lean`](FixedPointChallenge.lean), [`FixedPointSolution.lean`](FixedPointSolution.lean), [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml) | Palomar: the statements of record, their proofs, the Comparator configuration, the metadata |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/`](.github/workflows) | CI: build, audit, import list of the audit, line lengths |

## Other formalizations

Brouwer's theorem has other formal proofs, in Lean 4, Lean 3, HOL Light, Isabelle/HOL, Mizar and
Coq ([the list, with methods and links](docs/DETAILS.md#other-formalizations)); this one is
independent of them. Mathlib `v4.36.0-rc2` has none.

## References

- L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, Math. Ann. 71 (1911/1912), 97–115,
  whose topological proof is not the one formalized here.
- J. Milnor, *Analytic proofs of the "hairy ball theorem" and the Brouwer fixed point theorem*,
  Amer. Math. Monthly 85 (1978), 521–524.
- C. A. Rogers, *A less strange version of Milnor's proof of Brouwer's fixed-point theorem*,
  Amer. Math. Monthly 87 (1980), 525–527.
- P. D. Lax, *Change of variables in multiple integrals*, Amer. Math. Monthly 106 (1999), 497–501,
  where Brouwer's theorem is a corollary of the change of variables formula.

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## License

Apache-2.0; see [LICENSE](LICENSE).
