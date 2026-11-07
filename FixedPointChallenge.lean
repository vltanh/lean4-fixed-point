module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Challenge: Brouwer's fixed-point theorem

Statements of record for Brouwer's fixed-point theorem (L. E. J. Brouwer, *Über Abbildung von
Mannigfaltigkeiten*, Math. Ann. 71 (1911/1912), 97–115) and the no-retraction theorem, in
Mathlib's vocabulary. The proofs, in `FixedPointSolution.lean`, are analytic, along the lines of
Milnor (Amer. Math. Monthly 85 (1978), 521–524) and Rogers (Amer. Math. Monthly 87 (1980),
525–527).

## Conventions

* A *finite-dimensional real normed space* `V` (`[NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]`) is `ℝⁿ`, for some `n ≥ 0`, with some norm; every such space is
  linearly homeomorphic to `ℝⁿ` with the Euclidean norm, so the choice of norm does not matter.
  A *finite-dimensional real inner product space* `E` (`[InnerProductSpace ℝ E]` in place of
  `[NormedSpace ℝ V]`) is `ℝⁿ` with a scalar product and its norm, for instance
  `EuclideanSpace ℝ (Fin n)`.
* `Convex ℝ s`: `s` contains the segment between any two of its points. `IsCompact s`: `s` is
  compact; in a finite-dimensional space, closed and bounded. `s.Nonempty`: `s` has a point.
* Maps are total functions `f : V → V`. `MapsTo f s t` says `f x ∈ t` for every `x ∈ s`, and
  `ContinuousOn f s` says that the restriction of `f` to `s` is continuous; the values of `f`
  outside `s` play no part. A continuous self-map of `s` is thus any `f` with `MapsTo f s s` and
  `ContinuousOn f s`.
* `closedBall c R = {x | ‖x - c‖ ≤ R}` and `sphere 0 1 = {x | ‖x‖ = 1}`.

## The theorems

* `BrouwerChallenge.exists_fixedPoint` (**Brouwer's fixed-point theorem**): every continuous
  self-map of a nonempty compact convex subset `s` of a finite-dimensional real normed space has
  a fixed point in `s`. This is the standard formulation (a continuous map of a nonempty compact
  convex subset of `ℝⁿ` into itself has a fixed point), for every dimension `n`, `n = 0`
  included, and for every norm.
* `BrouwerChallenge.exists_fixedPoint_closedBall`: the same for a closed ball `closedBall c R`,
  `R ≥ 0`, of a finite-dimensional real inner product space: a map that is continuous on the
  ball and maps it into itself has a fixed point in it. For `R = 0` the ball is the point `c`.
* `BrouwerChallenge.no_retraction` (**the no-retraction theorem**): the unit sphere of a
  finite-dimensional real inner product space is not a retract of its closed unit ball, that is,
  no map is continuous on the closed unit ball, maps it into the unit sphere and fixes every
  point of the sphere. For `E = ℝⁿ`, `n ≥ 1`, this says that `Sⁿ⁻¹` is not a retract of the
  closed ball `Dⁿ`. In dimension `0` the sphere is empty while the ball is the point `0`, so the
  statement holds trivially.
-/

public section

open Set Metric

namespace BrouwerChallenge

/-- **Brouwer's fixed-point theorem**: in a finite-dimensional real normed space, a map that is
continuous on a nonempty compact convex set `s` and maps `s` into itself has a fixed point in
`s`. -/
theorem exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x := by
  sorry

/-- **Brouwer's fixed-point theorem** for a closed ball of a finite-dimensional real inner product
space: a map that is continuous on the ball and maps it into itself has a fixed point in it. -/
theorem exists_fixedPoint_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {c : E} {R : ℝ} (hR : 0 ≤ R) {f : E → E}
    (hmaps : MapsTo f (closedBall c R) (closedBall c R)) (hf : ContinuousOn f (closedBall c R)) :
    ∃ x ∈ closedBall c R, f x = x := by
  sorry

/-- **The no-retraction theorem**: there is no retraction of the closed unit ball of a
finite-dimensional real inner product space onto its unit sphere, that is, no map that is
continuous on the closed ball, maps it into the sphere and fixes every point of the sphere. -/
theorem no_retraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ¬ ∃ r : E → E, ContinuousOn r (closedBall 0 1) ∧ MapsTo r (closedBall 0 1) (sphere 0 1) ∧
      ∀ x ∈ sphere (0 : E) 1, r x = x := by
  sorry

end BrouwerChallenge
