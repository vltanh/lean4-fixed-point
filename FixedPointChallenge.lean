module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Challenge: the fixed-point theorems of Brouwer, Kakutani and Schauder

Statements of record, in Mathlib's vocabulary, for

* Brouwer's fixed-point theorem (L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*,
  Math. Ann. 71 (1911/1912), 97–115) and the no-retraction theorem;
* Kakutani's fixed-point theorem (S. Kakutani, *A generalization of Brouwer's fixed point
  theorem*, Duke Math. J. 8 (1941), 457–459);
* Schauder's fixed-point theorem (J. Schauder, *Der Fixpunktsatz in Funktionalräumen*, Studia
  Math. 2 (1930), 171–180), in its two forms.

The proofs are in `FixedPointSolution.lean`.

## Conventions

* A *finite-dimensional real normed space* `V` (`[NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]`) is `ℝⁿ`, for some `n ≥ 0`, with some norm; every such space is
  linearly homeomorphic to `ℝⁿ` with the Euclidean norm, so the choice of norm does not matter.
  A *finite-dimensional real inner product space* `E` (`[InnerProductSpace ℝ E]` in place of
  `[NormedSpace ℝ V]`) is `ℝⁿ` with a scalar product and its norm, for instance
  `EuclideanSpace ℝ (Fin n)`. A *real normed space* `E`, without `[FiniteDimensional ℝ E]`, may
  have any dimension; with `[CompleteSpace E]` it is a real Banach space.
* `Convex ℝ s`: `s` contains the segment between any two of its points. `IsCompact s`: `s` is
  compact; in a finite-dimensional space, closed and bounded. `IsClosed s`: `s` is closed.
  `closure t`: the closure of `t`, so `IsCompact (closure t)` says that `t` is relatively compact.
  `s.Nonempty`: `s` has a point.
* Maps are total functions `f : V → V`. `MapsTo f s t` says `f x ∈ t` for every `x ∈ s`, and
  `ContinuousOn f s` says that the restriction of `f` to `s` is continuous; the values of `f`
  outside `s` play no part. A continuous self-map of `s` is thus any `f` with `MapsTo f s s` and
  `ContinuousOn f s`. `f '' s` is the image of `s`.
* A set-valued map is a function `φ : V → Set V`; again only its values at points of `s` play a
  part. Its graph over `s` is `{p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}`, a subset of `V × V` with the
  product topology. When `s` is closed, this graph is closed exactly when `xₙ → x` in `s`,
  `yₙ ∈ φ xₙ` and `yₙ → y` imply `y ∈ φ x`, which is Kakutani's upper semicontinuity.
* `closedBall c R = {x | ‖x - c‖ ≤ R}` and `sphere 0 1 = {x | ‖x‖ = 1}`.

## The theorems

* `FixedPointChallenge.brouwer` (**Brouwer's fixed-point theorem**): every continuous self-map
  of a nonempty compact convex subset `s` of a finite-dimensional real normed space has a fixed
  point in `s`. This is the standard formulation (a continuous map of a nonempty compact convex
  subset of `ℝⁿ` into itself has a fixed point), for every dimension `n`, `n = 0` included, and
  for every norm.
* `FixedPointChallenge.brouwer_closedBall`: the same for a closed ball `closedBall c R`, `R ≥ 0`,
  of a finite-dimensional real inner product space: a map that is continuous on the ball and maps
  it into itself has a fixed point in it. For `R = 0` the ball is the point `c`.
* `FixedPointChallenge.no_retraction` (**the no-retraction theorem**): the unit sphere of a
  finite-dimensional real inner product space is not a retract of its closed unit ball, that is,
  no map is continuous on the closed unit ball, maps it into the unit sphere and fixes every
  point of the sphere. For `E = ℝⁿ`, `n ≥ 1`, this says that `Sⁿ⁻¹` is not a retract of the
  closed ball `Dⁿ`. In dimension `0` the sphere is empty while the ball is the point `0`, so the
  statement holds trivially.
* `FixedPointChallenge.kakutani` (**Kakutani's fixed-point theorem**): let `s` be a nonempty
  compact convex subset of a finite-dimensional real normed space, and `φ` a set-valued map that
  sends each point of `s` to a nonempty convex subset of `s`, with closed graph over `s`. Then
  `x ∈ φ x` for some `x ∈ s`. The values `φ x` are then closed, being sections of the graph.
* `FixedPointChallenge.schauder` (**Schauder's fixed-point theorem**): every continuous self-map
  of a nonempty compact convex subset `s` of a real normed space, of any dimension, has a fixed
  point in `s`. The space need not be complete.
* `FixedPointChallenge.schauder_of_isCompact_closure_image` (**Schauder's fixed-point theorem**,
  second form): in a real Banach space, every continuous self-map `f` of a nonempty closed convex
  set `s` with relatively compact image `f '' s` has a fixed point in `s`.
-/

public section

open Set Metric

namespace FixedPointChallenge

/-- **Brouwer's fixed-point theorem**: in a finite-dimensional real normed space, a map that is
continuous on a nonempty compact convex set `s` and maps `s` into itself has a fixed point in
`s`. -/
theorem brouwer {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x := by
  sorry

/-- **Brouwer's fixed-point theorem** for a closed ball of a finite-dimensional real inner product
space: a map that is continuous on the ball and maps it into itself has a fixed point in it. -/
theorem brouwer_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

/-- **Kakutani's fixed-point theorem**: in a finite-dimensional real normed space, if a set-valued
map `φ` sends each point of a nonempty compact convex set `s` to a nonempty convex subset of `s`
and its graph `{(x, y) | x ∈ s, y ∈ φ x}` is closed, then `x ∈ φ x` for some `x ∈ s`. -/
theorem kakutani {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s)
    (hφne : ∀ x ∈ s, (φ x).Nonempty) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x := by
  sorry

/-- **Schauder's fixed-point theorem**: in a real normed space, a map that is continuous on a
nonempty compact convex set `s` and maps `s` into itself has a fixed point in `s`. -/
theorem schauder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty) {f : E → E}
    (hmaps : MapsTo f s s) (hf : ContinuousOn f s) : ∃ x ∈ s, f x = x := by
  sorry

/-- **Schauder's fixed-point theorem**, second form: in a real Banach space, a map that is
continuous on a nonempty closed convex set `s`, maps `s` into itself and has a relatively compact
image `f '' s` has a fixed point in `s`. -/
theorem schauder_of_isCompact_closure_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {s : Set E} (hconv : Convex ℝ s) (hcl : IsClosed s)
    (hne : s.Nonempty) {f : E → E} (hmaps : MapsTo f s s) (hf : ContinuousOn f s)
    (himg : IsCompact (closure (f '' s))) : ∃ x ∈ s, f x = x := by
  sorry

end FixedPointChallenge
