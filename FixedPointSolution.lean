module

public import FixedPoint

/-!
# Solution

Restates the three theorems of `FixedPointChallenge.lean` word for word and proves them from the
library (`Brouwer.exists_fixedPoint`, `Brouwer.exists_fixedPoint_closedBall`,
`Brouwer.no_retraction`). Palomar's Comparator checks that these are the Challenge's statements and
that their proofs use only the standard axioms (`comparator.json`).
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
  exact Brouwer.exists_fixedPoint hconv hcomp hne hmaps hf

/-- **Brouwer's fixed-point theorem** for a closed ball of a finite-dimensional real inner product
space: a map that is continuous on the ball and maps it into itself has a fixed point in it. -/
theorem exists_fixedPoint_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {c : E} {R : ℝ} (hR : 0 ≤ R) {f : E → E}
    (hmaps : MapsTo f (closedBall c R) (closedBall c R)) (hf : ContinuousOn f (closedBall c R)) :
    ∃ x ∈ closedBall c R, f x = x := by
  exact Brouwer.exists_fixedPoint_closedBall hR hmaps hf

/-- **The no-retraction theorem**: there is no retraction of the closed unit ball of a
finite-dimensional real inner product space onto its unit sphere, that is, no map that is
continuous on the closed ball, maps it into the sphere and fixes every point of the sphere. -/
theorem no_retraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ¬ ∃ r : E → E, ContinuousOn r (closedBall 0 1) ∧ MapsTo r (closedBall 0 1) (sphere 0 1) ∧
      ∀ x ∈ sphere (0 : E) 1, r x = x := by
  exact Brouwer.no_retraction

end BrouwerChallenge
