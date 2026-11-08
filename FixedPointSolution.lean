module

public import FixedPoint

/-!
# Solution

Restates the six theorems of `FixedPointChallenge.lean` word for word and proves them from the
library (`Brouwer.exists_fixedPoint`, `Brouwer.exists_fixedPoint_closedBall`,
`Brouwer.no_retraction`, `Kakutani.exists_fixedPoint`, `Schauder.exists_fixedPoint`,
`Schauder.exists_fixedPoint_of_isCompact_closure_image`). Palomar's Comparator checks that these
are the Challenge's statements and that their proofs use only the standard axioms
(`comparator.json`).
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
  exact Brouwer.exists_fixedPoint hconv hcomp hne hmaps hf

/-- **Brouwer's fixed-point theorem** for a closed ball of a finite-dimensional real inner product
space: a map that is continuous on the ball and maps it into itself has a fixed point in it. -/
theorem brouwer_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

/-- **Kakutani's fixed-point theorem**: in a finite-dimensional real normed space, if a set-valued
map `φ` sends each point of a nonempty compact convex set `s` to a nonempty convex subset of `s`
and its graph `{(x, y) | x ∈ s, y ∈ φ x}` is closed, then `x ∈ φ x` for some `x ∈ s`. -/
theorem kakutani {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s)
    (hφne : ∀ x ∈ s, (φ x).Nonempty) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x := by
  exact Kakutani.exists_fixedPoint hconv hcomp hne hmaps hφne hφconv hgraph

/-- **Schauder's fixed-point theorem**: in a real normed space, a map that is continuous on a
nonempty compact convex set `s` and maps `s` into itself has a fixed point in `s`. -/
theorem schauder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty) {f : E → E}
    (hmaps : MapsTo f s s) (hf : ContinuousOn f s) : ∃ x ∈ s, f x = x := by
  exact Schauder.exists_fixedPoint hconv hcomp hne hmaps hf

/-- **Schauder's fixed-point theorem**, second form: in a real Banach space, a map that is
continuous on a nonempty closed convex set `s`, maps `s` into itself and has a relatively compact
image `f '' s` has a fixed point in `s`. -/
theorem schauder_of_isCompact_closure_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {s : Set E} (hconv : Convex ℝ s) (hcl : IsClosed s)
    (hne : s.Nonempty) {f : E → E} (hmaps : MapsTo f s s) (hf : ContinuousOn f s)
    (himg : IsCompact (closure (f '' s))) : ∃ x ∈ s, f x = x := by
  exact Schauder.exists_fixedPoint_of_isCompact_closure_image hconv hcl hne hmaps hf himg

end FixedPointChallenge
