/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Kakutani.Simplex
public import FixedPoint.Common.NearestPoint
public import FixedPoint.Common.EnclosingSimplex
public import FixedPoint.Common.Euclidean

/-!
# Kakutani's fixed-point theorem for compact convex sets

Let `s` be a nonempty compact convex subset of a finite-dimensional real normed space `V`, and
`φ : V → Set V` a set-valued map that sends each point of `s` to a nonempty convex subset of `s`,
with closed graph `{(x, y) | x ∈ s, y ∈ φ x}`. Then `x ∈ φ x` for some `x ∈ s`.

* `Kakutani.exists_fixedPoint_of_innerProductSpace` (Kakutani 1941, Corollary): for a
  finite-dimensional real inner product space;
* `Kakutani.exists_fixedPoint` (**Kakutani's fixed-point theorem**): for a finite-dimensional real
  normed space;
* `Kakutani.isClosed_graph_iff_seq`: for closed `s`, the graph is closed exactly when `φ` is upper
  semicontinuous in Kakutani's sense, stated with sequences.

## Proof

Kakutani's reduction to his Theorem 1. In an inner product space, `s` lies in a simplex `K`
(`FixedPoint.exists_subset_convexHull_simplex`), and is a retract of the space through the
nearest-point map `π` (`NearestPoint.exists_lipschitzWith_retraction`), Kakutani's unspecified
retraction. The map `x ↦ φ (π x)` sends `K` to nonempty convex subsets of `s ⊆ K`, with closed
graph, so `x ∈ φ (π x)` for some `x ∈ K` (`Kakutani.exists_fixedPoint_convexHull_range`). Then
`x ∈ s`, so `π x = x` and `x ∈ φ x`. A linear isomorphism `V ≃L[ℝ] EuclideanSpace ℝ (Fin n)`
reduces normed spaces to inner product spaces, as for Brouwer's theorem
(`FixedPoint.exists_mem_self_of_euclidean`).

Kakutani's `s` is a bounded closed convex set; it must also be nonempty, which he leaves
implicit. A second proof, which needs no simplex, is `Kakutani.Selection.exists_fixedPoint`.
-/

@[expose] public section

open Set Filter Topology Module
open scoped InnerProductSpace

namespace Kakutani

/-- **Kakutani's fixed-point theorem** in a finite-dimensional real inner product space (Kakutani
1941, Corollary): if `φ` sends each point of a nonempty compact convex set `s` to a nonempty
convex subset of `s` and its graph `{(x, y) | x ∈ s, y ∈ φ x}` is closed, then `x ∈ φ x` for some
`x ∈ s`. -/
theorem exists_fixedPoint_of_innerProductSpace {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {s : Set F} (hconv : Convex ℝ s)
    (hcomp : IsCompact s) (hne : s.Nonempty) {φ : F → Set F} (hmaps : ∀ x ∈ s, φ x ⊆ s)
    (hφne : ∀ x ∈ s, (φ x).Nonempty) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : F × F | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x := by
  obtain ⟨π, hπ, hπs, hπfix⟩ :=
    NearestPoint.exists_lipschitzWith_retraction hne hcomp.isClosed hconv
  -- a simplex `K` that contains `s`
  obtain ⟨v, hsK⟩ := FixedPoint.exists_subset_convexHull_simplex hcomp.isBounded
  -- the graph of `x ↦ φ (π x)` over `K` is closed
  have hgraph' : IsClosed {p : F × F | p.1 ∈ convexHull ℝ (range v) ∧ p.2 ∈ φ (π p.1)} := by
    have : {p : F × F | p.1 ∈ convexHull ℝ (range v) ∧ p.2 ∈ φ (π p.1)} =
        Prod.fst ⁻¹' convexHull ℝ (range v) ∩
          Prod.map π id ⁻¹' {p : F × F | p.1 ∈ s ∧ p.2 ∈ φ p.1} := by
      ext p
      simp [hπs]
    rw [this]
    exact (((finite_range v).isCompact_convexHull ℝ).isClosed.preimage continuous_fst).inter
      (hgraph.preimage (hπ.continuous.prodMap continuous_id))
  obtain ⟨x, -, hx⟩ := exists_fixedPoint_convexHull_range v (φ := fun x ↦ φ (π x))
    (fun x _ ↦ (hmaps _ (hπs x)).trans hsK) (fun x _ ↦ hφne _ (hπs x))
    (fun x _ ↦ hφconv _ (hπs x)) hgraph'
  have hxs : x ∈ s := hmaps _ (hπs x) hx
  exact ⟨x, hxs, by simpa [hπfix x hxs] using hx⟩

/-- **Kakutani's fixed-point theorem**: in a finite-dimensional real normed space, if `φ` sends
each point of a nonempty compact convex set `s` to a nonempty convex subset of `s` and its graph
`{(x, y) | x ∈ s, y ∈ φ x}` is closed, then `x ∈ φ x` for some `x ∈ s`. -/
theorem exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s)
    (hφne : ∀ x ∈ s, (φ x).Nonempty) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x :=
  FixedPoint.exists_mem_self_of_euclidean
    (fun _ hconv hcomp hne _ hmaps hφne hφconv hgraph ↦
      exists_fixedPoint_of_innerProductSpace hconv hcomp hne hmaps hφne hφconv hgraph)
    hconv hcomp hne hmaps hφne hφconv hgraph

/-- For a closed set `s`, the graph `{(x, y) | x ∈ s, y ∈ φ x}` is closed exactly when `φ` is upper
semicontinuous in Kakutani's sense: if `x n → a` in `s`, `y n ∈ φ (x n)` and `y n → b`, then
`b ∈ φ a`. -/
theorem isClosed_graph_iff_seq {X : Type*} [PseudoMetricSpace X] {s : Set X} (hs : IsClosed s)
    {φ : X → Set X} :
    IsClosed {p : X × X | p.1 ∈ s ∧ p.2 ∈ φ p.1} ↔
      ∀ (x y : ℕ → X) (a b : X), (∀ n, x n ∈ s) → (∀ n, y n ∈ φ (x n)) →
        Tendsto x atTop (𝓝 a) → Tendsto y atTop (𝓝 b) → b ∈ φ a := by
  refine ⟨fun hG x y a b hx hy ha hb ↦ ?_, fun h ↦ IsSeqClosed.isClosed fun p q hp hlim ↦ ?_⟩
  · exact (hG.mem_of_tendsto (ha.prodMk_nhds hb) (Eventually.of_forall fun n ↦ ⟨hx n, hy n⟩)).2
  · have h1 : Tendsto (fun n ↦ (p n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto _).comp hlim
    have h2 : Tendsto (fun n ↦ (p n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto _).comp hlim
    exact ⟨hs.mem_of_tendsto h1 (Eventually.of_forall fun n ↦ (hp n).1),
      h _ _ _ _ (fun n ↦ (hp n).1) (fun n ↦ (hp n).2) h1 h2⟩

end Kakutani
