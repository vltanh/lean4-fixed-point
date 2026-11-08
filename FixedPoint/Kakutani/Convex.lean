/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Kakutani.Simplex
public import FixedPoint.Brouwer.NearestPoint
public import Mathlib.Analysis.Normed.Affine.Convex

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

Kakutani's reduction to his Theorem 1. In an inner product space, `s` lies in the convex hull `K`
of a finite set (`Convex.exists_subset_interior_convexHull_finset_of_isCompact`), and is a retract
of the space through the nearest-point map `π` (`Brouwer.exists_lipschitzWith_retraction`). The
map `x ↦ φ (π x)` sends `K` to nonempty convex subsets of `s ⊆ K`, with closed graph, so
`x ∈ φ (π x)` for some `x ∈ K` (`Kakutani.exists_fixedPoint_convexHull`). Then `x ∈ s`, so
`π x = x` and `x ∈ φ x`. A linear isomorphism `V ≃L[ℝ] EuclideanSpace ℝ (Fin n)` reduces normed
spaces to inner product spaces.

Kakutani encloses `s` in a simplex; the formalization encloses it in the convex hull of a finite
set, the image of a simplex under a linear map, for which Theorem 1 is proved the same way
(`Kakutani.exists_fixedPoint_convexHull`), and uses the nearest-point retraction, which Kakutani
leaves unspecified. A second proof, which needs no simplex, is
`Kakutani.PartitionOfUnity.exists_fixedPoint`.
-/

@[expose] public section

open Set Filter Topology Module

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
  obtain ⟨π, hπ, hπs, hπfix⟩ := Brouwer.exists_lipschitzWith_retraction hne hcomp.isClosed hconv
  -- a convex hull `K` of a finite set that contains `s`
  obtain ⟨u, hsu, -⟩ := hconv.exists_subset_interior_convexHull_finset_of_isCompact hcomp
    (univ_mem : univ ∈ 𝓝ˢ s)
  have hsK : s ⊆ convexHull ℝ (u : Set F) := hsu.trans interior_subset
  have hune : (u : Set F).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact convexHull_nonempty_iff.1 ⟨x, hsK hx⟩
  -- the graph of `x ↦ φ (π x)` over `K` is closed
  have hgraph' : IsClosed {p : F × F | p.1 ∈ convexHull ℝ (u : Set F) ∧ p.2 ∈ φ (π p.1)} := by
    have : {p : F × F | p.1 ∈ convexHull ℝ (u : Set F) ∧ p.2 ∈ φ (π p.1)} =
        Prod.fst ⁻¹' convexHull ℝ (u : Set F) ∩
          Prod.map π id ⁻¹' {p : F × F | p.1 ∈ s ∧ p.2 ∈ φ p.1} := by
      ext p
      simp [hπs]
    rw [this]
    exact ((u.finite_toSet.isCompact_convexHull ℝ).isClosed.preimage continuous_fst).inter
      (hgraph.preimage (hπ.continuous.prodMap continuous_id))
  obtain ⟨x, -, hx⟩ := exists_fixedPoint_convexHull (φ := fun x ↦ φ (π x)) u.finite_toSet hune
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
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hs' : e.symm ⁻¹' s = e '' s := (e.image_eq_preimage_symm s).symm
  obtain ⟨y, hy, hyφ⟩ := exists_fixedPoint_of_innerProductSpace (s := e.symm ⁻¹' s)
    (φ := fun y ↦ e.symm ⁻¹' φ (e.symm y))
    (hconv.linear_preimage e.symm.toLinearEquiv.toLinearMap)
    (hs' ▸ hcomp.image e.continuous) (hs' ▸ hne.image e)
    (fun y hy z hz ↦ hmaps _ hy hz)
    (fun y hy ↦ by
      obtain ⟨z, hz⟩ := hφne _ hy
      exact ⟨e z, by simpa using hz⟩)
    (fun y hy ↦ (hφconv _ hy).linear_preimage e.symm.toLinearEquiv.toLinearMap)
    (hgraph.preimage (e.symm.continuous.prodMap e.symm.continuous))
  exact ⟨e.symm y, hy, hyφ⟩

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
