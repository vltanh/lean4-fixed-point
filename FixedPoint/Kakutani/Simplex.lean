/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Brouwer.Convex
public import FixedPoint.Kakutani.Limit
public import FixedPoint.Simplex.Subdivision
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Kakutani's fixed-point theorem for simplices

Let `S` be a closed simplex, or more generally the convex hull of finitely many points, in a real
normed space `V`, and `φ : V → Set V` a set-valued map that sends each point of `S` to a nonempty
convex subset of `S`, with closed graph `{(x, y) | x ∈ S, y ∈ φ x}`. Then `x ∈ φ x` for some
`x ∈ S`.

* `Kakutani.exists_fixedPoint_stdSimplex`: for the standard simplex of `Fin (r + 1) → ℝ`;
* `Kakutani.exists_fixedPoint_simplex` (S. Kakutani, *A generalization of Brouwer's fixed point
  theorem*, Duke Math. J. 8 (1941), 457–459, Theorem 1): for a closed simplex `S.closedInterior`,
  `S : Affine.Simplex ℝ V r`;
* `Kakutani.exists_fixedPoint_convexHull_range`, `Kakutani.exists_fixedPoint_convexHull`: for the
  convex hull of finitely many points.

Kakutani does not say that the values `φ x` are nonempty; his proof picks a point of each, and
the theorem fails for `φ x = ∅`, so the values are required nonempty here. His closed convex
values become convex values, closedness following from the closed graph.

## Proof

Kakutani's proof, on the standard simplex `Δ`.

1. Pick `y v ∈ φ v` for each `v ∈ Δ`. The map `φₙ = BarycentricSubdivision.interp n y`, linear on
   each simplex of the `n`-th barycentric subdivision of `Δ` with the value `y v` at each vertex
   `v`, is continuous and maps `Δ` into itself, so it has a fixed point `xₙ` by Brouwer's theorem
   (`Brouwer.exists_fixedPoint`).
2. If `xₙ` lies in the simplex of the subdivision with vertices `xₙᵢ` and `xₙ = ∑ λₙᵢ xₙᵢ`, then
   `xₙ = φₙ xₙ = ∑ λₙᵢ y (xₙᵢ)`, with `y (xₙᵢ) ∈ φ (xₙᵢ)`, and the vertices are within
   `2 (r / (r + 1)) ^ n` of `xₙ` (`BarycentricSubdivision.dist_verts_le`).
3. Along a subsequence, `xₙ → x₀`, `λₙ → λ₀` and `y (xₙᵢ) → y₀ᵢ`; then `xₙᵢ → x₀`, so
   `y₀ᵢ ∈ φ x₀` by the closed graph, and `x₀ = ∑ λ₀ᵢ y₀ᵢ ∈ φ x₀` by convexity
   (`Kakutani.exists_mem_self_of_approx`).

A simplex `S` with vertices `v 0, …, v r` in `V` is the image of `Δ` under the linear map
`A u = ∑ u k • v k`, which maps the subdivisions of `Δ` to those of `S`; the theorem for `S`
follows from the theorem on `Δ` for `u ↦ {u' ∈ Δ | A u' ∈ φ (A u)}`. This change of coordinates is
the only difference from Kakutani's text, which subdivides `S` itself. It does not use that the
vertices are affinely independent, so the theorem holds for convex hulls of finitely many points.
-/

@[expose] public section

open Set Filter Topology BarycentricSubdivision

namespace Kakutani

/-- **Kakutani's fixed-point theorem** for the standard simplex `Δ` of `Fin (r + 1) → ℝ`, by
Kakutani's proof: if `φ` sends each point of `Δ` to a nonempty convex subset of `Δ` and its graph
`{(x, y) | x ∈ Δ, y ∈ φ x}` is closed, then `x ∈ φ x` for some `x ∈ Δ`. -/
theorem exists_fixedPoint_stdSimplex {r : ℕ} {φ : (Fin (r + 1) → ℝ) → Set (Fin (r + 1) → ℝ)}
    (hmaps : ∀ x ∈ simplex r, φ x ⊆ simplex r) (hφne : ∀ x ∈ simplex r, (φ x).Nonempty)
    (hφconv : ∀ x ∈ simplex r, Convex ℝ (φ x))
    (hgraph : IsClosed {p : (Fin (r + 1) → ℝ) × (Fin (r + 1) → ℝ) |
      p.1 ∈ simplex r ∧ p.2 ∈ φ p.1}) :
    ∃ x ∈ simplex r, x ∈ φ x := by
  choose! y hy using hφne
  -- Step 1: `φₙ = interp n y` has a fixed point `x n`, by Brouwer's theorem
  have hfix : ∀ n : ℕ, ∃ x ∈ simplex r, interp n y x = x := fun n ↦
    Brouwer.exists_fixedPoint (convex_simplex r) (isCompact_simplex r) ⟨_, single_mem_simplex 0⟩
      (fun x hx ↦ (convex_simplex r).sum_mem (fun k _ ↦ (coords_mem n hx).1 k)
        (coords_mem n hx).2 fun k _ ↦ hmaps _ (verts_mem n hx k) (hy _ (verts_mem n hx k)))
      (continuousOn_interp n y)
  choose x hx hxfix using hfix
  -- Steps 2 and 3: `x n = ∑ λₙᵢ y (xₙᵢ)` with vertices `xₙᵢ` close to `x n`, and the limit
  have hr : (r : ℝ) / (r + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hδ : Tendsto (fun n : ℕ ↦ 2 * ((r : ℝ) / (r + 1)) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).const_mul 2
  exact exists_mem_self_of_approx (isCompact_simplex r) hmaps hφconv hgraph (x := x)
    (w := fun n ↦ coords n (x n)) (a := fun n ↦ verts n (x n))
    (y := fun n k ↦ y (verts n (x n) k)) hδ hx (fun n k ↦ (coords_mem n (hx n)).1 k)
    (fun n ↦ (coords_mem n (hx n)).2)
    (fun n k ↦ ⟨verts_mem n (hx n) k, hy _ (verts_mem n (hx n) k), dist_verts_le n (hx n) k⟩)
    hxfix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Kakutani's fixed-point theorem** for the convex hull `S` of finitely many points
`v 0, …, v r` of a real normed space: if `φ` sends each point of `S` to a nonempty convex subset
of `S` and its graph `{(x, y) | x ∈ S, y ∈ φ x}` is closed, then `x ∈ φ x` for some `x ∈ S`. -/
theorem exists_fixedPoint_convexHull_range {r : ℕ} (v : Fin (r + 1) → V) {φ : V → Set V}
    (hmaps : ∀ x ∈ convexHull ℝ (range v), φ x ⊆ convexHull ℝ (range v))
    (hφne : ∀ x ∈ convexHull ℝ (range v), (φ x).Nonempty)
    (hφconv : ∀ x ∈ convexHull ℝ (range v), Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ convexHull ℝ (range v) ∧ p.2 ∈ φ p.1}) :
    ∃ x ∈ convexHull ℝ (range v), x ∈ φ x := by
  set K := convexHull ℝ (range v)
  -- the linear map `A u = ∑ u k • v k` maps the standard simplex onto `K`
  let A : (Fin (r + 1) → ℝ) →L[ℝ] V := ∑ k, (ContinuousLinearMap.proj k).smulRight (v k)
  have hA : ∀ u, A u = ∑ k, u k • v k := fun u ↦ by simp [A]
  have himage : A '' simplex r = K := by
    apply subset_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [hA]
      exact (convex_convexHull ℝ _).sum_mem (fun k _ ↦ hu.1 k) hu.2
        fun k _ ↦ subset_convexHull ℝ _ ⟨k, rfl⟩
    · refine convexHull_min ?_ ((convex_simplex r).linear_image A.toLinearMap)
      rintro _ ⟨k, rfl⟩
      exact ⟨Pi.single k 1, single_mem_simplex k, by simp [hA, Pi.single_apply]⟩
  have hAK : ∀ u ∈ simplex r, A u ∈ K := fun u hu ↦ himage ▸ mem_image_of_mem A hu
  -- the set-valued map `u ↦ {u' ∈ Δ | A u' ∈ φ (A u)}` on the standard simplex
  let ψ : (Fin (r + 1) → ℝ) → Set (Fin (r + 1) → ℝ) := fun u ↦ simplex r ∩ A ⁻¹' φ (A u)
  have hψne : ∀ u ∈ simplex r, (ψ u).Nonempty := fun u hu ↦ by
    obtain ⟨z, hz⟩ := hφne _ (hAK u hu)
    have hzK : z ∈ A '' simplex r := himage ▸ hmaps _ (hAK u hu) hz
    obtain ⟨u', hu', rfl⟩ := hzK
    exact ⟨u', hu', hz⟩
  have hψgraph : IsClosed {p : (Fin (r + 1) → ℝ) × (Fin (r + 1) → ℝ) |
      p.1 ∈ simplex r ∧ p.2 ∈ ψ p.1} := by
    have : {p : (Fin (r + 1) → ℝ) × (Fin (r + 1) → ℝ) | p.1 ∈ simplex r ∧ p.2 ∈ ψ p.1} =
        (simplex r ×ˢ simplex r) ∩ Prod.map A A ⁻¹' {q : V × V | q.1 ∈ K ∧ q.2 ∈ φ q.1} := by
      ext ⟨p₁, p₂⟩
      simp only [ψ, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod, Prod.map]
      exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂⟩, hAK _ h₁, h₃⟩, fun ⟨⟨h₁, h₂⟩, _, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩
    rw [this]
    exact ((isClosed_simplex r).prod (isClosed_simplex r)).inter
      (hgraph.preimage (A.continuous.prodMap A.continuous))
  obtain ⟨u, hu, hψu⟩ := exists_fixedPoint_stdSimplex (φ := ψ) (fun _ _ ↦ inter_subset_left)
    hψne (fun u hu ↦ (convex_simplex r).inter ((hφconv _ (hAK u hu)).linear_preimage A.toLinearMap))
    hψgraph
  exact ⟨A u, hAK u hu, hψu.2⟩

/-- **Kakutani's fixed-point theorem** for a closed simplex (Kakutani 1941, Theorem 1): if `φ`
sends each point of the closed simplex `S` of a real normed space to a nonempty convex subset of
`S` and its graph `{(x, y) | x ∈ S, y ∈ φ x}` is closed, then `x ∈ φ x` for some `x ∈ S`. -/
theorem exists_fixedPoint_simplex {r : ℕ} (S : Affine.Simplex ℝ V r) {φ : V → Set V}
    (hmaps : ∀ x ∈ S.closedInterior, φ x ⊆ S.closedInterior)
    (hφne : ∀ x ∈ S.closedInterior, (φ x).Nonempty)
    (hφconv : ∀ x ∈ S.closedInterior, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ S.closedInterior ∧ p.2 ∈ φ p.1}) :
    ∃ x ∈ S.closedInterior, x ∈ φ x := by
  rw [← S.convexHull_eq_closedInterior] at hmaps hφne hφconv hgraph ⊢
  exact exists_fixedPoint_convexHull_range S.points hmaps hφne hφconv hgraph

/-- **Kakutani's fixed-point theorem** for the convex hull `S` of a nonempty finite set of a real
normed space: if `φ` sends each point of `S` to a nonempty convex subset of `S` and its graph
`{(x, y) | x ∈ S, y ∈ φ x}` is closed, then `x ∈ φ x` for some `x ∈ S`. -/
theorem exists_fixedPoint_convexHull {t : Set V} (ht : t.Finite) (htne : t.Nonempty)
    {φ : V → Set V} (hmaps : ∀ x ∈ convexHull ℝ t, φ x ⊆ convexHull ℝ t)
    (hφne : ∀ x ∈ convexHull ℝ t, (φ x).Nonempty)
    (hφconv : ∀ x ∈ convexHull ℝ t, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ convexHull ℝ t ∧ p.2 ∈ φ p.1}) :
    ∃ x ∈ convexHull ℝ t, x ∈ φ x := by
  obtain ⟨n, f, rfl⟩ := ht.fin_embedding
  cases n with
  | zero =>
    obtain ⟨_, ⟨i, -⟩⟩ := htne
    exact i.elim0
  | succ r => exact exists_fixedPoint_convexHull_range (fun i ↦ f i) hmaps hφne hφconv hgraph

end Kakutani
