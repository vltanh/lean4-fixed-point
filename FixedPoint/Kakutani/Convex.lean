/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Kakutani.Simplex
public import FixedPoint.Common.NearestPoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

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
(`Kakutani.exists_subset_convexHull_simplex`), and is a retract of the space through the
nearest-point map `π` (`NearestPoint.exists_lipschitzWith_retraction`), Kakutani's unspecified
retraction. The map `x ↦ φ (π x)` sends `K` to nonempty convex subsets of `s ⊆ K`, with closed
graph, so `x ∈ φ (π x)` for some `x ∈ K` (`Kakutani.exists_fixedPoint_convexHull_range`). Then
`x ∈ s`, so `π x = x` and `x ∈ φ x`. A linear isomorphism `V ≃L[ℝ] EuclideanSpace ℝ (Fin n)`
reduces normed spaces to inner product spaces, as for Brouwer's theorem.

Kakutani's `s` is a bounded closed convex set; it must also be nonempty, which he leaves
implicit. A second proof, which needs no simplex, is `Kakutani.Selection.exists_fixedPoint`.
-/

@[expose] public section

open Set Filter Topology Module
open scoped InnerProductSpace

namespace Kakutani

/-- A bounded set of a finite-dimensional real inner product space lies in a simplex. With an
orthonormal basis `b` of `F`, `d = dim F` and `s ⊆ closedBall 0 R`, the simplex has the vertices
`v₀ = -R ∑ i, b i` and `v₀ + 2 d R b i`: a point `x` of the ball is
`(1 - ∑ μ i) v₀ + ∑ μ i (v₀ + 2 d R b i)` with `μ i = (⟪b i, x⟫ + R) / (2 d R)`. -/
theorem exists_subset_convexHull_simplex {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {s : Set F} (hs : Bornology.IsBounded s) :
    ∃ v : Fin (finrank ℝ F + 1) → F, s ⊆ convexHull ℝ (range v) := by
  obtain ⟨R, hR, hsR⟩ := hs.subset_closedBall_lt 0 0
  set d := finrank ℝ F
  let b := stdOrthonormalBasis ℝ F
  let v₀ : F := -(R • ∑ i, b i)
  let c : ℝ := 2 * d * R
  let v : Fin (d + 1) → F := Fin.cons v₀ fun i ↦ v₀ + c • b i
  refine ⟨v, fun x hx ↦ ?_⟩
  have hxR : ‖x‖ ≤ R := by simpa using hsR hx
  have hinner : ∀ i, |⟪b i, x⟫_ℝ| ≤ R := fun i ↦
    (abs_real_inner_le_norm _ _).trans (by rw [b.orthonormal.1 i, one_mul]; exact hxR)
  have hd : ∀ i : Fin d, (1 : ℝ) ≤ d := fun i ↦ by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.pos i).ne'
  have hc : ∀ i : Fin d, 0 < c := fun i ↦ mul_pos (mul_pos two_pos (by linarith [hd i])) hR
  let μ : Fin d → ℝ := fun i ↦ (⟪b i, x⟫_ℝ + R) / c
  have hμ0 : ∀ i, 0 ≤ μ i := fun i ↦
    div_nonneg (by linarith [neg_abs_le ⟪b i, x⟫_ℝ, hinner i]) (hc i).le
  have hμ1 : ∀ i, μ i ≤ 1 / d := fun i ↦ by
    rw [div_le_div_iff₀ (hc i) (by linarith [hd i])]
    nlinarith [le_abs_self ⟪b i, x⟫_ℝ, hinner i, hd i]
  have hsum : ∑ i, μ i ≤ 1 := by
    refine (Finset.sum_le_sum fun i _ ↦ hμ1 i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · rw [mul_one_div_cancel (by exact_mod_cast h.ne')]
  let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, μ i) μ
  have hterm : ∀ i, μ i • (v₀ + c • b i) = μ i • v₀ + (⟪b i, x⟫_ℝ + R) • b i := fun i ↦ by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ (hc i).ne']
  have heq : ∑ j, w j • v j = x := by
    rw [Fin.sum_univ_succ]
    simp only [w, v, Fin.cons_zero, Fin.cons_succ, hterm, Finset.sum_add_distrib,
      ← Finset.sum_smul, add_smul, ← Finset.smul_sum]
    have hrepr : ∑ i, ⟪b i, x⟫_ℝ • b i = x := b.sum_repr' x
    rw [hrepr]
    simp only [v₀]
    module
  rw [← heq]
  refine (convex_convexHull ℝ _).sum_mem (fun j _ ↦ ?_) ?_ fun j _ ↦ subset_convexHull ℝ _ ⟨j, rfl⟩
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp only [w, Fin.cons_zero]
      linarith
    · simp only [w, Fin.cons_succ]
      exact hμ0 i
  · rw [Fin.sum_univ_succ]
    simp [w]

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
  obtain ⟨v, hsK⟩ := exists_subset_convexHull_simplex hcomp.isBounded
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
