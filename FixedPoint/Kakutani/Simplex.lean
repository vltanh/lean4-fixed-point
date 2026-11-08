/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Brouwer.Convex
public import FixedPoint.Schauder.Projection
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Kakutani's fixed-point theorem for simplices

Let `S` be a closed simplex, or more generally the convex hull of a nonempty finite set, in a
finite-dimensional real normed space `V`, and `φ : V → Set V` a set-valued map that sends each
point of `S` to a nonempty convex subset of `S`, with closed graph
`{(x, y) | x ∈ S, y ∈ φ x}`. Then `x ∈ φ x` for some `x ∈ S`.

* `Kakutani.exists_fixedPoint_convexHull`: for the convex hull of a nonempty finite set;
* `Kakutani.exists_fixedPoint_simplex` (S. Kakutani, *A generalization of Brouwer's fixed point
  theorem*, Duke Math. J. 8 (1941), 457–459, Theorem 1): for a closed simplex `S.closedInterior`,
  `S : Affine.Simplex ℝ V r`.

Kakutani does not say that the values `φ x` are nonempty; his proof picks a point of each, and
the theorem fails for `φ x = ∅`, so the values are required nonempty here. His closed convex
values become convex values, closedness following from the closed graph.

## Proof

Kakutani's argument, except for the construction of the approximating maps.

1. For `δ > 0`, cover `S` by finitely many open balls of radius `δ` centered at points `c ∈ S`,
   pick `y c ∈ φ c`, and let `F x` be the average of the `y c` weighted by the partition of unity
   of Schauder's projection (`Schauder.blend`). Then `F` is continuous on `S` and maps `S` into
   `S`, so it has a fixed point `x` by Brouwer's theorem (`Brouwer.exists_fixedPoint`). By
   Carathéodory's theorem, `x = ∑ w j • y j` for `d + 1` weights `w j ≥ 0` of sum `1`, `d = dim V`,
   and points `y j ∈ φ (a j)` with `a j ∈ S` within `δ` of `x` (`Kakutani.exists_approx`).
2. Take `δ = 1 / (n + 1)`. A subsequence of `(x, w, y)` converges to some `(x₀, w₀, y₀)`, and the
   `a j` converge to `x₀` too. As the graph is closed, `y₀ j ∈ φ x₀`; as `φ x₀` is convex,
   `x₀ = ∑ w₀ j • y₀ j ∈ φ x₀`.

Departure from Kakutani's proof: Kakutani approximates `φ` by the map that is linear on each
simplex of the `n`-th barycentric subdivision of `S` and sends each of its vertices `v` to a point
of `φ v`; its fixed point is a convex combination of the values at the `r + 1` vertices of a
small simplex. Mathlib has no geometric barycentric subdivision of a simplex in a vector space, so
step 1 replaces it by the partition of unity of Schauder's projection, and Carathéodory's theorem
brings the number of points down to `d + 1`. Step 2 is Kakutani's. Brouwer's theorem is applied to
`S` as a compact convex set, and the partition of unity needs only that `S` be compact and
convex.
-/

@[expose] public section

open Set Filter Topology Module

namespace Kakutani

/-- **Carathéodory's theorem** with exactly `finrank + 1` points: a point of the convex hull of `T`
in a finite-dimensional real vector space is a convex combination of `finrank + 1` points of `T`,
repetitions and zero weights allowed. -/
theorem exists_sum_fin_eq_of_mem_convexHull {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {T : Set V} {x : V} (hx : x ∈ convexHull ℝ T) :
    ∃ (w : Fin (finrank ℝ V + 1) → ℝ) (z : Fin (finrank ℝ V + 1) → V),
      (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, z j ∈ T) ∧ ∑ j, w j • z j = x := by
  classical
  obtain ⟨ι, _, z, w, hzT, hind, hw0, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Fintype.card (Fin (finrank ℝ V + 1)) := by
    rw [Fintype.card_fin]
    exact (AffineIndependent.card_le_finrank_succ hind).trans
      (Nat.succ_le_succ (Submodule.finrank_le _))
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  have hext : ∀ j, j ∉ range e → Function.extend e w 0 j = 0 := fun j hj ↦
    Function.extend_apply' _ _ _ (by simpa using hj)
  refine ⟨Function.extend e w 0, Function.extend e z fun _ ↦ z i₀, fun j ↦ ?_, ?_,
    fun j ↦ ?_, ?_⟩
  · by_cases h : j ∈ range e
    · obtain ⟨i, rfl⟩ := h
      rw [e.injective.extend_apply]
      exact (hw0 i).le
    · rw [hext j h]
  · rw [← hw1]
    exact (Fintype.sum_of_injective e e.injective _ _ hext
      fun i ↦ (e.injective.extend_apply _ _ _).symm).symm
  · by_cases h : j ∈ range e
    · obtain ⟨i, rfl⟩ := h
      rw [e.injective.extend_apply]
      exact hzT ⟨i, rfl⟩
    · rw [Function.extend_apply' _ _ _ (by simpa using h)]
      exact hzT ⟨i₀, rfl⟩
  · rw [← hwz]
    refine (Fintype.sum_of_injective e e.injective _ _ (fun j hj ↦ ?_)
      fun i ↦ ?_).symm
    · rw [hext j hj, zero_smul]
    · rw [e.injective.extend_apply, e.injective.extend_apply]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Step 1 of Kakutani's proof, with the partition of unity of Schauder's projection in place of
the barycentric subdivision: for every `δ > 0`, some `x ∈ s` is a convex combination
`∑ w j • y j` of `finrank + 1` points `y j ∈ φ (a j)`, with `a j ∈ s` within `δ` of `x`. -/
theorem exists_approx {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)
    {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s) (hφne : ∀ x ∈ s, (φ x).Nonempty) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ x ∈ s, ∃ (w : Fin (finrank ℝ V + 1) → ℝ) (a y : Fin (finrank ℝ V + 1) → V),
      (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
        (∀ j, a j ∈ s ∧ y j ∈ φ (a j) ∧ dist (a j) x < δ) ∧ ∑ j, w j • y j = x := by
  classical
  obtain ⟨t, hts, htfin, hcover⟩ := hcomp.finite_cover_balls hδ
  have hcov : ∀ x ∈ s, ∃ c ∈ htfin.toFinset, dist x c < δ := fun x hx ↦ by
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcover hx)
    exact ⟨c, htfin.mem_toFinset.2 hc, hxc⟩
  choose! g hg using hφne
  -- the approximating map: the values `g c ∈ φ c` averaged with Schauder's partition of unity
  let F := Schauder.blend htfin.toFinset δ g
  have hT : ∀ x, g '' {c | c ∈ htfin.toFinset ∧ dist x c < δ} ⊆ s := fun x ↦ by
    rintro _ ⟨c, ⟨hc, -⟩, rfl⟩
    have hcs : c ∈ s := hts (htfin.mem_toFinset.1 hc)
    exact hmaps c hcs (hg c hcs)
  have hF : MapsTo F s s := fun x hx ↦
    convexHull_min (hT x) hconv (Schauder.blend_mem_convexHull (hcov x hx) g)
  obtain ⟨x, hx, hFx⟩ := Brouwer.exists_fixedPoint hconv hcomp hne hF
    ((Schauder.continuousOn_blend _ δ g).mono hcov)
  have hxT : x ∈ convexHull ℝ (g '' {c | c ∈ htfin.toFinset ∧ dist x c < δ}) := by
    have h := Schauder.blend_mem_convexHull (hcov x hx) g
    rwa [show Schauder.blend htfin.toFinset δ g x = x from hFx] at h
  obtain ⟨w, z, hw0, hw1, hz, hsum⟩ := exists_sum_fin_eq_of_mem_convexHull hxT
  choose a ha using hz
  refine ⟨x, hx, w, a, z, hw0, hw1, fun j ↦ ?_, hsum⟩
  obtain ⟨⟨hc, hdist⟩, hgz⟩ := ha j
  have has : a j ∈ s := hts (htfin.mem_toFinset.1 hc)
  exact ⟨has, hgz ▸ hg _ has, by rw [dist_comm]; exact hdist⟩

/-- **Kakutani's fixed-point theorem** for the convex hull `S` of a nonempty finite set in a
finite-dimensional real normed space: if `φ` sends each point of `S` to a nonempty convex subset
of `S` and its graph `{(x, y) | x ∈ S, y ∈ φ x}` is closed, then `x ∈ φ x` for some `x ∈ S`. -/
theorem exists_fixedPoint_convexHull {t : Set V} (ht : t.Finite) (htne : t.Nonempty)
    {φ : V → Set V} (hmaps : ∀ x ∈ convexHull ℝ t, φ x ⊆ convexHull ℝ t)
    (hφne : ∀ x ∈ convexHull ℝ t, (φ x).Nonempty)
    (hφconv : ∀ x ∈ convexHull ℝ t, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ convexHull ℝ t ∧ p.2 ∈ φ p.1}) :
    ∃ x ∈ convexHull ℝ t, x ∈ φ x := by
  set s := convexHull ℝ t
  have hcomp : IsCompact s := ht.isCompact_convexHull ℝ
  -- Step 1, for `δ = 1 / (n + 1)`
  choose x hx w a y hw0 hw1 hay hsum using fun n : ℕ ↦
    exists_approx (convex_convexHull ℝ t) hcomp (htne.convexHull (𝕜 := ℝ)) hmaps hφne
      (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  -- Step 2: a convergent subsequence
  have hK : IsCompact (s ×ˢ ((univ.pi fun _ : Fin (finrank ℝ V + 1) ↦ Icc (0 : ℝ) 1) ×ˢ
      univ.pi fun _ : Fin (finrank ℝ V + 1) ↦ s)) :=
    hcomp.prod ((isCompact_univ_pi fun _ ↦ isCompact_Icc).prod
      (isCompact_univ_pi fun _ ↦ hcomp))
  have hw1' : ∀ n j, w n j ≤ 1 := fun n j ↦ (hw1 n) ▸
    Finset.single_le_sum (fun i _ ↦ hw0 n i) (Finset.mem_univ j)
  obtain ⟨⟨x₀, w₀, y₀⟩, ⟨hx₀, -, -⟩, ψ, hψ, hlim⟩ :=
    hK.tendsto_subseq (x := fun n ↦ (x n, w n, y n))
      fun n ↦ ⟨hx n, fun j _ ↦ ⟨hw0 n j, hw1' n j⟩, fun j _ ↦ hmaps _ (hay n j).1 (hay n j).2.1⟩
  have hxlim : Tendsto (fun k ↦ x (ψ k)) atTop (𝓝 x₀) :=
    (continuous_fst.tendsto _).comp hlim
  have hwlim : ∀ j, Tendsto (fun k ↦ w (ψ k) j) atTop (𝓝 (w₀ j)) := fun j ↦
    (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).tendsto _).comp hlim
  have hylim : ∀ j, Tendsto (fun k ↦ y (ψ k) j) atTop (𝓝 (y₀ j)) := fun j ↦
    (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  have halim : ∀ j, Tendsto (fun k ↦ a (ψ k) j) atTop (𝓝 x₀) := fun j ↦
    hxlim.congr_dist (squeeze_zero (fun _ ↦ dist_nonneg)
      (fun k ↦ by rw [dist_comm]; exact (hay (ψ k) j).2.2.le)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop))
  -- the limits `y₀ j` lie in `φ x₀`, as the graph is closed
  have hy₀ : ∀ j, y₀ j ∈ φ x₀ := fun j ↦
    (hgraph.mem_of_tendsto ((halim j).prodMk_nhds (hylim j))
      (Eventually.of_forall fun k ↦ ⟨(hay (ψ k) j).1, (hay (ψ k) j).2.1⟩)).2
  have hw₀0 : ∀ j, 0 ≤ w₀ j := fun j ↦ ge_of_tendsto' (hwlim j) fun k ↦ hw0 (ψ k) j
  have hw₀1 : ∑ j, w₀ j = 1 :=
    tendsto_nhds_unique (tendsto_finsetSum _ fun j _ ↦ hwlim j)
      (by simpa only [hw1] using tendsto_const_nhds)
  have heq : ∑ j, w₀ j • y₀ j = x₀ :=
    tendsto_nhds_unique (tendsto_finsetSum _ fun j _ ↦ (hwlim j).smul (hylim j))
      (by simpa only [hsum] using hxlim)
  exact ⟨x₀, hx₀, heq ▸ (hφconv x₀ hx₀).sum_mem (fun j _ ↦ hw₀0 j) hw₀1 fun j _ ↦ hy₀ j⟩

/-- **Kakutani's fixed-point theorem** for a closed simplex (Kakutani 1941, Theorem 1): if `φ`
sends each point of the closed simplex `S` of a finite-dimensional real normed space to a
nonempty convex subset of `S` and its graph `{(x, y) | x ∈ S, y ∈ φ x}` is closed, then
`x ∈ φ x` for some `x ∈ S`. -/
theorem exists_fixedPoint_simplex {r : ℕ} (S : Affine.Simplex ℝ V r) {φ : V → Set V}
    (hmaps : ∀ x ∈ S.closedInterior, φ x ⊆ S.closedInterior)
    (hφne : ∀ x ∈ S.closedInterior, (φ x).Nonempty)
    (hφconv : ∀ x ∈ S.closedInterior, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ S.closedInterior ∧ p.2 ∈ φ p.1}) :
    ∃ x ∈ S.closedInterior, x ∈ φ x := by
  rw [← S.convexHull_eq_closedInterior] at hmaps hφne hφconv hgraph ⊢
  exact exists_fixedPoint_convexHull (finite_range _) (range_nonempty _) hmaps hφne hφconv hgraph

end Kakutani
