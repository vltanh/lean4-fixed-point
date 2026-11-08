/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Brouwer.KKM
public import FixedPoint.Common.ContinuousMap
public import FixedPoint.Common.SchauderProjection
public import FixedPoint.Schauder.Limit

/-!
# Schauder's fixed-point theorem for compact convex sets

* `Schauder.exists_dist_lt`: for every `ε > 0`, a continuous self-map `f` of a nonempty compact
  convex set `s` of a real normed space moves some point of `s` by less than `3 ε`.
* `Schauder.exists_fixedPoint` (**Schauder's fixed-point theorem**, J. Schauder, *Der Fixpunktsatz
  in Funktionalräumen*, Studia Math. 2 (1930), 171–180, Satz I): `f` has a fixed point in `s`.
* `Schauder.exists_fixedPoint_continuousMap`: the same for a continuous map `C(s, s)`.

## Proof

Schauder's proof of Satz I.

1. Take `δ > 0` with `dist (f y) (f z) < ε` for `y, z ∈ s` within `δ`, and a finite `ε`-net
   `ξ 0, …, ξ m` of `s`. Its convex hull `H ⊆ s` is the image of the standard `m`-simplex `Δ`
   under `A u = ∑ k, u k • ξ k`.
2. Triangulate finely: the `n`-th barycentric subdivision of `Δ`, whose simplices `A` maps to
   simplices of `H` (possibly degenerate), each vertex within `min ε (δ / 2)` of every point of
   its simplex, so the vertices are within `δ` of each other.
   Schauder's simplicial approximation of `f` sends each vertex `d` to a point `ξ j` of the net
   within `ε` of `f d`, and is linear on each simplex: on `Δ`, the map
   `BarycentricSubdivision.interp n (fun v ↦ e (j v))`.
3. By Brouwer's theorem for the simplex, in the proof of Knaster, Kuratowski and Mazurkiewicz that
   Schauder cites (`Brouwer.KKM.exists_fixedPoint_stdSimplex`), it has a fixed point `u`, and
   `x = A u = ∑ c k • ξ (j (w k))` for the vertices `w k` of a simplex containing `u` and the
   coordinates `c` of `u` in it.
4. For the vertex `d = A (w 0)`: `dist d x < ε`, and `x` is a convex combination of points `ξ`
   within `ε` of `f (A (w k))`, which are within `ε` of `f d`, so `dist x (f d) ≤ 2 ε` by the
   convexity of the norm; hence `dist (f d) d < 3 ε`, Schauder's bound.

Schauder reaches `3 ε` through his estimate (4), that the simplicial map moves `x` and `d` less
than `ε` apart, which he derives from his condition (1) and Hilfssatz I. That does not follow as
written: the values of the simplicial map at the vertices are points of the net within
`2 ε + min ε δ(n, ε)` of each other, not within `δ(n, ε)`. The argument survives with a larger
constant; the formalization reaches `3 ε` by the estimate of step 4 instead.
5. As `ε` is arbitrary, compactness gives a fixed point
   (`Schauder.exists_fixedPoint_of_forall_dist_lt`).

Schauder triangulates `H` itself; the formalization triangulates the simplex `Δ` and maps it
onto `H`, which gives the same simplicial approximation when the points of the net are affinely
independent; Brouwer's theorem is then applied on `Δ` rather than on `H`. A second proof,
`Schauder.Projection.exists_fixedPoint`, replaces the simplicial approximation by Schauder's
projection.

Statement: Schauder states Satz I for complete metric linear spaces, not necessarily locally
convex; his proof is valid only for normed (or locally convex) spaces, where the estimate above
holds, and the general case is Schauder's problem (Scottish Book, Problem 54). The theorem
is stated here for real normed spaces, complete or not.
-/

@[expose] public section

open Set Filter Topology BarycentricSubdivision

namespace Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Schauder's approximation: for every `ε > 0`, a map that is continuous on a nonempty compact
convex set `s` of a real normed space and maps `s` into itself moves a point of `s` by less than
`3 ε`. -/
theorem exists_dist_lt {s : Set E} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)
    {f : E → E} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ s, dist (f x) x < 3 * ε := by
  classical
  -- `f` is uniformly continuous on `s`
  obtain ⟨δ, hδ, hfδ⟩ :=
    Metric.uniformContinuousOn_iff.1 (hcomp.uniformContinuousOn_of_continuous hf) ε hε
  -- an `ε`-net `ξ 0, …, ξ m` of `s`
  obtain ⟨t, hts, hcov⟩ := SchauderProjection.exists_finset_cover hcomp hε
  obtain ⟨N, ξ, hξ⟩ := (t : Set E).toFinite.fin_embedding
  obtain ⟨y₀, hy₀⟩ := hne
  cases N with
  | zero =>
    obtain ⟨c, hc, -⟩ := hcov y₀ hy₀
    have : c ∈ range ξ := hξ ▸ hc
    obtain ⟨i, -⟩ := this
    exact i.elim0
  | succ m =>
  have hξs : ∀ k, ξ k ∈ s := fun k ↦ hts (hξ ▸ mem_range_self k)
  -- `A u = ∑ k, u k • ξ k` maps the standard simplex onto the convex hull of the net
  let A : (Fin (m + 1) → ℝ) →L[ℝ] E := ∑ k, (ContinuousLinearMap.proj k).smulRight (ξ k)
  have hA : ∀ u, A u = ∑ k, u k • ξ k := fun u ↦ by simp [A]
  have hAs : ∀ u ∈ simplex m, A u ∈ s := fun u hu ↦ by
    rw [hA]
    exact hconv.sum_mem (fun k _ ↦ hu.1 k) hu.2 fun k _ ↦ hξs k
  set M : ℝ := ∑ k, ‖ξ k‖ + 1
  have hM : 0 < M := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) ↦ norm_nonneg (ξ k)
    linarith
  have hAdist : ∀ a b, dist (A a) (A b) ≤ M * l1 (a - b) := fun a b ↦ by
    rw [dist_eq_norm, ← map_sub, hA, l1, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have := Finset.single_le_sum (fun j _ ↦ norm_nonneg (ξ j)) (Finset.mem_univ k)
    linarith
  -- each point of the simplex gets the index of a point of the net within `ε` of `f (A u)`
  have hlab : ∀ u ∈ simplex m, ∃ j, dist (f (A u)) (ξ j) < ε := fun u hu ↦ by
    obtain ⟨c, hc, hdc⟩ := hcov _ (hmaps (hAs u hu))
    obtain ⟨j, rfl⟩ : c ∈ range ξ := hξ ▸ hc
    exact ⟨j, hdc⟩
  choose! lab hlab using hlab
  -- a subdivision fine enough
  have hr : (m : ℝ) / (m + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M * (2 * ((m : ℝ) / (m + 1)) ^ n) < min ε (δ / 2) := by
    have : Tendsto (fun n : ℕ ↦ M * (2 * ((m : ℝ) / (m + 1)) ^ n)) atTop (𝓝 0) := by
      simpa using
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).const_mul 2).const_mul M
    exact (this.eventually (gt_mem_nhds (lt_min hε (by positivity)))).exists
  -- Schauder's simplicial approximation, on the simplex, and its fixed point
  let g := interp n fun v ↦ (Pi.single (lab v) 1 : Fin (m + 1) → ℝ)
  obtain ⟨u, hu, hgu⟩ := Brouwer.KKM.exists_fixedPoint_stdSimplex (f := g)
    (fun v hv ↦ (convex_simplex m).sum_mem (fun k _ ↦ (coords_mem n hv).1 k) (coords_mem n hv).2
      fun k _ ↦ single_mem_simplex _) (continuousOn_interp n _)
  set w := verts n u
  set c := coords n u
  have hc : c ∈ simplex m := coords_mem n hu
  have hw : ∀ k, w k ∈ simplex m := verts_mem n hu
  have hAu : A u = ∑ k, c k • ξ (lab (w k)) := by
    conv_lhs => rw [← hgu]
    simp only [g, interp, map_sum, map_smul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [hA, Pi.single_apply]
    rfl
  -- the vertices are close to `u`
  have hclose : ∀ k, dist (A (w k)) (A u) < min ε (δ / 2) := fun k ↦
    (hAdist _ _).trans_lt ((mul_le_mul_of_nonneg_left (l1_verts_sub_le n hu k) hM.le).trans_lt hn)
  -- the vertex `d = A (w 0)`
  refine ⟨A (w 0), hAs _ (hw 0), ?_⟩
  have hfar : dist (A u) (f (A (w 0))) ≤ 2 * ε := by
    have hsplit : A u - f (A (w 0)) = ∑ k, c k • (ξ (lab (w k)) - f (A (w 0))) := by
      rw [hAu]
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hc.2, one_smul]
    rw [dist_eq_norm, hsplit]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖c k • (ξ (lab (w k)) - f (A (w 0)))‖ ≤ ∑ k, c k * (2 * ε) :=
          Finset.sum_le_sum fun k _ ↦ by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc.1 k)]
            refine mul_le_mul_of_nonneg_left ?_ (hc.1 k)
            have h1 : dist (ξ (lab (w k))) (f (A (w k))) < ε := by
              rw [dist_comm]
              exact hlab _ (hw k)
            have h2 : dist (f (A (w k))) (f (A (w 0))) < ε := by
              refine hfδ _ (hAs _ (hw k)) _ (hAs _ (hw 0)) ?_
              have h1k := (hclose k).trans_le (min_le_right _ _)
              have h10 := (hclose 0).trans_le (min_le_right _ _)
              calc dist (A (w k)) (A (w 0)) ≤ dist (A (w k)) (A u) + dist (A u) (A (w 0)) :=
                    dist_triangle _ _ _
                _ < δ / 2 + δ / 2 := add_lt_add h1k (by rw [dist_comm]; exact h10)
                _ = δ := by ring
            rw [← dist_eq_norm]
            linarith [dist_triangle (ξ (lab (w k))) (f (A (w k))) (f (A (w 0)))]
      _ = 2 * ε := by rw [← Finset.sum_mul, hc.2, one_mul]
  calc dist (f (A (w 0))) (A (w 0)) ≤ dist (f (A (w 0))) (A u) + dist (A u) (A (w 0)) :=
        dist_triangle _ _ _
    _ < 2 * ε + ε := by
        rw [dist_comm (f _)]
        exact add_lt_add_of_le_of_lt hfar ((dist_comm (A u) _).trans_lt
          ((hclose 0).trans_le (min_le_left _ _)))
    _ = 3 * ε := by ring

/-- **Schauder's fixed-point theorem**: in a real normed space, a map that is continuous on a
nonempty compact convex set `s` and maps `s` into itself has a fixed point in `s`. -/
theorem exists_fixedPoint {s : Set E} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : E → E} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x :=
  exists_fixedPoint_of_forall_dist_lt hcomp hf fun ε hε ↦ by
    obtain ⟨x, hx, hdx⟩ := exists_dist_lt hconv hcomp hne hmaps hf (div_pos hε three_pos)
    exact ⟨x, hx, by linarith⟩

/-- **Schauder's fixed-point theorem** for a continuous self-map of a nonempty compact convex set
of a real normed space. -/
theorem exists_fixedPoint_continuousMap {s : Set E} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) (f : C(s, s)) : ∃ x, f x = x :=
  FixedPoint.exists_fixedPoint_continuousMap_of
    (fun _ hmaps hf ↦ exists_fixedPoint hconv hcomp hne hmaps hf) f

end Schauder
