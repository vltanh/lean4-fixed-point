/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Common.ContinuousMap
public import FixedPoint.Common.EnclosingSimplex
public import FixedPoint.Common.Euclidean
public import FixedPoint.Common.NearestPoint
public import FixedPoint.Common.Sperner
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Brouwer's theorem through the Knaster–Kuratowski–Mazurkiewicz lemma

A second proof of Brouwer's fixed-point theorem, after B. Knaster, C. Kuratowski and
S. Mazurkiewicz, *Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe*, Fund. Math. 14
(1929), 132–137. It uses Sperner's lemma and nothing of the analytic proof.

* `Brouwer.KKM.exists_mem_iInter` (**the KKM lemma**): if closed sets `F 0, …, F r` cover each
  face of the standard simplex `Δ` spanned by the vertices `e i`, `i ∈ I`, by the sets `F i`,
  `i ∈ I`, then they have a common point in `Δ`.
* `Brouwer.KKM.exists_fixedPoint_stdSimplex`: a continuous self-map `f` of `Δ` has a fixed point.
* `Brouwer.KKM.exists_fixedPoint`, `Brouwer.KKM.exists_fixedPoint_continuousMap`: Brouwer's
  theorem for compact convex sets of finite-dimensional real normed spaces.

## Proof

1. **KKM lemma.** Label each point `v ∈ Δ` by some `i` with `v i ≠ 0` and `v ∈ F i`: the face of
   `Δ` spanned by the `e i` with `v i ≠ 0` contains `v` and is covered by these `F i`. This is a
   Sperner labeling, so a simplex of the `n`-th barycentric subdivision carries all the labels
   (`Sperner.count_eq_one`, `Sperner.exists_cell`): it has a vertex in each `F i`, and its vertices
   are within `2 (r / (r + 1)) ^ n` of each other. Along a subsequence, its first vertex converges
   to some `x`; then so do the others, and `x ∈ F i` for every `i` as the `F i` are closed.
2. **Brouwer's theorem for `Δ`.** The sets `F i = {x ∈ Δ | f x i ≤ x i}` are closed, and they cover
   the face spanned by the `e i`, `i ∈ I`: there `∑ i ∈ I, x i = 1 ≥ ∑ i ∈ I, f x i`. A common
   point `x` has `f x i ≤ x i` for every `i`, and both sum to `1`, so `f x = x`.
3. **Compact convex sets.** In an inner product space, `s` lies in a simplex with vertices `v k`
   and continuous barycentric coordinates `μ` (`FixedPoint.exists_simplex_coords`), and is a
   retract of the space through the nearest-point map `π`. A fixed point `u` of
   `u ↦ μ (f (π (∑ k, u k • v k)))` on `Δ` gives the fixed point `x = ∑ k, u k • v k` of `f ∘ π`,
   which lies in `s`, so `f x = x`. A linear isomorphism with Euclidean space gives normed spaces
   (`FixedPoint.exists_fixedPoint_of_euclidean`).

KKM cover a simplex by closed sets and apply Sperner's lemma to fine simplicial subdivisions of
it; the subdivisions here are the iterated barycentric ones.
-/

@[expose] public section

open Set Filter Topology Module BarycentricSubdivision

namespace Brouwer.KKM

/-- **The Knaster–Kuratowski–Mazurkiewicz lemma**: if closed sets `F 0, …, F r` are such that,
for every set `I` of indices, the face of the standard simplex spanned by the vertices `e i`,
`i ∈ I`, is covered by the `F i`, `i ∈ I`, then the `F i` have a common point in the simplex. -/
theorem exists_mem_iInter {r : ℕ} {F : Fin (r + 1) → Set (Fin (r + 1) → ℝ)}
    (hF : ∀ i, IsClosed (F i))
    (hface : ∀ I : Finset (Fin (r + 1)),
      convexHull ℝ ((fun i ↦ (Pi.single i 1 : Fin (r + 1) → ℝ)) '' I) ⊆ ⋃ i ∈ I, F i) :
    ∃ x ∈ simplex r, ∀ i, x ∈ F i := by
  classical
  -- a Sperner labeling by the sets `F i`
  have hlabel : ∀ v ∈ simplex r, ∃ i, v i ≠ 0 ∧ v ∈ F i := fun v hv ↦ by
    let I := Finset.univ.filter fun i ↦ v i ≠ 0
    have hvI : v ∈ convexHull ℝ ((fun i ↦ (Pi.single i 1 : Fin (r + 1) → ℝ)) '' I) := by
      have hsum : ∑ i ∈ I, v i • (Pi.single i 1 : Fin (r + 1) → ℝ) = v := by
        rw [Finset.sum_filter]
        have hterm : ∀ i, (if v i ≠ 0 then v i • (Pi.single i 1 : Fin (r + 1) → ℝ) else 0) =
            v i • Pi.single i 1 := fun i ↦ by
          by_cases h : v i = 0
          · simp [h]
          · simp [h]
        simp_rw [hterm]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [← hsum]
      refine (convex_convexHull ℝ _).sum_mem (fun i _ ↦ hv.1 i) ?_
        fun i hi ↦ subset_convexHull ℝ _ ⟨i, hi, rfl⟩
      rw [Finset.sum_filter_ne_zero]
      exact hv.2
    obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.1 (hface I hvI)
    exact ⟨i, (Finset.mem_filter.1 hi).2, hvi⟩
  choose! lab hlab using hlabel
  -- for each `n`, a simplex of the `n`-th subdivision carrying all the labels
  have hcell : ∀ n : ℕ, ∃ w : Fin (r + 1) → Fin (r + 1) → ℝ, (∀ k, w k ∈ simplex r) ∧
      Finset.univ.image (lab ∘ w) = Finset.univ ∧
        ∀ j k, l1 (w j - w k) ≤ 2 * ((r : ℝ) / (r + 1)) ^ n := fun n ↦
    Sperner.exists_cell n (by
      rw [Sperner.count_eq_one r n lab fun v hv ↦ (hlab v hv).1]
      exact one_ne_zero)
  choose w hw himg hdist using hcell
  have hvert : ∀ n i, ∃ k, lab (w n k) = i := fun n i ↦ by
    have : i ∈ Finset.univ.image (lab ∘ w n) := (himg n).symm ▸ Finset.mem_univ i
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 this
    exact ⟨k, hk⟩
  choose k hk using hvert
  -- a convergent subsequence of the vertices `w n 0`
  obtain ⟨x, hx, ψ, hψ, hlim⟩ := (isCompact_simplex r).tendsto_subseq (x := fun n ↦ w n 0)
    fun n ↦ hw n 0
  have hr : (r : ℝ) / (r + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hδ : Tendsto (fun m ↦ 2 * ((r : ℝ) / (r + 1)) ^ ψ m) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).comp
      hψ.tendsto_atTop).const_mul 2
  refine ⟨x, hx, fun i ↦ ?_⟩
  -- the vertex labeled `i` converges to `x` too
  have hlim_i : Tendsto (fun m ↦ w (ψ m) (k (ψ m) i)) atTop (𝓝 x) :=
    hlim.congr_dist (squeeze_zero (fun _ ↦ dist_nonneg)
      (fun m ↦ (dist_le_l1 _ _).trans (hdist (ψ m) 0 (k (ψ m) i))) hδ)
  refine (hF i).mem_of_tendsto hlim_i (Eventually.of_forall fun m ↦ ?_)
  have := (hlab _ (hw (ψ m) (k (ψ m) i))).2
  rwa [hk] at this

/-- **Brouwer's fixed-point theorem** for the standard simplex, by the KKM lemma. -/
theorem exists_fixedPoint_stdSimplex {r : ℕ} {f : (Fin (r + 1) → ℝ) → Fin (r + 1) → ℝ}
    (hmaps : MapsTo f (simplex r) (simplex r)) (hf : ContinuousOn f (simplex r)) :
    ∃ x ∈ simplex r, f x = x := by
  classical
  let F : Fin (r + 1) → Set (Fin (r + 1) → ℝ) := fun i ↦ simplex r ∩ {x | f x i ≤ x i}
  have hF : ∀ i, IsClosed (F i) := fun i ↦
    ((continuous_apply i).comp_continuousOn hf |>.prodMk
      (continuous_apply i).continuousOn).preimage_isClosed_of_isClosed (isClosed_simplex r)
      (isClosed_le continuous_fst continuous_snd)
  -- the face spanned by the `e i`, `i ∈ I`, is covered by the `F i`, `i ∈ I`
  have hface : ∀ I : Finset (Fin (r + 1)),
      convexHull ℝ ((fun i ↦ (Pi.single i 1 : Fin (r + 1) → ℝ)) '' I) ⊆ ⋃ i ∈ I, F i := by
    intro I x hx
    have hxface : x ∈ simplex r ∩ {x | ∀ i ∉ I, x i = 0} := by
      refine convexHull_min ?_ ((convex_simplex r).inter ?_) hx
      · rintro _ ⟨i, hi, rfl⟩
        exact ⟨single_mem_simplex i, fun j hj ↦ by
          simp [show j ≠ i from fun h ↦ hj (h ▸ hi)]⟩
      · intro a ha b hb s t _ _ _ i hi
        simp [ha i hi, hb i hi]
    obtain ⟨hxs, hx0⟩ := hxface
    have hIne : I.Nonempty := by
      by_contra hI
      rw [Finset.not_nonempty_iff_eq_empty] at hI
      subst hI
      have h0 : ∑ i, x i = 0 := Finset.sum_eq_zero fun i _ ↦ hx0 i (Finset.notMem_empty i)
      linarith [hxs.2]
    by_contra hcon
    simp only [mem_iUnion, not_exists] at hcon
    have hlt : ∀ i ∈ I, x i < f x i := fun i hi ↦ by
      by_contra h
      exact hcon i hi ⟨hxs, not_lt.1 h⟩
    have hxI : ∑ i ∈ I, x i = 1 := by
      rw [← hxs.2, Finset.sum_subset (Finset.subset_univ I) fun i _ hi ↦ hx0 i hi]
    have hfI : ∑ i ∈ I, f x i ≤ 1 := (hmaps hxs).2 ▸
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) fun i _ _ ↦ (hmaps hxs).1 i
    have := Finset.sum_lt_sum_of_nonempty hIne hlt
    linarith
  obtain ⟨x, hx, hxF⟩ := exists_mem_iInter hF hface
  refine ⟨x, hx, ?_⟩
  -- `f x i ≤ x i` for every `i`, and both sum to `1`
  have hle : ∀ i ∈ Finset.univ, f x i ≤ x i := fun i _ ↦ (hxF i).2
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [(hmaps hx).2, hx.2])
  exact funext fun i ↦ heq i (Finset.mem_univ i)

/-- Brouwer's theorem for compact convex sets of a finite-dimensional real inner product space,
by the KKM lemma. -/
theorem exists_fixedPoint_of_innerProductSpace {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {s : Set F} (hconv : Convex ℝ s)
    (hcomp : IsCompact s) (hne : s.Nonempty) {f : F → F} (hmaps : MapsTo f s s)
    (hf : ContinuousOn f s) : ∃ x ∈ s, f x = x := by
  obtain ⟨π, hπ, hπs, hπfix⟩ :=
    NearestPoint.exists_lipschitzWith_retraction hne hcomp.isClosed hconv
  obtain ⟨v, μ, hμ, hμv, hμs⟩ := FixedPoint.exists_simplex_coords hcomp.isBounded
  let A : (Fin (finrank ℝ F + 1) → ℝ) →L[ℝ] F :=
    ∑ k, (ContinuousLinearMap.proj k).smulRight (v k)
  have hA : ∀ u, A u = ∑ k, u k • v k := fun u ↦ by simp [A]
  have hcont : Continuous fun u ↦ μ (f (π (A u))) :=
    hμ.comp (hf.comp_continuous (hπ.continuous.comp A.continuous) fun u ↦ hπs _)
  obtain ⟨u, -, hu⟩ := exists_fixedPoint_stdSimplex (f := fun u ↦ μ (f (π (A u))))
    (fun u _ ↦ hμs _ (hmaps (hπs _))) hcont.continuousOn
  have hx : A u = f (π (A u)) := by
    conv_lhs => rw [← hu]
    rw [hA, hμv]
  have hxs : A u ∈ s := hx ▸ hmaps (hπs _)
  exact ⟨A u, hxs, by rw [hπfix _ hxs] at hx; exact hx.symm⟩

/-- **Brouwer's fixed-point theorem**, proved through the KKM lemma: in a finite-dimensional real
normed space, a map that is continuous on a nonempty compact convex set `s` and maps `s` into
itself has a fixed point in `s`. -/
theorem exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x :=
  FixedPoint.exists_fixedPoint_of_euclidean
    (fun _ hconv hcomp hne _ hmaps hf ↦ exists_fixedPoint_of_innerProductSpace hconv hcomp hne
      hmaps hf) hconv hcomp hne hmaps hf

/-- **Brouwer's fixed-point theorem** for a continuous self-map of a nonempty compact convex set
of a finite-dimensional real normed space, proved through the KKM lemma. -/
theorem exists_fixedPoint_continuousMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) (f : C(s, s)) : ∃ x, f x = x :=
  FixedPoint.exists_fixedPoint_continuousMap_of
    (fun _ hmaps hf ↦ exists_fixedPoint hconv hcomp hne hmaps hf) f

end Brouwer.KKM
