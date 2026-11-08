/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Common.Subdivision
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A simplex containing a bounded set

`FixedPoint.exists_simplex_coords`: a bounded set `s` of a finite-dimensional real inner product
space `F` of dimension `d` lies in a simplex with vertices `v 0, …, v d`, with barycentric
coordinates `μ x` that depend continuously on `x`: `x = ∑ k, μ x k • v k` for every `x`, and
`μ x` is in the standard simplex for `x ∈ s`. With an orthonormal basis `b` of `F` and
`s ⊆ closedBall 0 R`, the vertices are `v 0 = -R ∑ i, b i` and `v (i + 1) = v 0 + 2 d R b i`, and
`μ x (i + 1) = (⟪b i, x⟫ + R) / (2 d R)`, `μ x 0 = 1 - ∑ i, μ x (i + 1)`.

`FixedPoint.exists_subset_convexHull_simplex` is the inclusion `s ⊆ convexHull ℝ (range v)`.
-/

@[expose] public section

open Set Module BarycentricSubdivision
open scoped InnerProductSpace

namespace FixedPoint

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A bounded set lies in a simplex, with barycentric coordinates `μ x` continuous in `x`, in the
standard simplex for `x ∈ s`, and with `x = ∑ k, μ x k • v k` for every `x`. -/
theorem exists_simplex_coords {s : Set F} (hs : Bornology.IsBounded s) :
    ∃ (v : Fin (finrank ℝ F + 1) → F) (μ : F → Fin (finrank ℝ F + 1) → ℝ), Continuous μ ∧
      (∀ x, ∑ k, μ x k • v k = x) ∧ ∀ x ∈ s, μ x ∈ simplex (finrank ℝ F) := by
  obtain ⟨R, hR, hsR⟩ := hs.subset_closedBall_lt 0 0
  set d := finrank ℝ F
  let b := stdOrthonormalBasis ℝ F
  let v₀ : F := -(R • ∑ i, b i)
  let c : ℝ := 2 * d * R
  have hd : ∀ i : Fin d, (1 : ℝ) ≤ d := fun i ↦ by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.pos i).ne'
  have hc : ∀ i : Fin d, 0 < c := fun i ↦ mul_pos (mul_pos two_pos (by linarith [hd i])) hR
  let ν : F → Fin d → ℝ := fun x i ↦ (⟪b i, x⟫_ℝ + R) / c
  let μ : F → Fin (d + 1) → ℝ := fun x ↦ Fin.cons (1 - ∑ i, ν x i) (ν x)
  refine ⟨Fin.cons v₀ fun i ↦ v₀ + c • b i, μ, ?_, fun x ↦ ?_, fun x hx ↦ ?_⟩
  · have hν : ∀ i, Continuous fun x ↦ ν x i := fun i ↦
      ((continuous_const.inner continuous_id).add continuous_const).div_const c
    refine continuous_pi fun k ↦ Fin.cases ?_ (fun i ↦ ?_) k
    · simp only [μ, Fin.cons_zero]
      exact continuous_const.sub (continuous_finsetSum _ fun i _ ↦ hν i)
    · simp only [μ, Fin.cons_succ]
      exact hν i
  · have hterm : ∀ i, ν x i • (v₀ + c • b i) = ν x i • v₀ + (⟪b i, x⟫_ℝ + R) • b i :=
      fun i ↦ by rw [smul_add, smul_smul, div_mul_cancel₀ _ (hc i).ne']
    rw [Fin.sum_univ_succ]
    simp only [μ, Fin.cons_zero, Fin.cons_succ, hterm, Finset.sum_add_distrib,
      ← Finset.sum_smul, add_smul, ← Finset.smul_sum]
    have hrepr : ∑ i, ⟪b i, x⟫_ℝ • b i = x := b.sum_repr' x
    rw [hrepr]
    simp only [v₀]
    module
  · have hxR : ‖x‖ ≤ R := by simpa using hsR hx
    have hinner : ∀ i, |⟪b i, x⟫_ℝ| ≤ R := fun i ↦
      (abs_real_inner_le_norm _ _).trans (by rw [b.orthonormal.1 i, one_mul]; exact hxR)
    have hν0 : ∀ i, 0 ≤ ν x i := fun i ↦
      div_nonneg (by linarith [neg_abs_le ⟪b i, x⟫_ℝ, hinner i]) (hc i).le
    have hν1 : ∀ i, ν x i ≤ 1 / d := fun i ↦ by
      rw [div_le_div_iff₀ (hc i) (by linarith [hd i])]
      nlinarith [le_abs_self ⟪b i, x⟫_ℝ, hinner i, hd i]
    have hsum : ∑ i, ν x i ≤ 1 := by
      refine (Finset.sum_le_sum fun i _ ↦ hν1 i).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos d with h | h
      · simp [h]
      · rw [mul_one_div_cancel (by exact_mod_cast h.ne')]
    have hnonneg : ∀ k, 0 ≤ μ x k := fun k ↦ by
      induction k using Fin.cases with
      | zero =>
        simp only [μ, Fin.cons_zero]
        linarith
      | succ i =>
        simp only [μ, Fin.cons_succ]
        exact hν0 i
    refine ⟨hnonneg, ?_⟩
    rw [Fin.sum_univ_succ]
    simp [μ]

/-- A bounded set of a finite-dimensional real inner product space lies in a simplex. -/
theorem exists_subset_convexHull_simplex {s : Set F} (hs : Bornology.IsBounded s) :
    ∃ v : Fin (finrank ℝ F + 1) → F, s ⊆ convexHull ℝ (range v) := by
  obtain ⟨v, μ, -, hμv, hμs⟩ := exists_simplex_coords hs
  refine ⟨v, fun x hx ↦ ?_⟩
  rw [← hμv x]
  exact (convex_convexHull ℝ _).sum_mem (fun k _ ↦ (hμs x hx).1 k) (hμs x hx).2
    fun k _ ↦ subset_convexHull ℝ _ ⟨k, rfl⟩

end FixedPoint
