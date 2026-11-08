/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact

/-!
# Iterated barycentric subdivisions of the standard simplex

Let `Δ = BarycentricSubdivision.simplex r = {x : Fin (r + 1) → ℝ | x ≥ 0, ∑ x = 1}` be the
standard `r`-simplex. Its barycentric subdivision has one piece for each ordering of the vertices:
for a permutation `σ`, the piece `{x ∈ Δ | x (σ 0) ≥ x (σ 1) ≥ ⋯ ≥ x (σ r)}` is the simplex whose
`k`-th vertex is the barycenter `vertex σ k` of `e (σ 0), …, e (σ k)`. A point `x` of the piece
is `x = ∑ k, coord σ x k • vertex σ k` with the barycentric coordinates
`coord σ x k = (k + 1) (x (σ k) - x (σ (k + 1)))`, `x (σ (r + 1)) = 0` (`vmap_coord`), and the
linear map `vmap σ : e k ↦ vertex σ k` maps `Δ` onto the piece.

The `n`-th barycentric subdivision subdivides each piece of the `(n - 1)`-th; equivalently, its
pieces are the images under the maps `vmap σ` of the pieces of the `(n - 1)`-th subdivision of
`Δ`. For `x ∈ Δ`, sorted by `σ = Tuple.sortDesc x`:

* `verts n x k`, `k = 0, …, r`, are the vertices of a piece of the `n`-th subdivision that
  contains `x`, and `coords n x` are the barycentric coordinates of `x` in it
  (`sum_coords_smul_verts`): `verts (n + 1) x = vmap σ ∘ verts n (coord σ x)` and
  `coords (n + 1) x = coords n (coord σ x)`;
* `interp n g x = ∑ k, coords n x k • g (verts n x k)` is the map that is linear on each piece of
  the `n`-th subdivision and takes the values `g v` at its vertices `v`;
* `continuousOn_interp`: `interp n g` is continuous on `Δ`, whatever `g`. On the piece of `σ` it
  is `interp (n - 1) (g ∘ vmap σ) ∘ coord σ` (`interp_succ`), since two orderings of `x` give the
  same coordinates and the same vertices wherever the coordinates do not vanish (`coord_eq`,
  `vertex_eq`); the pieces are closed and finitely many;
* `dist_verts_le`: the vertices are within `2 (r / (r + 1)) ^ n` of `x`, because `vmap σ`
  contracts the `ℓ¹` distance between points of `Δ` by `r / (r + 1)` (`l1_vmap_le`): every
  `vertex σ k` gives the weight at least `1 / (r + 1)` to `e (σ 0)`.
-/

@[expose] public section

open Set Finset Function

namespace BarycentricSubdivision

variable {r : ℕ}

/-! ### The standard simplex -/

/-- The standard `r`-simplex `{x | x ≥ 0, ∑ x = 1}` in `Fin (r + 1) → ℝ`. -/
def simplex (r : ℕ) : Set (Fin (r + 1) → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem convex_simplex (r : ℕ) : Convex ℝ (simplex r) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i ↦ ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hx.2, hy.2, mul_one, hab]

theorem isClosed_simplex (r : ℕ) : IsClosed (simplex r) := by
  have : simplex r = (⋂ i, {x : Fin (r + 1) → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i = 1} := by
    ext x
    simp [simplex]
  rw [this]
  exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const)

theorem le_one_of_mem_simplex {x : Fin (r + 1) → ℝ} (hx : x ∈ simplex r) (i : Fin (r + 1)) :
    x i ≤ 1 :=
  hx.2 ▸ Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)

theorem isCompact_simplex (r : ℕ) : IsCompact (simplex r) :=
  (isCompact_univ_pi fun _ ↦ isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    (isClosed_simplex r) fun _ hx i _ ↦ ⟨hx.1 i, le_one_of_mem_simplex hx i⟩

theorem single_mem_simplex (k : Fin (r + 1)) : (Pi.single k 1 : Fin (r + 1) → ℝ) ∈ simplex r :=
  ⟨fun i ↦ by by_cases h : i = k <;> simp [h], by simp⟩

/-! ### One barycentric subdivision -/

/-- The values of `x` in the order `σ`, `x (σ 0), …, x (σ r)`, followed by zeros. -/
noncomputable def sorted (σ : Equiv.Perm (Fin (r + 1))) (x : Fin (r + 1) → ℝ) (j : ℕ) : ℝ :=
  if h : j < r + 1 then x (σ ⟨j, h⟩) else 0

/-- The barycentric coordinates of `x` in the piece of `σ`:
`(k + 1) (x (σ k) - x (σ (k + 1)))`, with `x (σ (r + 1)) = 0`. -/
noncomputable def coord (σ : Equiv.Perm (Fin (r + 1))) (x : Fin (r + 1) → ℝ) :
    Fin (r + 1) → ℝ :=
  fun k ↦ ((k : ℕ) + 1 : ℝ) * (sorted σ x k - sorted σ x (k + 1))

/-- The `k`-th vertex of the piece of `σ`: the barycenter of `e (σ 0), …, e (σ k)`. -/
noncomputable def vertex (σ : Equiv.Perm (Fin (r + 1))) (k : Fin (r + 1)) : Fin (r + 1) → ℝ :=
  fun i ↦ if (σ.symm i : ℕ) ≤ k then ((k : ℕ) + 1 : ℝ)⁻¹ else 0

/-- The linear map sending `e k` to `vertex σ k`; it maps the simplex onto the piece of `σ`. -/
noncomputable def vmap (σ : Equiv.Perm (Fin (r + 1))) :
    (Fin (r + 1) → ℝ) →ₗ[ℝ] Fin (r + 1) → ℝ :=
  ∑ k, (LinearMap.proj k : (Fin (r + 1) → ℝ) →ₗ[ℝ] ℝ).smulRight (vertex σ k)

theorem vmap_apply (σ : Equiv.Perm (Fin (r + 1))) (u : Fin (r + 1) → ℝ) :
    vmap σ u = ∑ k, u k • vertex σ k := by
  simp [vmap]

theorem sum_range_ite_sub (f : ℕ → ℝ) (j : ℕ) :
    ∀ n, ∑ k ∈ range n, (if j ≤ k then f k - f (k + 1) else 0) = if j ≤ n then f j - f n else 0
  | 0 => by
    by_cases h : j ≤ 0
    · obtain rfl : j = 0 := by omega
      simp
    · simp [h]
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_ite_sub f j n]
    by_cases h : j ≤ n
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left (by omega)]
      ring
    · by_cases h' : j = n + 1
      · subst h'
        simp
      · rw [ite_eq_right h, ite_eq_right h, ite_eq_right (by omega), add_zero]

theorem sum_range_mul_sub (f : ℕ → ℝ) :
    ∀ n, ∑ k ∈ range n, ((k : ℝ) + 1) * (f k - f (k + 1)) = ∑ k ∈ range n, f k - n * f n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, sum_range_mul_sub f n]
    push_cast
    ring

theorem sorted_last (σ : Equiv.Perm (Fin (r + 1))) (x : Fin (r + 1) → ℝ) :
    sorted σ x (r + 1) = 0 := by
  simp [sorted]

theorem sorted_val (σ : Equiv.Perm (Fin (r + 1))) (x : Fin (r + 1) → ℝ) (j : Fin (r + 1)) :
    sorted σ x j = x (σ j) := by
  simp [sorted, j.isLt]

/-- The point with the coordinates `coord σ x` in the piece of `σ` is `x`. -/
theorem vmap_coord (σ : Equiv.Perm (Fin (r + 1))) (x : Fin (r + 1) → ℝ) :
    vmap σ (coord σ x) = x := by
  ext i
  rw [vmap_apply, Finset.sum_apply]
  have hterm : ∀ k : Fin (r + 1), (coord σ x k • vertex σ k) i =
      if (σ.symm i : ℕ) ≤ (k : ℕ) then sorted σ x k - sorted σ x (k + 1) else 0 := by
    intro k
    simp only [Pi.smul_apply, smul_eq_mul, coord, vertex]
    split_ifs
    · field_simp
    · simp
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range
      (fun k ↦ if (σ.symm i : ℕ) ≤ k then sorted σ x k - sorted σ x (k + 1) else 0) (r + 1),
    sum_range_ite_sub, ite_eq_left (by omega), sorted_last, sub_zero, sorted_val]
  simp

theorem coord_nonneg {σ : Equiv.Perm (Fin (r + 1))} {x : Fin (r + 1) → ℝ} (hx : x ∈ simplex r)
    (hσ : Antitone (x ∘ σ)) (k : Fin (r + 1)) : 0 ≤ coord σ x k := by
  refine mul_nonneg (by positivity) (sub_nonneg.2 ?_)
  rw [sorted_val]
  unfold sorted
  split_ifs with h
  · exact hσ (Fin.le_iff_val_le_val.2 (by simp))
  · exact hx.1 _

/-- For `x` in the piece of `σ`, the coordinates `coord σ x` are in the simplex. -/
theorem coord_mem {σ : Equiv.Perm (Fin (r + 1))} {x : Fin (r + 1) → ℝ} (hx : x ∈ simplex r)
    (hσ : Antitone (x ∘ σ)) : coord σ x ∈ simplex r := by
  refine ⟨coord_nonneg hx hσ, ?_⟩
  simp only [coord]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ ((k : ℝ) + 1) * (sorted σ x k - sorted σ x (k + 1)))
      (r + 1), sum_range_mul_sub, sorted_last, mul_zero, sub_zero,
    ← Fin.sum_univ_eq_sum_range (sorted σ x)]
  simp only [sorted_val]
  rw [Equiv.sum_comp σ x]
  exact hx.2

theorem vertex_mem_simplex (σ : Equiv.Perm (Fin (r + 1))) (k : Fin (r + 1)) :
    vertex σ k ∈ simplex r := by
  refine ⟨fun i ↦ by unfold vertex; split_ifs <;> positivity, ?_⟩
  unfold vertex
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun j : Fin (r + 1) ↦ (j : ℕ) ≤ k).card = (k : ℕ) + 1 := by
    have : (Finset.univ.filter fun j : Fin (r + 1) ↦ (j : ℕ) ≤ k) = Finset.Iic k := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Fin.le_def]
    rw [this, Fin.card_Iic]
  rw [hcard]
  push_cast
  field_simp

theorem vmap_mem (σ : Equiv.Perm (Fin (r + 1))) {u : Fin (r + 1) → ℝ} (hu : u ∈ simplex r) :
    vmap σ u ∈ simplex r := by
  rw [vmap_apply]
  exact (convex_simplex r).sum_mem (fun k _ ↦ hu.1 k) hu.2 fun k _ ↦ vertex_mem_simplex σ k

/-- Two orderings of `x` give the same sorted values. -/
theorem sorted_eq {σ τ : Equiv.Perm (Fin (r + 1))} {x : Fin (r + 1) → ℝ}
    (hσ : Antitone (x ∘ σ)) (hτ : Antitone (x ∘ τ)) : sorted σ x = sorted τ x := by
  have h := Tuple.unique_antitone hσ hτ
  funext j
  unfold sorted
  split_ifs
  · exact congrFun h _
  · rfl

/-- Two orderings of `x` give the same coordinates. -/
theorem coord_eq {σ τ : Equiv.Perm (Fin (r + 1))} {x : Fin (r + 1) → ℝ}
    (hσ : Antitone (x ∘ σ)) (hτ : Antitone (x ∘ τ)) : coord σ x = coord τ x := by
  unfold coord
  rw [sorted_eq hσ hτ]

/-- For an ordering `σ` of `x` with `x (σ k) > x (σ (k + 1))`, the first `k + 1` indices of `σ`
are those where `x` is at least `x (σ k)`. -/
theorem symm_le_iff {σ : Equiv.Perm (Fin (r + 1))} {x : Fin (r + 1) → ℝ} (hσ : Antitone (x ∘ σ))
    {k : Fin (r + 1)} (hgap : sorted σ x k ≠ sorted σ x (k + 1)) (i : Fin (r + 1)) :
    (σ.symm i : ℕ) ≤ k ↔ sorted σ x k ≤ x i := by
  rw [sorted_val]
  constructor
  · intro hle
    simpa using hσ (show σ.symm i ≤ k from Fin.le_iff_val_le_val.2 hle)
  · intro hge
    by_contra hlt
    push Not at hlt
    have hk1 : (k : ℕ) + 1 < r + 1 := by have := (σ.symm i).isLt; omega
    have h1 : x i ≤ x (σ ⟨k + 1, hk1⟩) := by
      simpa using hσ (show (⟨k + 1, hk1⟩ : Fin (r + 1)) ≤ σ.symm i from
        Fin.le_iff_val_le_val.2 (by simp; omega))
    have h2 : x (σ ⟨k + 1, hk1⟩) ≤ x (σ k) :=
      hσ (show k ≤ (⟨k + 1, hk1⟩ : Fin (r + 1)) from Fin.le_iff_val_le_val.2 (by simp))
    apply hgap
    rw [sorted_val, show sorted σ x ((k : ℕ) + 1) = x (σ ⟨k + 1, hk1⟩) by simp [sorted, hk1]]
    exact le_antisymm (hge.trans h1) h2 |>.symm ▸ rfl

/-- Two orderings of `x` have the same `k`-th vertex wherever the `k`-th coordinate of `x` does
not vanish. -/
theorem vertex_eq {σ τ : Equiv.Perm (Fin (r + 1))} {x : Fin (r + 1) → ℝ}
    (hσ : Antitone (x ∘ σ)) (hτ : Antitone (x ∘ τ)) {k : Fin (r + 1)} (hk : coord σ x k ≠ 0) :
    vertex σ k = vertex τ k := by
  have hgap : sorted σ x k ≠ sorted σ x (k + 1) := fun h ↦ hk (by simp [coord, h])
  have hgap' : sorted τ x k ≠ sorted τ x (k + 1) := by rwa [← sorted_eq hσ hτ]
  funext i
  unfold vertex
  have hiff : ((σ.symm i : ℕ) ≤ k) ↔ ((τ.symm i : ℕ) ≤ k) := by
    rw [symm_le_iff hσ hgap, symm_le_iff hτ hgap', sorted_eq hσ hτ]
  by_cases h : (σ.symm i : ℕ) ≤ k
  · rw [ite_eq_left h, ite_eq_left (hiff.1 h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.2 h)]

/-- The piece of the first barycentric subdivision where `σ` orders `x` decreasingly. -/
def piece (σ : Equiv.Perm (Fin (r + 1))) : Set (Fin (r + 1) → ℝ) :=
  {x | x ∈ simplex r ∧ Antitone (x ∘ σ)}

theorem mem_piece {σ : Equiv.Perm (Fin (r + 1))} {x : Fin (r + 1) → ℝ} :
    x ∈ piece σ ↔ x ∈ simplex r ∧ Antitone (x ∘ σ) :=
  Iff.rfl

theorem isClosed_piece (σ : Equiv.Perm (Fin (r + 1))) : IsClosed (piece σ) := by
  have : piece σ = simplex r ∩
      ⋂ a, ⋂ b, ⋂ (_ : a ≤ b), {x : Fin (r + 1) → ℝ | x (σ b) ≤ x (σ a)} := by
    ext x
    simp [piece, Antitone]
  rw [this]
  exact (isClosed_simplex r).inter (isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
    isClosed_iInter fun _ ↦ isClosed_le (continuous_apply _) (continuous_apply _))

theorem iUnion_piece : ⋃ σ, piece σ = simplex r :=
  subset_antisymm (iUnion_subset fun _ _ hx ↦ hx.1) fun x hx ↦
    mem_iUnion.2 ⟨Tuple.sortDesc x, hx, Tuple.antitone_sortDesc x⟩

/-! ### Iterated subdivisions -/

/-- The barycentric coordinates of `x` in a piece of the `n`-th barycentric subdivision that
contains it. -/
noncomputable def coords : ℕ → (Fin (r + 1) → ℝ) → Fin (r + 1) → ℝ
  | 0, x => x
  | n + 1, x => coords n (coord (Tuple.sortDesc x) x)

/-- The vertices of a piece of the `n`-th barycentric subdivision that contains `x`. -/
noncomputable def verts : ℕ → (Fin (r + 1) → ℝ) → Fin (r + 1) → Fin (r + 1) → ℝ
  | 0, _ => fun k ↦ Pi.single k 1
  | n + 1, x => fun k ↦ vmap (Tuple.sortDesc x) (verts n (coord (Tuple.sortDesc x) x) k)

theorem coords_mem : ∀ n {x : Fin (r + 1) → ℝ}, x ∈ simplex r → coords n x ∈ simplex r
  | 0, _, hx => hx
  | n + 1, x, hx => coords_mem n (coord_mem hx (Tuple.antitone_sortDesc x))

theorem verts_mem : ∀ n {x : Fin (r + 1) → ℝ}, x ∈ simplex r → ∀ k, verts n x k ∈ simplex r
  | 0, _, _, k => single_mem_simplex k
  | n + 1, x, hx, k => vmap_mem _ (verts_mem n (coord_mem hx (Tuple.antitone_sortDesc x)) k)

/-- `x` is the combination of the vertices `verts n x` with the coefficients `coords n x`. -/
theorem sum_coords_smul_verts : ∀ n {x : Fin (r + 1) → ℝ}, x ∈ simplex r →
    ∑ k, coords n x k • verts n x k = x
  | 0, x, _ => by
    ext i
    simp [coords, verts, Finset.sum_apply, Pi.single_apply]
  | n + 1, x, hx => by
    simp only [coords, verts]
    rw [show ∀ (c : Fin (r + 1) → ℝ) (v : Fin (r + 1) → Fin (r + 1) → ℝ),
        ∑ k, c k • vmap (Tuple.sortDesc x) (v k) = vmap (Tuple.sortDesc x) (∑ k, c k • v k) by
          intro c v
          simp [map_sum, map_smul],
      sum_coords_smul_verts n (coord_mem hx (Tuple.antitone_sortDesc x)), vmap_coord]

/-- If `x = ∑ k, c k • w k` with `c ≥ 0` and `w k ≥ 0`, a vertex `w k` with `c k ≠ 0` vanishes
wherever `x` vanishes. -/
theorem eq_zero_of_sum_smul {ι : Type*} [Fintype ι] {c : ι → ℝ} {w : ι → Fin (r + 1) → ℝ}
    {x : Fin (r + 1) → ℝ} (hc : ∀ k, 0 ≤ c k) (hw : ∀ k i, 0 ≤ w k i)
    (hsum : ∑ k, c k • w k = x) {k : ι} (hk : c k ≠ 0) {i : Fin (r + 1)} (hi : x i = 0) :
    w k i = 0 := by
  have h : ∑ j, c j * w j i = 0 := by
    rw [← hi, ← hsum]
    simp [Finset.sum_apply]
  have hle : c k * w k i ≤ 0 := h ▸ Finset.single_le_sum (f := fun j ↦ c j * w j i)
    (fun j _ ↦ mul_nonneg (hc j) (hw j i)) (Finset.mem_univ k)
  exact (mul_eq_zero.1 (le_antisymm hle (mul_nonneg (hc k) (hw k i)))).resolve_left hk

/-! ### Piecewise-linear interpolation -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The map that is linear on each piece of the `n`-th barycentric subdivision and takes the value
`g v` at each vertex `v`. -/
noncomputable def interp (n : ℕ) (g : (Fin (r + 1) → ℝ) → E) (x : Fin (r + 1) → ℝ) : E :=
  ∑ k, coords n x k • g (verts n x k)

/-- On the piece of `σ`, the interpolation on the `(n + 1)`-th subdivision is the interpolation of
`g ∘ vmap σ` on the `n`-th, at the coordinates of `x` in the piece. -/
theorem interp_succ (n : ℕ) (g : (Fin (r + 1) → ℝ) → E) {x : Fin (r + 1) → ℝ}
    (hx : x ∈ simplex r) {σ : Equiv.Perm (Fin (r + 1))} (hσ : Antitone (x ∘ σ)) :
    interp (n + 1) g x = interp n (g ∘ vmap σ) (coord σ x) := by
  have hτ : Antitone (x ∘ Tuple.sortDesc x) := Tuple.antitone_sortDesc x
  have hu : coord (Tuple.sortDesc x) x = coord σ x := coord_eq hτ hσ
  have hcσ : coord σ x ∈ simplex r := coord_mem hx hσ
  simp only [interp, coords, verts, Function.comp_apply]
  rw [hu]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : coords n (coord σ x) k = 0
  · simp [hk]
  congr 2
  rw [vmap_apply, vmap_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hv : verts n (coord σ x) k j = 0
  · simp [hv]
  rw [vertex_eq hτ hσ (k := j) ?_]
  rw [hu]
  intro hj
  exact hv (eq_zero_of_sum_smul (fun k ↦ (coords_mem n hcσ).1 k)
    (fun k i ↦ (verts_mem n hcσ k).1 i) (sum_coords_smul_verts n hcσ) hk hj)

theorem continuous_sorted (σ : Equiv.Perm (Fin (r + 1))) (j : ℕ) :
    Continuous fun x : Fin (r + 1) → ℝ ↦ sorted σ x j := by
  unfold sorted
  by_cases h : j < r + 1
  · simp only [dite_eq_left h]
    exact continuous_apply _
  · simp only [dite_eq_right h]
    exact continuous_const

theorem continuous_coord (σ : Equiv.Perm (Fin (r + 1))) :
    Continuous (coord σ : (Fin (r + 1) → ℝ) → Fin (r + 1) → ℝ) :=
  continuous_pi fun k ↦ continuous_const.mul
    ((continuous_sorted σ k).sub (continuous_sorted σ (k + 1)))

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The interpolation on the `n`-th barycentric subdivision is continuous on the simplex, for any
values `g` at the vertices. -/
theorem continuousOn_interp : ∀ (n : ℕ) (g : (Fin (r + 1) → ℝ) → E),
    ContinuousOn (interp n g) (simplex r)
  | 0, g => by
    have : interp 0 g = fun x ↦ ∑ k, x k • g (Pi.single k 1) := by
      funext x
      simp [interp, coords, verts]
    rw [this]
    exact (continuous_finsetSum _ fun k _ ↦ (continuous_apply k).smul continuous_const).continuousOn
  | n + 1, g => by
    rw [← iUnion_piece]
    refine LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite _) isClosed_piece
      fun σ ↦ ?_
    exact ((continuousOn_interp n (g ∘ vmap σ)).comp (s := piece σ)
      (continuous_coord σ).continuousOn fun _ hx ↦ coord_mem (mem_piece.1 hx).1
        (mem_piece.1 hx).2).congr fun _ hx ↦ interp_succ n g (mem_piece.1 hx).1 (mem_piece.1 hx).2

/-! ### The mesh -/

/-- The `ℓ¹` norm. -/
def l1 (v : Fin (r + 1) → ℝ) : ℝ := ∑ i, |v i|

theorem l1_nonneg (v : Fin (r + 1) → ℝ) : 0 ≤ l1 v :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem dist_le_l1 (v w : Fin (r + 1) → ℝ) : dist v w ≤ l1 (v - w) := by
  refine (dist_pi_le_iff (l1_nonneg _)).2 fun i ↦ ?_
  rw [Real.dist_eq]
  exact Finset.single_le_sum (f := fun j ↦ |(v - w) j|) (fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ i)

/-- `vmap σ` contracts the `ℓ¹` norm of vectors of sum `0` by `r / (r + 1)`. -/
theorem l1_vmap_le (σ : Equiv.Perm (Fin (r + 1))) {d : Fin (r + 1) → ℝ} (hd : ∑ i, d i = 0) :
    l1 (vmap σ d) ≤ r / (r + 1) * l1 d := by
  set c : ℝ := ((r : ℝ) + 1)⁻¹ with hc
  let w : Fin (r + 1) → Fin (r + 1) → ℝ := fun k ↦ vertex σ k - Pi.single (σ 0) c
  have hw : vmap σ d = ∑ k, d k • w k := by
    simp only [w, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hd, zero_smul, sub_zero,
      vmap_apply]
  have hw0 : ∀ k i, 0 ≤ w k i := by
    intro k i
    simp only [w, Pi.sub_apply, vertex, Pi.single_apply]
    by_cases hi : i = σ 0
    · subst hi
      have hk : ((k : ℕ) : ℝ) + 1 ≤ (r : ℝ) + 1 := by
        have := k.isLt
        exact_mod_cast (show (k : ℕ) + 1 ≤ r + 1 by omega)
      simp only [Equiv.symm_apply_apply, Fin.val_zero, zero_le, ite_true]
      exact sub_nonneg.2 (inv_anti₀ (by positivity) hk)
    · simp only [hi, ite_false, sub_zero]
      split_ifs <;> positivity
  have hw1 : ∀ k, l1 (w k) = r / (r + 1) := by
    intro k
    simp only [l1, abs_of_nonneg (hw0 k _)]
    simp only [w, Pi.sub_apply, Finset.sum_sub_distrib, (vertex_mem_simplex σ k).2]
    simp [hc]
    field_simp
    ring
  calc l1 (vmap σ d) = ∑ i, |∑ k, d k * w k i| := by
        rw [hw]
        simp [l1, Finset.sum_apply]
    _ ≤ ∑ i, ∑ k, |d k| * w k i := Finset.sum_le_sum fun i _ ↦
        (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ ↦ by
          rw [abs_mul, abs_of_nonneg (hw0 k i)]))
    _ = ∑ k, |d k| * l1 (w k) := by
        rw [Finset.sum_comm]
        simp [l1, Finset.mul_sum, abs_of_nonneg (hw0 _ _)]
    _ = r / (r + 1) * l1 d := by
        rw [Finset.sum_congr rfl fun k _ ↦ congrArg (|d k| * ·) (hw1 k), ← Finset.sum_mul,
          mul_comm]
        rfl

/-- The vertices of the piece of the `n`-th subdivision that contains `x` are within
`2 (r / (r + 1)) ^ n` of `x` in the `ℓ¹` norm. -/
theorem l1_verts_sub_le : ∀ n {x : Fin (r + 1) → ℝ}, x ∈ simplex r → ∀ k,
    l1 (verts n x k - x) ≤ 2 * ((r : ℝ) / (r + 1)) ^ n
  | 0, x, hx, k => by
    simp only [verts, pow_zero, mul_one]
    calc l1 (Pi.single k 1 - x) ≤ l1 (Pi.single k 1) + l1 x := by
          simp only [l1, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ ↦ abs_sub _ _
      _ = 2 := by
          have h1 : l1 (Pi.single k 1 : Fin (r + 1) → ℝ) = 1 := by
            simp [l1, Pi.single_apply, apply_ite]
          have h2 : l1 x = 1 := by simp [l1, abs_of_nonneg (hx.1 _), hx.2]
          rw [h1, h2]
          norm_num
  | n + 1, x, hx, k => by
    have hσ := Tuple.antitone_sortDesc x
    have hu := coord_mem hx hσ
    have hv := verts_mem n hu k
    have heq : verts (n + 1) x k - x = vmap (Tuple.sortDesc x)
        (verts n (coord (Tuple.sortDesc x) x) k - coord (Tuple.sortDesc x) x) := by
      simp only [verts, map_sub, vmap_coord]
    have hd : ∑ i, (verts n (coord (Tuple.sortDesc x) x) k - coord (Tuple.sortDesc x) x) i = 0 :=
      by simp [Finset.sum_sub_distrib, hv.2, hu.2]
    rw [heq]
    calc _ ≤ r / (r + 1) * l1 (verts n (coord (Tuple.sortDesc x) x) k -
          coord (Tuple.sortDesc x) x) := l1_vmap_le _ hd
      _ ≤ r / (r + 1) * (2 * ((r : ℝ) / (r + 1)) ^ n) :=
          mul_le_mul_of_nonneg_left (l1_verts_sub_le n hu k) (by positivity)
      _ = 2 * ((r : ℝ) / (r + 1)) ^ (n + 1) := by ring

/-- The vertices of the piece of the `n`-th subdivision that contains `x` are within
`2 (r / (r + 1)) ^ n` of `x`. -/
theorem dist_verts_le (n : ℕ) {x : Fin (r + 1) → ℝ} (hx : x ∈ simplex r) (k : Fin (r + 1)) :
    dist (verts n x k) x ≤ 2 * ((r : ℝ) / (r + 1)) ^ n :=
  (dist_le_l1 _ _).trans (l1_verts_sub_le n hx k)

end BarycentricSubdivision
