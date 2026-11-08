/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Common.Subdivision
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Sperner's lemma for iterated barycentric subdivisions

A labeling `h` of the standard simplex `Δ = BarycentricSubdivision.simplex r` by the vertices
`0, …, r` is a *Sperner labeling* if every point `v` gets a label `i` with `v i ≠ 0`.
**Sperner's lemma** (`Sperner.count_eq_one`): for every `n`, the number of simplices of the `n`-th
barycentric subdivision of `Δ` whose vertices carry all the labels is odd. In particular one of
them exists, with vertices within `2 (r / (r + 1)) ^ n` of each other in the `ℓ¹` norm
(`Sperner.exists_cell`).

## Counting

The simplices of the `n`-th subdivision are the images of `Δ` under the compositions
`vmap σ₁ ∘ ⋯ ∘ vmap σₙ` (`FixedPoint/Common/Subdivision.lean`), with vertices the images of the
vertices `e k` of `Δ`. All counts are taken mod 2 and defined by recursion on `n`:

* `count n h A`: the simplices whose vertices carry exactly the labels `A`;
* `doors n h A`: the pairs of a simplex and one of its facets, the facet opposite a vertex, whose
  vertices carry exactly the labels `A`.

## Proof

Sperner's proof, by induction on the dimension, counts the pairs of a simplex and a facet labeled
`0, …, r - 1` in two ways.

1. By simplices (`doors_eq_count`): a simplex labeled `0, …, r` has one such facet, a simplex
   labeled `0, …, r - 1` with a label repeated has two, and any other none
   (`sum_erase_image_eq`).
2. By facets (`doors_eq`): a facet inside `Δ` lies in two simplices, so it counts twice, and the
   facets on the boundary of `Δ` count once each. KKM assert this; for the barycentric
   subdivision, mod 2, it reduces to two facts about the first subdivision, proved here: the
   pieces of `σ` and `σ * swap k (k + 1)` agree on their `k`-th facet (`vmap_mul_swap`), which
   pairs the facets inside `Δ`; and the last facet of the piece of `σ` is the piece of a
   permutation `τ` of `r` letters in the face `x (σ last) = 0` of `Δ` (`vmap_pieceOf_facet`), so
   that the facets on the boundary of `Δ` form the subdivisions of its faces. Here `facet m`
   embeds the `(r - 1)`-simplex as the face `x m = 0` of `Δ`.
3. For a Sperner labeling, only the face `x r = 0` carries the labels `0, …, r - 1`, and the
   labeling restricted to it is a Sperner labeling of an `(r - 1)`-simplex, so by induction the
   count is odd.
-/

@[expose] public section

open Finset Function BarycentricSubdivision Equiv

namespace Sperner

/-! ### One simplex: its facets labeled `0, …, r - 1` -/

/-- A simplex whose vertices carry all the labels `0, …, m + 1` has one facet labeled
`0, …, m`; any other simplex has an even number of them. -/
theorem sum_erase_image_eq {m : ℕ} (c : Fin (m + 2) → Fin (m + 2)) :
    (∑ k, if (univ.erase k).image c = univ.erase (Fin.last _) then (1 : ZMod 2) else 0) =
      if univ.image c = univ then 1 else 0 := by
  classical
  set b := Fin.last (m + 1)
  -- removing a vertex whose label occurs elsewhere keeps the labels
  have herase : ∀ x y, x ≠ y → c x = c y → (univ.erase x).image c = univ.image c := by
    intro x y hxy hc
    refine subset_antisymm (image_subset_image (erase_subset _ _)) fun z hz ↦ ?_
    obtain ⟨w, -, rfl⟩ := mem_image.1 hz
    by_cases hw : w = x
    · subst hw
      exact mem_image.2 ⟨y, mem_erase.2 ⟨hxy.symm, mem_univ _⟩, hc.symm⟩
    · exact mem_image.2 ⟨w, mem_erase.2 ⟨hw, mem_univ _⟩, rfl⟩
  rw [Finset.sum_boole]
  by_cases hS : univ.image c = univ
  · rw [ite_eq_left hS]
    have hsurj : Surjective c := fun y ↦ by
      have hy : y ∈ univ.image c := by rw [hS]; exact mem_univ y
      obtain ⟨x, -, hx⟩ := mem_image.1 hy
      exact ⟨x, hx⟩
    have hinj : Injective c := Finite.injective_iff_surjective.2 hsurj
    obtain ⟨k₀, hk₀⟩ := hsurj b
    have : univ.filter (fun k ↦ (univ.erase k).image c = univ.erase b) = {k₀} := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      rw [image_erase hinj, hS, erase_inj _ (mem_univ _), ← hk₀]
      exact hinj.eq_iff
    rw [this, card_singleton, Nat.cast_one]
  · rw [ite_eq_right hS]
    by_cases hA : univ.image c = univ.erase b
    · have hcard : (univ.image c).card = m + 1 := by
        rw [hA, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
        rfl
      have hninj : ¬ Injective c := fun hinj ↦ by
        rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin] at hcard
        omega
      obtain ⟨j, j', hcc, hjj⟩ : ∃ j j', c j = c j' ∧ j ≠ j' := by
        by_contra hcon
        push Not at hcon
        exact hninj hcon
      have hinjOn : Set.InjOn c (univ.erase j : Finset _) := by
        refine Finset.card_image_iff.1 ?_
        rw [herase j j' hjj hcc, hcard, card_erase_of_mem (mem_univ _), card_univ,
          Fintype.card_fin]
        rfl
      have hfilter : univ.filter (fun k ↦ (univ.erase k).image c = univ.erase b) = {j, j'} := by
        ext k
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · intro hk
          have hck : c k ∈ (univ.erase k).image c := by
            rw [hk, ← hA]
            exact mem_image_of_mem c (mem_univ k)
          obtain ⟨i, hi, hik⟩ := mem_image.1 hck
          have hik' : i ≠ k := ne_of_mem_erase hi
          by_contra hkjj
          push Not at hkjj
          by_cases hij : i = j
          · subst hij
            exact hkjj.2 (hinjOn (by simp [hkjj.1]) (by simp [hjj.symm]) (hik.symm.trans hcc))
          · exact hik' (hinjOn (by simp [hij]) (by simp [hkjj.1]) hik)
        · rintro (rfl | rfl)
          · rw [herase k j' hjj hcc, hA]
          · rw [herase k j hjj.symm hcc.symm, hA]
      rw [hfilter, card_pair hjj]
      rfl
    · have : univ.filter (fun k ↦ (univ.erase k).image c = univ.erase b) = ∅ := by
        refine filter_eq_empty_iff.2 fun k _ hk ↦ hA ?_
        have hsub : univ.erase b ⊆ univ.image c := hk ▸ image_subset_image (erase_subset _ _)
        have hb : b ∉ univ.image c := fun hb ↦ hS (eq_univ_of_forall fun y ↦ by
          by_cases hy : y = b
          · exact hy ▸ hb
          · exact hsub (mem_erase.2 ⟨hy, mem_univ _⟩))
        exact subset_antisymm (fun y hy ↦ mem_erase.2 ⟨fun h ↦ hb (by rw [← h]; exact hy),
          mem_univ _⟩) hsub
      rw [this, card_empty, Nat.cast_zero]

/-! ### The counts -/

variable {r : ℕ} {L : Type*} [DecidableEq L]

/-- The number mod 2 of simplices of the `n`-th barycentric subdivision whose vertices carry
exactly the labels `A`: a sum over the sequences `σ₁, …, σₙ` of permutations, which index the
simplices `vmap σ₁ ∘ ⋯ ∘ vmap σₙ` of the subdivision, distinct sequences giving distinct
simplices. -/
noncomputable def count : ℕ → ((Fin (r + 1) → ℝ) → L) → Finset L → ZMod 2
  | 0, h, A => if univ.image (fun k ↦ h (Pi.single k 1)) = A then 1 else 0
  | n + 1, h, A => ∑ σ : Perm (Fin (r + 1)), count n (h ∘ vmap σ) A

/-- The number mod 2 of pairs of a simplex of the `n`-th barycentric subdivision and a facet of it
whose vertices carry exactly the labels `A`. -/
noncomputable def doors : ℕ → ((Fin (r + 1) → ℝ) → L) → Finset L → ZMod 2
  | 0, h, A => ∑ k, if (univ.erase k).image (fun j ↦ h (Pi.single j 1)) = A then 1 else 0
  | n + 1, h, A => ∑ σ : Perm (Fin (r + 1)), doors n (h ∘ vmap σ) A

/-- The count depends only on the labels of the points of the simplex. -/
theorem count_congr : ∀ (n : ℕ) {h h' : (Fin (r + 1) → ℝ) → L},
    (∀ v ∈ simplex r, h v = h' v) → ∀ A, count n h A = count n h' A
  | 0, h, h', hh, A => by
    simp only [count, hh _ (single_mem_simplex _)]
  | n + 1, h, h', hh, A => Finset.sum_congr rfl fun σ _ ↦
    count_congr n (fun v hv ↦ hh _ (vmap_mem σ hv)) A

/-- No simplex is labeled `A` if a label of `A` is missing from the simplex. -/
theorem count_eq_zero : ∀ (n : ℕ) {h : (Fin (r + 1) → ℝ) → L} {A : Finset L} {a : L},
    a ∈ A → (∀ v ∈ simplex r, h v ≠ a) → count n h A = 0
  | 0, h, A, a, ha, hh => by
    simp only [count]
    refine ite_eq_right fun hA ↦ ?_
    obtain ⟨k, -, hk⟩ := mem_image.1 (hA ▸ ha : a ∈ univ.image fun k ↦ h (Pi.single k 1))
    exact hh _ (single_mem_simplex k) hk
  | n + 1, h, A, a, ha, hh => Finset.sum_eq_zero fun σ _ ↦
    count_eq_zero n ha fun v hv ↦ hh _ (vmap_mem σ hv)

/-- Relabeling by an injective map. -/
theorem count_comp {L' : Type*} [DecidableEq L'] {g : L → L'} (hg : Injective g) :
    ∀ (n : ℕ) (h : (Fin (r + 1) → ℝ) → L) (A : Finset L),
      count n (g ∘ h) (A.image g) = count n h A
  | 0, h, A => by
    have : univ.image (fun k ↦ g (h (Pi.single k 1))) =
        (univ.image fun k ↦ h (Pi.single k 1)).image g := by rw [image_image]; rfl
    simp only [count, comp_apply, this, (image_injective hg).eq_iff]
  | n + 1, h, A => Finset.sum_congr rfl fun σ _ ↦ count_comp hg n _ A

/-! ### The faces of the simplex -/

/-- The embedding of the `r`-simplex as the face `x m = 0` of the `(r + 1)`-simplex. -/
def facet (m : Fin (r + 2)) (u : Fin (r + 1) → ℝ) : Fin (r + 2) → ℝ :=
  fun i ↦ Fin.snoc (α := fun _ ↦ ℝ) u 0 (swap m (Fin.last _) i)

theorem facet_self (m : Fin (r + 2)) (u : Fin (r + 1) → ℝ) : facet m u m = 0 := by
  simp [facet]

theorem facet_last_castSucc (u : Fin (r + 1) → ℝ) (j : Fin (r + 1)) :
    facet (Fin.last _) u (Fin.castSucc j) = u j := by
  simp [facet]

theorem facet_mem {m : Fin (r + 2)} {u : Fin (r + 1) → ℝ} (hu : u ∈ simplex r) :
    facet m u ∈ simplex (r + 1) := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · simp only [facet]
    induction swap m (Fin.last _) i using Fin.lastCases with
    | last => simp
    | cast j => simpa using hu.1 j
  · simp only [facet]
    rw [Equiv.sum_comp (swap m (Fin.last _)) (Fin.snoc (α := fun _ ↦ ℝ) u 0),
      Fin.sum_univ_castSucc]
    simp [hu.2]

theorem snoc_single (j : Fin (r + 1)) :
    Fin.snoc (α := fun _ ↦ ℝ) (Pi.single j 1 : Fin (r + 1) → ℝ) 0 =
      Pi.single (Fin.castSucc j) 1 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [(Fin.castSucc_ne_last j).symm]
  | cast i => simp [Pi.single_apply, Fin.castSucc_inj]

theorem facet_single (m : Fin (r + 2)) (j : Fin (r + 1)) :
    facet m (Pi.single j 1) = Pi.single (swap m (Fin.last _) (Fin.castSucc j)) 1 := by
  funext i
  simp only [facet, snoc_single, Pi.single_apply, swap_apply_eq_iff]

theorem image_swap_castSucc (m : Fin (r + 2)) :
    univ.image (fun j : Fin (r + 1) ↦ swap m (Fin.last _) (Fin.castSucc j)) = univ.erase m := by
  ext i
  simp only [mem_image, mem_univ, true_and, mem_erase, and_true]
  constructor
  · rintro ⟨j, rfl⟩ h
    rw [swap_apply_eq_iff, swap_apply_left] at h
    exact Fin.castSucc_ne_last j h
  · intro hi
    have hne : swap m (Fin.last _) i ≠ Fin.last _ := by
      rw [Ne, swap_apply_eq_iff, swap_apply_right]
      exact hi
    obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.2 hne
    exact ⟨j, by rw [hj, swap_apply_self]⟩

/-! ### The first subdivision near the faces -/

/-- The pieces of `σ` and `σ * swap k (k + 1)` agree on their `k`-th facet. -/
theorem vmap_mul_swap (σ : Perm (Fin (r + 2))) (k : Fin (r + 1)) {u : Fin (r + 2) → ℝ}
    (hu : u (Fin.castSucc k) = 0) :
    vmap (σ * swap (Fin.castSucc k) k.succ) u = vmap σ u := by
  rw [vmap_apply, vmap_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j = Fin.castSucc k
  · simp [hj, hu]
  congr 1
  funext i
  have hjk : (j : ℕ) ≠ k := fun h ↦ hj (Fin.ext (by rw [h]; rfl))
  have key : (((swap (Fin.castSucc k) k.succ) (σ.symm i) : Fin (r + 2)) : ℕ) ≤ (j : ℕ) ↔
      ((σ.symm i : Fin (r + 2)) : ℕ) ≤ (j : ℕ) := by
    by_cases ht : σ.symm i = Fin.castSucc k
    · rw [ht, swap_apply_left]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    by_cases ht' : σ.symm i = k.succ
    · rw [ht', swap_apply_right]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    · rw [swap_apply_of_ne_of_ne ht ht']
  simp only [vertex, Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap, key]

/-- The permutation of `r + 2` letters that sends `m` to `last` and is `τ` on the others. -/
def pieceOf (m : Fin (r + 2)) (τ : Perm (Fin (r + 1))) : Perm (Fin (r + 2)) :=
  swap m (Fin.last _) * (finSuccEquiv' (Fin.last _)).symm.permCongr τ.optionCongr

theorem permCongr_castSucc (τ : Perm (Fin (r + 1))) (j : Fin (r + 1)) :
    (finSuccEquiv' (Fin.last _)).symm.permCongr τ.optionCongr (Fin.castSucc j) =
      Fin.castSucc (τ j) := by
  simp [Equiv.permCongr_apply, finSuccEquiv'_last_apply_castSucc, finSuccEquiv'_symm_some,
    Fin.succAbove_last]

theorem permCongr_last (τ : Perm (Fin (r + 1))) :
    (finSuccEquiv' (Fin.last _)).symm.permCongr τ.optionCongr (Fin.last _) = Fin.last _ := by
  simp [Equiv.permCongr_apply]

theorem pieceOf_last (m : Fin (r + 2)) (τ : Perm (Fin (r + 1))) :
    pieceOf m τ (Fin.last _) = m := by
  rw [pieceOf, Perm.mul_apply, permCongr_last, swap_apply_right]

theorem bijective_pieceOf :
    Bijective fun p : Fin (r + 2) × Perm (Fin (r + 1)) ↦ pieceOf p.1 p.2 := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · rintro ⟨m, τ⟩ ⟨m', τ'⟩ h
    have hm : m = m' := by
      simpa [pieceOf_last] using congrArg (fun σ : Perm (Fin (r + 2)) ↦ σ (Fin.last _)) h
    subst hm
    simp only [pieceOf, mul_right_inj] at h
    refine Prod.ext rfl (Equiv.ext fun j ↦ ?_)
    have := congrArg (fun σ : Perm (Fin (r + 2)) ↦ σ (Fin.castSucc j)) h
    rw [permCongr_castSucc, permCongr_castSucc] at this
    exact Fin.castSucc_injective _ this
  · simp [Fintype.card_perm, Nat.factorial_succ]

/-- Permuting the letters permutes the coordinates of the piece. -/
theorem vmap_mul_apply (π σ : Perm (Fin (r + 1))) (u : Fin (r + 1) → ℝ) (i : Fin (r + 1)) :
    vmap (π * σ) u i = vmap σ u (π.symm i) := by
  simp [vmap_apply, Finset.sum_apply, vertex, Perm.mul_def]

/-- The last facet of the piece of `pieceOf m τ` is the piece of `τ` in the face `x m = 0`. -/
theorem vmap_pieceOf_facet (m : Fin (r + 2)) (τ : Perm (Fin (r + 1))) (u : Fin (r + 1) → ℝ) :
    vmap (pieceOf m τ) (facet (Fin.last _) u) = facet m (vmap τ u) := by
  funext i
  rw [pieceOf, vmap_mul_apply, Equiv.symm_swap]
  simp only [facet]
  induction swap m (Fin.last _) i using Fin.lastCases with
  | last =>
    have hl : ((finSuccEquiv' (Fin.last _)).symm.permCongr τ.optionCongr).symm (Fin.last _) =
        Fin.last _ := by rw [Equiv.symm_apply_eq, permCongr_last]
    rw [Fin.snoc_last, vmap_apply, Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, vertex, hl, Fin.val_last]
    by_cases hk : k = Fin.last _
    · subst hk
      simp [facet_self]
    · rw [ite_eq_right (by have := Fin.val_lt_last hk; omega), mul_zero]
  | cast j =>
    rw [Fin.snoc_castSucc, vmap_apply, vmap_apply, Finset.sum_apply, Finset.sum_apply,
      Fin.sum_univ_castSucc]
    simp only [Pi.smul_apply, smul_eq_mul, facet_last_castSucc, facet_self, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1
    simp only [vertex]
    have : ((finSuccEquiv' (Fin.last _)).symm.permCongr τ.optionCongr).symm (Fin.castSucc j) =
        Fin.castSucc (τ.symm j) := by
      rw [Equiv.symm_apply_eq, permCongr_castSucc, Equiv.apply_symm_apply]
    rw [this]
    rfl

/-! ### Counting the doors -/

private theorem add_self_eq_zero (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

/-- **Counting the doors by facets**: the facets labeled `A` are counted by the faces of the
simplex. -/
theorem doors_eq : ∀ (n : ℕ) (h : (Fin (r + 2) → ℝ) → L) (A : Finset L),
    doors n h A = ∑ m, count n (h ∘ facet m) A
  | 0, h, A => by
    simp only [doors, count, comp_apply, facet_single]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [← image_swap_castSucc m, image_image]
    rfl
  | n + 1, h, A => by
    simp only [doors]
    simp_rw [doors_eq n]
    rw [Finset.sum_comm, Fin.sum_univ_castSucc]
    -- the facets inside the simplex count twice
    have hinner : ∀ k : Fin (r + 1),
        ∑ σ : Perm (Fin (r + 2)), count n ((h ∘ vmap σ) ∘ facet (Fin.castSucc k)) A = 0 := by
      intro k
      refine Finset.sum_involution (fun σ _ ↦ σ * swap (Fin.castSucc k) k.succ)
        (fun σ _ ↦ ?_) (fun σ _ _ hσ ↦ ?_) (fun _ _ ↦ mem_univ _)
        (fun σ _ ↦ by rw [mul_assoc, swap_mul_self, mul_one])
      · have : (h ∘ vmap (σ * swap (Fin.castSucc k) k.succ)) ∘ facet (Fin.castSucc k) =
            (h ∘ vmap σ) ∘ facet (Fin.castSucc k) := by
          funext u
          simp only [comp_apply]
          rw [vmap_mul_swap σ k (facet_self _ u)]
        rw [this, add_self_eq_zero]
      · have : swap (Fin.castSucc k) k.succ = 1 := mul_left_cancel (hσ.trans (mul_one σ).symm)
        have h1 := congrArg (fun π : Perm (Fin (r + 2)) ↦ π (Fin.castSucc k)) this
        simp only [swap_apply_left, Perm.one_apply] at h1
        exact absurd h1.symm Fin.castSucc_lt_succ.ne
    simp only [hinner, Finset.sum_const_zero, zero_add]
    -- the facets on the boundary are the subdivisions of the faces
    rw [← (bijective_pieceOf (r := r)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun τ _ ↦ ?_
    congr 1
    funext u
    simp only [comp_apply, vmap_pieceOf_facet]

/-- **Counting the doors by simplices**: for labels in `0, …, r + 1`, the facets labeled
`0, …, r` are as many, mod 2, as the simplices labeled `0, …, r + 1`. -/
theorem doors_eq_count : ∀ (n : ℕ) (h : (Fin (r + 2) → ℝ) → Fin (r + 2)),
    doors n h (univ.erase (Fin.last _)) = count n h univ
  | 0, _ => sum_erase_image_eq _
  | n + 1, _ => Finset.sum_congr rfl fun _ _ ↦ doors_eq_count n _

/-! ### Sperner's lemma -/

/-- In dimension `0`, the only simplex is the point `1`, which carries the only label. -/
theorem count_fin_one : ∀ (n : ℕ) (h : (Fin 1 → ℝ) → Fin 1), count n h univ = 1
  | 0, h => by
    simp only [count]
    exact ite_eq_left (eq_univ_of_forall fun i ↦ mem_image.2 ⟨0, mem_univ _, Subsingleton.elim _ _⟩)
  | n + 1, h => by
    simp only [count, count_fin_one n, Finset.sum_const, card_univ, Fintype.card_perm,
      Fintype.card_fin]
    rfl

/-- **Sperner's lemma** for the `n`-th barycentric subdivision of the standard simplex: for a
labeling `h` that gives each point `v` a label `i` with `v i ≠ 0`, the simplices labeled
`0, …, r` are odd in number. -/
theorem count_eq_one : ∀ (r n : ℕ) (h : (Fin (r + 1) → ℝ) → Fin (r + 1)),
    (∀ v ∈ simplex r, v (h v) ≠ 0) → count n h univ = 1
  | 0, n, h, _ => count_fin_one n h
  | r + 1, n, h, hh => by
    rw [← doors_eq_count, doors_eq, Fin.sum_univ_castSucc]
    -- the faces `x i = 0`, `i ≤ r`, have no simplex labeled `0, …, r`
    have hzero : ∀ k : Fin (r + 1),
        count n (h ∘ facet (Fin.castSucc k)) (univ.erase (Fin.last _)) = 0 := fun k ↦
      count_eq_zero n (a := Fin.castSucc k) (mem_erase.2 ⟨Fin.castSucc_ne_last k, mem_univ _⟩)
        fun u hu hk ↦ hh _ (facet_mem hu) (by rw [comp_apply] at hk; rw [hk, facet_self])
    simp only [hzero, Finset.sum_const_zero, zero_add]
    -- on the face `x (r + 1) = 0`, the labeling is a Sperner labeling of the `r`-simplex
    have hlast : ∀ u ∈ simplex r, h (facet (Fin.last _) u) ≠ Fin.last _ := fun u hu hk ↦
      hh _ (facet_mem hu) (by rw [hk, facet_self])
    let h' : (Fin (r + 1) → ℝ) → Fin (r + 1) := fun u ↦
      if hu : h (facet (Fin.last _) u) ≠ Fin.last _ then (h (facet (Fin.last _) u)).castPred hu
      else 0
    have hh' : ∀ u ∈ simplex r, Fin.castSucc (h' u) = h (facet (Fin.last _) u) := fun u hu ↦ by
      simp [h', hlast u hu]
    have hsperner : ∀ u ∈ simplex r, u (h' u) ≠ 0 := fun u hu ↦ by
      have := hh (facet (Fin.last _) u) (facet_mem hu)
      rwa [← hh' u hu, facet_last_castSucc] at this
    rw [count_congr n (h := h ∘ facet (Fin.last _)) (h' := Fin.castSucc ∘ h')
        (fun u hu ↦ (hh' u hu).symm),
      show univ.erase (Fin.last (r + 1)) = univ.image Fin.castSucc by
        ext i; induction i using Fin.lastCases <;> simp [Fin.castSucc_ne_last],
      count_comp (Fin.castSucc_injective _)]
    exact count_eq_one r n h' hsperner

/-- A simplex of the `n`-th subdivision whose vertices carry the labels `A`, if the count is not
zero: its vertices `w k` are in the simplex, carry the labels `A`, and are within
`2 (r / (r + 1)) ^ n` of each other in the `ℓ¹` norm. -/
theorem exists_cell : ∀ (n : ℕ) {h : (Fin (r + 1) → ℝ) → L} {A : Finset L},
    count n h A ≠ 0 → ∃ w : Fin (r + 1) → Fin (r + 1) → ℝ, (∀ k, w k ∈ simplex r) ∧
      univ.image (h ∘ w) = A ∧ ∀ j k, l1 (w j - w k) ≤ 2 * ((r : ℝ) / (r + 1)) ^ n
  | 0, h, A, hc => by
    refine ⟨fun k ↦ Pi.single k 1, single_mem_simplex, ?_, fun j k ↦ ?_⟩
    · by_contra hA
      exact hc (by simp only [count]; exact ite_eq_right hA)
    · have hj := single_mem_simplex (r := r) j
      have hk := single_mem_simplex (r := r) k
      calc l1 (Pi.single j 1 - Pi.single k 1 : Fin (r + 1) → ℝ)
          ≤ l1 (Pi.single j 1 : Fin (r + 1) → ℝ) + l1 (Pi.single k 1 : Fin (r + 1) → ℝ) := by
            simp only [l1, ← Finset.sum_add_distrib]
            exact Finset.sum_le_sum fun i _ ↦ abs_sub _ _
        _ = 2 := by
            simp only [l1, abs_of_nonneg (hj.1 _), abs_of_nonneg (hk.1 _), hj.2, hk.2]
            norm_num
        _ = 2 * ((r : ℝ) / (r + 1)) ^ 0 := by simp
  | n + 1, h, A, hc => by
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    obtain ⟨w, hw, himg, hdist⟩ := exists_cell n hσ
    refine ⟨fun k ↦ vmap σ (w k), fun k ↦ vmap_mem σ (hw k), himg, fun j k ↦ ?_⟩
    have hd : ∑ i, (w j - w k) i = 0 := by simp [Finset.sum_sub_distrib, (hw j).2, (hw k).2]
    calc l1 (vmap σ (w j) - vmap σ (w k)) = l1 (vmap σ (w j - w k)) := by rw [map_sub]
      _ ≤ r / (r + 1) * l1 (w j - w k) := l1_vmap_le σ hd
      _ ≤ r / (r + 1) * (2 * ((r : ℝ) / (r + 1)) ^ n) :=
          mul_le_mul_of_nonneg_left (hdist j k) (by positivity)
      _ = 2 * ((r : ℝ) / (r + 1)) ^ (n + 1) := by ring

end Sperner
