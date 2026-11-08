module

public meta import Lean.Elab.Command
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.lpSpace
-- One `import all` line per module of the library, so that proofs are visible to the axiom
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find FixedPoint -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all FixedPoint.Brouwer.Ball
import all FixedPoint.Brouwer.Convex
import all FixedPoint.Brouwer.DetPolynomial
import all FixedPoint.Brouwer.KKM
import all FixedPoint.Brouwer.Polytope
import all FixedPoint.Brouwer.SmoothFixedPoint
import all FixedPoint.Brouwer.SmoothRetraction
import all FixedPoint.Common.ContinuousMap
import all FixedPoint.Common.EnclosingSimplex
import all FixedPoint.Common.Euclidean
import all FixedPoint.Common.NearestPoint
import all FixedPoint.Common.SchauderProjection
import all FixedPoint.Common.Sperner
import all FixedPoint.Common.Subdivision
import all FixedPoint.Kakutani.Convex
import all FixedPoint.Kakutani.Limit
import all FixedPoint.Kakutani.Selection
import all FixedPoint.Kakutani.Simplex
import all FixedPoint.Schauder.CompactImage
import all FixedPoint.Schauder.Convex
import all FixedPoint.Schauder.Limit
import all FixedPoint.Schauder.Projection
-- The Challenge's theorems, as `FixedPointSolution.lean` restates and proves them.
import all FixedPointSolution

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Prints the axioms on which the main theorems depend (`#print axioms`), then checks that they, the
theorems of `FixedPointChallenge.lean` as `FixedPointSolution.lean` proves them, and every
declaration of the library, including private and auxiliary ones, depend only on Lean's standard
axioms `propext`, `Classical.choice` and `Quot.sound`. A `sorry` would show up as the axiom
`sorryAx`. The run fails otherwise.

Finally, it checks that the main theorems apply in the forms used downstream.
-/

open Lean Elab Command

namespace Audit

/-- The main theorems of the library, and the Challenge's theorems as the Solution proves them. -/
meta def mainResults : List Name :=
  [``Brouwer.no_retraction,
   ``Brouwer.exists_fixedPoint_closedBall,
   ``Brouwer.exists_fixedPoint,
   ``Brouwer.exists_fixedPoint_continuousMap,
   ``Brouwer.exists_fixedPoint_convexHull_of_finite,
   ``Brouwer.KKM.exists_fixedPoint,
   ``Brouwer.KKM.exists_mem_iInter,
   ``Sperner.count_eq_one,
   ``Brouwer.no_contDiffAt_retraction,
   ``Brouwer.exists_fixedPoint_of_contDiffAt,
   ``Kakutani.exists_fixedPoint,
   ``Kakutani.exists_fixedPoint_of_innerProductSpace,
   ``Kakutani.exists_fixedPoint_simplex,
   ``Kakutani.exists_fixedPoint_convexHull,
   ``Kakutani.exists_fixedPoint_stdSimplex,
   ``Kakutani.Selection.exists_fixedPoint,
   ``Schauder.exists_fixedPoint,
   ``Schauder.exists_fixedPoint_continuousMap,
   ``Schauder.exists_fixedPoint_of_isCompact_closure_image,
   ``Schauder.Projection.exists_fixedPoint,
   ``FixedPointChallenge.brouwer,
   ``FixedPointChallenge.brouwer_closedBall,
   ``FixedPointChallenge.no_retraction,
   ``FixedPointChallenge.kakutani,
   ``FixedPointChallenge.schauder,
   ``FixedPointChallenge.schauder_of_isCompact_closure_image]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`FixedPoint).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      out := out ++ d.constNames
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut rows : Array String := #[]
  for n in mainResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    rows := rows.push s!"{n}: {axs.toList}"
  let library := libraryConstants env
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#print axioms Brouwer.no_retraction
#print axioms Brouwer.exists_fixedPoint_closedBall
#print axioms Brouwer.exists_fixedPoint
#print axioms Brouwer.exists_fixedPoint_continuousMap
#print axioms Kakutani.exists_fixedPoint
#print axioms Schauder.exists_fixedPoint
#print axioms Schauder.exists_fixedPoint_of_isCompact_closure_image

#audit

/-! ## Independence of the proofs -/

/-- Walks through the declarations that `root` uses, directly or through others. Returns whether
it reaches `target`, and the declarations of the library it meets without a proof: those would be
seen as axioms, if a module of the library lacked its `import all` line, and hide what they use. -/
meta def reaches (env : Environment) (target root : Name) : Bool × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut found := false
  let mut hidden : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if n == target then found := true
    if let some ci := env.find? n then
      if ci matches .axiomInfo _ then
        if let some idx := env.getModuleIdxFor? n then
          if Audit.isLibraryModule env.header.moduleNames[idx.toNat]! then hidden := hidden.push n
      for m in ci.getUsedConstantsAsSet do
        unless seen.contains m do stack := stack.push m
  return (found, hidden)

/-- Resolves the two names and walks from the first, failing on library declarations without a
proof. -/
meta def reachesCmd (a b : Ident) : CommandElabM (Name × Name × Bool) := do
  let na ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let nb ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
  let (found, hidden) := reaches (← getEnv) nb na
  unless hidden.isEmpty do
    throwError m!"declarations of the library without a proof (missing `import all`?): {hidden}"
  return (na, nb, found)

/-- `#independent a of b` checks that the declaration `a` does not use `b`. -/
elab "#independent " a:ident " of " b:ident : command => do
  let (na, nb, found) ← reachesCmd a b
  if found then throwError m!"{na} uses {nb}"
  logInfo m!"{na} does not use {nb}"

/-- `#uses a of b` checks that the declaration `a` uses `b`: a control for `#independent`. -/
elab "#uses " a:ident " of " b:ident : command => do
  let (na, nb, found) ← reachesCmd a b
  unless found do throwError m!"{na} does not use {nb}"
  logInfo m!"{na} uses {nb}"

-- Controls: the analytic proof, and the second proofs of Kakutani's and Schauder's theorems, use
-- the analytic proof of Brouwer's theorem; the KKM proof uses Sperner's lemma.
#uses Brouwer.exists_fixedPoint of Brouwer.no_contDiffAt_retraction
#uses Kakutani.Selection.exists_fixedPoint of Brouwer.no_contDiffAt_retraction
#uses Schauder.Projection.exists_fixedPoint of Brouwer.no_contDiffAt_retraction
#uses Brouwer.KKM.exists_fixedPoint of Sperner.count_eq_one

-- The proof through the KKM lemma uses nothing of the analytic proof.
#independent Brouwer.KKM.exists_fixedPoint of Brouwer.no_contDiffAt_retraction
#independent Brouwer.KKM.exists_fixedPoint of Brouwer.exists_fixedPoint_closedBall
-- Kakutani's and Schauder's proofs use Brouwer's theorem in the proof of Knaster, Kuratowski and
-- Mazurkiewicz, which both papers cite.
#independent Kakutani.exists_fixedPoint of Brouwer.no_contDiffAt_retraction
#independent Schauder.exists_fixedPoint of Brouwer.no_contDiffAt_retraction
#independent Schauder.exists_fixedPoint_of_isCompact_closure_image
  of Brouwer.no_contDiffAt_retraction

/-! ## The statements in the forms used downstream -/

open Set Metric in
/-- The no-retraction theorem for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/
example (n : ℕ) :
    ¬ ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn r (closedBall 0 1) ∧ MapsTo r (closedBall 0 1) (sphere 0 1) ∧
        ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1, r x = x :=
  Brouwer.no_retraction

open Set Metric in
/-- Brouwer's theorem for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/
example (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1))
    (hf : ContinuousOn f (closedBall 0 1)) : ∃ x ∈ closedBall 0 1, f x = x :=
  Brouwer.exists_fixedPoint_closedBall zero_le_one hmaps hf

open Set in
/-- Brouwer's theorem for compact convex sets, in the form `∀ s, … → ∃ x ∈ s, f x = x`. -/
example (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∀ s : Set V, Convex ℝ s → IsCompact s → s.Nonempty → ∀ f : V → V, MapsTo f s s →
      ContinuousOn f s → ∃ x ∈ s, f x = x :=
  fun _ hconv hcomp hne _ hmaps hf ↦ Brouwer.exists_fixedPoint hconv hcomp hne hmaps hf

open Set in
/-- Kakutani's theorem for compact convex sets, in the form `∀ s, … → ∃ x ∈ s, x ∈ φ x`. -/
example (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∀ s : Set V, Convex ℝ s → IsCompact s → s.Nonempty → ∀ φ : V → Set V,
      (∀ x ∈ s, φ x ⊆ s) → (∀ x ∈ s, (φ x).Nonempty) → (∀ x ∈ s, Convex ℝ (φ x)) →
        IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1} → ∃ x ∈ s, x ∈ φ x :=
  fun _ hconv hcomp hne _ hmaps hφne hφconv hgraph ↦
    Kakutani.exists_fixedPoint hconv hcomp hne hmaps hφne hφconv hgraph

open Set in
/-- Schauder's theorem for compact convex sets of a real normed space, of any dimension. -/
example (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ s : Set E, Convex ℝ s → IsCompact s → s.Nonempty → ∀ f : E → E, MapsTo f s s →
      ContinuousOn f s → ∃ x ∈ s, f x = x :=
  fun _ hconv hcomp hne _ hmaps hf ↦ Schauder.exists_fixedPoint hconv hcomp hne hmaps hf

open Set in
/-- Schauder's theorem for closed convex sets of the Hilbert space `ℓ²(ℕ)` and maps with relatively
compact image. -/
example (s : Set (lp (fun _ : ℕ ↦ ℝ) 2)) (hconv : Convex ℝ s) (hcl : IsClosed s)
    (hne : s.Nonempty) (f : lp (fun _ : ℕ ↦ ℝ) 2 → lp (fun _ : ℕ ↦ ℝ) 2) (hmaps : MapsTo f s s)
    (hf : ContinuousOn f s) (himg : IsCompact (closure (f '' s))) : ∃ x ∈ s, f x = x :=
  Schauder.exists_fixedPoint_of_isCompact_closure_image hconv hcl hne hmaps hf himg
