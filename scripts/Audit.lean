module

public meta import Lean.Elab.Command
public import Mathlib.Analysis.InnerProductSpace.PiL2
-- One `import all` line per module of the library, so that proofs are visible to the axiom
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find FixedPoint -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all FixedPoint.Brouwer
import all FixedPoint.Brouwer.Ball
import all FixedPoint.Brouwer.Convex
import all FixedPoint.Brouwer.DetPolynomial
import all FixedPoint.Brouwer.NearestPoint
import all FixedPoint.Brouwer.SmoothFixedPoint
import all FixedPoint.Brouwer.SmoothRetraction
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
   ``Brouwer.no_contDiffAt_retraction,
   ``Brouwer.exists_fixedPoint_of_contDiffAt,
   ``BrouwerChallenge.exists_fixedPoint,
   ``BrouwerChallenge.exists_fixedPoint_closedBall,
   ``BrouwerChallenge.no_retraction]

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

#audit

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
