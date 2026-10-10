import Holant.Proofs.LinearProgramming.Parsing.FramePrefix
import Holant.Proofs.LinearProgramming.Parsing.Infrastructure.OptionContextInterface
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.OptionMapInterface
import Holant.Proofs.LinearProgramming.Support.OptionalValue

/-! Physical pair-parser composition. Component premises are actual finite
Computes objects on ALL raw words, not correctness callbacks or presumed
successful parses. Parsing.Source.parseComputes installs the concrete
scalar/list/unary component programs internally; callers supply only bytes.

The pair constructor calls FramePrefix's real good/bad program and the two
installed component machines, then uses existing optional-context/map/copy
programs. None propagation is physical. No parser is a whole-word opcode.
-/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Pair
open Holant Turing Computability Holant.Algebraic
open Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient
open Holant.LocalDrafts.RemoteWork.RationalLP.Support
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
open Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Infrastructure
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
noncomputable section
variable {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)

def combine (p : Option A × Option B) : Option (A × B) :=
  p.1.bind (fun a => p.2.map (fun b => (a,b)))

/-- Existing optional-context programs propagate either actual component
failure. The only fallback is the absent Option, never a dummy A/B value. -/
def combineComputes :
    Computes (pairEncoding (optionEncoding ea) (optionEncoding eb))
      (optionEncoding (pairEncoding ea eb)) combine := by
  let inner := ((Wiring.swapComputes (optionEncoding ea) eb).andThen
    (OptionContext.computes eb ea)).andThen (OptionMap.computes (Wiring.swapComputes eb ea))
  let full := ((OptionContext.computes (optionEncoding ea) eb).andThen
    (OptionMap.computes inner)).andThen
      (OptionalValue.getDComputes (optionEncoding (pairEncoding ea eb)) none)
  exact congrComputes full (fun p => by
    rcases p with ⟨a,b⟩
    cases a <;> cases b <;> rfl)

/-- Composable installed pair decoder using precisely the old pairEncoding.
wa/wb are machine objects with actual arbitrary-word output contracts.
They are constructor parameters, not assumptions of Parsing.Source.parseComputes. -/
def computes
    (wa : Computes Frame.wordEncoding (optionEncoding ea) ea.decode)
    (wb : Computes Frame.wordEncoding (optionEncoding eb) eb.decode) :
    Computes Frame.wordEncoding (optionEncoding (pairEncoding ea eb))
      (pairEncoding ea eb).decode := by
  let left := (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding).andThen wa
  let right := (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding).andThen wb
  let components := (pairComputes left right).andThen (combineComputes ea eb)
  let full := (FramePrefix.computes.andThen (OptionMap.computes components)).andThen
    (OptionalValue.getDComputes (optionEncoding (pairEncoding ea eb)) none)
  exact congrComputes full (fun input => by
    change ((unframe input).map (fun p => combine (ea.decode p.1,eb.decode p.2))).getD none=
      (unframe input).bind (fun p => (ea.decode p.1).bind
        (fun a => (eb.decode p.2).bind (fun b => some (a,b))))
    cases hu : unframe input with
    | none => rfl
    | some p =>
      cases ha : ea.decode p.1 <;> cases hb : eb.decode p.2 <;>
        simp [combine,ha,hb])

/-- Every composition copy, component parse, Option branch and output frame
is charged by the existing Computes closure polynomial. -/
theorem primitive_bound
    (wa : Computes Frame.wordEncoding (optionEncoding ea) ea.decode)
    (wb : Computes Frame.wordEncoding (optionEncoding eb) eb.decode) (input : List Bool) :
    let w := computes ea eb wa wb
    primitiveCost w.machine (w.outputs input).steps (some (initList w.machine.computer input))≤
      (primitivePolynomial w).eval input.length :=
  computes_primitive_cost (computes ea eb wa wb) input

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Pair
