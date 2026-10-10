import Holant.Complexity.BinaryInterpolation.Chains.Compiler.LocalRows
import Holant.Complexity.BinaryCompose.Arithmetic

/-! Actual original-row parsing and dynamic fresh-edge offsets. The weight of
an earlier marked occurrence is computed from its original label; multiplying
that count by the input chain length uses the checked binary machine.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution RawClosedNetwork
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable (s b : ℕ) (arity : ℕ → ℕ)
abbrev Input := ℕ × FixedGadgetSubstitution.Compiler.Input s b arity
abbrev inputEncoding := pairEncoding UnaryBinary.unaryEncoding (validatedEncoding s b arity)
abbrev Query := Σ x : Input s b arity, Fin x.2.val.vertices.length
def queryEncoding := sigmaEncoding (inputEncoding s b arity)
  (fun x => OccurrenceLabel.unaryPortEncoding x.2.val.vertices.length)

noncomputable def contextComputes : Computes (queryEncoding s b arity) (inputEncoding s b arity)
    (fun x => x.1) :=
  recode (Wiring.firstComputes (inputEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

noncomputable def indexComputes : Computes (queryEncoding s b arity) UnaryBinary.unaryEncoding
    (fun x => x.2.val) :=
  recode (Wiring.secondComputes (inputEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

noncomputable def lengthComputes : Computes (queryEncoding s b arity) UnaryBinary.unaryEncoding
    (fun x => x.1.1) :=
  (contextComputes s b arity).andThen
    (Wiring.firstComputes UnaryBinary.unaryEncoding (validatedEncoding s b arity))

noncomputable def sourceComputes : Computes (queryEncoding s b arity) (validatedEncoding s b arity)
    (fun x => x.1.2) :=
  (contextComputes s b arity).andThen
    (Wiring.secondComputes UnaryBinary.unaryEncoding (validatedEncoding s b arity))

def originalQuery (x : Query s b arity) : FixedGadgetSubstitution.Compiler.Query s b arity :=
  ⟨x.1.2,x.2⟩

noncomputable def originalQueryComputes : Computes (queryEncoding s b arity)
    (FixedGadgetSubstitution.Compiler.queryEncoding s b arity) (originalQuery s b arity) :=
  recode (pairComputes (sourceComputes s b arity) (indexComputes s b arity))
    id (fun _ => rfl) (fun _ => rfl)

noncomputable def originalRowComputes : Computes (queryEncoding s b arity) vertexEncoding
    (fun x => x.1.2.val.vertices.get x.2) :=
  (originalQueryComputes s b arity).andThen (FixedGadgetSubstitution.Compiler.originalRowComputes s b arity)

def before (distinguished : ℕ) (x : Query s b arity) : ℕ :=
  FixedGadgetSubstitution.Compiler.prefixWeight s b arity
    (fun i => if i = distinguished then 1 else 0) (originalQuery s b arity x)

noncomputable def beforeComputes (distinguished : ℕ) : Computes (queryEncoding s b arity)
    UnaryBinary.unaryEncoding (before s b arity distinguished) :=
  (originalQueryComputes s b arity).andThen
    (FixedGadgetSubstitution.Compiler.prefixWeightComputes s b arity
      (fun i => if i = distinguished then 1 else 0))

noncomputable def multiplyComputes : Computes Endpoints.natPairEncoding encodingNatBool
    (fun p => p.1 * p.2) :=
  Endpoints.prepareArithmeticComputes.andThen BinaryCompose.multiplicationComputes

def offset (distinguished : ℕ) (x : Query s b arity) : ℕ :=
  x.1.2.val.edges.length + x.1.1 * before s b arity distinguished x

noncomputable def offsetComputes (distinguished : ℕ) : Computes (queryEncoding s b arity)
    encodingNatBool (offset s b arity distinguished) :=
  (pairComputes
    (((sourceComputes s b arity).andThen
      (FixedGadgetSubstitution.Compiler.edgeCountComputes s b arity)).andThen UnaryBinary.computes)
    ((pairComputes ((lengthComputes s b arity).andThen UnaryBinary.computes)
      ((beforeComputes s b arity distinguished).andThen UnaryBinary.computes)).andThen multiplyComputes)).andThen
        FixedGadgetSubstitution.Compiler.addComputes

def placement (distinguished : ℕ) (x : Query s b arity) : Chains.Compiler.LocalInput :=
  (x.1.1,(offset s b arity distinguished x,(x.1.2.val.vertices.get x.2).2))

noncomputable def placementComputes (distinguished : ℕ) : Computes (queryEncoding s b arity)
    Chains.Compiler.localEncoding (placement s b arity distinguished) :=
  pairComputes (lengthComputes s b arity)
    (pairComputes (offsetComputes s b arity distinguished)
      ((originalRowComputes s b arity).andThen
        (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
          id (fun _ => rfl) (fun _ => rfl))))

def marked (distinguished : ℕ) (x : Query s b arity) : Bool :=
  decide ((x.1.2.val.vertices.get x.2).1 = distinguished)

noncomputable def markedComputes (distinguished : ℕ) : Computes (queryEncoding s b arity)
    encodingBoolBool (marked s b arity distinguished) :=
  (pairComputes
    ((originalRowComputes s b arity).andThen
      (recode (Wiring.firstComputes encodingNatBool (framedListEncoding endpointEncoding))
        id (fun _ => rfl) (fun _ => rfl)))
    (constantComputes (queryEncoding s b arity) encodingNatBool distinguished)).andThen Endpoints.equalComputes

def rows (distinguished label : ℕ) (x : Query s b arity) : List RawVertex :=
  if marked s b arity distinguished x then
    placedRows label (placement s b arity distinguished x) else [x.1.2.val.vertices.get x.2]

noncomputable def rowChunkComputes (distinguished label : ℕ) : Computes (queryEncoding s b arity)
    Frame.wordEncoding (fun x => FixedGadgetSubstitution.Compiler.entries vertexEncoding
      (rows s b arity distinguished label x)) := by
  let yes := ((placementComputes s b arity distinguished).andThen
    (Chains.Compiler.rowsComputes label)).andThen (FixedGadgetSubstitution.Compiler.entriesComputes vertexEncoding)
  let no := (originalRowComputes s b arity).andThen (FixedGadgetSubstitution.Compiler.entryComputes vertexEncoding)
  refine congrComputes (ifComputes (markedComputes s b arity distinguished) yes no) ?_
  intro x
  cases h : marked s b arity distinguished x <;>
    simp [rows,h,FixedGadgetSubstitution.Compiler.entries]

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
