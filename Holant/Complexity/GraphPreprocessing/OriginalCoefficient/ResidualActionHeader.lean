import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalBounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeaderBounds

/-! Conditioned traversal headers from original raw/cut/vertex data. The actual
canonical parent flag controls whether the b label is emitted; a and b are
produced by the genuine two-pin coefficient machinery. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionHeader
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
def flag (x : ResidualContext.Query s b arity) := (RawParentRow.value (ResidualContext.original x)).parent.isSome
noncomputable def flagComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) encodingBoolBool flag :=
  ((ResidualContext.originalComputes s b arity).andThen (RawParentRow.computes s b arity)).andThen ActionHeader.presenceComputes
def data (a z : Bool) (x : ResidualContext.Query s b arity) : ActionHeader.Data s b arity :=
  (flag x,(ResidualOriginalCoefficient.zeroValue a z x,ResidualOriginalCoefficient.parentValue a z x))
noncomputable def dataComputes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) (ActionHeader.dataEncoding s b arity) (data a z) :=
  pairComputes (flagComputes s b arity) (pairComputes (ResidualOriginalCoefficient.zeroComputes a z s b arity)
    (ResidualOriginalCoefficient.parentComputes a z s b arity))
def value (a z : Bool) (x : ResidualContext.Query s b arity) := ActionHeader.emit s b arity (data a z x)
noncomputable def computes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) Frame.wordEncoding (value a z) :=
  (dataComputes a z s b arity).andThen (ActionHeader.emitComputes s b arity)
abbrev flagMachine := (ResidualContext.originalMachine.compose RawParentRow.machine).compose ActionHeader.presenceMachine
abbrev dataMachine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) := pairMachine flagMachine
  (pairMachine (ResidualOriginalCoefficient.zeroMachine a z s b arity) (ResidualOriginalCoefficient.parentMachine a z s b arity))
abbrev machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) := (dataMachine a z s b arity).compose (ActionHeader.emitMachine s b arity)
@[simp] theorem computes_machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : (computes a z s b arity).machine=machine a z s b arity := rfl
theorem inFP (a z : Bool) : InFP (ResidualContext.queryEncoding s b arity) Frame.wordEncoding (value a z) := (computes a z s b arity).inFP
theorem root_header (a z : Bool) (x : ResidualContext.Query s b arity)
    (hp : (RawParentRow.value (ResidualContext.original x)).parent=none) :
    value a z x=Traversal.literals (Holant.Algebraic.frame ((treeLabelEncoding s b arity).encode (ResidualOriginalCoefficient.zeroValue a z x))) := by
  simp only [value,ActionHeader.emit,data,flag,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte,List.append_nil]
theorem child_header (a z : Bool) (x : ResidualContext.Query s b arity) (q : ℕ × Bool)
    (hp : (RawParentRow.value (ResidualContext.original x)).parent=some q) :
    value a z x=Traversal.literals (Holant.Algebraic.frame ((treeLabelEncoding s b arity).encode (ResidualOriginalCoefficient.zeroValue a z x))++
      Holant.Algebraic.frame ((treeLabelEncoding s b arity).encode (ResidualOriginalCoefficient.parentValue a z x))) := by
  simp only [value,ActionHeader.emit,data,flag,hp,Option.isSome_some,↓reduceIte]
theorem output_length (a z : Bool) (x : ResidualContext.Query s b arity) :
    (value a z x).length≤8*lengthBound s b arity+4 := ActionHeader.emit_length _
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionHeader
