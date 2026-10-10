import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentCodeCompiler
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProductBounds
import Holant.Complexity.GraphPreprocessing.ComponentSelection.RawRoots

/-! Actual raw-network compilation through its physically enumerated original
component roots. Every root invokes the selective component compiler exactly
once; emitted code entries are joined by the real product controller. The final
GraphCode naming theorem is separated from this operational assembly. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphListCompiler
open Turing Computability BinaryCompose FixedFieldMachines ComponentSelection
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := {r : RawClosedNetwork // r.WellFormed s b arity}
def roots (x : Input s b arity) : List (Fin x.val.vertices.length) := (x.val.graph x.property).roots
def entries (x : Input s b arity) := (roots x).map (fun v => ComponentCodeCompiler.value ⟨x,v⟩)
def value (x : Input s b arity) := CodeProduct.product (entries x)

def emitted {A : Type} (e : Encoding A Bool) (code : Code A) := true::Holant.Algebraic.frame (CodeProduct.entry e code)
noncomputable def emitComputes {A : Type} (e : Encoding A Bool) :
    Computes (codeEncoding e) Frame.wordEncoding (emitted e) :=
  recode (((ActionChildLinear.frameComputes.andThen (OrdinaryCoefficient.prefixComputes [false,true])).andThen
    ActionChildLinear.frameComputes).andThen (OrdinaryCoefficient.prefixComputes [true]))
    (codeEncoding e).encode (fun _ => rfl) (fun _ => rfl)
abbrev frameMachine := pairMachine identityMachine (Constant.machine [])
abbrev emitMachine := ((frameMachine.compose (OrdinaryCoefficient.prefixMachine [false,true])).compose frameMachine).compose
  (OrdinaryCoefficient.prefixMachine [true])
@[simp] theorem emit_machine {A : Type} (e : Encoding A Bool) : (emitComputes e).machine=emitMachine := rfl

def chunkValue (x : RawRootReach.Input s b arity) := emitted (treeLabelEncoding s b arity) (ComponentCodeCompiler.value x)
noncomputable def chunkComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding chunkValue :=
  (ComponentCodeCompiler.computes s b arity).andThen (emitComputes (treeLabelEncoding s b arity))
def indices (x : Input s b arity) := OccurrenceLabel.unaryPortEncoding x.val.vertices.length
def listEncoding (s b : ℕ) (arity : ℕ → ℕ) :=
  ContextFlatMap.inputEncoding (RawClosedNetwork.validatedEncoding s b arity) indices
def listValue (x : Σr : Input s b arity,List (Fin r.val.vertices.length)) :=
  x.2.flatMap (fun v => chunkValue ⟨x.1,v⟩)
noncomputable def listComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (listEncoding s b arity) Frame.wordEncoding listValue :=
  ContextFlatMap.computes (RawClosedNetwork.validatedEncoding s b arity) indices chunkValue (chunkComputes s b arity)
def selected (x : Input s b arity) : Σr : Input s b arity,List (Fin r.val.vertices.length) := ⟨x,roots x⟩
noncomputable def selectedComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (listEncoding s b arity) selected :=
  recode (pairComputes (identityComputes (RawClosedNetwork.validatedEncoding s b arity)) (RawRoots.computes s b arity)) id
    (fun _ => rfl) (fun x => by
      change Holant.Algebraic.frame _++framedListEncode UnaryBinary.unaryEncoding ((roots x).map Fin.val)=_
      rw [ActionChildList.index_encoding]
      rfl)
noncomputable def chunksComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) Frame.wordEncoding (fun x => listValue (selected x)) :=
  (selectedComputes s b arity).andThen (listComputes s b arity)
theorem chunks_word {A B : Type} (e : Encoding A Bool) (f : B → Code A) (xs : List B) :
    xs.flatMap (fun b => emitted e (f b))++[false]=(CodeProduct.inputEncoding e).encode (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [List.flatMap_cons,List.map_cons,List.append_assoc,List.cons_append,emitted,
      CodeProduct.inputEncoding,framedListEncoding,framedListEncode,CodeProduct.entryEncoding] using
      congrArg (fun tail => emitted e (f a)++tail) ih
noncomputable def entriesComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (CodeProduct.inputEncoding (treeLabelEncoding s b arity)) entries :=
  recode ((pairComputes (chunksComputes s b arity)
    (constantComputes (RawClosedNetwork.validatedEncoding s b arity) Frame.wordEncoding [false])).andThen WordJoin.computes)
    id (fun _ => rfl) (fun x => chunks_word (treeLabelEncoding s b arity) (fun v => ComponentCodeCompiler.value ⟨x,v⟩) (roots x))
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) value :=
  (entriesComputes s b arity).andThen (CodeProduct.computes (treeLabelEncoding s b arity))
abbrev chunkMachine (s b : ℕ) (arity : ℕ → ℕ) := (ComponentCodeCompiler.machine s b arity).compose emitMachine
abbrev chunksMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine identityMachine RawRoots.machine).compose (ContextFlatMap.machine (chunkMachine s b arity))
abbrev entriesMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine (chunksMachine s b arity) (Constant.machine [false])).compose WordJoin.machine
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) := (entriesMachine s b arity).compose (CodeProduct.driver (treeLabelEncoding s b arity))
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) value := (computes s b arity).inFP
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (computes s b arity).time*Polynomial.C (machine s b arity).primitiveBudget
theorem primitive_bound (x : Input s b arity) :
    primitiveCost (machine s b arity) ((computes s b arity).outputs x).steps
      (some (initList (machine s b arity).computer (RawClosedNetwork.encoding.encode x.val)))≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val).length := by
  have h := Nat.mul_le_mul_right (machine s b arity).primitiveBudget ((computes s b arity).outputs x).steps_le_m
  change _≤((computes s b arity).time.eval (RawClosedNetwork.encoding.encode x.val).length)*(machine s b arity).primitiveBudget at h
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphListCompiler
