import Holant.Proofs.Tractability.ProductMachine.Endpoint
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Dispatch


namespace Holant.LocalDrafts.Tractability.ProductMachine.Templates

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution.Compiler

abbrev Record := ℕ × (ℕ × (ℕ × (ℕ × ℕ)))

def recordEncoding : Encoding Record Bool :=
  pairEncoding encodingNatBool (pairEncoding encodingNatBool
    (pairEncoding encodingNatBool (pairEncoding encodingNatBool encodingNatBool)))

inductive LocalFactor where
  | scalar (label : ℕ)
  | unary (port : ℕ) (falseLabel trueLabel : ℕ)
  | link (left right : ℕ) (flip : Bool)
  deriving DecidableEq

def place (ports : List RawEndpoint) : LocalFactor → Record
  | .scalar c => (0, c, 0, 0, 0)
  | .unary i c d => (1, Endpoint.number (ports.getD i (0, false)), c, d, 0)
  | .link i j p => (2, Endpoint.number (ports.getD i (0, false)),
      Endpoint.number (ports.getD j (0, false)), p.toNat, 0)

def portsEncoding := framedListEncoding RawClosedNetwork.endpointEncoding

noncomputable def addressComputes (i : ℕ) : Computes portsEncoding encodingNatBool
    (fun ports => Endpoint.number (ports.getD i (0, false))) :=
  (getDComputes RawClosedNetwork.endpointEncoding i (0, false)).andThen Endpoint.computes

noncomputable def constant (n : ℕ) := constantComputes portsEncoding encodingNatBool n

/-- The branch is on a compile-time template constructor, not on a decoded
unbounded runtime structure in the machine's finite state. -/
noncomputable def factorComputes (f : LocalFactor) :
    Computes portsEncoding recordEncoding (fun ports => place ports f) := by
  cases f with
  | scalar c => exact constantComputes portsEncoding recordEncoding (0, c, 0, 0, 0)
  | unary i c d =>
    exact pairComputes (constant 1) (pairComputes (addressComputes i)
      (pairComputes (constant c) (pairComputes (constant d) (constant 0))))
  | link i j p =>
    exact pairComputes (constant 2) (pairComputes (addressComputes i)
      (pairComputes (addressComputes j) (pairComputes (constant p.toNat) (constant 0))))

noncomputable def templateComputes (fs : List LocalFactor) :
    Computes portsEncoding (framedListEncoding recordEncoding) (fun ports => fs.map (place ports)) :=
  fixedListComputes portsEncoding recordEncoding place factorComputes fs

noncomputable def templateEntriesComputes (fs : List LocalFactor) :
    Computes portsEncoding Frame.wordEncoding (fun ports => entries recordEncoding (fs.map (place ports))) :=
  (templateComputes fs).andThen (entriesComputes recordEncoding)

variable (s b : ℕ) (arity : ℕ → ℕ) (templates : Fin s → List LocalFactor)

noncomputable def originalPortsComputes : Computes (queryEncoding s b arity) portsEncoding
    (fun x => (x.1.val.vertices.get x.2).2) :=
  (originalRowComputes s b arity).andThen
    (recode (Wiring.secondComputes encodingNatBool portsEncoding) id (fun _ => rfl) (fun _ => rfl))

def vertexEntries (x : Query s b arity) : List Bool :=
  entries recordEncoding ((templates (sourceLabel s b arity x)).map
    (place (x.1.val.vertices.get x.2).2))

/-- Finite label selection reads the original record and instantiates its fixed
local formula with its actual ordered endpoint list. -/
noncomputable def vertexComputes : Computes (queryEncoding s b arity) Frame.wordEncoding
    (vertexEntries s b arity templates) :=
  chooseComputes (queryEncoding s b arity) Frame.wordEncoding s (sourceLabel s b arity)
    (fun x i => entries recordEncoding ((templates i).map (place (x.1.val.vertices.get x.2).2)))
    (labelRecodeComputes s b arity UnaryBinary.unaryEncoding Fin.val)
    (fun i => (originalPortsComputes s b arity).andThen (templateEntriesComputes (templates i)))

def allVertexEntries (x : Input s b arity) : List Bool :=
  (List.finRange x.val.vertices.length).flatMap (fun v => vertexEntries s b arity templates ⟨x, v⟩)

/-- Actual unbounded original-row loop, including nullary and zero templates. -/
noncomputable def allVerticesComputes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    Frame.wordEncoding (allVertexEntries s b arity templates) :=
  allRowsFlatMapComputes s b arity (vertexEntries s b arity templates)
    (vertexComputes s b arity templates)

theorem allVertices_primitive_bound (x : Input s b arity) :
    let w := allVerticesComputes s b arity templates
    primitiveCost w.machine (w.outputs x).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode x.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode x.val).length :=
  computes_primitive_cost (allVerticesComputes s b arity templates) x

end Holant.LocalDrafts.Tractability.ProductMachine.Templates
