import Holant.Proofs.Hardness.BinaryCSPProgrammeCircuitAccess

/-! Literal finite signed-NAND2 gate writers. The sixteen NAND rows and six
marked signs are emitted by actual framed-list machines; no gate evaluator is
used as a machine instruction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeCircuitBlocks
open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace U
export Holant.LocalDrafts.CountingHardness.VerifierCompiler.Stateful.CapacityFrontend.Unary (addComputes)
end U
namespace G
export BinaryThreeSupportGraph (Rows pinBlock nandBlock)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev rowsEncoding := pairEncoding edgesEncoding signsEncoding
abbrev inputEncoding := pairEncoding (pairEncoding encodingNatBool encodingNatBool) unary
abbrev Address := Bool ⊕ ℕ

def address (p : (ℕ×ℕ)×ℕ) : Address→ℕ
  | .inl false => p.1.1
  | .inl true => p.1.2
  | .inr k => p.2+k

def addressComputes (i : Address) : Computes inputEncoding encodingNatBool (fun p => address p i) := by
  cases i with
  | inl b =>
    cases b with
    | false =>
      exact (Wiring.firstComputes (pairEncoding encodingNatBool encodingNatBool) unary).andThen
        (Wiring.firstComputes encodingNatBool encodingNatBool)
    | true =>
      exact (Wiring.firstComputes (pairEncoding encodingNatBool encodingNatBool) unary).andThen
        (Wiring.secondComputes encodingNatBool encodingNatBool)
  | inr k =>
    exact ((pairComputes (Wiring.secondComputes (pairEncoding encodingNatBool encodingNatBool) unary)
      (constantComputes inputEncoding unary k)).andThen U.addComputes).andThen UnaryBinary.computes

def edgeList (es : List (Address×Address)) : Computes inputEncoding edgesEncoding
    (fun p => es.map (fun e => (address p e.1,address p e.2))) :=
  fixedListComputes inputEncoding edgeEncoding (fun p e => (address p e.1,address p e.2))
    (fun e => pairComputes (addressComputes e.1) (addressComputes e.2)) es

def signList (ss : List Address) : Computes inputEncoding signsEncoding
    (fun p => ss.map (address p)) :=
  fixedListComputes inputEncoding encodingNatBool address addressComputes ss

def nandEdges : List (Address×Address) :=
  [(.inl false,.inr 1),(.inr 4,.inl false),(.inr 4,.inr 1),
   (.inl true,.inr 2),(.inr 5,.inl true),(.inr 5,.inr 2),
   (.inr 0,.inr 3),(.inr 6,.inr 0),(.inr 6,.inr 3),
   (.inr 7,.inl false),(.inr 7,.inr 0),(.inr 8,.inl true),(.inr 8,.inr 0),
   (.inr 9,.inr 1),(.inr 9,.inr 2),(.inr 9,.inr 3)]
def nandSigns : List Address := [.inr 4,.inr 5,.inr 6,.inr 7,.inr 8,.inr 9]

def nandComputes : Computes inputEncoding rowsEncoding (fun p => G.nandBlock p.1.1 p.1.2 p.2) :=
  congrComputes (pairComputes (edgeList nandEdges) (signList nandSigns))
    (fun p => by simp [nandEdges,nandSigns,address,G.nandBlock])

abbrev pinEncoding := pairEncoding encodingBoolBool unary

def pinComputes : Computes pinEncoding rowsEncoding (fun p => G.pinBlock p.1 p.2) := by
  let flag := Wiring.firstComputes encodingBoolBool unary
  let offset := Wiring.secondComputes encodingBoolBool unary
  let prepare := pairComputes (constantComputes pinEncoding (pairEncoding encodingNatBool encodingNatBool) (0,0)) offset
  let yes := prepare.andThen (pairComputes (edgeList [(.inr 1,.inr 0)]) (signList [.inr 1]))
  let no := prepare.andThen (pairComputes (edgeList [(.inr 0,.inr 0),(.inr 1,.inr 1)]) (signList []))
  exact congrComputes (ifComputes flag yes no) (fun p => by cases p.1 <;> simp [G.pinBlock,address])

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeCircuitBlocks
