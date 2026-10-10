import Holant.Proofs.Hardness.GeneralEOSignedParityProgram
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPinNative

/-! Literal mixed-family minor expansion. Every source row keeps its label and
writes its fixed list of parent ports, using only the two reserved constants
and source variable addresses. Labels, repetitions and nullary rows are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyMinorRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open GeneralEOPairedCSPFamilyRaw
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (mapComputes flatten lengthComputes getD)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (unaryAdd)
end A
namespace Pr
export GeneralEOPairedCSPFamilyProgramme (offsetComputes labelRecodeComputes)
end Pr
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {a b : ℕ → ℕ}
variable (Q : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (b i.val))
variable (ports : (i : Fin s) → Fin (P i).count → Bool ⊕ Fin (Q i).count)

abbrev RowInput (s : ℕ) := Σ r : Raw s, Fin r.labels.length
abbrev rowEncoding (s : ℕ) := sigmaEncoding (encoding s)
  (fun r => OccurrenceLabel.unaryPortEncoding r.labels.length)

def port (r : Raw s) (v : ℕ) {i : Fin s} : Bool ⊕ Fin (Q i).count → ℕ
  | .inl z => if z then 1 else 0
  | .inr j => r.addresses.getD (r.offset Q v+j.val) 0+2

def row (r : Raw s) (v : Fin r.labels.length) : List ℕ :=
  List.ofFn (fun j => port Q r v.val (ports (r.labels.get v) j))

def addresses (r : Raw s) : List ℕ := (List.finRange r.labels.length).flatMap (row Q P ports r)
def query (r : Raw s) : Raw s := ⟨r.variables,r.labels,addresses Q P ports r⟩

def contextComputes : Computes (rowEncoding s) (encoding s) (fun x => x.1) :=
  recode (Wiring.firstComputes (encoding s) unary) (fun x => (x.1,x.2.val))
    (fun _ => rfl) (fun _ => rfl)
def indexComputes : Computes (rowEncoding s) unary (fun x => x.2.val) :=
  recode (Wiring.secondComputes (encoding s) unary) (fun x => (x.1,x.2.val))
    (fun _ => rfl) (fun _ => rfl)
def offsetComputes : Computes (rowEncoding s) unary (fun x => x.1.offset Q x.2.val) :=
  recode (Pr.offsetComputes Q) (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def labelComputes : Computes (rowEncoding s) (labelEncoding s) (fun x => x.1.labels.get x.2) := by
  let prep : Computes (rowEncoding s) (OriginalCoefficient.ParentRowSelect.inputEncoding (labelEncoding s))
      (fun x => ⟨x.1.labels,x.2⟩) :=
    recode (pairComputes (contextComputes.andThen labelsComputes) indexComputes)
      id (fun _ => rfl) (fun _ => rfl)
  exact prep.andThen (OriginalCoefficient.ParentRowSelect.computes (labelEncoding s))

def labelIndexComputes : Computes (rowEncoding s) unary (fun x => (x.1.labels.get x.2).val) :=
  labelComputes.andThen (Pr.labelRecodeComputes unary Fin.val)

def portComputes {i : Fin s} (q : Bool ⊕ Fin (Q i).count) :
    Computes (rowEncoding s) encodingNatBool (fun x => port Q x.1 x.2.val q) := by
  cases q with
  | inl z => exact constantComputes (rowEncoding s) encodingNatBool (if z then 1 else 0)
  | inr j =>
    let slot := (pairComputes (offsetComputes Q) (constantComputes (rowEncoding s) unary j.val)).andThen A.unaryAdd
    let address := (pairComputes (contextComputes.andThen addressesComputes) slot).andThen (W.getD encodingNatBool 0)
    exact (pairComputes address (constantComputes (rowEncoding s) encodingNatBool 2)).andThen FixedGadgetSubstitution.Compiler.addComputes

def rowForComputes (i : Fin s) : Computes (rowEncoding s) addressesEncoding
    (fun x => List.ofFn (fun j => port Q x.1 x.2.val (ports i j))) :=
  congrComputes (fixedListComputes (rowEncoding s) encodingNatBool
    (fun x j => port Q x.1 x.2.val (ports i j))
    (fun j => portComputes Q (ports i j)) (List.finRange (P i).count))
    (fun x => by apply List.ext_getElem <;> simp)

def rowComputes : Computes (rowEncoding s) addressesEncoding (fun x => row Q P ports x.1 x.2) :=
  chooseComputes (rowEncoding s) addressesEncoding s (fun x => x.1.labels.get x.2)
    (fun x i => List.ofFn (fun j => port Q x.1 x.2.val (ports i j))) labelIndexComputes
    (rowForComputes Q P ports)

def addressesComputes : Computes (encoding s) addressesEncoding (addresses Q P ports) :=
  congrComputes ((GeneralEOSignedParityProgram.tabulate (encoding s) addressesEncoding
    (fun r => r.labels.length) (labelsComputes.andThen (W.lengthComputes (labelEncoding s)))
    (row Q P ports) (rowComputes Q P ports)).andThen (W.flatten encodingNatBool))
    (fun _ => by simp [addresses,List.flatMap_def])

def queryComputes : Computes (encoding s) (encoding s) (query Q P ports) :=
  recode (pairComputes variablesComputes (pairComputes labelsComputes (addressesComputes Q P ports)))
    id (fun _ => rfl) (fun _ => rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyMinorRaw
