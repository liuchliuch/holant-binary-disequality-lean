import Holant.Proofs.Hardness.GeneralEOPairedFamilyMinorRaw
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPrivateRaw

/-! Fixed-size private blocks for mixed CSP families. Every row retains its
literal label and heterogeneous exposed arity. The finite byte writer retains
all declared variables, including unused ones. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyPrivateRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding GeneralEOPairedCSPFamilyRaw
namespace M
export GeneralEOPairedFamilyMinorRaw
  (RowInput rowEncoding contextComputes indexComputes offsetComputes labelIndexComputes)
end M
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (lengthComputes getD flatten)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (unaryAdd)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a b : ℕ → ℕ}
variable (Q : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (b i.val))
variable (k : ℕ) (hcount : ∀i,(P i).count=(Q i).count+k)

def port (r : Raw s) (v : ℕ) {i : Fin s} : Fin ((Q i).count+k) → ℕ :=
  Fin.addCases (fun j=>r.addresses.getD (r.offset Q v+j.val) 0)
    (fun j=>r.variables+(v*k+j.val))

def rowFor (r : Raw s) (v : ℕ) (i : Fin s) : List ℕ :=
  List.ofFn (fun j=>port Q k r v (Fin.cast (hcount i) j))

def row (r : Raw s) (v : Fin r.labels.length) : List ℕ :=
  rowFor Q P k hcount r v.val (r.labels.get v)

def addresses (r : Raw s) : List ℕ := (List.finRange r.labels.length).flatMap (row Q P k hcount r)

def query (r : Raw s) : Raw s :=
  ⟨r.variables+r.labels.length*k,r.labels,addresses Q P k hcount r⟩

def countComputes : Computes (encoding s) unary (fun r : Raw s=>r.labels.length*k) :=
  (pairComputes (labelsComputes.andThen (W.lengthComputes (labelEncoding s)))
    (constantComputes (encoding s) unary k)).andThen BinaryInterpolation.WeightCompiler.multiplyUnaryComputes

def oldComputes {i : Fin s} (j : Fin (Q i).count) :
    Computes (M.rowEncoding s) encodingNatBool
      (fun x=>x.1.addresses.getD (x.1.offset Q x.2.val+j.val) 0) :=
  (pairComputes (M.contextComputes.andThen addressesComputes)
    ((pairComputes (M.offsetComputes Q) (constantComputes (M.rowEncoding s) unary j.val)).andThen A.unaryAdd)).andThen
      (W.getD encodingNatBool 0)

def freshComputes (j : Fin k) : Computes (M.rowEncoding s) encodingNatBool
    (fun x=>x.1.variables+(x.2.val*k+j.val)) := by
  let block := (pairComputes M.indexComputes (constantComputes (M.rowEncoding s) unary k)).andThen
    BinaryInterpolation.WeightCompiler.multiplyUnaryComputes
  let index := (pairComputes block (constantComputes (M.rowEncoding s) unary j.val)).andThen A.unaryAdd
  exact ((pairComputes (M.contextComputes.andThen variablesComputes) index).andThen A.unaryAdd).andThen
    UnaryBinary.computes

def portComputes {i : Fin s} (j : Fin ((Q i).count+k)) :
    Computes (M.rowEncoding s) encodingNatBool (fun x=>port Q k x.1 x.2.val j) := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) j
  · simpa only [port,Fin.addCases_left] using oldComputes Q j
  · simpa only [port,Fin.addCases_right] using freshComputes k j

def rowForComputes (i : Fin s) : Computes (M.rowEncoding s) addressesEncoding
    (fun x=>rowFor Q P k hcount x.1 x.2.val i) :=
  congrComputes (fixedListComputes (M.rowEncoding s) encodingNatBool
    (fun x j=>port Q k x.1 x.2.val (Fin.cast (hcount i) j))
    (fun j=>portComputes Q k (Fin.cast (hcount i) j)) (List.finRange (P i).count))
    (fun x=>by apply List.ext_getElem <;> simp [rowFor])

def rowComputes : Computes (M.rowEncoding s) addressesEncoding (fun x=>row Q P k hcount x.1 x.2) :=
  chooseComputes (M.rowEncoding s) addressesEncoding s (fun x=>x.1.labels.get x.2)
    (fun x i=>rowFor Q P k hcount x.1 x.2.val i) M.labelIndexComputes (rowForComputes Q P k hcount)

def addressesComputes : Computes (encoding s) addressesEncoding (addresses Q P k hcount) :=
  congrComputes ((GeneralEOSignedParityProgram.tabulate (encoding s) addressesEncoding
    (fun r=>r.labels.length) (labelsComputes.andThen (W.lengthComputes (labelEncoding s)))
    (row Q P k hcount) (rowComputes Q P k hcount)).andThen (W.flatten encodingNatBool))
    (fun _=>by simp [addresses,List.flatMap_def])

def queryComputes : Computes (encoding s) (encoding s) (query Q P k hcount) :=
  recode (pairComputes ((pairComputes variablesComputes (countComputes k)).andThen A.unaryAdd)
    (pairComputes labelsComputes (addressesComputes Q P k hcount))) id (fun _=>rfl) (fun _=>rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyPrivateRaw
