import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyCycles
import Holant.Proofs.Hardness.GeneralEOPairedCSPRaw
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Records

/-! Ordinary mixed CSP records retain every original label, including nullary
occurrences. Variable declarations are unary, and occurrence addresses and
labels are binary. No covering or incidence certificate is carried by input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot.StackProgram.GraphLabelEncoding
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

structure Raw (s : ℕ) where
  «variables» : ℕ
  labels : List (Fin s)
  addresses : List ℕ
  deriving DecidableEq, Repr

abbrev unary := UnaryBinary.unaryEncoding
abbrev labelEncoding (s : ℕ) := SignatureLabel.binaryFinEncoding s
abbrev labelsEncoding (s : ℕ) := framedListEncoding (labelEncoding s)
abbrev addressesEncoding := framedListEncoding encodingNatBool
abbrev fieldsEncoding (s : ℕ) := pairEncoding unary (pairEncoding (labelsEncoding s) addressesEncoding)

def Raw.fields {s : ℕ} (r : Raw s) : ℕ×(List (Fin s)×List ℕ) := (r.variables,r.labels,r.addresses)
def ofFields {s : ℕ} (a : ℕ×(List (Fin s)×List ℕ)) : Raw s := ⟨a.1,a.2.1,a.2.2⟩

def encoding (s : ℕ) : Encoding (Raw s) Bool where
  encode r := (fieldsEncoding s).encode r.fields
  decode bits := ofFields <$> (fieldsEncoding s).decode bits
  decode_encode r := by rw [(fieldsEncoding s).decode_encode]; rfl

variable {s : ℕ} {arity : ℕ→ℕ} (P : (i : Fin s)→OrientedPerfectPairing (arity i.val))

def Raw.edgeCount (r : Raw s) : ℕ := (r.labels.map (fun i=>(P i).count)).sum
def Raw.offset (r : Raw s) (v : ℕ) : ℕ := ((r.labels.map (fun i=>(P i).count)).take v).sum
def Raw.WellFormed (r : Raw s) : Prop :=
  r.addresses.length=r.edgeCount P ∧ ∀v∈r.addresses,v<r.variables
instance rawWellFormedDecidable (r : Raw s) : Decidable (r.WellFormed P) := by
  unfold Raw.WellFormed
  infer_instance
abbrev Input := {r : Raw s // r.WellFormed P}

def inputEncoding : Encoding (Input P) Bool where
  encode r := (encoding s).encode r.val
  decode bits := ((encoding s).decode bits).bind fun r=>
    if h : r.WellFormed P then some ⟨r,h⟩ else none
  decode_encode r := by simp [r.property]

theorem malformed_rejected (r : Raw s) (hr : ¬r.WellFormed P) :
    (inputEncoding P).decode ((encoding s).encode r)=none := by simp [inputEncoding,hr]

def fieldsComputes : Computes (encoding s) (fieldsEncoding s) Raw.fields :=
  recode (identityComputes (fieldsEncoding s)) Raw.fields (fun _=>rfl) (fun _=>rfl)
def variablesComputes : Computes (encoding s) unary Raw.variables :=
  fieldsComputes.andThen (Wiring.firstComputes unary (pairEncoding (labelsEncoding s) addressesEncoding))
def tailComputes : Computes (encoding s) (pairEncoding (labelsEncoding s) addressesEncoding)
    (fun r=>(r.labels,r.addresses)) :=
  fieldsComputes.andThen (Wiring.secondComputes unary (pairEncoding (labelsEncoding s) addressesEncoding))
def labelsComputes : Computes (encoding s) (labelsEncoding s) Raw.labels :=
  tailComputes.andThen (Wiring.firstComputes (labelsEncoding s) addressesEncoding)
def addressesComputes : Computes (encoding s) addressesEncoding Raw.addresses :=
  tailComputes.andThen (Wiring.secondComputes (labelsEncoding s) addressesEncoding)

def Raw.labelsFn (r : Raw s) : Fin r.labels.length→Fin s := r.labels.get

theorem count_eq (r : Raw s) : GeneralEOPairedCSPFamilyCycles.count P r.labelsFn=r.edgeCount P := by
  rw [GeneralEOPairedCSPFamilyCycles.count,Raw.edgeCount,←List.sum_ofFn]
  congr 1
  change List.ofFn ((fun i=>(P i).count) ∘ r.labelsFn)=_
  rw [←List.map_ofFn]
  simp [Raw.labelsFn]

def scope (r : Raw s) (hr : r.WellFormed P) :
    GeneralEOPairedCSPFamilyCycles.Slot P r.labelsFn→Fin r.variables := fun t=>
  ⟨r.addresses.getD t.val 0,by
    have hi : t.val<r.addresses.length := by rw [hr.1,←count_eq P]; exact t.isLt
    apply hr.2
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _⟩

@[simp] theorem scope_val (r : Raw s) (hr : r.WellFormed P)
    (t : GeneralEOPairedCSPFamilyCycles.Slot P r.labelsFn) :
    (scope P r hr t).val=r.addresses.getD t.val 0 := rfl

theorem addresses_scope (r : Raw s) (hr : r.WellFormed P) :
    GeneralEOPairedCSPScan.NatScan.addresses (scope P r hr)=r.addresses := by
  apply List.ext_getElem
  · simpa [GeneralEOPairedCSPScan.NatScan.addresses,count_eq] using hr.1.symm
  · intro i hi hj
    simp only [GeneralEOPairedCSPScan.NatScan.addresses,List.getElem_ofFn,scope_val]
    exact List.getD_eq_getElem _ _ hj

def value {K : Type*} [CommSemiring K] (g : (i : Fin s)→Signature K (P i).count) (r : Raw s) : K :=
  ∑x : Fin r.variables→Bool,∏v : Fin r.labels.length,
    g (r.labelsFn v) (fun j=>GeneralEOPairedCSPRaw.read x
      (r.addresses.getD (r.offset P v.val+j.val) 0))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyRaw
