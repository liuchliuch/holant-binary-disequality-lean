import Holant.Proofs.Hardness.GeneralEOPairedCSPRecords
import Holant.Proofs.Hardness.BinaryCSPProgrammeCore

/-! Finite CSP input with unary variable/constraint declarations and binary
variable addresses. Explicit constraint count preserves nullary occurrences.
The validated decoder rejects wrong row lengths and out-of-range addresses. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

structure Raw where
  «variables» : ℕ
  constraints : ℕ
  addresses : List ℕ
  deriving DecidableEq, Repr

def Raw.WellFormed (r : Raw) (count : ℕ) : Prop :=
  r.addresses.length=r.constraints*count ∧ ∀v∈r.addresses,v<r.variables

instance rawWellFormedDecidable (r : Raw) (count : ℕ) : Decidable (r.WellFormed count) := by
  unfold Raw.WellFormed
  infer_instance

abbrev unary := UnaryBinary.unaryEncoding
abbrev addressesEncoding := framedListEncoding encodingNatBool
abbrev fieldsEncoding := pairEncoding unary (pairEncoding unary addressesEncoding)

def Raw.fields (r : Raw) : ℕ×(ℕ×List ℕ) := (r.variables,r.constraints,r.addresses)
def ofFields (a : ℕ×(ℕ×List ℕ)) : Raw := ⟨a.1,a.2.1,a.2.2⟩

def encoding : Encoding Raw Bool where
  encode r := fieldsEncoding.encode r.fields
  decode bits := ofFields <$> fieldsEncoding.decode bits
  decode_encode r := by rw [fieldsEncoding.decode_encode]; rfl

abbrev Input (count : ℕ) := {r : Raw // r.WellFormed count}

def inputEncoding (count : ℕ) : Encoding (Input count) Bool where
  encode r := encoding.encode r.val
  decode bits := (encoding.decode bits).bind fun r=>
    if h : r.WellFormed count then some ⟨r,h⟩ else none
  decode_encode r := by simp [r.property]

theorem malformed_rejected (count : ℕ) (r : Raw) (hr : ¬r.WellFormed count) :
    (inputEncoding count).decode (encoding.encode r)=none := by
  simp [inputEncoding,hr]

def fieldsComputes : Computes encoding fieldsEncoding Raw.fields :=
  recode (identityComputes fieldsEncoding) Raw.fields (fun _=>rfl) (fun _=>rfl)

def variablesComputes : Computes encoding unary Raw.variables :=
  fieldsComputes.andThen (Wiring.firstComputes unary (pairEncoding unary addressesEncoding))

def tailComputes : Computes encoding (pairEncoding unary addressesEncoding)
    (fun r=>(r.constraints,r.addresses)) :=
  fieldsComputes.andThen (Wiring.secondComputes unary (pairEncoding unary addressesEncoding))

def constraintsComputes : Computes encoding unary Raw.constraints :=
  tailComputes.andThen (Wiring.firstComputes unary addressesEncoding)

def addressesComputes : Computes encoding addressesEncoding Raw.addresses :=
  tailComputes.andThen (Wiring.secondComputes unary addressesEncoding)

variable {n : ℕ} (p : OrientedPerfectPairing n)

def scope (r : Raw) (hr : r.WellFormed p.count) :
    GeneralEOPairedCSPCycles.Slot (N:=r.constraints) p→Fin r.variables := fun s=>
  ⟨r.addresses.getD s.val 0,by
    have hi : s.val<r.addresses.length := by rw [hr.1]; exact s.isLt
    apply hr.2
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _⟩

@[simp] theorem scope_val (r : Raw) (hr : r.WellFormed p.count)
    (s : GeneralEOPairedCSPCycles.Slot (N:=r.constraints) p) :
    (scope p r hr s).val=r.addresses.getD s.val 0 := rfl

theorem addresses_scope (r : Raw) (hr : r.WellFormed p.count) :
    GeneralEOPairedCSPScan.NatScan.addresses (scope p r hr)=r.addresses := by
  apply List.ext_getElem
  · simpa using hr.1.symm
  · intro i hi hj
    simp only [GeneralEOPairedCSPScan.NatScan.addresses,List.getElem_ofFn,scope_val]
    exact List.getD_eq_getElem _ _ hj

def read {m : ℕ} (x : Fin m→Bool) (i : ℕ) : Bool := if h : i<m then x ⟨i,h⟩ else false

theorem read_at {m : ℕ} (x : Fin m→Bool) (i : Fin m) : read x i.val=x i := by
  simp [read,i.isLt]

def value {K : Type*} [CommSemiring K] (g : Signature K p.count) (r : Raw) : K :=
  ∑x : Fin r.variables→Bool,∏v : Fin r.constraints,
    g (fun j=>read x (r.addresses.getD (v.val*p.count+j.val) 0))

theorem value_scope {K : Type*} [CommSemiring K] (g : Signature K p.count)
    (r : Raw) (hr : r.WellFormed p.count) :
    value p g r=GeneralEOPairedCSP.value p g (scope p r hr) := by
  unfold value GeneralEOPairedCSP.value
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext j
  have h : (GeneralEOPairedCSPCycles.incidence p v j).val=v.val*p.count+j.val := by
    change j.val+p.count*v.val=v.val*p.count+j.val
    simp [Nat.mul_comm,Nat.add_comm]
  rw [←h,←scope_val p r hr,read_at]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPRaw
