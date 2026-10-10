import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRestrictionRaw

/-! Each source constraint receives one distinct private Boolean variable.
The actual byte writer retains all declared variables, repeated addresses and
nullary source rows. It emits the ordinary unpinned raw CSP codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionMarginalRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
namespace R
export GeneralEOPairedCSPRaw (Raw encoding unary addressesEncoding variablesComputes constraintsComputes addressesComputes)
end R
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten getD append)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (unaryAdd)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons list₁)
end A
namespace P
export GeneralEOPairedFamilyExtractionRestrictionRaw (rowEncoding slotComputes)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable (m : ℕ)

def port (r : R.Raw) (v : ℕ) : Fin (m+1) → ℕ :=
  Fin.lastCases (r.variables+v) (fun j => r.addresses.getD (v*m+j.val) 0)

def row (r : R.Raw) (v : ℕ) : List ℕ := List.ofFn (port m r v)
def addresses (r : R.Raw) : List ℕ := ((List.range r.constraints).map (row m r)).flatten

def raw (r : R.Raw) : R.Raw := ⟨r.variables+r.constraints,r.constraints,addresses m r⟩

def oldComputes (j : Fin m) : Computes P.rowEncoding encodingNatBool
    (fun x : R.Raw×ℕ => x.1.addresses.getD (x.2*m+j.val) 0) :=
  (pairComputes ((Wiring.firstComputes R.encoding R.unary).andThen R.addressesComputes)
    (P.slotComputes j)).andThen (W.getD encodingNatBool 0)

def oldListComputes (js : List (Fin m)) : Computes P.rowEncoding R.addressesEncoding
    (fun x : R.Raw×ℕ => js.map (fun j => x.1.addresses.getD (x.2*m+j.val) 0)) :=
  match js with
  | [] => constantComputes P.rowEncoding R.addressesEncoding []
  | j::js => (pairComputes (oldComputes m j) (oldListComputes js)).andThen (A.cons encodingNatBool)

def freshComputes : Computes P.rowEncoding encodingNatBool (fun x : R.Raw×ℕ=>x.1.variables+x.2) :=
  ((pairComputes ((Wiring.firstComputes R.encoding R.unary).andThen R.variablesComputes)
    (Wiring.secondComputes R.encoding R.unary)).andThen A.unaryAdd).andThen UnaryBinary.computes

def rowComputes : Computes P.rowEncoding R.addressesEncoding (fun x : R.Raw×ℕ=>row m x.1 x.2) :=
  congrComputes ((pairComputes (oldListComputes m (List.ofFn id))
    (A.list₁ encodingNatBool (freshComputes))).andThen (W.append encodingNatBool))
    (fun x => by simp only [row,List.ofFn_succ',port,List.map_ofFn,Function.comp_def,
      Fin.lastCases_castSucc,Fin.lastCases_last,List.concat_eq_append,id_eq])

def addressesComputes : Computes R.encoding R.addressesEncoding (addresses m) :=
  (W.tabulate R.encoding R.addressesEncoding (fun r : R.Raw=>r.constraints) R.constraintsComputes
    (row m) (rowComputes m)).andThen (W.flatten encodingNatBool)

def rawComputes : Computes R.encoding R.encoding (raw m) :=
  recode (pairComputes ((pairComputes R.variablesComputes R.constraintsComputes).andThen A.unaryAdd)
    (pairComputes R.constraintsComputes (addressesComputes m))) id (fun _=>rfl) (fun _=>rfl)

@[simp] theorem row_length (r : R.Raw) (v : ℕ) : (row m r v).length=m+1 := List.length_ofFn

theorem addresses_length (r : R.Raw) : (addresses m r).length=r.constraints*(m+1) := by
  simp [addresses,List.length_flatten,List.map_map,Function.comp_def]

theorem valid (r : R.Raw) (hr : r.WellFormed m) : (raw m r).WellFormed (m+1) := by
  refine ⟨addresses_length m r,?_⟩
  intro a ha
  obtain ⟨qs,hqs,ha⟩ := List.mem_flatten.mp ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hqs
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  have hv' : v<r.constraints := List.mem_range.mp hv
  refine Fin.lastCases ?_ (fun j=>?_) j
  · simpa only [port,Fin.lastCases_last,raw] using Nat.add_lt_add_left hv' r.variables
  · simp only [port,Fin.lastCases_castSucc]
    have hi : v*m+j.val<r.addresses.length := by
      rw [hr.1]
      exact lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (by
        simpa only [Nat.succ_mul] using Nat.mul_le_mul_right m hv')
    have hh := hr.2 (r.addresses.getD (v*m+j.val) 0) (by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem _)
    exact lt_of_lt_of_le hh (Nat.le_add_right _ _)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionMarginalRaw
