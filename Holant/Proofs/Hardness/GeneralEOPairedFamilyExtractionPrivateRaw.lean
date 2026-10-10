import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionMarginalRaw

/-! Each constraint receives a disjoint block of k private variables, written
by actual finite-list machines. Old variables and unused addresses are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPrivateRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
namespace R
export GeneralEOPairedCSPRaw (Raw encoding unary addressesEncoding variablesComputes constraintsComputes addressesComputes)
end R
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten getD)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (unaryAdd)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons)
end A
namespace P
export GeneralEOPairedFamilyExtractionRestrictionRaw (rowEncoding slotComputes)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable (m k : ℕ)

def port (r : R.Raw) (v : ℕ) : Fin (m+k) → ℕ :=
  Fin.addCases (fun j => r.addresses.getD (v*m+j.val) 0)
    (fun j => r.variables+(v*k+j.val))
def row (r : R.Raw) (v : ℕ) : List ℕ := List.ofFn (port m k r v)
def addresses (r : R.Raw) : List ℕ := ((List.range r.constraints).map (row m k r)).flatten
def raw (r : R.Raw) : R.Raw := ⟨r.variables+r.constraints*k,r.constraints,addresses m k r⟩

def privateCountComputes : Computes R.encoding R.unary (fun r : R.Raw => r.constraints*k) :=
  (pairComputes R.constraintsComputes (constantComputes R.encoding R.unary k)).andThen
    BinaryInterpolation.WeightCompiler.multiplyUnaryComputes

def freshComputes (j : Fin k) : Computes P.rowEncoding encodingNatBool
    (fun x : R.Raw×ℕ => x.1.variables+(x.2*k+j.val)) :=
  ((pairComputes ((Wiring.firstComputes R.encoding R.unary).andThen R.variablesComputes)
    (P.slotComputes j)).andThen A.unaryAdd).andThen UnaryBinary.computes

def portComputes (j : Fin (m+k)) : Computes P.rowEncoding encodingNatBool
    (fun x : R.Raw×ℕ => port m k x.1 x.2 j) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [port,Fin.addCases_left] using GeneralEOPairedFamilyExtractionMarginalRaw.oldComputes m j
  · simpa only [port,Fin.addCases_right] using freshComputes k j

def portsComputes (js : List (Fin (m+k))) : Computes P.rowEncoding R.addressesEncoding
    (fun x : R.Raw×ℕ => js.map (port m k x.1 x.2)) :=
  match js with
  | [] => constantComputes P.rowEncoding R.addressesEncoding []
  | j::js => (pairComputes (portComputes m k j) (portsComputes js)).andThen (A.cons encodingNatBool)

def rowComputes : Computes P.rowEncoding R.addressesEncoding (fun x : R.Raw×ℕ => row m k x.1 x.2) :=
  congrComputes (portsComputes m k (List.ofFn id))
    (fun _ => by simp only [row,List.map_ofFn,Function.comp_def,id_eq])

def addressesComputes : Computes R.encoding R.addressesEncoding (addresses m k) :=
  (W.tabulate R.encoding R.addressesEncoding (fun r : R.Raw=>r.constraints) R.constraintsComputes
    (row m k) (rowComputes m k)).andThen (W.flatten encodingNatBool)

def rawComputes : Computes R.encoding R.encoding (raw m k) :=
  recode (pairComputes ((pairComputes R.variablesComputes (privateCountComputes k)).andThen A.unaryAdd)
    (pairComputes R.constraintsComputes (addressesComputes m k))) id (fun _=>rfl) (fun _=>rfl)

@[simp] theorem row_length (r : R.Raw) (v : ℕ) : (row m k r v).length=m+k := List.length_ofFn

theorem addresses_length (r : R.Raw) : (addresses m k r).length=r.constraints*(m+k) := by
  simp [addresses,List.length_flatten,List.map_map,Function.comp_def]

theorem valid (r : R.Raw) (hr : r.WellFormed m) : (raw m k r).WellFormed (m+k) := by
  refine ⟨addresses_length m k r,?_⟩
  intro a ha
  obtain ⟨qs,hqs,ha⟩ := List.mem_flatten.mp ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hqs
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  have hv' : v<r.constraints := List.mem_range.mp hv
  refine Fin.addCases (fun j=>?_) (fun j=>?_) j
  · simp only [port,Fin.addCases_left]
    have hi : v*m+j.val<r.addresses.length := by
      rw [hr.1]
      exact lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (by
        simpa only [Nat.succ_mul] using Nat.mul_le_mul_right m hv')
    have hh := hr.2 (r.addresses.getD (v*m+j.val) 0) (by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem _)
    exact lt_of_lt_of_le hh (Nat.le_add_right _ _)
  · simp only [port,Fin.addCases_right,raw]
    apply Nat.add_lt_add_left
    exact lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right k hv')

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPrivateRaw
