import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPinRaw
import Holant.Proofs.Hardness.GeneralEOPairedCSPValidation

/-! A physical byte programme expands each fixed constant/identification minor
into its literal parent row. Source addresses are ordinary free variables;
the target reserves 0,1 for false,true and shifts every free address by two. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRestrictionRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
namespace R
export GeneralEOPairedCSPRaw (Raw encoding unary addressesEncoding variablesComputes constraintsComputes addressesComputes)
end R
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten getD)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (unaryAdd bool)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {m n : ℕ} (p : Fin n → Bool ⊕ Fin m)

abbrev rowEncoding := pairEncoding R.encoding R.unary

def port (r : R.Raw) (v : ℕ) : Bool ⊕ Fin m → ℕ
  | .inl b => if b then 1 else 0
  | .inr j => r.addresses.getD (v*m+j.val) 0+2

def row (r : R.Raw) (v : ℕ) : List ℕ := List.ofFn (fun i => port r v (p i))

def addresses (r : R.Raw) : List ℕ := ((List.range r.constraints).map (row p r)).flatten

def raw (r : R.Raw) : R.Raw := ⟨r.variables,r.constraints,addresses p r⟩

def slotComputes (j : Fin m) : Computes rowEncoding R.unary (fun x => x.2*m+j.val) :=
  (pairComputes
    ((pairComputes (Wiring.secondComputes R.encoding R.unary)
      (constantComputes rowEncoding R.unary m)).andThen
        BinaryInterpolation.WeightCompiler.multiplyUnaryComputes)
    (constantComputes rowEncoding R.unary j.val)).andThen A.unaryAdd

def portComputes (q : Bool ⊕ Fin m) : Computes rowEncoding encodingNatBool
    (fun x => port x.1 x.2 q) := by
  cases q with
  | inl b => exact constantComputes rowEncoding encodingNatBool (if b then 1 else 0)
  | inr j =>
    let lookup := (pairComputes ((Wiring.firstComputes R.encoding R.unary).andThen R.addressesComputes)
      (slotComputes j)).andThen (W.getD encodingNatBool 0)
    exact (pairComputes lookup (constantComputes rowEncoding encodingNatBool 2)).andThen
      FixedGadgetSubstitution.Compiler.addComputes

def portsComputes (qs : List (Bool ⊕ Fin m)) : Computes rowEncoding R.addressesEncoding
    (fun x => qs.map (port x.1 x.2)) :=
  match qs with
  | [] => constantComputes rowEncoding R.addressesEncoding []
  | q::qs => (pairComputes (portComputes q) (portsComputes qs)).andThen (A.cons encodingNatBool)

def rowComputes : Computes rowEncoding R.addressesEncoding (fun x => row p x.1 x.2) :=
  congrComputes (portsComputes (List.ofFn p)) (fun _ => by simp only [row,List.map_ofFn,Function.comp_def])

def addressesComputes : Computes R.encoding R.addressesEncoding (addresses p) :=
  (W.tabulate R.encoding R.addressesEncoding (fun r : R.Raw => r.constraints)
    R.constraintsComputes (row p) (rowComputes p)).andThen (W.flatten encodingNatBool)

def rawComputes : Computes R.encoding R.encoding (raw p) :=
  recode (pairComputes R.variablesComputes (pairComputes R.constraintsComputes (addressesComputes p)))
    id (fun _ => rfl) (fun _ => rfl)

def lengthValidComputes : Computes R.encoding encodingBoolBool
    (fun r => decide (r.addresses.length=r.constraints*m)) :=
  (pairComputes
    ((R.addressesComputes.andThen
      (Holant.LocalDrafts.Tractability.AffineMachine.WireLists.lengthComputes encodingNatBool)).andThen
        UnaryBinary.computes)
    (((pairComputes R.constraintsComputes (constantComputes R.encoding R.unary m)).andThen
      BinaryInterpolation.WeightCompiler.multiplyUnaryComputes).andThen UnaryBinary.computes)).andThen
      UniversalPairReduction.SmoothingCompiler.Endpoints.equalComputes

def validates : Computes R.encoding encodingBoolBool (fun r => decide (r.WellFormed m)) :=
  congrComputes (A.bool Bool.and (lengthValidComputes (m:=m))
    GeneralEOPairedCSPValidation.addressesValidComputes)
    (fun r => by apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]; rfl)

@[simp] theorem row_length (r : R.Raw) (v : ℕ) : (row p r v).length=n := List.length_ofFn

theorem addresses_length (r : R.Raw) : (addresses p r).length=r.constraints*n := by
  simp [addresses,List.length_flatten,List.map_map,Function.comp_def]

theorem addresses_lt (r : R.Raw) (hr : r.WellFormed m) :
    ∀a∈addresses p r,a<r.variables+2 := by
  intro a ha
  obtain ⟨qs,hqs,ha⟩ := List.mem_flatten.mp ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hqs
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  have hv' : v<r.constraints := List.mem_range.mp hv
  cases he : p j with
  | inl b => cases b <;> simp [port]
  | inr i =>
    have hi : v*m+i.val<r.addresses.length := by
      rw [hr.1]
      exact lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (by
        simpa only [Nat.succ_mul] using Nat.mul_le_mul_right m hv')
    have hh := hr.2 (r.addresses.getD (v*m+i.val) 0) (by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem _)
    change r.addresses.getD (v*m+i.val) 0+2<r.variables+2
    omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRestrictionRaw
