import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyValidated

/-! Physical validation of arbitrary CSP records before any oracle query.
Wrong occurrence counts and out-of-range variable addresses are rejected by
actual finite stack programmes, not merely a proof-carrying input subtype. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyValidation
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GeneralEOPairedCSPFamilyRaw FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (map bool)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (list₁)
end A
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (lengthComputes)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ→ℕ} (P : (i : Fin s)→OrientedPerfectPairing (arity i.val))

def lengthValidComputes : Computes (encoding s) encodingBoolBool
    (fun r=>decide (r.addresses.length=r.edgeCount P)) :=
  (pairComputes
    ((addressesComputes.andThen (W.lengthComputes encodingNatBool)).andThen UnaryBinary.computes)
    ((GeneralEOPairedCSPFamilyProgramme.edgeCountComputes P).andThen UnaryBinary.computes)).andThen
      Endpoints.equalComputes

def addressesValidComputes : Computes (encoding s) encodingBoolBool
    (fun r=>r.addresses.all (fun v=>decide (v<r.variables))) := by
  let cell : Computes (pairEncoding (encoding s) encodingNatBool) encodingBoolBool
      (fun x=>decide (x.2<x.1.variables)) :=
    (pairComputes (Wiring.secondComputes (encoding s) encodingNatBool)
      (((Wiring.firstComputes (encoding s) encodingNatBool).andThen variablesComputes).andThen
        UnaryBinary.computes)).andThen Endpoints.lessComputes
  exact congrComputes ((A.map encodingNatBool encodingBoolBool addressesComputes
    (fun r v=>decide (v<r.variables)) cell).andThen
      Holant.LocalDrafts.Tractability.AffineMachine.ResidueCells.all)
    (fun r=>by simp only [List.all_map,Function.comp_def,id_eq])

def validates : Computes (encoding s) encodingBoolBool (fun r=>decide (r.WellFormed P)) :=
  congrComputes (A.bool Bool.and (lengthValidComputes P) addressesValidComputes)
    (fun r=>by apply Bool.eq_iff_iff.mpr; simp [Raw.WellFormed,List.all_eq_true])

def rawQueries (r : Raw s) : List RawClosedNetwork :=
  if r.WellFormed P then [GeneralEOPairedCSPFamilyProgramme.raw P r] else []

def rawQueriesComputes : Computes (encoding s) (framedListEncoding RawClosedNetwork.encoding)
    (rawQueries P) :=
  congrComputes (ifComputes (validates P)
    (A.list₁ RawClosedNetwork.encoding (GeneralEOPairedCSPFamilyProgramme.rawComputes P))
    (constantComputes (encoding s) (framedListEncoding RawClosedNetwork.encoding) []))
    (fun r=>by simp [rawQueries])

theorem invalid_no_queries (r : Raw s) (hr : ¬r.WellFormed P) :
    rawQueries P r=[] := by simp [rawQueries,hr]

def queries (r : Raw s) : List (GeneralEOPairedCSPRecords.TargetInput (s:=s) (arity:=arity)) :=
  if hr : r.WellFormed P then [GeneralEOPairedCSPFamilyValidated.query P ⟨r,hr⟩] else []

def queriesComputes : Computes (encoding s)
    (framedListEncoding (RawClosedNetwork.validatedEncoding s 1 arity)) (queries P) :=
  recode (rawQueriesComputes P) id (fun _=>rfl) (fun r=>by
    simp only [id_eq]
    by_cases hr : r.WellFormed P
    · simp only [rawQueries,queries,ite_eq_left hr,dite_eq_left hr]
      have h := GeneralEOPairedCSPFamilyValidated.raw_eq P ⟨r,hr⟩
      change GeneralEOPairedCSPFamilyProgramme.raw P r=_ at h
      rw [h]
      rfl
    · simp only [rawQueries,queries,ite_eq_right hr,dite_eq_right hr]
      rfl)

theorem rejected (r : Raw s) (hr : ¬r.WellFormed P) : queries P r=[] := by
  simp [queries,hr]

theorem accepted (r : Raw s) (hr : r.WellFormed P) :
    queries P r=[GeneralEOPairedCSPFamilyValidated.query P ⟨r,hr⟩] := by
  simp [queries,hr]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyValidation
