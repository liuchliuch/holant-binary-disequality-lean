import Holant.Proofs.Hardness.GeneralEOPairedCSPValidated

/-! Physical validation of arbitrary CSP records before any oracle query.
Wrong occurrence counts and out-of-range variable addresses are rejected by
actual finite stack programmes, not merely a proof-carrying input subtype. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPValidation
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GeneralEOPairedCSPRaw FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
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

variable {n : ℕ} (p : OrientedPerfectPairing n)

def lengthValidComputes : Computes encoding encodingBoolBool
    (fun r=>decide (r.addresses.length=r.constraints*p.count)) :=
  (pairComputes
    ((addressesComputes.andThen (W.lengthComputes encodingNatBool)).andThen UnaryBinary.computes)
    ((GeneralEOPairedCSPProgramme.edgeCountComputes p).andThen UnaryBinary.computes)).andThen
      Endpoints.equalComputes

def addressesValidComputes : Computes encoding encodingBoolBool
    (fun r=>r.addresses.all (fun v=>decide (v<r.variables))) := by
  let cell : Computes (pairEncoding encoding encodingNatBool) encodingBoolBool
      (fun x=>decide (x.2<x.1.variables)) :=
    (pairComputes (Wiring.secondComputes encoding encodingNatBool)
      (((Wiring.firstComputes encoding encodingNatBool).andThen variablesComputes).andThen
        UnaryBinary.computes)).andThen Endpoints.lessComputes
  exact congrComputes ((A.map encodingNatBool encodingBoolBool addressesComputes
    (fun r v=>decide (v<r.variables)) cell).andThen
      Holant.LocalDrafts.Tractability.AffineMachine.ResidueCells.all)
    (fun r=>by simp only [List.all_map,Function.comp_def,id_eq])

def validates : Computes encoding encodingBoolBool (fun r=>decide (r.WellFormed p.count)) :=
  congrComputes (A.bool Bool.and (lengthValidComputes p) addressesValidComputes)
    (fun r=>by apply Bool.eq_iff_iff.mpr; simp [Raw.WellFormed,List.all_eq_true])

def rawQueries (label : ℕ) (r : Raw) : List RawClosedNetwork :=
  if r.WellFormed p.count then [GeneralEOPairedCSPProgramme.raw p label r] else []

def rawQueriesComputes (label : ℕ) : Computes encoding (framedListEncoding RawClosedNetwork.encoding)
    (rawQueries p label) :=
  congrComputes (ifComputes (validates p)
    (A.list₁ RawClosedNetwork.encoding (GeneralEOPairedCSPProgramme.rawComputes p label))
    (constantComputes encoding (framedListEncoding RawClosedNetwork.encoding) []))
    (fun r=>by simp [rawQueries])

theorem invalid_no_queries (label : ℕ) (r : Raw) (hr : ¬r.WellFormed p.count) :
    rawQueries p label r=[] := by simp [rawQueries,hr]

variable {s : ℕ} {arity : ℕ→ℕ} (label : Fin s)
variable (q : OrientedPerfectPairing (arity label.val))

def queries (r : Raw) : List (GeneralEOPairedCSPRecords.TargetInput (s:=s) (arity:=arity)) :=
  if hr : r.WellFormed q.count then [GeneralEOPairedCSPValidated.query label q ⟨r,hr⟩] else []

def queriesComputes : Computes encoding
    (framedListEncoding (RawClosedNetwork.validatedEncoding s 1 arity)) (queries label q) :=
  recode (rawQueriesComputes q label.val) id (fun _=>rfl) (fun r=>by
    simp only [id_eq]
    by_cases hr : r.WellFormed q.count
    · simp only [rawQueries,queries,ite_eq_left hr,dite_eq_left hr]
      have h := GeneralEOPairedCSPValidated.raw_eq label q ⟨r,hr⟩
      change GeneralEOPairedCSPProgramme.raw q label.val r=_ at h
      rw [h]
      rfl
    · simp only [rawQueries,queries,ite_eq_right hr,dite_eq_right hr]
      rfl)

theorem rejected (r : Raw) (hr : ¬r.WellFormed q.count) : queries label q r=[] := by
  simp [queries,hr]

theorem accepted (r : Raw) (hr : r.WellFormed q.count) :
    queries label q r=[GeneralEOPairedCSPValidated.query label q ⟨r,hr⟩] := by
  simp [queries,hr]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPValidation
