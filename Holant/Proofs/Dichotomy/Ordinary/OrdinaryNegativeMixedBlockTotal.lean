import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSource
import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyValidation
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms

/-! Arbitrary raw mixed-CSP inputs are validated by a real machine. Valid
inputs are passed unchanged to the literal mixed-block source; malformed
inputs issue no query and return field zero. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockTotal
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export OrdinaryNegativeMixedBlockData (family Input inputEncoding Recipe EvenRecipe)
end D
namespace C
export GeneralEOPairedCSPFamilyRaw (Raw encoding value)
end C
namespace A
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (list₁)
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (get)
end A
namespace M
export OrdinaryNegativeMixedBlockSource (trace privateValue privateControlled)
end M
namespace E
export StableHigherCurrentEvenCSPSource (tables)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {u : ℕ} {a : ℕ→ℕ}

def rawQueries (r : C.Raw u) : List (C.Raw u) :=
  if r.WellFormed (arity:=fun i=>a i*2) (D.family u a) then [r] else []

def rawComputes : Computes (C.encoding u) (framedListEncoding (C.encoding u)) (rawQueries (a:=a)) :=
  congrComputes (ifComputes (GeneralEOPairedCSPFamilyValidation.validates (arity:=fun i=>a i*2) (D.family u a))
    (A.list₁ (C.encoding u) (identityComputes (C.encoding u)))
    (constantComputes (C.encoding u) (framedListEncoding (C.encoding u)) []))
    (fun r=>by simp [rawQueries])

def queries (r : C.Raw u) : List (D.Input (u:=u) (a:=a)) :=
  if hr : r.WellFormed (arity:=fun i=>a i*2) (D.family u a) then [⟨r,hr⟩] else []

def queriesComputes : Computes (C.encoding u) (framedListEncoding (D.inputEncoding (u:=u) (a:=a))) queries :=
  recode (rawComputes (u:=u) (a:=a)) id (fun _=>rfl) (fun r=>by
    by_cases hr : r.WellFormed (arity:=fun i=>a i*2) (D.family u a)
    · simp only [rawQueries,queries,id_eq,ite_eq_left hr,dite_eq_left hr]; rfl
    · simp only [rawQueries,queries,id_eq,ite_eq_right hr,dite_eq_right hr]; rfl)

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (g : (i : Fin u)→Signature K (a i.val))

def value (r : D.Input (u:=u) (a:=a)) : K := C.value (arity:=fun i=>a i*2) (D.family u a) g r.val

def totalValue (r : C.Raw u) : K :=
  if r.WellFormed (arity:=fun i=>a i*2) (D.family u a) then C.value (arity:=fun i=>a i*2) (D.family u a) g r else 0

def pre : Computes (C.encoding u)
    (OracleBatch.contextEncoding (D.inputEncoding (u:=u) (a:=a)) encodingBoolBool)
    (fun r=>(queries (a:=a) r,false)) :=
  pairComputes queriesComputes (constantComputes (C.encoding u) encodingBoolBool false)

def post : Computes (OracleBatch.contextEncoding F.encoding encodingBoolBool) F.encoding
    (fun y=>y.1.getD 0 0) :=
  A.get F.encoding 0 (Wiring.firstComputes (framedListEncoding F.encoding) encodingBoolBool)
    (constantComputes _ UnaryBinary.unaryEncoding 0)

def toValid (bound : PolynomialOutputBound (D.inputEncoding (u:=u) (a:=a)) F.encoding (value g)) :
    LengthControlledOracleReduction (C.encoding u) F.encoding (D.inputEncoding (u:=u) (a:=a)) F.encoding
      (totalValue g) (value g) := by
  let q := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch (pre (u:=u) (a:=a)) (post F) bound
  refine {
    reduction := {
      machine := q.reduction.machine
      time := q.reduction.time
      correct := ?_ }
    targetOutput := q.targetOutput
    queryBound := q.queryBound
    safeQuery := q.safeQuery }
  intro oracle ho r
  have h := q.reduction.correct oracle ho r
  by_cases hr : r.WellFormed (arity:=fun i=>a i*2) (D.family u a)
  · simpa only [queries,dif_pos hr,totalValue,if_pos hr,OracleBatch.answers,List.map_cons,List.map_nil,
      List.getD_cons_zero,value] using h
  · simpa [queries,hr,totalValue,OracleBatch.answers] using h

variable {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (e p0 p1 : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (k : ℕ) (blocks : D.Recipe (u:=u) (s:=s) (a:=fun i=>a i+k) (b:=b))
variable (balanced : D.EvenRecipe blocks)

def controlled : LengthControlledOracleReduction (C.encoding u) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 b) F.encoding
    (totalValue (M.trace H k blocks)) ((E.tables F H).evaluate F) :=
  Programme.compose
    (toValid F (M.trace H k blocks)
      (M.privateControlled F H e p0 p1 he h0 h1 k blocks balanced).sourceOutputBound)
    (M.privateControlled F H e p0 p1 he h0 h1 k blocks balanced)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockTotal
end
