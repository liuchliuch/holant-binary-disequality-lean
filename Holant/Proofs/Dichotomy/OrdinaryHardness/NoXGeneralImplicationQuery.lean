import Holant.Proofs.Hardness.BinaryCSPProgrammeStars
import Holant.Proofs.Hardness.BinaryCSPProgrammeValidated

/-! Each signed NAND edge is replaced by two outgoing implication edges
from one fresh signed auxiliary vertex. This is an actual bounded tape writer;
old signs, unused variables and repeated original endpoints are preserved. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralImplicationQuery
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 BinaryCSPProgrammeCore
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten append)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (get unaryAdd)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons list₁)
end A
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false

def edgeRows (r : Raw) (i : ℕ) : List (ℕ×ℕ) :=
  [(r.variables+i,(r.edges.getD i (0,0)).1),(r.variables+i,(r.edges.getD i (0,0)).2)]

def fresh (r : Raw) : List ℕ := (List.range r.edges.length).map (fun i=>r.variables+i)

def expand (r : Raw) : Raw :=
  ⟨r.variables+r.edges.length,(List.range r.edges.length).flatMap (edgeRows r),r.signs++fresh r⟩

abbrev context := pairEncoding encoding unary

def old : Computes context encoding Prod.fst := Wiring.firstComputes encoding unary

def index : Computes context unary Prod.snd := Wiring.secondComputes encoding unary

def auxiliary : Computes context encodingNatBool (fun x : Raw×ℕ=>x.1.variables+x.2) :=
  ((pairComputes (old.andThen variablesComputes) index).andThen A.unaryAdd).andThen UnaryBinary.computes

def selected : Computes context edgeEncoding (fun x : Raw×ℕ=>x.1.edges.getD x.2 (0,0)) :=
  A.get edgeEncoding (0,0) (old.andThen edgesComputes) index

def firstEdge : Computes context edgeEncoding
    (fun x : Raw×ℕ=>(x.1.variables+x.2,(x.1.edges.getD x.2 (0,0)).1)) :=
  pairComputes auxiliary (selected.andThen (Wiring.firstComputes encodingNatBool encodingNatBool))

def secondEdge : Computes context edgeEncoding
    (fun x : Raw×ℕ=>(x.1.variables+x.2,(x.1.edges.getD x.2 (0,0)).2)) :=
  pairComputes auxiliary (selected.andThen (Wiring.secondComputes encodingNatBool encodingNatBool))

def rowComputes : Computes context edgesEncoding (fun x : Raw×ℕ=>edgeRows x.1 x.2) :=
  (pairComputes firstEdge (A.list₁ edgeEncoding secondEdge)).andThen (A.cons edgeEncoding)

def expandedEdges : Computes encoding edgesEncoding
    (fun r=>(List.range r.edges.length).flatMap (edgeRows r)) :=
  congrComputes ((W.tabulate encoding edgesEncoding (fun r=>r.edges.length) edgeCountComputes
    edgeRows rowComputes).andThen (W.flatten edgeEncoding)) (fun _=>rfl)

def freshComputes : Computes encoding signsEncoding fresh :=
  W.tabulate encoding encodingNatBool (fun r=>r.edges.length) edgeCountComputes
    (fun r i=>r.variables+i) auxiliary

def computes : Computes encoding encoding expand :=
  assemble ((pairComputes variablesComputes edgeCountComputes).andThen A.unaryAdd)
    expandedEdges ((pairComputes signsComputes freshComputes).andThen (W.append encodingNatBool))

theorem selected_mem (r : Raw) (i : ℕ) (hi : i<r.edges.length) : r.edges.getD i (0,0)∈r.edges := by
  rw [List.getD_eq_get r.edges (0,0) ⟨i,hi⟩]
  exact List.get_mem _ _

theorem valid (r : Raw) (hr : r.WellFormed) : (expand r).WellFormed := by
  have size : (expand r).variables=r.variables+r.edges.length := rfl
  constructor
  · intro e he
    obtain ⟨i,hi,he⟩ := List.mem_flatMap.mp he
    have hi' : i<r.edges.length := List.mem_range.mp hi
    have bounds:=hr.1 _ (selected_mem r i hi')
    simp only [edgeRows,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl <;> change r.variables+i<r.variables+r.edges.length ∧ _
    all_goals constructor
    all_goals omega
  · intro v hv
    rcases List.mem_append.mp hv with old|new
    · exact (hr.2 v old).trans_le (Nat.le_add_right _ _)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp new
      have hi' := List.mem_range.mp hi
      change r.variables+i<r.variables+r.edges.length
      omega

def query (r : P.Input) : P.Input := ⟨expand r.val,valid r.val r.property⟩

def queryComputes : Computes P.inputEncoding P.inputEncoding query :=
  recode computes Subtype.val (fun _=>rfl) (fun _=>rfl)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralImplicationQuery
end
