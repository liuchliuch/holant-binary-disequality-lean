import Holant.Proofs.Hardness.BinaryCSPProgrammeCore
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms

/-! Physical signed-to-unsigned star queries. Every occurrence of a sign gets
its own fresh leaves; repeated sign addresses are deliberately not deduplicated.
Original variables and original ordered binary rows remain present verbatim. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeStars
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten append lengthComputes succComputes)
end W
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (get unaryAdd)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

def leafEdges (r : Raw) (k : ℕ) : List (ℕ × ℕ) :=
  (List.range r.signs.length).flatMap fun i =>
    (List.range k).map fun j => (r.signs.getD i 0,r.variables+i*k+j)

def expand (r : Raw) (k : ℕ) : Raw :=
  ⟨r.variables+r.signs.length*k,r.edges++leafEdges r k,[]⟩

abbrev inputEncoding := pairEncoding encoding unary
abbrev rowEncoding := pairEncoding inputEncoding unary
abbrev cellEncoding := pairEncoding rowEncoding unary

def input : Computes inputEncoding encoding Prod.fst := Wiring.firstComputes encoding unary
def leaves : Computes inputEncoding unary Prod.snd := Wiring.secondComputes encoding unary
def rowInput : Computes rowEncoding inputEncoding Prod.fst := Wiring.firstComputes inputEncoding unary
def rowIndex : Computes rowEncoding unary Prod.snd := Wiring.secondComputes inputEncoding unary

def rowStart : Computes rowEncoding unary (fun x => x.1.1.variables+x.2*x.1.2) :=
  (pairComputes (rowInput.andThen (input.andThen variablesComputes))
    ((pairComputes rowIndex (rowInput.andThen leaves)).andThen
      BinaryInterpolation.WeightCompiler.multiplyUnaryComputes)).andThen A.unaryAdd

def rowAddress : Computes rowEncoding encodingNatBool (fun x => x.1.1.signs.getD x.2 0) :=
  A.get encodingNatBool 0 (rowInput.andThen (input.andThen signsComputes)) rowIndex

def cellComputes : Computes cellEncoding edgeEncoding
    (fun x => (x.1.1.1.signs.getD x.1.2 0,x.1.1.1.variables+x.1.2*x.1.1.2+x.2)) :=
  pairComputes ((Wiring.firstComputes rowEncoding unary).andThen rowAddress)
    (((pairComputes ((Wiring.firstComputes rowEncoding unary).andThen rowStart)
      (Wiring.secondComputes rowEncoding unary)).andThen A.unaryAdd).andThen UnaryBinary.computes)

def rowComputes : Computes rowEncoding edgesEncoding
    (fun x => (List.range x.1.2).map fun j =>
      (x.1.1.signs.getD x.2 0,x.1.1.variables+x.2*x.1.2+j)) :=
  W.tabulate rowEncoding edgeEncoding (fun x => x.1.2) (rowInput.andThen leaves) _ cellComputes

def leafEdgesComputes : Computes inputEncoding edgesEncoding (fun x => leafEdges x.1 x.2) :=
  congrComputes ((W.tabulate inputEncoding edgesEncoding (fun x => x.1.signs.length)
    (input.andThen signCountComputes) _ rowComputes).andThen (W.flatten edgeEncoding))
    (fun _ => rfl)

def expandComputes : Computes inputEncoding encoding (fun x => expand x.1 x.2) :=
  assemble
    ((pairComputes (input.andThen variablesComputes)
      ((pairComputes (input.andThen signCountComputes) leaves).andThen
        BinaryInterpolation.WeightCompiler.multiplyUnaryComputes)).andThen A.unaryAdd)
    ((pairComputes (input.andThen edgesComputes) leafEdgesComputes).andThen (W.append edgeEncoding))
    (constantComputes inputEncoding signsEncoding [])

def queries (r : Raw) : List Raw := (List.range (r.signs.length+1)).map (expand r)

def queriesComputes : Computes encoding (framedListEncoding encoding) queries :=
  W.tabulate encoding encoding (fun r => r.signs.length+1)
    (signCountComputes.andThen W.succComputes) expand expandComputes

def polyTime : PolyTime inputEncoding encoding (fun x => expand x.1 x.2) := expandComputes.toPolyTime
def queriesPolyTime : PolyTime encoding (framedListEncoding encoding) queries := queriesComputes.toPolyTime

@[simp] theorem leafEdges_length (r : Raw) (k : ℕ) : (leafEdges r k).length=r.signs.length*k := by
  simp [leafEdges,List.length_flatMap,List.sum_replicate,Nat.mul_comm]

@[simp] theorem expand_variables (r : Raw) (k : ℕ) :
    (expand r k).variables=r.variables+r.signs.length*k := rfl
@[simp] theorem expand_signs (r : Raw) (k : ℕ) : (expand r k).signs=[] := rfl
@[simp] theorem expand_edges_length (r : Raw) (k : ℕ) :
    (expand r k).edges.length=r.edges.length+r.signs.length*k := by simp [expand]
@[simp] theorem query_count (r : Raw) : (queries r).length=r.signs.length+1 := by simp [queries]

/-- Every old row, including its order and endpoints, is retained as a prefix. -/
theorem original_rows (r : Raw) (k : ℕ) : r.edges <+: (expand r k).edges :=
  ⟨leafEdges r k,rfl⟩

@[simp] theorem expand_zero (r : Raw) : expand r 0=⟨r.variables,r.edges,[]⟩ := by
  simp [expand,leafEdges]

theorem expand_valid (r : Raw) (hr : r.WellFormed) (k : ℕ) : (expand r k).WellFormed := by
  constructor
  · intro e he
    obtain he | he := List.mem_append.mp he
    · exact ⟨(hr.1 e he).1.trans_le (Nat.le_add_right _ _),
        (hr.1 e he).2.trans_le (Nat.le_add_right _ _)⟩
    · obtain ⟨i,hi,he⟩ := List.mem_flatMap.mp he
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
      have hi' : i < r.signs.length := List.mem_range.mp hi
      have hj' : j < k := List.mem_range.mp hj
      have hs : r.signs.getD i 0 ∈ r.signs := by
        rw [List.getD_eq_get r.signs 0 ⟨i,hi'⟩]
        exact List.get_mem _ _
      have hmul : (i+1)*k ≤ r.signs.length*k := Nat.mul_le_mul_right k hi'
      constructor
      · exact (hr.2 _ hs).trans_le (Nat.le_add_right _ _)
      · change r.variables+i*k+j < r.variables+r.signs.length*k
        rw [Nat.add_mul,Nat.one_mul] at hmul
        omega
  · simp [expand]

theorem query_valid (r : Raw) (hr : r.WellFormed) (q : Raw) (hq : q ∈ queries r) :
    q.WellFormed := by
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hq
  exact expand_valid r hr k

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeStars
