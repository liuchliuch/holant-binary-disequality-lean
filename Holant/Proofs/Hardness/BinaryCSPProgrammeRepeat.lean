import Holant.Proofs.Hardness.BinaryCSPProgrammeStars

/-! Positive Hadamard repetition writes k+1 copies of every binary row. The
variable declaration is unchanged, so isolated variables continue to contribute
their original factor two. No exponent-zero oracle query is constructed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeRepeat
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten succComputes)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

def expand (r : Raw) (k : ℕ) : Raw :=
  ⟨r.variables,r.edges.flatMap (List.replicate (k+1)),r.signs⟩

abbrev inputEncoding := pairEncoding encoding unary
abbrev repeatEncoding := pairEncoding unary edgeEncoding

def edgeCopiesComputes : Computes repeatEncoding edgesEncoding
    (fun x => List.replicate (x.1+1) x.2) := by
  let count := (Wiring.firstComputes unary edgeEncoding).andThen W.succComputes
  let cell := (Wiring.firstComputes repeatEncoding unary).andThen
    (Wiring.secondComputes unary edgeEncoding)
  exact congrComputes (W.tabulate repeatEncoding edgeEncoding (fun x => x.1+1) count
    (fun x _ => x.2) cell) (fun x => by simp)

def repeatComputes : Computes inputEncoding encoding (fun x => expand x.1 x.2) := by
  let raw := Wiring.firstComputes encoding unary
  let k := Wiring.secondComputes encoding unary
  let chunks := (pairComputes k (raw.andThen edgesComputes)).andThen
    (UniversalPairReduction.SmoothingCompiler.mapListComputes unary edgeEncoding edgesEncoding
      (fun n e => List.replicate (n+1) e) edgeCopiesComputes)
  let expanded := congrComputes (chunks.andThen (W.flatten edgeEncoding))
    (fun _ => (List.flatMap_def).symm)
  exact assemble (raw.andThen variablesComputes) expanded (raw.andThen signsComputes)

def polyTime : PolyTime inputEncoding encoding (fun x => expand x.1 x.2) := repeatComputes.toPolyTime

@[simp] theorem repeat_variables (r : Raw) (k : ℕ) : (expand r k).variables=r.variables := rfl
@[simp] theorem repeat_signs (r : Raw) (k : ℕ) : (expand r k).signs=r.signs := rfl
@[simp] theorem repeat_zero (r : Raw) : expand r 0=r := by
  cases r with
  | mk n es ss =>
    simp only [expand,Nat.zero_add,List.replicate_one]
    congr 1
    induction es with
    | nil => rfl
    | cons e es ih => simpa using congrArg (List.cons e) ih
@[simp] theorem repeat_edges_length (r : Raw) (k : ℕ) :
    (expand r k).edges.length=r.edges.length*(k+1) := by
  simp [expand,List.length_flatMap,List.sum_replicate]

theorem repeat_valid (r : Raw) (hr : r.WellFormed) (k : ℕ) : (expand r k).WellFormed := by
  refine ⟨?_,hr.2⟩
  intro e he
  obtain ⟨old,hold,he⟩ := List.mem_flatMap.mp he
  have heq : e=old := (List.mem_replicate.mp he).2
  subst e
  exact hr.1 old hold

/-- The full cube budget is intentionally collision-insensitive. -/
def sampleCount (r : Raw) : ℕ := (r.edges.length+1)^3
def queries (r : Raw) : List Raw := (List.range (sampleCount r)).map (expand r)

def sampleCountComputes : Computes encoding unary sampleCount := by
  let n := edgeCountComputes.andThen W.succComputes
  let sq := (pairComputes n n).andThen BinaryInterpolation.WeightCompiler.multiplyUnaryComputes
  exact congrComputes ((pairComputes sq n).andThen BinaryInterpolation.WeightCompiler.multiplyUnaryComputes)
    (fun _ => by simp [sampleCount,pow_succ,pow_zero])

def queriesComputes : Computes encoding (framedListEncoding encoding) queries :=
  W.tabulate encoding encoding sampleCount sampleCountComputes expand repeatComputes

def queriesPolyTime : PolyTime encoding (framedListEncoding encoding) queries := queriesComputes.toPolyTime

@[simp] theorem query_count (r : Raw) : (queries r).length=(r.edges.length+1)^3 := by
  simp [queries,sampleCount]

theorem query_valid (r : Raw) (hr : r.WellFormed) (q : Raw) (hq : q ∈ queries r) :
    q.WellFormed := by
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hq
  exact repeat_valid r hr k

theorem query_positive (r : Raw) (q : Raw) (hq : q ∈ queries r) :
    ∃ k, 0<k ∧ q.edges=r.edges.flatMap (List.replicate k) ∧ q.variables=r.variables := by
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hq
  exact ⟨k+1,Nat.zero_lt_succ k,rfl,rfl⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeRepeat
