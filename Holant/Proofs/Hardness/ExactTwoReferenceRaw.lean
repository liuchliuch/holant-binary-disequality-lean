import Holant.Proofs.Hardness.PairedPinsRaw

/-! Literal shared-reference ring records. The old singleton signature keeps
label0 and every original ordered port. Each01 row becomes an E row, retaining
its first two ports and appending reference ports2/3. New native edges connect
port3_i to port2_(i+1) in ONE cycle. The m=1 cycle is a legal same-row loop.
Defaults only make the raw function total; validation/semantics are separate. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceRaw
open Holant.Complexity

abbrev sourceArity := PairedPinsRaw.targetArity 1 (fun _=>4)
def targetArity (_ : ℕ) : ℕ := 4

def oldRows (r : RawClosedNetwork) : List RawVertex := r.vertices.filter fun row=>row.1<1
def pinRows (r : RawClosedNetwork) : List RawVertex := r.vertices.filter fun row=>row.1==1
def count (r : RawClosedNetwork) : ℕ := (pinRows r).length

/-- Cyclic predecessor on valid indices, without runtime natural division. -/
def previous (m i : ℕ) : ℕ := if i=0 then m-1 else i-1

def row (r : RawClosedNetwork) (i : ℕ) : RawVertex :=
  (1,[((pinRows r).getD i (0,[])).2.getD 0 (0,false),
      ((pinRows r).getD i (0,[])).2.getD 1 (0,false),
      (r.edges.length+previous (count r) i,true),
      (r.edges.length+i,false)])

def rows (r : RawClosedNetwork) : List RawVertex := (List.range (count r)).map (row r)

def raw (r : RawClosedNetwork) : RawClosedNetwork where
  vertices := oldRows r++rows r
  edges := r.edges++List.replicate (count r) 0

theorem row_label (r : RawClosedNetwork) (i : ℕ) : (row r i).1=1 := rfl
theorem row_arity (r : RawClosedNetwork) (i : ℕ) : (row r i).2.length=4 := rfl
theorem rows_length (r : RawClosedNetwork) : (rows r).length=count r := by simp [rows]
theorem edges_length (r : RawClosedNetwork) : (raw r).edges.length=r.edges.length+count r := by simp [raw]
theorem vertices_length (r : RawClosedNetwork) :
    (raw r).vertices.length=(oldRows r).length+count r := by simp [raw,rows_length]

theorem previous_one : previous 1 0=0 := rfl

theorem single_row (r : RawClosedNetwork) (h : count r=1) :
    row r 0=(1,[((pinRows r).getD 0 (0,[])).2.getD 0 (0,false),
      ((pinRows r).getD 0 (0,[])).2.getD 1 (0,false),
      (r.edges.length,true),(r.edges.length,false)]) := by
  simp [row,h,previous]

/-- Literal m=0 empty instance; no extra loop and no factor2 are inserted. -/
theorem empty_raw : raw ⟨[],[]⟩=⟨[],[]⟩ := rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceRaw
