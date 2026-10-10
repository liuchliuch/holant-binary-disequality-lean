import Holant.Proofs.Hardness.ExactTwoReferenceValidation
import Holant.Complexity.UniversalPairReduction.Input

/-! A shared reference cycle with one literal directed-pin anchor. Every old
pin becomes a DEQ4 row; the anchor fixes all reference colours to false. The
zero-pin case is one anchor self-loop and has scalar one. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationRaw
open Holant.Complexity UniversalPairReduction
open ExactTwoReferenceRaw (previous)
def oldRows (s : ℕ) (r : RawClosedNetwork) : List RawVertex := r.vertices.filter fun row => row.1<s
def pinRows (s : ℕ) (r : RawClosedNetwork) : List RawVertex := r.vertices.filter fun row => row.1==s
def count (s : ℕ) (r : RawClosedNetwork) : ℕ := (pinRows s r).length

def reference (s : ℕ) (r : RawClosedNetwork) (i : ℕ) : List RawEndpoint :=
  [(r.edges.length+previous (count s r+1) i,true),(r.edges.length+i,false)]
def anchor (s : ℕ) (r : RawClosedNetwork) : RawVertex := (s,reference s r 0)
def row (s j : ℕ) (r : RawClosedNetwork) (i : ℕ) : RawVertex :=
  (j,[((pinRows s r).getD i (0,[])).2.getD 0 (0,false),
      ((pinRows s r).getD i (0,[])).2.getD 1 (0,false)]++reference s r (i+1))
def rows (s j : ℕ) (r : RawClosedNetwork) : List RawVertex := (List.range (count s r)).map (row s j r)
def raw (s j : ℕ) (r : RawClosedNetwork) : RawClosedNetwork where
  vertices := oldRows s r++anchor s r::rows s j r
  edges := r.edges++List.replicate (count s r+1) 0

theorem row_label (s j : ℕ) (r : RawClosedNetwork) (i : ℕ) : (row s j r i).1=j := rfl
theorem row_arity (s j : ℕ) (r : RawClosedNetwork) (i : ℕ) : (row s j r i).2.length=4 := rfl
theorem rows_length (s j : ℕ) (r : RawClosedNetwork) : (rows s j r).length=count s r := by simp [rows]
theorem edges_length (s j : ℕ) (r : RawClosedNetwork) :
    (raw s j r).edges.length=r.edges.length+count s r+1 := by simp [raw,Nat.add_assoc]
theorem vertices_length (s j : ℕ) (r : RawClosedNetwork) :
    (raw s j r).vertices.length=(oldRows s r).length+count s r+1 := by
  simp [raw,rows_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem reference_zero (s : ℕ) (r : RawClosedNetwork) :
    reference s r 0=[(r.edges.length+count s r,true),(r.edges.length,false)] := by
  simp [reference,previous]
theorem reference_succ (s : ℕ) (r : RawClosedNetwork) (i : ℕ) :
    reference s r (i+1)=[(r.edges.length+i,true),(r.edges.length+i+1,false)] := by
  simp [reference,previous,Nat.add_assoc]
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationRaw
