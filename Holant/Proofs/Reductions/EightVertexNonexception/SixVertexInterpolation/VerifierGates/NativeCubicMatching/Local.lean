import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.Clauses
import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Tree
import Holant.NetworkContraction


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
open Holant Holant.Complexity
open scoped BigOperators
namespace OldTree
export Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Tree
  (bit tri ternary Wire Valid weight localPartition local_partition_exact)
end OldTree

def ONE : Signature ℚ 3 := fun x =>
  if (OldTree.bit (x 0)+OldTree.bit (x 1)+OldTree.bit (x 2)==1) then 1 else 0
def TWO : Signature ℚ 3 := fun x => ONE (fun i => !x i)
def clause (side : Bool) : Signature ℚ 3 := if side then TWO else ONE
def arity (_ : ℕ) : ℕ := 3
def palette (i : Fin 2) : Signature ℚ (arity i.val) := if i.val=0 then ONE else TWO
def edge (_ : Fin 1) : Kernel ℚ := Signature.disequality

/-- Constructive Boolean table equals the existing mathematical ternary.
The explicit Boolean guard permits the low-degree kernel tables to reduce
without treating Classical.propDecidable as executable data. -/
theorem one_ternary (x : Fin 3 → Bool) : ONE x=OldTree.ternary x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    norm_num [ONE,OldTree.ternary,OldTree.tri,OldTree.bit,h0,h1,h2]

theorem clause_complement (x : Fin 3 → Bool) : TWO x=ONE (fun i => !x i) := rfl
theorem clause_gauge (side : Bool) (x : Fin 3 → Bool) :
    clause side (fun i => if side then !x i else x i)=ONE x := by
  cases side <;> simp [clause,TWO]

/-- All eight coefficients, including every zero word. The fourth tag of
the old definition is retained in this comparison. -/
theorem tagged_coefficients (side : Bool) (x : Fin 3 → Bool) :
    clause side x =
      if side then VerifierGates.twoClause (1 : ℚ) 1 1 ![x 0,x 1,x 2,false]
      else VerifierGates.oneClause (1 : ℚ) 1 1 ![x 0,x 1,x 2,true] := by
  cases side <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    norm_num [clause,ONE,TWO,OldTree.ternary,OldTree.tri,OldTree.bit,
      VerifierGates.oneClause,VerifierGates.twoClause,h0,h1,h2]

theorem edge_complement (a b : Bool) :
    (Signature.disequality a (!b) : ℚ)=Signature.equality a b := by
  cases a <;> cases b <;> norm_num [Signature.disequality,Signature.equality]
theorem edge_both_complement (a b : Bool) :
    (Signature.disequality (!a) (!b) : ℚ)=Signature.disequality a b := by
  cases a <;> cases b <;> norm_num [Signature.disequality]

def pin (selected : Bool) : Signature ℚ 1 := fun x => if x 0=selected then 1 else 0

/-- Ports 0,1 of the cubic vertex are the TWO occurrences of its native-X
self-loop. Port 2 is the sole boundary; no unary palette label is added. -/
def loopNetwork (selected : Bool) : Network ℚ 1 :=
  (Network.corolla (clause selected)).contract Signature.disequality

theorem loop_vertices (selected : Bool) : (loopNetwork selected).shape.vertices=1 := rfl
theorem loop_edges (selected : Bool) : (loopNetwork selected).shape.edges=1 := rfl
theorem loop_vertex (selected : Bool) (v : Fin (loopNetwork selected).shape.vertices) :
    (loopNetwork selected).vertex v=clause selected := rfl
theorem loop_edge (selected : Bool) (e : Fin (loopNetwork selected).shape.edges) :
    (loopNetwork selected).edge e=Signature.disequality := by
  fin_cases e
  rfl

/-- TWO produces 2·pin1; ONE produces 2·pin0. Both legal loop orientations
are counted, so the factor two is an actual extension multiplicity. -/
theorem loop_denote (selected : Bool) : (loopNetwork selected).denote=(2 : ℚ) • pin selected := by
  funext x
  rw [loopNetwork,Network.denote_contract,Network.denote_corolla,
    Signature.contract_disequality]
  have hword (a b : Bool) : Fin.cons a (Fin.cons b x)=![a,b,x 0] := by
    funext i
    fin_cases i <;> rfl
  rw [hword,hword]
  cases selected <;> cases hx : x 0 <;>
    norm_num [clause,ONE,TWO,OldTree.ternary,OldTree.tri,OldTree.bit,pin,
      Pi.smul_apply,smul_eq_mul,hx]

/-- The pad is joined by an ACTUAL native-X edge. A left ONE therefore
receives zero from a TWO self-loop, and a right TWO receives one from ONE. -/
def paddingWeight (side bit : Bool) : ℚ :=
  ∑ b : Bool,Signature.disequality bit b * (loopNetwork (!side)).denote (fun _ => b)
theorem padding_exact (side bit : Bool) :
    paddingWeight side bit=2*(if bit=side then (1 : ℚ) else 0) := by
  rw [paddingWeight]
  simp_rw [loop_denote]
  cases side <;> cases bit <;>
    norm_num [Fintype.sum_bool,pin,Pi.smul_apply,smul_eq_mul,Signature.disequality]

def normalizedWord (side : Bool) (w : List Bool) : List Bool :=
  w.map (fun b => if side then !b else b)
def indicator (side : Bool) (w : List Bool) : ℚ :=
  if (normalizedWord side w).count true=1 then 1 else 0

/-- Padding slots are APPENDED after the original ordered occurrences.
Their bit is side, hence becomes false in the same normalized coordinates. -/
theorem padding_indicator (side : Bool) (w : List Bool) (p : ℕ) :
    indicator side (w++List.replicate p side)=indicator side w := by
  cases side <;>
    simp [indicator,normalizedWord,List.map_append,List.map_replicate,List.count_append,List.count_replicate]

theorem clause_indicator (side : Bool) (x : Fin 3 → Bool) :
    clause side x=indicator side (List.ofFn x) := by
  cases side <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    norm_num [clause,ONE,TWO,OldTree.ternary,OldTree.tri,OldTree.bit,indicator,
      normalizedWord,List.ofFn_succ,h0,h1,h2]

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
