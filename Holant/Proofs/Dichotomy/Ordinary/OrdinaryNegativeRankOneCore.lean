import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingCore

/-! Actual two-point restriction using one unchanged original row, literal X,
and both pins. There is no affine-support or rank-one premise on the row. All
private coordinates are guarded or tied by a real X vertex, and each fixed
original port is balanced by one literal pin. External incidence is exactly
the Hamming distance of the two selected original words. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneCore
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue (coefficient)
end B
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences (count_ofFn)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
variable {n : ℕ}

def arity (n j : ℕ) : ℕ := if j=0 then n else if j=1 then 2 else 1

def external : Fin (1+n) := Fin.castAdd n (0 : Fin 1)
def privatePort (i : Fin n) : Fin (1+n) := Fin.natAdd 1 i

def neg (s t : Fin n→Bool) (i : Fin n) : Bool := s i && !(t i)
def rowPorts (s t : Fin n→Bool) (i : Fin n) : Bool ⊕ Fin (1+n) :=
  if s i=t i then .inl (s i) else if s i then .inr (privatePort i) else .inr external

def pinNode (b : Bool) (p : Bool ⊕ Fin (1+n)) :
    Node (u:=1) (s:=4) (a:=fun _=>1+n) (b:=arity n) 0 :=
  if b then ⟨3,fun _=>p⟩ else ⟨2,fun _=>p⟩

def privateRows (s t : Fin n→Bool) (i : Fin n) :
    List (Node (u:=1) (s:=4) (a:=fun _=>1+n) (b:=arity n) 0) :=
  if neg s t i then [⟨1,![.inr (privatePort i),.inr external]⟩]
  else [pinNode false (.inr (privatePort i)),pinNode false (.inr (privatePort i))]

def fixedRows (s t : Fin n→Bool) (i : Fin n) :
    List (Node (u:=1) (s:=4) (a:=fun _=>1+n) (b:=arity n) 0) :=
  if s i=t i then [pinNode (s i) (.inl (s i))] else []

def recipe (s t : Fin n→Bool) : Recipe (u:=1) (s:=4) (a:=fun _=>1+n) (b:=arity n) :=
  fun _=>⟨0,rowPorts s t⟩::(List.ofFn (privateRows s t)).flatten++(List.ofFn (fixedRows s t)).flatten

variable {K : Type} [CommSemiring K]
def pin (b : Bool) : Signature K 1 := fun x=>if x 0=b then 1 else 0

def table (f : Signature K n) (j : Fin 4) : Signature K (arity n j.val) :=
  match j with
  | ⟨0,_⟩=>f
  | ⟨1,_⟩=>fun (x : Fin 2→Bool)=>Signature.disequality (x 0) (x 1)
  | ⟨2,_⟩=>pin false
  | ⟨3,_⟩=>pin true
  | ⟨j+4,h⟩=>False.elim (by omega)

def rowValue (f : Signature K n)
    (node : Node (u:=1) (s:=4) (a:=fun _=>1+n) (b:=arity n) 0)
    (w : Fin (1+n)→Bool) : K := table f node.1 (T.substitute node.2 w)

theorem pinNode_value (f : Signature K n) (b : Bool) (p : Bool ⊕ Fin (1+n))
    (w : Fin (1+n)→Bool) :
    rowValue f (pinNode b p) w=if Sum.elim id w p=b then 1 else 0 := by
  cases b <;> cases p <;> rfl

theorem coefficient_value (f : Signature K n) (s t : Fin n→Bool) (w : Fin (1+n)→Bool) :
    coefficient (table f) (recipe s t) 0 w=
      f (T.substitute (rowPorts s t) w)*
        ∏i,if neg s t i then Signature.disequality (w (privatePort i)) (w external)
          else (if w (privatePort i)=false then 1 else 0)^2 := by
  simp only [coefficient,B.coefficient,recipe,List.map_append,List.prod_append,
    List.map_cons,List.prod_cons,List.map_flatten,List.prod_flatten,
    List.map_ofFn,List.prod_ofFn]
  change (f (T.substitute (rowPorts s t) w)*
    ∏i,((privateRows s t i).map (fun node=>rowValue f node w)).prod)*
    (∏i,((fixedRows s t i).map (fun node=>rowValue f node w)).prod)=_
  have hp (i : Fin n) : ((privateRows s t i).map (fun node=>rowValue f node w)).prod=
      if neg s t i then Signature.disequality (w (privatePort i)) (w external)
      else (if w (privatePort i)=false then 1 else 0)^2 := by
    cases h : neg s t i <;> cases hw : w (privatePort i) <;>
      simp [privateRows,h,rowValue,table,pinNode,pin,T.substitute,pow_two,hw]
  have hf (i : Fin n) : ((fixedRows s t i).map (fun node=>rowValue f node w)).prod=1 := by
    by_cases h : s i=t i
    · simp only [fixedRows,ite_eq_left h,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,pinNode_value]
      simp
    · simp [fixedRows,h]
  simp_rw [hp,hf]
  simp

def privateAssignment (s t : Fin n→Bool) (z : Bool) (i : Fin n) : Bool :=
  if neg s t i then !z else false

theorem private_factor (s t : Fin n→Bool) (z : Fin 1→Bool) (y : Fin n→Bool) (i : Fin n) :
    (if neg s t i then Signature.disequality (K:=K) (Fin.addCases z y (privatePort i))
      (Fin.addCases z y external) else (if Fin.addCases z y (privatePort i)=false then 1 else 0)^2)=
    if y i=privateAssignment s t (z 0) i then 1 else 0 := by
  simp only [privatePort,external,Fin.addCases_left,Fin.addCases_right,privateAssignment]
  by_cases hn : neg s t i=true
  · simp only [hn,ite_true]
    cases hy : y i <;> cases hz : z 0 <;> simp [Signature.disequality]
  · simp only [hn]
    cases hy : y i <;> simp

theorem original_word (s t : Fin n→Bool) (z : Fin 1→Bool) :
    T.substitute (rowPorts s t) (Fin.addCases z (privateAssignment s t (z 0)))=
      if z 0 then t else s := by
  funext i
  cases hs : s i <;> cases ht : t i <;> cases hz : z 0 <;>
    simp [rowPorts,T.substitute,privatePort,external,privateAssignment,neg,hs,ht,hz]

def trace (f : Signature K n) (s t : Fin n→Bool) : Signature K 1 := fun z=>
  ∑y : Fin n→Bool,coefficient (table f) (recipe s t) 0 (Fin.addCases z y)

/-- A unique private assignment survives, so the two original coefficients
are retained exactly. Duplicate chosen words are permitted. -/
theorem trace_value (f : Signature K n) (s t : Fin n→Bool) (z : Fin 1→Bool) :
    trace f s t z=if z 0 then f t else f s := by
  classical
  unfold trace
  simp_rw [coefficient_value,private_factor]
  have prod (y : Fin n→Bool) :
      (∏i,if y i=privateAssignment s t (z 0) i then (1:K) else 0)=
        if y=privateAssignment s t (z 0) then 1 else 0 := by
    rw [Fintype.prod_boole]
    simp only [funext_iff]
    by_cases he : ∀i,y i=privateAssignment s t (z 0) i <;> simp [he]
  simp_rw [prod]
  rw [Finset.sum_eq_single (privateAssignment s t (z 0))]
  · rw [ite_eq_left rfl,mul_one,original_word]
    cases z 0 <;> rfl
  · intro y _ hy
    simp [hy]
  · simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneCore
end
