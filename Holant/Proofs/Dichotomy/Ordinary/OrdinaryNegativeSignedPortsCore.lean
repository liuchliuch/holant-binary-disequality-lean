import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingCore

/-! Literal arbitrary signed port substitution. A complemented port uses one
actual X vertex and one fresh private wire. Unused private wires are guarded
by two pins. No parity, negation, or compressed row is treated as a free gate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedPortsCore
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue (coefficient)
end B
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n m : ℕ}
abbrev Port (m : ℕ) := Bool ⊕ (Fin m×Bool)
def arity (n j : ℕ) : ℕ := if j=0 then n else if j=1 then 2 else 1

def external (j : Fin m) : Fin (m+n) := Fin.castAdd n j
def privatePort (i : Fin n) : Fin (m+n) := Fin.natAdd m i

def word (p : Fin n→Port m) (z : Fin m→Bool) (i : Fin n) : Bool :=
  match p i with
  | .inl b=>b
  | .inr (j,s)=>s ^^ z j

def rowPorts (p : Fin n→Port m) (i : Fin n) : Bool ⊕ Fin (m+n) :=
  match p i with
  | .inl b=>.inl b
  | .inr (j,s)=>.inr (if s then privatePort i else external j)

def pinNode (b : Bool) (q : Bool ⊕ Fin (m+n)) :
    Node (u:=1) (s:=4) (a:=fun _=>m+n) (b:=arity n) 0 :=
  if b then ⟨3,fun _=>q⟩ else ⟨2,fun _=>q⟩

def privateRows (p : Fin n→Port m) (i : Fin n) :
    List (Node (u:=1) (s:=4) (a:=fun _=>m+n) (b:=arity n) 0) :=
  match p i with
  | .inr (j,true)=>[⟨1,![.inr (privatePort i),.inr (external j)]⟩]
  | _=>[pinNode false (.inr (privatePort i)),pinNode false (.inr (privatePort i))]

def fixedRows (p : Fin n→Port m) (i : Fin n) :
    List (Node (u:=1) (s:=4) (a:=fun _=>m+n) (b:=arity n) 0) :=
  match p i with
  | .inl b=>[pinNode b (.inl b)]
  | _=>[]

def recipe (p : Fin n→Port m) : Recipe (u:=1) (s:=4) (a:=fun _=>m+n) (b:=arity n) :=
  fun _=>⟨0,rowPorts p⟩::(List.ofFn (privateRows p)).flatten++(List.ofFn (fixedRows p)).flatten

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
    (node : Node (u:=1) (s:=4) (a:=fun _=>m+n) (b:=arity n) 0)
    (w : Fin (m+n)→Bool) : K := table f node.1 (T.substitute node.2 w)

theorem pinNode_value (f : Signature K n) (b : Bool) (q : Bool ⊕ Fin (m+n))
    (w : Fin (m+n)→Bool) :
    rowValue f (pinNode b q) w=if Sum.elim id w q=b then 1 else 0 := by
  cases b <;> cases q <;> rfl

def privateFactor (p : Fin n→Port m) (w : Fin (m+n)→Bool) (i : Fin n) : K :=
  match p i with
  | .inr (j,true)=>Signature.disequality (w (privatePort i)) (w (external j))
  | _=>(if w (privatePort i)=false then 1 else 0)^2

theorem coefficient_value (f : Signature K n) (p : Fin n→Port m) (w : Fin (m+n)→Bool) :
    coefficient (table f) (recipe p) 0 w=
      f (T.substitute (rowPorts p) w)*∏i,privateFactor p w i := by
  simp only [coefficient,B.coefficient,recipe,List.map_append,List.prod_append,
    List.map_cons,List.prod_cons,List.map_flatten,List.prod_flatten,
    List.map_ofFn,List.prod_ofFn]
  change (f (T.substitute (rowPorts p) w)*
    ∏i,((privateRows p i).map (fun node=>rowValue f node w)).prod)*
    (∏i,((fixedRows p i).map (fun node=>rowValue f node w)).prod)=_
  have hp (i : Fin n) : ((privateRows p i).map (fun node=>rowValue f node w)).prod=privateFactor p w i := by
    cases h : p i with
    | inl b=>cases hw : w (privatePort i) <;> simp [privateRows,privateFactor,h,rowValue,table,pinNode,pin,T.substitute,pow_two,hw]
    | inr q=>rcases q with ⟨j,s⟩;cases s <;> cases hw : w (privatePort i) <;>
        simp [privateRows,privateFactor,h,rowValue,table,pinNode,pin,T.substitute,pow_two,hw]
  have hf (i : Fin n) : ((fixedRows p i).map (fun node=>rowValue f node w)).prod=1 := by
    cases h : p i with
    | inl b=>simp only [fixedRows,h,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,pinNode_value];simp
    | inr q=>simp [fixedRows,h]
  simp_rw [hp,hf]
  simp

def privateAssignment (p : Fin n→Port m) (z : Fin m→Bool) (i : Fin n) : Bool :=
  match p i with
  | .inr (j,true)=>!(z j)
  | _=>false

theorem private_factor (p : Fin n→Port m) (z : Fin m→Bool) (y : Fin n→Bool) (i : Fin n) :
    privateFactor (K:=K) p (Fin.addCases z y) i=
      if y i=privateAssignment p z i then 1 else 0 := by
  cases h : p i with
  | inl b=>cases hy : y i <;>
      simp [privateFactor,privateAssignment,h,privatePort,Fin.addCases_right,hy]
  | inr q=>
      rcases q with ⟨j,s⟩
      cases s <;> cases hy : y i <;> cases hz : z j <;>
        simp [privateFactor,privateAssignment,h,privatePort,external,Fin.addCases_left,
          Fin.addCases_right,hy,hz,Signature.disequality]

theorem original_word (p : Fin n→Port m) (z : Fin m→Bool) :
    T.substitute (rowPorts p) (Fin.addCases z (privateAssignment p z))=word p z := by
  funext i
  cases h : p i with
  | inl b=>simp [rowPorts,T.substitute,word,h]
  | inr q=>
      rcases q with ⟨j,s⟩
      cases s <;> cases hz : z j <;>
        simp [rowPorts,T.substitute,privatePort,external,privateAssignment,word,h,hz]

def trace (f : Signature K n) (p : Fin n→Port m) : Signature K m := fun z=>
  ∑y : Fin n→Bool,coefficient (table f) (recipe p) 0 (Fin.addCases z y)

/-- The complete private sum is exactly the original unsquared coefficient. -/
theorem trace_value (f : Signature K n) (p : Fin n→Port m) (z : Fin m→Bool) :
    trace f p z=f (word p z) := by
  classical
  unfold trace
  simp_rw [coefficient_value,private_factor]
  have prod (y : Fin n→Bool) :
      (∏i,if y i=privateAssignment p z i then (1:K) else 0)=
        if y=privateAssignment p z then 1 else 0 := by
    rw [Fintype.prod_boole]
    simp only [funext_iff]
    by_cases he : ∀i,y i=privateAssignment p z i <;> simp [he]
  simp_rw [prod]
  rw [Finset.sum_eq_single (privateAssignment p z)]
  · rw [ite_eq_left rfl,mul_one,original_word]
  · intro y _ hy
    simp [hy]
  · simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedPortsCore
end
