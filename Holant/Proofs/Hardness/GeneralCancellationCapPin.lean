import Holant.Proofs.Hardness.SparseDirectPin

/-!
# Six literal original-M caps, with both external orientations

Cap indices 0,...,5 name original loops 01,02,03,12,13,23. The false
orientation keeps the two remaining ORIGINAL ports in increasing order; true
reverses this boundary. Reindexing acts on the original corolla network, never
on its vertex signature. Every cap has one label-0 original M and one native
edge-0 X. Its finite coefficient table is proved from Network.denote.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCancellationCapPin
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end Chain
variable {K : Type*} [Field K]

abbrev Choice := Fin 6 × Bool

def portOrder (c : Fin 6) (rev : Bool) : Equiv.Perm (Fin 4) where
  toFun := if rev then
    ![![0,1,3,2],![0,3,1,2],![0,3,2,1],![3,0,1,2],![3,0,2,1],![3,2,0,1]] c
    else ![![0,1,2,3],![0,2,1,3],![0,2,3,1],![2,0,1,3],![2,0,3,1],![2,3,0,1]] c
  invFun := if rev then
    ![![0,1,3,2],![0,2,3,1],![0,3,2,1],![1,2,3,0],![1,3,2,0],![2,3,1,0]] c
    else ![![0,1,2,3],![0,2,1,3],![0,3,1,2],![1,2,0,3],![1,3,0,2],![2,3,0,1]] c
  left_inv := by fin_cases c <;> cases rev <;> decide
  right_inv := by fin_cases c <;> cases rev <;> decide

def network (M : Signature K 4) (k : Choice) : Network K 2 :=
  (Chain.reindex (Network.corolla M) (portOrder k.1 k.2)).contract Signature.disequality

abbrev delta : Signature K 2 := SparseDirectPin.delta

def antiTensor (p q : K) : Signature K 2 := fun x=>
  if x 0 then (if x 1 then 0 else q) else (if x 1 then p else 0)

/-- The literal unordered-loop table, oriented by increasing remaining ports. -/
def coefficients (M : Signature K 4) (c : Fin 6) : K × K :=
  let e := entries M
  ![(e.c+e.w,e.d+e.z),(e.b+e.w,e.d+e.y),(e.b+e.z,e.c+e.y),
    (e.b+e.c,e.z+e.y),(e.b+e.d,e.w+e.y),(e.c+e.d,e.w+e.z)] c

def oriented (M : Signature K 4) (k : Choice) : K × K :=
  if k.2 then (coefficients M k.1).swap else coefficients M k.1

/-- No gadget, evaluator, scalar-success or spectral hypothesis is input. -/
def Applicable (M : Signature K 4) : Prop :=
  ∃ k : Choice, (oriented M k).1≠0 ∧ (oriented M k).2=0

def selected (M : Signature K 4) : Choice := by
  classical
  exact if h : Applicable M then Classical.choose h else (0,false)

theorem selected_spec (M : Signature K 4) (h : Applicable M) :
    (oriented M (selected M)).1≠0 ∧ (oriented M (selected M)).2=0 := by
  classical
  simp only [selected,dite_eq_left h]
  exact Classical.choose_spec h

/-- Actual disequality contraction, with original port identities retained. -/
theorem contraction (M : Signature K 4) (k : Choice) (t : Fin 2 → Bool) :
    (network M k).denote t=
      M (fun i=>(Fin.cons false (Fin.cons true t) : Fin 4→Bool) (portOrder k.1 k.2 i))+
      M (fun i=>(Fin.cons true (Fin.cons false t) : Fin 4→Bool) (portOrder k.1 k.2 i)) := by
  rw [network,Network.denote_contract,Chain.reindex_denote,Network.denote_corolla,
    Signature.contract_disequality]
  rfl

/-- All twelve oriented cap tables, proved from the real network denotation. -/
theorem full_table (M : Signature K 4) (hM : EvenSupport M) (k : Choice) :
    (network M k).denote=antiTensor (oriented M k).1 (oriented M k).2 := by
  funext t
  have hw (a b : Bool) : (Fin.cons a (Fin.cons b t) : Fin 4→Bool)=![a,b,t 0,t 1] := by
    funext i
    fin_cases i <;> rfl
  rw [contraction,hw,hw,←table_entries M hM]
  rcases k with ⟨c,rev⟩
  fin_cases c <;> cases rev <;> cases h0 : t 0 <;> cases h1 : t 1 <;>
    simp [portOrder,coefficients,oriented,entries,table,antiTensor,h0,h1]

theorem boundary_swap (M : Signature K 4) (hM : EvenSupport M) (c : Fin 6)
    (t : Fin 2→Bool) :
    (network M (c,true)).denote t=(network M (c,false)).denote ![t 1,t 0] := by
  rw [full_table M hM,full_table M hM]
  cases h0 : t 0 <;> cases h1 : t 1 <;> simp [oriented,antiTensor,h0,h1]

theorem denote (M : Signature K 4) (hM : EvenSupport M) (k : Choice)
    (hz : (oriented M k).2=0) :
    (network M k).denote=(oriented M k).1 • delta := by
  rw [full_table M hM]
  funext t
  cases h0 : t 0 <;> cases h1 : t 1 <;>
    simp [antiTensor,delta,SparseDirectPin.delta,h0,h1,hz,Pi.smul_apply,smul_eq_mul]

def labels (M : Signature K 4) (k : Choice) : Labelling (network M k).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity _ := rfl
  edge _ := 0

abbrev template (M : Signature K 4) (k : Choice) := (labels M k).template

theorem valid (M : Signature K 4) (k : Choice) :
    (template M k).WellFormed 1 1 (fun _=>4) := (labels M k).wellFormed

/-- Original-port rows: native loop endpoints are false/true, and the remaining
ports keep their ordered external indices. There is exactly one original label. -/
def ports (k : Choice) : List (ℕ ⊕ (ℕ × Bool)) :=
  if k.2 then
    ![[.inr (0,false),.inr (0,true),.inl 1,.inl 0],
      [.inr (0,false),.inl 1,.inr (0,true),.inl 0],
      [.inr (0,false),.inl 1,.inl 0,.inr (0,true)],
      [.inl 1,.inr (0,false),.inr (0,true),.inl 0],
      [.inl 1,.inr (0,false),.inl 0,.inr (0,true)],
      [.inl 1,.inl 0,.inr (0,false),.inr (0,true)]] k.1
  else
    ![[.inr (0,false),.inr (0,true),.inl 0,.inl 1],
      [.inr (0,false),.inl 0,.inr (0,true),.inl 1],
      [.inr (0,false),.inl 0,.inl 1,.inr (0,true)],
      [.inl 0,.inr (0,false),.inr (0,true),.inl 1],
      [.inl 0,.inr (0,false),.inl 1,.inr (0,true)],
      [.inl 0,.inl 1,.inr (0,false),.inr (0,true)]] k.1

theorem records (M : Signature K 4) (k : Choice) :
    (template M k).boundary=2 ∧ (template M k).vertices=[(0,ports k)] ∧
      (template M k).edges=[0] := by
  rcases k with ⟨c,rev⟩
  fin_cases c <;> cases rev <;> exact ⟨rfl,rfl,rfl⟩

theorem literal_vertex (M : Signature K 4) (k : Choice)
    (v : Fin (network M k).shape.vertices) : (network M k).vertex v=M := rfl

theorem template_actual (M : Signature K 4) (k : Choice) :
    ((template M k).network (valid M k) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=(network M k).denote := by
  apply Labelling.denote_template_of_labels (labels M k) _ _ (network M k).vertex (network M k).edge
  · intro v x; rfl
  · intro e a b; fin_cases e; rfl

theorem template_denote (M : Signature K 4) (hM : EvenSupport M) (k : Choice)
    (hz : (oriented M k).2=0) :
    ((template M k).network (valid M k) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=(oriented M k).1 • delta := by
  rw [template_actual]
  exact denote M hM k hz

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCancellationCapPin
