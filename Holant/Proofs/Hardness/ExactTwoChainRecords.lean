import Holant.Proofs.Hardness.ExactTwoChainTemplate
import Mathlib.Data.List.OfFn

/-! Table-free ordered records of the actual two-edge chains. New edge IDs0,1
are the last interface, and every old edge is shifted by2. The physical row
provider will emit these records from variable unary length k. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainRecords
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export ExactTwoChain (q series joinOrder network spectral)
end C
namespace T
export ExactTwoChainTemplate (shapeTemplate compile valid denote)
end T
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex enumerate template_denote_heq)
end Chain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384

def extendEndpoint : LocalEndpoint → LocalEndpoint
  | .inl i=>if i=0 then .inl 0 else if i=2 then .inl 2 else if i=1 then .inr (1,false) else .inr (0,false)
  | .inr p=>.inr (p.1+2,p.2)
def extendRow (r : LocalVertex) : LocalVertex := (r.1,r.2.map extendEndpoint)

def explicitRow (label k i : ℕ) : LocalVertex :=
  (label,[if i=0 then .inl 0 else .inr (2*(k-i)+1,true),
    if i=k then .inl 1 else .inr (2*(k-1-i)+1,false),
    if i=0 then .inl 2 else .inr (2*(k-i),true),
    if i=k then .inl 3 else .inr (2*(k-1-i),false)])

def explicitTemplate (label edge k : ℕ) : Template where
  boundary:=4
  vertices:=(List.range (k+1)).map (explicitRow label k)
  edges:=List.replicate (2*k) edge

theorem vertices_length (label edge k : ℕ) : (explicitTemplate label edge k).vertices.length=k+1 := by
  simp [explicitTemplate]
theorem edges_length (label edge k : ℕ) : (explicitTemplate label edge k).edges.length=2*k := by
  simp [explicitTemplate]

theorem extend_explicitRow (label k i : ℕ) (hi : i≤k) :
    extendRow (explicitRow label k i)=explicitRow label (k+1) i := by
  by_cases h0 : i=0
  · subst i
    by_cases hk : k=0
    · subst k; rfl
    · simp [extendRow,explicitRow,extendEndpoint,hk,Ne.symm hk]
      omega
  · have hs : i≠k+1 := by omega
    by_cases hik : i=k
    · subst i
      simp [extendRow,explicitRow,extendEndpoint,h0]
    · simp [extendRow,explicitRow,extendEndpoint,h0,hik,hs]
      omega

theorem explicit_vertices_succ (label edge k : ℕ) :
    (explicitTemplate label edge (k+1)).vertices=
      (explicitTemplate label edge k).vertices.map extendRow ++
        [(label,[.inr (1,true),.inl 1,.inr (0,true),.inl 3])] := by
  unfold explicitTemplate
  rw [List.range_succ]
  simp only [List.map_append,List.map_cons,List.map_nil,List.map_map]
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro i hi
    exact (extend_explicitRow label k i (Nat.lt_succ_iff.mp (List.mem_range.mp hi))).symm
  · simp [explicitRow]

def appendRoute (e : ℕ) (p : Fin 4 ⊕ (Fin e × Bool)) : Fin 4 ⊕ (Fin (e+2) × Bool) :=
  (Network.contractPorts (e+0+1) 4) ((Network.contractPorts (e+0) 6)
    ((Equiv.sumCongr C.joinOrder (Equiv.refl _))
      ((Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr (finSumFinEquiv : (Fin e ⊕ Fin 0) ≃ Fin (e+0)) (Equiv.refl Bool)))
          (Network.tensorPorts (Fin e) (Fin 0) 4 4 (.inl p)))))

theorem appendRoute_embed (e : ℕ) (p : Fin 4 ⊕ (Fin e × Bool)) :
    Template.embed 4 (e+2) (appendRoute e p)=extendEndpoint (Template.embed 4 e p) := by
  cases p with
  | inl i=>fin_cases i <;> rfl
  | inr p=>rfl

theorem compile_vertices_succ (label edge k : ℕ) :
    (T.compile label edge (k+1)).vertices=(T.compile label edge k).vertices.map extendRow ++
      [(label,[.inr (1,true),.inl 1,.inr (0,true),.inl 3])] := by
  change (T.shapeTemplate (C.series (C.network (K:=ℚ) k) (Network.corolla C.q)).shape label edge).vertices=_
  simp only [T.shapeTemplate,C.series,Network.contract,Chain.reindex,Chain.tensor,Chain.enumerate,
    Network.tensorFinite,Network.corolla]
  rw [List.ofFn_add]
  simp only [List.ofFn_succ,List.ofFn_zero,List.map_ofFn,List.append_nil]
  congr 1
  · simp only [T.compile,T.shapeTemplate,List.map_ofFn,extendRow]
    apply congrArg List.ofFn
    funext v
    have hv : Fin.castLE (Nat.le_add_right (C.network (K:=ℚ) k).shape.vertices 1) v=Fin.castAdd 1 v := rfl
    simp only [Equiv.trans_apply,Equiv.sigmaCongrLeft_apply,Fin.cast]
    generalize hq : finSumFinEquiv.symm
      (Fin.castLE (Nat.le_add_right (C.network (K:=ℚ) k).shape.vertices 1) v)=r
    have hqv : r=Sum.inl v := by rw [←hq,hv]; exact finSumFinEquiv_symm_apply_castAdd v
    cases hqv
    change (label,List.ofFn _)=(label,
      (List.ofFn fun i : Fin ((C.network (K:=ℚ) k).shape.arity v)=>
        Labelling.localEndpoint ((C.network (K:=ℚ) k).shape.ports ⟨v,i⟩)).map extendEndpoint)
    rw [List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    change Template.embed 4 ((C.network (K:=ℚ) k).shape.edges+2)
      (appendRoute _ ((C.network (K:=ℚ) k).shape.ports ⟨v,i⟩))=
        extendEndpoint (Template.embed 4 _ ((C.network (K:=ℚ) k).shape.ports ⟨v,i⟩))
    exact appendRoute_embed _ _
  · simp only [Equiv.trans_apply,Equiv.sigmaCongrLeft_apply,Fin.cast]
    generalize hq : finSumFinEquiv.symm (Fin.natAdd (C.network (K:=ℚ) k).shape.vertices (0 : Fin 1))=r
    have hqv : r=Sum.inr 0 := by rw [←hq]; exact finSumFinEquiv_symm_apply_natAdd 0
    cases hqv
    rfl

theorem compile_vertices (label edge k : ℕ) :
    (T.compile label edge k).vertices=(explicitTemplate label edge k).vertices := by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [compile_vertices_succ,explicit_vertices_succ,ih]

theorem compile_eq (label edge k : ℕ) : T.compile label edge k=explicitTemplate label edge k := by
  apply congrArg₂ (fun vs es=>(⟨4,vs,es⟩ : Template)) (compile_vertices label edge k)
  change List.replicate (C.network (K:=ℚ) k).shape.edges edge=List.replicate (2*k) edge
  rw [(ExactTwoChain.network_counts (K:=ℚ) k).2]

variable {K : Type*} [Field K] {s b : ℕ} (a : ℕ → ℕ)
variable (label : Fin s) (hlabel : a label.val=4) (edge : Fin b)

include hlabel in
theorem valid (k : ℕ) : (explicitTemplate label.val edge.val k).WellFormed s b a := by
  rw [←compile_eq]
  exact T.valid a label hlabel edge k

theorem denote (k : ℕ) (G : (i : Fin s) → Signature K (a i.val)) (X : Fin b → Kernel K)
    (hq : (⟨a label.val,G label⟩ : AnySignature K)=⟨4,C.q⟩) (hX : X edge=Signature.disequality) :
    ((explicitTemplate label.val edge.val k).network (valid a label hlabel edge k) G X).denote=
      C.spectral ((2 : K)^k) := by
  have he := Chain.template_denote_heq _ _ (valid a label hlabel edge k) (T.valid a label hlabel edge k)
    (compile_eq label.val edge.val k).symm G X
  exact (eq_of_heq he).trans (T.denote a label hlabel edge k G X hq hX)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainRecords
