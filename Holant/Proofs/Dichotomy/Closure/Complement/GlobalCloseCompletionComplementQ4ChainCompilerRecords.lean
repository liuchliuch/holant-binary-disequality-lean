import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerNetwork
import Mathlib.Data.List.OfFn

/-! Literal four-port records for the recursive positive chain. The two
newest X edges have IDs 1 and 0, while every old edge ID increases by two. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerRecords
open Holant Holant.Complexity FixedGadgetSubstitution
namespace N
export GlobalCloseCompletionComplementQ4ChainCompilerNetwork
  (literal shapeTemplate compile valid template_value)
end N
namespace G
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork (connect order)
end G
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex enumerate)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false

def extendEndpoint : LocalEndpoint→LocalEndpoint
  | .inl i=>if i<2 then .inl i else .inr (3-i,false)
  | .inr p=>.inr (p.1+2,p.2)
def extendRow (row : LocalVertex) : LocalVertex:=(row.1,row.2.map extendEndpoint)
def incoming (k i : ℕ) (channel : Bool) : LocalEndpoint:=
  if i=0 then .inl (if channel then 1 else 0)
  else .inr (2*(k-i)+(if channel then 0 else 1),true)
def outgoing (k i : ℕ) (channel : Bool) : LocalEndpoint:=
  if i=k then .inl (if channel then 3 else 2)
  else .inr (2*(k-1-i)+(if channel then 0 else 1),false)
def explicitRow (label k i : ℕ) : LocalVertex :=
  (label,if i=0 then [incoming k i false,incoming k i true,outgoing k i false,outgoing k i true]
    else [outgoing k i false,outgoing k i true,incoming k i false,incoming k i true])
def explicitTemplate (label edge k : ℕ) : Template where
  boundary:=4
  vertices:=(List.range (k+1)).map (explicitRow label k)
  edges:=List.replicate (2*k) edge

@[simp] theorem explicit_vertices (label edge k : ℕ) : (explicitTemplate label edge k).vertices.length=k+1 := by
  simp [explicitTemplate]
@[simp] theorem explicit_edges (label edge k : ℕ) : (explicitTemplate label edge k).edges.length=2*k := by
  simp [explicitTemplate]

theorem extend_incoming (k i : ℕ) (hi : i≤k) (c : Bool) :
    extendEndpoint (incoming k i c)=incoming (k+1) i c := by
  by_cases hz : i=0
  · subst i;cases c <;> rfl
  · cases c <;> simp [incoming,extendEndpoint,hz] <;> omega

theorem extend_outgoing (k i : ℕ) (hi : i≤k) (c : Bool) :
    extendEndpoint (outgoing k i c)=outgoing (k+1) i c := by
  have hn : i≠k+1:=by omega
  by_cases he : i=k
  · subst i;cases c <;> simp [outgoing,extendEndpoint]
  · cases c <;> simp [outgoing,extendEndpoint,he,hn] <;> omega

theorem extend_explicit (label k i : ℕ) (hi : i≤k) :
    extendRow (explicitRow label k i)=explicitRow label (k+1) i := by
  unfold extendRow explicitRow
  split_ifs <;> simp only [List.map_cons,List.map_nil,extend_incoming k i hi,extend_outgoing k i hi]

theorem explicit_succ (label edge k : ℕ) :
    (explicitTemplate label edge (k+1)).vertices=
      (explicitTemplate label edge k).vertices.map extendRow++
        [(label,[.inl 2,.inl 3,.inr (1,true),.inr (0,true)])] := by
  unfold explicitTemplate
  rw [List.range_succ]
  simp only [List.map_append,List.map_cons,List.map_nil,List.map_map]
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro i hi
    exact (extend_explicit label k i (Nat.lt_succ_iff.mp (List.mem_range.mp hi))).symm
  · simp [explicitRow,incoming,outgoing]

def appendRoute (e : ℕ) (p : Fin 4⊕(Fin e×Bool)) : Fin 4⊕(Fin (e+2)×Bool) :=
  (Network.contractPorts (e+0+1) 4) ((Network.contractPorts (e+0) 6)
    ((Equiv.sumCongr (G.order false) (Equiv.refl _))
      ((Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr (finSumFinEquiv : (Fin e⊕Fin 0)≃Fin (e+0)) (Equiv.refl Bool)))
          (Network.tensorPorts (Fin e) (Fin 0) 4 4 (.inl p)))))

theorem append_embed (e : ℕ) (p : Fin 4⊕(Fin e×Bool)) :
    Template.embed 4 (e+2) (appendRoute e p)=extendEndpoint (Template.embed 4 e p) := by
  cases p with
  | inl i=>fin_cases i <;> rfl
  | inr p=>rfl

theorem compile_succ (label edge k : ℕ) :
    (N.compile label edge (k+1)).vertices=
      (N.compile label edge k).vertices.map extendRow++
        [(label,[.inl 2,.inl 3,.inr (1,true),.inr (0,true)])] := by
  change (N.shapeTemplate (G.connect (N.literal (K:=ℚ) 0 k)
    (Network.corolla 0) false).shape label edge).vertices=_
  simp only [N.shapeTemplate,G.connect,Network.contract,C.reindex,C.tensor,C.enumerate,
    Network.tensorFinite,Network.corolla]
  rw [List.ofFn_add]
  simp only [List.ofFn_succ,List.ofFn_zero,List.map_ofFn,List.append_nil]
  congr 1
  · simp only [N.compile,N.shapeTemplate,List.map_ofFn,extendRow]
    apply congrArg List.ofFn
    funext v
    have hv : Fin.castLE (Nat.le_add_right (N.literal (K:=ℚ) 0 k).shape.vertices 1) v=Fin.castAdd 1 v:=rfl
    simp only [Equiv.trans_apply,Equiv.sigmaCongrLeft_apply,Fin.cast]
    generalize hq : finSumFinEquiv.symm
      (Fin.castLE (Nat.le_add_right (N.literal (K:=ℚ) 0 k).shape.vertices 1) v)=q
    have hqv : q=Sum.inl v := by rw [←hq,hv];exact finSumFinEquiv_symm_apply_castAdd v
    cases hqv
    change (label,List.ofFn _)=(label,
      (List.ofFn fun i : Fin ((N.literal (K:=ℚ) 0 k).shape.arity v)=>
        Labelling.localEndpoint ((N.literal (K:=ℚ) 0 k).shape.ports ⟨v,i⟩)).map extendEndpoint)
    rw [List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    change Template.embed 4 ((N.literal (K:=ℚ) 0 k).shape.edges+2)
      (appendRoute _ ((N.literal (K:=ℚ) 0 k).shape.ports ⟨v,i⟩))=
        extendEndpoint (Template.embed 4 _ ((N.literal (K:=ℚ) 0 k).shape.ports ⟨v,i⟩))
    exact append_embed _ _
  · simp only [Equiv.trans_apply,Equiv.sigmaCongrLeft_apply,Fin.cast]
    generalize hq : finSumFinEquiv.symm
      (Fin.natAdd (N.literal (K:=ℚ) 0 k).shape.vertices (0 : Fin 1))=q
    have hqv : q=Sum.inr 0 := by rw [←hq];exact finSumFinEquiv_symm_apply_natAdd 0
    cases hqv
    rfl

theorem compile_vertices (label edge k : ℕ) :
    (N.compile label edge k).vertices=(explicitTemplate label edge k).vertices := by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [compile_succ,explicit_succ,ih]

theorem compile_eq (label edge k : ℕ) : N.compile label edge k=explicitTemplate label edge k := by
  exact congrArg₂ (fun vs es=>(⟨4,vs,es⟩ : Template)) (compile_vertices label edge k)
    (by simp [N.compile,N.shapeTemplate,explicitTemplate])

theorem valid {s b : ℕ} (a : ℕ→ℕ) (label : Fin s) (hl : a label.val=4) (edge : Fin b) (k : ℕ) :
    (explicitTemplate label.val edge.val k).WellFormed s b a := by
  rw [←compile_eq]
  exact N.valid a label hl edge k


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerRecords
end
