import Holant.Proofs.Hardness.PositiveDynamicStageRecords

/-! A literal recursive row emitter for fully inlined staged block chains.
Its records contain only the supplied original label and native-X edge label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicStageSeriesRecords
open Holant Holant.Complexity FixedGadgetSubstitution
namespace D
export PositiveDynamicStage (stage blockChain)
end D
namespace T
export ExactTwoChainTemplate (shapeTemplate)
end T
namespace R
export ExactTwoChainRecords (extendEndpoint extendRow)
end R
namespace DT
export PositiveDynamicStageTemplate (compile valid denote counts)
end DT
namespace DR
export PositiveDynamicStageRecords (singleBlock compile_singleBlock)
end DR
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (reindex tensor enumerate)
end Chain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type*} [Field K]

def rightEndpoint (offset : ℕ) : LocalEndpoint → LocalEndpoint
  | .inl i => if i=1 then .inl 1 else if i=3 then .inl 3 else if i=0 then .inr (1,true) else .inr (0,true)
  | .inr p => .inr (offset+p.1+2,p.2)

def rightRow (offset : ℕ) (r : LocalVertex) : LocalVertex := (r.1,r.2.map (rightEndpoint offset))

def join (edge : ℕ) (l r : Template) : Template where
  boundary := 4
  vertices := l.vertices.map R.extendRow ++ r.vertices.map (rightRow l.edges.length)
  edges := List.replicate (l.edges.length+r.edges.length+2) edge

def leftRoute (e f : ℕ) (p : Fin 4 ⊕ (Fin e × Bool)) : Fin 4 ⊕ (Fin (e+f+2) × Bool) :=
  (Network.contractPorts (e+f+1) 4) ((Network.contractPorts (e+f) 6)
    ((Equiv.sumCongr ExactTwoChain.joinOrder (Equiv.refl _))
      ((Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr (finSumFinEquiv : (Fin e ⊕ Fin f) ≃ Fin (e+f)) (Equiv.refl Bool)))
          (Network.tensorPorts (Fin e) (Fin f) 4 4 (.inl p)))))

def rightRoute (e f : ℕ) (p : Fin 4 ⊕ (Fin f × Bool)) : Fin 4 ⊕ (Fin (e+f+2) × Bool) :=
  (Network.contractPorts (e+f+1) 4) ((Network.contractPorts (e+f) 6)
    ((Equiv.sumCongr ExactTwoChain.joinOrder (Equiv.refl _))
      ((Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr (finSumFinEquiv : (Fin e ⊕ Fin f) ≃ Fin (e+f)) (Equiv.refl Bool)))
          (Network.tensorPorts (Fin e) (Fin f) 4 4 (.inr p)))))

theorem leftRoute_embed (e f : ℕ) (p : Fin 4 ⊕ (Fin e × Bool)) :
    Template.embed 4 (e+f+2) (leftRoute e f p)=R.extendEndpoint (Template.embed 4 e p) := by
  cases p with
  | inl i => fin_cases i <;> rfl
  | inr p => rfl

theorem rightRoute_embed (e f : ℕ) (p : Fin 4 ⊕ (Fin f × Bool)) :
    Template.embed 4 (e+f+2) (rightRoute e f p)=rightEndpoint e (Template.embed 4 f p) := by
  cases p with
  | inl i => fin_cases i <;> rfl
  | inr p => rfl

theorem shapeTemplate_series_vertices (N M : Network K 4) (label edge : ℕ) :
    (T.shapeTemplate (ExactTwoChain.series N M).shape label edge).vertices=
      (T.shapeTemplate N.shape label edge).vertices.map R.extendRow ++
        (T.shapeTemplate M.shape label edge).vertices.map (rightRow N.shape.edges) := by
  simp only [T.shapeTemplate,ExactTwoChain.series,Network.contract,Chain.reindex,Chain.tensor,
    Chain.enumerate,Network.tensorFinite]
  rw [List.ofFn_add]
  simp only [List.map_ofFn]
  congr 1
  · apply congrArg List.ofFn
    funext v
    have hv : Fin.castLE (Nat.le_add_right N.shape.vertices M.shape.vertices) v=Fin.castAdd M.shape.vertices v := rfl
    simp only [Equiv.trans_apply,Equiv.sigmaCongrLeft_apply,Fin.cast]
    generalize hq : finSumFinEquiv.symm
      (Fin.castLE (Nat.le_add_right N.shape.vertices M.shape.vertices) v)=r
    have hqv : r=Sum.inl v := by rw [←hq,hv]; exact finSumFinEquiv_symm_apply_castAdd v
    cases hqv
    change (label,List.ofFn _)=(label,
      (List.ofFn fun i : Fin (N.shape.arity v)=>Labelling.localEndpoint (N.shape.ports ⟨v,i⟩)).map R.extendEndpoint)
    rw [List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    exact leftRoute_embed _ _ (N.shape.ports ⟨v,i⟩)
  · apply congrArg List.ofFn
    funext v
    simp only [Equiv.trans_apply,Equiv.sigmaCongrLeft_apply,Fin.cast]
    generalize hq : finSumFinEquiv.symm (Fin.natAdd N.shape.vertices v)=r
    have hqv : r=Sum.inr v := by rw [←hq]; exact finSumFinEquiv_symm_apply_natAdd v
    cases hqv
    change (label,List.ofFn _)=(label,
      (List.ofFn fun i : Fin (M.shape.arity v)=>Labelling.localEndpoint (M.shape.ports ⟨v,i⟩)).map (rightEndpoint N.shape.edges))
    rw [List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    exact rightRoute_embed _ _ (M.shape.ports ⟨v,i⟩)

theorem shapeTemplate_series (N M : Network K 4) (label edge : ℕ) :
    T.shapeTemplate (ExactTwoChain.series N M).shape label edge=
      join edge (T.shapeTemplate N.shape label edge) (T.shapeTemplate M.shape label edge) := by
  apply congrArg₂ (fun vs es=>(⟨4,vs,es⟩ : Template))
  · simpa only [T.shapeTemplate,List.length_replicate] using shapeTemplate_series_vertices N M label edge
  · simp only [T.shapeTemplate,List.length_replicate]
    rfl

/-- Fully literal two-level block-chain emitter, before any bit-cost claim. -/
def records (label edge n : ℕ) : ℕ → Template
  | 0 => DR.singleBlock label edge n
  | k+1 => join edge (records label edge n k) (DR.singleBlock label edge n)

theorem compile_records (label edge n k : ℕ) : DT.compile label edge n k=records label edge n k := by
  induction k with
  | zero => exact DR.compile_singleBlock label edge n
  | succ k ih =>
      change T.shapeTemplate (ExactTwoChain.series (D.blockChain (K:=ℚ) 0 0 0 n k)
        (D.stage (K:=ℚ) 0 0 0 n)).shape label edge=_
      rw [shapeTemplate_series]
      change join edge (DT.compile label edge n k) (DT.compile label edge n 0)=_
      rw [ih,DR.compile_singleBlock]
      rfl

@[simp] theorem boundary (label edge n k : ℕ) : (records label edge n k).boundary=4 := by
  rw [←compile_records]
  rfl

theorem counts (label edge n k : ℕ) (hn : 0<n) :
    (records label edge n k).vertices.length=n*(k+1) ∧
      (records label edge n k).edges.length=2*n*(k+1)-2 := by
  rw [←compile_records]
  exact DT.counts label edge n k hn

variable {s e : ℕ} (ar : ℕ → ℕ) (label : Fin s) (hlabel : ar label.val=4) (edge : Fin e)

include hlabel in
theorem valid (n k : ℕ) : (records label.val edge.val n k).WellFormed s e ar := by
  rw [←compile_records]
  exact DT.valid ar label hlabel edge n k

theorem denote [CharZero K] (a b c : K) (n k : ℕ) (hn : 0<n)
    (G : (i : Fin s) → Signature K (ar i.val)) (X : Fin e → Kernel K)
    (hq : (⟨ar label.val,G label⟩ : AnySignature K)=⟨4,ThreeModeSignatures.original a b c⟩)
    (hX : X edge=Signature.disequality) :
    HEq ((records label.val edge.val n k).network (valid ar label hlabel edge n k) G X).denote
      (ThreeModeSignatures.spectral ((PositiveDynamicStage.A a b n)^(k+1))
        ((PositiveDynamicStage.B a b n+PositiveDynamicStage.C c n)^(k+1))
        ((PositiveDynamicStage.B a b n-PositiveDynamicStage.C c n)^(k+1))) := by
  have he := Holant.Complexity.BinaryInterpolation.Chains.template_denote_heq _ _
    (valid ar label hlabel edge n k) (DT.valid ar label hlabel edge n k)
    (compile_records label.val edge.val n k).symm G X
  exact he.trans (heq_of_eq (DT.denote ar label hlabel edge a b c n k hn G X hq hX))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicStageSeriesRecords
