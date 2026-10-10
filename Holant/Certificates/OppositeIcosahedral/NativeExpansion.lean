import Holant.Certificates.OppositeIcosahedral.NetworkCovariance
import Holant.Certificates.MatchingContractionClosure.NativeCollection

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev NativeVertex {n : ℕ} (s : NetworkShape n) := Fin s.vertices⊕Fin s.edges

def expansionArity {n : ℕ} (s : NetworkShape n) : NativeVertex s→ℕ := Sum.elim s.arity (fun _ => 2)

def originalPort {n : ℕ} (s : NetworkShape n) (p : Σv : Fin s.vertices,Fin (s.arity v)) :
    Σv : NativeVertex s,Fin (expansionArity s v) := ⟨.inl p.1,p.2⟩

def expansionPortMap {n : ℕ} (s : NetworkShape n) :
    (Σv : NativeVertex s,Fin (expansionArity s v))→(Fin n⊕((Fin s.edges×Bool)×Bool))
  | ⟨.inl v,i⟩ => match s.ports ⟨v,i⟩ with
    | .inl j => .inl j
    | .inr eb => .inr (eb,false)
  | ⟨.inr e,i⟩ => Fin.cases (.inr ((e,false),true)) (fun _ => .inr ((e,true),true)) i

def expansionPortInv {n : ℕ} (s : NetworkShape n) :
    (Fin n⊕((Fin s.edges×Bool)×Bool))→(Σv : NativeVertex s,Fin (expansionArity s v))
  | .inl j => originalPort s (s.ports.symm (.inl j))
  | .inr (eb,false) => originalPort s (s.ports.symm (.inr eb))
  | .inr ((e,b),true) => ⟨.inr e,if b then (1 : Fin 2) else (0 : Fin 2)⟩

def expansionPorts {n : ℕ} (s : NetworkShape n) :
    (Σv : NativeVertex s,Fin (expansionArity s v))≃(Fin n⊕((Fin s.edges×Bool)×Bool)) where
  toFun := expansionPortMap s
  invFun := expansionPortInv s
  left_inv p := by
    rcases p with ⟨v,i⟩
    cases v with
    | inl v =>
      cases he : s.ports ⟨v,i⟩ <;>
        simp only [expansionPortMap,he,expansionPortInv]
      all_goals
        change originalPort s (s.ports.symm _)=originalPort s ⟨v,i⟩
        apply congrArg (originalPort s)
        rw [←he]
        exact s.ports.symm_apply_apply ⟨v,i⟩
    | inr e => fin_cases i <;> rfl
  right_inv p := by
    rcases p with j|⟨⟨e,b⟩,z⟩
    · simp [expansionPortMap,expansionPortInv,originalPort]
    · cases z <;> cases b <;> simp [expansionPortMap,expansionPortInv,originalPort] <;> rfl

def expansionLabels {n : ℕ} (N : Network ℂ n) :
    (v : NativeVertex N.shape)→Signature ℂ (expansionArity N.shape v)
  | .inl v => N.vertex v
  | .inr e => MatchingContractionClosure.binarySignature
      (MatchingContractionClosure.nativePair (Matrix.of (N.edge e)))

def expansionFinite {n : ℕ} (N : Network ℂ n) :
    FiniteNetwork ℂ (NativeVertex N.shape) (Fin N.shape.edges×Bool) n where
  arity := expansionArity N.shape
  ports := expansionPorts N.shape
  vertex := expansionLabels N
  edge := fun _ => Signature.disequality

def nativeExpansion {n : ℕ} (N : Network ℂ n) : Network ℂ n := (expansionFinite N).toNetwork

def expansionChoices (m : ℕ) : ((Fin m×Bool)→Bool)≃((Fin m×Bool)→Bool) where
  toFun c q := !(c q)
  invFun c q := !(c q)
  left_inv c := by funext q; simp
  right_inv c := by funext q; simp

theorem expansion_original_assignment {n : ℕ} (s : NetworkShape n) (x : Fin n→Bool)
    (z : (Fin s.edges×Bool)→Bool) (v : Fin s.vertices) :
    (fun i => Sum.elim x (FiniteNetwork.endpointChoiceAssignment ((expansionChoices s.edges).symm z))
      (expansionPorts s ⟨.inl v,i⟩))=s.assignment x z v := by
  funext i
  cases he : s.ports ⟨v,i⟩ <;>
    simp [expansionPorts,expansionPortMap,NetworkShape.assignment,he,
      FiniteNetwork.endpointChoiceAssignment,expansionChoices]

theorem expansion_binary_assignment {n : ℕ} (N : Network ℂ n) (x : Fin n→Bool)
    (z : (Fin N.shape.edges×Bool)→Bool) (e : Fin N.shape.edges) :
    expansionLabels N (.inr e)
      (fun i => Sum.elim x (FiniteNetwork.endpointChoiceAssignment ((expansionChoices N.shape.edges).symm z))
        (expansionPorts N.shape ⟨.inr e,i⟩))=N.edge e (z (e,false)) (z (e,true)) := by
  change MatchingContractionClosure.nativePair (Matrix.of (N.edge e)) (!(z (e,false))) (!(z (e,true)))=_
  rw [MatchingContractionClosure.nativePair_apply]
  simp

/-- Any literal kernel network is compiled to a native-X network by inserting
one actual binary X K X per edge. Original vertices and boundary order are kept. -/
theorem nativeExpansion_denote {n : ℕ} (N : Network ℂ n) : (nativeExpansion N).denote=N.denote := by
  letI : DecidableEq (Fin N.shape.edges×Bool) := Classical.decEq _
  rw [nativeExpansion,FiniteNetwork.denote_toNetwork]
  funext x
  rw [expansionFinite,FiniteNetwork.denote_disequality_apply]
  let F : ((Fin N.shape.edges×Bool)→Bool)→ℂ := fun c =>
    ∏v : NativeVertex N.shape,expansionLabels N v
      (fun i => Sum.elim x (FiniteNetwork.endpointChoiceAssignment c) (expansionPorts N.shape ⟨v,i⟩))
  change (∑c,F c)=_
  rw [←(expansionChoices N.shape.edges).symm.sum_comp F]
  unfold Network.denote
  apply Finset.sum_congr (by ext z; simp)
  intro z hz
  dsimp only [F]
  rw [Fintype.prod_sum_type]
  change (∏v,N.vertex v (fun i => Sum.elim x
      (FiniteNetwork.endpointChoiceAssignment ((expansionChoices N.shape.edges).symm z))
      (expansionPorts N.shape ⟨.inl v,i⟩)))*
    (∏e,expansionLabels N (.inr e) (fun i => Sum.elim x
      (FiniteNetwork.endpointChoiceAssignment ((expansionChoices N.shape.edges).symm z))
      (expansionPorts N.shape ⟨.inr e,i⟩)))=_
  apply congrArg₂ (fun a b : ℂ => a*b)
  · apply Finset.prod_congr rfl
    intro v hv
    exact congrArg (N.vertex v) (expansion_original_assignment N.shape x z v)
  · apply Finset.prod_congr rfl
    intro e he
    exact expansion_binary_assignment N x z e

def expansionResources {n : ℕ} (N : Network ℂ n) : SignatureFamily ℂ :=
  {p | (∃v : Fin N.shape.vertices,p=⟨N.shape.arity v,N.vertex v⟩) ∨
    ∃e : Fin N.shape.edges,p=⟨2,MatchingContractionClosure.binarySignature
      (MatchingContractionClosure.nativePair (Matrix.of (N.edge e)))⟩}

theorem nativeExpansion_realizes {n : ℕ} (N : Network ℂ n) :
    Gadget.Realizes (expansionResources N) .disequality N.denote := by
  have hh := Gadget.realizes_network (nativeExpansion N) (expansionResources N) .disequality
    (by
      intro v
      change (⟨_,expansionLabels N ((Fintype.equivFin (NativeVertex N.shape)).symm v)⟩ : AnySignature ℂ)∈_
      cases he : (Fintype.equivFin (NativeVertex N.shape)).symm v with
      | inl w => exact Or.inl ⟨w,rfl⟩
      | inr e => exact Or.inr ⟨e,rfl⟩)
    (by intro e; rfl)
  rwa [nativeExpansion_denote] at hh

theorem nativeExpansion_vertices {n : ℕ} (N : Network ℂ n) :
    (nativeExpansion N).shape.vertices=N.shape.vertices+N.shape.edges := by
  simp [nativeExpansion,FiniteNetwork.toNetwork,NativeVertex]

theorem nativeExpansion_edges {n : ℕ} (N : Network ℂ n) :
    (nativeExpansion N).shape.edges=2*N.shape.edges := by
  simp [nativeExpansion,FiniteNetwork.toNetwork,Nat.mul_comm]

end
end Holant.Certificates.OppositeIcosahedral
