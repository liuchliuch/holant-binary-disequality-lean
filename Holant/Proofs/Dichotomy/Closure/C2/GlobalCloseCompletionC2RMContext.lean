import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RMActual
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2KAffine
import Holant.Proofs.Algorithms.RingHomDescent
import Holant.OpenNetworkComposition.ProjectiveSubstitution
import Holant.ReedMuller.TwoChart.NativeXExpansionContext

/-! Literal RM context networks descend to the original coefficient field.
Their normalized RM vertices are replaced by the proved actual nonzero RM
multiples, and all substitution factors remain in the actual output tensor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RMContext
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller.TwoChart
namespace R
export GlobalCloseCompletionC2RMActual (rm rm_algebraic)
end R
namespace B
export GlobalCloseCompletionC2BitTranslateActual (identity)
end B
namespace RH
export RingHomRealization (mapSignature mapAny mapFamily)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [CharZero K] {n m : ℕ}
variable (phi : K→+*AlgebraicComplex)

def resources (f : Signature K n) : SignatureFamily K := {q |
  q=⟨n,f⟩ ∨ q=⟨2,B.identity⟩ ∨ q=⟨8,R.rm⟩}

theorem map_rm : RH.mapSignature phi (R.rm (K:=K))=algebraicRM := by
  rw [←R.rm_algebraic]
  funext x
  simp only [RH.mapSignature,R.rm]
  split_ifs <;> simp

theorem map_identity : RH.mapSignature phi (B.identity (K:=K))=fun x=>Signature.equality (x 0) (x 1) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [RH.mapSignature,B.identity,Signature.equality,h0,h1]

theorem mapped_resources (f : Signature K n) :
    RH.mapFamily phi (resources f)=insert (⟨n,RH.mapSignature phi f⟩ : AnySignature AlgebraicComplex) algebraicIRMFamily := by
  ext q
  constructor
  · rintro ⟨q,(rfl|rfl|rfl),rfl⟩
    · exact Or.inl rfl
    · right; left
      exact congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex)) (map_identity phi)
    · right; right
      exact congrArg (fun f : Signature AlgebraicComplex 8=>(⟨8,f⟩ : AnySignature AlgebraicComplex)) (map_rm phi)
  · rintro (rfl|rfl|rfl)
    · exact ⟨⟨n,f⟩,Or.inl rfl,rfl⟩
    · exact ⟨⟨2,B.identity⟩,Or.inr (Or.inl rfl),congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex)) (map_identity phi)⟩
    · exact ⟨⟨8,R.rm⟩,Or.inr (Or.inr rfl),congrArg (fun f : Signature AlgebraicComplex 8=>(⟨8,f⟩ : AnySignature AlgebraicComplex)) (map_rm phi)⟩

variable (f : Signature K n) (N : Network AlgebraicComplex m)
variable (uses : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex)∈
  insert (⟨n,RH.mapSignature phi f⟩ : AnySignature AlgebraicComplex) algebraicIRMFamily)

include uses in
private theorem mapped_uses (v : Fin N.shape.vertices) :
    (⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex)∈RH.mapFamily phi (resources f) := by
  rw [mapped_resources]
  exact uses v

def descend : Network K m where
  shape := N.shape
  vertex v := (RingHomDescent.vertex_preimage phi (N.vertex v) (mapped_uses phi f N uses v)).choose
  edge _ := Signature.disequality

theorem descend_uses (v : Fin N.shape.vertices) :
    (⟨N.shape.arity v,(descend phi f N uses).vertex v⟩ : AnySignature K)∈resources f :=
  (RingHomDescent.vertex_preimage phi (N.vertex v) (mapped_uses phi f N uses v)).choose_spec.1

theorem descend_maps (native : ∀e,N.edge e=Signature.disequality) : (descend phi f N uses).map phi=N := by
  cases N with
  | mk shape vertex edge =>
    unfold descend Network.map
    congr 1
    · funext v x
      exact congrFun ((RingHomDescent.vertex_preimage phi (vertex v) (mapped_uses phi f _ uses v)).choose_spec.2) x
    · funext e a b
      change phi (Signature.disequality a b)=edge e a b
      have he : edge e=Signature.disequality := native e
      rw [he]
      cases a <;> cases b <;> simp [Signature.disequality]

theorem descend_denote (native : ∀e,N.edge e=Signature.disequality) :
    RH.mapSignature phi (descend phi f N uses).denote=N.denote := by
  funext x
  change phi ((descend phi f N uses).denote x)=N.denote x
  rw [←Network.denote_map phi,descend_maps phi f N uses native]

variable (F : SignatureFamily K) (hI : (⟨2,B.identity⟩ : AnySignature K)∈F)
variable (actual : Gadget.Realizes F .disequality f)
variable (c : K) (hc : c≠0) (rmActual : Gadget.Realizes F .disequality (c • R.rm))

include hI actual hc rmActual in
theorem resources_actual (q : AnySignature K) (hq : q∈resources f) : Gadget.RealizesUpTo F .disequality q.2 := by
  rcases hq with rfl|rfl|rfl
  · exact ⟨1,one_ne_zero,by simpa using actual⟩
  · exact ⟨1,one_ne_zero,by simpa using Gadget.realizes_of_mem F .disequality B.identity hI⟩
  · exact ⟨c,hc,rmActual⟩

include hI actual hc rmActual in
theorem context_actual (native : ∀e,N.edge e=Signature.disequality) :
    Gadget.RealizesUpTo F .disequality (descend phi f N uses).denote := by
  apply OpenNetworkComposition.realizesUpTo_network F (descend phi f N uses)
  · intro v
    exact resources_actual f F hI actual c hc rmActual _ (descend_uses phi f N uses v)
  · exact fun _=>rfl
  · norm_num

include uses hI actual hc rmActual in
theorem bad_context (native : ∀e,N.edge e=Signature.disequality) (bad : ¬Affine N.denote) :
    ∃q : Signature K m,Gadget.Realizes F .disequality q ∧
      ¬Affine (RH.mapSignature phi q) ∧ ¬Affine (sourceKBasis.action (RH.mapSignature phi q)) := by
  obtain ⟨d,hd,actualQ⟩ := context_actual phi f N uses F hI actual c hc rmActual native
  let q : Signature K m := fun x=>d*(descend phi f N uses).denote x
  have equation : RH.mapSignature phi q=fun x=>phi d*N.denote x := by
    funext x
    change phi (d*(descend phi f N uses).denote x)=_
    rw [map_mul,←congrFun (descend_denote phi f N uses native) x]
    rfl
  have badQ : ¬Affine (RH.mapSignature phi q) := by
    intro ha
    rw [equation] at ha
    have h := ha.scale (phi d)⁻¹
    have hd' : phi d≠0 := (map_ne_zero phi).mpr hd
    apply bad
    convert h using 1
    funext x
    simp [←mul_assoc,hd']
  exact ⟨q,actualQ,badQ,fun h=>badQ ((GlobalCloseCompletionC2KAffine.sourceK_affine_iff _).mp h)⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RMContext
end
