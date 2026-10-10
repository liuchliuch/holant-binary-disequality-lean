import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RadonActual
import Holant.ReedMuller.CharacterRecognition.SourceAPI
import Holant.ReedMuller.TwoChart.Localization

/-! Actual original-field Bell/RM resources for the character-aware Radon
and localization networks. Normalized Bell vertices are projectively
substituted by their actual supplied graphs, keeping every scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterResources
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.TwoChart
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace A
export GlobalCloseCompletionC2RadonActual (complexEmbedding mapped_rm descend_upTo)
end A
namespace RH
export RingHomRealization (mapSignature mapFamily realizes_map realizesUpTo_map)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [CharZero K]

/-- Literal ordered Pauli/Bell row over the unchanged coefficient field. -/
def bell (d l : ZMod 2) : Signature K 2 := fun x=>
  (intSign (l*bit (x 0)) : K)*(if boolEquiv (x 0)+boolEquiv (x 1)=d then 1 else 0)

variable (phi : K→+*AlgebraicComplex)

theorem map_bell (d l : ZMod 2) : RH.mapSignature phi (bell d l)=algebraicBell d l := by
  funext x
  apply Subtype.ext
  simp only [RH.mapSignature,bell,map_mul,map_intCast,algebraicBell,bellSignature,bellKernel,
    sign,parityKernel,bit]
  split_ifs <;> simp

theorem complex_bell (d l : ZMod 2) :
    RH.mapSignature (A.complexEmbedding phi) (bell d l)=bellSignature d l := by
  funext x
  exact congrArg Subtype.val (congrFun (map_bell phi d l) x)

theorem descend_algebraic {m : ℕ} (F : SignatureFamily K) (g : Signature AlgebraicComplex m)
    (actual : Gadget.RealizesUpTo (RH.mapFamily phi F) .disequality g) :
    ∃q : Signature K m,∃d : AlgebraicComplex,d≠0 ∧ Gadget.Realizes F .disequality q ∧
      RH.mapSignature phi q=d • g := by
  obtain ⟨d,hd,N,uses,native,equation⟩ := actual
  let M := RingHomDescent.descendNetwork phi N uses
  refine ⟨M.tensor,d,hd,⟨M,RingHomDescent.descend_labels phi N uses,native,rfl⟩,?_⟩
  exact (RingHomDescent.descend_tensor phi N uses).trans equation

variable (F : SignatureFamily K) (bells : ∀d l,Gadget.RealizesUpTo F .disequality (bell d l))
variable (c : K) (hc : c≠0) (rmActual : Gadget.Realizes F .disequality (c • R.rm))
variable {n : ℕ} (f : Signature K n) (actual : Gadget.Realizes F .disequality f)

include bells hc rmActual actual in
theorem complex_resource (q : AnySignature ℂ)
    (member : q∈SignedRadon.cardFamily (fun _ _=>1) (RH.mapSignature (A.complexEmbedding phi) f)) :
    Gadget.RealizesUpTo (RH.mapFamily (A.complexEmbedding phi) F) .disequality q.2 := by
  rcases member with rfl|(rfl|⟨d,l,rfl⟩)
  · exact ⟨1,one_ne_zero,by simpa using RH.realizes_map (A.complexEmbedding phi) actual⟩
  · have h : Gadget.RealizesUpTo F .disequality (R.rm (K:=K)) := ⟨c,hc,rmActual⟩
    have mapped := RH.realizesUpTo_map (A.complexEmbedding phi) (A.complexEmbedding phi).injective h
    rwa [A.mapped_rm] at mapped
  · have mapped := RH.realizesUpTo_map (A.complexEmbedding phi) (A.complexEmbedding phi).injective (bells d l)
    rw [complex_bell] at mapped
    simpa only [one_smul] using mapped

include bells hc rmActual actual in
theorem algebraic_resource (q : AnySignature AlgebraicComplex)
    (member : q∈insert (⟨n,RH.mapSignature phi f⟩ : AnySignature AlgebraicComplex)
      (algebraicRetainedFamily (fun _ _=>1))) :
    Gadget.RealizesUpTo (RH.mapFamily phi F) .disequality q.2 := by
  rcases member with rfl|(rfl|⟨d,l,rfl⟩)
  · exact ⟨1,one_ne_zero,by simpa using RH.realizes_map phi actual⟩
  · have h : Gadget.RealizesUpTo F .disequality (R.rm (K:=K)) := ⟨c,hc,rmActual⟩
    have mapped := RH.realizesUpTo_map phi phi.injective h
    rwa [GlobalCloseCompletionC2RMContext.map_rm] at mapped
  · have mapped := RH.realizesUpTo_map phi phi.injective (bells d l)
    rw [map_bell] at mapped
    simpa only [one_smul] using mapped

include bells hc rmActual actual in
theorem bad_context {m : ℕ} (N : Network AlgebraicComplex m)
    (uses : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex)∈
      insert (⟨n,RH.mapSignature phi f⟩ : AnySignature AlgebraicComplex)
        (algebraicRetainedFamily (fun _ _=>1)))
    (native : ∀e,N.edge e=Signature.disequality) (bad : ¬Affine N.denote) :
    ∃q : Signature K m,Gadget.Realizes F .disequality q ∧ ¬Affine (RH.mapSignature phi q) := by
  have network := OpenNetworkComposition.realizesUpTo_network (RH.mapFamily phi F) N
    (fun v=>algebraic_resource phi F bells c hc rmActual f actual _ (uses v)) native (by norm_num)
  obtain ⟨q,d,hd,actualQ,equation⟩ := descend_algebraic phi F N.denote network
  refine ⟨q,actualQ,?_⟩
  intro affine
  have unscaled := affine.scale d⁻¹
  rw [equation] at unscaled
  apply bad
  convert unscaled using 1
  funext x
  simp [←mul_assoc,hd]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterResources
end
