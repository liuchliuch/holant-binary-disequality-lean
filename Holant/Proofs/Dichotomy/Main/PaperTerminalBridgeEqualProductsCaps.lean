import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsAlgebra
import Holant.Proofs.Hardness.EightVertexGaugeCaps
import Holant.OpenNetworkComposition.Closure
import Holant.OpenNetworkComposition.ProjectiveContraction

/-! Actual native-X cap ratios, their reversed orientation, and bounded
composition. Inverse ratios are supplied by the real reversed binary gadget;
no diagonal gates, literal-I vertices or torsion hypotheses are used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsCaps
open Holant Holant.OpenNetworkComposition
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export GeneralCancellationCapPin (antiTensor network portOrder)
end C
namespace G
export StableDenseResidualGaugeCore (weighted)
export EightVertexGaugeCaps (exact_cap scalar loopPorts remainingPorts)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def Rel (F : SignatureFamily K) (p q : K) : Prop := Gadget.RealizesUpTo F .disequality (C.antiTensor p q)

theorem refl (F : SignatureFamily K) (p : K) (nonzero : p≠0) : Rel F p p := by
  refine ⟨p⁻¹,inv_ne_zero nonzero,?_⟩
  convert Gadget.realizes_edgeBox F .disequality using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [C.antiTensor,EdgeKind.value,Signature.disequality,h0,h1,nonzero]

theorem symm (F : SignatureFamily K) (p q : K) (h : Rel F p q) : Rel F q p := by
  obtain ⟨c,hc,actual⟩ := h
  refine ⟨c,hc,?_⟩
  have reversed := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ actual (Equiv.swap 0 1)
  convert reversed using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Tensor.reindex,C.antiTensor,Equiv.symm_swap,h0,h1]

theorem trans (F : SignatureFamily K) (p q r : K) (middle : q≠0)
    (left : Rel F p q) (right : Rel F q r) : Rel F p r := by
  obtain ⟨c,hc,actualC⟩ := left
  obtain ⟨d,hd,actualD⟩ := right
  have actual := realizes_splice F (fun x=>c*C.antiTensor p q x)
    (fun x=>d*C.antiTensor q r x) actualC actualD 0
  refine ⟨c*d*q,mul_ne_zero (mul_ne_zero hc hd) middle,?_⟩
  convert actual using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [spliceTensor,C.antiTensor,Signature.disequality,h0,h1,Function.update] <;> ring

theorem unscale {n : ℕ} (F : SignatureFamily K) (f : Signature K n) (c : K) (nonzero : c≠0)
    (h : Gadget.RealizesUpTo F .disequality (fun x=>c*f x)) : Gadget.RealizesUpTo F .disequality f := by
  obtain ⟨d,hd,actual⟩ := h
  refine ⟨d*c,mul_ne_zero hd nonzero,?_⟩
  convert actual using 1
  funext x
  ring

theorem cap_actual (F : SignatureFamily K) (q : Signature K 4) (actual : Gadget.Realizes F .disequality q)
    (k : GeneralCancellationCapPin.Choice) : Gadget.RealizesUpTo F .disequality (C.network q k).denote := by
  have reordered := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality q actual
    (C.portOrder k.1 k.2).symm
  simp only [Equiv.symm_symm] at reordered
  have contracted := realizes_contract F _ reordered (by norm_num)
  have value : (C.network q k).denote=Signature.contract Signature.disequality
      (Tensor.reindex (C.portOrder k.1 k.2) q) := by
    rw [C.network,Network.denote_contract,
      Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,Network.denote_corolla]
  rwa [←value] at contracted

theorem cap_relation (F : SignatureFamily K) (a : K) (u : Fin 4→K) (scale : a≠0)
    (actual : Gadget.Realizes F .disequality (G.weighted a u)) (k : Fin 6)
    (sum : u (G.loopPorts k).1+u (G.loopPorts k).2≠0) :
    Rel F (u (G.remainingPorts k).1) (u (G.remainingPorts k).2) := by
  have h := cap_actual F (G.weighted a u) actual (k,true)
  rw [G.exact_cap] at h
  exact unscale F _ (G.scalar a u k) (mul_ne_zero scale sum) h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsCaps
end
