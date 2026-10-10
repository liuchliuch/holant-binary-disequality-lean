import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramActual
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange
import Holant.Proofs.Algorithms.RingHomRealization

/-! Exact coefficient transport for the two-copy Gram source, and descent of
an analytically real proper split to the original coefficient field. The
original normalization scalar is squared, never discarded. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramTransport
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
namespace G
export GlobalCloseCompletionKleinGramActual (gram)
end G
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K L : Type*} [Field K] [Field L] {n : ℕ}

theorem gram_map (phi : K→+*L) (f : Signature K (2+n)) :
    RH.mapSignature phi (G.gram f)=G.gram (RH.mapSignature phi f) := by
  funext x
  simp only [RH.mapSignature,G.gram,map_sum,map_mul]

theorem gram_scale (f : Signature K (2+n)) (c : K) : G.gram (c • f)=c^2 • G.gram f := by
  funext x
  simp only [G.gram,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem real_gram (phi : K→+*ℂ) (f : Signature K (2+n)) (r : Signature ℝ (2+n)) (c : ℂ)
    (normal : RH.mapSignature phi f=fun x=>c*(r x:ℂ)) :
    RH.mapSignature phi (G.gram f)=fun x=>c^2*(G.gram (K:=ℝ) r x:ℂ) := by
  have form : RH.mapSignature phi f=c • RH.mapSignature Complex.ofRealHom r := normal
  rw [gram_map,form,gram_scale,←gram_map]
  rfl

theorem real_split_descends {m : ℕ} (phi : K→+*ℂ) (f : Signature K m) (nonzero : f≠0)
    (r : Signature ℝ m) (c : ℂ) (hc : c≠0)
    (normal : RH.mapSignature phi f=fun x=>c*(r x:ℂ))
    {a b : AnySignature ℝ} (split : ProperSplit ⟨m,r⟩ a b) :
    ∃u v : AnySignature K,Nonempty (ProperSplit ⟨m,f⟩ u v) := by
  let S := split.map Complex.ofRealHom
  let SC : ProperSplit (mapSignature phi ⟨m,f⟩)
      (mapSignature Complex.ofRealHom a) (mapSignature Complex.ofRealHom b) :=
    { left_pos := S.left_pos
      right_pos := S.right_pos
      ports := S.ports
      scale := Units.mk0 c hc*S.scale
      equation := by
        funext x
        change Fin m→Bool at x
        change phi (f x)=(c*(S.scale:ℂ))*_
        have hn := congrFun normal x
        change phi (f x)=c*(r x:ℂ) at hn
        rw [hn]
        have hs := congrFun S.equation x
        change (r x:ℂ)=(S.scale:ℂ)*_ at hs
        rw [hs]
        simp only [mul_assoc,S,ProperSplit.map,mapSignature] }
  exact SC.descends phi ⟨m,f⟩ nonzero


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramTransport
end
