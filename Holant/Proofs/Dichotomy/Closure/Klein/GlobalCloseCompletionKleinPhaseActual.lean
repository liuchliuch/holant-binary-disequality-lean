import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterResources
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH8Wiring

/-! Literal real sign dressings, bit translations and two-copy joins over the
same original field. Every sign uses an actual ordered J row; every shift uses
retained I, and every projective multiplier remains in the final realization. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinPhaseActual
open Holant Holant.OpenNetworkComposition
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CharacterFlat
namespace C
export GlobalCloseCompletionKleinCharacterResources (bell)
end C
namespace W
export GlobalCloseCompletionKleinH8Wiring (join actual scale)
end W
namespace B
export GlobalCloseCompletionC2BitTranslateActual (translate translate_actual)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] {n : ℕ}

def phase (s : Finset (Fin n)) (f : Signature K n) : Signature K n :=
  fun x=>(∏i∈s,if x i then -1 else 1)*f x

theorem splice_J (f : Signature K n) (i : Fin n) :
    spliceTensor f (C.bell 1 1) i=fun x=>(if x i then -1 else 1)*f x := by
  funext x
  cases hi : x i <;>
    simp [spliceTensor,C.bell,intSign,bit,boolEquiv,Signature.disequality,hi,
      Function.update_eq_self,mul_comm]
  all_goals rw [←hi,Function.update_eq_self]

theorem splice_upTo (F : SignatureFamily K) (f : Signature K n) (b : Signature K 2)
    (actualF : Gadget.RealizesUpTo F .disequality f) (actualB : Gadget.RealizesUpTo F .disequality b)
    (i : Fin n) : Gadget.RealizesUpTo F .disequality (spliceTensor f b i) := by
  obtain ⟨c,hc,actualF⟩ := actualF
  obtain ⟨d,hd,actualB⟩ := actualB
  refine ⟨c*d,mul_ne_zero hc hd,?_⟩
  have h := realizes_splice F _ _ actualF actualB i
  convert h using 1
  funext x
  simp only [spliceTensor,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem phase_actual (F : SignatureFamily K)
    (J : Gadget.RealizesUpTo F .disequality (C.bell 1 1))
    (f : Signature K n) (actual : Gadget.RealizesUpTo F .disequality f) (s : Finset (Fin n)) :
    Gadget.RealizesUpTo F .disequality (phase s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have empty : phase (∅ : Finset (Fin n)) f=f := by funext x;simp [phase]
    rw [empty]
    exact actual
  | @insert i s hi ih =>
    have h := splice_upTo F (phase s f) (C.bell 1 1) ih J i
    rw [splice_J] at h
    convert h using 1
    funext x
    simp only [phase,Finset.prod_insert hi,mul_assoc]

theorem translate_upTo (F : SignatureFamily K) (identity : RetainsIdentity F)
    (f : Signature K n) (actual : Gadget.RealizesUpTo F .disequality f) (mask : Fin n→Bool) :
    Gadget.RealizesUpTo F .disequality (B.translate f mask) := by
  obtain ⟨c,hc,actual⟩ := actual
  refine ⟨c,hc,?_⟩
  have h := B.translate_actual F identity (c • f) actual mask
  exact h

theorem join_upTo (F : SignatureFamily K) (identity : RetainsIdentity F)
    (f g : Signature K 8) (left : Gadget.RealizesUpTo F .disequality f)
    (right : Gadget.RealizesUpTo F .disequality g) : Gadget.RealizesUpTo F .disequality (W.join f g) := by
  obtain ⟨c,hc,left⟩ := left
  obtain ⟨d,hd,right⟩ := right
  refine ⟨c*d,mul_ne_zero hc hd,?_⟩
  have h := W.actual F identity (c • f) (d • g) left right
  rwa [W.scale] at h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinPhaseActual
end
