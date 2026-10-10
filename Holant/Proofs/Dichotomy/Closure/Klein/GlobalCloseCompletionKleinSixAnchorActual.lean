import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixAnchorData
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinPhasePrime
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinBitTranslate

/-! The first-card gauge is an actual original-field programme and preserves
primality. Its real first Bell card is exactly the old scalar times I tensor I. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixAnchorActual
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
namespace D
export GlobalCloseCompletionKleinSixAnchorData (order mask phaseMask phaseSet word weight tailWord word_pair weight_pair normalized_line)
end D
namespace A
export GlobalCloseCompletionKleinPhaseActual (phase phase_actual translate_upTo)
end A
namespace T
export GlobalCloseCompletionC2BitTranslateActual (translate)
end T
namespace C
export GlobalCloseCompletionKleinSixBellNorm (card)
end C
namespace N
export GlobalCloseCompletionKleinGramNorm (rows)
end N
namespace DL
export GlobalCloseCompletionKleinSixFiniteData (line)
end DL
namespace S
export GlobalCloseCompletionKleinRMPhaseSource (index4)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K L : Type*} [Field K] [Field L]

def gauge (a : Fin 48) (f : Signature K 6) : Signature K 6 :=
  A.phase (D.phaseSet a) (T.translate (Tensor.reindex (D.order a) f) (D.mask a))

theorem value (a : Fin 48) (f : Signature K 6) (x : Fin 6→Bool) :
    gauge a f x=(D.weight a x:K)*f (D.word a x) := by
  change gauge a f x=(D.weight a x:K)*f (fun i=>x (D.order a i) ^^ D.mask a (D.order a i))
  simp only [gauge,A.phase,D.phaseSet,Finset.prod_filter,Fin.prod_univ_succ,T.translate,Tensor.reindex]
  cases ha : a.val.testBit 3 <;> cases hb : a.val.testBit 1 <;>
    simp [D.phaseMask,D.weight,ha,hb]

theorem map_gauge (phi : K→+*L) (a : Fin 48) (f : Signature K 6) :
    RingHomRealization.mapSignature phi (gauge a f)=gauge a (RingHomRealization.mapSignature phi f) := by
  funext x
  simp only [RingHomRealization.mapSignature,value,map_mul,map_intCast]

theorem prime (a : Fin 48) (f : Signature K 6) (prime : Prime (⟨6,f⟩ : AnySignature K)) :
    Prime (⟨6,gauge a f⟩ : AnySignature K) :=
  GlobalCloseCompletionKleinPhasePrime.phase_prime _
    (GlobalCloseCompletionKleinBitTranslate.prime _
      (GlobalCloseCompletionKleinGramAllPairs.prime_reindex f prime (D.order a)) (D.mask a)) (D.phaseSet a)

theorem actual (F : SignatureFamily K) (identity : RetainsIdentity F)
    (J : Gadget.RealizesUpTo F .disequality (GlobalCloseCompletionKleinCharacterResources.bell 1 1))
    (a : Fin 48) (f : Signature K 6) (actual : Gadget.RealizesUpTo F .disequality f) :
    Gadget.RealizesUpTo F .disequality (gauge a f) := by
  have reordered := Holant.OpenNetworkComposition.ProjectiveSubstitution.realizesUpTo_reindex
    F (D.order a) f actual
  have translated := A.translate_upTo F identity _ reordered (D.mask a)
  exact A.phase_actual F J _ translated (D.phaseSet a)

theorem card_gauge (a : Fin 48) (f : Signature ℝ 6) (k : Fin 4) (z : Fin 4→Bool) :
    C.card (gauge a f) k z=(D.weight a (Fin.addCases (m:=2) (n:=4) (fun _=>false) z):ℝ)*
      C.card f k (D.tailWord a z) := by
  simp only [C.card,N.rows,value,D.word_pair,D.weight_pair]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem first_card (a : Fin 48) (f : Signature ℝ 6) (d : ℝ)
    (form : ∀z : Fin 4→Bool,C.card f 0 z=d*(DL.line a (S.index4 z):ℝ)) (z : Fin 4→Bool) :
    C.card (gauge a f) 0 z=d*(DL.line 0 (S.index4 z):ℝ) := by
  rw [card_gauge,form]
  have h := congrArg (fun t : ℤ=>(t:ℝ)) (D.normalized_line a z)
  simp only [Int.cast_mul] at h
  calc
    _=d*((D.weight a (Fin.addCases (m:=2) (n:=4) (fun _=>false) z):ℝ)*
      (DL.line a (S.index4 (D.tailWord a z)):ℝ)) := by ring
    _=d*(DL.line 0 (S.index4 z):ℝ) := congrArg (fun t=>d*t) h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixAnchorActual
end
