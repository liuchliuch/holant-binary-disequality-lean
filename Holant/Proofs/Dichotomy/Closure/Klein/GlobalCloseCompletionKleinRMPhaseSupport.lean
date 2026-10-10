import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinRMPhaseSource
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramCertificate

/-! The four boundary support positions of each phase probe. A nonzero Pauli
matching supported there has product +1 in its integer normalization. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRMPhaseSupport
open Holant
open scoped BigOperators
namespace C
export GlobalCloseCompletionKleinGramCertificate (pauli product)
end C
namespace S
export GlobalCloseCompletionKleinRMPhaseSource (index4)
end S
namespace T
export GlobalCloseCompletionKleinRMPhaseTable (positions)
end T
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def word4 (i : Fin 16) (k : Fin 4) : Bool := i.val.testBit (3-k.val)

theorem index_word : ∀i : Fin 16,S.index4 (word4 i)=i := by decide +kernel
theorem word_index : ∀x : Fin 4→Bool,word4 (S.index4 x)=x := by decide +kernel

theorem positions_injective : ∀j : Fin 7,Function.Injective (T.positions j) := by decide +kernel

def Supported (p : Fin 4→Fin 4) (a b : Fin 4) (j : Fin 7) : Prop :=
  ∀x : Fin 4→Bool,C.product p a b x≠0→∃k : Fin 4,S.index4 x=T.positions j k

theorem pauli_product : ∀p : Fin 4→Fin 4,Function.Injective p→∀j : Fin 7,∀a b : Fin 4,
    Supported p a b j→(∏k : Fin 4,C.product p a b (word4 (T.positions j k)))=1 := by
  unfold Function.Injective Supported
  decide +kernel

theorem pauli_power : ∀k : Fin 4,∀a b : Bool,(C.pauli k a b)^4=0 ∨ (C.pauli k a b)^4=1 := by decide

theorem product_power (p : Fin 4→Fin 4) (a b : Fin 4) (x : Fin 4→Bool) :
    (C.product p a b x)^4=0 ∨ (C.product p a b x)^4=1 := by
  rw [C.product,mul_pow]
  rcases pauli_power a (x (p 0)) (x (p 1)) with h|h <;>
    rcases pauli_power b (x (p 2)) (x (p 3)) with h'|h' <;> simp [h,h']


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRMPhaseSupport
