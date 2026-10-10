import Holant.Certificates.FourthRootOdd.NetworkTools
import Holant.Certificates.TwelveLoops.Transfers

namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops

def nativeContract {K : Type*} [Semiring K] (f : Signature K 4) (p : Fin 6) : Signature K 2 :=
  Signature.contract Signature.disequality (Tensor.reindex (portEquiv p).symm f)

variable {K : Type*} [CommSemiring K]

def nativeLoopNetwork (f : Signature K 4) (p : Fin 6) : Network K 2 :=
  (reorderNetwork (singleVertexNetwork f) (portEquiv p).symm).contract Signature.disequality

theorem nativeLoopNetwork_denote (f : Signature K 4) (p : Fin 6) :
    (nativeLoopNetwork f p).denote=nativeContract f p := by
  rw [nativeLoopNetwork,Network.denote_contract,reorderNetwork_denote,singleVertexNetwork_denote]
  rfl

theorem nativeContract_realizes (f : Signature K 4) (p : Fin 6) :
    Gadget.Realizes ({⟨4,f⟩} : SignatureFamily K) .disequality (nativeContract f p) := by
  rw [←nativeLoopNetwork_denote]
  apply Gadget.realizes_network
  · intro v
    exact Set.mem_singleton _
  · intro e
    change Fin 1 at e
    have he : e=0 := Subsingleton.elim _ _
    subst e
    rfl

end Holant.Certificates.FourthRootOdd
