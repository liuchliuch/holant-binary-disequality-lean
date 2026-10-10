import Holant.Proofs.Hardness.GeneralEOAffinePlaneChainLabels
import Holant.Proofs.Hardness.ExactTwoSignatures

/-! A scalar matrix period is realized by an actual positive native-X chain.
In particular, exponent24 uses24 original quaternary vertices and46 native
edges, with ordered boundary0101/1010 and no synthetic DEQ vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneDEQ
open Holant Holant.Complexity
open scoped Matrix
namespace C
export GeneralEOAffinePlaneChain (Mat binary bitIndex table literal literal_denote)
end C
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

theorem lifted_scalar (c : K) :
    EOBinaryPlaneCore.lift (C.binary (c • (1 : C.Mat (K:=K))))=c • ExactTwoSignatures.E := by
  funext x
  rw [Pi.smul_apply,smul_eq_mul,ExactTwoSignatures.E_reference]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [EOBinaryPlaneCore.lift,C.binary,C.bitIndex,Matrix.one_apply,h0,h1,h2,h3]

theorem power_denote (M : Signature K 4) (e : Equiv.Perm (Fin 4))
    (f : Signature K 2) (hM : Tensor.reindex e M=EOBinaryPlaneCore.lift f)
    (k : ℕ) (c : K) (hp : C.table f^(k+1)=c • (1 : C.Mat (K:=K))) :
    (C.literal M e k).denote=c • ExactTwoSignatures.E := by
  rw [C.literal_denote M e f hM k,hp,lifted_scalar]

theorem period24 (M : Signature K 4) (e : Equiv.Perm (Fin 4))
    (f : Signature K 2) (hM : Tensor.reindex e M=EOBinaryPlaneCore.lift f)
    (c : K) (hp : C.table f^24=c • (1 : C.Mat (K:=K))) :
    (C.literal M e 23).shape.vertices=24 ∧
    (C.literal M e 23).shape.edges=46 ∧
    BinaryInterpolation.Chains.Native (C.literal M e 23) ∧
    BinaryInterpolation.Chains.Uses (C.literal M e 23) {⟨4,M⟩} ∧
    (C.literal M e 23).denote=c • ExactTwoSignatures.E :=
  ⟨GeneralEOAffinePlaneChain.literal_vertices M e 23,
    GeneralEOAffinePlaneChain.literal_edges M e 23,
    GeneralEOAffinePlaneChain.literal_native M e 23,
    GeneralEOAffinePlaneChain.literal_uses M e _ (Set.mem_singleton _) 23,
    power_denote M e f hM 23 c hp⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneDEQ
