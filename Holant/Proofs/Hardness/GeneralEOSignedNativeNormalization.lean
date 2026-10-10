import Holant.Proofs.Hardness.GeneralEOSignedNativeParity

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeParity
open Holant Holant.Tractable
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable (S : NetworkShape 0)
variable (P : (v : Fin S.vertices) → OrientedPerfectPairing (S.arity v))

def signedScope (v : Fin S.vertices) (j : Fin (P v).count) : Fin (S.edges*2) × Bool :=
  let t := port S v ((P v).ports (j,false))
  (D.scope (links S P) t.1, Bool.xor (D.signs (links S P) t.1) t.2)

def signedInput (y : Fin (S.edges*2) → Bool) (v : Fin S.vertices) : Fin (P v).count → Bool :=
  fun j => Bool.xor (signedScope S P v j).2 (y (signedScope S P v j).1)

theorem compressed_reconstruct (y : Fin (S.edges*2) → Bool) (v : Fin S.vertices) :
    compressedInput S P (D.reconstruct (links S P) y) v = signedInput S P y v := by
  funext j
  simp only [compressedInput,row,GeneralEOSignedParityComponents.reconstruct,signedInput,signedScope]
  generalize D.signs (links S P) (port S v ((P v).ports (j,false))).1 = a
  generalize y (D.scope (links S P) (port S v ((P v).ports (j,false))).1) = b
  generalize (port S v ((P v).ports (j,false))).2 = c
  cases a <;> cases b <;> cases c <;> rfl

theorem signed_sum {K : Type*} [CommSemiring K] (N : Network K 0)
    (P : (v : Fin N.shape.vertices) → OrientedPerfectPairing (N.shape.arity v))
    (he : ∀e,N.edge e=Signature.disequality) (hf : ∀v,C.Covers (P v) (N.vertex v))
    (hg : D.Good (links N.shape P)) :
    (∑y : Fin (N.shape.edges*2) → Bool,
      ∏v,C.compress (P v) (N.vertex v) (signedInput N.shape P y v)) =
      (2:K)^GeneralCSPUnused.unusedCount (D.scope (links N.shape P)) * N.denote Fin.elim0 := by
  classical
  have h := D.assignment_sum (links N.shape P) hg (weight N.shape P N.vertex)
  rw [←denote_parity N P he hf] at h
  simpa only [weight,compressed_reconstruct] using h

theorem inconsistent_denote {K : Type*} [CommSemiring K] (N : Network K 0)
    (P : (v : Fin N.shape.vertices) → OrientedPerfectPairing (N.shape.arity v))
    (he : ∀e,N.edge e=Signature.disequality) (hf : ∀v,C.Covers (P v) (N.vertex v))
    (hg : ¬D.Good (links N.shape P)) : N.denote Fin.elim0=0 := by
  rw [denote_parity N P he hf]
  exact D.inconsistent_sum_zero (links N.shape P) hg (weight N.shape P N.vertex)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeParity
