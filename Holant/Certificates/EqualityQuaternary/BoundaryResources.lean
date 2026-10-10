import Holant.Certificates.EqualityQuaternary.KleinOrbitNetwork

/-! Retained binary representatives are literal current-alphabet resources.
This connects original-q copy counts to the displayed actual network itself,
without expanding a binary representative into an arbitrary predecessor gadget.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary
open Holant Holant.Marked Holant.Tractable
open Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false

namespace Boundary
def Uses (F : SignatureFamily Scalar) {n : ℕ} (N : Network Scalar n) : Prop :=
  ∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature Scalar)∈F

theorem attachFirst_uses {F : SignatureFamily Scalar} {N : Network Scalar 4}
    (h : Uses F N) (B : Mat) (hB : (⟨2,kernelSignature B⟩ : AnySignature Scalar)∈F) : Uses F (attachFirst N B) := by
  intro v
  change (⟨_,(Network.tensorFinite N (singleVertexNetwork (kernelSignature B))).vertex
    ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin 1)).symm v)⟩ : AnySignature Scalar)∈F
  cases (Fintype.equivFin (Fin N.shape.vertices ⊕ Fin 1)).symm v with
  | inl v => exact h v
  | inr v => exact hB

theorem attach_uses {F : SignatureFamily Scalar} {N : Network Scalar 4}
    (h : Uses F N) (i : Fin 4) (B : Mat) (hB : (⟨2,kernelSignature B⟩ : AnySignature Scalar)∈F) : Uses F (attach N i B) :=
  attachFirst_uses (N:=reorderNetwork N (Equiv.swap 0 i)) h B hB

theorem flipLastTwo_uses {F : SignatureFamily Scalar} {N : Network Scalar 4}
    (h : Uses F N) (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F) : Uses F (flipLastTwo N) :=
  attach_uses (attach_uses h 2 _ hI) 3 _ hI
end Boundary

namespace Klein
def Retained {F : SignatureFamily Scalar} {kind : Kind} (reps : Representatives F kind) : Prop :=
  ∀ j,(⟨2,kernelSignature (reps.matrix j)⟩ : AnySignature Scalar)∈F

namespace Orbit
theorem netAct_uses {F : SignatureFamily Scalar} (reps : Representatives F .exotic)
    (hret : Retained reps) (op : Op) {N : Network Scalar 4} (h : Boundary.Uses F N) :
    Boundary.Uses F (netAct reps op N) := by
  cases op with
  | dress i j => exact Boundary.attach_uses h i _ (hret _)
  | swap i => exact h

theorem netRun_uses {F : SignatureFamily Scalar} (reps : Representatives F .exotic)
    (hret : Retained reps) (ops : List Op) {N : Network Scalar 4} (h : Boundary.Uses F N) :
    Boundary.Uses F (netRun reps ops N) := by
  induction ops generalizing N with
  | nil => exact h
  | cons op ops ih => exact ih (netAct_uses reps hret op h)
end Orbit
end Klein
end Holant.Certificates.EqualityQuaternary
