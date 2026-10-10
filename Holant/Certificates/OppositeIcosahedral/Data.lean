import Holant.Certificates.RainbowOrbit.GroupRepresentatives
import Holant.Certificates.RainbowOrbit.Proportional
import Holant.ReedMuller.CoefficientAtlas.ContractionTransport

/-! Literal D and opposite icosahedral source coordinates for Lemma9.2.
All actions in this tree are analytical coefficient identities until an actual
original-coordinate network and its source labels are explicitly supplied. -/
namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev Mat := Matrix Bool Bool ℂ

def D : Mat := Matrix.of Q0+Matrix.of Q3
def Dinv : Mat := (1/2 : ℂ) • (Matrix.of Q0-Matrix.of Q3)
def X : Mat := Signature.disequality

def conjugate (U : Mat) : Mat := D*U*Dinv
def pull (U : Mat) : Mat := Dinv*U*D

def kappa (K : Mat) : Mat := Dinv.transpose*K*Dinv
def unkappa (K : Mat) : Mat := D.transpose*K*D

/-- The opposite source display uses odd permutations of the same original
four golden coordinates and keeps the full original tetrahedral subset. -/
def oppositeBase (U : Binary) : Prop := tetrahedralBase U ∨
  ∃π : Equiv.Perm (Fin 4),Equiv.Perm.sign π=(-1 : ℤˣ) ∧ ∃ε : Fin 3→Bool,
    U=quaternion (fun i => goldenVector ε (π.symm i))

def Direction (U : Mat) : Prop :=
  ∃c : ℂ,c≠0 ∧ ∃V : Binary,oppositeBase V ∧ U=c • Matrix.of V

def chiralitySwap : Equiv.Perm (Fin 4) := Equiv.swap 1 2

def forwardSigns : Fin 4→Bool := ![false,false,true,false]
def inverseSigns : Fin 4→Bool := ![false,true,false,false]

theorem chiralitySwap_sign : Equiv.Perm.sign chiralitySwap=(-1 : ℤˣ) := by decide +kernel

end
end Holant.Certificates.OppositeIcosahedral
