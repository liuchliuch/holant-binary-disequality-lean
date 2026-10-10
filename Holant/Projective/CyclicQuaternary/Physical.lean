import Holant.Projective.CyclicQuaternary.Coordinates
import Holant.Tractable.Anchor.MatrixActions
import Holant.Realization

/-! Walsh and recorded-scalar bridge from the original physical q and native-X
binary representatives to the analytic classification. Every closing operation
is a literal finite sum across two native edges; Walsh action is analytic only. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Holant.Projective.CyclicQuaternary.Physical
open CyclicPhasePencil Holant.Tractable
abbrev Scalar := AlgebraicComplex
abbrev Mat := Kernel Scalar

def P : Mat := fun a b => if a && b then -1 else 1
def Pinv : Mat := (1/2 : Scalar) • P

def walsh {n : ℕ} (q : Signature Scalar n) : Signature Scalar n :=
  Signature.coordinateAction (fun _ => Pinv) q

def walshBinary (C : Mat) : Mat := Kernel.mul (Kernel.mul Pinv C) (Kernel.transpose Pinv)

theorem walshBinary_signature (C : Mat) : walsh (kernelSignature C)=kernelSignature (walshBinary C) :=
  coordinateAction_kernelSignature Pinv C

theorem P_Pinv : Kernel.mul P Pinv=Signature.equality := by
  funext a b
  cases a <;> cases b <;> norm_num [Kernel.mul,P,Pinv,Signature.equality]

theorem Pinv_P : Kernel.mul Pinv P=Signature.equality := by
  funext a b
  cases a <;> cases b <;> norm_num [Kernel.mul,P,Pinv,Signature.equality]

theorem native_walsh_edge : Kernel.pullback Signature.disequality P=(2 : Scalar) • Z := by
  funext a b
  cases a <;> cases b <;> norm_num [Kernel.pullback,Kernel.mul,P,Z,diagonal,Signature.disequality]

def words4 : Word ≃ (Bool × Bool × Bool × Bool) where
  toFun w := (w 0,w 1,w 2,w 3)
  invFun w := ![w.1,w.2.1,w.2.2.1,w.2.2.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem sum_words4 (f : Word → Scalar) :
    (∑ w, f w)=∑ a : Bool,∑ b : Bool,∑ c : Bool,∑ d : Bool,f ![a,b,c,d] := by
  rw [← words4.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Finite-sum closure with a stated effective two-port kernel. -/
def contractKernel (q : Signature Scalar 4) (i : Fin 3) (side : Bool) (E : Mat) : Mat :=
  fun u v => ∑ a : Bool,∑ b : Bool,E a b*q (join i side a b u v)

/-- The actual original-coordinate attachment of both ports of C through X. -/
def physicalCard (q : Signature Scalar 4) (i : Fin 3) (side : Bool) (C : Mat) : Mat :=
  contractKernel q i side (Kernel.mul (Kernel.mul Signature.disequality C) Signature.disequality)

/-- Exact local holographic transport for the two native-edge attachment.
No normalized q or C is substituted for the physical source inputs. -/
theorem walsh_physicalCard (q : Signature Scalar 4) (i : Fin 3) (side : Bool) (C : Mat) :
    walshBinary (physicalCard q i side C)=
      contractKernel (walsh q) i side
        (Kernel.mul (Kernel.mul ((2 : Scalar) • Z) (walshBinary C)) ((2 : Scalar) • Z)) := by
  funext u v
  fin_cases i <;> cases side <;> cases u <;> cases v <;>
    simp [walshBinary,physicalCard,contractKernel,walsh,Signature.coordinateAction,sum_words4,
      Fin.prod_univ_succ,Kernel.mul,Kernel.transpose,Pinv,P,Z,diagonal,Signature.disequality,join] <;> ring

end Holant.Projective.CyclicQuaternary.Physical
