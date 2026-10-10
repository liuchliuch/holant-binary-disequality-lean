import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleChoice
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportExtraction

/-! Affine-support closure of the actual literal positive blocks. This lets
an original Affine-square row feed the two-resource extraction without adding
an affine-support hypothesis on its internally generated non-Product block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSupportClosure
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export GeneralEONegativeClosedSupport (Closed)
end C
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {m n : ℕ}

theorem substitute_triple (p : Fin n→Bool ⊕ Fin m) (x y z : Fin m→Bool) :
    T.substitute p (tripleXor x y z)=tripleXor (T.substitute p x) (T.substitute p y) (T.substitute p z) := by
  funext i
  cases hp : p i with
  | inl b=>cases b <;> simp [T.substitute,tripleXor,hp]
  | inr j=>simp [T.substitute,tripleXor,hp]

theorem substitute_closed (f : Signature AlgebraicComplex n) (hf : C.Closed f)
    (p : Fin n→Bool ⊕ Fin m) : C.Closed (fun x=>f (T.substitute p x)) := by
  intro x y z hx hy hz
  change f (T.substitute p (tripleXor x y z))≠0
  rw [substitute_triple]
  exact hf _ _ _ hx hy hz

theorem mul_closed (f g : Signature AlgebraicComplex n) (hf : C.Closed f) (hg : C.Closed g) :
    C.Closed (fun x=>f x*g x) := by
  intro x y z hx hy hz
  exact mul_ne_zero (hf _ _ _ (mul_ne_zero_iff.mp hx).1 (mul_ne_zero_iff.mp hy).1 (mul_ne_zero_iff.mp hz).1)
    (hg _ _ _ (mul_ne_zero_iff.mp hx).2 (mul_ne_zero_iff.mp hy).2 (mul_ne_zero_iff.mp hz).2)

theorem evaluate_closed (f : Signature AlgebraicComplex n) (hf : C.Closed f)
    (ps : List (Fin n→Bool ⊕ Fin m)) : C.Closed (B.evaluate f ps) := by
  induction ps with
  | nil=>intro x y z hx hy hz; exact one_ne_zero
  | cons p ps ih=>exact mul_closed _ _ (substitute_closed f hf p) ih

theorem closed_of_square_affine (f : Signature AlgebraicComplex n)
    (hf : Affine (fun x=>f x^2)) : C.Closed f := by
  intro x y z hx hy hz
  have h := Holant.LocalDrafts.Hardness.EightVertexNonexception.affine_support_xor3 hf x y z (pow_ne_zero 2 hx) (pow_ne_zero 2 hy) (pow_ne_zero 2 hz)
  exact (pow_ne_zero_iff (by decide : 2≠0)).mp h

variable (K : IntermediateField ℚ AlgebraicComplex) (f : Signature K n)
variable (D : OrdinaryNegativeNonproductBundleChoice.Choice K f)

theorem nonproduct_choice_closed
    (hf : C.Closed (fun x=>(f x : AlgebraicComplex))) :
    C.Closed (fun x=>((D.coefficient x : K) : AlgebraicComplex)) := by
  have h := evaluate_closed (fun x=>(f x : AlgebraicComplex)) hf D.rows
  simpa only [OrdinaryNegativeNonproductBundleChoice.Choice.coefficient,
    OrdinaryNegativePhaseBundleChoice.coe_evaluate] using h

theorem nonproduct_choice_closed_of_square_affine
    (hf : Affine (fun x=>(f x : AlgebraicComplex)^2)) :
    C.Closed (fun x=>((D.coefficient x : K) : AlgebraicComplex)) :=
  nonproduct_choice_closed K f D (closed_of_square_affine _ hf)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSupportClosure
end
