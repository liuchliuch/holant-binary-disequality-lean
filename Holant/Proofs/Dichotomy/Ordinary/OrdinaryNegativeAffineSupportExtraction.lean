import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleSupport
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionUniversal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativePhaseBundleChoice

/-! Exact two-resource extraction on arbitrary affine support. Actual support
points choose the coordinate shifts; the literal tensor retains the two rows.
The output is a finite signed-minor/private-sum binary outside both A and P.
Coordinate shifts here are semantic and must be compiled using actual X. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSupportExtraction
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace S
export OrdinaryNegativeNonproductBundleSupport (flip flip_flip product_shifted_iff)
end S
namespace T
export GeneralEOPairedFamilyExtractionTensor (tensor tensor_failures tensor_nonzero)
end T
namespace G
export GeneralEOPairedFamilyExtractionGadget (Gadget denote Bad)
end G
namespace U
export GeneralEOPairedFamilyExtractionUniversal (exists_gadget)
end U
namespace C
export GeneralEONegativeClosedSupport (Closed)
export GeneralEOPairedFamilyExtractionChoice (tensor_closed)
export GeneralEOPairedFamilyExtractionSupport (origin xorClosed_of_closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {m n : ℕ}

def shift {K : Type*} (f : Signature K n) (base : Fin n→Bool) : Signature K n :=
  fun x=>f (S.flip base x)

theorem flip_affine (base : Fin n→Bool) : Holant.Tractable.TwoTranslate.IsAffineMap (S.flip base) := by
  intro x y
  funext i
  simp only [S.flip,AffinePhase.xor,AffinePhase.origin]
  cases base i <;> cases x i <;> cases y i <;> rfl

theorem affine_shift_iff (f : Signature AlgebraicComplex n) (base : Fin n→Bool) :
    Affine (shift f base) ↔ Affine f := by
  constructor
  · intro h
    have hs := h.precompose (S.flip base) (flip_affine base)
    change Affine (fun x=>f (S.flip base (S.flip base x))) at hs
    simpa only [S.flip_flip] using hs
  · intro h
    exact h.precompose (S.flip base) (flip_affine base)

theorem product_shift_iff (f : Signature AlgebraicComplex n) (base : Fin n→Bool) :
    Product (shift f base) ↔ Product f := S.product_shifted_iff base f

theorem shift_origin {K : Type*} (f : Signature K n) (base : Fin n→Bool) :
    shift f base C.origin=f base := by
  simp only [shift,OrdinaryNegativeNonproductBundleSupport.flip_origin]

theorem shift_closed (f : Signature AlgebraicComplex n) (base : Fin n→Bool) (hc : C.Closed f) :
    C.Closed (shift f base) := by
  intro x y z hx hy hz
  have h := hc (S.flip base x) (S.flip base y) (S.flip base z) hx hy hz
  apply (show f (tripleXor (S.flip base x) (S.flip base y) (S.flip base z))=
    shift f base (tripleXor x y z) from ?_) ▸ h
  congr 1
  funext i
  simp only [S.flip,tripleXor]
  cases base i <;> cases x i <;> cases y i <;> cases z i <;> rfl

/-- Arity-preserving literal tensor over the original coefficient field. -/
def combined {K : Type*} [Mul K] (f : Signature K m) (g : Signature K n)
    (left : Fin m→Bool) (right : Fin n→Bool) : Signature K (m+n) := fun x=>
  shift f left (fun i=>x (Fin.castAdd n i))*shift g right (fun j=>x (Fin.natAdd m j))

theorem combined_eq (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (left : Fin m→Bool) (right : Fin n→Bool) :
    combined f g left right=T.tensor (shift f left) (shift g right) := rfl

theorem combined_origin {K : Type*} [Mul K] (f : Signature K m) (g : Signature K n)
    (left : Fin m→Bool) (right : Fin n→Bool) :
    combined f g left right C.origin=f left*g right := by
  change shift f left C.origin*shift g right C.origin=_
  rw [shift_origin,shift_origin]

theorem combined_closed (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (left : Fin m→Bool) (right : Fin n→Bool) (hf : C.Closed f) (hg : C.Closed g) :
    C.Closed (combined f g left right) := by
  rw [combined_eq]
  exact C.tensor_closed _ _ (shift_closed f left hf) (shift_closed g right hg)

theorem combined_failures (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (left : Fin m→Bool) (right : Fin n→Bool) (hl : f left≠0) (hr : g right≠0)
    (ha : ¬Affine f) (hp : ¬Product g) :
    ¬Affine (combined f g left right) ∧ ¬Product (combined f g left right) := by
  have hf : shift f left≠0 := by intro h; exact hl (by simpa only [shift_origin,Pi.zero_apply] using congrFun h C.origin)
  have hg : shift g right≠0 := by intro h; exact hr (by simpa only [shift_origin,Pi.zero_apply] using congrFun h C.origin)
  rw [combined_eq]
  exact T.tensor_failures hf hg (fun h=>ha ((affine_shift_iff f left).mp h))
    (fun h=>hp ((product_shift_iff g right).mp h))

variable (K : IntermediateField ℚ AlgebraicComplex) (f : Signature K m) (g : Signature K n)

def ambientLeft : Signature AlgebraicComplex m := fun x=>(f x : AlgebraicComplex)
def ambientRight : Signature AlgebraicComplex n := fun x=>(g x : AlgebraicComplex)

theorem coe_combined (left : Fin m→Bool) (right : Fin n→Bool) (x : Fin (m+n)→Bool) :
    ((combined f g left right x : K) : AlgebraicComplex)=
      combined (ambientLeft K f) (ambientRight K g) left right x := rfl

theorem coe_denote (left : Fin m→Bool) (right : Fin n→Bool) (q : G.Gadget (m+n) 2)
    (z : Fin 2→Bool) :
    ((G.denote (combined f g left right) q z : K) : AlgebraicComplex)=
      G.denote (combined (ambientLeft K f) (ambientRight K g) left right) q z := by
  simp only [G.denote,IntermediateField.coe_sum,OrdinaryNegativePhaseBundleChoice.coe_evaluate]
  rfl

structure Choice where
  left : Fin m→Bool
  right : Fin n→Bool
  left_nonzero : f left≠0
  right_nonzero : g right≠0
  gadget : G.Gadget (m+n) 2
  nonaffine : ¬Affine (fun z=>((G.denote (combined f g left right) gadget z : K) : AlgebraicComplex))
  nonproduct : ¬Product (fun z=>((G.denote (combined f g left right) gadget z : K) : AlgebraicComplex))

/-- Support, two class failures, and original coefficients are the only inputs;
no support base, compressed hard row, successful gadget, or source is supplied. -/
theorem exists_choice (hf : C.Closed (ambientLeft K f)) (hg : C.Closed (ambientRight K g))
    (ha : ¬Affine (ambientLeft K f)) (hp : ¬Product (ambientRight K g)) : Nonempty (Choice K f g) := by
  have hfn : ambientLeft K f≠0 := fun h=>ha (Or.inl h)
  have hgn : ambientRight K g≠0 := fun h=>hp (Or.inl h)
  obtain ⟨l,hl⟩ := Function.ne_iff.mp hfn
  obtain ⟨r,hr⟩ := Function.ne_iff.mp hgn
  have hl' : f l≠0 := by intro h; exact hl (by simp [ambientLeft,h])
  have hr' : g r≠0 := by intro h; exact hr (by simp [ambientRight,h])
  have h0 : combined (ambientLeft K f) (ambientRight K g) l r C.origin≠0 := by
    rw [combined_origin]
    exact mul_ne_zero hl hr
  have hclosed := combined_closed (ambientLeft K f) (ambientRight K g) l r hf hg
  have hbad := combined_failures (ambientLeft K f) (ambientRight K g) l r hl hr ha hp
  obtain ⟨q,hqa,hqp⟩ := U.exists_gadget _ h0 (C.xorClosed_of_closed _ h0 hclosed) hbad.1 hbad.2
  refine ⟨⟨l,r,hl',hr',q,?_,?_⟩⟩
  · simpa only [coe_denote] using hqa
  · simpa only [coe_denote] using hqp

def choose (hf : C.Closed (ambientLeft K f)) (hg : C.Closed (ambientRight K g))
    (ha : ¬Affine (ambientLeft K f)) (hp : ¬Product (ambientRight K g)) : Choice K f g :=
  Classical.choice (exists_choice K f g hf hg ha hp)

namespace Choice
variable {K f g}

def coefficient (D : Choice K f g) : Signature K 2 := G.denote (combined f g D.left D.right) D.gadget

end Choice
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSupportExtraction
end
