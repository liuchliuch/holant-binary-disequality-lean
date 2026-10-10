import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSystematicSupport

/-! Every actual original coordinate of the internally chosen support chart
is an explicit signed binary character. Selected original ports recover the
logical word exactly; no compressed row is promoted to a physical resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineCharacters
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.FlatNetwork
open OrdinaryNegativeAffineSystematicSupport
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n r : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)

/-- Each mask is read off the original port's actual basis values. -/
def mask (j : Fin n) : Fin r→ZMod 2 := fun i=>
  bitValue (ZMod 2) (D.encode (basis i) j)-bitValue (ZMod 2) (D.encode (origin r) j)

def character (j : Fin n) (x : Word r) : Bool := boolEquiv.symm (TwoTranslate.dot (mask D j) x)

theorem coordinate_vector (j : Fin n) (x : Word r) :
    bitValue (ZMod 2) (D.encode x j)=
      bitValue (ZMod 2) (D.encode (origin r) j)+TwoTranslate.dot (mask D j) x := by
  let q : Word r→ZMod 2 := fun y=>
    bitValue (ZMod 2) (D.encode y j)-bitValue (ZMod 2) (D.encode (origin r) j)
  have hq0 : q (origin r)=0 := by simp [q]
  have hq (y z : Word r) : q (xor y z)=q y+q z := by
    dsimp [q]
    rw [D.affine y z]
    simp only [AffinePhase.xor,bitValue_xor]
    ring_nf
    have h2 : (2 : ZMod 2)=0 := by decide
    simp [h2]
  have equal : q=fun y=>TwoTranslate.dot (mask D j) y :=
    additive_word_eq _ _ hq0 (by simp) hq
      (by intro y z;rw [dot_xor]) (by intro i;simp [q,mask])
  have h := congrFun equal x
  dsimp [q] at h
  linear_combination h

/-- The original port is its actual base bit XOR its explicitly computed
binary character, including constant coordinates (zero masks). -/
theorem coordinate_signed (j : Fin n) (x : Word r) :
    D.encode x j=Bool.xor (D.encode (origin r) j) (character D j x) := by
  apply boolEquiv.injective
  change bitValue (ZMod 2) (D.encode x j)=bitValue (ZMod 2)
    (Bool.xor (D.encode (origin r) j) (character D j x))
  rw [bitValue_xor,coordinate_vector D j x]
  congr 1
  exact (boolEquiv.apply_symm_apply _).symm

/-- An actual information port carries exactly its singleton character. -/
theorem mask_selected (j i : Fin r) : mask D (D.ports j) i=if i=j then 1 else 0 := by
  simp only [mask,D.free,origin,bitValue_false,sub_zero]
  by_cases h : i=j
  · subst i;simp [basis]
  · have h' : j≠i := Ne.symm h
    simp [basis,h,h']

theorem selected_recovery (x : Word r) : (fun i=>D.encode x (D.ports i))=x := by
  funext i;exact D.free x i

/-- Zero masks are precisely fixed coordinates of the original support. -/
theorem mask_zero_iff (j : Fin n) : mask D j=0 ↔ ∀x,D.encode x j=D.encode (origin r) j := by
  constructor
  · intro hm x
    rw [coordinate_signed]
    have hc : character D j x=false := by
      apply boolEquiv.injective
      change boolEquiv (boolEquiv.symm (TwoTranslate.dot (mask D j) x))=boolEquiv false
      simp [hm,TwoTranslate.dot,boolEquiv]
    rw [hc,Bool.xor_false]
  · intro h
    funext i
    simp [mask,h (basis i)]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineCharacters
end
