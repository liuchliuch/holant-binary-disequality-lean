import Holant.Proofs.Hardness.EightVertexCapNetwork
import Holant.Proofs.Hardness.EightVertexCancellationLocal

/-! A complementary original-coefficient region: an actual cap weights the
first original port so that p*b+q*y vanishes. The unweighted sum b+y need
not vanish. The finite cap, its exact scalar and all original corners remain
in the hypothesis and the derived tensor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCapLocal
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace Cap
export GeneralCancellationCapPin (Choice oriented)
end Cap
export EightVertexCapNetwork (output)
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K]

def p (M : Signature K 4) (k : Cap.Choice) : K := (Cap.oriented M k).1
def q (M : Signature K 4) (k : Cap.Choice) : K := (Cap.oriented M k).2

/-- Literal degree-two and degree-four tests on original M, for one of its
six loops in either orientation. No gadget-access or desired hardness premise. -/
structure Coefficients (M : Signature K 4) (k : Cap.Choice) : Prop where
  cancel : p M k*(entries M).b+q M k*(entries M).y=0
  outer : (p M k*(entries M).a)*(q M k*(entries M).x)+(p M k*(entries M).b)^2≠0
  c : p M k*(entries M).c≠0
  z : q M k*(entries M).z≠0
  sum : q M k*(entries M).w+p M k*(entries M).d≠0
  additional :
    (p M k*(entries M).c)*(q M k*(entries M).z)+(p M k*(entries M).d)^2≠0 ∨
    (p M k*(entries M).c)*(q M k*(entries M).z)+(q M k*(entries M).w)^2≠0

def Applicable (M : Signature K 4) : Prop := EvenSupport M ∧ ∃k, Coefficients M k

def selected (M : Signature K 4) : Cap.Choice := by
  classical
  exact if h : Applicable M then Classical.choose h.2 else (0,false)

theorem selected_spec (M : Signature K 4) (h : Applicable M) : Coefficients M (selected M) := by
  classical
  simpa only [selected,dite_eq_left h] using Classical.choose_spec h.2

theorem output_entries (M : Signature K 4) (k : Cap.Choice) :
    entries (output M k)=
      ⟨p M k*(entries M).a,p M k*(entries M).b,p M k*(entries M).c,p M k*(entries M).d,
       q M k*(entries M).w,q M k*(entries M).z,q M k*(entries M).y,q M k*(entries M).x⟩ := rfl

theorem output_even (M : Signature K 4) (he : EvenSupport M) (k : Cap.Choice) :
    EvenSupport (output M k) := by
  intro t ht
  simp only [output,he t ht,mul_zero]

/-- Every downstream cancellation hypothesis follows from original coefficients. -/
theorem output_applicable (M : Signature K 4) (he : EvenSupport M)
    (k : Cap.Choice) (h : Coefficients M k) :
    EightVertexCancellationLocal.Applicable (output M k) where
  even := output_even M he k
  cancel := h.cancel
  outer := h.outer
  c := h.c
  z := h.z
  sum := h.sum
  additional := h.additional

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCapLocal
