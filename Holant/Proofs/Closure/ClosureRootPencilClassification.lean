import Holant.Proofs.Closure.ClosureRootPencilRuling
import Holant.Proofs.Closure.ClosureRootPencilSource

/-! Literal P/C endpoint data from the closed fixed ruling. Complementary
supports, parity, endpoint orientation and both nonzero coefficients are
produced by the frozen binary-pencil theorem, not supplied by a caller. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective

structure Complementary (m : ℕ) (U V : Signature ℂ 4) where
  ruling : Ruling m U V
  parity : Bool
  orientation : Bool
  coefficient0 : ℂ
  coefficient1 : ℂ
  coefficient0_nonzero : coefficient0 ≠ 0
  coefficient1_nonzero : coefficient1 ≠ 0
  variable0 : ruling.variable0=coefficient0 • parityAxis parity orientation
  variable1 : ruling.variable1=coefficient1 • parityAxis parity (!orientation)

def Complementary.coefficient {m : ℕ} {U V : Signature ℂ 4}
    (C : Complementary m U V) (a : Bool) : ℂ :=
  if a then C.coefficient1 else C.coefficient0

theorem Complementary.coefficient_nonzero {m : ℕ} {U V : Signature ℂ 4}
    (C : Complementary m U V) (a : Bool) : C.coefficient a ≠ 0 := by
  cases a
  · exact C.coefficient0_nonzero
  · exact C.coefficient1_nonzero

theorem Complementary.endpoint {m : ℕ} {U V : Signature ℂ 4}
    (C : Complementary m U V) (a : Bool) :
    (if a then V else U)=pairTensor C.ruling.ports C.ruling.fixed
      (C.coefficient a • parityAxis C.parity (C.orientation ^^ a)) := by
  cases a
  · simpa only [coefficient,Bool.xor_false,Bool.false_eq_true,ite_false] using C.ruling.endpoint0.trans
      (congrArg (pairTensor C.ruling.ports C.ruling.fixed) C.variable0)
  · simpa only [coefficient,Bool.xor_true,ite_true] using C.ruling.endpoint1.trans
      (congrArg (pairTensor C.ruling.ports C.ruling.fixed) C.variable1)

inductive Classification (m : ℕ) (U V : Signature ℂ 4)
  | proportional (R : Ruling m U V) (relation : BinaryProportional R.variable0 R.variable1)
  | complementary (C : Complementary m U V)

theorem classified {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    Nonempty (Classification m U V) := by
  let R := ruling hm U V samples
  rcases binary_pencil_classification_endpoints hm R.variable0 R.variable1 R.samples with
    proportional | complementary
  · exact ⟨.proportional R proportional⟩
  · obtain ⟨p,lam,alpha,hlam,halpha,forward | reverse⟩ := complementary
    · have hn : alpha ≠ 0 := by
        intro hz
        rw [hz,zero_pow (by omega : m ≠ 0)] at halpha
        norm_num at halpha
      exact ⟨.complementary ⟨R,p,false,lam,lam*alpha,hlam,mul_ne_zero hlam hn,
        forward.1,forward.2⟩⟩
    · have hn : alpha ≠ 0 := by
        intro hz
        rw [hz,zero_pow (by omega : m ≠ 0)] at halpha
        norm_num at halpha
      exact ⟨.complementary ⟨R,p,true,lam*alpha,lam,mul_ne_zero hlam hn,hlam,
        reverse.1,reverse.2⟩⟩

def classification {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    Classification m U V := Classical.choice (classified hm U V samples)

/-- Raw actual-deck source boundary. Per-sample matching, scalar and parity
remain arbitrary in the input and are aligned by the proved producer. -/
def fromRootMatching {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ ClosureSixPort.RootMatching m (pencil U V t)) :
    Classification m U V :=
  classification hm U V (fun t ht => (samples t ht).imp id ((rootMatching_iff_product m _).mp))

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
