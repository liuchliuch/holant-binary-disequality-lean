import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinNormalized
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnarySignedPairConversion
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternaryForm

/-! A paired normal form at a supported-word pivot is an explicitly signed
paired form of the actual graph. Its row/column permutation and determinant
are retained exactly, then the proved physical signed conversion is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinSignedRecover
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain OrdinaryNegativeCubicGadgets
namespace F
export GlobalCloseCompletionUnaryBitFlip (value word value_twice)
end F
namespace A
export GlobalCloseCompletionUnarySignedPairAlgebra (row)
end A
namespace Q
export GlobalCloseCompletionUnaryQuaternaryForm (Paired determinant)
end Q
namespace D
export GlobalCloseCompletionUnaryBothPinNormalized (Data)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K]

def compressed (f : Signature K 4) : Matrix Bool Bool K := fun p q=>f ![p,p,q,q]

theorem row_value (f : Signature K 4) (support : Q.Paired f) : f=A.row (compressed f) false false := by
  funext x
  have word : x=![x 0,x 1,x 2,x 3] := by funext i;fin_cases i <;>rfl
  rw [word]
  cases h0 : x 0 <;>cases h1 : x 1 <;>cases h2 : x 2 <;>cases h3 : x 3 <;>
    simp [A.row,compressed,h0,h1,h2,h3]
  all_goals apply support <;>simp

theorem compressed_det (f : Signature K 4) : (compressed f).det=Q.determinant f := by
  rw [Holant.Complexity.BinaryInterpolation.det_entries]
  rfl

def flipMatrix (B : Matrix Bool Bool K) (s t : Bool) : Matrix Bool Bool K := fun p q=>B (p^^s) (q^^t)

theorem xor_equation (a b s t : Bool) : ((a^^s)=(b^^t))↔a=(b^^(t^^s)) := by
  cases a <;>cases b <;>cases s <;>cases t <;>decide

theorem recovered_value (B : Matrix Bool Bool K) (mask : Fin 4→Bool) :
    F.value mask (A.row B false false)=
      A.row (flipMatrix B (mask 0) (mask 2)) (mask 0^^mask 1) (mask 2^^mask 3) := by
  funext x
  simp only [F.value,F.word,A.row,Bool.xor_false,flipMatrix]
  simp only [xor_equation]

theorem flipped_det (B : Matrix Bool Bool K) (s t : Bool) :
    (flipMatrix B s t).det=(if s=t then 1 else -1)*B.det := by
  rw [Holant.Complexity.BinaryInterpolation.det_entries,Holant.Complexity.BinaryInterpolation.det_entries]
  cases s <;>cases t <;>simp [flipMatrix] <;>ring

theorem flipped_nonsingular (B : Matrix Bool Bool K) (s t : Bool) (det : B.det≠0) :
    (flipMatrix B s t).det≠0 := by
  rw [flipped_det]
  exact mul_ne_zero (by split_ifs <;>simp) det

variable {r : ℕ} {a : ℕ→ℕ} (H : (i : Fin r)→Signature K (a i.val))
variable (N : D.Data H 4) (support : Q.Paired N.value) (det : Q.determinant N.value≠0)

include support in
theorem actual_value : N.actual.network.denote=
    A.row (flipMatrix (compressed N.value) (N.mask 0) (N.mask 2))
      (N.mask 0^^N.mask 1) (N.mask 2^^N.mask 3) := by
  have h:=congrArg (F.value N.mask) (row_value N.value support)
  change F.value N.mask (F.value N.mask N.actual.network.denote)=_ at h
  rw [F.value_twice,recovered_value] at h
  exact h

include det in
theorem actual_det : (flipMatrix (compressed N.value) (N.mask 0) (N.mask 2)).det≠0 := by
  apply flipped_nonsingular
  rwa [compressed_det]

variable (pins : Bool→Macro H 1) (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)

def produce : GlobalCloseCompletionUnarySignedPairConversion.Output (H:=H) :=
  GlobalCloseCompletionUnarySignedPairConversion.produce pins pinsForm
    (show Macro H 4 from ⟨N.actual.network,N.actual.labels,N.actual.exact,N.actual.ordinary⟩)
    (flipMatrix (compressed N.value) (N.mask 0) (N.mask 2))
    (N.mask 0^^N.mask 1) (N.mask 2^^N.mask 3) (actual_value H N support) (actual_det H N det)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinSignedRecover
end
