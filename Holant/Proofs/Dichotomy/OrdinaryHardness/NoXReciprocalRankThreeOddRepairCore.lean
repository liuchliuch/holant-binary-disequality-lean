import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralUniformTranslation
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffinePorts

/-! Exact Boolean geometry of the genuine two-copy odd-seven repair. Only
three negative ports are joined; its three positive partners become the
new boundary. No sign gate or semantic coordinate flip is installed. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOddRepairCore
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word)
namespace C
export NoXReciprocalMixedProjectionCore (logical)
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
end C
set_option maxHeartbeats 800000
set_option Elab.async false
abbrev Word (n : ℕ) := Fin n→Bool

def exotic : Word 7 := ![false,false,false,true,true,true,false]
def Canonical (z : Word 7) : Prop :=
  z 3=(z 1 ^^ z 2) ∧ z 4=(z 0 ^^ z 2) ∧ z 5=(z 0 ^^ z 1) ∧ z 6=((z 0 ^^ z 1) ^^ z 2)
def Exotic (z : Word 7) : Prop := Canonical (C.logical exotic z)
instance (z : Word 7) : Decidable (Canonical z) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
instance (z : Word 7) : Decidable (Exotic z) := inferInstanceAs (Decidable (Canonical _))
def project (z : Word 7) : Word 3 := ![z 0,z 1,z 2]

theorem code_project (z : Word 7) (h : Canonical z) : C.codeSeven (project z)=z := by
  funext i
  fin_cases i <;> simp_all [Canonical,C.codeSeven,project]
theorem canonical_code (x : Word 3) : Canonical (C.codeSeven x) := by
  simp [Canonical,C.codeSeven]

theorem canonical_iff (z : Word 7) : Canonical z ↔ ∃x : Word 3,z=C.codeSeven x := by
  constructor
  · intro h
    exact ⟨project z,(code_project z h).symm⟩
  · rintro ⟨x,rfl⟩
    exact canonical_code x

def first (z : Word 7) (t : Word 3) : Word 7 := ![z 0,z 1,z 2,t 0,t 1,t 2,z 6]
def second (z : Word 7) (t : Word 3) : Word 7 := ![false,z 4,z 5,t 0,t 2,t 1,z 3]
def privateWord (z : Word 7) : Word 3 := ![!(z 3),!(z 4),!(z 5)]
def correction (z : Word 7) : Word 7 := second z (privateWord z)

theorem forced (z : Word 7) (t : Word 3) (h : Exotic (second z t)) : t=privateWord z := by
  simp [Exotic,Canonical,C.logical,exotic,second] at h
  funext i
  fin_cases i
  · have ht:=h.1
    rw [←h.2.2.2] at ht
    simpa [privateWord] using ht
  · simpa [privateWord] using congrArg Bool.not h.2.2.1
  · simpa [privateWord] using congrArg Bool.not h.2.1

theorem first_private (z : Word 7) : first z (privateWord z)=C.logical exotic z := by
  funext i
  fin_cases i <;> simp [first,privateWord,C.logical,exotic]

theorem correction_code (x : Word 3) : Exotic (correction (C.codeSeven x)) := by
  have hx:x=![x 0,x 1,x 2]:=by funext i;fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> decide

def correctionPorts : Fin 7→Port 7 :=
  ![.inl false,.inr (4,false),.inr (5,false),.inr (3,true),.inr (5,true),.inr (4,true),.inr (3,false)]
theorem word_correction (z : Word 7) : word correctionPorts z=correction z := by
  funext i
  fin_cases i <;> simp [word,correctionPorts,correction,second,privateWord]
theorem correction_even (q : Fin 7) : Even (OrdinaryNegativeSignedPortsIncidence.bundleSize correctionPorts q) := by
  fin_cases q <;> decide

theorem correction_affine : TwoTranslate.IsAffineMap correction := by
  intro x y
  funext i
  fin_cases i <;> simp [correction,second,privateWord,AffinePhase.xor,AffinePhase.origin]

variable {K : Type*} [Field K] (f : Signature K 7)
variable (support : ∀z,f z≠0 ↔ Exotic z)
include support in
theorem sum_value (z : Word 7) : (∑t : Word 3,f (first z t)*f (second z t))=
    f (C.logical exotic z)*f (correction z) := by
  classical
  rw [←first_private]
  change _=f (first z (privateWord z))*f (second z (privateWord z))
  apply Finset.sum_eq_single (privateWord z)
  · intro t _ different
    have zero:f (second z t)=0 := by
      by_contra nonzero
      exact different (forced z t ((support _).mp nonzero))
    rw [zero,mul_zero]
  · simp

include support in
theorem full (x : Word 3) : f (C.logical exotic (C.codeSeven x))*f (correction (C.codeSeven x))≠0 := by
  apply mul_ne_zero
  · apply (support _).mpr
    change Canonical (C.logical exotic (C.logical exotic (C.codeSeven x)))
    rw [NoXGeneralUniformTranslation.involution]
    exact canonical_code x
  · exact (support _).mpr (correction_code x)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOddRepairCore
