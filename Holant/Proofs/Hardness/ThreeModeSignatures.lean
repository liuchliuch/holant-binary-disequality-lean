import Holant.Proofs.Hardness.TwoCoefficientSignatures
import Holant.Proofs.Hardness.SignedTwoCoefficientSignatures

/-! Literal self-dual three-coefficient EO signatures and proof-only spectral
coordinates. None of the three projectors is declared an oracle signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeSignatures
open Holant
open Holant.LocalDrafts.Hardness.EightVertexNonexception
variable {K : Type*} [Field K]

def original (a b c : K) : Signature K 4 := table ⟨0,a,c,b,b,c,a,0⟩
def spectral (u v w : K) : Signature K 4 :=
  table ⟨0,(v-w)/2,u,(v+w)/2,(v+w)/2,u,(v-w)/2,0⟩

theorem self_dual (a b c : K) (x : Fin 4 → Bool) :
    original a b c (fun i=>!x i)=original a b c x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [original,table,h0,h1,h2,h3]

theorem eo (a b c : K) : DenseEOUnitLocal.EOSupport (original a b c) := by
  intro x hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [weight,show (Finset.univ : Finset (Fin 4))={0,1,2,3} by decide,
      Finset.filter_insert,Finset.filter_singleton,h0,h1,h2,h3] at hx <;>
    simp [original,table,h0,h1,h2,h3]

theorem middle (a b c : K) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    DenseEOUnitLocal.NonzeroMiddle (original a b c) := by
  simp [DenseEOUnitLocal.NonzeroMiddle,entries,original,table,ha,hb,hc]

variable [CharZero K]

theorem original_spectral (a b c : K) : original a b c=spectral c (a+b) (b-a) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [original,spectral,table,h0,h1,h2,h3] <;> ring

theorem spectral_linear (u v w : K) :
    spectral u v w=u • ExactTwoSignatures.E+
      v • ((1/2 : K) • ExactTwoSignatures.B)+
      w • ((-1/2 : K) • SignedTwoCoefficientSignatures.Bminus) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [spectral,ExactTwoSignatures.E,ExactTwoSignatures.B,
      SignedTwoCoefficientSignatures.Bminus,table,h0,h1,h2,h3] <;> ring

@[simp] theorem spectral_target (u : K) : spectral u 0 0=u • ExactTwoSignatures.E := by
  rw [spectral_linear]
  simp

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeSignatures
