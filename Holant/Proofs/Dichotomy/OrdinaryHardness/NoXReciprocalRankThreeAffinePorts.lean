import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreePorts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedProjection

/-! Proper affine face substitutions retain every sign in the original
port map. A face may fix its coordinate at either supported bit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeAffinePorts
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word)
namespace P
export OrdinaryNegativeSparseRankThreeParity (Transform bits value image linearWord linearWord_pin linearWord_affine)
end P
namespace A
export OrdinaryNegativeSparseMixingAlpha (codeSeven codeSeven_affine)
end A
namespace R
export OrdinaryNegativeSparseRankThreePorts (port word_code)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
structure Transform where
  base : P.Transform
  shift : Fin 8
  deriving DecidableEq, Fintype

def input (t : Transform) (x : Fin 3→Bool) : Fin 3→Bool :=
  AffinePhase.xor (P.bits t.shift) (P.linearWord t.base x)

def offset (t : Transform) (j : Fin 7) : Bool := P.value j.succ (P.bits t.shift)

theorem input_pin (t : Transform) (x : Fin 3→Bool) : input t x t.base.axis=P.bits t.shift t.base.axis := by
  simp [input,AffinePhase.xor,P.linearWord_pin]

theorem input_affine (t : Transform) : TwoTranslate.IsAffineMap (input t) := by
  intro x y
  funext i
  have h:=congrFun (P.linearWord_affine t.base x y) i
  simp only [AffinePhase.xor] at h
  simp only [input,AffinePhase.xor]
  rw [h]
  cases P.bits t.shift i <;> cases P.linearWord t.base x i <;>
    cases P.linearWord t.base y i <;> cases P.linearWord t.base (AffinePhase.origin 3) i <;> rfl

theorem code_add (a b : Fin 3→Bool) (j : Fin 7) :
    A.codeSeven (AffinePhase.xor a b) j=(A.codeSeven a j ^^ A.codeSeven b j) := by
  revert a b j
  decide

theorem succ_value (j : Fin 7) (x : Fin 3→Bool) : P.value j.succ x=A.codeSeven x j := by
  simp [P.value]

theorem code_input (t : Transform) (j : Fin 7) (x : Fin 3→Bool) :
    A.codeSeven (input t x) j=(offset t j ^^ P.value (P.image t.base j) x) := by
  rw [input,code_add,OrdinaryNegativeSparseRankThreeParity.image_value]
  rw [offset,succ_value]

variable {n : ℕ}
def transformed (p : Fin n→Port 7) (t : Transform) (i : Fin n) : Port 7 :=
  match p i with
  | .inl b=>.inl b
  | .inr (j,b)=>if h:P.image t.base j=0 then .inl (b ^^ offset t j) else
      .inr (⟨(P.image t.base j).val-1,by have hl:=(P.image t.base j).isLt;have hn:=(P.image t.base j).pos_iff_ne_zero.mpr h;omega⟩,
        b ^^ offset t j)

theorem transformed_word (p : Fin n→Port 7) (t : Transform) (x : Fin 3→Bool) :
    word (transformed p t) (A.codeSeven x)=word p (A.codeSeven (input t x)) := by
  funext i
  cases hi:p i with
  | inl b=>simp [word,transformed,hi]
  | inr q=>
    rcases q with ⟨j,b⟩
    rw [show word p (A.codeSeven (input t x)) i= (b ^^ A.codeSeven (input t x) j) by simp [word,hi],code_input]
    by_cases hz:P.image t.base j=0
    · simp [transformed,word,hi,hz,P.value]
    · simp [transformed,word,hi,hz,P.value,Bool.xor_assoc]

variable {f : Signature AlgebraicComplex n}
variable (D : OrdinaryNegativeAffineSystematicSupport.SystematicSupport f 3)
theorem transformed_code (t : Transform) (x : Fin 3→Bool) :
    word (transformed (R.port D) t) (A.codeSeven x)=D.encode (input t x) := by
  rw [transformed_word,R.word_code]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeAffinePorts
end
