import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixBellCoordinates
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixFiniteForms
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncoding

/-! Reconstruction of the original six-port tensor from its four actual Bell
cards, with the literal factor one-half and one common scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixReconstruction
open Holant
namespace B
export GlobalCloseCompletionKleinSixBellNorm (card matrix)
end B
namespace N
export GlobalCloseCompletionKleinGramNorm (rows)
end N
namespace W
export GlobalCloseCompletionKleinGramCertificate (word pauli)
end W
namespace S
export GlobalCloseCompletionKleinRMPhaseSource (index4)
end S
namespace H
export GlobalCloseCompletionKleinH6RMBell (E bell)
end H
namespace F
export GlobalCloseCompletionKleinSixFiniteForms (tensor index6 pauli_cast)
end F
namespace D
export GlobalCloseCompletionKleinSixFiniteData (source line sign)
end D
namespace C
export GlobalCloseCompletionKleinSixBellCoordinates (Normal)
end C
namespace M
export GlobalCloseCompletionKleinSixMatchingCoordinates (sign)
end M
namespace A
export GlobalCloseCompletionKleinSixEncoding (lift source_lift)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def tailWord (x : Fin 6→Bool) : Fin 4→Bool := ![x 2,x 3,x 4,x 5]
def tailIndex (x : Fin 6→Bool) : Fin 16 := ⟨(F.index6 x).val%16,Nat.mod_lt _ (by decide)⟩

theorem first_bit : ∀x : Fin 6→Bool,(F.index6 x).val.testBit 5=x 0 := by decide +kernel
theorem second_bit : ∀x : Fin 6→Bool,(F.index6 x).val.testBit 4=x 1 := by decide +kernel
theorem tail_index : ∀x : Fin 6→Bool,tailIndex x=S.index4 (tailWord x) := by decide +kernel

theorem lift_value (e : Fin 4) (a : Fin 48) (x : Fin 6→Bool) :
    (A.lift e a (F.index6 x):ℝ)=H.E e (x 0) (x 1)*(D.line a (S.index4 (tailWord x)):ℝ) := by
  change ((W.pauli e ((F.index6 x).val.testBit 5) ((F.index6 x).val.testBit 4)*D.line a (tailIndex x):ℤ):ℝ)=_
  rw [first_bit,second_bit,tail_index,Int.cast_mul,F.pauli_cast]

theorem tensor_value (a b c : Fin 48) (s : Fin 8) (x : Fin 6→Bool) :
    F.tensor (K:=ℝ) a b c s x=
      H.E 0 (x 0) (x 1)*(D.line 0 (S.index4 (tailWord x)):ℝ)+
      (D.sign s 0:ℝ)*H.E 1 (x 0) (x 1)*(D.line a (S.index4 (tailWord x)):ℝ)+
      (D.sign s 1:ℝ)*H.E 2 (x 0) (x 1)*(D.line b (S.index4 (tailWord x)):ℝ)+
      (D.sign s 2:ℝ)*H.E 3 (x 0) (x 1)*(D.line c (S.index4 (tailWord x)):ℝ) := by
  rw [F.tensor,A.source_lift]
  simp only [Int.cast_add,Int.cast_mul,lift_value]
  ring

def phasePack (p : Fin 4→Bool) : Fin 8 :=
  ⟨(if p 1 then 1 else 0)+2*(if p 2 then 1 else 0)+4*(if p 3 then 1 else 0),by
    cases p 1 <;> cases p 2 <;> cases p 3 <;> decide⟩

theorem phase_one : ∀p : Fin 4→Bool,M.sign (p 1)=D.sign (phasePack p) 0 := by decide +kernel
theorem phase_two : ∀p : Fin 4→Bool,M.sign (p 2)=D.sign (phasePack p) 1 := by decide +kernel
theorem phase_three : ∀p : Fin 4→Bool,M.sign (p 3)=D.sign (phasePack p) 2 := by decide +kernel

theorem reconstruct (f : Signature ℝ 6) (u : Fin 2→Bool) (z : Fin 4→Bool) :
    f (Fin.addCases (m:=2) (n:=4) u z)=(1/2:ℝ)*∑k : Fin 4,H.E k (u 0) (u 1)*B.card f k z := by
  have coordinates : u=![u 0,u 1] := by funext i;fin_cases i <;> rfl
  rw [coordinates]
  cases h0 : u 0 <;> cases h1 : u 1 <;>
    norm_num [B.card,B.matrix,N.rows,W.word,H.E,H.bell,Fin.sum_univ_succ,h0,h1] <;> ring

theorem form (f : Signature ℝ 6) (R : C.Normal f) (anchor : R.label 0=0) :
    f=(R.scale/2) • F.tensor (R.label 1) (R.label 2) (R.label 3) (phasePack R.phase) := by
  funext x
  have joined : (Fin.addCases (m:=2) (n:=4) ![x 0,x 1] (tailWord x) : Fin 6→Bool)=x := by
    funext i
    fin_cases i <;> rfl
  have h := reconstruct f ![x 0,x 1] (tailWord x)
  rw [joined] at h
  have card (k : Fin 4) : B.card f k (tailWord x)=
      R.scale*(M.sign (R.phase k):ℝ)*(D.line (R.label k) (S.index4 (tailWord x)):ℝ) := by
    have h := R.value k (S.index4 (tailWord x))
    rw [GlobalCloseCompletionKleinRMPhaseSupport.word_index] at h
    exact h
  rw [h]
  change (1/2:ℝ)*(∑k : Fin 4,H.E k (x 0) (x 1)*B.card f k (tailWord x))=
    (R.scale/2)*F.tensor (R.label 1) (R.label 2) (R.label 3) (phasePack R.phase) x
  rw [tensor_value]
  simp only [card,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,anchor,R.phase_zero,M.sign,
    Bool.false_eq_true,ite_false,Int.cast_one,mul_one]
  rw [←phase_one R.phase,←phase_two R.phase,←phase_three R.phase]
  cases h1 : R.phase 1 <;> cases h2 : R.phase 2 <;> cases h3 : R.phase 3 <;>
    norm_num [M.sign,h1,h2,h3] <;> ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixReconstruction
end
