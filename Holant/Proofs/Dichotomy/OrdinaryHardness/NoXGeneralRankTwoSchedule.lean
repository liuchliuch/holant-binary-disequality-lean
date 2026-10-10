import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoFaces
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralParityBool
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoRegularize
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalEvenCharacterPhase

/-! A fixed seven-copy original-row schedule implements the exact rank-two
separate-sign parity certificate. The unused correction slots are supported
constant pinnings, so their coefficients are preserved rather than discarded. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoSchedule
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXSeparateSignedProjection (signedCount)
end P
namespace F
export NoXGeneralRankTwoFaces (ports lineCount)
end F
namespace C
export NoXGeneralRankTwoParity (generator repair TotalOdd BothOdd exceptional_or_repair)
end C
namespace B
export NoXGeneralParityBool (even_iff odd_iff conditional cancel)
end B
namespace R
export OrdinaryNegativeRankTwoRegularize (basePort base_word)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ} (p : Fin n→Port 3)

def positive : Fin 3→Bool := fun j=>Nat.bodd (P.signedCount p j false)
def negative : Fin 3→Bool := fun j=>Nat.bodd (P.signedCount p j true)

theorem line_parity (i : Fin 4) :
    (Nat.bodd (F.lineCount p i false),Nat.bodd (F.lineCount p i true))=C.generator (positive p) (negative p) i := by
  fin_cases i <;> simp [F.lineCount,C.generator,positive,negative,Nat.bodd_add]

theorem base_count (j : Fin 3) (bit : Bool) : P.signedCount (R.basePort p) j bit=0 := by
  unfold P.signedCount
  apply Finset.sum_eq_zero
  intro i _
  cases h : p i with
  | inl b=>simp [R.basePort,h]
  | inr q=>rcases q with ⟨a,b⟩;simp [R.basePort,h]

def flag (flags : Fin 3→Bool×Bool) (reverse : Bool) (j : Fin 3) : Bool :=
  if reverse then (flags j).2 else (flags j).1

def correction (i : Fin 4) (flags : Fin 3→Bool×Bool) (reverse : Bool) (j : Fin 3) : Fin n→Port 3 :=
  if flag flags reverse j then F.ports p i j reverse else R.basePort p

def rows (i : Fin 4) (flags : Fin 3→Bool×Bool) : Fin 7→Fin n→Port 3 :=
  Fin.cases p (Fin.addCases (m:=3) (n:=3) (motive:=fun _=>Fin n→Port 3)
    (correction p i flags false) (correction p i flags true))

theorem correction_count (i : Fin 4) (flags : Fin 3→Bool×Bool) (reverse : Bool) (j q : Fin 3) (bit : Bool) :
    P.signedCount (correction p i flags reverse j) q bit=
      if j=q then (if flag flags reverse j then F.lineCount p i (bit ^^ reverse) else 0) else 0 := by
  cases h : flag flags reverse j <;> simp [correction,h,base_count,NoXGeneralRankTwoFaces.signed_count]

theorem count (i : Fin 4) (flags : Fin 3→Bool×Bool) (q : Fin 3) (bit : Bool) :
    (∑v : Fin 7,P.signedCount (rows p i flags v) q bit)=
      (P.signedCount p q bit+(if (flags q).1 then F.lineCount p i bit else 0))+
        (if (flags q).2 then F.lineCount p i (!bit) else 0) := by
  rw [Fin.sum_univ_succ]
  simp only [rows,Fin.cases_zero,Fin.cases_succ]
  rw [Fin.sum_univ_add (a:=3) (b:=3)]
  simp only [Fin.addCases_left,Fin.addCases_right,correction_count,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    flag,Bool.false_eq_true,ite_false,Bool.xor_false,Bool.xor_true]
  omega

variable (i : Fin 4) (flags : Fin 3→Bool×Bool)
variable (repairs : ∀j,C.repair (C.generator (positive p) (negative p) i) (flags j)=(positive p j,negative p j))
include repairs in
theorem even_counts (q : Fin 3) (bit : Bool) : Even (∑v : Fin 7,P.signedCount (rows p i flags v) q bit) := by
  rw [count,B.even_iff,Nat.bodd_add,Nat.bodd_add,B.conditional,B.conditional]
  have h:=repairs q
  rw [←line_parity p i] at h
  cases bit
  · exact B.cancel _ _ _ (congrArg Prod.fst h).symm
  · exact B.cancel _ _ _ (congrArg Prod.snd h).symm

/-- The two genuine exceptional parity patterns, or a complete physical
seven-copy schedule with separate even counts. -/
theorem choose :
    (∀j,Odd (OrdinaryNegativeSignedPortsIncidence.bundleSize p j)) ∨
    (∀j bit,Odd (P.signedCount p j bit)) ∨
    ∃i : Fin 4,∃flags : Fin 3→Bool×Bool,∀q bit,Even (∑v : Fin 7,P.signedCount (rows p i flags v) q bit) := by
  rcases C.exceptional_or_repair (positive p) (negative p) with total|both|⟨i,flags,repair⟩
  · left
    intro j
    rw [B.odd_iff,←NoXLocalEvenCharacterPhase.totalCount p j,Fintype.sum_bool,Nat.bodd_add]
    simpa only [positive,negative,Bool.xor_comm] using total j
  · right;left
    intro j bit
    rw [B.odd_iff]
    cases bit
    · exact (both j).1
    · exact (both j).2
  · right;right
    exact ⟨i,flags,even_counts p i flags repair⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoSchedule
end
