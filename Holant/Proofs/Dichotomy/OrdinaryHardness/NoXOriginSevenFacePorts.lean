import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginPorts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedProjection

/-! Literal port substitutions for the two parallel binary faces of a
seven-character origin chart. The two signed counts remain separate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginSevenFacePorts
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
export NoXSeparateSignedProjection (signedCount)
end I
namespace P
export NoXUnsignedRows (Positive)
end P
namespace A
export OrdinaryNegativeSparseMixingAlpha (codeThree codeSeven)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ}

def mapping (bit : Bool) : Fin 7→Port 3 :=
  ![.inl bit,.inr (0,false),.inr (1,false),.inr (2,false),
    .inr (1,bit),.inr (0,bit),.inr (2,bit)]

def ports (ps : Fin n→Port 7) (bit : Bool) : Fin n→Port 3 := fun i=>
  match ps i with
  | .inl b=>.inl b
  | .inr (q,_)=>mapping bit q

theorem mapping_code (bit : Bool) (x : Word 2) :
    word (mapping bit) (A.codeThree x)=A.codeSeven (Fin.cons bit x) := by
  have hcons : (Fin.cons bit x : Word 3)=![bit,x 0,x 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hcons]
  funext i
  fin_cases i <;> cases bit <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [OrdinaryNegativeSignedPortsCore.word,mapping,A.codeThree,A.codeSeven,h0,h1]

theorem word_code (ps : Fin n→Port 7) (positive : P.Positive ps) (bit : Bool) (x : Word 2) :
    word (ports ps bit) (A.codeThree x)=word ps (A.codeSeven (Fin.cons bit x)) := by
  funext i
  cases hi : ps i with
  | inl b=>simp [OrdinaryNegativeSignedPortsCore.word,ports,hi]
  | inr pair=>
      rcases pair with ⟨q,sgn⟩
      cases sgn
      · have hm:=congrFun (mapping_code bit x) q
        simpa [OrdinaryNegativeSignedPortsCore.word,ports,hi] using hm
      · exact False.elim (positive i q hi)

theorem count_formula (ps : Fin n→Port 7) (positive : P.Positive ps)
    (bit : Bool) (j : Fin 3) (sgn : Bool) :
    I.signedCount (ports ps bit) j sgn=
      ∑q,I.bundleSize ps q*(if mapping bit q=.inr (j,sgn) then 1 else 0) := by
  unfold I.signedCount I.bundleSize
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : ps i with
  | inl b=>simp [ports,hi]
  | inr pair=>
      rcases pair with ⟨q,sign⟩
      cases sign
      · rw [Finset.sum_eq_single q]
        · simp [ports,hi]
        · intro k _ hk
          simp [Ne.symm hk]
        · simp
      · exact False.elim (positive i q hi)

theorem positive_zero (ps : Fin n→Port 7) : P.Positive (ports ps false) := by
  intro i j
  cases hi : ps i with
  | inl b=>simp [ports,hi]
  | inr pair=>
      rcases pair with ⟨q,sgn⟩
      fin_cases q <;> simp [ports,hi,mapping]

theorem count_zero (ps : Fin n→Port 7) (positive : P.Positive ps) (j : Fin 3) :
    I.signedCount (ports ps false) j false=
      ![I.bundleSize ps 1+I.bundleSize ps 5,I.bundleSize ps 2+I.bundleSize ps 4,
        I.bundleSize ps 3+I.bundleSize ps 6] j := by
  rw [count_formula ps positive]
  fin_cases j <;> simp [Fin.sum_univ_succ,mapping]

theorem count_one (ps : Fin n→Port 7) (positive : P.Positive ps) (j : Fin 3) (bit : Bool) :
    I.signedCount (ports ps true) j bit=
      if bit then ![I.bundleSize ps 5,I.bundleSize ps 4,I.bundleSize ps 6] j
      else ![I.bundleSize ps 1,I.bundleSize ps 2,I.bundleSize ps 3] j := by
  rw [count_formula ps positive]
  fin_cases j <;> cases bit <;> simp [Fin.sum_univ_succ,mapping]

theorem bundle_of_positive {m : ℕ} (ps : Fin n→Port m) (positive : P.Positive ps) (j : Fin m) :
    I.bundleSize ps j=I.signedCount ps j false := by
  unfold I.bundleSize I.signedCount
  apply Finset.sum_congr rfl
  intro i _
  cases hi : ps i with
  | inl b=>simp
  | inr pair=>
      rcases pair with ⟨q,sgn⟩
      cases sgn
      · simp
      · exact False.elim (positive i q hi)

theorem even_zero (ps : Fin n→Port 7) (positive : P.Positive ps)
    (odd : ∀q,Odd (I.bundleSize ps q)) : ∀j,Even (I.bundleSize (ports ps false) j) := by
  intro j
  rw [bundle_of_positive _ (positive_zero ps),count_zero ps positive]
  fin_cases j <;> exact Odd.add_odd (odd _) (odd _)

theorem odd_one (ps : Fin n→Port 7) (positive : P.Positive ps)
    (odd : ∀q,Odd (I.bundleSize ps q)) : ∀j bit,Odd (I.signedCount (ports ps true) j bit) := by
  intro j bit
  rw [count_one ps positive]
  fin_cases j <;> cases bit <;> exact odd _


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginSevenFacePorts
end
