import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXUnsignedRows
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginPairConditions
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreePorts
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoPorts

/-! An origin-supported systematic chart has only positive character ports.
Exact oriented support-difference counts determine the three/seven parity
patterns without discarding any original port multiplicity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginPorts
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
namespace W
export NoXWeightedRankOneCore (negativeCount)
end W
namespace P
export NoXUnsignedRows (Positive)
end P
namespace R2
export OrdinaryNegativeRankTwoPorts (port word_code)
export OrdinaryNegativeSparseMixingAlpha (codeThree)
end R2
namespace R3
export OrdinaryNegativeSparseRankThreePorts (port word_code)
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
end R3
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n m r : ℕ}

theorem negative_word (ps : Fin n→Port m) (positive : P.Positive ps) (a b : Word m) :
    W.negativeCount (word ps a) (word ps b)=
      ∑j,I.bundleSize ps j*(if a j && !(b j) then 1 else 0) := by
  unfold W.negativeCount I.bundleSize
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases h : ps i with
  | inl bit=>cases bit <;> simp [OrdinaryNegativeSignedPortsCore.word,OrdinaryNegativeRankOneCore.neg,h]
  | inr pair=>
      rcases pair with ⟨k,sgn⟩
      cases sgn
      · rw [Finset.sum_eq_single k]
        · cases ha : a k <;> cases hb : b k <;>
            simp [OrdinaryNegativeSignedPortsCore.word,OrdinaryNegativeRankOneCore.neg,h,ha,hb]
        · intro j _ hj
          simp [Ne.symm hj]
        · simp
      · exact False.elim (positive i k h)

variable {f : Signature AlgebraicComplex n}

theorem encode_origin (D : SystematicSupport f r) (base : f (origin n)≠0) : D.encode (origin r)=origin n :=
  D.covers (origin n) base

theorem two_positive (D : SystematicSupport f 2) (base : f (origin n)≠0) : P.Positive (R2.port D) := by
  intro i j
  have he : D.encode ![false,false] i=false := by
    have word : (![false,false] : Word 2)=origin 2 := by funext q;fin_cases q <;> rfl
    rw [word,encode_origin D base]
    rfl
  unfold R2.port
  simp only [he,Bool.false_xor]
  split_ifs <;> simp

theorem seven_positive (D : SystematicSupport f 3) (base : f (origin n)≠0) : P.Positive (R3.port D) := by
  intro i j
  have he : D.encode (origin 3) i=false := by rw [encode_origin D base];rfl
  simp only [R3.port,he]
  split_ifs <;> simp

theorem even_add_mod {a b : ℕ} (h : Even (a+b)) : a%2=b%2 := by
  have ha:=Nat.mod_lt a (by decide : 0<2)
  have hb:=Nat.mod_lt b (by decide : 0<2)
  have he : (a+b)%2=0 := Nat.even_iff.mp h
  omega

section Two
variable (D : SystematicSupport f 2) (base : f (origin n)≠0)
variable (pairs : ∀a b : Word 2,Even (W.negativeCount (D.encode a) (D.encode b)))

include base pairs in
theorem two_even : ∀j,Even (I.bundleSize (R2.port D) j) := by
  have h0:=pairs ![true,false] ![false,true]
  have h1:=pairs ![true,true] ![true,false]
  have h2:=pairs ![true,false] ![true,true]
  have formula (a b : Word 2) : W.negativeCount (D.encode a) (D.encode b)=
      ∑j,I.bundleSize (R2.port D) j*(if R2.codeThree a j && !(R2.codeThree b j) then 1 else 0) := by
    rw [←R2.word_code D a,←R2.word_code D b,negative_word _ (two_positive D base)]
  rw [formula] at h0 h1 h2
  simp only [Fin.sum_univ_three,R2.codeThree] at h0 h1 h2
  norm_num at h0 h1 h2
  intro j
  fin_cases j <;> assumption
end Two

section Seven
variable (D : SystematicSupport f 3) (base : f (origin n)≠0)
variable (pairs : ∀a b : Word 3,Even (W.negativeCount (D.encode a) (D.encode b)))

include base pairs in
theorem seven_even_or_odd : (∀j,Even (I.bundleSize (R3.port D) j)) ∨
    (∀j,Odd (I.bundleSize (R3.port D) j)) := by
  let c := I.bundleSize (R3.port D)
  have formula (a b : Word 3) : W.negativeCount (D.encode a) (D.encode b)=
      ∑j,c j*(if R3.codeSeven a j && !(R3.codeSeven b j) then 1 else 0) := by
    rw [←R3.word_code D a,←R3.word_code D b,negative_word _ (seven_positive D base)]
  have h04:=pairs ![true,false,false] ![false,true,false]
  have h05:=pairs ![true,false,false] ![false,false,true]
  have h15:=pairs ![false,true,false] ![false,false,true]
  have h13:=pairs ![false,true,false] ![true,false,false]
  have h23:=pairs ![false,false,true] ![true,false,false]
  have h06:=pairs ![true,false,false] ![false,true,true]
  rw [formula] at h04 h05 h15 h13 h23 h06
  norm_num [Fin.sum_univ_succ,R3.codeSeven] at h04 h05 h15 h13 h23 h06
  have e04:=even_add_mod h04
  have e05:=even_add_mod h05
  have e15:=even_add_mod h15
  have e13:=even_add_mod h13
  have e23:=even_add_mod h23
  have e06:=even_add_mod h06
  have all (j : Fin 7) : c j%2=c 0%2 := by
    fin_cases j
    · rfl
    · exact e15.trans e05.symm
    · exact e23.trans (e13.symm.trans (e15.trans e05.symm))
    · exact e13.symm.trans (e15.trans e05.symm)
    · exact e04.symm
    · exact e05.symm
    · exact e06.symm
  rcases Nat.even_or_odd (c 0) with even|odd
  · left
    intro j
    exact Nat.even_iff.mpr ((all j).trans (Nat.even_iff.mp even))
  · right
    intro j
    exact Nat.odd_iff.mpr ((all j).trans (Nat.odd_iff.mp odd))
end Seven


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginPorts
end
