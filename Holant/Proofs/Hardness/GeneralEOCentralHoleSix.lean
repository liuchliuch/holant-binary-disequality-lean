import Holant.Proofs.Hardness.GeneralEOCentralHoleStep

/-! The six-port endpoint of MWX Lemma 52, realized by actual networks.
The two missing-coefficient branches use the physical Lemma 50 construction;
the remaining branch uses one literal directed 01 vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleSix
open Holant Holant.Tractable
namespace S
export GeneralEOCentralHoleStep (pinned_central pin_hole descent_hole)
end S
namespace C
export GeneralEOPinnedDescentCore (network slice10 slice01 central)
end C
namespace O
export GeneralEOPinnedDescentOperations (word pinned pinned_denote)
end O
namespace N
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote)
end N
namespace H
export GeneralEONegativeSupportTensor (CentralHole)
end H
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

def alpha : Fin 6 → Bool := ![true,false,true,false,false,true]
def beta : Fin 6 → Bool := ![true,false,false,true,true,false]
def gamma : Fin 6 → Bool := ![false,true,true,false,true,false]
def delta : Fin 6 → Bool := ![false,true,false,true,false,true]
def epsilon : Fin 6 → Bool := ![true,false,false,true,false,true]
def zeta : Fin 6 → Bool := ![false,true,true,false,false,true]
def q1001 : Fin 4 → Bool := ![true,false,false,true]
def q0110 : Fin 4 → Bool := ![false,true,true,false]
def q1010 : Fin 4 → Bool := ![true,false,true,false]
def q0101 : Fin 4 → Bool := ![false,true,false,true]

theorem xor_quaternary : tripleXor q1001 q0110 q1010 = q0101 := by
  funext i
  fin_cases i <;> rfl

theorem charge_quaternary : charge q0101 = 0 := by decide

/-- Old ports 2,3 become the first pair; all original vertices stay put. -/
def middle : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![2,3,0,1,4,5] : Fin 6 → Fin 6) (by decide)

/-- Old ports 4,5 become the first pair, retaining the order of ports 0–3. -/
def lastPair : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![2,3,4,5,0,1] : Fin 6 → Fin 6) (by decide)

theorem reboundary_central (T : Network K 6)
    (he : Signature.CentralSupport T.denote) (e : Equiv.Perm (Fin 6)) :
    Signature.CentralSupport (N.reboundary T e).denote := by
  intro x hx
  rw [N.reboundary_denote, Tensor.reindex_apply]
  apply he
  have hw : weight (fun i => x (e i)) = weight x :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  simpa only [hw] using hx

@[simp] theorem middle_alpha (T : Network K 6) :
    (N.reboundary T middle).denote alpha = T.denote alpha := by
  rw [N.reboundary_denote, Tensor.reindex_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem middle_beta (T : Network K 6) :
    (N.reboundary T middle).denote beta = T.denote gamma := by
  rw [N.reboundary_denote, Tensor.reindex_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem middle_gamma (T : Network K 6) :
    (N.reboundary T middle).denote gamma = T.denote beta := by
  rw [N.reboundary_denote, Tensor.reindex_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem middle_delta (T : Network K 6) :
    (N.reboundary T middle).denote delta = T.denote delta := by
  rw [N.reboundary_denote, Tensor.reindex_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem middle_epsilon (T : Network K 6) :
    (N.reboundary T middle).denote epsilon = T.denote zeta := by
  rw [N.reboundary_denote, Tensor.reindex_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem lastPair_word (T : Network K 6) (u v : Bool) (x : Fin 4 → Bool) :
    (N.reboundary T lastPair).denote (O.word u v x) =
      T.denote ![x 0,x 1,x 2,x 3,u,v] := by
  rw [N.reboundary_denote, Tensor.reindex_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

variable (T : Network K 6) (he : Signature.CentralSupport T.denote)
variable (ha : T.denote alpha ≠ 0) (hb : T.denote beta ≠ 0)

def firstOutput : Network K 4 := C.network T he q1001 q0110 q1010 ha hb

theorem firstOutput_central : Signature.CentralSupport (firstOutput T he ha hb).denote :=
  C.central T he q1001 q0110 q1010 ha hb

theorem firstOutput_hole [CharZero K] (hc : T.denote gamma ≠ 0)
    (hd : T.denote delta = 0) (hε : T.denote epsilon = 0) :
    H.CentralHole (firstOutput T he ha hb).denote := by
  apply S.descent_hole T he q1001 q0110 q1010 ha hb hc
  · rw [xor_quaternary]
    exact hε
  · rw [xor_quaternary]
    exact hd
  · rw [xor_quaternary]
    exact charge_quaternary

variable (hc : T.denote gamma ≠ 0)

inductive Branch where
  | firstPair | middlePair | lastPair
  deriving DecidableEq, Repr, Fintype

/-- The two inspected coefficients determine the pair of original ports. -/
def select : Branch := by
  classical
  exact if T.denote epsilon = 0 then .firstPair
    else if T.denote zeta = 0 then .middlePair else .lastPair

/-- Exactly the three constructive cases in the published six-port proof. -/
def branchNetwork : Branch → Network K 4
  | .firstPair => firstOutput T he ha hb
  | .middlePair => firstOutput (N.reboundary T middle) (reboundary_central T he middle)
      (by simpa using ha) (by simpa using hc)
  | .lastPair => O.pinned (N.reboundary T lastPair) false

def output : Network K 4 := branchNetwork T he ha hb hc (select T)

theorem output_central : Signature.CentralSupport (output T he ha hb hc).denote := by
  classical
  unfold output select
  split_ifs
  · exact firstOutput_central T he ha hb
  · exact firstOutput_central _ _ _ _
  · exact S.pinned_central _ (reboundary_central T he lastPair) false

theorem output_hole [CharZero K] (hd : T.denote delta = 0) :
    H.CentralHole (output T he ha hb hc).denote := by
  classical
  unfold output select
  split_ifs with hε hζ
  · exact firstOutput_hole T he ha hb hc hd hε
  · exact firstOutput_hole _ _ _ _ (by simpa using hb)
      (by simpa using hd) (by simpa using hζ)
  · apply S.pin_hole (N.reboundary T lastPair) false q1001 q0110 q1010
    · rw [lastPair_word]
      exact hε
    · rw [lastPair_word]
      exact hζ
    · rw [lastPair_word]
      exact ha
    · rw [xor_quaternary, lastPair_word]
      exact hd
    · rw [xor_quaternary]
      decide

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleSix
