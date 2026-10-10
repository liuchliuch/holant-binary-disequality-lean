import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryPartialJoin
import Holant.Proofs.Reductions.GeneralExtraction.SupportCaps


noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryJoin
open Holant
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace PartialJoin
export GeneralOddHigherResidueQuaternaryPartialJoin
  (word block left right value value_add_left value_add_right)
end PartialJoin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem word_constant_iff {k : ℕ} (u : Fin 2 → Bool) (z : Fin k → Bool) (b : Bool) :
    PartialJoin.word u z=(fun _ => b) ↔ u=(fun _ => b) ∧ z=(fun _ => b) := by
  constructor
  · intro h
    constructor <;> funext i
    · simpa [PartialJoin.word] using congrFun h ((PartialJoin.block k).symm (.inl i))
    · simpa [PartialJoin.word] using congrFun h ((PartialJoin.block k).symm (.inr i))
  · rintro ⟨rfl,rfl⟩
    funext i
    unfold PartialJoin.word
    cases PartialJoin.block k i <;> rfl

def zeroOne : Fin 4 → Bool := ![false,false,true,true]
def oneZero : Fin 4 → Bool := ![true,true,false,false]

theorem halves_iff (w : Fin 4 → Bool) (b t : Bool) :
    PartialJoin.left w=(fun _ => b) ∧ PartialJoin.right w=(fun _ => t) ↔ w=![b,b,t,t] := by
  constructor
  · rintro ⟨hl,hr⟩
    funext i
    have hl0 := congrFun hl 0
    have hl1 := congrFun hl 1
    have hr0 := congrFun hr 0
    have hr1 := congrFun hr 1
    fin_cases i <;> assumption
  · intro h
    subst w
    constructor <;> funext i <;> fin_cases i <;> rfl

variable {K : Type*} [Field K]

def nativeTable (c : K) : Signature K 4 :=
  fun w => (if w=zeroOne then c else 0)+(if w=oneZero then c else 0)

theorem value_pins {k : ℕ} (W : Fin k → Kernel K) (c d : K) (b t : Bool) :
    PartialJoin.value W (purePin c b (k+2)) (purePin d t (k+2))=
      fun w => if PartialJoin.left w=(fun _ => b) ∧ PartialJoin.right w=(fun _ => t)
        then c*d*∏ i,W i b t else 0 := by
  classical
  funext w
  by_cases hl : PartialJoin.left w=fun _ => b
  · by_cases hr : PartialJoin.right w=fun _ => t
    · simp [PartialJoin.value,purePin,word_constant_iff,hl,hr]
    · simp [PartialJoin.value,purePin,word_constant_iff,hl,hr]
  · simp [PartialJoin.value,purePin,word_constant_iff,hl]

/-- One joined edge excludes the two equal-endpoint summands; every remaining
edge contributes exactly one. Thus the nonzero scalar is precisely α*β. -/
theorem native_value {k : ℕ} (hk : 0<k) (α β : K) :
    PartialJoin.value (fun _ : Fin k => Signature.disequality)
      (purePin α false (k+2)+purePin β true (k+2))
      (purePin α false (k+2)+purePin β true (k+2))=nativeTable (α*β) := by
  simp only [PartialJoin.value_add_left,PartialJoin.value_add_right,value_pins]
  funext w
  simp [Signature.disequality,hk.ne',halves_iff,nativeTable,zeroOne,oneZero,mul_comm,add_comm]


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryJoin
