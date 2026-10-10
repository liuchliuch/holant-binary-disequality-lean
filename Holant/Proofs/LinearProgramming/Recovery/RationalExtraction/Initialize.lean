import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.FloorProgram
import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Programs

set_option autoImplicit false

/-! Kernel-checked recovery component. From the original endpoint bytes, floor(lo) either gives
an integer answer or creates determinant-one neighbors enclosing the entire
interval. Signed endpoints need no supplied shift, positive-chart witness or
precomputed continued fraction.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Initialize
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
noncomputable section

def base (q : Query) : ℤ := FloorProgram.value (lo q)
def initialNeighbors (q : Query) : Neighbors := ((base q,1),(base q+1,1))
def value (q : Query) : Result :=
  if lo q≤(base q:ℚ) then hit (base q:ℚ) (initialNeighbors q)
  else if ((base q+1:ℤ):ℚ)≤hi q then hit ((base q+1:ℤ):ℚ) (initialNeighbors q)
  else pending (initialNeighbors q)

def endpoints : Computes queryEncoding RationalArithmetic.inputEncoding (fun q : Query => q.1) :=
  Wiring.firstComputes _ _
def lower : Computes queryEncoding rationalEncoding lo := endpoints.andThen RationalArithmetic.firstComputes
def upper : Computes queryEncoding rationalEncoding hi := endpoints.andThen RationalArithmetic.secondComputes
def baseComputes : Computes queryEncoding IntegerArithmetic.encoding base := lower.andThen FloorProgram.computes
def successor : Computes queryEncoding IntegerArithmetic.encoding (fun q : Query => base q+1) :=
  (pairComputes baseComputes (constantComputes queryEncoding IntegerArithmetic.encoding 1)).andThen
    RationalArithmetic.integerAdditionComputes
def castBase : Computes queryEncoding rationalEncoding (fun q : Query => (base q:ℚ)) :=
  congrComputes ((pairComputes baseComputes (constantComputes queryEncoding encodingNatBool 1)).andThen
    RationalArithmetic.normalizationForwardComputes) (fun q => by simp [Rat.mkRat_eq_div])
def castSuccessor : Computes queryEncoding rationalEncoding (fun q : Query => ((base q+1:ℤ):ℚ)) :=
  congrComputes ((pairComputes successor (constantComputes queryEncoding encodingNatBool 1)).andThen
    RationalArithmetic.normalizationForwardComputes) (fun q => by simp [Rat.mkRat_eq_div])
def neighborsComputes : Computes queryEncoding neighborsEncoding initialNeighbors :=
  pairComputes (pairComputes baseComputes (constantComputes queryEncoding encodingNatBool 1))
    (pairComputes successor (constantComputes queryEncoding encodingNatBool 1))
def atInteger : Computes queryEncoding encodingBoolBool (fun q : Query => decide (lo q≤(base q:ℚ))) :=
  (pairComputes lower castBase).andThen Comparison.rationalLe
def crossesInteger : Computes queryEncoding encodingBoolBool
    (fun q : Query => decide (((base q+1:ℤ):ℚ)≤hi q)) :=
  (pairComputes castSuccessor upper).andThen Comparison.rationalLe
def firstAnswer : Computes queryEncoding resultEncoding
    (fun q : Query => hit (base q:ℚ) (initialNeighbors q)) :=
  pairComputes (pairComputes (constantComputes queryEncoding encodingBoolBool true)
    (constantComputes queryEncoding encodingBoolBool true)) (pairComputes castBase neighborsComputes)
def secondAnswer : Computes queryEncoding resultEncoding
    (fun q : Query => hit ((base q+1:ℤ):ℚ) (initialNeighbors q)) :=
  pairComputes (pairComputes (constantComputes queryEncoding encodingBoolBool true)
    (constantComputes queryEncoding encodingBoolBool true)) (pairComputes castSuccessor neighborsComputes)
def unfinished : Computes queryEncoding resultEncoding (fun q => pending (initialNeighbors q)) :=
  pairComputes (pairComputes (constantComputes queryEncoding encodingBoolBool false)
    (constantComputes queryEncoding encodingBoolBool false))
    (pairComputes (constantComputes queryEncoding rationalEncoding 0) neighborsComputes)
def computes : Computes queryEncoding resultEncoding value :=
  congrComputes (ifComputes atInteger firstAnswer (ifComputes crossesInteger secondAnswer unfinished))
    (fun q => by simp [value])

theorem adjacent (q : Query) : Neighbors.adjacent (initialNeighbors q) := by
  simp [Neighbors.adjacent,initialNeighbors]
theorem safe (q : Query) (hq : Valid q) : Jump.Safe q (value q) := by
  have hb := FloorProgram.bounds (lo q)
  change (base q:ℚ)≤lo q ∧ lo q<(base q:ℚ)+1 at hb
  have hcap : 1≤cap q := Nat.succ_le_iff.mpr hq.2
  by_cases h0 : lo q≤(base q:ℚ)
  · have hx : Candidate q (base q:ℚ) := ⟨h0,hb.1.trans hq.1,by simpa using hcap⟩
    simp only [value,h0,if_pos,Jump.Safe,done,found,hit,answer,neighbors]
    exact ⟨by intro _ _; exact hx,by simp,by simp⟩
  · by_cases h1 : ((base q+1:ℤ):ℚ)≤hi q
    · have hx : Candidate q ((base q+1:ℤ):ℚ) :=
        ⟨by simpa using hb.2.le,h1,by simpa using hcap⟩
      simp only [value,h0,if_neg,h1,if_pos,Jump.Safe,done,found,hit,answer,neighbors]
      exact ⟨by intro _ _; exact hx,by simp,by simp⟩
    · have hbr : Neighbors.Brackets q (initialNeighbors q) := by
        refine ⟨adjacent q,?_,?_⟩
        · simpa [initialNeighbors,Fraction.value_eq] using lt_of_not_ge h0
        · simpa [initialNeighbors,Fraction.value_eq] using lt_of_not_ge h1
      simp only [value,h0,h1,if_neg,Jump.Safe,done,found,pending,answer,neighbors]
      exact ⟨by simp,by simp,by intro _; exact hbr⟩

/-- Initial Euclidean cross distances sum to the canonical endpoint denominator.
This is the origin of the bit fuel; no search bound of magnitude D is used. -/
theorem initial_cross_sum (q : Query) :
    Fraction.lowerCross (lo q) (initialNeighbors q).1+
      Fraction.upperCross (lo q) (initialNeighbors q).2=(lo q).den := by
  dsimp [Fraction.lowerCross,Fraction.upperCross,initialNeighbors]
  ring

end
end Initialize
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
