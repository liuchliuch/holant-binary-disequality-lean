import Holant.Dihedral.TwoCardLocalization.Program
import Holant.Certificates.MatchingContractionClosure.Presentation

/-! Exact correspondence between named original surviving ports and the
ordered smaller signature used by the actual contraction program. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open Holant.Certificates
variable {n : ℕ}

def remainingOrder (u v : Fin (n+2)) (huv : u ≠ v) : Fin n ≃ MatchingContractionClosure.Remaining u v where
  toFun j := ⟨pairOrder u v j.succ.succ,by
    constructor
    · intro h
      exact Fin.succ_ne_zero j.succ ((pairOrder u v).injective (h.trans (pairOrder_first u v huv).symm))
    · intro h
      exact Fin.succ_succ_ne_one j ((pairOrder u v).injective (h.trans (pairOrder_second u v).symm))⟩
  invFun x := ⟨((pairOrder u v).symm x.val).val-2,by
    have h0 : (pairOrder u v).symm x.val ≠ 0 := by
      intro h; apply x.property.1
      have hh := congrArg (pairOrder u v) h
      simpa [pairOrder_first u v huv] using hh
    have h1 : (pairOrder u v).symm x.val ≠ 1 := by
      intro h; apply x.property.2
      have hh := congrArg (pairOrder u v) h
      simpa [pairOrder_second u v] using hh
    have hh0 : ((pairOrder u v).symm x.val).val ≠ 0 := by
      intro hh; apply h0; apply Fin.ext; exact hh
    have hh1 : ((pairOrder u v).symm x.val).val ≠ 1 := by
      intro hh; apply h1; apply Fin.ext
      simpa only [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1<n+2)] using hh
    omega⟩
  left_inv j := by apply Fin.ext; simp only [Equiv.symm_apply_apply,Fin.val_succ]; omega
  right_inv x := by
    apply Subtype.ext
    apply (pairOrder u v).symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Fin.ext
    simp only [Fin.val_succ]
    have h0 : (pairOrder u v).symm x.val ≠ 0 := by
      intro h; apply x.property.1
      have hh := congrArg (pairOrder u v) h
      simpa [pairOrder_first u v huv] using hh
    have h1 : (pairOrder u v).symm x.val ≠ 1 := by
      intro h; apply x.property.2
      have hh := congrArg (pairOrder u v) h
      simpa [pairOrder_second u v] using hh
    have hh0 : ((pairOrder u v).symm x.val).val ≠ 0 := by
      intro hh; apply h0; apply Fin.ext; exact hh
    have hh1 : ((pairOrder u v).symm x.val).val ≠ 1 := by
      intro hh; apply h1; apply Fin.ext
      simpa only [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1<n+2)] using hh
    omega

variable {K : Type*} [Field K]

theorem contractPair_order (u v : Fin (n+2)) (huv : u ≠ v) (C : Kernel K)
    (q : Signature K (n+2)) :
    Tensor.reindex (remainingOrder u v huv).symm (MatchingContractionClosure.contractPair u v C q) =
      Signature.contract C (Tensor.reindex (pairOrder u v).symm q) := by
  funext x
  let y : MatchingContractionClosure.Remaining u v → Bool := fun z => x ((remainingOrder u v huv).symm z)
  have hw (a b : Bool) : MatchingContractionClosure.insertPair u v a b (MatchingContractionClosure.extendRemaining u v y) =
      fun i => pair a b x ((pairOrder u v).symm i) := by
    have h := insertPair_order (pairOrder u v) a b (MatchingContractionClosure.extendRemaining u v y)
    rw [pairOrder_first u v huv,pairOrder_second u v] at h
    change MatchingContractionClosure.insertPair u v a b (MatchingContractionClosure.extendRemaining u v y)=_ at h
    have hrest : (fun j : Fin n => MatchingContractionClosure.extendRemaining u v y (pairOrder u v j.succ.succ)) = x := by
      funext j
      change MatchingContractionClosure.extendRemaining u v y (remainingOrder u v huv j).val=x j
      rw [MatchingContractionClosure.extendRemaining_apply]
      simp [y]
    rw [h,hrest]
  simp only [Tensor.reindex,MatchingContractionClosure.contractPair,Signature.contract]
  change (∑ a : Bool,∑ b : Bool,C a b*q (MatchingContractionClosure.insertPair u v a b (MatchingContractionClosure.extendRemaining u v y)))=_
  simp only [hw]

end Holant.Dihedral.TwoCardLocalization
