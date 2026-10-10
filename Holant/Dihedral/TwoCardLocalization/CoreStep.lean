import Holant.Dihedral.CompatibleCoefficientLine.PortAlignment
import Holant.OpenNetworkComposition.ProjectiveContraction

/-! Generic physical lifting of a residual-pair contraction to the original
ancestor while retaining its first two deleted ports. This is independent of
all dihedral phase and matching arguments. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine Holant.OpenNetworkComposition
variable {K : Type*} [Field K] {n : ℕ}

def outsideOrder (p : Equiv.Perm (Fin (n+2))) : Equiv.Perm (Fin (n+4)) :=
  (swapPairs n).trans (liftPair p)

def outsideClose (p : Equiv.Perm (Fin (n+2))) (C : Kernel K)
    (q : Signature K (n+4)) : Signature K (n+2) :=
  Signature.contract C (Tensor.reindex (outsideOrder p).symm q)

theorem word_outsideOrder (p : Equiv.Perm (Fin (n+2))) (a b c d : Bool) (x : Fin n → Bool) :
    (fun i => pair a b (pair c d x) ((outsideOrder p).symm i)) =
      pair c d (fun i => pair a b x (p.symm i)) := by
  have h := congrArg (fun w : Fin (n+4) → Bool => fun i => w ((liftPair p).symm i))
    (word_swapPairs a b c d x)
  change (fun i => pair a b (pair c d x) ((outsideOrder p).symm i)) = _ at h
  rw [word_liftPair] at h
  exact h

/-- Only the selected inherited cards are transported, by their actual kernels.
No parity, nonzero or multi-card preservation hypothesis is used here. -/
theorem outside_card (p : Equiv.Perm (Fin (n+2))) (C A : Kernel K)
    (q : Signature K (n+4)) :
    Signature.contract A (outsideClose p C q) =
      Signature.contract C (Tensor.reindex p.symm (Signature.contract A q)) := by
  funext x
  simp only [outsideClose,Signature.contract,Tensor.reindex,word_outsideOrder,Fintype.sum_bool]
  ring

@[simp] theorem contract_smul (C : Kernel K) (c : K) (q : Signature K (n+2)) :
    Signature.contract C (c • q)=c • Signature.contract C q := by
  funext x
  simp only [Signature.contract,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

def binarySignature (B : Kernel K) : Signature K 2 := fun x => B (x 0) (x 1)

private theorem update_second (a b c : Bool) (x : Fin n → Bool) :
    Function.update (pair a b x) 1 c = pair a c x := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp [pair]
  · simp [pair]
  · have hk : k.succ.succ ≠ (1 : Fin (n+2)) := Fin.succ_succ_ne_one k
    simp only [Function.update_of_ne hk,Fin.cons_succ]

def physicalValue (q : Signature K (n+2)) (B : Kernel K) : Signature K n :=
  fun x => ∑ a : Bool, ∑ b : Bool, B (!a) (!b)*q (pair a b x)

/-- Exact finite-sum semantics of the two successive native-X connections. -/
theorem contract_splice (q : Signature K (n+2)) (B : Kernel K) :
    Signature.contract Signature.disequality (spliceTensor q (binarySignature B) 1) =
      physicalValue q B := by
  funext x
  rw [Signature.contract_disequality]
  simp only [spliceTensor,update_second,binarySignature,Fin.cons_one,Fin.cons_zero,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  simp [Signature.disequality,physicalValue]
  ring

/-- Arbitrary actual gadgets are connected, retaining the proved possible
circle factor. The operation uses exactly one supplied binary representative. -/
theorem realizes_connection (F : SignatureFamily K) (q : Signature K (n+2)) (B : Kernel K)
    (hq : Gadget.Realizes F .disequality q)
    (hB : Gadget.Realizes F .disequality (binarySignature B)) (htwo : (2:K) ≠ 0) :
    ∃ c : K, (c=1 ∨ c=(2:K)⁻¹) ∧ c ≠ 0 ∧
      Gadget.Realizes F .disequality (c • physicalValue q B) := by
  have hs := realizes_splice F q (binarySignature B) hq hB (1 : Fin (n+2))
  obtain ⟨c,hc,hn,hr⟩ := realizes_contract_with_scale F
    (spliceTensor q (binarySignature B) 1) hs htwo
  refine ⟨c,hc,hn,?_⟩
  rw [contract_splice] at hr
  exact hr

/-- One physical step on the actual ancestor, with the retained deleted pair
and exact representative/circle multiplier still visible. -/
theorem actual_outside_step (F : SignatureFamily K) (q : Signature K (n+4))
    (hq : Gadget.Realizes F .disequality q) (p : Equiv.Perm (Fin (n+2)))
    (C B : Kernel K) (κ : K) (hκ : κ ≠ 0)
    (hB : Gadget.Realizes F .disequality (binarySignature B))
    (hentries : ∀ a b, B (!a) (!b)=κ*C a b) (htwo : (2:K) ≠ 0) :
    ∃ c : K, (c=1 ∨ c=(2:K)⁻¹) ∧ c*κ ≠ 0 ∧
      Gadget.Realizes F .disequality ((c*κ) • outsideClose p C q) := by
  obtain ⟨c,hc,hn,hr⟩ := realizes_connection F (Tensor.reindex (outsideOrder p).symm q) B
    (realizes_reindex F .disequality q hq (outsideOrder p)) hB htwo
  refine ⟨c,hc,mul_ne_zero hn hκ,?_⟩
  convert hr using 1
  funext x
  simp only [outsideClose,physicalValue,Signature.contract,hentries,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

end Holant.Dihedral.TwoCardLocalization
