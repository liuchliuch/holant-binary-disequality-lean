import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Encoding
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Prod

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Every additional witness bit is checked false. The
ordered old prefix and its unique false suffix give a genuine bijection;
discarding an arbitrary suffix would multiply the accepting count. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness
open Computability Holant.Complexity

namespace Padding
def extract (n : ℕ) (bits : List Bool) : Option (List Bool) :=
  if n ≤ bits.length then
    if (bits.drop n).all (!·) then some (bits.take n) else none
  else none

def accept (n : ℕ) (A : List Bool → Bool) (bits : List Bool) : Bool :=
  (extract n bits).elim false A

theorem extract_append (firstBits tail : List Bool) :
    extract firstBits.length (firstBits++tail) =
      if tail.all (!·) then some firstBits else none := by
  simp [extract,List.take_append,List.drop_append]

def split (n r : ℕ) : (Fin (n+r) → Bool) ≃ (Fin n → Bool) × (Fin r → Bool) where
  toFun x := (fun i => x (Fin.castAdd r i),fun i => x (Fin.natAdd n i))
  invFun p := Fin.addCases p.1 p.2
  left_inv x := by
    funext i
    induction i using Fin.addCases <;> simp
  right_inv p := by
    apply Prod.ext <;> funext i <;> simp

def canonicalEquiv (n r : ℕ) : (Fin n → Bool) ≃
    {x : Fin (n+r) → Bool // ∀ i : Fin r, x (Fin.natAdd n i)=false} where
  toFun x := ⟨Fin.addCases x (fun _ => false),by intro i; simp⟩
  invFun x := fun i => x.val (Fin.castAdd r i)
  left_inv x := by funext i; simp
  right_inv x := by
    apply Subtype.ext
    funext i
    induction i using Fin.addCases with
    | left i => simp
    | right i => simpa using (x.property i).symm

theorem tail_all (r : ℕ) (t : Fin r → Bool) :
    (List.ofFn t).all (!·) = decide (t = fun _ => false) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp [List.all_eq_true,List.forall_mem_ofFn_iff,funext_iff]

theorem unique_tail (r : ℕ) :
    countAccepted (fun t : Fin r → Bool => decide (t = fun _ => false)) = 1 := by
  classical
  simp [countAccepted]

/-- The split representation reads every old bit and rejects every nonzero
extra bit. This is also the operational predicate used by the literal guard. -/
theorem accept_split (n r : ℕ) (A : List Bool → Bool)
    (p : (Fin n → Bool) × (Fin r → Bool)) :
    accept n A (List.ofFn ((split n r).symm p)) =
      (A (List.ofFn p.1) && decide (p.2 = fun _ => false)) := by
  classical
  have hl : List.ofFn ((split n r).symm p) = List.ofFn p.1 ++ List.ofFn p.2 := by
    simp [split,List.ofFn_add]
    funext i
    change Fin.addCases p.1 p.2 (Fin.castAdd r i) = p.1 i
    simp
  have hx := extract_append (List.ofFn p.1) (List.ofFn p.2)
  simp only [List.length_ofFn] at hx
  rw [accept,hl,hx,tail_all]
  cases decide (p.2 = fun _ => false) <;> simp

/-- Explicit inverse maps on accepted vectors: append the unique false tail,
then recover precisely the first n bits. No cardinality-choice equivalence. -/
def acceptedEquiv (n r : ℕ) (A : List Bool → Bool) :
    {bits : Fin n → Bool // A (List.ofFn bits) = true} ≃
      {bits : Fin (n+r) → Bool // accept n A (List.ofFn bits) = true} where
  toFun b := ⟨(split n r).symm (b.val,fun _ => false),by
    rw [accept_split]
    simp only [b.property,decide_true,Bool.and_self]⟩
  invFun b := ⟨((split n r) b.val).1,by
    have h : accept n A (List.ofFn ((split n r).symm ((split n r) b.val))) = true := by
      simpa only [Equiv.symm_apply_apply] using b.property
    rw [accept_split] at h
    simp only [Bool.and_eq_true] at h
    exact h.1⟩
  left_inv b := by
    apply Subtype.ext
    exact congrArg Prod.fst ((split n r).apply_symm_apply (b.val,fun _ => false))
  right_inv b := by
    apply Subtype.ext
    apply (split n r).injective
    change (split n r) ((split n r).symm (((split n r) b.val).1,fun _ => false)) = (split n r) b.val
    rw [Equiv.apply_symm_apply]
    refine Prod.ext rfl ?_
    have h : accept n A (List.ofFn ((split n r).symm ((split n r) b.val))) = true := by
      simpa only [Equiv.symm_apply_apply] using b.property
    rw [accept_split] at h
    simp only [Bool.and_eq_true] at h
    exact (of_decide_eq_true h.2).symm

/-- The length change is solely the canonical Fin-index cast induced by n≤m. -/
def acceptedEquivOfLe (n m : ℕ) (h : n ≤ m) (A : List Bool → Bool) :
    {bits : Fin n → Bool // A (List.ofFn bits) = true} ≃
      {bits : Fin m → Bool // accept n A (List.ofFn bits) = true} := by
  exact (acceptedEquiv n (m-n) A).trans (Equiv.cast
    (congrArg (fun size : ℕ => {bits : Fin size → Bool // accept n A (List.ofFn bits) = true})
      (Nat.add_sub_of_le h)))

theorem count_exact (n r : ℕ) (A : List Bool → Bool) :
    witnessCount (n+r) (accept n A) = witnessCount n A := by
  classical
  let e := split n r
  have ha (p : (Fin n → Bool) × (Fin r → Bool)) :
      accept n A (List.ofFn (e.symm p)) =
        (A (List.ofFn p.1) && decide (p.2 = fun _ => false)) := by
    have hl : List.ofFn (e.symm p) = List.ofFn p.1 ++ List.ofFn p.2 := by
      simp [e,split,List.ofFn_add]
      funext i
      change Fin.addCases p.1 p.2 (Fin.castAdd r i) = p.1 i
      simp
    have hx := extract_append (List.ofFn p.1) (List.ofFn p.2)
    simp only [List.length_ofFn] at hx
    rw [accept,hl,hx,tail_all]
    cases decide (p.2 = fun _ => false) <;> simp
  have hc := countAccepted_equiv e.symm
    (fun x : Fin (n+r) → Bool => accept n A (List.ofFn x))
  have hf : (fun p => accept n A (List.ofFn (e.symm p))) =
      (fun p : (Fin n → Bool) × (Fin r → Bool) =>
        A (List.ofFn p.1) && decide (p.2 = fun _ => false)) := funext ha
  rw [hf,countAccepted_product (fun x : Fin n → Bool => A (List.ofFn x))
    (fun t : Fin r → Bool => decide (t = fun _ => false)),unique_tail,Nat.mul_one] at hc
  exact hc.symm

theorem count_of_le (n m : ℕ) (h : n ≤ m) (A : List Bool → Bool) :
    witnessCount m (accept n A) = witnessCount n A := by
  simpa only [Nat.add_sub_of_le h] using count_exact n (m-n) A
end Padding

variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}

def oldLength (w : SharpPWitness ea f) (a : α) : ℕ :=
  w.witnessLength.eval (ea.encode a).length
def newLength (w : SharpPWitness ea f) (a : α) : ℕ :=
  w.witnessLength.eval ((inputEncoding w).encode a).length
def paddedAccept (w : SharpPWitness ea f) (p : α × List Bool) : Bool :=
  Padding.accept (oldLength w p.1) (fun bits => w.accept (p.1,bits)) p.2

theorem oldLength_le_newLength (w : SharpPWitness ea f) (a : α) :
    oldLength w a ≤ newLength w a :=
  natPolynomial_eval_mono w.witnessLength (original_length_le w a)

/-- Same f and the ORIGINAL witness polynomial evaluated at the new raw bit
length. Padding legality and the count law are proved, not supplied. -/
theorem padded_counts (w : SharpPWitness ea f) (a : α) :
    f a = witnessCount (newLength w a) (fun bits => paddedAccept w (a,bits)) := by
  rw [w.counts a]
  exact (Padding.count_of_le (oldLength w a) (newLength w a)
    (oldLength_le_newLength w a) (fun bits => w.accept (a,bits))).symm

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness
