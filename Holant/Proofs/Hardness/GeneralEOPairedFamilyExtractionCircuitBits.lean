import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRecipe
import Holant.ReedMuller.AffinePatching.ReconstructionSupport

/-! An affine Boolean map has a finite XOR circuit with exactly one extension
of each input assignment. Every internal bit is retained explicitly. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionCircuitBits
open Holant Holant.Tractable
open AffinePhase TwoTranslate
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {m n : ℕ}

@[simp] theorem residueBit_bit (b : Bool) : residueBit (bitValue (ZMod 2) b)=b := by cases b <;> rfl

def coefficient (p : Word m → Word n) (i : Fin n) (j : Fin m) : ZMod 2 :=
  bitValue (ZMod 2) (p (basis j) i)-bitValue (ZMod 2) (p (origin m) i)

theorem affine_coordinate (p : Word m → Word n) (hp : IsAffineMap p)
    (i : Fin n) (z : Word m) :
    bitValue (ZMod 2) (p z i)=bitValue (ZMod 2) (p (origin m) i)+dot (coefficient p i) z := by
  let q : Word m → ZMod 2 := fun x=>bitValue (ZMod 2) (p x i)-bitValue (ZMod 2) (p (origin m) i)
  have hq0 : q (origin m)=0 := sub_self _
  have hadd (x y : Word m) : q (xor x y)=q x+q y := by
    dsimp only [q]
    rw [hp x y]
    simp only [xor_apply,bitValue_xor]
    ring_nf
    have htwo : (2 : ZMod 2)=0 := by decide
    simp only [htwo,mul_zero,sub_zero]
  have he : q=(fun x=>dot (coefficient p i) x) := additive_word_eq _ _ hq0
    (dot_origin _) hadd (dot_xor _) (fun j=>by simp only [dot_basis]; rfl)
  have h := congrFun he z
  dsimp [q] at h
  linear_combination h

def partialBit (p : Word m → Word n) (z : Word m) (i : Fin n) (t : Fin (m+1)) : Bool :=
  residueBit (bitValue (ZMod 2) (p (origin m) i)+
    ∑j : Fin t.val,coefficient p i (Fin.castLE (Nat.le_of_lt_succ t.isLt) j)*
      bitValue (ZMod 2) (z (Fin.castLE (Nat.le_of_lt_succ t.isLt) j)))

@[simp] theorem partialBit_zero (p : Word m → Word n) (z : Word m) (i : Fin n) :
    partialBit p z i 0=p (origin m) i := by simp [partialBit]

theorem partialBit_last (p : Word m → Word n) (hp : IsAffineMap p) (z : Word m) (i : Fin n) :
    partialBit p z i (Fin.last m)=p z i := by
  apply bitValue_injective
  simp only [partialBit,bitValue_residueBit,Fin.val_last,Fin.castLE_refl]
  exact (affine_coordinate p hp i z).symm

def input (p : Word m → Word n) (z : Word m) (i : Fin n) (j : Fin m) : Bool :=
  if residueBit (coefficient p i j) then z j else false

theorem bit_input (p : Word m → Word n) (z : Word m) (i : Fin n) (j : Fin m) :
    bitValue (ZMod 2) (input p z i j)=coefficient p i j*bitValue (ZMod 2) (z j) := by
  unfold input
  generalize h : coefficient p i j=a
  fin_cases a <;> simp

theorem partialBit_step (p : Word m → Word n) (z : Word m) (i : Fin n) (j : Fin m) :
    partialBit p z i j.succ=Bool.xor (partialBit p z i j.castSucc) (input p z i j) := by
  apply bitValue_injective
  simp only [partialBit,bitValue_residueBit,bitValue_xor,bit_input,Fin.val_succ,Fin.val_castSucc]
  rw [Fin.sum_univ_castSucc]
  have he : (∑ k : Fin j.val,coefficient p i
      (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) k.castSucc)*
      bitValue (ZMod 2) (z (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) k.castSucc)))=
      ∑k : Fin j.val,coefficient p i
        (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) k)*
        bitValue (ZMod 2) (z (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) k)) := by rfl
  rw [he,←add_assoc]
  rfl

variable {r : ℕ}

def address (v : Fin r) (i : Fin n) (t : Fin (m+1)) : Fin ((r*n)*(m+1)) :=
  finProdFinEquiv (finProdFinEquiv (v,i),t)

def assignment (ps : Fin r → Word m → Word n) (z : Word m) : Word ((r*n)*(m+1)) := fun a=>
  let vt := finProdFinEquiv.symm a
  let vi := finProdFinEquiv.symm vt.1
  partialBit (ps vi.1) z vi.2 vt.2

@[simp] theorem assignment_at (ps : Fin r → Word m → Word n) (z : Word m)
    (v : Fin r) (i : Fin n) (t : Fin (m+1)) :
    assignment ps z (address v i t)=partialBit (ps v) z i t := by simp [assignment,address]

def Consistent (ps : Fin r → Word m → Word n) (z : Word m)
    (y : Word ((r*n)*(m+1))) : Prop :=
  ∀v i, y (address v i 0)=ps v (origin m) i ∧
    ∀j : Fin m,y (address v i j.succ)=Bool.xor (y (address v i j.castSucc)) (input (ps v) z i j)

theorem consistent_iff (ps : Fin r → Word m → Word n) (z : Word m)
    (y : Word ((r*n)*(m+1))) : Consistent ps z y ↔ y=assignment ps z := by
  constructor
  · intro h
    have he (v : Fin r) (i : Fin n) (t : Fin (m+1)) : y (address v i t)=partialBit (ps v) z i t := by
      induction t using Fin.induction with
      | zero => simpa only [partialBit_zero] using (h v i).1
      | succ j ih => rw [(h v i).2 j,ih,←partialBit_step]
    funext a
    obtain ⟨⟨vi,t⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨v,i⟩,rfl⟩ := finProdFinEquiv.surjective vi
    exact (he v i t).trans (assignment_at ps z v i t).symm
  · rintro rfl v i
    simp only [assignment_at,partialBit_zero]
    exact ⟨True.intro,fun j=>partialBit_step (ps v) z i j⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionCircuitBits
