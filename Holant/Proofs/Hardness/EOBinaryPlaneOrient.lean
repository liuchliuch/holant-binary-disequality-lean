import Holant.Proofs.Hardness.EOBinaryPlaneCore

/-! Reversing an actual opposite-port pair complements exactly its compressed
Boolean argument. Thus every three-entry binary plane can be oriented with its
unique missing word at 11 using only original-port order. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneOrient
open Holant
namespace C
export EOBinaryPlaneCore (pairing word compress lift)
end C
set_option backward.isDefEq.respectTransparency false

def flipWord (signs : Fin 2→Bool) (z : Fin 2→Bool) : Fin 2→Bool :=
  fun j=>Bool.xor (signs j) (z j)

theorem flipWord_twice (signs z : Fin 2→Bool) : flipWord signs (flipWord signs z)=z := by
  funext j
  change Bool.xor (signs j) (Bool.xor (signs j) (z j))=z j
  cases signs j <;> cases z j <;> rfl

def pairTwist (signs : Fin 2→Bool) : Equiv.Perm (Fin 2×Bool) where
  toFun p := (p.1,Bool.xor p.2 (signs p.1))
  invFun p := (p.1,Bool.xor p.2 (signs p.1))
  left_inv := by rintro ⟨j,b⟩; dsimp only; cases b <;> cases signs j <;> rfl
  right_inv := by rintro ⟨j,b⟩; dsimp only; cases b <;> cases signs j <;> rfl

def ports (signs : Fin 2→Bool) : Equiv.Perm (Fin 4) :=
  C.pairing.ports.symm.trans ((pairTwist signs).trans C.pairing.ports)

theorem lift_flip {K : Type*} [Zero K] (f : Signature K 2) (signs : Fin 2→Bool) :
    Tensor.reindex (ports signs) (C.lift f)=C.lift (fun z=>f (flipWord signs z)) := by
  funext x
  cases hs0 : signs 0 <;> cases hs1 : signs 1 <;>
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [Tensor.reindex_apply,C.lift,ports,pairTwist,C.pairing,hs0,hs1,h0,h1,h2,h3]
  all_goals (congr 1; funext j; fin_cases j <;> simp [flipWord,hs0,hs1])

def signsFor (missing : Fin 2→Bool) : Fin 2→Bool := fun j=>!(missing j)

theorem last_to_missing (missing : Fin 2→Bool) :
    flipWord (signsFor missing) ![true,true]=missing := by
  funext j
  have hj : (![true,true] : Fin 2→Bool) j=true := by fin_cases j <;> rfl
  change Bool.xor (!(missing j)) (![true,true] j)=missing j
  rw [hj]
  cases missing j <;> rfl

theorem missing_to_last (missing : Fin 2→Bool) :
    flipWord (signsFor missing) missing=![true,true] := by
  have h := congrArg (flipWord (signsFor missing)) (last_to_missing missing)
  rw [flipWord_twice] at h
  exact h.symm

def oriented {K : Type*} (f : Signature K 2) (missing : Fin 2→Bool) : Signature K 2 :=
  fun z=>f (flipWord (signsFor missing) z)

theorem oriented_last {K : Type*} (f : Signature K 2) (missing : Fin 2→Bool) :
    oriented f missing ![true,true]=f missing := congrArg f (last_to_missing missing)

theorem oriented_nonzero {K : Type*} [Zero K] (f : Signature K 2) (missing : Fin 2→Bool)
    (h : ∀z,z≠missing → f z≠0) (z : Fin 2→Bool) (hz : z≠![true,true]) :
    oriented f missing z≠0 := by
  apply h
  intro he
  have hh := congrArg (flipWord (signsFor missing)) he
  rw [flipWord_twice,missing_to_last] at hh
  exact hz hh

/-- The missing word becomes 11; all other coefficients stay nonzero, with no
synthetic pin, sign weight, or binary palette label. -/
theorem three_orientation {K : Type*} [Zero K] (f : Signature K 2) (missing : Fin 2→Bool)
    (hz : f missing=0) (hn : ∀z,z≠missing → f z≠0) :
    oriented f missing ![false,false]≠0 ∧ oriented f missing ![false,true]≠0 ∧
    oriented f missing ![true,false]≠0 ∧ oriented f missing ![true,true]=0 := by
  exact ⟨oriented_nonzero f missing hn _ (by decide),oriented_nonzero f missing hn _ (by decide),
    oriented_nonzero f missing hn _ (by decide),(oriented_last f missing).trans hz⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneOrient
