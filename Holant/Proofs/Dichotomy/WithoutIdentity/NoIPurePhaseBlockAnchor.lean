import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseBlockTransform
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseAnchorIncidence
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseAnchorRecipe

/-! Synchronization uses one fixed original-row block anchor. Every test
and correction is still a finite family of literal original substitutions.
A legal combined block would be Affine, contradicting its exact bad phase
pullback. No per-signature phase choice is used in this argument. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseBlockAnchor
open Holant Holant.Tractable
open NoIPurePhaseBlock
open NoIPurePhaseLegalAffine (LegalAffine)
open scoped BigOperators
namespace C
export NoIPurePhaseIncidenceCore.C (codeSeven)
export NoIPurePhaseAnchorRecipe.A (codeSeven_affine)
end C
namespace T
export NoIPurePhaseIncidenceRegularization.P (Transform image)
end T
namespace S
export NoIPurePhaseAnchorIncidence (copies)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false
variable {n : ℕ}

theorem phase_nonzero (r : AlgebraicComplex) (rn : r≠0)
    (f : Signature AlgebraicComplex n) (B : Block n 7) (z : Fin 7→Bool)
    (full : value f B z≠0) : phase r f B z≠0 := by
  rw [phase_value]
  exact mul_ne_zero full (NoIPurePhaseRecipeFactor.nonzero B.ports r rn z)

def zeroTransform : T.Transform:=⟨0,0,0⟩

theorem charge_zero_transform (A : Block n 7) (j : Fin 7) :
    NoIPurePhaseBlock.charge (transform A zeroTransform) j=0 := by
  rw [charge_transform]
  have hz : ∀k : Fin 7,T.image zeroTransform k=0 := by decide
  have hn : (0 : Fin 8) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
  simp [hz,hn]

def slot (A : Block n 7) (a t : ZMod 4) (i : Fin 3) : Block n 7:=
  if i.val<S.copies a t then A else transform A zeroTransform

def correction (A : Block n 7) (a t : ZMod 4) : Block n 7:=flatten (slot A a t)

theorem slot_charge (A : Block n 7) (a t : ZMod 4)
    (uniform : ∀j,(NoIPurePhaseBlock.charge A j : ZMod 4)=a) (i : Fin 3) (j : Fin 7) :
    (NoIPurePhaseBlock.charge (slot A a t i) j : ZMod 4)=if i.val<S.copies a t then a else 0 := by
  unfold slot
  split_ifs <;> simp [uniform,charge_zero_transform]

theorem correction_zero (A B : Block n 7) (a t : ZMod 4)
    (odd : a=1 ∨ a=3) (anchor : ∀j,(NoIPurePhaseBlock.charge A j : ZMod 4)=a)
    (test : ∀j,(NoIPurePhaseBlock.charge B j : ZMod 4)=t) (j : Fin 7) :
    NoIPurePhaseBlock.charge (append B (correction A a t)) j%4=0 := by
  have finite : ∀a t : ZMod 4,(a=1 ∨ a=3)→
      t+(∑i : Fin 3,if i.val<S.copies a t then a else 0)=0 := by decide
  have cast : (NoIPurePhaseBlock.charge (append B (correction A a t)) j : ZMod 4)=0 := by
    rw [charge_append,Int.cast_add,test,correction,charge_flatten,Int.cast_sum]
    simp_rw [slot_charge A a t anchor]
    exact finite a t odd
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp cast)

theorem correction_affine (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (A : Block n 7) (a t : ZMod 4) (good : Affine (phase r f A)) :
    Affine (phase r f (correction A a t)) := by
  have each (i : Fin 3) : Affine (phase r f (slot A a t i)) := by
    unfold slot
    split_ifs
    · exact good
    · exact transform_affine r f A zeroTransform good
  have h:=((each 0).mul (each 1)).mul (each 2)
  have eqn : phase r f (correction A a t) = fun z =>
      phase r f (slot A a t 0) z * phase r f (slot A a t 1) z * phase r f (slot A a t 2) z := by
    funext z
    rw [correction, phase_flatten, Fin.prod_univ_three]
  rw [eqn]
  exact h

theorem correction_full (r : AlgebraicComplex) (rn : r≠0)
    (f : Signature AlgebraicComplex n) (A : Block n 7) (a t : ZMod 4)
    (full : ∀x : Fin 3→Bool,value f A (C.codeSeven x)≠0) :
    ∀x : Fin 3→Bool,phase r f (correction A a t) (C.codeSeven x)≠0 := by
  intro x
  rw [correction,phase_flatten]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  unfold slot
  split_ifs
  · exact phase_nonzero r rn f A _ (full x)
  · exact phase_nonzero r rn f (transform A zeroTransform) _
      (transform_full_code f A zeroTransform full x)

/-- A fixed odd anchor excludes every constant-charge bad test in its one
chosen phase. Subsequent tests do not choose a different phase. -/
theorem odd_excludes (f : Signature AlgebraicComplex n) (legal : LegalAffine f)
    (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1)
    (A B : Block n 7) (a t : ZMod 4) (odd : a=1 ∨ a=3)
    (anchor : ∀j,(NoIPurePhaseBlock.charge A j : ZMod 4)=a) (test : ∀j,(NoIPurePhaseBlock.charge B j : ZMod 4)=t)
    (good : Affine (phase r f A))
    (full : ∀x : Fin 3→Bool,value f A (C.codeSeven x)≠0)
    (bad : ¬Affine (fun x : Fin 3→Bool=>phase r f B (C.codeSeven x))) : False := by
  have h:=legal_phase f legal r rn root (append B (correction A a t))
    (correction_zero A B a t odd anchor test)
  have pull:=h.precompose C.codeSeven C.codeSeven_affine
  apply bad
  apply (NoIPureAffineMultiplier.mul_iff _ _
    ((correction_affine r f A a t good).precompose C.codeSeven C.codeSeven_affine)
    (fun x _=>correction_full r rn f A a t full x)).mp
  simpa only [phase_append] using pull

/-- Two all-two blocks cancel with exactly one anchor copy. -/
theorem two_excludes (f : Signature AlgebraicComplex n) (legal : LegalAffine f)
    (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1) (A B : Block n 7)
    (anchor : ∀j,(NoIPurePhaseBlock.charge A j : ZMod 4)=2) (test : ∀j,(NoIPurePhaseBlock.charge B j : ZMod 4)=2)
    (good : Affine (phase r f A))
    (full : ∀x : Fin 3→Bool,value f A (C.codeSeven x)≠0)
    (bad : ¬Affine (fun x : Fin 3→Bool=>phase r f B (C.codeSeven x))) : False := by
  have zero (j : Fin 7) : NoIPurePhaseBlock.charge (append B A) j%4=0 := by
    have cast : (NoIPurePhaseBlock.charge (append B A) j : ZMod 4)=0 := by
      rw [charge_append,Int.cast_add,test,anchor]
      decide
    exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp cast)
  have pull:=(legal_phase f legal r rn root (append B A) zero).precompose C.codeSeven C.codeSeven_affine
  apply bad
  apply (NoIPureAffineMultiplier.mul_iff _ _ (good.precompose C.codeSeven C.codeSeven_affine)
    (fun x _=>phase_nonzero r rn f A _ (full x))).mp
  simpa only [phase_append] using pull


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseBlockAnchor
end
