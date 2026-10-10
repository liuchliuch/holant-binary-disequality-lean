import Holant.Platonic.StabilizerErasure.AlignedForms

/-! Every invertible binary computational-coordinate change is a genuine
analytic Clifford, including the controlled bit addition used to remove a
Bell factor. Both exact Pauli normalizations are proved explicitly. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def relabelWords (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector n) : Word n ≃ Word n where
  toFun w := wordVector (e (vectorWord w))
  invFun w := wordVector (e.symm (vectorWord w))
  left_inv w := by simp
  right_inv w := by simp

def relabelOperator (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector n) :
    Signature ℂ n ≃ₗ[ℂ] Signature ℂ n where
  toFun f w := f (relabelWords e w)
  invFun f w := f ((relabelWords e).symm w)
  left_inv f := by ext w;simp
  right_inv f := by ext w;simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem relabel_normalizes (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector n) :
    NormalizesPauli (relabelOperator e) := by
  intro P
  refine ⟨⟨P.phase,e.symm P.shift,P.character.comp e.toLinearMap⟩,?_⟩
  intro f
  ext w
  simp [relabelOperator,relabelWords,Pauli.run,map_add]

def relabelClifford (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector n) : AnalyticClifford n where
  operator := relabelOperator e
  unitary f g := (relabelWords e).sum_comp (fun w => starRingEnd ℂ (f w)*g w)
  pauli_forward := relabel_normalizes e
  pauli_inverse := relabel_normalizes e.symm

def controlledAdd (r : Fin (n+1)) : BinaryVector (n+2) ≃ₗ[ZMod 2] BinaryVector (n+2) where
  toFun x := Fin.cons (x 0) (Function.update (Fin.tail x) r (x r.succ+x 0))
  invFun x := Fin.cons (x 0) (Function.update (Fin.tail x) r (x r.succ+x 0))
  left_inv x := by
    ext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
      by_cases hj : j=r
      · subst j;simp [Fin.tail,add_assoc,CharTwo.add_self_eq_zero]
      · simp [Fin.tail,hj]
  right_inv x := by
    ext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
      by_cases hj : j=r
      · subst j;simp [Fin.tail,add_assoc,CharTwo.add_self_eq_zero]
      · simp [Fin.tail,hj]
  map_add' x y := by
    ext j
    cases j using Fin.cases with
    | zero => simp [Ne.symm (Fin.succ_ne_zero r)]
    | succ j =>
      by_cases hj : j=r <;> simp [hj,Fin.tail] <;> ring
  map_smul' c x := by
    ext j
    cases j using Fin.cases with
    | zero => simp [Ne.symm (Fin.succ_ne_zero r)]
    | succ j =>
      by_cases hj : j=r <;> simp [hj,Fin.tail,mul_add]

theorem controlledAdd_word (r : Fin (n+1)) (b c : Bool) (w : Word n) :
    relabelWords (controlledAdd r) (Fin.cons b (r.insertNth c w))=
      Fin.cons b (r.insertNth (Bool.xor c b) w) := by
  ext j
  cases j using Fin.cases with
  | zero => simp [relabelWords,wordVector,vectorWord,controlledAdd,Ne.symm (Fin.succ_ne_zero r)]
  | succ j =>
    by_cases hj : j=r
    · subst j
      cases b <;> cases c <;> simp [relabelWords,wordVector,vectorWord,controlledAdd,boolEquiv]
    · have he : ∃i : Fin n,r.succAbove i=j := by
        exact ⟨(finSuccAboveEquiv r).symm ⟨j,hj⟩,
          congrArg Subtype.val ((finSuccAboveEquiv r).apply_symm_apply ⟨j,hj⟩)⟩
      obtain ⟨i,rfl⟩ := he
      simp [relabelWords,wordVector,vectorWord,controlledAdd,Fin.tail,Fin.succAbove_ne]

end
end Holant.Platonic.StabilizerErasure
