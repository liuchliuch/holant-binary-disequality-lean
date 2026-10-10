import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinPhasePrime
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinBitTranslate
import Holant.ReedMuller.CharacterFlat.Tensor

/-! Boundary Pauli signs, bit translations and port reorderings preserve the
actual character-flat class in both directions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterGauge
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CharacterFlat
namespace A
export GlobalCloseCompletionKleinPhaseActual (phase)
end A
namespace T
export GlobalCloseCompletionC2BitTranslateActual (translate)
end T
namespace S
export GlobalCloseCompletionKleinPhasePrime (single involutive)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n : ℕ}

def coordinate (i : Fin n) : Character n where
  toFun := fun x=>x i
  map_add' := by intros;rfl
  map_smul' := by intros;rfl

theorem coordinate_apply (i : Fin n) (x : BinaryVector n) : coordinate i x=x i := rfl

theorem bit_sign (b : Bool) : sign (boolEquiv b)=(if b then -1 else 1) := by cases b <;> norm_num [boolEquiv,sign,intSign]

theorem single (f : Signature ℂ n) (flat : CFlat f) (i : Fin n) : CFlat (S.single f i) := by
  rcases flat with rfl|⟨c,a,D,ell,selfDual,rfl⟩
  · left;funext x;simp [S.single]
  right
  refine ⟨c,a,D,ell+coordinate i,selfDual,?_⟩
  funext x
  simp only [S.single,signature,value,LinearMap.add_apply,coordinate_apply,sign_add,vectorWord,bit_sign]
  split_ifs <;> ring

theorem phase (f : Signature ℂ n) (flat : CFlat f) (s : Finset (Fin n)) : CFlat (A.phase s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have eq : A.phase (∅ : Finset (Fin n)) f=f := by funext x;simp [A.phase]
    rwa [eq]
  | @insert i s hi ih =>
    have h := single (A.phase s f) ih i
    have eq : S.single (A.phase s f) i=A.phase (insert i s) f := by
      funext x
      simp only [S.single,A.phase,Finset.prod_insert hi,mul_assoc]
    rwa [eq] at h

theorem phase_involutive (s : Finset (Fin n)) (f : Signature ℂ n) : A.phase s (A.phase s f)=f := by
  funext x
  have signs : (∏i∈s,if x i then (-1:ℂ) else 1)^2=1 := by
    rw [←Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i _
    cases x i <;> norm_num
  change (∏i∈s,if x i then (-1:ℂ) else 1)*((∏i∈s,if x i then (-1:ℂ) else 1)*f x)=f x
  calc
    _=(∏i∈s,if x i then (-1:ℂ) else 1)^2*f x := by ring
    _=f x := by rw [signs,one_mul]

theorem phase_iff (s : Finset (Fin n)) (f : Signature ℂ n) : CFlat (A.phase s f) ↔ CFlat f := by
  constructor
  · intro flat
    have h := phase _ flat s
    rwa [phase_involutive] at h
  · exact fun flat=>phase f flat s

theorem bit_xor : ∀a b : Bool,bit (a ^^ b)=bit a+bit b := by decide +kernel

theorem translate (f : Signature ℂ n) (flat : CFlat f) (mask : Fin n→Bool) : CFlat (T.translate f mask) := by
  rcases flat with rfl|⟨c,a,D,ell,selfDual,rfl⟩
  · exact Or.inl rfl
  let v : BinaryVector n:=vectorWord mask
  right
  refine ⟨c*Units.mk0 (sign (ell v)) (sign_nonzero _),a-v,D,ell,selfDual,?_⟩
  funext x
  have word : vectorWord (fun i=>x i ^^ mask i)=vectorWord x+v := by
    funext i
    exact bit_xor (x i) (mask i)
  have shift : vectorWord x+v-a=vectorWord x-(a-v) := by abel
  simp only [T.translate,signature,value,Units.val_mul,Units.val_mk0]
  rw [word,shift,LinearMap.map_add,sign_add]
  split_ifs <;> ring

theorem translate_iff (f : Signature ℂ n) (mask : Fin n→Bool) : CFlat (T.translate f mask) ↔ CFlat f := by
  constructor
  · intro flat
    have h := translate _ flat mask
    rwa [GlobalCloseCompletionKleinBitTranslate.involutive] at h
  · exact fun flat=>translate f flat mask

theorem reindex_iff (p : Equiv.Perm (Fin n)) (f : Signature ℂ n) : CFlat (Tensor.reindex p f) ↔ CFlat f := by
  constructor
  · intro flat
    have h := CFlat.reindex p.symm _ flat
    rwa [Tensor.reindex_symm] at h
  · exact CFlat.reindex p f


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterGauge
end
