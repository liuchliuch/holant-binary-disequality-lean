import Holant.ReedMuller.CharacterFlat.Contraction

/-! Literal scalar, port-permutation and disjoint-product closure for linear
characters on actual affine self-dual support codes. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

def leftLinear : BinaryVector (m+n) →ₗ[ZMod 2] BinaryVector m where
  toFun := leftVector
  map_add' := by intros;rfl
  map_smul' := by intros;rfl

def rightLinear : BinaryVector (m+n) →ₗ[ZMod 2] BinaryVector n where
  toFun := rightVector
  map_add' := by intros;rfl
  map_smul' := by intros;rfl

@[simp] theorem leftLinear_apply (x : BinaryVector (m+n)) : leftLinear x=leftVector x := rfl
@[simp] theorem rightLinear_apply (x : BinaryVector (m+n)) : rightLinear x=rightVector x := rfl

theorem NonzeroFlat.reindex (e : Fin n ≃ Fin m) (f : Signature ℂ n) (hf : NonzeroFlat f) :
    NonzeroFlat (Holant.Tensor.reindex e f) := by
  obtain ⟨c,a,D,ell,hD,rfl⟩ := hf
  refine ⟨c,(fun i => a (e.symm i)),relabelCode e D,ell.comp (coordinateMap e),
    relabelCode_selfDual e D hD,?_⟩
  funext x
  simp only [Holant.Tensor.reindex,signature,value]
  have he : vectorWord (fun i => x (e i))-a=
      coordinateMap e (vectorWord x-(fun i => a (e.symm i))) := by
    funext i
    simp [coordinateMap,vectorWord]
  rw [he]
  rfl

theorem CFlat.reindex (e : Fin n ≃ Fin m) (f : Signature ℂ n) (hf : CFlat f) :
    CFlat (Holant.Tensor.reindex e f) := by
  rcases hf with rfl | hf
  · exact Or.inl rfl
  · exact Or.inr (hf.reindex e f)

theorem NonzeroFlat.tensor (f : Signature ℂ m) (g : Signature ℂ n)
    (hf : NonzeroFlat f) (hg : NonzeroFlat g) : NonzeroFlat (Signature.tensor f g) := by
  obtain ⟨c,a,D,ell,hD,rfl⟩ := hf
  obtain ⟨d,b,E,chi,hE,rfl⟩ := hg
  refine ⟨c*d,joinVector a b,directCode D E,ell.comp leftLinear+chi.comp rightLinear,
    directCode_selfDual D E hD hE,?_⟩
  funext x
  have hl : leftVector (vectorWord x-joinVector a b)=
      vectorWord (fun i => x (Fin.castAdd n i))-a := by
    funext i;simp [leftVector,joinVector,vectorWord]
  have hr : rightVector (vectorWord x-joinVector a b)=
      vectorWord (fun i => x (Fin.natAdd m i))-b := by
    funext i;simp [rightVector,joinVector,vectorWord]
  simp only [Signature.tensor_apply,signature,value,mem_directCode,hl,hr,Units.val_mul,
    LinearMap.add_apply,LinearMap.comp_apply]
  have hvl : leftVector (vectorWord x)=vectorWord (fun i => x (Fin.castAdd n i)) := rfl
  have hvr : rightVector (vectorWord x)=vectorWord (fun i => x (Fin.natAdd m i)) := rfl
  simp only [leftLinear_apply,rightLinear_apply,hvl,hvr,sign_add]
  split_ifs <;> simp_all <;> ring

theorem CFlat.tensor (f : Signature ℂ m) (g : Signature ℂ n)
    (hf : CFlat f) (hg : CFlat g) : CFlat (Signature.tensor f g) := by
  rcases hf with rfl | hf
  · left;funext x;simp
  rcases hg with rfl | hg
  · left;funext x;simp
  exact Or.inr (hf.tensor f g hg)

theorem NonzeroFlat.smul (f : Signature ℂ n) (hf : NonzeroFlat f) (a : ℂ) (ha : a≠0) :
    NonzeroFlat (a • f) := by
  obtain ⟨c,b,D,ell,hD,rfl⟩ := hf
  refine ⟨Units.mk0 a ha*c,b,D,ell,hD,?_⟩
  funext x
  simp only [signature,value,Pi.smul_apply,smul_eq_mul,Units.val_mul,Units.val_mk0]
  split_ifs <;> ring

theorem CFlat.smul (f : Signature ℂ n) (hf : CFlat f) (a : ℂ) : CFlat (a • f) := by
  by_cases ha : a=0
  · left;subst a;simp
  rcases hf with rfl | hf
  · left;simp
  exact Or.inr (hf.smul f a ha)

end
end Holant.ReedMuller.CharacterFlat
