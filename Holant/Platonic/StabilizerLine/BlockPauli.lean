import Holant.Platonic.StabilizerLine.Pauli

/-! Exact Pauli conjugation by the normalized partial Hadamard, including its
fourth-root phase and both unchanged and transformed logical coordinates. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n r s : ℕ}

theorem walshKernel_vector (x y : Word r) :
    (walshKernel x y:ℂ)=sign (dot (vectorWord x) (vectorWord y)) := by
  rw [walshKernel_dot]
  rfl

def firstCharacter (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) : BinaryVector r →ₗ[ZMod 2] ZMod 2 :=
  ell.comp (e.symm.toLinearMap.comp (LinearMap.inl ..))

def blockZLabel (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) : BinaryVector r := characterLabel (firstCharacter e ell)

theorem block_character (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) (a : BinaryVector r) (b : BinaryVector s) :
    ell (e.symm (a,b))=dot (blockZLabel e ell) a+ell (e.symm (0,b)) := by
  have hp : (a,b)=(a,0)+(0,b) := by simp
  rw [hp,map_add,map_add]
  rw [blockZLabel,characterLabel_dot]
  rfl

def residualMap (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) :
    BinaryVector n →ₗ[ZMod 2] BinaryVector n :=
  e.symm.toLinearMap.comp ((0 : BinaryVector n →ₗ[ZMod 2] BinaryVector r).prod (rightCoordinates e))

def blockPauli (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) (P : Pauli n) : Pauli n where
  phase := P.phase+Holant.Tractable.TwoTranslate.evenLift (dot (blockZLabel e P.character) (e P.shift).1)
  shift := e.symm (blockZLabel e P.character,(e P.shift).2)
  character := (dotBilinear (e P.shift).1).comp (leftCoordinates e)+P.character.comp (residualMap e)

theorem block_pauli_exponent
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (P : Pauli n) (y t : BinaryVector r) (z : BinaryVector s) :
    dot y (t+(e P.shift).1)+P.character (e.symm (t+(e P.shift).1,z))=
      dot (blockZLabel e P.character) (e P.shift).1+
        (dot (e P.shift).1 y+P.character (e.symm (0,z)))+
        dot (y+blockZLabel e P.character) t := by
  rw [block_character]
  simp only [dot_add_right,dot_add_left]
  rw [dot_comm y (e P.shift).1]
  abel

theorem block_pauli_shift
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (P : Pauli n) (t : Word r) (z : Word s) :
    wordVector (vectorWord ((wordBlockEquiv e).symm
      (xor t (wordVector (e P.shift).1),z))+P.shift)=
      (wordBlockEquiv e).symm (t,wordVector (vectorWord z+(e P.shift).2)) := by
  apply vector_injective
  simp only [wordBlockEquiv,Equiv.coe_fn_symm_mk,vector_word,vector_xor]
  apply e.injective
  simp only [map_add,LinearEquiv.apply_symm_apply]
  ext i <;> simp [add_assoc,CharTwo.add_self_eq_zero]

theorem blockWalsh_normalizes
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) :
    NormalizesPauli (blockWalsh e) := by
  intro P
  refine ⟨blockPauli e P,?_⟩
  intro f
  funext x
  obtain ⟨⟨y,z⟩,rfl⟩ := (wordBlockEquiv e).symm.surjective x
  have hp : wordVector (vectorWord ((wordBlockEquiv e).symm (y,z))+(blockPauli e P).shift)=
      (wordBlockEquiv e).symm (wordVector (vectorWord y+blockZLabel e P.character),
        wordVector (vectorWord z+(e P.shift).2)) := by
    apply vector_injective
    simp only [wordBlockEquiv,Equiv.coe_fn_symm_mk,vector_word,blockPauli]
    rw [←map_add]
    rfl
  have he : (blockPauli e P).character (vectorWord ((wordBlockEquiv e).symm (y,z)))=
      dot (e P.shift).1 (vectorWord y)+P.character (e.symm (0,vectorWord z)) := by
    simp [blockPauli,leftCoordinates,residualMap,rightCoordinates,wordBlockEquiv,
      dotBilinear_apply]
  change blockWalsh e (P.run f) ((wordBlockEquiv e).symm (y,z))=
    phaseRoot (blockPauli e P).phase*
      sign ((blockPauli e P).character (vectorWord ((wordBlockEquiv e).symm (y,z))))*
      blockWalsh e f (wordVector (vectorWord ((wordBlockEquiv e).symm (y,z))+(blockPauli e P).shift))
  rw [hp,he,blockWalsh_at_block,blockWalsh_at_block]
  rw [←(xorEquiv (wordVector (e P.shift).1)).sum_comp]
  simp only [xorEquiv,Equiv.coe_fn_mk,Pauli.run,block_pauli_shift,walshKernel_vector,
    vector_xor,vector_word,blockPauli,phaseRoot_add,phaseRoot_even]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hs := congrArg sign (block_pauli_exponent e P (vectorWord y) (vectorWord t) (vectorWord z))
  simp only [sign_add] at hs
  simp only [wordBlockEquiv,Equiv.coe_fn_symm_mk,vector_word,vector_xor,sign_add] at hs ⊢
  linear_combination ((sqrtTwo⁻¹^r:AlgebraicComplex):ℂ)*phaseRoot P.phase*
    f (wordVector (e.symm (vectorWord t,vectorWord z+(e P.shift).2)))*hs

end
end Holant.Platonic.StabilizerLine
