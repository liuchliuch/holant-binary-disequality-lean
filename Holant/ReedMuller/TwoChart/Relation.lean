import Holant.ReedMuller.TwoChart.ObstructionWitnesses
import Holant.ReedMuller.CharacterFlat.FactorCode
import Holant.ReedMuller.CharacterFlat.Converse

/-! The actual localizer relation is self-dual by its original-coordinate
isometry and half-dimension calculation. Its character-flat realization is a
conclusion of the proved RM/ordered-Bell network calculus. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

 def relationMap (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m) :
    (S×J) →ₗ[ZMod 2] BinaryVector (n+m) where
  toFun x := joinVector (x.1.val+x.2.val) (phi x.1)
  map_add' := by
    intro x y
    change joinVector ((x.1.val+y.1.val)+(x.2.val+y.2.val)) (phi (x.1+y.1))=
      joinVector (x.1.val+x.2.val) (phi x.1)+joinVector (y.1.val+y.2.val) (phi y.1)
    rw [map_add,←join_add]
    congr 1
    abel
  map_smul' := by
    intro c x
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp [joinVector,mul_add]
    · simp [joinVector,map_smul]

 def relationCode (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m) : BinaryCode (n+m) :=
  LinearMap.range (relationMap S J phi)

 theorem relationMap_injective (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m) :
    Function.Injective (relationMap S J phi) := by
  intro x y h
  have hR := congrArg rightVector h
  have hs : x.1=y.1 := phi.injective (by simpa only [relationMap,LinearMap.coe_mk,
    AddHom.coe_mk,right_join] using hR)
  have hL := congrArg leftVector h
  have hj : x.2=y.2 := by
    apply Subtype.ext
    simpa only [relationMap,LinearMap.coe_mk,AddHom.coe_mk,left_join,hs,add_right_inj] using hL
  exact Prod.ext hs hj

 theorem relationCode_finrank (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m) :
    Module.finrank (ZMod 2) (relationCode S J phi)=m+Module.finrank (ZMod 2) J := by
  rw [relationCode,LinearMap.finrank_range_of_inj (relationMap_injective S J phi),Module.finrank_prod]
  rw [phi.finrank_eq]
  simp [BinaryVector]

 theorem relationCode_selfDual (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (hphi : ∀ s t : S,dot (phi s) (phi t)=dot s.val t.val)
    (hJ : ∀ j∈J,∀ k∈J,dot j k=0)
    (horth : ∀ s∈S,∀ j∈J,dot s j=0)
    (hdim : m+2*Module.finrank (ZMod 2) J=n) : SelfDual (relationCode S J phi) := by
  apply selfDual_of_selfOrthogonal_halfDimension
  · rintro x ⟨⟨s,j⟩,rfl⟩ y ⟨⟨t,k⟩,rfl⟩
    change dot (joinVector (s.val+j.val) (phi s)) (joinVector (t.val+k.val) (phi t))=0
    rw [dot_parts,left_join,right_join,left_join,right_join,dot_add_left,dot_add_right,
      dot_add_right,hphi,horth _ s.property _ k.property,hJ _ j.property _ k.property]
    have hjs : dot j.val t.val=0 := by rw [dot_comm];exact horth _ t.property _ j.property
    rw [hjs]
    simpa using (CharTwo.add_self_eq_zero (dot s.val t.val))
  · rw [relationCode_finrank]
    omega

 theorem localizer_character_flat (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (hphi : ∀ s t : S,dot (phi s) (phi t)=dot s.val t.val)
    (hJ : ∀ j∈J,∀ k∈J,dot j k=0)
    (horth : ∀ s∈S,∀ j∈J,dot s j=0)
    (hdim : m+2*Module.finrank (ZMod 2) J=n)
    (p : BinaryVector n) (chi : Character (n+m)) :
    NonzeroFlat (signature 1 (joinVector p 0) (relationCode S J phi) chi) :=
  ⟨1,joinVector p 0,relationCode S J phi,chi,
    relationCode_selfDual S J phi hphi hJ horth hdim,rfl⟩

end
end Holant.ReedMuller.TwoChart
