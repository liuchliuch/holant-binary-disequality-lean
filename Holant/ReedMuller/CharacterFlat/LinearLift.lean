import Holant.ReedMuller.CharacterFlat.Basic

/-! Literal linear sections of a two-port contraction and its complete sign
sum. A nontrivial character cancels the entire two-element fibre. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def tailEmbedding : BinaryVector n →ₗ[ZMod 2] BinaryVector (n+2) where
  toFun x := prepend 0 x
  map_add' := by intro x y;funext i;refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [prepend]
  map_smul' := by intro c x;funext i;refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [prepend]

def dotLinear (z : BinaryVector n) : Character n where
  toFun x := dot x z
  map_add' := fun x y => dot_add_left x y z
  map_smul' := fun c x => dot_smul_left c x z

def sectionLinear (z : BinaryVector n) : BinaryVector n →ₗ[ZMod 2] BinaryVector (n+2) where
  toFun x := prepend (dot x z) x
  map_add' := by intro x y;funext i;refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [prepend,dot_add_left]
  map_smul' := by intro c x;funext i;refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [prepend,dot_smul_left]

theorem lift_linear_decomposition (eta b : ZMod 2) (x : BinaryVector n) :
    lift eta b x=lift eta 0 0+tailEmbedding x+b • pairWord n := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
    simp [lift,tailEmbedding,prepend,pairWord,add_comm]

theorem character_lift (ell : Character (n+2)) (eta b : ZMod 2) (x : BinaryVector n) :
    ell (lift eta b x)=ell (lift eta 0 0)+ell (tailEmbedding x)+b*ell (pairWord n) := by
  rw [lift_linear_decomposition,map_add,map_add,map_smul]
  rfl

theorem lift_affine_section (eta b : ZMod 2) (z x : BinaryVector n) :
    lift eta (b+dot x z) x=lift eta b 0+sectionLinear z x := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
    simp [lift,sectionLinear,prepend,add_assoc,add_comm,add_left_comm]

theorem character_affine_section (ell : Character (n+2)) (eta b : ZMod 2) (z x : BinaryVector n) :
    ell (lift eta (b+dot x z) x)=ell (lift eta b 0)+(ell.comp (sectionLinear z)) x := by
  rw [lift_affine_section,map_add]
  rfl

theorem sign_sum_lift (ell : Character (n+2)) (eta : ZMod 2) (x : BinaryVector n) :
    (∑ b : ZMod 2,sign (ell (lift eta b x)))=
      if ell (pairWord n)=0 then
        2*sign (ell (lift eta 0 0))*sign ((ell.comp tailEmbedding) x) else 0 := by
  have he : (∑ b : ZMod 2,sign (ell (lift eta b x)))=
      ∑ b : ZMod 2,sign ((ell (lift eta 0 0)+ell (tailEmbedding x))+b*ell (pairWord n)) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [character_lift]
  rw [he,sign_sum]
  split_ifs <;> simp only [sign_add,LinearMap.comp_apply] <;> ring

end
end Holant.ReedMuller.CharacterFlat
