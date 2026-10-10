import Holant.ReedMuller.FlatNetwork.Relabel
import Holant.OrderedTensor

/-! Disjoint tensor products retain self-dual directions, affine shifts and
all nonzero component scalars, including the empty nullary product. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

def joinVector (x : BinaryVector m) (y : BinaryVector n) : BinaryVector (m+n) := Fin.addCases x y
def leftVector (x : BinaryVector (m+n)) : BinaryVector m := fun i => x (Fin.castAdd n i)
def rightVector (x : BinaryVector (m+n)) : BinaryVector n := fun i => x (Fin.natAdd m i)

@[simp] theorem left_join (x : BinaryVector m) (y : BinaryVector n) : leftVector (joinVector x y)=x := by
  funext i
  simp [leftVector,joinVector]
@[simp] theorem right_join (x : BinaryVector m) (y : BinaryVector n) : rightVector (joinVector x y)=y := by
  funext i
  simp [rightVector,joinVector]

theorem dot_parts (x y : BinaryVector (m+n)) :
    dot x y=dot (leftVector x) (leftVector y)+dot (rightVector x) (rightVector y) :=
  Fin.sum_univ_add _

def directCode (D : BinaryCode m) (E : BinaryCode n) : BinaryCode (m+n) where
  carrier := {x | leftVector x∈D ∧ rightVector x∈E}
  zero_mem' := ⟨D.zero_mem,E.zero_mem⟩
  add_mem' := fun hx hy => ⟨D.add_mem hx.1 hy.1,E.add_mem hx.2 hy.2⟩
  smul_mem' := fun c x hx => ⟨D.smul_mem c hx.1,E.smul_mem c hx.2⟩

@[simp] theorem mem_directCode (D : BinaryCode m) (E : BinaryCode n)
    (x : BinaryVector (m+n)) : x∈directCode D E ↔ leftVector x∈D ∧ rightVector x∈E := Iff.rfl

theorem directCode_selfDual (D : BinaryCode m) (E : BinaryCode n)
    (hD : SelfDual D) (hE : SelfDual E) : SelfDual (directCode D E) := by
  intro x
  constructor
  · rintro ⟨hx0,hx1⟩ y ⟨hy0,hy1⟩
    rw [dot_parts,(hD _).mp hx0 _ hy0,(hE _).mp hx1 _ hy1,zero_add]
  · intro hx
    constructor
    · apply (hD _).mpr
      intro y hy
      have hj : joinVector y (0:BinaryVector n)∈directCode D E := by
        exact ⟨by simpa using hy,by simp⟩
      have H := hx _ hj
      rw [dot_parts,left_join,right_join] at H
      simpa [dot] using H
    · apply (hE _).mpr
      intro y hy
      have hj : joinVector (0:BinaryVector m) y∈directCode D E := by
        exact ⟨by simp,by simpa using hy⟩
      have H := hx _ hj
      rw [dot_parts,left_join,right_join] at H
      simpa [dot] using H

theorem flat_tensor (f : Signature ℂ m) (g : Signature ℂ n) (hf : Flat f) (hg : Flat g) :
    Flat (Signature.tensor f g) := by
  obtain ⟨c,a,D,hD,rfl⟩ := hf
  obtain ⟨d,b,E,hE,rfl⟩ := hg
  refine ⟨c*d,joinVector a b,directCode D E,directCode_selfDual D E hD hE,?_⟩
  funext x
  have hleft : leftVector (fun i => bit (x i)-joinVector a b i)=
      (fun i => bit (x (Fin.castAdd n i))-a i) := by
    funext i
    simp [leftVector,joinVector]
  have hright : rightVector (fun i => bit (x i)-joinVector a b i)=
      (fun i => bit (x (Fin.natAdd m i))-b i) := by
    funext i
    simp [rightVector,joinVector]
  simp only [Signature.tensor_apply,flatSignature]
  simp only [mem_directCode]
  rw [hleft,hright,Units.val_mul]
  split_ifs <;> simp_all

theorem flatOrZero_tensor (f : Signature ℂ m) (g : Signature ℂ n)
    (hf : FlatOrZero f) (hg : FlatOrZero g) : FlatOrZero (Signature.tensor f g) := by
  rcases hf with rfl | hf
  · left;funext x;simp
  rcases hg with rfl | hg
  · left;funext x;simp
  exact Or.inr (flat_tensor f g hf hg)

theorem emptyCode_selfDual : SelfDual (⊥ : BinaryCode 0) := by
  intro x
  have hx : x=0 := Subsingleton.elim _ _
  subst x
  simp [dot]

theorem nullary_unit_flat : Flat (Signature.scalar (1:ℂ)) := by
  refine ⟨1,0,⊥,emptyCode_selfDual,?_⟩
  funext x
  have hx : (fun i => bit (x i))=(0 : BinaryVector 0) := Subsingleton.elim _ _
  simp [flatSignature,Signature.scalar,hx]

end
end Holant.ReedMuller.FlatNetwork
