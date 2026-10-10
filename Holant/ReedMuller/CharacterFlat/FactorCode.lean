import Holant.ReedMuller.CharacterFlat.Tensor

/-! Cartesian support directions split into their actual coordinate subcodes.
Self-duality descends by the literal dot-product decomposition. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

@[simp] theorem join_parts (x : BinaryVector (m+n)) :
    joinVector (leftVector x) (rightVector x)=x := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [joinVector,leftVector,rightVector]

@[simp] theorem join_add (x x' : BinaryVector m) (y y' : BinaryVector n) :
    joinVector (x+x') (y+y')=joinVector x y+joinVector x' y' := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [joinVector]

@[simp] theorem join_sub (x x' : BinaryVector m) (y y' : BinaryVector n) :
    joinVector (x-x') (y-y')=joinVector x y-joinVector x' y' := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [joinVector]

@[simp] theorem join_zero : joinVector (0:BinaryVector m) (0:BinaryVector n)=0 := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [joinVector]

def leftEmbedding : BinaryVector m →ₗ[ZMod 2] BinaryVector (m+n) where
  toFun x := joinVector x 0
  map_add' := by intros;simp [←join_add]
  map_smul' := by
    intro c x
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [joinVector]

def rightEmbedding : BinaryVector n →ₗ[ZMod 2] BinaryVector (m+n) where
  toFun x := joinVector 0 x
  map_add' := by intros;simp [←join_add]
  map_smul' := by
    intro c x
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [joinVector]

def leftCode (D : BinaryCode (m+n)) : BinaryCode m := D.comap leftEmbedding
def rightCode (D : BinaryCode (m+n)) : BinaryCode n := D.comap rightEmbedding

@[simp] theorem mem_leftCode (D : BinaryCode (m+n)) (x : BinaryVector m) :
    x∈leftCode D ↔ joinVector x (0:BinaryVector n)∈D := Iff.rfl
@[simp] theorem mem_rightCode (D : BinaryCode (m+n)) (x : BinaryVector n) :
    x∈rightCode D ↔ joinVector (0:BinaryVector m) x∈D := Iff.rfl

def Splits (D : BinaryCode (m+n)) : Prop :=
  ∀ x,x∈D → leftVector x∈leftCode D ∧ rightVector x∈rightCode D

theorem splits_of_cartesian (D : BinaryCode (m+n)) (P : BinaryVector m → Prop)
    (Q : BinaryVector n → Prop)
    (h : ∀ x y,joinVector x y∈D ↔ P x ∧ Q y) : Splits D := by
  have hz := (h 0 0).mp (by simpa using D.zero_mem)
  intro x hx
  have hp := (h (leftVector x) (rightVector x)).mp (by simpa using hx)
  exact ⟨(h _ 0).mpr ⟨hp.1,hz.2⟩,(h 0 _).mpr ⟨hz.1,hp.2⟩⟩

theorem leftCode_selfDual (D : BinaryCode (m+n)) (hD : SelfDual D) (hs : Splits D) :
    SelfDual (leftCode D) := by
  intro x
  constructor
  · intro hx y hy
    have H := (hD _).mp hx _ hy
    change dot (joinVector _ _) (joinVector _ _)=0 at H
    rw [dot_parts,left_join,right_join,left_join,right_join] at H
    simpa [dot] using H
  · intro hx
    apply (hD _).mpr
    intro y hy
    change dot (joinVector _ _) y=0
    rw [dot_parts,left_join,right_join]
    have H := hx (leftVector y) (hs y hy).1
    simpa [dot] using H

theorem rightCode_selfDual (D : BinaryCode (m+n)) (hD : SelfDual D) (hs : Splits D) :
    SelfDual (rightCode D) := by
  intro x
  constructor
  · intro hx y hy
    have H := (hD _).mp hx _ hy
    change dot (joinVector _ _) (joinVector _ _)=0 at H
    rw [dot_parts,left_join,right_join,left_join,right_join] at H
    simpa [dot] using H
  · intro hx
    apply (hD _).mpr
    intro y hy
    change dot (joinVector _ _) y=0
    rw [dot_parts,left_join,right_join]
    have H := hx (rightVector y) (hs y hy).2
    simpa [dot] using H

 theorem split_code_eq (D : BinaryCode (m+n)) (hs : Splits D) :
    D=directCode (leftCode D) (rightCode D) := by
  ext x
  constructor
  · exact hs x
  · intro hx
    have H := D.add_mem hx.1 hx.2
    have he : joinVector (leftVector x) (0:BinaryVector n)+
        joinVector (0:BinaryVector m) (rightVector x)=x := by
      rw [←join_add]
      simpa using join_parts x
    change joinVector (leftVector x) (0:BinaryVector n)+
      joinVector (0:BinaryVector m) (rightVector x)∈D at H
    rwa [he] at H

end
end Holant.ReedMuller.CharacterFlat
