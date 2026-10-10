import Holant.Proofs.Hardness.TwoCoefficientData
import Holant.Proofs.Hardness.ExactTwoSignatures
import Holant.Proofs.Hardness.DenseEOUnitLocal

/-! Literal ordered two-coefficient EO tensors. The distinguished pair is
0101/1010; the other four middle words carry b. No pin access or ratio
condition is contained in these definitions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientSignatures
open Holant
open Holant.LocalDrafts.Hardness.EightVertexNonexception
variable {K : Type*} [Field K]

def weighted (a b : K) : Signature K 4 := table ⟨0,b,a,b,b,a,b,0⟩

theorem linear (a b : K) : weighted a b=a • ExactTwoSignatures.E+b • ExactTwoSignatures.B := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [weighted,ExactTwoSignatures.E,ExactTwoSignatures.B,table,h0,h1,h2,h3]

theorem self_dual (a b : K) (x : Fin 4 → Bool) : weighted a b (fun i=>!x i)=weighted a b x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [weighted,table,h0,h1,h2,h3]

theorem eo (a b : K) : DenseEOUnitLocal.EOSupport (weighted a b) := by
  intro x hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [weight,show (Finset.univ : Finset (Fin 4))={0,1,2,3} by decide,
      Finset.filter_insert,Finset.filter_singleton,h0,h1,h2,h3] at hx <;>
    simp [weighted,table,h0,h1,h2,h3]

theorem middle (a b : K) (ha : a≠0) (hb : b≠0) :
    DenseEOUnitLocal.NonzeroMiddle (weighted a b) := by
  simp [DenseEOUnitLocal.NonzeroMiddle,entries,weighted,table,ha,hb]

def middleSwap : Equiv.Perm (Fin 4) where
  toFun := ![0,2,1,3]
  invFun := ![0,2,1,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Swapping original ports1/2 moves the distinguished coefficient to the
0011/1100 pair; it is not a relabelling of the signature dictionary. -/
theorem swapped_table (a b : K) : Tensor.reindex middleSwap (weighted a b)=table ⟨0,a,b,b,b,b,a,0⟩ := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex_apply,middleSwap,weighted,table,h0,h1,h2,h3]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientSignatures
