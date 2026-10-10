import Holant.Proofs.Reductions.EightVertexNonexception.NativeChain
import Holant.Proofs.Hardness.GeneralEOAffinePlaneChain

/-! Two copies of the literal complementary even table, joined through Z and
I, have a sparse output. Its compressed trace-zero matrix squares to a scalar
identity. Every coefficient is the original one; no genericity is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinTwistedAlgebra
open Holant
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.EightVertex.ProductAnchor
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

def Z : Kernel K := fun b c=>if b=c then (if b then -1 else 1) else 0

def normal (a b c d : K) : Signature K 4 := table ⟨a,b,c,d,d,c,b,a⟩

def sparse (a c : K) : Signature K 4 := table ⟨a,0,c,0,0,-c,0,-a⟩

def twisted (f : Signature K 4) : Signature K 4 :=
  Signature.contract Signature.equality (Signature.contract Z
    (Tensor.reindex (wiringEquiv ![false,false,true,true]).symm (Signature.tensor f f)))

theorem twisted_normal (a b c d : K) :
    twisted (normal a b c d)=sparse (a^2-b^2) (c^2-d^2) := by
  funext x
  have eval (u v w z : Bool) :
      Tensor.reindex (wiringEquiv ![false,false,true,true]).symm
        (Signature.tensor (normal a b c d) (normal a b c d))
        (Fin.cons u (Fin.cons v (Fin.cons w (Fin.cons z x))))=
      normal a b c d ![x 0,x 1,u,w]*normal a b c d ![v,z,x 2,x 3] := by
    simp only [Tensor.reindex_apply,Signature.tensor_apply]
    congr 1 <;> apply congrArg (normal a b c d) <;> funext i <;> fin_cases i <;> rfl
  unfold twisted Signature.contract
  simp only [Fintype.sum_bool,eval]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Z,Signature.equality,normal,sparse,table,h0,h1,h2,h3] <;> ring

/-- Move the two repeated coordinates adjacent and flip one endpoint in each
pair. This is a real boundary permutation followed by two literal-I legs. -/
def planeOrder : Equiv.Perm (Fin 4) := Equiv.swap 1 2

def planeWord (x : Fin 4→Bool) : Fin 4→Bool := ![x 0,x 2,!(x 1),!(x 3)]

def compressed (a c : K) : Signature K 2 := fun x=>
  if x 0 then (if x 1 then -a else -c) else (if x 1 then c else a)

theorem sparse_plane (a c : K) :
    (fun x=>sparse a c (planeWord x))=EOBinaryPlaneCore.lift (compressed a c) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [planeWord,sparse,table,EOBinaryPlaneCore.lift,compressed,h0,h1,h2,h3]

theorem compressed_square (a c : K) :
    GeneralEOAffinePlaneChain.table (compressed a c)^2=
      (a^2-c^2) • (1 : GeneralEOAffinePlaneChain.Mat (K:=K)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two,GeneralEOAffinePlaneChain.table,compressed,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

/-- The exact residual of all three possible pairings: two squared coefficient
pairs agree. This is derived algebra, not a supplied classification. -/
theorem paired_squares (a b c d : K)
    (h0 : (a^2-b^2)^2=(c^2-d^2)^2)
    (h1 : (a^2-c^2)^2=(b^2-d^2)^2)
    (h2 : (a^2-d^2)^2=(b^2-c^2)^2) (two : (2:K)≠0) :
    (a^2=b^2 ∧ c^2=d^2) ∨ (a^2=c^2 ∧ b^2=d^2) ∨
      (a^2=d^2 ∧ b^2=c^2) := by
  have p0 : (a^2-b^2-c^2+d^2)*(a^2-b^2+c^2-d^2)=0 := by
    linear_combination h0
  have p1 : (a^2-b^2-c^2+d^2)*(a^2+b^2-c^2-d^2)=0 := by
    linear_combination h1
  have p2 : (a^2-b^2+c^2-d^2)*(a^2+b^2-c^2-d^2)=0 := by
    linear_combination h2
  rcases mul_eq_zero.mp p0 with z0|z1
  · rcases mul_eq_zero.mp p2 with z1|z2
    · left
      constructor
      · apply (mul_left_cancel₀ two)
        linear_combination z0+z1
      · apply (mul_left_cancel₀ two)
        linear_combination z1-z0
    · right; left
      constructor
      · apply (mul_left_cancel₀ two)
        linear_combination z0+z2
      · apply (mul_left_cancel₀ two)
        linear_combination z2-z0
  · rcases mul_eq_zero.mp p1 with z0|z2
    · left
      constructor
      · apply (mul_left_cancel₀ two)
        linear_combination z0+z1
      · apply (mul_left_cancel₀ two)
        linear_combination z1-z0
    · right; right
      constructor
      · apply (mul_left_cancel₀ two)
        linear_combination z1+z2
      · apply (mul_left_cancel₀ two)
        linear_combination z2-z1


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinTwistedAlgebra
end
