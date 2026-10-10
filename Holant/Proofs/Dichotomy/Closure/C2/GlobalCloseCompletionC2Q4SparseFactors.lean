import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSixSquare
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! The determinant-zero sparse cases have explicit proper two-binary
splits in the original coefficient field, including their exact port order.
They therefore cannot be a prime current quaternary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4SparseFactors
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def binary (p : Bool) (a b : K) : Signature K 2 := fun x=>
  if x 1=(x 0 ^^ p) then (if x 0 then b else a) else 0

def crossing : (Fin 2⊕Fin 2)≃Fin 4 := Equiv.ofBijective
  (Sum.elim (![0,3] : Fin 2→Fin 4) (![1,2] : Fin 2→Fin 4)) (by decide)

def straight : (Fin 2⊕Fin 2)≃Fin 4 := Equiv.ofBijective
  (Sum.elim (![0,1] : Fin 2→Fin 4) (![2,3] : Fin 2→Fin 4)) (by decide)

theorem signed_not_prime (B C : K) (hB : B≠0) (sum : B^2+C^2=0) :
    ¬Prime (⟨4,S.signed B C 0⟩ : AnySignature K) := by
  intro prime
  apply prime.2
  refine ⟨⟨2,binary true 1 (C/B)⟩,⟨2,binary true B C⟩,⟨{
    left_pos := by change 0<2;decide
    right_pos := by change 0<2;decide
    ports := crossing
    scale := 1
    equation := ?_ }⟩⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [S.signed,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,binary,crossing,h0,h1,h2,h3]
  all_goals field_simp [hB]
  all_goals first | (solve | ring) | (solve | linear_combination sum) | (solve | linear_combination -sum)

theorem pair_not_prime (A D : K) (hA : A≠0) (squares : A^2=D^2) :
    ¬Prime (⟨4,T.normal A 0 0 D⟩ : AnySignature K) := by
  intro prime
  apply prime.2
  refine ⟨⟨2,binary false 1 (D/A)⟩,⟨2,binary false A D⟩,⟨{
    left_pos := by change 0<2;decide
    right_pos := by change 0<2;decide
    ports := crossing
    scale := 1
    equation := ?_ }⟩⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,binary,crossing,h0,h1,h2,h3]
  all_goals field_simp [hA]
  all_goals first | (solve | ring) | (solve | linear_combination squares) | (solve | linear_combination -squares)

theorem eo_not_prime (C D : K) (hC : C≠0) (squares : C^2=D^2) :
    ¬Prime (⟨4,T.normal 0 0 C D⟩ : AnySignature K) := by
  intro prime
  apply prime.2
  refine ⟨⟨2,binary true 1 (D/C)⟩,⟨2,binary true C D⟩,⟨{
    left_pos := by change 0<2;decide
    right_pos := by change 0<2;decide
    ports := straight
    scale := 1
    equation := ?_ }⟩⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,binary,straight,h0,h1,h2,h3]
  all_goals field_simp [hC]
  all_goals first | (solve | ring) | (solve | linear_combination squares) | (solve | linear_combination -squares)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4SparseFactors
end
