import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWGeneralCore

/-! Three independently transformed W ports also admit an equality/X
triangle with nonzero repeated-column contraction. The choice is proved in
Hadamard coordinates; only the actual equality or X edge is constructed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWGeneralXCore
open Holant Holant.Tractable
namespace W
export GlobalCloseCompletionIndependentPinsWGeneralCore (image core)
end W
namespace Z
export GlobalCloseCompletionIndependentPinsWGeneralCore (gram choose_pair)
end Z
namespace X
export GlobalCloseCompletionIndependentPinsWX (flip)
end X
namespace T
export GlobalCloseCompletionTernaryGHZCore (triangle action)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def gram (B C : Kernel K) (i j : Bool) : K := B false i*C true j+B true i*C false j

theorem triangle_image (A B C : Kernel K) :
    T.triangle (X.flip (W.image A B C))=T.action (Matrix.of A)
      (W.core (gram B C false false) (gram B C false true)
        (gram B C true false) (gram B C true true)) := by
  funext x
  simp [T.triangle,X.flip,W.image,T.action,W.core,gram,Fintype.sum_bool]
  ring

theorem gram_determinant (B C : Kernel K) :
    gram B C false false*gram B C true true-gram B C false true*gram B C true false=
      -(B false false*B true true-B false true*B true false)*
        (C false false*C true true-C false true*C true false) := by
  simp only [gram]
  ring

def hadamard (A : Kernel K) : Kernel K := fun i j=>
  if i then A false j-A true j else A false j+A true j

theorem hadamard_det (A : Kernel K) :
    hadamard A false false*hadamard A true true-hadamard A false true*hadamard A true false=
      -2*(A false false*A true true-A false true*A true false) := by
  simp only [hadamard,Bool.false_eq_true,ite_false,ite_true]
  ring

theorem hadamard_gram (A B : Kernel K) (v : Bool) :
    Z.gram (if v then -1 else 1) (hadamard A) (hadamard B) false false=
      2*(if v then gram A B false false else Z.gram 1 A B false false) := by
  cases v <;> simp only [Bool.false_eq_true,ite_false,ite_true,Z.gram,gram,hadamard]
  all_goals ring

theorem choose_pair [CharZero K] (A B C : Kernel K)
    (ha : A false false*A true true-A false true*A true false≠0)
    (hb : B false false*B true true-B false true*B true false≠0)
    (hc : C false false*C true true-C false true*C true false≠0) :
    (∃v : Bool,(if v then gram B C false false else Z.gram 1 B C false false)≠0) ∨
    (∃v : Bool,(if v then gram A B false false else Z.gram 1 A B false false)≠0) ∨
    (∃v : Bool,(if v then gram C A false false else Z.gram 1 C A false false)≠0) := by
  have det (M : Kernel K) (h : M false false*M true true-M false true*M true false≠0) :
      hadamard M false false*hadamard M true true-hadamard M false true*hadamard M true false≠0 := by
    rw [hadamard_det]
    exact mul_ne_zero (by norm_num) h
  have lift (M N : Kernel K) :
      (∃v : Bool,Z.gram (if v then -1 else 1) (hadamard M) (hadamard N) false false≠0)→
      ∃v : Bool,(if v then gram M N false false else Z.gram 1 M N false false)≠0 := by
    rintro ⟨v,h⟩
    refine ⟨v,?_⟩
    rw [hadamard_gram] at h
    exact (mul_ne_zero_iff.mp h).2
  rcases Z.choose_pair (hadamard A) (hadamard B) (hadamard C) (det A ha) (det B hb) (det C hc) with bc|ab|ca
  · exact Or.inl (lift B C bc)
  · exact Or.inr (Or.inl (lift A B ab))
  · exact Or.inr (Or.inr (lift C A ca))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWGeneralXCore
end
