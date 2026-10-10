import Holant.Proofs.Algorithms.TransformRecognition.RationalRootCode
import Holant.Proofs.Algorithms.TransformRecognition.EncodedGuard


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalCoefficientBindings
open Holant.LocalDrafts.EffectiveAlgebraic MvPolynomial
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
variable {m r n : ℕ}

def target (original : Fin m → RootCode) (rational : Fin r → ℚ) : Fin (m+r) → RootCode :=
  Fin.addCases original (fun j => RationalRootCode.code (rational j))

def values {E : Type*} [Field E] (original : Fin m → E) (rational : Fin r → ℚ) : Fin (m+r) → E :=
  Fin.addCases original (fun j => (rational j : E))

theorem target_represents (original : Fin m → RootCode) (w : Fin m → ℂ)
    (hw : ∀ i, (original i).Represents (w i)) (rational : Fin r → ℚ) :
    ∀ i, (target original rational i).Represents (values w rational i) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [target,values,Fin.addCases_left] using hw i
  | right j => simpa only [target,values,Fin.addCases_right] using RationalRootCode.represents (rational j)

def row (negativeOne : Fin r) (address : Fin m → Fin n) (i : Fin m) :
    EncodedSystem.Equation (m+r) n :=
  [(Fin.castAdd r i,0),(Fin.natAdd m negativeOne,EncodedGuard.hit (address i))]

def rows (negativeOne : Fin r) (address : Fin m → Fin n) : EncodedSystem.System (m+r) n :=
  (List.finRange m).map (row negativeOne address)

noncomputable section

theorem row_eval (w : Fin m → ℂ) (rational : Fin r → ℚ) (negativeOne : Fin r)
    (hneg : rational negativeOne = -1) (address : Fin m → Fin n)
    (i : Fin m) (z : Fin n → ℂ) :
    aeval z (EncodedSystem.polynomial (values w rational) (row negativeOne address i)) =
      w i-z (address i) := by
  simp [row,EncodedSystem.polynomial,values,EncodedGuard.hit,hneg,sub_eq_add_neg]

theorem rows_zero_iff (w : Fin m → ℂ) (rational : Fin r → ℚ) (negativeOne : Fin r)
    (hneg : rational negativeOne=-1) (address : Fin m → Fin n) (z : Fin n → ℂ) :
    (∀ e ∈ rows negativeOne address,
      aeval z (EncodedSystem.polynomial (values w rational) e)=0) ↔
    ∀ i, z (address i)=w i := by
  constructor
  · intro h i
    have he := h _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    rw [row_eval w rational negativeOne hneg] at he
    exact (sub_eq_zero.mp he).symm
  · intro h e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    rw [row_eval w rational negativeOne hneg,h i,sub_self]

/-- A system with these physical rows added has precisely the corresponding
substitution constraints, including repeated appearances of each entry. -/
theorem append_zero_iff (w : Fin m → ℂ) (rational : Fin r → ℚ) (negativeOne : Fin r)
    (hneg : rational negativeOne=-1) (address : Fin m → Fin n)
    (S : EncodedSystem.System (m+r) n) (z : Fin n → ℂ) :
    (∀ e ∈ rows negativeOne address ++ S,
      aeval z (EncodedSystem.polynomial (values w rational) e)=0) ↔
    (∀ i, z (address i)=w i) ∧
      ∀ e ∈ S, aeval z (EncodedSystem.polynomial (values w rational) e)=0 := by
  rw [List.forall_mem_append,rows_zero_iff w rational negativeOne hneg]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalCoefficientBindings
