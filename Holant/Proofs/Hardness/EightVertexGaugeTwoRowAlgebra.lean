import Holant.Proofs.Hardness.GeneralCancellationCapPin
import Holant.Proofs.Hardness.EightVertexGaugeTwoRowNetwork
import Holant.Proofs.Dichotomy.Retained.StableDenseResidualGaugeCore
import Holant.Proofs.Hardness.EightVertexGaugeSectorAlgebra

/-! Exact two-row analysis on the weighted-even residual locus. Both vanishing
sector cases are retained as explicit products of binary tensors. A live
sector defect is only a failure of the complementary-product equations;
it is not called hardness or an exclusion of the affine/local-affine classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowAlgebra
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open StableDenseResidualGaugeCore
namespace TwoRow
export EightVertexGaugeTwoRowNetwork (network term denote realizes)
end TwoRow
variable {K : Type} [Field K]

export EightVertexGaugeSectorAlgebra
  (evenFactor oddFactor output defect straight_factor crossed_factor self_crossed_factor output_full)

/-- A complete native-network evaluation, with the original scalars retained. -/
theorem network_output (a b : K) (u v : Fin 4 → K) (cross : Bool) :
    (TwoRow.network (weighted a u) (weighted b v) cross).denote = output a b u v cross := by
  funext x
  rw [TwoRow.denote,word_eta x]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    cases cross <;>
    simp [TwoRow.term,EightVertexGaugeTwoRowNetwork.term,weighted,output,table,
      evenFactor,oddFactor] <;> ring

theorem output_realizes (a b : K) (u v : Fin 4 → K) (cross : Bool)
    (F : SignatureFamily K)
    (hM : (⟨4,weighted a u⟩ : AnySignature K) ∈ F)
    (hN : (⟨4,weighted b v⟩ : AnySignature K) ∈ F) :
    Gadget.Realizes F .disequality (output a b u v cross) := by
  rw [← network_output]
  exact TwoRow.realizes _ _ cross F hM hN

/-- A live two-row output remains on the residual locus exactly when its
two sector factors have equal squares. No tractable-class conclusion occurs. -/
theorem products_iff (a b : K) (u v : Fin 4 → K) (cross : Bool)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) :
    StableDenseResidualGaugeCore.Products (output a b u v cross) ↔
      evenFactor u v ^ 2 = oddFactor u v cross ^ 2 := by
  have hc : (a*b)^2*u 0*u 1*v 0*v 1 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (mul_ne_zero ha hb)) (hu 0)) (hu 1)) (hv 0)) (hv 1)
  constructor
  · intro h
    have hz := defect a b u v cross
    rw [h.2.1,sub_self] at hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz.symm).resolve_left hc)
  · intro h
    unfold StableDenseResidualGaugeCore.Products
    refine ⟨?_,?_,?_⟩
    · change (a*b*evenFactor u v)*(a*b*u 0*u 1*v 0*v 1*evenFactor u v) =
        (a*b*v 0*v 1*evenFactor u v)*(a*b*u 0*u 1*evenFactor u v)
      ring
    · change (a*b*evenFactor u v)*(a*b*u 0*u 1*v 0*v 1*evenFactor u v) =
        (a*b*u 1*v 1*oddFactor u v cross)*(a*b*u 0*v 0*oddFactor u v cross)
      linear_combination (a*b)^2*u 0*u 1*v 0*v 1 * h
    · change (a*b*evenFactor u v)*(a*b*u 0*u 1*v 0*v 1*evenFactor u v) =
        (a*b*u 1*v 0*oddFactor u v cross)*(a*b*u 0*v 1*oddFactor u v cross)
      linear_combination (a*b)^2*u 0*u 1*v 0*v 1 * h

def diagonalTensor (r s : K) : Signature K 2 := fun x =>
  if x 0 then (if x 1 then s else 0) else (if x 1 then 0 else r)

/-- If the odd sector vanishes, the surviving tensor is a literal product
of two weighted equalities, including a possible zero scalar. -/
theorem odd_zero_product (a b : K) (u v : Fin 4 → K) (cross : Bool)
    (hO : oddFactor u v cross = 0) :
    output a b u v cross = fun x => a*b*evenFactor u v *
      Signature.tensor (diagonalTensor 1 (u 0*u 1))
        (diagonalTensor 1 (v 0*v 1)) x := by
  funext x
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp [output,table,hO,Signature.tensor_apply,diagonalTensor] <;> ring

/-- If the even sector vanishes, the surviving tensor is a literal product
of two weighted disequalities, including a possible zero scalar. -/
theorem even_zero_product (a b : K) (u v : Fin 4 → K) (cross : Bool)
    (hE : evenFactor u v = 0) :
    output a b u v cross = fun x => a*b*oddFactor u v cross *
      Signature.tensor (GeneralCancellationCapPin.antiTensor (u 1) (u 0))
        (GeneralCancellationCapPin.antiTensor (v 1) (v 0)) x := by
  funext x
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp [output,table,hE,Signature.tensor_apply,GeneralCancellationCapPin.antiTensor] <;> ring

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowAlgebra
end
