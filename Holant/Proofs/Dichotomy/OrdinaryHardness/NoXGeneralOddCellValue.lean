import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddTerminalNetwork
import Holant.Proofs.Tetrahedral.EvenCSPReduction.Semantics

/-! Simultaneous conditioning of actual cell-edge bits is exactly conditioning
the corresponding original CSP variables. Unused variables retain their two
choices, and every unsupported physical edge assignment vanishes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddCellValue
open Holant Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace C
export Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Compilation
  (cell sourceNetwork Words flatWords bits Supported supportedVariables supported_bits rowProduct rowProduct_guard vertex_product)
end C
namespace T
export NoXGeneralOddTerminalNetwork (weight)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (eqLabel : Fin s)
variable (eqLiteral : (⟨a eqLabel.val,H eqLabel⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (r : Raw.Input s a)
variable (selected : Fin n→Fin (C.sourceNetwork r H eqLabel eqLiteral).shape.edges)
variable (slots : Fin n→Fin r.val.variables)
variable (same : ∀w : C.Words r,C.Supported r w→∀j,
  C.flatWords r w (selected j)=w (slots j) (C.cell r (slots j)).root)

include same in
theorem value (z : Fin n→Bool) :
    (∑c : Fin (C.sourceNetwork r H eqLabel eqLiteral).shape.edges→Bool,
      if (fun j=>c (selected j))=z then T.weight (C.sourceNetwork r H eqLabel eqLiteral) c else 0)=
    ∑x : Fin r.val.variables→Bool,if (fun j=>x (slots j))=z then
      Raw.factorWeight H r (fun p=>x (Raw.route r p)) else 0 := by
  classical
  have weights (w : C.Words r) : T.weight (C.sourceNetwork r H eqLabel eqLiteral) (C.flatWords r w)=
      Raw.factorWeight H r (C.bits r w)*C.rowProduct (K:=K) r w := C.vertex_product r H eqLabel eqLiteral w
  erw [←Equiv.sum_comp (C.flatWords r)]
  simp_rw [weights,C.rowProduct_guard]
  rw [Finset.sum_congr_set {w : C.Words r | C.Supported r w}
    (fun w=>if (fun j=>C.flatWords r w (selected j))=z then
      Raw.factorWeight H r (C.bits r w)*(if C.Supported r w then 1 else 0) else 0)
    (fun w=>if (fun j=>w.val (slots j) (C.cell r (slots j)).root)=z then Raw.factorWeight H r (C.bits r w.val) else 0)
    (by
      intro w hw
      change C.Supported r w at hw
      simp only [ite_eq_left hw,mul_one]
      simp_rw [same w hw])
    (by
      intro w hw
      change ¬C.Supported r w at hw
      simp only [ite_eq_right hw,mul_zero,ite_self])]
  apply Fintype.sum_equiv (C.supportedVariables r)
  intro w
  change (if (fun j=>w.val (slots j) (C.cell r (slots j)).root)=z then Raw.factorWeight H r (C.bits r w.val) else 0)=
    (if (fun j=>w.val (slots j) (C.cell r (slots j)).root)=z then
      Raw.factorWeight H r (fun p=>w.val (Raw.route r p) (C.cell r (Raw.route r p)).root) else 0)
  congr 1
  congr 1
  funext p
  exact C.supported_bits r w.val w.property p

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddCellValue
end
