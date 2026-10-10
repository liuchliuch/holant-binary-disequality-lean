import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationBlocks
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationEighth
import Holant.Proofs.Dichotomy.Native.NativeTableBase

/-! Exhaustive controlled consumption of an actual nonzero two-block row.
The finite residuals are literal pure Eq4 or a complete diagonal product;
the other cases use actual native EO/Ising source programmes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationBlockSource
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace S
export GlobalCloseCompletionComplementQ4Series (row)
end S
namespace B
export GlobalCloseCompletionComplementQ4ClassificationBlocks
  (eo eo_value square square_value Pure DiagonalProduct pure_of_zero product_of_equal_square pure_of_fourth repaired)
end B
namespace T
export GlobalCloseCompletionComplementQ4Templates (connect)
end T
namespace O
export PaperControlled.C2NativePairOutcome (Macro)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {size degree : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin size)→Signature K (arity i.val)) (F : FixedField K degree)
variable (phi : K→+*ℂ)

abbrev Hard : Prop := PaperControlledHardness.Hard
  (RawClosedNetwork.validatedEncoding size 1 arity) F.encoding ((NativeAntiTargetSource.base H F).evaluate F)
def Outcome : Prop := B.Pure H ∨ Nonempty (B.DiagonalProduct H) ∨ Hard H F

def eoMacro (N : NativeAntiTargetSource.Output H 4) : O.Macro H where
  network:=(B.eo H N).network
  labels:=(B.eo H N).labels
  exact:=(B.eo H N).exact
  native:=(B.eo H N).native

include phi in
theorem hard_of_eighth (N : NativeAntiTargetSource.Output H 4) (a b : K)
    (form : N.network.denote=S.row a b 0 0) (ha : a≠0) (hb : b≠0) (eighth : a^8≠b^8) : Hard H F := by
  apply GlobalCloseCompletionComplementQ4ClassificationIsing.hard F H phi (eoMacro H N) (a^2) (b^2)
    (B.eo_value H N a b form) (pow_ne_zero _ ha) (pow_ne_zero _ hb)
  intro h
  apply eighth
  simpa only [←pow_mul] using h

include phi in
theorem nonzero_left (N : NativeAntiTargetSource.Output H 4) (a b : K)
    (form : N.network.denote=S.row a b 0 0) (ha : a≠0) : Outcome H F := by
  classical
  by_cases hb : b=0
  · subst b
    exact Or.inl (B.pure_of_zero H N a ha form)
  by_cases squares : a^2=b^2
  · exact Or.inr (Or.inl (B.product_of_equal_square H N a b ha hb form squares))
  by_cases fourth : a^4=b^4
  · exact Or.inl (B.pure_of_fourth H N a b ha hb form squares fourth)
  right;right
  by_cases eighth : a^8=b^8
  · have escape:=GlobalCloseCompletionComplementQ4ClassificationEighth.escape a b ha hb fourth eighth
    exact hard_of_eighth H F phi (B.square H N) (2*a*b) (a^2+b^2)
      (B.square_value H N a b form) escape.1 escape.2.1 escape.2.2
  · exact hard_of_eighth H F phi N a b form ha hb eighth

include phi in
/-- A zero leading block coefficient is repaired by a real series with the
original retained source. Only its nonzero endpoint is needed. -/
theorem classified (N Q : NativeAntiTargetSource.Output H 4) (a b p q r s : K)
    (form : N.network.denote=S.row a b 0 0) (nonzero : a≠0 ∨ b≠0)
    (seed : Q.network.denote=S.row p q r s) (hp : p≠0) : Outcome H F := by
  classical
  by_cases ha : a=0
  · have hb:=nonzero.resolve_left (not_not.mpr ha)
    rw [ha] at form
    exact nonzero_left H F phi (T.connect H N Q) (b*p) (b*q)
      (B.repaired H N Q b p q r s form seed) (mul_ne_zero hb hp)
  · exact nonzero_left H F phi N a b form ha


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationBlockSource
end
