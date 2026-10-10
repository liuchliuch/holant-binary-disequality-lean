import Holant.Proofs.Algorithms.CyclicBoundary.AlgebraicRepresentatives
import Holant.Proofs.Algorithms.CyclicBoundary.NonsquareExit
import Holant.Proofs.Algorithms.RingHomDescent
import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist
import Holant.OrderedTensor


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.DoubledDescent
open Holant.Tractable
open Holant.Projective.CyclicQuaternary
open RingHomRealization AlgebraicRepresentatives ActualCards NonsquareExit
open Holant.LocalDrafts.FinitePGL2.Stabilization
noncomputable section
set_option backward.isDefEq.respectTransparency false

def binary (r : AlgebraicComplex) : Signature AlgebraicComplex 2 :=
  Signature.coordinateAction (fun _ => Physical.P)
    (fun x => if x 0=x 1 then 0 else if x 0 then r else 1)

theorem binary_embedding (r : AlgebraicComplex) :
    mapSignature inclusion (binary r)=physical₂ (DihedralFactor.anti (r:ℂ)) := by
  have hp (a b : Bool) : inclusion (Physical.P a b) = ZeroEndpointDressing.hadamard a b := by
    cases a <;> cases b <;> simp [Physical.P, ZeroEndpointDressing.hadamard]
  have hb (y : Fin 2 → Bool) : inclusion (if y 0=y 1 then 0 else if y 0 then r else 1) =
      DihedralFactor.anti (r:ℂ) (y 0) (y 1) := by
    cases h0 : y 0 <;> cases h1 : y 1 <;> simp [h0,h1,DihedralFactor.anti] <;> rfl
  funext x
  simp only [mapSignature,binary,physical₂,PhysicalAttachments.binary,
    Signature.coordinateAction,map_sum,map_mul,map_prod,hp,hb]

def square (B : Signature AlgebraicComplex 2) : Signature AlgebraicComplex 4 :=
  Tensor.reindex (ZeroEndpointFactor.ports 0) (Tensor.tensor B B)

theorem square_embedding (B : Signature AlgebraicComplex 2) :
    mapSignature inclusion (square B)=doubled (mapSignature inclusion B) := by
  funext x
  simp [square,doubled,Tensor.reindex,Tensor.tensor,mapSignature]

theorem square_ordered (B : Signature AlgebraicComplex 2) : square B=Signature.tensor B B := by
  funext x
  simp only [square,Tensor.reindex,Tensor.tensor,Signature.tensor_apply]
  congr 1
  · congr 1
    funext j
    fin_cases j <;> rfl
  · congr 1
    funext j
    fin_cases j <;> rfl

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ}
variable (hN : 0 < N) (d : DoubledOutside (mapFamily inclusion F) N)

def ratio : AlgebraicComplex := (liftRoot hN ⟨d.ratio,d.ratio_root⟩).val

theorem ratio_value : (ratio hN d : ℂ)=d.ratio := rfl

theorem ratio_root : (ratio hN d)^N=1 := (liftRoot hN ⟨d.ratio,d.ratio_root⟩).property

theorem ratio_nonzero : ratio hN d ≠ 0 := by
  intro h
  have he := congrArg inclusion h
  apply d.ratio_nonzero
  change d.ratio = 0 at he
  exact he

def factor : Signature AlgebraicComplex 2 := binary (ratio hN d)

theorem factor_embedding : mapSignature inclusion (factor hN d)=
    physical₂ (DihedralFactor.anti d.ratio) := binary_embedding _

theorem factor_nonzero : factor hN d ≠ 0 := by
  intro hz
  apply d.binary_nonzero
  rw [←factor_embedding hN d,hz]
  funext x
  simp [mapSignature]

/-- Only the square is made actual over F. The scalar descent uses the
actual network and a nonzero entry, not an assumed field-membership proof. -/
theorem square_actual : Gadget.RealizesUpTo F .disequality (square (factor hN d)) := by
  apply RingHomDescent.realizesUpTo_descends inclusion
  rw [square_embedding,factor_embedding]
  exact d.doubled_actual

theorem ordered_square_actual :
    Gadget.RealizesUpTo F .disequality (Signature.tensor (factor hN d) (factor hN d)) := by
  rw [←square_ordered]
  exact square_actual hN d

/-- The actual retained parent can be the scaled square. Its complete
nonzero scalar is stored in ProperSplit; it is not normalized away. -/
theorem actual_parent_split : ∃ c : AlgebraicComplex, ∃ hc : c ≠ 0,
    Gadget.Realizes F .disequality (c • square (factor hN d)) ∧
      Nonempty (ProperSplit
        (⟨4,c • square (factor hN d)⟩ : AnySignature AlgebraicComplex)
        ⟨2,factor hN d⟩ ⟨2,factor hN d⟩) := by
  obtain ⟨c,hc,ha⟩ := square_actual hN d
  refine ⟨c,hc,ha,⟨{
    left_pos := by change 0 < 2; decide
    right_pos := by change 0 < 2; decide
    ports := ZeroEndpointFactor.ports 0
    scale := Units.mk0 c hc
    equation := ?_ }⟩⟩
  funext x
  rfl

theorem factor_outside : ¬ Holant.Projective.CyclicPhasePencil.IsPhase N
    (walshTransfer (mapSignature inclusion (factor hN d))) := by
  rw [factor_embedding]
  exact d.binary_outside

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.DoubledDescent
