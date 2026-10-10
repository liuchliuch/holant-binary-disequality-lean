import Holant.Platonic.StabilizerErasure.BellCoefficients
import Holant.Platonic.StabilizerErasure.BinaryRelabeling
import Holant.Platonic.StabilizerErasure.PureStabilizerResidual

/-! The mixed residual is a stabilizer isometry in the source's primary
definition. Bell postselection is followed by a genuine controlled-add /
Hadamard Clifford, then two actual fixed-zero factors are removed. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.FlatNetwork Holant.Platonic.StabilizerLine
open Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def bellDecoder (r : Fin (n+1)) : AnalyticClifford (n+2) :=
  composeClifford (axisProgram 0 1).clifford (relabelClifford (controlledAdd r))

theorem siteAction_zero_cons (R : Kernel ℂ) (f : Signature ℂ (n+1)) (b : Bool) (w : Word n) :
    siteAction 0 R f (Fin.cons b w)=∑d : Bool,R b d*f (Fin.cons d w) := by
  simp [siteAction]

theorem bellDecoder_projected (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (f : Signature ℂ (k+1)) (b c : Bool) (w : Word n) :
    (bellDecoder r).operator (bellProjected V r f) (Fin.cons b (r.insertNth c w))=
      if b=false ∧ c=false then mixedResidual V r f w else 0 := by
  change (axisProgram 0 1).run
    ((relabelClifford (controlledAdd r)).operator (bellProjected V r f))
      (Fin.cons b (r.insertNth c w))=_
  rw [axisProgram_exact]
  change siteAction 0 localH
    ((relabelClifford (controlledAdd r)).operator (bellProjected V r f))
      (Fin.cons b (r.insertNth c w))=_
  rw [siteAction_zero_cons]
  change (∑d : Bool,localH b d*
    bellProjected V r f (relabelWords (controlledAdd r) (Fin.cons d (r.insertNth c w))))=_
  simp_rw [controlledAdd_word,bellProjected_mixedResidual]
  cases b <;> cases c <;> simp [localH] <;> ring_nf <;>
    (try simp only [show ((Real.sqrt 2 : ℂ)⁻¹)^2=(1/2 : ℂ) from sqrtTwo_complex_inv_sq]) <;> ring

theorem bellDecoder_zero_factorization (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (f : Signature ℂ (k+1)) :
    (bellDecoder r).operator (bellProjected V r f)=
      attachZero (residualCoordinates 0)
        (attachZero (residualCoordinates r) (mixedResidual V r f)) := by
  ext x
  obtain ⟨b,y,rfl⟩ := Fin.exists_cons x
  obtain ⟨⟨c,w⟩,hy⟩ := (siteWords r).symm.surjective y
  change r.insertNth c w=y at hy
  subst y
  rw [bellDecoder_projected,attachZero_residualCoordinates]
  simp only [Fin.cons_zero,Fin.removeNth_zero,Fin.tail_cons]
  rw [attachZero_residualCoordinates]
  cases b <;> cases c <;> simp

/-- This is the source's actual stabilizer property for the constructed
mixed W, including the exact code image and all auxiliary/logical Paulis. -/
theorem mixedResidual_stabilizer (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (h : ∀p : Fin 4,p≠0 → ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=0) :
    IsStabilizerIsometry (mixedResidual V r) := by
  let U := (bellDecoder r).operator.toLinearMap.comp (bellProjected V r)
  have hU : IsStabilizerIsometry U :=
    semantic_postcompose _ (bellProjected_stabilizer V r h) (bellDecoder r)
  let W := (attachZero (residualCoordinates r)).comp (mixedResidual V r)
  have hW : IsStabilizerIsometry W :=
    remove_fixed_zero_stabilizer U hU (residualCoordinates 0) W
      (bellDecoder_zero_factorization V r)
  exact remove_fixed_zero_stabilizer W hW (residualCoordinates r) (mixedResidual V r) (fun _ => rfl)

end
end Holant.Platonic.StabilizerErasure
