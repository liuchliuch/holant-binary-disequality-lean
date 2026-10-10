import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicLift
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZTrace

/-! The exact resource retained by every sourced unary branch. A conformal
unary chart sends literal Z to a nonsingular symmetric trace-zero row; the
isotropic source retains literal X. Membership survives every actual old-row
extension and is stronger than an unsupported independent-pair claim. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTraceOrX
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace U
export GeneralOddNonisotropicFrame (chart frame norm)
end U
namespace Z
export GlobalCloseCompletionUnaryIsotropicSource (z)
end Z
namespace T
export GlobalCloseCompletionSymmetricGHZTrace (binary)
end T
namespace D
export GlobalCloseCompletionUnaryDescentSource (ambient norm_map charted_exact frameBasis)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K]

def diagonal (u : Signature K 1) : K := u (fun _=>false)^2-u (fun _=>true)^2
def offDiagonal (u : Signature K 1) : K := -2*u (fun _=>false)*u (fun _=>true)

theorem chart_z (u : Signature K 1) : U.chart u Z.z=T.binary (diagonal u) (offDiagonal u) (offDiagonal u) := by
  funext x
  unfold U.chart Signature.coordinateAction
  rw [←(piFinTwoEquiv (fun _ : Fin 2=>Bool)).symm.sum_comp]
  cases h0 : x 0 <;>cases h1 : x 1 <;>
    simp [Fintype.sum_prod_type,Fin.prod_univ_two,piFinTwoEquiv,Fintype.sum_bool,
      U.frame,Z.z,T.binary,diagonal,offDiagonal,h0,h1] <;>ring

theorem determinant (u : Signature K 1) :
    -(diagonal u)^2-offDiagonal u*offDiagonal u= -(U.norm u)^2 := by
  unfold diagonal offDiagonal U.norm
  ring

theorem determinant_nonzero (u : Signature K 1) (hu : U.norm u≠0) :
    -(diagonal u)^2-offDiagonal u*offDiagonal u≠0 := by
  rw [determinant]
  exact neg_ne_zero.mpr (pow_ne_zero _ hu)

inductive Witness (F : SignatureFamily AlgebraicComplex) : Type where
  | trace (a b : AlgebraicComplex)
      (member : (⟨2,T.binary a b b⟩ : AnySignature AlgebraicComplex)∈F)
      (nonsingular : -a^2-b*b≠0)
  | x (member : (⟨2,xAnchor⟩ : AnySignature AlgebraicComplex)∈F)

def Witness.mono {F G : SignatureFamily AlgebraicComplex} (w : Witness F) (old : F⊆G) : Witness G := by
  cases w with
  | trace a b member det=>exact .trace a b (old member) det
  | x member=>exact .x (old member)

variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin r)→Signature L (b i.val)) (u : Signature L 1)
variable (normNonzero : U.norm u≠0)
variable (hasZ : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈D.ambient L H)

def chartWitness : Witness (D.ambient L (GlobalCloseCompletionUnaryChartSource.chartTable H u)) := by
  let v : Signature AlgebraicComplex 1:=fun x=>(u x : AlgebraicComplex)
  have hv : U.norm v≠0 := by
    intro zero
    apply normNonzero
    apply Subtype.ext
    exact (D.norm_map L u).trans zero
  have member : (⟨2,U.chart v Z.z⟩ : AnySignature AlgebraicComplex)∈
      D.ambient L (GlobalCloseCompletionUnaryChartSource.chartTable H u) := by
    change (⟨2,U.chart v Z.z⟩ : AnySignature AlgebraicComplex)∈
      GlobalCloseCompletionUnaryEndpointSource.chartedFamily L H u
    rw [D.charted_exact L H u normNonzero]
    exact ⟨⟨2,zAnchor⟩,hasZ,rfl⟩
  rw [chart_z] at member
  exact .trace (diagonal v) (offDiagonal v) member (determinant_nonzero v hv)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTraceOrX
end
