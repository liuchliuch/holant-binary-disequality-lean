import Holant.Platonic.StabilizerErasure.SemanticIsometry
import Holant.Platonic.StabilizerErasure.AlignedForms

/-! The pure residual W is a source-level stabilizer isometry. Its exact
Pauli eigenspace and logical representatives follow by actual removal of
a fixed-zero tensor factor after a genuine one-qubit X reset. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.RadonAccess
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def residualCoordinates (r : Fin (n+1)) :
    BinaryVector (n+1) ≃ₗ[ZMod 2] BinaryVector n × BinaryVector 1 where
  toFun x := (r.removeNth x,![x r])
  invFun x := r.insertNth (x.2 0) x.1
  left_inv x := by simp
  right_inv x := by
    apply Prod.ext
    · simp
    · ext j;fin_cases j;simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · ext j;fin_cases j;rfl
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · ext j;fin_cases j;rfl

theorem attachZero_residualCoordinates (r : Fin (n+1)) (f : Signature ℂ n) (w : Word (n+1)) :
    attachZero (residualCoordinates r) f w=if w r=false then f (r.removeNth w) else 0 := by
  have hw : wordVector (r.removeNth (vectorWord w))=r.removeNth w := by
    ext j
    simp [wordVector,vectorWord,Fin.removeNth]
  cases hb : w r <;>
    simp [attachZero,residualCoordinates,vectorWord,boolEquiv,hb,funext_iff,Fin.forall_fin_succ,hw]

def resetBitProgram (r : Fin (n+1)) (b : Bool) : Program (n+1) :=
  if b then .translate (unitWord r) else .identity

theorem removeNth_update (r : Fin (n+1)) (w : Word (n+1)) (b : Bool) :
    r.removeNth (Function.update w r b)=r.removeNth w := by
  ext j
  simp [Fin.removeNth,Fin.succAbove_ne]

theorem pure_reset_factorization (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (b : Bool)
    (h : ∀f,siteAction r (qubitPauli 3) (V.map f)=(if b then (-1 : ℂ) else 1) • V.map f)
    (f : Signature ℂ k) :
    (V.postcompose (resetBitProgram r b).clifford).map f=
      attachZero (residualCoordinates r) (pureResidual V r b f) := by
  ext w
  rw [StabilizerIsometry.postcompose_map,Program.clifford_apply,attachZero_residualCoordinates]
  cases b
  · change V.map f w=_
    exact pure_column_expansion V r false h f w
  · change V.map f (wordVector (vectorWord w+unitWord r))=_
    rw [wordVector_add_unit,pure_column_expansion V r true h]
    simp [removeNth_update]

theorem pureResidual_stabilizer (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (b : Bool)
    (h : ∀f,siteAction r (qubitPauli 3) (V.map f)=(if b then (-1 : ℂ) else 1) • V.map f) :
    IsStabilizerIsometry (pureResidual V r b) :=
  remove_fixed_zero_stabilizer _ (V.postcompose (resetBitProgram r b).clifford).semantic
    (residualCoordinates r) (pureResidual V r b) (pure_reset_factorization V r b h)

end
end Holant.Platonic.StabilizerErasure
