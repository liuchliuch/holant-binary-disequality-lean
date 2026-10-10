import Holant.Platonic.StabilizerErasure.NoErasureNormalForm
import Holant.BoundaryAction

/-! The physical frame in the column theorem is literally the tensor
product of the displayed one-qubit Clifford matrices, not merely an
arbitrary global Clifford that happens to align the selected Paulis. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
open Holant.Platonic.StabilizerCode
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def singleFrame (r : Fin (n+1)) (R : Kernel ℂ) : Fin (n+1) → Kernel ℂ :=
  fun j => if j=r then R else Signature.equality

@[simp] theorem siteWords_symm_apply (r : Fin (n+1)) (b : Bool) (w : Word n) :
    (siteWords r).symm (b,w)=r.insertNth b w := rfl

theorem coordinateAction_singleFrame (r : Fin (n+1)) (R : Kernel ℂ)
    (f : Signature ℂ (n+1)) :
    Signature.coordinateAction (singleFrame r R) f=siteAction r R f := by
  ext w
  unfold Signature.coordinateAction
  rw [←(siteWords r).symm.sum_comp,Fintype.sum_prod_type]
  simp only [siteWords_symm_apply]
  have hp (b : Bool) (y : Word n) :
      (∏j : Fin (n+1),singleFrame r R j (w j) ((r.insertNth b y : Word (n+1)) j))=
        R (w r) b*(∏i : Fin n,Signature.equality (w (r.succAbove i)) (y i)) := by
    rw [Fin.prod_univ_succAbove _ r]
    simp [singleFrame,Fin.succAbove_ne]
  simp_rw [hp]
  change (∑b : Bool,∑y : Word n,
    (R (w r) b*(∏i : Fin n,Signature.equality (r.removeNth w i) (y i)))*f (r.insertNth b y))=_
  simp [Signature.prod_equality,siteAction,mul_ite,ite_mul]

theorem axisFamily_coordinateAction (p : Fin (n+1) → Fin 4) (rs : List (Fin (n+1)))
    (hn : rs.Nodup) (f : Signature ℂ (n+1)) :
    (axisFamilyProgram p rs).run f=
      Signature.coordinateAction (fun r => if r∈rs then axisMatrix (p r) else Signature.equality) f := by
  induction rs with
  | nil => simp [axisFamilyProgram,Program.run]
  | cons s rs ih =>
    obtain ⟨hs,hn⟩ := List.nodup_cons.mp hn
    change (axisProgram s (p s)).run ((axisFamilyProgram p rs).run f)=_
    rw [axisProgram_exact,ih hn,←coordinateAction_singleFrame,Signature.coordinateAction_comp]
    congr 1
    funext j
    by_cases hj : j=s
    · subst j;simp [singleFrame,hs]
    · simp [singleFrame,hj,List.mem_cons]

theorem physicalAxisClifford_tensor {n : ℕ} (p : Fin n → Fin 4) (f : Signature ℂ n) :
    (physicalAxisClifford p).operator f=
      Signature.coordinateAction (fun r => axisMatrix (p r)) f := by
  cases n with
  | zero =>
    have he : (fun r : Fin 0 => axisMatrix (p r))=fun _ => Signature.equality :=
      funext (fun r => Fin.elim0 r)
    rw [he,Signature.coordinateAction_equality]
    rfl
  | succ n =>
    change (axisFamilyProgram p (List.finRange (n+1))).run f=_
    rw [axisFamily_coordinateAction p _ (List.nodup_finRange _)]
    simp

theorem each_axisMatrix_is_clifford (p : Fin 4) :
    ∃C : AnalyticClifford 1,∀f,C.operator f=siteAction 0 (axisMatrix p) f :=
  ⟨(axisProgram 0 p).clifford,axisProgram_exact 0 p⟩

end
end Holant.Platonic.StabilizerErasure
