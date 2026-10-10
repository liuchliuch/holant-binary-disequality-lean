import Holant.Platonic.StabilizerErasure.PhysicalPauli
import Holant.Kernel

/-! Genuine one-port Clifford rotations aligning each nonidentity Hermitian
Pauli with Z. The operators are constructed from the checked gate program,
and their action is literally one two-by-two matrix at the selected port. -/
namespace Holant.Platonic.StabilizerCode
noncomputable section
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.RadonAccess
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerErasure
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 def siteCoordinates (r : Fin (n+1)) :
    BinaryVector (n+1) ≃ₗ[ZMod 2] BinaryVector 1×BinaryVector n where
  toFun x:=(![x r],r.removeNth x)
  invFun p:=r.insertNth (p.1 0) p.2
  left_inv x:=by simp
  right_inv p:=by
    apply Prod.ext
    · ext i;fin_cases i;simp
    · simp
  map_add' x y:=by
    apply Prod.ext
    · ext i;fin_cases i;rfl
    · rfl
  map_smul' c x:=by
    apply Prod.ext
    · ext i;fin_cases i;rfl
    · rfl

 theorem site_blockWord (r : Fin (n+1)) (t : Fin 1→Bool) (w : Fin (n+1)→Bool) :
    blockWord (siteCoordinates r) t w=r.insertNth (t 0) (r.removeNth w) := by
  apply vector_injective
  apply (siteCoordinates r).injective
  rw [blockWord_coordinates]
  apply Prod.ext
  · ext i
    fin_cases i
    simp [siteCoordinates,vectorWord]
  · ext i
    simp [siteCoordinates,vectorWord,Fin.removeNth]

 def oneWordEquiv : (Fin 1→Bool) ≃ Bool where
  toFun w:=w 0
  invFun b:=![b]
  left_inv w:=by ext i;fin_cases i;rfl
  right_inv b:=rfl

 def localH (a b : Bool) : ℂ := ((sqrtTwo⁻¹:AlgebraicComplex):ℂ)*if a && b then -1 else 1
 def localSinv (a b : Bool) : ℂ := if a=b then (if a then -Complex.I else 1) else 0

 theorem site_hadamard (r : Fin (n+1)) (f : Signature ℂ (n+1)) :
    (Program.hadamard 1 n (siteCoordinates r)).run f=siteAction r localH f := by
  funext w
  simp only [Program.run,blockWalsh,pow_one]
  rw [←oneWordEquiv.symm.sum_comp]
  simp only [site_blockWord]
  simp [siteCoordinates,oneWordEquiv,siteAction,localH,walshKernel,
    vectorWord,wordVector,boolEquiv,Fin.prod_univ_succ,Finset.mul_sum]
  cases hw : w r <;> simp [hw,hadamard] <;> ring

 def siteQuadratic (r : Fin (n+1)) : QuadraticPhase (n+1) where
  constant:=0
  linear j:=if j=r then 1 else 0
  mixed _ _:=0
  even_mixed _ _ _:=Or.inl rfl

 theorem siteQuadratic_eval (r : Fin (n+1)) (w : Fin (n+1)→Bool) :
    (siteQuadratic r).eval w=bitValue (ZMod 4) (w r) := by
  simp [siteQuadratic,QuadraticPhase.eval]

 theorem site_inverse_phase (r : Fin (n+1)) (f : Signature ℂ (n+1)) :
    (Program.phase (siteQuadratic r) true).run f=siteAction r localSinv f := by
  funext w
  simp only [Program.run,phaseAction,phaseExponent,ite_true,siteQuadratic_eval]
  cases hw : w r <;> simp [bitValue,siteAction,localSinv,hw,fourthRootPhase]
  all_goals norm_num [show (-1 : ZMod 4).val=3 by decide,pow_succ,Complex.I_mul_I]

 theorem siteAction_mul (r : Fin (n+1)) (A B : Kernel ℂ) (f : Signature ℂ (n+1)) :
    siteAction r A (siteAction r B f)=siteAction r (Kernel.mul A B) f := by
  ext w
  simp [siteAction,Kernel.mul_apply,mul_add,add_mul]
  ring

 def axisProgram (r : Fin (n+1)) : Fin 4→Program (n+1)
  | 0=>.identity
  | 1=>.hadamard 1 n (siteCoordinates r)
  | 2=>.comp (.hadamard 1 n (siteCoordinates r)) (.phase (siteQuadratic r) true)
  | 3=>.identity

 def axisMatrix : Fin 4→Kernel ℂ
  | 0=>qubitPauli 0
  | 1=>localH
  | 2=>Kernel.mul localH localSinv
  | 3=>qubitPauli 0

 theorem axisProgram_exact (r : Fin (n+1)) (p : Fin 4) (f : Signature ℂ (n+1)) :
    (axisProgram r p).run f=siteAction r (axisMatrix p) f := by
  fin_cases p
  · exact (siteAction_qubitPauli_zero r f).symm
  · exact site_hadamard r f
  · change (Program.hadamard 1 n (siteCoordinates r)).run
      ((Program.phase (siteQuadratic r) true).run f)=_
    rw [site_hadamard,site_inverse_phase,siteAction_mul]
    rfl
  · exact (siteAction_qubitPauli_zero r f).symm

 theorem axisMatrix_intertwines (p : Fin 4) (hp : p≠0) :
    Kernel.mul (axisMatrix p) (qubitPauli p)=Kernel.mul (qubitPauli 3) (axisMatrix p) := by
  funext a b
  fin_cases p <;> cases a <;> cases b
  all_goals try contradiction
  all_goals simp [axisMatrix,Kernel.mul_apply,localH,localSinv,qubitPauli]
  all_goals ring_nf <;> simp [Complex.I_sq] <;> ring

 theorem exists_local_axis_clifford (r : Fin (n+1)) (p : Fin 4) (hp : p≠0) :
    ∃C : AnalyticClifford (n+1),∃R : Kernel ℂ,
      (∀f,C.operator f=siteAction r R f) ∧
      ∀f,C.operator (siteAction r (qubitPauli p) f)=
        siteAction r (qubitPauli 3) (C.operator f) := by
  refine ⟨(axisProgram r p).clifford,axisMatrix p,axisProgram_exact r p,?_⟩
  intro f
  simp only [Program.clifford_apply,axisProgram_exact,siteAction_mul]
  rw [axisMatrix_intertwines p hp]

end
end Holant.Platonic.StabilizerCode
