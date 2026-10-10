import Holant.Platonic.StabilizerErasure.ErasureDichotomy

/-! Analytic pure and maximally-mixed column factorizations.  The residual
maps below are explicit linear isometries.  Proving that the mixed residual
has a Clifford encoder still requires the source's tableau elimination and
is deliberately not included as a hypothesis or claimed conclusion. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
open scoped BigOperators ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem hermitian_smul (f g : Signature ℂ n) (a b : ℂ) :
    hermitian (a • f) (b • g)=conj a*b*hermitian f g := by
  simp only [hermitian,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem hermitian_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → Signature ℂ n) (g : κ → Signature ℂ n) :
    hermitian (∑i,f i) (∑j,g j)=∑i,∑j,hermitian (f i) (g j) := by
  simp only [hermitian,Finset.sum_apply,map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

def auxiliaryKet (b : Bool) : Signature ℂ k →ₗ[ℂ] Signature ℂ (k+1) where
  toFun f w := if w 0=b then f ((0 : Fin (k+1)).removeNth w) else 0
  map_add' f g := by ext w;dsimp;split_ifs <;> simp
  map_smul' c f := by ext w;dsimp;split_ifs <;> simp

@[simp] theorem column_auxiliaryKet (b c : Bool) (f : Signature ℂ k) :
    column 0 b (auxiliaryKet c f)=if b=c then f else 0 := by
  ext w
  simp [column,auxiliaryKet]
  split_ifs <;> rfl

def mixedResidual (V : StabilizerIsometry k (n+1)) (r : Fin (n+1)) :
    Signature ℂ (k+1) →ₗ[ℂ] Signature ℂ n :=
  ∑b : Bool,(sqrtTwo : ℂ) • ((column r b).comp (V.map.comp (column 0 b)))

theorem mixedResidual_apply (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (f : Signature ℂ (k+1)) :
    mixedResidual V r f=∑b : Bool,(sqrtTwo : ℂ) • column r b (V.map (column 0 b f)) := by
  simp [mixedResidual]

theorem mixedResidual_auxiliaryKet (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (b : Bool) (f : Signature ℂ k) :
    mixedResidual V r (auxiliaryKet b f)=(sqrtTwo : ℂ) • column r b (V.map f) := by
  rw [mixedResidual_apply]
  cases b <;> simp

/-- The displayed mixed expansion has the exact positive 1/√2 factor. -/
theorem mixed_column_expansion (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (f : Signature ℂ k) (b : Bool) (w : Word n) :
    V.map f (r.insertNth b w)=
      (sqrtTwo : ℂ)⁻¹*mixedResidual V r (auxiliaryKet b f) w := by
  rw [mixedResidual_auxiliaryKet]
  have hs : (sqrtTwo : ℂ)≠0 := by exact_mod_cast sqrtTwo_ne_zero
  simp [column,←mul_assoc,hs]

theorem mixed_matrixUnit_compression (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (h : ∀p : Fin 4,p≠0 → ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=0)
    (b c : Bool) (f : Signature ℂ k) :
    V.adjoint (siteAction r (matrixUnit b c) (V.map f))=
      (if b=c then (1/2 : ℂ) else 0) • f := by
  rw [siteAction_pauli_expansion]
  simp only [Fin.sum_univ_succ,map_add,map_smul]
  cases b <;> cases c <;> norm_num [pauliCoefficient,matrixUnit,
    h 1 (by decide),h 2 (by decide),h 3 (by decide),siteAction_qubitPauli_zero]

theorem mixed_column_gram (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (h : ∀p : Fin 4,p≠0 → ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=0)
    (b c : Bool) (f g : Signature ℂ k) :
    hermitian (column r b (V.map f)) (column r c (V.map g))=
      (if b=c then (1/2 : ℂ) else 0)*hermitian f g := by
  rw [←hermitian_matrixUnit,V.adjoint_identity,mixed_matrixUnit_compression V r h]
  simp [hermitian,Finset.mul_sum,mul_left_comm]

/-- The two normalized columns together form one genuine isometry on an
auxiliary qubit and the logical input, including their mutual orthogonality. -/
theorem mixedResidual_isometry (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (h : ∀p : Fin 4,p≠0 → ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=0)
    (f g : Signature ℂ (k+1)) :
    hermitian (mixedResidual V r f) (mixedResidual V r g)=hermitian f g := by
  rw [mixedResidual_apply,mixedResidual_apply,hermitian_sum]
  simp_rw [hermitian_smul,mixed_column_gram V r h]
  have hs : (sqrtTwo : ℂ)*(sqrtTwo : ℂ)=2 := by
    change (Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)=2
    norm_cast
    nlinarith [Real.sq_sqrt (show (0 : ℝ)≤2 by norm_num)]
  simp only [coe_sqrtTwo,Complex.conj_ofReal] at hs ⊢
  rw [hs]
  rw [hermitian_columns (0 : Fin (k+1)) f g]
  simp

def pureResidual (V : StabilizerIsometry k (n+1)) (r : Fin (n+1)) (b : Bool) :
    Signature ℂ k →ₗ[ℂ] Signature ℂ n := (column r b).comp V.map

theorem z_eigenstate_support (r : Fin (n+1)) (b : Bool) (f : Signature ℂ (n+1))
    (h : siteAction r (qubitPauli 3) f=(if b then (-1 : ℂ) else 1) • f)
    (w : Word (n+1)) (hw : w r≠b) : f w=0 := by
  have he := congrFun h w
  cases b <;> cases hb : w r <;> simp_all [siteAction,qubitPauli]
  all_goals rw [←hb,Function.update_eq_self] at he
  all_goals first | linear_combination he/2 | linear_combination -he/2

theorem pure_column_expansion (V : StabilizerIsometry k (n+1)) (r : Fin (n+1)) (b : Bool)
    (h : ∀f,siteAction r (qubitPauli 3) (V.map f)=(if b then (-1 : ℂ) else 1) • V.map f)
    (f : Signature ℂ k) (w : Word (n+1)) :
    V.map f w=if w r=b then pureResidual V r b f (r.removeNth w) else 0 := by
  by_cases hw : w r=b
  · simp [pureResidual,column,←hw]
  · simp [hw,z_eigenstate_support r b (V.map f) (h f) w hw]

theorem pureResidual_isometry (V : StabilizerIsometry k (n+1)) (r : Fin (n+1)) (b : Bool)
    (h : ∀f,siteAction r (qubitPauli 3) (V.map f)=(if b then (-1 : ℂ) else 1) • V.map f)
    (f g : Signature ℂ k) :
    hermitian (pureResidual V r b f) (pureResidual V r b g)=hermitian f g := by
  have ho (c : Bool) (hc : c≠b) (v : Signature ℂ k) : column r c (V.map v)=0 := by
    ext w
    exact z_eigenstate_support r b (V.map v) (h v) _ (by simpa)
  rw [←V.isometry f g,hermitian_columns r]
  change hermitian (column r b (V.map f)) (column r b (V.map g))=_
  cases b <;> simp [ho,hermitian]

end
end Holant.Platonic.StabilizerErasure
