import Holant.Platonic.StabilizerErasure.PauliPostselection
import Holant.Platonic.StabilizerErasure.TensorAuxiliary

/-! Two actual commuting Bell measurements on an added logical qubit and
the correctable physical port. Both normalized projections are proved to
be stabilizer isometries from the original all-zero Pauli expectations. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CharacterFlat
open Holant.ReedMuller.RadonAccess Holant.Platonic.StabilizerLine
open Holant.Platonic.StabilizerCode
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem pauli_run_add (P : Pauli n) (f g : Signature ℂ n) :
    P.run (f+g)=P.run f+P.run g := (pauliLinear P).map_add f g

theorem positivePostselect_zero_of_commuting
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (P Q : Pauli n)
    (hP : ∀f,P.run (P.run f)=f)
    (hPQ : ∀f,P.run (Q.run f)=Q.run (P.run f))
    (hQ : ∀f g,hermitian (U f) (Q.run (U g))=0)
    (hPQ0 : ∀f g,hermitian (U f) (P.run (Q.run (U g)))=0)
    (f g : Signature ℂ k) :
    hermitian (positivePostselect P U f) (Q.run (positivePostselect P U g))=0 := by
  change hermitian ((sqrtTwo : ℂ)⁻¹ • (U f+P.run (U f)))
    (Q.run ((sqrtTwo : ℂ)⁻¹ • (U g+P.run (U g))))=0
  rw [pauli_run_smul,pauli_run_add,hermitian_smul]
  simp only [hermitian_add_left,hermitian_add_right,
    involutive_pauli_selfAdjoint P hP,←hPQ,hP,hQ,hPQ0,add_zero,zero_add,mul_zero]

def bellZ (r : Fin (n+1)) : Pauli (n+2) := prependPauli 0 1 (physicalPauli r 3)
def bellX (r : Fin (n+1)) : Pauli (n+2) := prependPauli 1 0 (physicalPauli r 1)

theorem bellZ_involution (r : Fin (n+1)) (f : Signature ℂ (n+2)) :
    (bellZ r).run ((bellZ r).run f)=f := by
  rw [pauli_square]
  simp [bellZ,prependPauli,physicalPauli,tailLinear]

theorem bellX_involution (r : Fin (n+1)) (f : Signature ℂ (n+2)) :
    (bellX r).run ((bellX r).run f)=f := by
  rw [pauli_square]
  simp [bellX,prependPauli,physicalPauli,tailLinear]

theorem bellZX_commute (r : Fin (n+1)) (f : Signature ℂ (n+2)) :
    (bellZ r).run ((bellX r).run f)=(bellX r).run ((bellZ r).run f) := by
  apply (pauli_commute_iff _ _).mpr
  norm_num [pauliPairing,bellZ,bellX,prependPauli,physicalPauli,tailLinear,unitWord_apply]
  decide

theorem prepend_zero_expectation (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (P : Pauli n) (h : ∀f g,hermitian (U f) (P.run (U g))=0)
    (a d : ZMod 2) (f g : Signature ℂ (k+1)) :
    hermitian (prependMap U f) ((prependPauli a d P).run (prependMap U g))=0 := by
  rw [hermitian_columns (0 : Fin (n+1))]
  apply Finset.sum_eq_zero
  intro b _
  rw [column_prependMap,column_prependPauli,column_prependMap,hermitian_smul_right,h,mul_zero]

def bellProjected (V : StabilizerIsometry k (n+1)) (r : Fin (n+1)) :
    Signature ℂ (k+1) →ₗ[ℂ] Signature ℂ (n+2) :=
  positivePostselect (bellX r) (positivePostselect (bellZ r) (prependMap V.map))

theorem bellProjected_stabilizer (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (h : ∀p : Fin 4,p≠0 → ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=0) :
    IsStabilizerIsometry (bellProjected V r) := by
  have h0 (p : Fin 4) (hp : p≠0) (f g : Signature ℂ k) :
      hermitian (V.map f) ((physicalPauli r p).run (V.map g))=0 := by
    rw [physicalPauli_exact,V.adjoint_identity,h p hp]
    simp [hermitian]
  have hZX (f g : Signature ℂ k) :
      hermitian (V.map f) ((physicalPauli r 3).run ((physicalPauli r 1).run (V.map g)))=0 := by
    have he : pauliProduct (physicalPauli r 3) (physicalPauli r 1)=
        pauliShiftPhase 1 (physicalPauli r 2) := by
      norm_num [pauliProduct,physicalPauli,pauliShiftPhase]
      decide
    rw [←pauliProduct_run,he,pauliShiftPhase_run,hermitian_smul_right,h0 2 (by decide),mul_zero]
  have hZ := prepend_zero_expectation V.map (physicalPauli r 3) (h0 3 (by decide)) 0 1
  have hX := prepend_zero_expectation V.map (physicalPauli r 1) (h0 1 (by decide)) 1 0
  have hZX0 (f g : Signature ℂ (k+1)) :
      hermitian (prependMap V.map f) ((bellZ r).run ((bellX r).run (prependMap V.map g)))=0 := by
    rw [hermitian_columns (0 : Fin (n+2))]
    apply Finset.sum_eq_zero
    intro b _
    simp only [bellZ,bellX,column_prependMap,column_prependPauli,zero_mul,ReedMuller.CharacterFlat.sign_zero,
      one_smul,add_zero,Equiv.symm_apply_apply,one_mul]
    rw [hermitian_smul_right,hZX,mul_zero]
  have hU := prependMap_stabilizer V.map V.semantic
  have hU1 := positivePostselect_stabilizer _ hU (bellZ r) (bellZ_involution r) hZ
  exact positivePostselect_stabilizer _ hU1 (bellX r) (bellX_involution r)
    (positivePostselect_zero_of_commuting _ _ _ (bellZ_involution r) (bellZX_commute r) hX hZX0)

end
end Holant.Platonic.StabilizerErasure
