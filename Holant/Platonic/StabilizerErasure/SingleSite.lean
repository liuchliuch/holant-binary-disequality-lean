import Holant.Platonic.StabilizerErasure.PauliCompression

/-! Literal single-port operators, their matrix-unit columns, and exact
Knill--Laflamme reduction to the four one-qubit matrix units. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Platonic.StabilizerLine
open Holant.Tractable.AffinePhase
open scoped BigOperators ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def siteWords (r : Fin (n+1)) : Word (n+1) ≃ Bool × Word n :=
  (Fin.insertNthEquiv (fun _ : Fin (n+1) => Bool) r).symm

def column (r : Fin (n+1)) (b : Bool) : Signature ℂ (n+1) →ₗ[ℂ] Signature ℂ n where
  toFun f x := f (r.insertNth b x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def siteAction (r : Fin (n+1)) (R : Bool → Bool → ℂ) :
    Signature ℂ (n+1) →ₗ[ℂ] Signature ℂ (n+1) where
  toFun f w := ∑b : Bool,R (w r) b*f (r.insertNth b (r.removeNth w))
  map_add' f g := by ext w;simp [mul_add,Finset.sum_add_distrib]
  map_smul' c f := by ext w;simp [mul_add,mul_left_comm]

def matrixUnit (c d : Bool) : Bool → Bool → ℂ := fun u v => if u=c ∧ v=d then 1 else 0

@[simp] theorem siteAction_matrixUnit (r : Fin (n+1)) (c d : Bool)
    (f : Signature ℂ (n+1)) (w : Word (n+1)) :
    siteAction r (matrixUnit c d) f w=
      if w r=c then f (r.insertNth d (r.removeNth w)) else 0 := by
  cases d <;> by_cases h : w r=c <;> simp [siteAction,matrixUnit,h]

theorem hermitian_columns (r : Fin (n+1)) (f g : Signature ℂ (n+1)) :
    hermitian f g=∑b : Bool,hermitian (column r b f) (column r b g) := by
  unfold hermitian
  rw [←(siteWords r).symm.sum_comp,Fintype.sum_prod_type]
  rfl

/-- The four matrix-unit expectations are precisely the four column Gram
forms, including the off-diagonal terms. -/
theorem hermitian_matrixUnit (r : Fin (n+1)) (c d : Bool)
    (f g : Signature ℂ (n+1)) :
    hermitian f (siteAction r (matrixUnit c d) g)=
      hermitian (column r c f) (column r d g) := by
  rw [hermitian_columns r]
  simp only [hermitian,column,LinearMap.coe_mk,AddHom.coe_mk,siteAction_matrixUnit,
    Fin.insertNth_apply_same,Fin.removeNth_insertNth]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb;simp [hb]
  · simp

theorem siteAction_expansion (r : Fin (n+1)) (R : Bool → Bool → ℂ)
    (f : Signature ℂ (n+1)) :
    siteAction r R f=∑c : Bool,∑d : Bool,R c d • siteAction r (matrixUnit c d) f := by
  ext w
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,siteAction_matrixUnit]
  rw [Finset.sum_eq_single (w r)]
  · simp [siteAction]
  · intro b _ hb
    have h : w r≠b := Ne.symm hb
    simp [h]
  · simp

/-- The source's all-one-qubit-operators erasure criterion, using the
proved adjoint of the actual encoding map. -/
def Correctable (V : StabilizerIsometry k (n+1)) (r : Fin (n+1)) : Prop :=
  ∀R : Bool → Bool → ℂ,IsScalar (fun f => V.adjoint (siteAction r R (V.map f)))

theorem correctable_iff_matrixUnits (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) : Correctable V r ↔
      ∀c d : Bool,IsScalar (fun f => V.adjoint (siteAction r (matrixUnit c d) (V.map f))) := by
  constructor
  · intro h c d;exact h (matrixUnit c d)
  · intro h R
    choose a ha using h
    refine ⟨∑c : Bool,∑d : Bool,R c d*a c d,?_⟩
    intro f
    change V.adjoint (siteAction r R (V.map f))=_
    rw [siteAction_expansion]
    simp only [map_sum,map_smul]
    simp_rw [ha,smul_smul]
    simp [add_smul]

theorem correctable_column_gram (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (h : Correctable V r) (c d : Bool) :
    ∃a : ℂ,∀f g,hermitian (column r c (V.map f)) (column r d (V.map g))=
      a*hermitian f g := by
  obtain ⟨a,ha⟩ := h (matrixUnit c d)
  refine ⟨a,?_⟩
  intro f g
  rw [←hermitian_matrixUnit,V.adjoint_identity]
  change hermitian f ((fun f => V.adjoint (siteAction r (matrixUnit c d) (V.map f))) g)=_
  rw [ha]
  simp [hermitian,Finset.mul_sum,mul_left_comm]

end
end Holant.Platonic.StabilizerErasure
