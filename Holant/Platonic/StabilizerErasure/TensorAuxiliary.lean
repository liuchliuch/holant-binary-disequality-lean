import Holant.Platonic.StabilizerErasure.SemanticClosure

/-! Tensor a logical/physical auxiliary qubit with a source-level stabilizer
isometry. The tensor action, exact Pauli factorization, code image, and all
logical representatives are proved, not postulated as closure properties. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.Platonic.StabilizerLine
open Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

@[simp] theorem column_zero_apply (b : Bool) (f : Signature ℂ (n+1)) (w : Word n) :
    column 0 b f w=f (Fin.cons b w) := by simp [column]

def prependMap (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    Signature ℂ (k+1) →ₗ[ℂ] Signature ℂ (n+1) where
  toFun f w := U (column 0 (w 0) f) (Fin.tail w)
  map_add' f g := by ext w;simp
  map_smul' c f := by ext w;simp

@[simp] theorem column_prependMap (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (b : Bool) (f : Signature ℂ (k+1)) :
    column 0 b (prependMap U f)=U (column 0 b f) := by
  ext w
  simp [column,prependMap,Fin.insertNth_zero]

theorem columns_ext {f g : Signature ℂ (n+1)}
    (h : ∀b : Bool,column 0 b f=column 0 b g) : f=g := by
  ext w
  have he := congrFun (h (w 0)) (Fin.tail w)
  simpa [column,Fin.insertNth_zero] using he

def assembleColumns (F : Bool → Signature ℂ k) : Signature ℂ (k+1) :=
  fun w => F (w 0) (Fin.tail w)

@[simp] theorem column_assembleColumns (F : Bool → Signature ℂ k) (b : Bool) :
    column 0 b (assembleColumns F)=F b := by
  ext w
  simp [column,assembleColumns,Fin.insertNth_zero]

def tailLinear : BinaryVector (n+1) →ₗ[ZMod 2] BinaryVector n where
  toFun := Fin.tail
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def insertZeroLinear : BinaryVector n →ₗ[ZMod 2] BinaryVector (n+1) where
  toFun x := Fin.cons 0 x
  map_add' x y := by ext j;cases j using Fin.cases <;> simp
  map_smul' c x := by ext j;cases j using Fin.cases <;> simp

def tailPauli (P : Pauli (n+1)) : Pauli n :=
  ⟨P.phase,Fin.tail P.shift,P.character.comp insertZeroLinear⟩

def prependPauli (a d : ZMod 2) (P : Pauli n) : Pauli (n+1) where
  phase := P.phase
  shift := Fin.cons a P.shift
  character := P.character.comp tailLinear+d • LinearMap.proj 0

theorem pauli_head_tail (P : Pauli (n+1)) :
    prependPauli (P.shift 0) (P.character (Fin.cons 1 0)) (tailPauli P)=P := by
  cases P with
  | mk phase shift character =>
    dsimp only [prependPauli,tailPauli]
    congr 1
    · exact Fin.cons_self_tail shift
    · apply LinearMap.ext
      intro x
      have hx : Fin.cons 0 (Fin.tail x)+x 0 • (Fin.cons 1 0 : BinaryVector (n+1))=x := by
        ext j;cases j using Fin.cases <;> simp [Fin.tail]
      change character (Fin.cons 0 (Fin.tail x))+character (Fin.cons 1 0)*x 0=character x
      conv_rhs => rw [←hx,map_add,map_smul]
      simp [mul_comm]

theorem column_prependPauli (a d : ZMod 2) (P : Pauli n) (b : Bool)
    (f : Signature ℂ (n+1)) :
    column 0 b ((prependPauli a d P).run f)=
      sign (d*boolEquiv b) • P.run (column 0 (boolEquiv.symm (boolEquiv b+a)) f) := by
  ext w
  have hx : wordVector (vectorWord (Fin.cons b w)+Fin.cons a P.shift)=
      Fin.cons (boolEquiv.symm (boolEquiv b+a)) (wordVector (vectorWord w+P.shift)) := by
    ext j;cases j using Fin.cases <;> simp [wordVector,vectorWord]
  simp only [column_zero_apply,Pauli.run,
    prependPauli,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.proj_apply,smul_eq_mul,Pi.smul_apply,hx]
  have ht : tailLinear (vectorWord (Fin.cons b w))=vectorWord w := by
    ext j;simp [tailLinear,Fin.tail,vectorWord]
  rw [ht]
  simp [vectorWord,sign_add]
  ring

theorem prependMap_intertwines (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (P : Pauli n) (Q : Pauli k) (h : ∀f,P.run (U f)=U (Q.run f))
    (a d : ZMod 2) (f : Signature ℂ (k+1)) :
    (prependPauli a d P).run (prependMap U f)=prependMap U ((prependPauli a d Q).run f) := by
  apply columns_ext
  intro b
  rw [column_prependPauli,column_prependMap,h,column_prependMap,column_prependPauli,map_smul]

theorem prependMap_range (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (f : Signature ℂ (n+1)) :
    f∈LinearMap.range (prependMap U) ↔ ∀b : Bool,column 0 b f∈LinearMap.range U := by
  constructor
  · rintro ⟨g,rfl⟩ b
    exact ⟨column 0 b g,(column_prependMap U b g).symm⟩
  · intro h
    choose g hg using h
    refine ⟨assembleColumns g,?_⟩
    apply columns_ext
    intro b
    simp [hg]

theorem prependMap_stabilizer (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hU : IsStabilizerIsometry U) : IsStabilizerIsometry (prependMap U) := by
  obtain ⟨hi,⟨t,P,hcomm,hcode⟩,hl⟩ := hU
  have hcolumn (P : Pauli n) (b : Bool) (f : Signature ℂ (n+1)) :
      column 0 b ((prependPauli 0 0 P).run f)=P.run (column 0 b f) := by
    simpa using column_prependPauli 0 0 P b f
  refine ⟨?_,⟨t,fun j => prependPauli 0 0 (P j),?_,?_⟩,?_⟩
  · intro f g
    rw [hermitian_columns (0 : Fin (n+1)),hermitian_columns (0 : Fin (k+1))]
    simp only [column_prependMap,hi]
  · intro i j f
    apply columns_ext
    intro b
    rw [hcolumn,hcolumn,hcolumn,hcolumn,hcomm]
  · intro f
    rw [prependMap_range]
    simp only [hcode]
    constructor
    · intro h j
      apply columns_ext
      intro b
      rw [hcolumn,h b j]
    · intro h b j
      have he := congrArg (column 0 b) (h j)
      simpa only [hcolumn] using he
  · intro Q
    obtain ⟨P,hP⟩ := hl (tailPauli Q)
    refine ⟨prependPauli (Q.shift 0) (Q.character (Fin.cons 1 0)) P,?_⟩
    intro f
    simpa only [pauli_head_tail] using prependMap_intertwines U P (tailPauli Q) hP
      (Q.shift 0) (Q.character (Fin.cons 1 0)) f

end
end Holant.Platonic.StabilizerErasure
