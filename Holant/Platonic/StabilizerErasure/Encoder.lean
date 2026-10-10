import Holant.Platonic.StabilizerLine.StandardPauli

/-! Concrete Clifford encoders with fixed zero ancillas.  The only data in an
encoder are a binary coordinate splitting and an actual analytic Clifford;
isometry, its adjoint, and the Pauli compression formula are proved below. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.AffinePatching
open Holant.Platonic.StabilizerLine
open scoped BigOperators ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k a : ℕ}

/-- Logical coordinates followed by ancillas initialized in the zero ket. -/
def attachZero (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) :
    Signature ℂ k →ₗ[ℂ] Signature ℂ n where
  toFun f w := if (e (vectorWord w)).2=0 then f (wordVector (e (vectorWord w)).1) else 0
  map_add' f g := by ext w;dsimp;split_ifs <;> simp
  map_smul' c f := by ext w;dsimp;split_ifs <;> simp

/-- The adjoint of initialization evaluates the ancillas at zero. -/
def evaluateZero (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) :
    Signature ℂ n →ₗ[ℂ] Signature ℂ k where
  toFun f w := f (wordVector (e.symm (vectorWord w,0)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluateZero_attachZero
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) (f : Signature ℂ k) :
    evaluateZero e (attachZero e f)=f := by
  ext w
  simp [evaluateZero,attachZero]

theorem attachZero_adjoint
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a)
    (f : Signature ℂ k) (g : Signature ℂ n) :
    hermitian (attachZero e f) g=hermitian f (evaluateZero e g) := by
  rw [hermitian_block e]
  simp only [attachZero,LinearMap.coe_mk,AddHom.coe_mk,wordBlockEquiv,
    Equiv.coe_fn_symm_mk,vector_word,LinearEquiv.apply_symm_apply]
  have hz (w : Word a) : vectorWord w=0 ↔ w=origin a := by
    constructor
    · intro h;apply vector_injective;simpa using h
    · rintro rfl;exact vector_origin
  simp only [hz,word_vector]
  rw [Finset.sum_eq_single (origin a)]
  · simp [hermitian,evaluateZero]
  · intro b _ hb;simp [hb]
  · simp

theorem attachZero_isometry
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a)
    (f g : Signature ℂ k) :
    hermitian (attachZero e f) (attachZero e g)=hermitian f g := by
  rw [attachZero_adjoint,evaluateZero_attachZero]

/-- A genuine stabilizer encoding presentation, with no normal-form conclusion
stored as an assumption.  A binary splitting is an invertible computational
basis relabeling; the initialized state in its second factor is exactly |0…0⟩. -/
structure StabilizerIsometry (k n : ℕ) where
  ancillas : ℕ
  coordinates : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector ancillas
  clifford : AnalyticClifford n

def StabilizerIsometry.map (V : StabilizerIsometry k n) :
    Signature ℂ k →ₗ[ℂ] Signature ℂ n :=
  V.clifford.operator.toLinearMap.comp (attachZero V.coordinates)

def StabilizerIsometry.adjoint (V : StabilizerIsometry k n) :
    Signature ℂ n →ₗ[ℂ] Signature ℂ k :=
  (evaluateZero V.coordinates).comp V.clifford.operator.symm.toLinearMap

theorem StabilizerIsometry.adjoint_identity (V : StabilizerIsometry k n)
    (f : Signature ℂ k) (g : Signature ℂ n) :
    hermitian (V.map f) g=hermitian f (V.adjoint g) := by
  exact (V.clifford.adjoint_identity _ _).trans (attachZero_adjoint _ _ _)

@[simp] theorem StabilizerIsometry.adjoint_map (V : StabilizerIsometry k n)
    (f : Signature ℂ k) : V.adjoint (V.map f)=f := by
  simp [StabilizerIsometry.adjoint,StabilizerIsometry.map]

theorem StabilizerIsometry.isometry (V : StabilizerIsometry k n)
    (f g : Signature ℂ k) : hermitian (V.map f) (V.map g)=hermitian f g := by
  rw [V.adjoint_identity,V.adjoint_map]

theorem StabilizerIsometry.injective (V : StabilizerIsometry k n) : Function.Injective V.map := by
  intro f g h
  simpa using congrArg V.adjoint h

def logicalPauli (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a)
    (P : Pauli n) : Pauli k where
  phase := P.phase
  shift := (e P.shift).1
  character := StabilizerLine.firstCharacter e P.character

theorem evaluateZero_pauli_attachZero
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a)
    (P : Pauli n) (f : Signature ℂ k) :
    evaluateZero e (P.run (attachZero e f))=
      if (e P.shift).2=0 then (logicalPauli e P).run f else 0 := by
  ext w
  simp only [evaluateZero,LinearMap.coe_mk,AddHom.coe_mk,Pauli.run,attachZero,
    vector_word,map_add,LinearEquiv.apply_symm_apply,Prod.fst_add,Prod.snd_add,
    zero_add,logicalPauli,StabilizerLine.firstCharacter,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearMap.inl_apply]
  split_ifs <;> first | rfl | simp

/-- Compression through an actual Clifford encoder is exactly zero or a
logical Pauli in the literal fourth-root Pauli group. -/
theorem StabilizerIsometry.pauli_compression (V : StabilizerIsometry k n) (P : Pauli n) :
    (∀f,V.adjoint (P.run (V.map f))=0) ∨
      ∃Q : Pauli k,∀f,V.adjoint (P.run (V.map f))=Q.run f := by
  obtain ⟨Q,hQ⟩ := V.clifford.inverse_conjugates P
  by_cases h : (V.coordinates Q.shift).2=0
  · right
    refine ⟨logicalPauli V.coordinates Q,?_⟩
    intro f
    change evaluateZero V.coordinates
      (V.clifford.operator.symm (P.run (V.clifford.operator (attachZero V.coordinates f))))=_
    rw [hQ,evaluateZero_pauli_attachZero,if_pos h]
  · left
    intro f
    change evaluateZero V.coordinates
      (V.clifford.operator.symm (P.run (V.clifford.operator (attachZero V.coordinates f))))=_
    rw [hQ,evaluateZero_pauli_attachZero,if_neg h]

end
end Holant.Platonic.StabilizerErasure
