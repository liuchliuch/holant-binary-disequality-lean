import Holant.Platonic.StabilizerErasure.NoCorrectableColumns

/-! Affine Pauli derivatives of the remaining column phase, proved directly
from exact physical logical representatives. This works for arbitrary
analytic Clifford alignments, without any Program/affine-preservation
assumption on the logical Clifford. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem framedMap_logical_representatives (V : StabilizerIsometry k n)
    (A : AnalyticClifford n) (B : AnalyticClifford k) (Q : Pauli k) :
    ∃P : Pauli n,∀f,P.run (framedMap V A B f)=framedMap V A B (Q.run f) := by
  obtain ⟨R,hR⟩ := B.pauli_inverse Q
  obtain ⟨P,hP⟩ := V.logical_representatives R
  obtain ⟨S,hS⟩ := A.pauli_forward P
  refine ⟨S,?_⟩
  intro f
  change S.run (A.operator (V.map (B.operator.symm f)))=
    A.operator (V.map (B.operator.symm (Q.run f)))
  rw [hR,←hP,hS]

def xPauli (u : BinaryVector k) : Pauli k := ⟨0,u,0⟩

theorem xPauli_ket (u z : BinaryVector k) :
    (xPauli u).run (ket (wordVector z))=ket (wordVector (z+u)) := by
  ext w
  have hh : wordVector (vectorWord w+u)=wordVector z ↔ w=wordVector (z+u) := by
    constructor
    · intro he
      apply vector_injective
      have he0 := congrArg vectorWord he
      simp only [vector_word] at he0 ⊢
      have hu := binary_self u
      linear_combination he0-hu
    · intro he
      subst w
      simp [add_assoc,binary_self]
  simp [Pauli.run,xPauli,ket,hh]

/-- All translation derivatives are literal fourth-root constants times
binary linear signs. The coefficient a itself is an arbitrary complex
function; this theorem derives, rather than assumes, its stabilizer phase
restriction from the actual encoder's logical Pauli representatives. -/
theorem framed_column_phase_derivatives (V : StabilizerIsometry k n)
    (A : AnalyticClifford n) (B : AnalyticClifford k)
    (c : BinaryVector n) (M : BinaryVector k →ₗ[ZMod 2] BinaryVector n)
    (a : BinaryVector k → ℂ) (ha : ∀z,a z≠0)
    (hcol : ∀z,framedMap V A B (ket (wordVector z))=a z • ket (wordVector (c+M z)))
    (u : BinaryVector k) :
    ∃q : ZMod 4,∃ell : BinaryVector k →ₗ[ZMod 2] ZMod 2,
      ∀z,a (z+u)=phaseRoot q*sign (ell z)*a z := by
  obtain ⟨P,hP⟩ := framedMap_logical_representatives V A B (xPauli u)
  refine ⟨P.phase+evenLift (P.character (c+M u)),P.character.comp M,?_⟩
  intro z
  have he := congrFun (hP (ket (wordVector z))) (wordVector (c+M (z+u)))
  rw [xPauli_ket,hcol z,hcol (z+u)] at he
  simp only [Pauli.run,vector_word,Pi.smul_apply,smul_eq_mul,ket,ite_true,mul_one] at he
  have hx : wordVector (c+M (z+u)+P.shift)=wordVector (c+M z) := by
    by_contra hx
    simp only [hx,ite_false,mul_zero] at he
    exact ha (z+u) he.symm
  rw [if_pos hx,mul_one] at he
  rw [←he,phaseRoot_add,phaseRoot_even]
  have hc : P.character (c+M (z+u))=P.character (c+M u)+(P.character.comp M) z := by
    simp only [map_add,LinearMap.comp_apply]
    abel
  rw [hc,sign_add]
  ring

end
end Holant.Platonic.StabilizerErasure
