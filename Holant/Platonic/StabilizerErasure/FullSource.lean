import Holant.Platonic.StabilizerErasure.ErasureNormalForms
import Holant.Platonic.StabilizerErasure.PhysicalTensorFrames
import Holant.Platonic.StabilizerErasure.ComputationalState
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Source correspondence for all conclusions of Lemma 9.20
(`stabilizer-erasure-column-normal-form`, immutable manuscript).

Input representation and proved direction:
The input is an actual Clifford encoder with fixed zero ancillas and an
invertible binary splitting. The source explicitly states an equivalent
encoder convention. Concrete encoder => primary semantic stabilizer
isometry is proved here; the reverse conversion from an arbitrary linear
map satisfying `IsStabilizerIsometry` to an encoder presentation is NOT
proved. Accordingly the final theorem accepts the concrete encoder input
convention, not arbitrary semantic input evidence. Residual W maps use the
source's primary semantic definition, with both properties proved.

* The input is an actual Clifford encoder with fixed zero ancillas.
  `StabilizerIsometry.semantic` proves the source's primary code-image and
  logical-Pauli definition, including arbitrary binary encoder coordinates.
* `source_correctable_erasure_normal_forms` constructs a fixed one-port
  Clifford and exactly one of the pure/mixed forms. Both residual W maps
  satisfy `IsStabilizerIsometry`: genuine isometry, exact common eigenspace
  of commuting actual Paulis, and all physical logical representatives.
* The pure unary factor is a computational basis stabilizer ket in that
  local frame; `computationalState_stabilizer` constructs its actual
  zero-input Clifford encoder. The mixed formula retains the actual positive 1/√2 and an
  auxiliary input qubit. Its stabilizer proof uses actual Bell projections,
  a genuine binary controlled-add/Hadamard Clifford, and fixed-factor removal.
* With no correctable port, physical axis Cliffords and one genuine logical
  Clifford are constructed, the affine basis columns are derived, and their
  residual phase is reconstructed as an even-mixed `QuadraticPhase` using
  actual logical-Pauli derivatives and the proved third-difference criterion.
* The physical frame is literally the tensor coordinate action. `columnMatrix`
  is the source k-by-N matrix; its transpose gives the output word, its actual
  matrix rank is k, and every actual matrix column is nonzero.
* N=0 is covered: encoder dimensions force k=0 and yield the empty matrix
  and a nonzero constant phase. No positive-output hypothesis is added.

No alignment, residual-stabilizer, affine-column, rank, or phase conclusion
is supplied as a premise to the final theorem below.
-/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def columnMatrix (b : Fin n → BinaryVector k) : Matrix (Fin k) (Fin n) (ZMod 2) :=
  fun j r => b r j

theorem columnMatrix_transpose_mulVec (b : Fin n → BinaryVector k) (z : BinaryVector k) :
    (columnMatrix b).transpose.mulVec z=columnLinearMap b z := rfl

theorem columnMatrix_rank (b : Fin n → BinaryVector k) :
    (columnMatrix b).rank=Module.finrank (ZMod 2) (columnLinearMap b).range := by
  rw [←Matrix.rank_transpose (columnMatrix b)]
  change Module.finrank (ZMod 2) (columnMatrix b).transpose.mulVecLin.range=_
  have he : (columnMatrix b).transpose.mulVecLin=columnLinearMap b := by
    ext z r
    rfl
  rw [he]

def ColumnNormalForm (V : StabilizerIsometry k n) : Prop :=
  ∃p : Fin n → Fin 4,∃B : AnalyticClifford k,
    ∃c : BinaryVector n,∃M : Matrix (Fin k) (Fin n) (ZMod 2),
      ∃a₀ : ℂ,∃Q : QuadraticPhase k,
        a₀≠0 ∧ M.rank=k ∧ (∀r,M.col r≠0) ∧
        ∀z,Signature.coordinateAction (fun r => axisMatrix (p r))
          (V.map (B.operator.symm (ket (wordVector z))))=
            (a₀*(fourthRootPhase (Q.eval (wordVector z)) : ℂ)) •
              ket (wordVector (c+M.transpose.mulVec z))

theorem source_column_normal_form_tensor (V : StabilizerIsometry k n)
    (h : NoCorrectableErasure V) : ColumnNormalForm V := by
  obtain ⟨p,B,c,b,a₀,Q,hp,ha,hr,he⟩ := source_no_erasure_column_normal_form V h
  refine ⟨p,B,c,columnMatrix b,a₀,Q,ha,?_,fun r => (hp r).2,?_⟩
  · rw [columnMatrix_rank]
    exact hr
  · intro z
    rw [columnMatrix_transpose_mulVec,←physicalAxisClifford_tensor]
    exact he z

def ErasureAlternatives : {k n : ℕ} → StabilizerIsometry k n → Prop
  | _,0,_ => True
  | _,n+1,V => ∀r : Fin (n+1),Correctable V r →
      ∃C : AnalyticClifford (n+1),∃R : Kernel ℂ,
        (∀f,C.operator f=siteAction r R f) ∧
        (PureStabilizerForm (C.operator.toLinearMap.comp V.map) r ∨
          MixedStabilizerForm (C.operator.toLinearMap.comp V.map) r) ∧
        ¬(PureStabilizerForm (C.operator.toLinearMap.comp V.map) r ∧
          MixedStabilizerForm (C.operator.toLinearMap.comp V.map) r)

/-- Lemma 9.20 under the source's concrete Clifford-encoder input convention.
The direction from arbitrary semantic input to that presentation is not
part of this theorem. -/
theorem source_stabilizer_erasure_column_normal_form (V : StabilizerIsometry k n) :
    ErasureAlternatives V ∧ (NoCorrectableErasure V → ColumnNormalForm V) := by
  constructor
  · cases n with
    | zero => trivial
    | succ n => exact fun r h => source_correctable_erasure_normal_forms V r h
  · exact source_column_normal_form_tensor V

end
end Holant.Platonic.StabilizerErasure
