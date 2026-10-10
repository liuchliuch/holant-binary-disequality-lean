import Holant.Proofs.Reductions.EightVertexNonexception.Source
import Holant.Proofs.Algorithms.FieldTransport

/-! A faithful ambient algebra map induces a physical map between independently
presented generated coefficient fields. Original graph bytes stay unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SignatureFieldMap
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.LocalDrafts.MainChain
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (coefficient field presentation tables targetEncoding TargetInput targetValue target_value_exact)
end O
set_option backward.isDefEq.respectTransparency false
variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
variable (M : Signature K 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (φ : K→ₐ[ℚ]L)
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
def mapped : Signature L 4 := fun x=>φ (M x)
local instance mappedAlgebra : Algebra ℚ (O.field (mapped M φ)) := (O.field (mapped M φ)).algebra'
include halg in
theorem mapped_algebraic : ∀x,IsAlgebraic ℚ (mapped M φ x) := fun x=>(halg x).algHom φ

abbrev originalPresentation := O.presentation M halg
abbrev originalValue := O.targetValue M halg
abbrev mappedPresentation := O.presentation (mapped M φ) (mapped_algebraic M halg φ)
abbrev mappedValue := O.targetValue (mapped M φ) (mapped_algebraic M halg φ)

theorem coefficient_map (i : ExactSignatureTables.CoefficientIndex 1 1 (fun _=>4)) :
    φ (O.coefficient M i)=O.coefficient (mapped M φ) i := by
  cases i with
  | inl i => rfl
  | inr i =>
      rcases i with ⟨i,u,v⟩
      cases u <;> cases v <;> simp [O.coefficient,Signature.disequality]

theorem field_map_le : O.field M≤(O.field (mapped M φ)).comap φ := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i,rfl⟩
  change φ (O.coefficient M i)∈O.field (mapped M φ)
  rw [coefficient_map]
  exact coefficient_mem_familyField (O.coefficient (mapped M φ)) i

def embedding : O.field M→ₐ[ℚ]O.field (mapped M φ) where
  toFun x := ⟨φ x,field_map_le M φ x.property⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_one' := Subtype.ext (map_one φ)
  map_add' x y := Subtype.ext (map_add φ (x:K) (y:K))
  map_mul' x y := Subtype.ext (map_mul φ (x:K) (y:K))
  commutes' q := Subtype.ext (φ.commutes q)

theorem embedding_value (x : O.field M) : (embedding M φ x : L)=φ (x:K) := rfl

theorem value_exact (r : O.TargetInput) :
    embedding M φ (originalValue M halg r)=mappedValue M halg φ r := by
  apply Subtype.ext
  rw [embedding_value,O.target_value_exact,O.target_value_exact]
  change φ.toRingHom ((r.val.realize r.property (fun _ : Fin 1=>M)
    (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0)=_
  rw [←Network.denote_map φ.toRingHom]
  apply congrFun (Network.denote_congr (r.val.shape r.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x; rfl
  · intro e x y
    change φ (Signature.disequality x y)=Signature.disequality x y
    cases x <;> cases y <;> simp [Signature.disequality]

def answerComputes : Computes (originalPresentation M halg).encoding
    (mappedPresentation M halg φ).encoding (embedding M φ) :=
  FieldCodec.computes (originalPresentation M halg) (mappedPresentation M halg φ)
    (embedding M φ).toLinearMap

/-- Query ORIGINAL M and convert its answer using the actual fixed rational
matrix. Neither original and image fields nor their basis words are identified. -/
def controlled : LengthControlledOracleReduction O.targetEncoding
    (mappedPresentation M halg φ).encoding O.targetEncoding (originalPresentation M halg).encoding
    (mappedValue M halg φ) (originalValue M halg) := by
  have r := FieldTransport.toOriginal (originalPresentation M halg) (mappedPresentation M halg φ)
    (embedding M φ) O.targetEncoding (originalValue M halg)
    ((O.tables M halg).outputBound (originalPresentation M halg))
  have hv : (fun r=>embedding M φ (originalValue M halg r))=mappedValue M halg φ :=
    funext (value_exact M halg φ)
  rw [hv] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SignatureFieldMap
