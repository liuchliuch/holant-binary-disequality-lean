import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTargetCore
import Holant.Proofs.Algorithms.FieldTransport
import Holant.Complexity.FixedGadgetSubstitution.Adjoin

/-! A finite family of actual native-X templates is compiled to the unchanged
original family. The macro field is included and answers are retracted by the
proved rational-linear Boolean programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureFamilyAccess
open Computability Holant Holant.Tractable Holant.Complexity Holant.Algebraic
open FixedGadgetSubstitution ExactSignatureTables BinaryCompose
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue target_exact)
end O
namespace C
export Holant.LocalDrafts.MainChain.FieldCodec (retractComputes retract_embedding)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {t s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (T : ℕ → Template) (hv : ∀ k<t,(T k).WellFormed s 1 a)
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

abbrev arity := sourceArity T
abbrev presentation := O.originalPresentation G
abbrev coordinates := templateCoordinates (presentation G) T hv (O.originalTables G)
abbrev tables := sourceTables T (O.originalTables G) (coordinates G T hv)
abbrev liftedValue := (tables G T hv).evaluate (presentation G)

def family (i : Fin t) : Signature AlgebraicComplex (arity T i.val) :=
  ((T i.val).network (hv i.val i.isLt) G (fun _ : Fin 1 => Signature.disequality)).denote

abbrev macroField := O.originalField (family G T hv)
abbrev macroPresentation := O.originalPresentation (family G T hv)
abbrev macroValue := O.originalValue (family G T hv)
local instance macroAlgebra : Algebra ℚ (macroField G T hv) := (macroField G T hv).algebra'

/-- Every macro coefficient is the original-field evaluation of its actual graph. -/
theorem coordinates_ambient (i : Fin t) (x : Fin (arity T i.val) → Bool) :
    ((presentation G).decode (coordinates G T hv i x) : AlgebraicComplex)=family G T hv i x := by
  rw [decode_templateCoordinates]
  have hm := Network.denote_map (O.originalField G).subtype
    ((T i.val).network (hv i.val i.isLt)
      (fun j y => (presentation G).decode ((O.originalTables G).vertex j y))
      (fun j u v => (presentation G).decode ((O.originalTables G).edge j u v))) x
  refine hm.symm.trans ?_
  congr 1
  unfold Network.map Template.network
  congr 1
  · funext v y
    simp only [O.originalTables,LinearEquiv.apply_symm_apply]
    rfl
  · funext e u v
    simp only [O.originalTables,LinearEquiv.apply_symm_apply]
    cases u <;> cases v <;> rfl

theorem field_le : macroField G T hv ≤ O.originalField G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  change family G T hv i x ∈ O.originalField G
  rw [←coordinates_ambient G T hv i x]
  exact ((presentation G).decode (coordinates G T hv i x)).property

def embedding : macroField G T hv →ₐ[ℚ] O.originalField G :=
  IntermediateField.inclusion (field_le G T hv)

theorem embedding_value (x : macroField G T hv) :
    (embedding G T hv x : AlgebraicComplex)=x :=
  IntermediateField.coe_inclusion (field_le G T hv) x

theorem lifted_value_ambient (q : Input t 1 (arity T)) :
    (liftedValue G T hv q : AlgebraicComplex)=
      (q.val.realize q.property (family G T hv) (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 := by
  rw [liftedValue,ExactSignatureTables.evaluate_eq_decoded]
  change (O.originalField G).subtype _=_
  rw [←Network.denote_map (O.originalField G).subtype]
  apply congrArg (fun N : Network AlgebraicComplex 0 => N.denote Fin.elim0)
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact coordinates_ambient G T hv (q.val.signatureLabel q.property v) x
  · funext e u v
    simp only [tables,sourceTables,O.originalTables,LinearEquiv.apply_symm_apply]
    cases u <;> cases v <;> rfl

theorem lifted_value (q : Input t 1 (arity T)) :
    liftedValue G T hv q=embedding G T hv (macroValue G T hv q) := by
  apply Subtype.ext
  rw [lifted_value_ambient G T hv,embedding_value,O.target_exact]

def query := Compiler.value t 1 (arity T) T s a (compilerHypotheses T hv)
def queryComputes := Compiler.computes t 1 (arity T) T s a (compilerHypotheses T hv)
def answer := (embedding G T hv).toLinearMap.leftInverse

def answerComputes : Computes (presentation G).encoding (macroPresentation G T hv).encoding
    (answer G T hv) := C.retractComputes (macroPresentation G T hv) (presentation G) (embedding G T hv)

theorem query_value (q : Input t 1 (arity T)) :
    O.originalValue G (query T hv q)=embedding G T hv (macroValue G T hv q) := by
  have hp := replacement_scale_power T q.val q.property hv
    (fun i x => (presentation G).decode (coordinates G T hv i x))
    (fun j x => (presentation G).decode ((O.originalTables G).vertex j x))
    (fun j x y => (presentation G).decode ((O.originalTables G).edge j x y)) 0
    (1 : O.originalField G) (fun i => by
      simp only [ite_self,one_smul]
      funext x
      exact (decode_templateCoordinates (presentation G) T hv (O.originalTables G) i x).symm)
  have hq : O.originalValue G (query T hv q)=liftedValue G T hv q := by
    rw [O.originalValue, ExactSignatureTables.evaluate_eq_decoded,
      liftedValue, ExactSignatureTables.evaluate_eq_decoded]
    simpa only [one_pow,one_mul,tables,sourceTables] using hp
  exact hq.trans (lifted_value G T hv q)

/-- Source and target are the literal original-family codecs on both sides. -/
def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 (arity T)) (macroPresentation G T hv).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (presentation G).encoding
    (macroValue G T hv) (O.originalValue G) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (queryComputes T hv)
    (answerComputes G T hv) ((O.originalTables G).outputBound (presentation G))
    (macroValue G T hv) (fun q => by
      change macroValue G T hv q=answer G T hv (O.originalValue G (query T hv q))
      rw [query_value G T hv]
      exact (C.retract_embedding (embedding G T hv) _).symm)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureFamilyAccess
