import Holant.Proofs.Hardness.GeneralEODEQPairingSource
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget
import Holant.Proofs.Algorithms.FieldTransport

/-! A finite physical template family is interpreted in its existing target
field. The source's independently generated coefficient field is recovered
by the implemented rational-linear retraction; no codec equality is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOFiniteMacroSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution BinaryCompose
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue target_exact)
end O
namespace A
export Holant.LocalDrafts.MainChain.RawArityTransport (input computes signatures denote)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {d s t : ℕ} {a b : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (M : ℕ → Template) (valid : ∀k<t,(M k).WellFormed s 1 a)
variable (H : (i : Fin t) → Signature AlgebraicComplex (b i.val))
variable (arity_eq : ∀i : Fin t,b i.val=sourceArity M i.val)
variable (native : ∀i x y,F.decode (T.edge i x y)=Signature.disequality x y)
variable (exact : ∀i x,(F.decode (templateCoordinates F M valid T i x) : AlgebraicComplex)=
  H i (fun j => x (Fin.cast (arity_eq i) j)))
local instance : Algebra ℚ (O.originalField H) := (O.originalField H).algebra'

include exact in
theorem field_le : O.originalField H≤K := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  have h := exact i (fun j => x (Fin.cast (arity_eq i).symm j))
  simp only [Fin.cast_cast,Fin.cast_eq_self] at h
  change H i x∈K
  rw [←h]
  exact (F.decode (templateCoordinates F M valid T i _)).property

def embedding : O.originalField H→ₐ[ℚ]K :=
  IntermediateField.inclusion (field_le K F T M valid H arity_eq exact)

abbrev tables := sourceTables M T (templateCoordinates F M valid T)
abbrev value := (tables K F T M valid).evaluate F

include native exact in
theorem source_value (r : ExactSignatureTables.Input t 1 b) :
    value K F T M valid (A.input arity_eq r)=
      embedding K F T M valid H arity_eq exact (O.originalValue H r) := by
  apply Subtype.ext
  rw [value,ExactSignatureTables.evaluate_eq_decoded]
  change K.subtype _=(embedding K F T M valid H arity_eq exact (O.originalValue H r) : AlgebraicComplex)
  rw [←Network.denote_map K.subtype]
  change _=(O.originalValue H r : AlgebraicComplex)
  rw [O.target_exact]
  have hm : ((A.input arity_eq r).val.realize (A.input arity_eq r).property
      (fun i x => F.decode ((tables K F T M valid).vertex i x))
      (fun i x y => F.decode ((tables K F T M valid).edge i x y))).map K.subtype=
    (A.input arity_eq r).val.realize (A.input arity_eq r).property
      (A.signatures arity_eq H) (fun _ => Signature.disequality) := by
    unfold Network.map RawClosedNetwork.realize
    congr 1
    · funext v x
      exact exact ((A.input arity_eq r).val.signatureLabel (A.input arity_eq r).property v) x
    · funext e x y
      change (F.decode (T.edge _ x y) : AlgebraicComplex)=Signature.disequality x y
      rw [native]
      cases x <;> cases y <;> rfl
  rw [hm]
  exact A.denote arity_eq H (fun _ : Fin 1 => Signature.disequality) r

def answer := (embedding K F T M valid H arity_eq exact).toLinearMap.leftInverse

def answerComputes : Computes F.encoding (O.originalPresentation H).encoding
    (answer K F T M valid H arity_eq exact) :=
  Holant.LocalDrafts.MainChain.FieldCodec.retractComputes
    (O.originalPresentation H) F (embedding K F T M valid H arity_eq exact)

/-- The source uses its own field and codec, and the physical query uses the
unchanged target presentation. Every answer conversion is executed. -/
def retagSource : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 b) (O.originalPresentation H).encoding
    (RawClosedNetwork.validatedEncoding t 1 (sourceArity M)) F.encoding
    (O.originalValue H) (value K F T M valid) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
    (A.computes arity_eq) (answerComputes K F T M valid H arity_eq exact)
    ((tables K F T M valid).outputBound F) (O.originalValue H) (fun r => by
      change O.originalValue H r=answer K F T M valid H arity_eq exact
        (value K F T M valid (A.input arity_eq r))
      rw [source_value K F T M valid H arity_eq native exact]
      exact (Holant.LocalDrafts.MainChain.FieldCodec.retract_embedding
        (embedding K F T M valid H arity_eq exact) _).symm)

def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 b) (O.originalPresentation H).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    (O.originalValue H) (T.evaluate F) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (retagSource K F T M valid H arity_eq native exact)
    (Holant.LocalDrafts.MainChain.MacroTransport.controlled F M valid T)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOFiniteMacroSource
