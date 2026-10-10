import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBPrimeEq4
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Adjoin
import Holant.Proofs.Hardness.GeneralEONonARSPinningFieldBridge

/-! A real scalar-Eq4 network over an arbitrary finite algebraic dictionary
adjoins literal Eq4 in the original dictionary's coefficient field. The
nonzero scalar is its actual all-zero network evaluation and is corrected
at every occurrence. All old dictionary labels remain unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBEqualityAdjoin
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace L
export GeneralEONonARSPinningFieldBridge (original lift labels exact native denote_lift)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K H) := OI.numberField H
variable (d : GlobalCloseCompletionBPrimeEq4.Output H)

abbrev K := O.originalField H
abbrev embedding : K H →ₐ[ℚ] AlgebraicComplex := (K H).val
abbrev F := OriginalLCodec.presentation (L:=K H)
abbrev network := L.lift H d.network d.labels
abbrev labels := L.labels H d.network d.labels
abbrev scalar : K H := (network H d).denote (fun _ => false)

theorem scalar_value : (scalar H d : AlgebraicComplex)=d.scalar := by
  rw [scalar,L.denote_lift H d.network d.labels d.exact d.native,d.denote]
  simp [Holant.EightVertex.ProductAnchor.equalityFour]

theorem scalar_nonzero : scalar H d≠0 := by
  intro zero
  apply d.nonzero
  exact (scalar_value H d).symm.trans (by rw [zero]; rfl)

theorem network_denote : (network H d).denote=scalar H d •
    Holant.EightVertex.ProductAnchor.equalityFour := by
  funext x
  apply Subtype.val_injective
  change (K H).subtype ((network H d).denote x)=_
  refine (L.denote_lift H d.network d.labels d.exact d.native x).trans ?_
  rw [d.denote]
  change d.scalar*Holant.EightVertex.ProductAnchor.equalityFour x=
    (K H).subtype (scalar H d*Holant.EightVertex.ProductAnchor.equalityFour x)
  have hc : (K H).subtype (scalar H d)=d.scalar := scalar_value H d
  rw [map_mul,hc]
  simp [Holant.EightVertex.ProductAnchor.equalityFour]

abbrev baseTables := OriginalLCodec.tables (L.original H)
abbrev template := (labels H d).template
abbrev arity := sourceArity (Adjoin.templates s a (template H d))
abbrev coordinates := ScaledAdjoin.coordinates (F H) (baseTables H)
  (template H d) (labels H d).wellFormed (scalar H d)
abbrev tables := sourceTables (Adjoin.templates s a (template H d)) (baseTables H) (coordinates H d)
def signatures (i : Fin (s+1)) : Signature (K H) (arity H d i.val) :=
  fun x => (F H).decode ((tables H d).vertex i x)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (arity H d)
abbrev value := (tables H d).evaluate (F H)

theorem base_signatures : (fun i x => (F H).decode ((baseTables H).vertex i x))=L.original H := by
  funext i x
  simp [baseTables,OriginalLCodec.tables,
    Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction.targetTables,
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables]

theorem base_edges : (fun j x y => (F H).decode ((baseTables H).edge j x y))=
    (fun _ : Fin 1 => Signature.disequality) := by
  funext j x y
  simp [baseTables,OriginalLCodec.tables,
    Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction.targetTables,
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables]

theorem macro_exact : ((template H d).network (labels H d).wellFormed
    (fun i x => (F H).decode ((baseTables H).vertex i x))
    (fun j x y => (F H).decode ((baseTables H).edge j x y))).denote=
      scalar H d • Holant.EightVertex.ProductAnchor.equalityFour := by
  rw [base_signatures,base_edges]
  exact (GeneralEOPinnedDescentAccess.template_denote (L.original H) (network H d) (labels H d)
    (L.exact H d.network d.labels) (L.native H d.network d.labels)).trans (network_denote H d)

private def decodeAny (f : AnySignature (Fin (Module.finrank ℚ (K H)) → ℚ)) :
    AnySignature (K H) := ⟨f.1,fun x => (F H).decode (f.2 x)⟩

def oldLabel (_H : (i : Fin s) → Signature AlgebraicComplex (a i.val)) (i : Fin s) : Fin (s+1) := ⟨i.val,by omega⟩
def eq4Label (_H : (i : Fin s) → Signature AlgebraicComplex (a i.val)) : Fin (s+1) := ⟨s,Nat.lt_succ_self _⟩

theorem old_signature (i : Fin s) :
    (⟨arity H d (oldLabel H i).val,signatures H d (oldLabel H i)⟩ : AnySignature (K H))=
      ⟨a i.val,L.original H i⟩ := by
  have h : (⟨arity H d (oldLabel H i).val,coordinates H d (oldLabel H i)⟩ :
      AnySignature (Fin (Module.finrank ℚ (K H)) → ℚ))=⟨a i.val,(baseTables H).vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (template H d) i)
      (ScaledAdjoin.old_coordinates (F H) (baseTables H) (template H d)
        (labels H d).wellFormed (scalar H d) i)
  exact (congrArg (decodeAny H) h).trans (congrArg (fun f => (⟨a i.val,f⟩ : AnySignature (K H)))
    (congrFun (base_signatures H) i))

theorem eq4_signature :
    (⟨arity H d (eq4Label H).val,signatures H d (eq4Label H)⟩ : AnySignature (K H))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  have h : (⟨arity H d (eq4Label H).val,coordinates H d (eq4Label H)⟩ :
      AnySignature (Fin (Module.finrank ℚ (K H)) → ℚ))=
      ⟨4,fun x => (F H).decode.symm
        (((template H d).network (labels H d).wellFormed
          (fun i x => (F H).decode ((baseTables H).vertex i x))
          (fun j x y => (F H).decode ((baseTables H).edge j x y))).denote x/scalar H d)⟩ :=
    Sigma.ext (Adjoin.new_boundary (template H d))
      (ScaledAdjoin.new_coordinates (F H) (baseTables H) (template H d)
        (labels H d).wellFormed (scalar H d))
  refine (congrArg (decodeAny H) h).trans ?_
  unfold decodeAny
  congr 1
  funext x
  change (F H).decode ((F H).decode.symm _)=_
  rw [LinearEquiv.apply_symm_apply,macro_exact]
  exact mul_div_cancel_left₀ _ (scalar_nonzero H d)

theorem original_tables : OriginalLCodec.tables (signatures H d)=tables H d := by
  unfold OriginalLCodec.tables
    Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction.targetTables
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables
  congr 1
  · funext i x
    exact (F H).decode.symm_apply_apply _

theorem mapped_original : OriginalLCodec.mapped (embedding H) (L.original H)=H := rfl

def toOriginal : LengthControlledOracleReduction
    (inputEncoding H d) (F H).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation H).encoding
    (OriginalLCodec.value (signatures H d)) (O.originalValue H) := by
  have source := Programme.compose
    (Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin (F H) (baseTables H)
      (template H d) (labels H d).wellFormed (scalar H d) (scalar_nonzero H d))
    (OriginalLCodec.toCoefficient (embedding H) (L.original H))
  unfold OriginalLCodec.coefficientPresentation at source
  rw [mapped_original] at source
  simpa only [OriginalLCodec.value,original_tables] using source


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBEqualityAdjoin
end
