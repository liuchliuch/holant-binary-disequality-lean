import Holant.Proofs.Closure.RetainedFinalAccess
import Holant.Proofs.Closure.ProgrammeRetained
import Holant.Certificates.EqualityQuaternary.Source
import Holant.Proofs.Algorithms.RingHomRealization

/-! Concrete original-field sources for row representatives. Every selected
matrix is an actual current-source binary, its original-field scalar is
recorded, and its retained label keeps the exact previously saved tree.
The C2 resources are constructed from literal I and the native-X group key;
no row classifier, SourceDeck, or changed-basis realization is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness
open RingHomRealization
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))

/-- The original input's literal embedding; no coefficient field is extracted
again after retention, normalization or a row change. -/
abbrev embedding : OI.K G →+* AlgebraicComplex :=
  (OriginalFrozenForest.OriginalInput.embedding G).toRingHom

abbrev ambientFamily (P : Palette G) : SignatureFamily AlgebraicComplex :=
  mapFamily (embedding G) P.family

def representative (j : completeGroup P.family torsion) : Kernel AlgebraicComplex :=
  (actualRepresentative P.family torsion j).map (embedding G)

theorem representative_actual (j : completeGroup P.family torsion) :
    Gadget.Realizes (ambientFamily G P) .disequality (kernelSignature (representative G P torsion j)) := by
  change Gadget.Realizes (mapFamily (embedding G) P.family) .disequality
    (RingHomRealization.mapSignature (embedding G)
      (Holant.Projective.BoundedTorsion.binarySignature (actualRepresentative P.family torsion j)))
  exact realizes_map (embedding G) (actualRepresentative_actual P.family torsion j).1

def representativeAccess (j : completeGroup P.family torsion) :
    CurrentSignatureAccess G P ⟨2,binarySignature (actualRepresentative P.family torsion j)⟩ :=
  currentSignatureAccess G P _ (actualRepresentative_actual P.family torsion j).1

variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩) (hm : 2 ≤ m)

abbrev retainedPalette : Palette G := ProgrammeRetained.palette G P torsion f core hcore hm

def representativeLabel (j : completeGroup P.family torsion) :
    Fin (retainedPalette G P torsion f core hcore hm).count :=
  RetainedCatalogue.deckLabel G P torsion f (.inl j)

def savedOccurrence (Q : Palette G) (i : Fin Q.count) : TreeOccurrence (OI.K G) :=
  ⟨⟨Q.arity i.val,Q.table i⟩,Q.trees i⟩

/-- Retention binds the whole original occurrence, not only its binary table. -/
theorem representative_saved (j : completeGroup P.family torsion) :
    savedOccurrence G (retainedPalette G P torsion f core hcore hm)
      (representativeLabel G P torsion f core hcore hm j) =
        fullDeckRoot P.family torsion f (.inl j) :=
  RetainedCatalogue.deck_saved G P torsion f (.inl j)

theorem representative_retained (j : completeGroup P.family torsion) :
    (⟨2,binarySignature (actualRepresentative P.family torsion j)⟩ : AnySignature (OI.K G)) ∈
      (retainedPalette G P torsion f core hcore hm).family := by
  rw [ProgrammeRetained.palette_family]
  exact fullRetainedDeck_representative P.family torsion f j

theorem representative_ambient_retained (j : completeGroup P.family torsion) :
    (⟨2,kernelSignature (representative G P torsion j)⟩ : AnySignature AlgebraicComplex) ∈
      ambientFamily G (retainedPalette G P torsion f core hcore hm) :=
  ⟨⟨2,binarySignature (actualRepresentative P.family torsion j)⟩,
    representative_retained G P torsion f core hcore hm j,rfl⟩

/-- Exact source-field provenance of an arbitrary actual current binary.
Its unit is not silently installed as a normalized gadget. The actual B has
its own separately charged original-G programme, and its proportional frozen
representative has a literal full-tree label in the constructed palette. -/
structure ActualBinaryResource (B : Binary (K:=OI.K G)) where
  key : completeGroup P.family torsion
  coefficient : OI.K G
  coefficient_nonzero : coefficient ≠ 0
  sourceEquation : B = coefficient • actualRepresentative P.family torsion key
  mappedEquation : B.map (embedding G) =
    (embedding G coefficient) • representative G P torsion key
  label : Fin (retainedPalette G P torsion f core hcore hm).count
  saved : savedOccurrence G (retainedPalette G P torsion f core hcore hm) label =
    fullDeckRoot P.family torsion f (.inl key)
  access : CurrentSignatureAccess G P ⟨2,binarySignature B⟩

def actualBinaryResource (B : Binary (K:=OI.K G)) (hB : ActualNonsingular P.family B) :
    ActualBinaryResource G P torsion f core hcore hm B := by
  let h := actual_binary_eq_representative P.family torsion B hB
  let j := Classical.choose h
  let hc := Classical.choose_spec h
  let c := Classical.choose hc
  have hn := (Classical.choose_spec hc).1
  have he := (Classical.choose_spec hc).2
  refine ⟨j,c,hn,he,?_,representativeLabel G P torsion f core hcore hm j,
    representative_saved G P torsion f core hcore hm j,currentSignatureAccess G P _ hB.1⟩
  rw [he]
  funext a b
  change embedding G (c * actualRepresentative P.family torsion j a b) =
    embedding G c * embedding G (actualRepresentative P.family torsion j a b)
  exact map_mul (embedding G) c (actualRepresentative P.family torsion j a b)

theorem resource_scalar_nonzero (B : Binary (K:=OI.K G))
    (R : ActualBinaryResource G P torsion f core hcore hm B) :
    embedding G R.coefficient ≠ 0 :=
  (map_ne_zero (embedding G)).mpr R.coefficient_nonzero

/-- The native-X group representative is retained exactly, with no unit
normalization, by the key-one convention already present in the frozen deck. -/
theorem native_retained :
    (⟨2,binarySignature (X : Binary (K:=OI.K G))⟩ : AnySignature (OI.K G)) ∈
      (retainedPalette G P torsion f core hcore hm).family := by
  simpa only [actualRepresentative_one] using
    representative_retained G P torsion f core hcore hm 1

theorem identity_ambient_retained :
    (⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) ∈
      ambientFamily G (retainedPalette G P torsion f core hcore hm) := by
  refine ⟨⟨2,binarySignature Signature.equality⟩,
    (retainedPalette G P torsion f core hcore hm).equality,?_⟩
  change (⟨2,fun x => embedding G (Signature.equality (x 0) (x 1))⟩ : AnySignature AlgebraicComplex) = _
  congr 1
  funext x
  simp [Signature.equality,kernelSignature]

theorem native_ambient_retained :
    (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈
      ambientFamily G (retainedPalette G P torsion f core hcore hm) := by
  refine ⟨⟨2,binarySignature (X : Binary (K:=OI.K G))⟩,
    native_retained G P torsion f core hcore hm,?_⟩
  change (⟨2,fun x => embedding G (Signature.disequality (x 0) (x 1))⟩ : AnySignature AlgebraicComplex) = _
  congr 1
  funext x
  simp [Signature.disequality,kernelSignature]

/-- Concrete C2 representatives are current retained I/native-X resources.
Constructing these resources does not assert the C2 deck or classify the
complete group as C2. Those remain distinct concrete routing obligations. -/
def c2Representatives : EqualityQuaternary.C2.Representatives
    (ambientFamily G (retainedPalette G P torsion f core hcore hm)) where
  matrix := EqualityQuaternary.C2.binary
  multiplier := fun _ => 1
  multiplier_ne_zero := fun _ => one_ne_zero
  actual := fun p => Gadget.realizes_of_mem _ .disequality _ (by
    cases p
    · exact identity_ambient_retained G P torsion f core hcore hm
    · exact native_ambient_retained G P torsion f core hcore hm)
  normal_form := fun p => by
    funext a b
    simp [Holant.Marked.scale]

theorem c2_retained : EqualityQuaternary.SourceRetained .c2
    (c2Representatives G P torsion f core hcore hm) := by
  intro p
  cases p
  · exact identity_ambient_retained G P torsion f core hcore hm
  · exact native_ambient_retained G P torsion f core hcore hm

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
