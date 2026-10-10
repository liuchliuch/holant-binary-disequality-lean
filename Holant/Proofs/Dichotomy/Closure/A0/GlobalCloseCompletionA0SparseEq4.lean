import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0CurrentSource
import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseFamily
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBPrimeEq4
import Holant.Proofs.Hardness.GeneralEOUniversalSource

/-! A sparse actual A0 q4 is consumed into either a real native scalar-Eq4
network or original-G counting hardness. Its one-q/I EO graph is compiled
through the same whole-current source, with no extra classifier assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0SparseEq4
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open FixedGadgetSubstitution Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace Q
export GlobalCloseCompletionA0Quaternary (normalized parity_and_complement)
end Q
namespace C
export GlobalCloseCompletionA0CurrentSource
  (count arity mapped source normalized_member identity_member identityLabel identity_literal SparseOutput)
end C
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
private theorem finite_preprocessed {r : ℕ} {b : ℕ → ℕ}
    (H : (i : Fin r) → Signature AlgebraicComplex (b i.val))
    (positive : ∀i : Fin r,0<b i.val) (nonzero : ∀i : Fin r,H i≠0) :
    Preprocessed (EONegativePairReduction.family H) := by
  rintro _ ⟨i,rfl⟩
  exact ⟨positive i,nonzero i⟩

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)
variable (d : C.SparseOutput G P torsion q core literal)

abbrev graph := Flip.network (Q.normalized G q) d.mask

theorem uses : ∀v,∃j : Fin (C.count G P torsion q core literal),
    (⟨C.arity G P torsion q core literal j.val,C.mapped G P torsion q core literal j⟩ :
      AnySignature AlgebraicComplex)=⟨(graph G P torsion q core literal d).shape.arity v,
        (graph G P torsion q core literal d).vertex v⟩ := by
  intro v
  by_cases ancestor : v=Flip.ancestor (Q.normalized G q) d.mask
  · rw [ancestor,(Flip.labels_exact (Q.normalized G q) d.mask).1]
    exact C.normalized_member G P torsion q core literal
  · rw [(Flip.labels_exact (Q.normalized G q) d.mask).2 v ancestor]
    exact C.identity_member G P torsion q core literal

def labels : Labelling (graph G P torsion q core literal d).shape
    (C.count G P torsion q core literal) 1 (C.arity G P torsion q core literal) where
  vertex v := (uses G P torsion q core literal d v).choose
  vertex_arity v := congrArg Sigma.fst (uses G P torsion q core literal d v).choose_spec
  edge _ := 0

abbrev templates (_k : ℕ) : Template where
  boundary := 4
  vertices := (labels G P torsion q core literal d).template.vertices
  edges := (labels G P torsion q core literal d).template.edges

theorem valid : ∀k<1,(templates G P torsion q core literal d k).WellFormed
    (C.count G P torsion q core literal) 1 (C.arity G P torsion q core literal) :=
  fun _ _ => (labels G P torsion q core literal d).wellFormed

abbrev table := GeneralEOPureFamilyAccess.family (C.mapped G P torsion q core literal)
  (templates G P torsion q core literal d) (valid G P torsion q core literal d)
abbrev family := EONegativePairReduction.family (table G P torsion q core literal d)

theorem table_exact (i : Fin 1) : table G P torsion q core literal d i=
    Flip.value (Q.normalized G q) d.mask := by
  exact (GeneralEOPinnedDescentAccess.template_denote (C.mapped G P torsion q core literal)
    (graph G P torsion q core literal d) (labels G P torsion q core literal d)
    (fun v => (uses G P torsion q core literal d v).choose_spec) (Flip.native _ _)).trans (Flip.denote _ _)

theorem central (i : Fin 1) : Signature.CentralSupport (table G P torsion q core literal d i) := by
  rw [table_exact]
  intro x hx
  change 2*weight x≠4 at hx
  exact d.eo x (by omega)

theorem nonzero (i : Fin 1) : table G P torsion q core literal d i≠0 := by
  rw [table_exact]
  exact d.prime.1

theorem preprocessed : Preprocessed (family G P torsion q core literal d) :=
  finite_preprocessed (table G P torsion q core literal d)
    (fun _ => by change 0<4; decide) (nonzero G P torsion q core literal d)

include N stable in
theorem complement_closed : ∀x,
    Flip.value (Q.normalized G q) d.mask (complementWord x)=0 ↔
      Flip.value (Q.normalized G q) d.mask x=0 := by
  have closed := (Q.parity_and_complement G P torsion N q core literal stable).choose_spec.2
  intro x
  change Q.normalized G q (xorWord (complementWord x) d.mask)=0 ↔ _
  rw [StableCurrentEvenEOTract.xorWord_complement]
  exact closed (xorWord x d.mask)

def macroSource := Programme.compose
  (GeneralEOPureFamilyAccess.source (C.mapped G P torsion q core literal)
    (templates G P torsion q core literal d) (valid G P torsion q core literal d))
  (C.source G P torsion N q core literal)

variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}
variable (negative : ¬EOTract (preprocess (family G P torsion q core literal d)))

attribute [local irreducible] GeneralEOUniversalSource.source macroSource

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    count (OriginalForestSource.value G) :=
  Programme.compose
    (GeneralEOUniversalSource.source (table G P torsion q core literal d)
      (central G P torsion q core literal d) negative w)
    (macroSource G P torsion N q core literal d)

include N negative in
theorem witnessCountingHard : StableCurrentEvenLocalOutcome.OriginalHard G := by
  intro α ea f w
  exact ⟨(source G P torsion N q core literal d negative w).reduction⟩

include N stable in
theorem class_of_tract (tract : EOTract (family G P torsion q core literal d)) :
    ∃C : EOClass,C.Holds (Flip.value (Q.normalized G q) d.mask) := by
  obtain ⟨_,_,sign,C,supports,pairings⟩ := tract
  have member : (⟨4,table G P torsion q core literal d (0 : Fin 1)⟩ : AnySignature AlgebraicComplex)∈
      family G P torsion q core literal d := ⟨0,rfl⟩
  have hs := supports _ member
  have hp := pairings _ member
  rw [table_exact] at hs hp
  exact ⟨C,GlobalCloseCompletionSparseFamily.class_of_supports _ d.eo
    (complement_closed G P torsion N q core literal stable d) sign C hs hp⟩

include N stable d in
theorem eq4_or_hard :
    Nonempty (GlobalCloseCompletionBPrimeEq4.Output (C.mapped G P torsion q core literal)) ∨
      StableCurrentEvenLocalOutcome.OriginalHard G := by
  classical
  by_cases tract : EOTract (preprocess (family G P torsion q core literal d))
  · left
    rw [preprocess_eq_self (preprocessed G P torsion q core literal d)] at tract
    obtain ⟨cls,hC⟩ := class_of_tract G P torsion N q core literal stable d tract
    apply GlobalCloseCompletionBPrimeEq4.class_output (C.mapped G P torsion q core literal)
      (C.identityLabel G P torsion q core literal) (C.identity_literal G P torsion q core literal)
      (graph G P torsion q core literal d) (labels G P torsion q core literal d)
      (fun v => (uses G P torsion q core literal d v).choose_spec) (Flip.native _ _) ?_ ?_ ?_ cls ?_
    · rw [Flip.denote]; exact d.eo
    · rw [Flip.denote]; exact d.prime
    · rw [Flip.denote]; exact complement_closed G P torsion N q core literal stable d
    · rw [Flip.denote]; exact hC
  · exact Or.inr (witnessCountingHard G P torsion N q core literal d tract)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0SparseEq4
end
