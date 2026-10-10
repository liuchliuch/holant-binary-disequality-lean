import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseFamily
import Holant.Proofs.Dichotomy.Closure.Macro.GlobalCloseCompletionMacroFamily
import Holant.Proofs.Hardness.GeneralEOUniversalSource

/-! Joint physical closure of a finite sparse native-M q4 family. Every actual
flip graph is serialized together and compiled through one original-G source.
The universal negative EO theorem eliminates the rejected joint criterion;
the positive criterion reconstructs one native identity A/P basis for every
original sparse row, including noncentral rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open StableCurrentEvenEOTransport StableCurrentEvenLocalOutcome
namespace M
export GlobalCloseCompletionMacroFamily (labels labels_exact template_denote family source)
end M
namespace S
export GlobalCloseCompletionSparseFamily (eoTable eoFamily originalFamily simultaneous_basis)
end S
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s t : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Fin t → Signature (OI.K G) 4) (core : Fin t → MinimumCore P.family)
variable (literal : ∀i,(core i).signature=⟨4,q i⟩)
variable (stable : ∀i,∀f∈rawDeck P.family torsion (q i),MatchingOrZero (actualTransfers P.family) f)
variable (d : ∀i,SparseOutput G P (q i) (core i) (literal i))

abbrev graph (i : Fin t) := Holant.Certificates.EqualityQuaternary.Flip.network (embedded G (q i)) (d i).mask

theorem uses (i : Fin t) : ∀v,∃j : Fin P.count,
    (⟨P.arity j.val,GlobalCloseCompletionMacroFamily.mapped G P j⟩ : AnySignature AlgebraicComplex)=
      ⟨(graph G P q core literal d i).shape.arity v,(graph G P q core literal d i).vertex v⟩ := by
  intro v
  rcases graph_uses G P (q i) (core i) (literal i) (d i).mask v with ⟨_,⟨j,rfl⟩,hj⟩
  exact ⟨j,hj⟩

abbrev labels (i : Fin t) := M.labels G P (graph G P q core literal d i) (uses G P q core literal d i)

/-- Boundary four is definitionally fixed even outside the finite dictionary;
only actual dictionary entries need a well-formed template. -/
abbrev templates (k : ℕ) : Template where
  boundary := 4
  vertices := if h : k<t then (labels G P q core literal d ⟨k,h⟩).template.vertices else []
  edges := if h : k<t then (labels G P q core literal d ⟨k,h⟩).template.edges else []

theorem templates_at (i : Fin t) : templates G P q core literal d i.val=
    (labels G P q core literal d i).template := by
  simp only [templates,dite_eq_left i.isLt]
  rfl

theorem valid : ∀k<t,(templates G P q core literal d k).WellFormed P.count 1 P.arity := by
  intro k hk
  rw [templates_at G P q core literal d ⟨k,hk⟩]
  exact (labels G P q core literal d ⟨k,hk⟩).wellFormed

abbrev table := M.family G P (templates G P q core literal d) (valid G P q core literal d)
abbrev family := EONegativePairReduction.family (table G P q core literal d)

private theorem template_any_congr (T U : Template) (h : T=U)
    (ht : T.WellFormed P.count 1 P.arity) (hu : U.WellFormed P.count 1 P.arity) :
    (⟨T.boundary,(T.network ht (GlobalCloseCompletionMacroFamily.mapped G P)
      (fun _ : Fin 1 => Signature.disequality)).denote⟩ : AnySignature AlgebraicComplex)=
    ⟨U.boundary,(U.network hu (GlobalCloseCompletionMacroFamily.mapped G P)
      (fun _ : Fin 1 => Signature.disequality)).denote⟩ := by
  cases h
  rfl

theorem table_exact (i : Fin t) : table G P q core literal d i=S.eoTable G P q core literal d i := by
  have ht := template_any_congr G P (templates G P q core literal d i.val)
    (labels G P q core literal d i).template (templates_at G P q core literal d i)
    (valid G P q core literal d i.val i.isLt) (labels G P q core literal d i).wellFormed
  have hg := (M.template_denote G P (graph G P q core literal d i) (uses G P q core literal d i)
    (Holant.Certificates.EqualityQuaternary.Flip.native (embedded G (q i)) (d i).mask)).trans
      ((Holant.Certificates.EqualityQuaternary.Flip.denote (embedded G (q i)) (d i).mask).trans
        (eoRow_exact G P (q i) (core i) (literal i) (d i)).symm)
  exact sigma_mk_injective (ht.trans (congrArg (fun f => (⟨4,f⟩ : AnySignature AlgebraicComplex)) hg))

theorem family_exact : family G P q core literal d=S.eoFamily G P q core literal d := by
  apply congrArg Set.range
  funext i
  exact congrArg (fun f => (⟨4,f⟩ : AnySignature AlgebraicComplex)) (table_exact G P q core literal d i)

theorem central (i : Fin t) : Signature.CentralSupport (table G P q core literal d i) := by
  rw [table_exact]
  intro x hx
  change 2*weight x≠4 at hx
  apply eoRow_support G P (q i) (core i) (literal i) (d i) x
  omega

theorem nonzero (i : Fin t) : table G P q core literal d i≠0 := by
  intro zero
  have hq : q i≠0 := ((congrArg Holant.LocalDrafts.FinitePGL2.Stabilization.Prime (literal i)).mp (core i).prime).1
  apply hq
  rw [table_exact] at zero
  change eoRow G P (q i) (core i) (literal i) (d i)=0 at zero
  rw [eoRow_exact] at zero
  funext x
  apply (ClosureSourceRows.embedding G).injective
  have h := congrFun zero (Holant.Marked.SupportAtlas.xorWord x (d i).mask)
  simpa only [Holant.Certificates.EqualityQuaternary.Flip.value,StableCurrentEvenEOTract.xorWord_involution,
    embedded,RingHomRealization.mapSignature,Pi.zero_apply,map_zero] using h

theorem preprocessed : Preprocessed (family G P q core literal d) := by
  rintro _ ⟨i,rfl⟩
  exact ⟨by change 0<4; decide,nonzero G P q core literal d i⟩

variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}
variable (negative : ¬EOTract (preprocess (family G P q core literal d)))

attribute [local irreducible] GeneralEOUniversalSource.source M.source

/-- All flips are substituted jointly into the exact original-G oracle. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction
    ea encodingNatBool (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  Programme.compose
    (GeneralEOUniversalSource.source (table G P q core literal d)
      (central G P q core literal d) negative w)
    (M.source G P (templates G P q core literal d) (valid G P q core literal d))

include negative in
theorem witnessCountingHard : OriginalHard G := by
  intro α ea f w
  exact ⟨(source G P q core literal d negative w).reduction⟩

include N stable core literal d in
/-- No singleton tractability or joint EO criterion is a caller premise. One
identity basis and ONE target class cover the whole original sparse family. -/
theorem simultaneous_basis_or_hard :
    (IsCommonKBasis affineClass (S.originalFamily G q) InvertibleKernel.identity ∨
      IsCommonKBasis productClass (S.originalFamily G q) InvertibleKernel.identity) ∨ OriginalHard G := by
  classical
  by_cases tract : EOTract (preprocess (family G P q core literal d))
  · rw [preprocess_eq_self (preprocessed G P q core literal d),family_exact] at tract
    exact Or.inl (S.simultaneous_basis G P torsion N q core literal stable d tract)
  · exact Or.inr (witnessCountingHard G P q core literal d tract)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseSource
end
