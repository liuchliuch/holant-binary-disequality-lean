import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBQuaternary
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBNativeCodec
import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseFamily
import Holant.Proofs.Hardness.GeneralEOUniversalSource

/-! Joint EO compilation of actual B-normalized sparse quaternaries. Every
one-q/I flip graph is substituted into the same normalized whole-current
source. Joint rejection is original-G counting hardness; acceptance gives
one literal Affine or Product class for all selected B-normalized rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBSparseSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open FixedGadgetSubstitution Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace Q
export GlobalCloseCompletionBQuaternary
  (normalized normalized_prime normalized_member identity_member parity_and_complement SparseOutput)
end Q
namespace S
export GlobalCloseCompletionBNativeCodec (mapped macroFamily macroSource)
end S
namespace B
export GlobalCloseCompletionBNativeSource (arity)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s t : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Fin t → Signature (OI.K G) 4) (core : Fin t → MinimumCore P.family)
variable (literal : ∀i,(core i).signature=⟨4,q i⟩)
variable (stable : ∀i,∀f∈rawDeck P.family torsion (q i),MatchingOrZero (actualTransfers P.family) f)
variable (d : ∀i,Q.SparseOutput G P (q i))

abbrev eoTable (i : Fin t) := Flip.value (Q.normalized G (q i)) (d i).mask
abbrev graph (i : Fin t) := Flip.network (Q.normalized G (q i)) (d i).mask

include core literal in
theorem uses (i : Fin t) : ∀v,∃j : Fin (P.count+1),
    (⟨B.arity G P j.val,S.mapped G P j⟩ : AnySignature AlgebraicComplex)=
      ⟨(graph G P q d i).shape.arity v,(graph G P q d i).vertex v⟩ := by
  intro v
  by_cases ancestor : v=Flip.ancestor (Q.normalized G (q i)) (d i).mask
  · rw [ancestor,(Flip.labels_exact (Q.normalized G (q i)) (d i).mask).1]
    exact Q.normalized_member G P (q i) (core i) (literal i)
  · rw [(Flip.labels_exact (Q.normalized G (q i)) (d i).mask).2 v ancestor]
    exact Q.identity_member G P

def labels (i : Fin t) : Labelling (graph G P q d i).shape (P.count+1) 1 (B.arity G P) where
  vertex v := (uses G P q core literal d i v).choose
  vertex_arity v := congrArg Sigma.fst (uses G P q core literal d i v).choose_spec
  edge _ := 0

abbrev templates (k : ℕ) : Template where
  boundary := 4
  vertices := if h : k<t then (labels G P q core literal d ⟨k,h⟩).template.vertices else []
  edges := if h : k<t then (labels G P q core literal d ⟨k,h⟩).template.edges else []

theorem templates_at (i : Fin t) : templates G P q core literal d i.val=
    (labels G P q core literal d i).template := by
  simp only [templates,dite_eq_left i.isLt]
  rfl

theorem valid : ∀k<t,(templates G P q core literal d k).WellFormed (P.count+1) 1 (B.arity G P) := by
  intro k hk
  rw [templates_at G P q core literal d ⟨k,hk⟩]
  exact (labels G P q core literal d ⟨k,hk⟩).wellFormed

abbrev table := S.macroFamily G P (templates G P q core literal d) (valid G P q core literal d)
abbrev family := EONegativePairReduction.family (table G P q core literal d)

private theorem template_any_congr (T U : Template) (h : T=U)
    (ht : T.WellFormed (P.count+1) 1 (B.arity G P)) (hu : U.WellFormed (P.count+1) 1 (B.arity G P)) :
    (⟨T.boundary,(T.network ht (S.mapped G P) (fun _ : Fin 1 => Signature.disequality)).denote⟩ :
      AnySignature AlgebraicComplex)=
    ⟨U.boundary,(U.network hu (S.mapped G P) (fun _ : Fin 1 => Signature.disequality)).denote⟩ := by
  cases h
  rfl

theorem table_exact (i : Fin t) : table G P q core literal d i=eoTable G P q d i := by
  have ht := template_any_congr G P (templates G P q core literal d i.val)
    (labels G P q core literal d i).template (templates_at G P q core literal d i)
    (valid G P q core literal d i.val i.isLt) (labels G P q core literal d i).wellFormed
  have hg := GeneralEOPinnedDescentAccess.template_denote (S.mapped G P) (graph G P q d i)
    (labels G P q core literal d i) (fun v => (uses G P q core literal d i v).choose_spec)
    (Flip.native (Q.normalized G (q i)) (d i).mask)
  exact sigma_mk_injective (ht.trans (congrArg
    (fun f => (⟨4,f⟩ : AnySignature AlgebraicComplex))
      (hg.trans (Flip.denote (Q.normalized G (q i)) (d i).mask))))

theorem central (i : Fin t) : Signature.CentralSupport (table G P q core literal d i) := by
  rw [table_exact]
  intro x hx
  change 2*weight x≠4 at hx
  exact (d i).eo x (by omega)

theorem nonzero (i : Fin t) : table G P q core literal d i≠0 := by
  rw [table_exact]
  exact (d i).prime.1

theorem preprocessed : Preprocessed (family G P q core literal d) := by
  rintro _ ⟨i,rfl⟩
  exact ⟨by change 0<4; decide,nonzero G P q core literal d i⟩

include N stable core literal in
theorem complement_closed (i : Fin t) : ∀x,
    eoTable G P q d i (complementWord x)=0 ↔ eoTable G P q d i x=0 := by
  have closed := (Q.parity_and_complement G P torsion N (q i) (core i) (literal i) (stable i)).choose_spec.2
  intro x
  change Q.normalized G (q i) (xorWord (complementWord x) (d i).mask)=0 ↔ _
  rw [StableCurrentEvenEOTract.xorWord_complement]
  exact closed (xorWord x (d i).mask)

variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}
variable (negative : ¬EOTract (preprocess (family G P q core literal d)))

attribute [local irreducible] GeneralEOUniversalSource.source S.macroSource

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    count (OriginalForestSource.value G) :=
  Programme.compose
    (GeneralEOUniversalSource.source (table G P q core literal d) (central G P q core literal d) negative w)
    (S.macroSource G P (templates G P q core literal d) (valid G P q core literal d))

include negative in
theorem witnessCountingHard : StableCurrentEvenLocalOutcome.OriginalHard G := by
  intro α ea f w
  exact ⟨(source G P q core literal d negative w).reduction⟩

include N stable in
theorem simultaneous_class (tract : EOTract (family G P q core literal d)) :
    ∃C : EOClass,∀i : Fin t,C.Holds (Q.normalized G (q i)) := by
  obtain ⟨_,_,sign,C,supports,pairings⟩ := tract
  refine ⟨C,fun i => ?_⟩
  have member : (⟨4,table G P q core literal d i⟩ : AnySignature AlgebraicComplex)∈
      family G P q core literal d := ⟨i,rfl⟩
  have hs := supports _ member
  have hp := pairings _ member
  rw [table_exact] at hs hp
  have hc := GlobalCloseCompletionSparseFamily.class_of_supports (eoTable G P q d i)
    (d i).eo (complement_closed G P torsion N q core literal stable d i) sign C hs hp
  exact StableCurrentEvenEOTract.class_unflip C _ (d i).mask hc

include N stable core literal d in
/-- One class covers every selected normalized q4. The other possibility is
actual original-G hardness, with all normalized and macro sources composed. -/
theorem simultaneous_class_or_hard :
    (∃C : EOClass,∀i : Fin t,C.Holds (Q.normalized G (q i))) ∨
      StableCurrentEvenLocalOutcome.OriginalHard G := by
  classical
  by_cases tract : EOTract (preprocess (family G P q core literal d))
  · left
    rw [preprocess_eq_self (preprocessed G P q core literal d)] at tract
    exact simultaneous_class G P torsion N q core literal stable d tract
  · exact Or.inr (witnessCountingHard G P q core literal d tract)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBSparseSource
end
