import Holant.Proofs.Dichotomy.Closure.Binary.GlobalCloseCompletionBinaryEOCore
import Holant.Proofs.Dichotomy.Closure.Mixed.GlobalCloseCompletionMixedEOModel
import Holant.Proofs.Dichotomy.Retained.StableCurrentBinaryClosure
import Holant.Proofs.Closure.ClosureSourceRows

/-! Native-M retained binary rows enter the joint EO family by actual palette
B/I networks. The original-field embedding and selected common class are exact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBinaryEO
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export GlobalCloseCompletionBinaryEOCore
  (graph output graph_denote graph_native graph_uses output_central output_nonzero class_of_pairings class_reconstruct)
end C
namespace M
export GlobalCloseCompletionMacroFamily (mapped labels labels_exact)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (f : Signature (OI.K G) 2)
variable (retained : (⟨2,f⟩ : AnySignature (OI.K G))∈P.family)
variable (prime : Prime (⟨2,f⟩ : AnySignature (OI.K G)))

abbrev embedded := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f
abbrev matrix := Matrix.map (binaryMatrix f) (ClosureSourceRows.embedding G)

theorem matrix_signature : Holant.Complexity.BinaryInterpolation.Chains.binarySignature (matrix G f)=embedded G f := by
  funext x
  change ClosureSourceRows.embedding G (f ![x 0,x 1])=ClosureSourceRows.embedding G (f x)
  apply congrArg (ClosureSourceRows.embedding G)
  apply congrArg f
  funext j
  fin_cases j <;> rfl

include N retained prime in
theorem monomial : IsMonomial (matrix G f) :=
  ClosureMarkedDihedral.Source.actual_binary_monomial (ClosureSourceRows.embedding G)
    P.family torsion N (binaryMatrix f) (retained_binary_prime_actual P.family f retained prime)

abbrev mappedFamily : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin P.count => (⟨P.arity i.val,M.mapped G P i⟩ : AnySignature AlgebraicComplex))

include retained in
theorem embedded_mem : (⟨2,embedded G f⟩ : AnySignature AlgebraicComplex)∈mappedFamily G P := by
  obtain ⟨j,hj⟩ := retained
  refine ⟨j,?_⟩
  exact congrArg (RingHomRealization.mapAny (ClosureSourceRows.embedding G)) hj

theorem equality_mem :
    (⟨2,Holant.Complexity.BinaryInterpolation.Chains.binarySignature
      (Signature.equality : Binary (K:=AlgebraicComplex))⟩ : AnySignature AlgebraicComplex)∈mappedFamily G P := by
  obtain ⟨j,hj⟩ := P.equality
  refine ⟨j,?_⟩
  have hm := congrArg (RingHomRealization.mapAny (ClosureSourceRows.embedding G)) hj
  apply hm.trans
  unfold RingHomRealization.mapAny
  congr 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [RingHomRealization.mapSignature,binarySignature,
      Holant.Complexity.BinaryInterpolation.Chains.binarySignature,Signature.equality,h0,h1]

/-- Every retained prime binary supplies its own graph, with labels from the
actual current palette, for the ONE finite mixed-family EO criterion. -/
def model : GlobalCloseCompletionMixedEOModel.Model G P ⟨2,embedded G f⟩ := by
  let hm := monomial G P torsion N f retained prime
  let p := hm.choose
  let w := hm.choose_spec.choose
  have hw : (∀b,w b≠0) ∧ matrix G f=Holant.Marked.monomial p w := hm.choose_spec.choose_spec
  let graph := C.graph (matrix G f) p
  have uses : ∀v,∃j : Fin P.count,
      (⟨P.arity j.val,M.mapped G P j⟩ : AnySignature AlgebraicComplex)=
        ⟨graph.shape.arity v,graph.vertex v⟩ := by
    apply C.graph_uses (matrix G f) p (mappedFamily G P)
    · rw [matrix_signature]
      exact embedded_mem G P f retained
    · exact equality_mem G P
  have native := C.graph_native (matrix G f) p
  have central : Signature.CentralSupport graph.denote := by
    rw [C.graph_denote,hw.2]
    exact C.output_central p w
  refine {
    graph := graph
    labels := M.labels G P graph uses
    exact := M.labels_exact G P graph uses
    native := native
    positive := by change 0<2; decide
    nonzero := ?_
    central := central
    reconstruct := ?_ }
  · rw [C.graph_denote,hw.2]
    exact C.output_nonzero p w hw.1
  · intro _sign cl _supports pairings
    have hc := C.class_of_pairings graph.denote central cl pairings
    rw [C.graph_denote] at hc
    rw [←matrix_signature]
    exact C.class_reconstruct (matrix G f) p cl hc

/-- Saved occurrences, including duplicate labels, retain their exact source
signature and feed the same joint model interface. -/
def saved_model (o : CurrentOccurrences.Id G P)
    (arity : (CurrentOccurrences.savedLeaf G P o).1.1=2) :
    GlobalCloseCompletionMixedEOModel.Model G P
      (FrontierCommonPresentation.embed G (CurrentOccurrences.savedLeaf G P o).1) := by
  have retained := CurrentOccurrences.savedLeaf_retained G P o
  have prime := CurrentOccurrences.savedLeaf_prime G P o
  generalize hleaf : (CurrentOccurrences.savedLeaf G P o).1=f at *
  rcases f with ⟨n,f⟩
  dsimp only at arity
  subst n
  exact model G P torsion N f retained prime

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBinaryEO
end
