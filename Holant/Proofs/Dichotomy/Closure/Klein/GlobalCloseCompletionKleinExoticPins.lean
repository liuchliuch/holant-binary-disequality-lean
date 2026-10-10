import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinExoticOrdinarySource

/-! The actual exotic ordinary Eq4 graph is descended to the fixed original
field with its literal finite labels. The ordinary source programme is kept,
and the checked Eq4-to-pins construction retains the complete H dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticPins
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
namespace S
export GlobalCloseCompletionKleinExoticOrdinarySource
  (retained table mapped graph labels graph_exact graph_ordinary outputScalar outputScalar_nonzero graph_denote)
end S
namespace I
export GlobalCloseCompletionOrdinaryAnchorInput (Input)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (exotic : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.exotic)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

abbrev sourceGraph := S.graph G P torsion cardinal noncyclic exotic q core literal stable
abbrev sourceLabels := S.labels G P torsion cardinal noncyclic exotic q core literal stable

def lifted : Network (OI.K G) 4 := (sourceLabels G P torsion cardinal noncyclic exotic q core literal stable).sourceNetwork
  (S.table G P torsion q core literal) (fun _ : Fin 1=>Signature.equality)

private theorem exact_cast {L : Type} {m n : ℕ} (f : Signature L m) (g : Signature L n)
    (h : (⟨m,f⟩ : AnySignature L)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h; rfl

theorem map_lifted : (lifted G P torsion cardinal noncyclic exotic q core literal stable).map
    (ClosureSourceRows.embedding G)=sourceGraph G P torsion cardinal noncyclic exotic q core literal stable := by
  unfold Network.map lifted Labelling.sourceNetwork
  congr 1
  · funext v x
    exact exact_cast _ _ (S.graph_exact G P torsion cardinal noncyclic exotic q core literal stable v)
      ((sourceLabels G P torsion cardinal noncyclic exotic q core literal stable).vertex_arity v) x
  · funext e b c
    change ClosureSourceRows.embedding G (Signature.equality b c)=
      (sourceGraph G P torsion cardinal noncyclic exotic q core literal stable).edge e b c
    rw [S.graph_ordinary]
    cases b <;> cases c <;> simp [Signature.equality]

theorem lifted_denote (x : Fin 4→Bool) :
    ClosureSourceRows.embedding G ((lifted G P torsion cardinal noncyclic exotic q core literal stable).denote x)=
      (sourceGraph G P torsion cardinal noncyclic exotic q core literal stable).denote x := by
  rw [←Network.denote_map (ClosureSourceRows.embedding G),map_lifted]

def scalar : OI.K G := (lifted G P torsion cardinal noncyclic exotic q core literal stable).denote (fun _=>false)

theorem scalar_value : ClosureSourceRows.embedding G (scalar G P torsion cardinal noncyclic exotic q core literal stable)=
    S.outputScalar G P torsion cardinal noncyclic exotic q core literal stable := by
  rw [scalar,lifted_denote,S.graph_denote]
  simp [Holant.EightVertex.ProductAnchor.equalityFour]

theorem scalar_nonzero : scalar G P torsion cardinal noncyclic exotic q core literal stable≠0 := by
  intro zero
  apply S.outputScalar_nonzero G P torsion cardinal noncyclic exotic q core literal stable
  exact (scalar_value G P torsion cardinal noncyclic exotic q core literal stable).symm.trans (by rw [zero,map_zero])

def input : I.Input G where
  K := OI.K G
  degree := _
  F := OI.presentation G
  count := (S.retained G P torsion q core literal).count
  b := (S.retained G P torsion q core literal).arity
  H := S.table G P torsion q core literal
  graph := lifted G P torsion cardinal noncyclic exotic q core literal stable
  labels := sourceLabels G P torsion cardinal noncyclic exotic q core literal stable
  exact := by
    intro v
    apply Sigma.ext ((sourceLabels G P torsion cardinal noncyclic exotic q core literal stable).vertex_arity v)
    exact HEq.symm (EdgeSubdivision.signature_cast_heq
      ((sourceLabels G P torsion cardinal noncyclic exotic q core literal stable).vertex_arity v)
      (S.table G P torsion q core literal ((sourceLabels G P torsion cardinal noncyclic exotic q core literal stable).vertex v)))
  ordinary := fun _=>rfl
  scalar := scalar G P torsion cardinal noncyclic exotic q core literal stable
  nonzero := scalar_nonzero G P torsion cardinal noncyclic exotic q core literal stable
  denote := by
    funext x
    apply (ClosureSourceRows.embedding G).injective
    refine (lifted_denote G P torsion cardinal noncyclic exotic q core literal stable x).trans
      ((congrFun (S.graph_denote G P torsion cardinal noncyclic exotic q core literal stable) x).trans ?_)
    change _*_=ClosureSourceRows.embedding G (_*_)
    rw [map_mul,scalar_value]
    congr 1
    simp [Holant.EightVertex.ProductAnchor.equalityFour,apply_ite]
  toOriginal := GlobalCloseCompletionA0OrdinarySource.source G (S.retained G P torsion q core literal)

def data : GenericOrdinarySource.Data G := GlobalCloseCompletionOrdinaryAnchorPins.data G
  (input G P torsion cardinal noncyclic exotic q core literal stable)

theorem old_included : UniversalPairReduction.FiniteFamily.family (S.mapped G P torsion q core literal)⊆
    GenericOrdinarySource.family G (data G P torsion cardinal noncyclic exotic q core literal stable) :=
  GlobalCloseCompletionOrdinaryAnchorPins.old_included G
    (input G P torsion cardinal noncyclic exotic q core literal stable)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticPins
end
