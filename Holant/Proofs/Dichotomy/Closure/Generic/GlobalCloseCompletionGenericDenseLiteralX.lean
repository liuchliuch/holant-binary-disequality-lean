import Holant.Proofs.Dichotomy.Closure.Dense.GlobalCloseCompletionDenseCanonicalCurrent
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryXAdjoin
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra

/-! An actual canonical dense binary supplies literal X to the SAME ordinary
Eq4/two-pin dictionary. The actual binary graph is transformed in the anchor's
matrix, descended by its literal labels to that dictionary's fixed field,
and normalized by its own nonzero off-diagonal entry. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionGenericDenseLiteralX
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.OpenNetworkComposition
namespace Pins
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
  (paletteArity palette palette_ambient value inputEncoding)
end Pins
namespace Single
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single (K F)
end Single
namespace X
export GlobalCloseCompletionOrdinaryXAdjoin (Output arity signatures old xLabel old_literal x_literal source)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
structure Input where
  count : ℕ
  arity : ℕ→ℕ
  table : (i : Fin count)→Signature AlgebraicComplex (arity i.val)
  identity : Holant.LocalDrafts.FinitePGL2.Stabilization.RetainsIdentity
    (UniversalPairReduction.FiniteFamily.family table)
  canonical : GlobalCloseCompletionBDenseCanonical.Canonical
    (UniversalPairReduction.FiniteFamily.family table)
  source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) (O.originalPresentation table).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (O.originalValue table) (OriginalForestSource.value G)
variable (D : Input G)
abbrev H := D.table
abbrev anchor := D.canonical.anchor
abbrev field := Single.K (H G D) (anchor G D)
local instance : Algebra ℚ (field G D) := (field G D).algebra'
abbrev presentation := Single.F (H G D) (anchor G D)
abbrev baseArity := Pins.paletteArity (H G D) (anchor G D)
abbrev baseTable := Pins.palette (H G D) (anchor G D)
def mapped (i : Fin (D.count+3)) : Signature AlgebraicComplex (baseArity G D i.val) :=
  RingHomRealization.mapSignature (field G D).subtype (baseTable G D i)

def native := Classical.choose (OrdinaryNormalization.realizes_exists_ordinary
  (D.identity) D.canonical.binary_actual)
theorem native_labels : ∀v,(⟨(native G D).shape.arity v,(native G D).vertex v⟩ :
    AnySignature AlgebraicComplex)∈UniversalPairReduction.FiniteFamily.family (H G D) :=
  (Classical.choose_spec (OrdinaryNormalization.realizes_exists_ordinary
    (D.identity) D.canonical.binary_actual)).1
theorem native_edges : ∀e,(native G D).edge e=Signature.disequality :=
  (Classical.choose_spec (OrdinaryNormalization.realizes_exists_ordinary
    (D.identity) D.canonical.binary_actual)).2.1
theorem native_denote : (native G D).denote=D.canonical.binary :=
  (Classical.choose_spec (OrdinaryNormalization.realizes_exists_ordinary
    (D.identity) D.canonical.binary_actual)).2.2

def graph : Network AlgebraicComplex 2 := OpenHolographic.transform
  (native G D) D.canonical.basis.inverse D.canonical.basis.matrix

theorem graph_edges : ∀e,(graph G D).edge e=Signature.equality := by
  intro e
  change Kernel.pullback ((native G D).edge e) D.canonical.basis.inverse=_
  rw [native_edges]
  have h := D.canonical.anchor.edge_exact
  change Kernel.pullback Signature.disequality D.canonical.basis.inverse=(fun b c=>1*Signature.equality b c) at h
  simpa only [one_mul] using h

theorem graph_denote : (graph G D).denote=
    fun x=>D.canonical.binaryScale*Signature.disequality (x 0) (x 1) := by
  rw [graph,OpenHolographic.denote_transform (native G D) D.canonical.basis.inverse D.canonical.basis.matrix
    D.canonical.basis.inverse_matrix,native_denote]
  exact D.canonical.binary_exact

theorem graph_labels : ∀v,(⟨(graph G D).shape.arity v,(graph G D).vertex v⟩ :
    AnySignature AlgebraicComplex)∈UniversalPairReduction.FiniteFamily.family (mapped G D) := by
  intro v
  have member : (⟨(graph G D).shape.arity v,(graph G D).vertex v⟩ :
      AnySignature AlgebraicComplex)∈Holant.Tractable.familyAction D.canonical.basis
        (UniversalPairReduction.FiniteFamily.family (H G D)) :=
    ⟨⟨(native G D).shape.arity v,(native G D).vertex v⟩,native_labels G D v,rfl⟩
  have h := Pins.palette_ambient (H G D) (anchor G D)
  rw [UniversalPairReduction.FiniteFamily.family]
  change (⟨(graph G D).shape.arity v,(graph G D).vertex v⟩ : AnySignature AlgebraicComplex)∈
    Set.range (fun i=>RingHomRealization.mapAny (field G D).subtype
      (⟨baseArity G D i.val,baseTable G D i⟩ : AnySignature (field G D)))
  rw [h]
  apply Or.inl; apply Or.inl; apply Or.inl
  change _∈familyAction D.canonical.basis (UniversalPairReduction.FiniteFamily.family (H G D))
  exact member

def labels := UniversalPairReduction.FiniteFamily.labelling (mapped G D)
  (graph G D) (graph_labels G D)

def lifted : Network (field G D) 2 := (labels G D).sourceNetwork
  (baseTable G D) (fun _ : Fin 1=>Signature.equality)

private theorem exact_cast {L : Type} {m n : ℕ} (f : Signature L m) (g : Signature L n)
    (h : (⟨m,f⟩ : AnySignature L)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h; rfl

theorem map_lifted : (lifted G D).map (field G D).subtype=graph G D := by
  unfold Network.map lifted Labelling.sourceNetwork
  congr 1
  · funext v x
    change mapped G D ((labels G D).vertex v)
      (fun i=>x (Fin.cast ((labels G D).vertex_arity v) i))=(graph G D).vertex v x
    exact exact_cast _ _ (graph_labels G D v).choose_spec
      ((labels G D).vertex_arity v) x
  · funext e b c
    change (field G D).subtype (Signature.equality b c)=(graph G D).edge e b c
    rw [graph_edges]
    cases b <;> cases c <;> rfl

theorem lifted_denote (x : Fin 2→Bool) :
    (field G D).subtype ((lifted G D).denote x)=(graph G D).denote x := by
  rw [←Network.denote_map (field G D).subtype,map_lifted]

def scalar : field G D := (lifted G D).denote ![false,true]
theorem scalar_value : (field G D).subtype (scalar G D)=D.canonical.binaryScale := by
  rw [scalar,lifted_denote,graph_denote]
  simp [Signature.disequality]
theorem scalar_nonzero : scalar G D≠0 := by
  intro zero
  apply D.canonical.binary_nonzero
  exact (scalar_value G D).symm.trans (by rw [zero,map_zero])

def output : X.Output (baseTable G D) where
  network := lifted G D
  labels := labels G D
  exact := by
    intro v
    apply Sigma.ext ((labels G D).vertex_arity v)
    exact HEq.symm (EdgeSubdivision.signature_cast_heq ((labels G D).vertex_arity v)
      (baseTable G D ((labels G D).vertex v)))
  ordinary := fun _=>rfl
  scalar := scalar G D
  nonzero := scalar_nonzero G D
  denote := by
    funext x
    apply (field G D).subtype.injective
    refine (lifted_denote G D x).trans ((congrFun (graph_denote G D) x).trans ?_)
    rw [map_mul]
    apply congrArg₂ (fun a b : AlgebraicComplex=>a*b) (scalar_value G D).symm
    cases x 0 <;> cases x 1 <;> simp [Signature.disequality]

private theorem mapAny_injective {K L : Type} [Field K] [Field L] (φ : K→+*L) :
    Function.Injective (RingHomRealization.mapAny φ) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m := congrArg Sigma.fst h
  subst m
  have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply congrArg (fun f : Signature K n=>(⟨n,f⟩ : AnySignature K))
  funext x
  exact φ.injective (congrFun hf x)

theorem base_eq4_exists : ∃i : Fin (D.count+3),
    (⟨baseArity G D i.val,baseTable G D i⟩ : AnySignature (field G D))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  have member : (⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ : AnySignature AlgebraicComplex)∈
      Set.range (fun i=>RingHomRealization.mapAny (field G D).subtype
        (⟨baseArity G D i.val,baseTable G D i⟩ : AnySignature (field G D))) := by
    rw [Pins.palette_ambient]
    exact Or.inl (Or.inl (Or.inr rfl))
  obtain ⟨i,hi⟩ := member
  refine ⟨i,?_⟩
  apply mapAny_injective (field G D).subtype
  refine hi.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 4=>(⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour]

theorem base_pin_exists (b : Bool) : ∃i : Fin (D.count+3),
    (⟨baseArity G D i.val,baseTable G D i⟩ : AnySignature (field G D))=
      ⟨1,QuaternaryUnaryAccess.pin b⟩ := by
  have member : (⟨1,QuaternaryUnaryAccess.pin b⟩ : AnySignature AlgebraicComplex)∈
      Set.range (fun i=>RingHomRealization.mapAny (field G D).subtype
        (⟨baseArity G D i.val,baseTable G D i⟩ : AnySignature (field G D))) := by
    rw [Pins.palette_ambient]
    cases b
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl
  obtain ⟨i,hi⟩ := member
  refine ⟨i,?_⟩
  apply mapAny_injective (field G D).subtype
  refine hi.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 1=>(⟨1,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,QuaternaryUnaryAccess.pin]

namespace Pair
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication (anchorControlled)
end Pair
namespace Unary
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess
  (pairControlled factorControlled ordinaryControlled paletteControlled)
end Unary
namespace Both
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins
  (pairPrefix companionPrefix nativePairControlled factorControlled ordinaryControlled)
end Both

def anchorSource :=
  Programme.compose (QuaternaryAnchorAccess.edgeControlled (H G D) (anchor G D))
    (Programme.compose (QuaternaryAnchorAccess.basisControlled (H G D) (anchor G D))
      (Programme.compose (QuaternaryAnchorAccess.macroControlled (H G D) (anchor G D))
        (QuaternaryAnchorAccess.originalControlled (H G D) (anchor G D))))
def companionSource (b : Bool) :=
  Programme.compose (QuaternaryOrdinaryCompanion.anchorControlled (H G D) (anchor G D) b)
    (anchorSource G D)
def pairSource (b : Bool) :=
  Programme.compose (Pair.anchorControlled D.count D.arity (H G D) (anchor G D) b)
    (companionSource G D b)
def singleSource (b : Bool) :=
  Programme.compose (Unary.paletteControlled (H G D) (anchor G D) b)
    (Programme.compose (Unary.ordinaryControlled (H G D) (anchor G D) b)
      (Programme.compose (Unary.factorControlled (H G D) (anchor G D) b)
        (Programme.compose (Unary.pairControlled (H G D) (anchor G D) b)
          (pairSource G D b))))
def secondPairSource :=
  Programme.compose (Both.pairPrefix (H G D) (anchor G D))
    (Programme.compose (Both.companionPrefix (H G D) (anchor G D)) (singleSource G D false))
def internalSource :=
  Programme.compose (Both.ordinaryControlled (H G D) (anchor G D))
    (Programme.compose (Both.factorControlled (H G D) (anchor G D))
      (Programme.compose (Both.nativePairControlled (H G D) (anchor G D)) (secondPairSource G D)))
def baseSource :=
  Programme.compose
    (Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source.paletteControlled (H G D) (anchor G D))
    (Programme.compose (internalSource G D) D.source)

def data : GenericLiteralXSource.Data G where
  K := field G D
  degree := _
  F := presentation G D
  size := (D.count+3)+1
  b := X.arity (baseTable G D) (output G D)
  H := X.signatures (presentation G D) (baseTable G D) (output G D)
  e := X.old (baseTable G D) (base_eq4_exists G D).choose
  p b := X.old (baseTable G D) (base_pin_exists G D b).choose
  x := X.xLabel (baseTable G D)
  he := (X.old_literal (presentation G D) (baseTable G D) (output G D) _).trans
    (base_eq4_exists G D).choose_spec
  hp b := (X.old_literal (presentation G D) (baseTable G D) (output G D) _).trans
    (base_pin_exists G D b).choose_spec
  hx := X.x_literal (presentation G D) (baseTable G D) (output G D)
  toOriginal := Programme.compose
    (X.source (presentation G D) (baseTable G D) (output G D))
    (baseSource G D)

theorem current_included : familyAction D.canonical.basis (UniversalPairReduction.FiniteFamily.family (H G D))⊆
    GenericLiteralXSource.family G (data G D) := by
  intro f hf
  have member : f∈Set.range (fun i=>RingHomRealization.mapAny (field G D).subtype
      (⟨baseArity G D i.val,baseTable G D i⟩ : AnySignature (field G D))) := by
    rw [Pins.palette_ambient]
    apply Or.inl; apply Or.inl; apply Or.inl
    change f∈familyAction D.canonical.basis (UniversalPairReduction.FiniteFamily.family (H G D))
    exact hf
  obtain ⟨i,hi⟩ := member
  refine ⟨X.old (baseTable G D) i,?_⟩
  change RingHomRealization.mapAny (field G D).subtype
    (⟨X.arity (baseTable G D) (output G D) (X.old (baseTable G D) i).val,
      X.signatures (presentation G D) (baseTable G D) (output G D)
        (X.old (baseTable G D) i)⟩ : AnySignature (field G D))=f
  rw [X.old_literal]
  exact hi


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionGenericDenseLiteralX
end
