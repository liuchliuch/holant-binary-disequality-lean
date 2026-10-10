import Holant.Proofs.Dichotomy.Closure.Dense.GlobalCloseCompletionDenseCanonicalCurrent
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryXAdjoin
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra

/-! An actual canonical dense binary supplies literal X to the SAME ordinary
Eq4/two-pin dictionary. The actual binary graph is transformed in the anchor's
matrix, descended by its literal labels to that dictionary's fixed field,
and normalized by its own nonzero off-diagonal entry. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionDenseLiteralX
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
variable (P : Palette G)
variable (C : GlobalCloseCompletionBDenseCanonical.Canonical (ClosureSourceRows.ambientFamily G P))
abbrev H := StableHigherCurrentPurePinsCore.mapped G P
abbrev anchor := StableHigherCurrentFamilyTransport.fromAmbient G P C.anchor
abbrev field := Single.K (H G P) (anchor G P C)
local instance : Algebra ℚ (field G P C) := (field G P C).algebra'
abbrev presentation := Single.F (H G P) (anchor G P C)
abbrev baseArity := Pins.paletteArity (H G P) (anchor G P C)
abbrev baseTable := Pins.palette (H G P) (anchor G P C)
def mapped (i : Fin (P.count+3)) : Signature AlgebraicComplex (baseArity G P C i.val) :=
  RingHomRealization.mapSignature (field G P C).subtype (baseTable G P C i)

def native := Classical.choose (OrdinaryNormalization.realizes_exists_ordinary
  (StableDenseGaugeCurrent.ambient_identity G P) C.binary_actual)
theorem native_labels : ∀v,(⟨(native G P C).shape.arity v,(native G P C).vertex v⟩ :
    AnySignature AlgebraicComplex)∈ClosureSourceRows.ambientFamily G P :=
  (Classical.choose_spec (OrdinaryNormalization.realizes_exists_ordinary
    (StableDenseGaugeCurrent.ambient_identity G P) C.binary_actual)).1
theorem native_edges : ∀e,(native G P C).edge e=Signature.disequality :=
  (Classical.choose_spec (OrdinaryNormalization.realizes_exists_ordinary
    (StableDenseGaugeCurrent.ambient_identity G P) C.binary_actual)).2.1
theorem native_denote : (native G P C).denote=C.binary :=
  (Classical.choose_spec (OrdinaryNormalization.realizes_exists_ordinary
    (StableDenseGaugeCurrent.ambient_identity G P) C.binary_actual)).2.2

def graph : Network AlgebraicComplex 2 := OpenHolographic.transform
  (native G P C) C.basis.inverse C.basis.matrix

theorem graph_edges : ∀e,(graph G P C).edge e=Signature.equality := by
  intro e
  change Kernel.pullback ((native G P C).edge e) C.basis.inverse=_
  rw [native_edges]
  have h := C.anchor.edge_exact
  change Kernel.pullback Signature.disequality C.basis.inverse=(fun b c=>1*Signature.equality b c) at h
  simpa only [one_mul] using h

theorem graph_denote : (graph G P C).denote=
    fun x=>C.binaryScale*Signature.disequality (x 0) (x 1) := by
  rw [graph,OpenHolographic.denote_transform (native G P C) C.basis.inverse C.basis.matrix
    C.basis.inverse_matrix,native_denote]
  exact C.binary_exact

theorem graph_labels : ∀v,(⟨(graph G P C).shape.arity v,(graph G P C).vertex v⟩ :
    AnySignature AlgebraicComplex)∈UniversalPairReduction.FiniteFamily.family (mapped G P C) := by
  intro v
  have member : (⟨(graph G P C).shape.arity v,(graph G P C).vertex v⟩ :
      AnySignature AlgebraicComplex)∈Holant.Tractable.familyAction C.basis
        (ClosureSourceRows.ambientFamily G P) :=
    ⟨⟨(native G P C).shape.arity v,(native G P C).vertex v⟩,native_labels G P C v,rfl⟩
  have h := Pins.palette_ambient (H G P) (anchor G P C)
  rw [UniversalPairReduction.FiniteFamily.family]
  change (⟨(graph G P C).shape.arity v,(graph G P C).vertex v⟩ : AnySignature AlgebraicComplex)∈
    Set.range (fun i=>RingHomRealization.mapAny (field G P C).subtype
      (⟨baseArity G P C i.val,baseTable G P C i⟩ : AnySignature (field G P C)))
  rw [h]
  apply Or.inl; apply Or.inl; apply Or.inl
  change _∈familyAction C.basis (UniversalPairReduction.FiniteFamily.family (H G P))
  rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq G P]
  exact member

def labels := UniversalPairReduction.FiniteFamily.labelling (mapped G P C)
  (graph G P C) (graph_labels G P C)

def lifted : Network (field G P C) 2 := (labels G P C).sourceNetwork
  (baseTable G P C) (fun _ : Fin 1=>Signature.equality)

private theorem exact_cast {L : Type} {m n : ℕ} (f : Signature L m) (g : Signature L n)
    (h : (⟨m,f⟩ : AnySignature L)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h; rfl

theorem map_lifted : (lifted G P C).map (field G P C).subtype=graph G P C := by
  unfold Network.map lifted Labelling.sourceNetwork
  congr 1
  · funext v x
    change mapped G P C ((labels G P C).vertex v)
      (fun i=>x (Fin.cast ((labels G P C).vertex_arity v) i))=(graph G P C).vertex v x
    exact exact_cast _ _ (graph_labels G P C v).choose_spec
      ((labels G P C).vertex_arity v) x
  · funext e b c
    change (field G P C).subtype (Signature.equality b c)=(graph G P C).edge e b c
    rw [graph_edges]
    cases b <;> cases c <;> rfl

theorem lifted_denote (x : Fin 2→Bool) :
    (field G P C).subtype ((lifted G P C).denote x)=(graph G P C).denote x := by
  rw [←Network.denote_map (field G P C).subtype,map_lifted]

def scalar : field G P C := (lifted G P C).denote ![false,true]
theorem scalar_value : (field G P C).subtype (scalar G P C)=C.binaryScale := by
  rw [scalar,lifted_denote,graph_denote]
  simp [Signature.disequality]
theorem scalar_nonzero : scalar G P C≠0 := by
  intro zero
  apply C.binary_nonzero
  exact (scalar_value G P C).symm.trans (by rw [zero,map_zero])

def output : X.Output (baseTable G P C) where
  network := lifted G P C
  labels := labels G P C
  exact := by
    intro v
    apply Sigma.ext ((labels G P C).vertex_arity v)
    exact HEq.symm (EdgeSubdivision.signature_cast_heq ((labels G P C).vertex_arity v)
      (baseTable G P C ((labels G P C).vertex v)))
  ordinary := fun _=>rfl
  scalar := scalar G P C
  nonzero := scalar_nonzero G P C
  denote := by
    funext x
    apply (field G P C).subtype.injective
    refine (lifted_denote G P C x).trans ((congrFun (graph_denote G P C) x).trans ?_)
    rw [map_mul]
    apply congrArg₂ (fun a b : AlgebraicComplex=>a*b) (scalar_value G P C).symm
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

theorem base_eq4_exists : ∃i : Fin (P.count+3),
    (⟨baseArity G P C i.val,baseTable G P C i⟩ : AnySignature (field G P C))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  have member : (⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ : AnySignature AlgebraicComplex)∈
      Set.range (fun i=>RingHomRealization.mapAny (field G P C).subtype
        (⟨baseArity G P C i.val,baseTable G P C i⟩ : AnySignature (field G P C))) := by
    rw [Pins.palette_ambient]
    exact Or.inl (Or.inl (Or.inr rfl))
  obtain ⟨i,hi⟩ := member
  refine ⟨i,?_⟩
  apply mapAny_injective (field G P C).subtype
  refine hi.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 4=>(⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour]

theorem base_pin_exists (b : Bool) : ∃i : Fin (P.count+3),
    (⟨baseArity G P C i.val,baseTable G P C i⟩ : AnySignature (field G P C))=
      ⟨1,QuaternaryUnaryAccess.pin b⟩ := by
  have member : (⟨1,QuaternaryUnaryAccess.pin b⟩ : AnySignature AlgebraicComplex)∈
      Set.range (fun i=>RingHomRealization.mapAny (field G P C).subtype
        (⟨baseArity G P C i.val,baseTable G P C i⟩ : AnySignature (field G P C))) := by
    rw [Pins.palette_ambient]
    cases b
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl
  obtain ⟨i,hi⟩ := member
  refine ⟨i,?_⟩
  apply mapAny_injective (field G P C).subtype
  refine hi.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 1=>(⟨1,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,QuaternaryUnaryAccess.pin]

def data : GenericLiteralXSource.Data G where
  K := field G P C
  degree := _
  F := presentation G P C
  size := (P.count+3)+1
  b := X.arity (baseTable G P C) (output G P C)
  H := X.signatures (presentation G P C) (baseTable G P C) (output G P C)
  e := X.old (baseTable G P C) (base_eq4_exists G P C).choose
  p b := X.old (baseTable G P C) (base_pin_exists G P C b).choose
  x := X.xLabel (baseTable G P C)
  he := (X.old_literal (presentation G P C) (baseTable G P C) (output G P C) _).trans
    (base_eq4_exists G P C).choose_spec
  hp b := (X.old_literal (presentation G P C) (baseTable G P C) (output G P C) _).trans
    (base_pin_exists G P C b).choose_spec
  hx := X.x_literal (presentation G P C) (baseTable G P C) (output G P C)
  toOriginal := Programme.compose
    (X.source (presentation G P C) (baseTable G P C) (output G P C))
    (StableHigherCurrentAnchorPins.fromAmbientToOriginal G P C.anchor).controlled

theorem current_included : familyAction C.basis (ClosureSourceRows.ambientFamily G P)⊆
    GenericLiteralXSource.family G (data G P C) := by
  intro f hf
  have member : f∈Set.range (fun i=>RingHomRealization.mapAny (field G P C).subtype
      (⟨baseArity G P C i.val,baseTable G P C i⟩ : AnySignature (field G P C))) := by
    rw [Pins.palette_ambient]
    apply Or.inl; apply Or.inl; apply Or.inl
    change f∈familyAction C.basis (UniversalPairReduction.FiniteFamily.family (H G P))
    rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq G P]
    exact hf
  obtain ⟨i,hi⟩ := member
  refine ⟨X.old (baseTable G P C) i,?_⟩
  change RingHomRealization.mapAny (field G P C).subtype
    (⟨X.arity (baseTable G P C) (output G P C) (X.old (baseTable G P C) i).val,
      X.signatures (presentation G P C) (baseTable G P C) (output G P C)
        (X.old (baseTable G P C) i)⟩ : AnySignature (field G P C))=f
  rw [X.old_literal]
  exact hi


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionDenseLiteralX
end
