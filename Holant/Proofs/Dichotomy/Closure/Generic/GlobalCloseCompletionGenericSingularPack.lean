import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularPrepare
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorPins

/-! The exact ordinary work-field table produced from the singular-cycle
anchor. The retained traceless binary and isotropic unary are literal old rows
of this same table, beside Eq4 and both computational pins. Their field scalars
are recovered from actual entries and reflected through its faithful subtype.
The input is a concrete finite native alphabet and its actual controlled
programme to G; no hardness/classification backend or field identity is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionGenericSingularPack
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace Pins
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
  (paletteArity palette palette_ambient)
end Pins
namespace Single
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single (K F)
end Single
namespace N
export GlobalCloseCompletionSingularNAND (traceless unary)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
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
  anchor : QuaternaryEqualityTerminal.AnchorStep (UniversalPairReduction.FiniteFamily.family table)
  x : AlgebraicComplex
  y : AlgebraicComplex
  u : AlgebraicComplex
  v : AlgebraicComplex
  y_nonzero : y≠0
  nonsingular : x^2+y^2≠0
  u_nonzero : u≠0
  square : v^2= -(u^2)
  binary_member : (⟨2,N.traceless x y⟩ : AnySignature AlgebraicComplex)∈
    familyAction anchor.basis (UniversalPairReduction.FiniteFamily.family table)
  unary_member : (⟨1,N.unary u v⟩ : AnySignature AlgebraicComplex)∈
    familyAction anchor.basis (UniversalPairReduction.FiniteFamily.family table)
  source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) (O.originalPresentation table).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (O.originalValue table) (OriginalForestSource.value G)
variable (d : Input G)
abbrev mapped := d.table
abbrev anchor := d.anchor
abbrev field := Single.K (mapped G d) (anchor G d)
local instance : Algebra ℚ (field G d) := (field G d).algebra'
abbrev presentation := Single.F (mapped G d) (anchor G d)
abbrev size := d.count+3
abbrev arity := Pins.paletteArity (mapped G d) (anchor G d)
abbrev table := Pins.palette (mapped G d) (anchor G d)
def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin (size G d)=>
  RingHomRealization.mapAny (field G d).subtype
    (⟨arity G d i.val,table G d i⟩ : AnySignature (field G d))

theorem transformed_included :
    familyAction d.anchor.basis (UniversalPairReduction.FiniteFamily.family (mapped G d))⊆family G d := by
  intro f hf
  rw [family,Pins.palette_ambient]
  apply Or.inl; apply Or.inl; apply Or.inl
  change f∈familyAction d.anchor.basis
    (UniversalPairReduction.FiniteFamily.family (mapped G d))
  exact hf

private theorem mapAny_injective {K L : Type} [Field K] [Field L] (phi : K→+*L) :
    Function.Injective (RingHomRealization.mapAny phi) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m := congrArg Sigma.fst h
  subst m
  have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply congrArg (fun f : Signature K n=>(⟨n,f⟩ : AnySignature K))
  funext z
  exact phi.injective (congrFun hf z)

theorem eq4_exists : ∃i : Fin (size G d),
    (⟨arity G d i.val,table G d i⟩ : AnySignature (field G d))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  have member : (⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ : AnySignature AlgebraicComplex)∈
      family G d := by
    rw [family,Pins.palette_ambient]
    exact Or.inl (Or.inl (Or.inr rfl))
  obtain ⟨i,hi⟩ := member
  refine ⟨i,?_⟩
  apply mapAny_injective (field G d).subtype
  refine hi.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 4=>(⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext z
  simp [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour]

theorem pin_exists (b : Bool) : ∃i : Fin (size G d),
    (⟨arity G d i.val,table G d i⟩ : AnySignature (field G d))=
      ⟨1,QuaternaryUnaryAccess.pin b⟩ := by
  have member : (⟨1,QuaternaryUnaryAccess.pin b⟩ : AnySignature AlgebraicComplex)∈family G d := by
    rw [family,Pins.palette_ambient]
    cases b
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl
  obtain ⟨i,hi⟩ := member
  refine ⟨i,?_⟩
  apply mapAny_injective (field G d).subtype
  refine hi.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 1=>(⟨1,f⟩ : AnySignature AlgebraicComplex))
  funext z
  simp [RingHomRealization.mapSignature,QuaternaryUnaryAccess.pin]

def e : Fin (size G d) := (eq4_exists G d).choose
def p (b : Bool) : Fin (size G d) := (pin_exists G d b).choose

theorem he : (⟨arity G d (e G d).val,table G d (e G d)⟩ : AnySignature (field G d))=
    ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := (eq4_exists G d).choose_spec
theorem hp (b : Bool) : (⟨arity G d (p G d b).val,table G d (p G d b)⟩ :
    AnySignature (field G d))=⟨1,QuaternaryUnaryAccess.pin b⟩ := (pin_exists G d b).choose_spec

private theorem cast_pair {K : Type} {m n : ℕ} (eqn : m=n) (f : Signature K m) :
    (⟨m,f⟩ : AnySignature K)=⟨n,fun z=>f (fun i=>z (Fin.cast eqn i))⟩ := by
  cases eqn
  rfl

private theorem cast_value {K : Type} {m n : ℕ} (f : Signature K m) (g : Signature K n)
    (eqn : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (hn : m=n) (z : Fin n→Bool) :
    f (fun i=>z (Fin.cast hn i))=g z := by cases eqn; rfl

def label {n : ℕ} (f : Signature AlgebraicComplex n) (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G d) :
    Fin (size G d) := member.choose

theorem labelArity {n : ℕ} (f : Signature AlgebraicComplex n)
    (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G d) :
    arity G d (label G d f member).val=n := congrArg Sigma.fst member.choose_spec

def lifted {n : ℕ} (f : Signature AlgebraicComplex n)
    (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G d) : Signature (field G d) n :=
  fun z=>table G d (label G d f member) (fun i=>z (Fin.cast (labelArity G d f member) i))

theorem lifted_literal {n : ℕ} (f : Signature AlgebraicComplex n)
    (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G d) :
    (⟨arity G d (label G d f member).val,table G d (label G d f member)⟩ :
      AnySignature (field G d))=⟨n,lifted G d f member⟩ :=
  cast_pair (labelArity G d f member) _

theorem lifted_value {n : ℕ} (f : Signature AlgebraicComplex n)
    (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G d) (z : Fin n→Bool) :
    (field G d).subtype (lifted G d f member z)=f z :=
  cast_value _ _ member.choose_spec (labelArity G d f member) z

theorem binary_member : (⟨2,N.traceless d.x d.y⟩ : AnySignature AlgebraicComplex)∈family G d :=
  transformed_included G d d.binary_member

theorem unary_member : (⟨1,N.unary d.u d.v⟩ : AnySignature AlgebraicComplex)∈family G d :=
  transformed_included G d d.unary_member

abbrev h := label G d (N.traceless d.x d.y) (binary_member G d)
abbrev w := label G d (N.unary d.u d.v) (unary_member G d)
abbrev binary := lifted G d (N.traceless d.x d.y) (binary_member G d)
abbrev unary := lifted G d (N.unary d.u d.v) (unary_member G d)
def x : field G d := binary G d ![false,false]
def y : field G d := binary G d ![false,true]
def u : field G d := unary G d (fun _=>false)
def v : field G d := unary G d (fun _=>true)

theorem x_value : (field G d).subtype (x G d)=d.x :=
  lifted_value G d _ (binary_member G d) ![false,false]
theorem y_value : (field G d).subtype (y G d)=d.y :=
  lifted_value G d _ (binary_member G d) ![false,true]
theorem u_value : (field G d).subtype (u G d)=d.u :=
  lifted_value G d _ (unary_member G d) (fun _=>false)
theorem v_value : (field G d).subtype (v G d)=d.v :=
  lifted_value G d _ (unary_member G d) (fun _=>true)

theorem binary_exact : binary G d=N.traceless (x G d) (y G d) := by
  funext z
  apply (field G d).subtype.injective
  apply (lifted_value G d _ (binary_member G d) z).trans
  cases h0 : z 0 <;> cases h1 : z 1 <;>
    simp [N.traceless,h0,h1] <;>
    first | exact (x_value G d).symm | exact (y_value G d).symm

theorem unary_exact : unary G d=N.unary (u G d) (v G d) := by
  funext z
  apply (field G d).subtype.injective
  apply (lifted_value G d _ (unary_member G d) z).trans
  cases hz : z 0 <;> simp [N.unary,hz] <;>
    first | exact (u_value G d).symm | exact (v_value G d).symm

theorem hh : (⟨arity G d (h G d).val,table G d (h G d)⟩ : AnySignature (field G d))=
    ⟨2,N.traceless (x G d) (y G d)⟩ :=
  (lifted_literal G d _ (binary_member G d)).trans (congrArg (Sigma.mk 2) (binary_exact G d))
theorem hw : (⟨arity G d (w G d).val,table G d (w G d)⟩ : AnySignature (field G d))=
    ⟨1,N.unary (u G d) (v G d)⟩ :=
  (lifted_literal G d _ (unary_member G d)).trans (congrArg (Sigma.mk 1) (unary_exact G d))

theorem y_nonzero : y G d≠0 := by
  intro zero
  apply d.y_nonzero
  rw [←y_value G d,zero,map_zero]

theorem nonsingular : (x G d)^2+(y G d)^2≠0 := by
  intro zero
  apply d.nonsingular
  have hz := congrArg (field G d).subtype zero
  simpa only [map_add,map_pow,map_zero,x_value G d,y_value G d] using hz

theorem u_nonzero : u G d≠0 := by
  intro zero
  apply d.u_nonzero
  rw [←u_value G d,zero,map_zero]

theorem square : (v G d)^2= -(u G d)^2 := by
  let phi : field G d →+* AlgebraicComplex := (field G d).val.toRingHom
  apply phi.injective
  calc
    phi ((v G d)^2) = (phi (v G d))^2 := map_pow _ _ _
    _ = d.v^2 := congrArg (fun z : AlgebraicComplex=>z^2) (v_value G d)
    _ = -d.u^2 := d.square
    _ = -(phi (u G d))^2 :=
      congrArg (fun z : AlgebraicComplex=> -(z^2)) (u_value G d).symm
    _ = phi (-((u G d)^2)) :=
      ((map_neg phi ((u G d)^2)).trans
        (congrArg Neg.neg (map_pow phi (u G d) 2))).symm

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
  Programme.compose (QuaternaryAnchorAccess.edgeControlled (mapped G d) (anchor G d))
    (Programme.compose (QuaternaryAnchorAccess.basisControlled (mapped G d) (anchor G d))
      (Programme.compose (QuaternaryAnchorAccess.macroControlled (mapped G d) (anchor G d))
        (QuaternaryAnchorAccess.originalControlled (mapped G d) (anchor G d))))
def companionSource (b : Bool) :=
  Programme.compose (QuaternaryOrdinaryCompanion.anchorControlled (mapped G d) (anchor G d) b)
    (anchorSource G d)
def pairSource (b : Bool) :=
  Programme.compose (Pair.anchorControlled d.count d.arity (mapped G d) (anchor G d) b)
    (companionSource G d b)
def singleSource (b : Bool) :=
  Programme.compose (Unary.paletteControlled (mapped G d) (anchor G d) b)
    (Programme.compose (Unary.ordinaryControlled (mapped G d) (anchor G d) b)
      (Programme.compose (Unary.factorControlled (mapped G d) (anchor G d) b)
        (Programme.compose (Unary.pairControlled (mapped G d) (anchor G d) b)
          (pairSource G d b))))
def secondPairSource :=
  Programme.compose (Both.pairPrefix (mapped G d) (anchor G d))
    (Programme.compose (Both.companionPrefix (mapped G d) (anchor G d)) (singleSource G d false))
def internalSource :=
  Programme.compose (Both.ordinaryControlled (mapped G d) (anchor G d))
    (Programme.compose (Both.factorControlled (mapped G d) (anchor G d))
      (Programme.compose (Both.nativePairControlled (mapped G d) (anchor G d)) (secondPairSource G d)))
def baseSource :=
  Programme.compose
    (Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source.paletteControlled (mapped G d) (anchor G d))
    (Programme.compose (internalSource G d) d.source)

/-- The ordinary table uses one chosen faithful work field throughout;
all its arbitrary-occurrence graph queries run back to unchanged original G. -/
def toOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (size G d) 1 (arity G d)) (presentation G d).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables (presentation G d) (table G d)).evaluate (presentation G d))
    (OriginalForestSource.value G) :=
  baseSource G d


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionGenericSingularPack
end
