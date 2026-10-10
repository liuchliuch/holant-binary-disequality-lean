import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularPrepare
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorPins

/-! The exact ordinary work-field table produced from the singular-cycle
anchor. The retained traceless binary and isotropic unary are literal old rows
of this same table, beside Eq4 and both computational pins. Their field scalars
are recovered from actual entries and reflected through its faithful subtype.
No new adjoin, successful source, or coefficient-field identity is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularOrdinaryPack
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
variable (P : Palette G) (d : GlobalCloseCompletionSingularPrepare.Prepared G P)

abbrev mapped := StableHigherCurrentPurePinsCore.mapped G d.palette
abbrev anchor := StableHigherCurrentFamilyTransport.fromAmbient G d.palette d.anchor
abbrev field := Single.K (mapped G P d) (anchor G P d)
local instance : Algebra ℚ (field G P d) := (field G P d).algebra'
abbrev presentation := Single.F (mapped G P d) (anchor G P d)
abbrev size := d.palette.count+3
abbrev arity := Pins.paletteArity (mapped G P d) (anchor G P d)
abbrev table := Pins.palette (mapped G P d) (anchor G P d)
def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin (size G P d)=>
  RingHomRealization.mapAny (field G P d).subtype
    (⟨arity G P d i.val,table G P d i⟩ : AnySignature (field G P d))

theorem transformed_included :
    familyAction d.anchor.basis (ClosureSourceRows.ambientFamily G d.palette)⊆family G P d := by
  intro f hf
  rw [family,Pins.palette_ambient]
  apply Or.inl; apply Or.inl; apply Or.inl
  change f∈familyAction d.anchor.basis
    (UniversalPairReduction.FiniteFamily.family (mapped G P d))
  rw [←StableHigherCurrentFamilyTransport.ambientFamily_eq G d.palette]
  exact hf

theorem current_included :
    familyAction d.anchor.basis (ClosureSourceRows.ambientFamily G P)⊆family G P d :=
  fun _ hf=>transformed_included G P d ((familyAction_mono d.anchor.basis d.old) hf)

private theorem mapAny_injective {K L : Type} [Field K] [Field L] (phi : K→+*L) :
    Function.Injective (RingHomRealization.mapAny phi) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m := congrArg Sigma.fst h
  subst m
  have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply congrArg (fun f : Signature K n=>(⟨n,f⟩ : AnySignature K))
  funext z
  exact phi.injective (congrFun hf z)

theorem eq4_exists : ∃i : Fin (size G P d),
    (⟨arity G P d i.val,table G P d i⟩ : AnySignature (field G P d))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  have member : (⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ : AnySignature AlgebraicComplex)∈
      family G P d := by
    rw [family,Pins.palette_ambient]
    exact Or.inl (Or.inl (Or.inr rfl))
  obtain ⟨i,hi⟩ := member
  refine ⟨i,?_⟩
  apply mapAny_injective (field G P d).subtype
  refine hi.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 4=>(⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext z
  simp [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour]

theorem pin_exists (b : Bool) : ∃i : Fin (size G P d),
    (⟨arity G P d i.val,table G P d i⟩ : AnySignature (field G P d))=
      ⟨1,QuaternaryUnaryAccess.pin b⟩ := by
  have member : (⟨1,QuaternaryUnaryAccess.pin b⟩ : AnySignature AlgebraicComplex)∈family G P d := by
    rw [family,Pins.palette_ambient]
    cases b
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl
  obtain ⟨i,hi⟩ := member
  refine ⟨i,?_⟩
  apply mapAny_injective (field G P d).subtype
  refine hi.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 1=>(⟨1,f⟩ : AnySignature AlgebraicComplex))
  funext z
  simp [RingHomRealization.mapSignature,QuaternaryUnaryAccess.pin]

def e : Fin (size G P d) := (eq4_exists G P d).choose
def p (b : Bool) : Fin (size G P d) := (pin_exists G P d b).choose

theorem he : (⟨arity G P d (e G P d).val,table G P d (e G P d)⟩ : AnySignature (field G P d))=
    ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := (eq4_exists G P d).choose_spec
theorem hp (b : Bool) : (⟨arity G P d (p G P d b).val,table G P d (p G P d b)⟩ :
    AnySignature (field G P d))=⟨1,QuaternaryUnaryAccess.pin b⟩ := (pin_exists G P d b).choose_spec

private theorem cast_pair {K : Type} {m n : ℕ} (eqn : m=n) (f : Signature K m) :
    (⟨m,f⟩ : AnySignature K)=⟨n,fun z=>f (fun i=>z (Fin.cast eqn i))⟩ := by
  cases eqn
  rfl

private theorem cast_value {K : Type} {m n : ℕ} (f : Signature K m) (g : Signature K n)
    (eqn : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (hn : m=n) (z : Fin n→Bool) :
    f (fun i=>z (Fin.cast hn i))=g z := by cases eqn; rfl

def label {n : ℕ} (f : Signature AlgebraicComplex n) (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G P d) :
    Fin (size G P d) := member.choose

theorem labelArity {n : ℕ} (f : Signature AlgebraicComplex n)
    (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G P d) :
    arity G P d (label G P d f member).val=n := congrArg Sigma.fst member.choose_spec

def lifted {n : ℕ} (f : Signature AlgebraicComplex n)
    (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G P d) : Signature (field G P d) n :=
  fun z=>table G P d (label G P d f member) (fun i=>z (Fin.cast (labelArity G P d f member) i))

theorem lifted_literal {n : ℕ} (f : Signature AlgebraicComplex n)
    (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G P d) :
    (⟨arity G P d (label G P d f member).val,table G P d (label G P d f member)⟩ :
      AnySignature (field G P d))=⟨n,lifted G P d f member⟩ :=
  cast_pair (labelArity G P d f member) _

theorem lifted_value {n : ℕ} (f : Signature AlgebraicComplex n)
    (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈family G P d) (z : Fin n→Bool) :
    (field G P d).subtype (lifted G P d f member z)=f z :=
  cast_value _ _ member.choose_spec (labelArity G P d f member) z

theorem binary_member : (⟨2,N.traceless d.x d.y⟩ : AnySignature AlgebraicComplex)∈family G P d := by
  have h := transformed_included G P d
    (show (⟨2,d.anchor.basis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) d.binary)⟩ :
      AnySignature AlgebraicComplex)∈familyAction d.anchor.basis (ClosureSourceRows.ambientFamily G d.palette) from
      ⟨_,⟨⟨2,d.binary⟩,d.binary_retained,rfl⟩,rfl⟩)
  rwa [d.binary_exact] at h

theorem unary_member : (⟨1,N.unary d.u d.v⟩ : AnySignature AlgebraicComplex)∈family G P d := by
  have h := transformed_included G P d
    (show (⟨1,d.anchor.basis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) d.unary)⟩ :
      AnySignature AlgebraicComplex)∈familyAction d.anchor.basis (ClosureSourceRows.ambientFamily G d.palette) from
      ⟨_,⟨⟨1,d.unary⟩,d.unary_retained,rfl⟩,rfl⟩)
  rwa [d.unary_exact] at h

abbrev h := label G P d (N.traceless d.x d.y) (binary_member G P d)
abbrev w := label G P d (N.unary d.u d.v) (unary_member G P d)
abbrev binary := lifted G P d (N.traceless d.x d.y) (binary_member G P d)
abbrev unary := lifted G P d (N.unary d.u d.v) (unary_member G P d)
def x : field G P d := binary G P d ![false,false]
def y : field G P d := binary G P d ![false,true]
def u : field G P d := unary G P d (fun _=>false)
def v : field G P d := unary G P d (fun _=>true)

theorem x_value : (field G P d).subtype (x G P d)=d.x :=
  lifted_value G P d _ (binary_member G P d) ![false,false]
theorem y_value : (field G P d).subtype (y G P d)=d.y :=
  lifted_value G P d _ (binary_member G P d) ![false,true]
theorem u_value : (field G P d).subtype (u G P d)=d.u :=
  lifted_value G P d _ (unary_member G P d) (fun _=>false)
theorem v_value : (field G P d).subtype (v G P d)=d.v :=
  lifted_value G P d _ (unary_member G P d) (fun _=>true)

theorem binary_exact : binary G P d=N.traceless (x G P d) (y G P d) := by
  funext z
  apply (field G P d).subtype.injective
  apply (lifted_value G P d _ (binary_member G P d) z).trans
  cases h0 : z 0 <;> cases h1 : z 1 <;>
    simp [N.traceless,h0,h1] <;>
    first | exact (x_value G P d).symm | exact (y_value G P d).symm

theorem unary_exact : unary G P d=N.unary (u G P d) (v G P d) := by
  funext z
  apply (field G P d).subtype.injective
  apply (lifted_value G P d _ (unary_member G P d) z).trans
  cases hz : z 0 <;> simp [N.unary,hz] <;>
    first | exact (u_value G P d).symm | exact (v_value G P d).symm

theorem hh : (⟨arity G P d (h G P d).val,table G P d (h G P d)⟩ : AnySignature (field G P d))=
    ⟨2,N.traceless (x G P d) (y G P d)⟩ :=
  (lifted_literal G P d _ (binary_member G P d)).trans (congrArg (Sigma.mk 2) (binary_exact G P d))
theorem hw : (⟨arity G P d (w G P d).val,table G P d (w G P d)⟩ : AnySignature (field G P d))=
    ⟨1,N.unary (u G P d) (v G P d)⟩ :=
  (lifted_literal G P d _ (unary_member G P d)).trans (congrArg (Sigma.mk 1) (unary_exact G P d))

theorem y_nonzero : y G P d≠0 := by
  intro zero
  apply d.y_nonzero
  rw [←y_value G P d,zero,map_zero]

theorem nonsingular : (x G P d)^2+(y G P d)^2≠0 := by
  intro zero
  apply d.nonsingular
  have hz := congrArg (field G P d).subtype zero
  simpa only [map_add,map_pow,map_zero,x_value G P d,y_value G P d] using hz

theorem u_nonzero : u G P d≠0 := by
  intro zero
  apply d.u_nonzero
  rw [←u_value G P d,zero,map_zero]

theorem square : (v G P d)^2= -(u G P d)^2 := by
  let phi : field G P d →+* AlgebraicComplex := (field G P d).val.toRingHom
  apply phi.injective
  calc
    phi ((v G P d)^2) = (phi (v G P d))^2 := map_pow _ _ _
    _ = d.v^2 := congrArg (fun z : AlgebraicComplex=>z^2) (v_value G P d)
    _ = -d.u^2 := d.square
    _ = -(phi (u G P d))^2 :=
      congrArg (fun z : AlgebraicComplex=> -(z^2)) (u_value G P d).symm
    _ = phi (-((u G P d)^2)) :=
      ((map_neg phi ((u G P d)^2)).trans
        (congrArg Neg.neg (map_pow phi (u G P d) 2))).symm

/-- The ordinary table uses one chosen faithful work field throughout;
all its arbitrary-occurrence graph queries run back to unchanged original G. -/
def toOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (size G P d) 1 (arity G P d)) (presentation G P d).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables (presentation G P d) (table G P d)).evaluate (presentation G P d))
    (OriginalForestSource.value G) :=
  (StableHigherCurrentAnchorPins.fromAmbientToOriginal G d.palette d.anchor).controlled


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularOrdinaryPack
end
