import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryXAdjoin
import Holant.Proofs.Dichotomy.General.GenericOrdinarySource

/-! Install a genuine ordinary unary graph as one literal label of the same
fixed-field source. The actual graph is expanded at every occurrence by the
controlled adjoin compiler, and all old rows and the original-G oracle remain
unchanged. The whole-family obstruction passes to the larger literal table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryLiteralSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {degree s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (a i.val))

structure Output : Type where
  network : Network K 1
  labels : Labelling network.shape s 1 a
  exact : LabelledNetwork.Exact H network labels
  ordinary : ∀e,network.edge e=Signature.equality

variable (d : Output H)
abbrev baseTables := QuaternaryOrdinaryCompanion.tables F H
abbrev template := d.labels.template
abbrev arity := sourceArity (Adjoin.templates s a (template H d))
abbrev coordinates := ScaledAdjoin.coordinates F (baseTables F H)
  (template H d) d.labels.wellFormed (1 : K)
abbrev tables := sourceTables (Adjoin.templates s a (template H d)) (baseTables F H) (coordinates F H d)
def signatures (i : Fin (s+1)) : Signature K (arity H d i.val) :=
  fun x=>F.decode ((tables F H d).vertex i x)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (arity H d)

private theorem exact_cast {L : Type} {m n : ℕ} (f : Signature L m) (g : Signature L n)
    (h : (⟨m,f⟩ : AnySignature L)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h; rfl

theorem macro_exact : ((template H d).network d.labels.wellFormed
    (fun i x=>F.decode ((baseTables F H).vertex i x))
    (fun j b c=>F.decode ((baseTables F H).edge j b c))).denote=d.network.denote := by
  simp only [baseTables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  rw [Labelling.denote_template]
  apply Network.denote_congr
  · intro v x
    exact exact_cast _ _ (d.exact v) (d.labels.vertex_arity v) x
  · intro e b c
    exact congrFun (congrFun (d.ordinary e).symm b) c

private def decodeAny (f : AnySignature (Fin degree→ℚ)) : AnySignature K :=
  ⟨f.1,fun x=>F.decode (f.2 x)⟩

def old (_H : (i : Fin s)→Signature K (a i.val)) (i : Fin s) : Fin (s+1) := Fin.castAdd 1 i
def unaryLabel (_H : (i : Fin s)→Signature K (a i.val)) : Fin (s+1) := ⟨s,Nat.lt_succ_self _⟩

theorem old_literal (i : Fin s) :
    (⟨arity H d (old H i).val,signatures F H d (old H i)⟩ : AnySignature K)=⟨a i.val,H i⟩ := by
  have h : (⟨arity H d (old H i).val,coordinates F H d (old H i)⟩ :
      AnySignature (Fin degree→ℚ))=⟨a i.val,(baseTables F H).vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (template H d) i)
      (ScaledAdjoin.old_coordinates F (baseTables F H) (template H d) d.labels.wellFormed (1 : K) i)
  refine (congrArg (decodeAny F) h).trans ?_
  apply congrArg (fun f : Signature K (a i.val)=>(⟨a i.val,f⟩ : AnySignature K))
  funext x
  exact LinearEquiv.apply_symm_apply _ _

theorem unary_literal :
    (⟨arity H d (unaryLabel H).val,signatures F H d (unaryLabel H)⟩ : AnySignature K)=
      ⟨1,d.network.denote⟩ := by
  have h : (⟨arity H d (unaryLabel H).val,coordinates F H d (unaryLabel H)⟩ :
      AnySignature (Fin degree→ℚ))=
      ⟨1,fun x=>F.decode.symm (((template H d).network d.labels.wellFormed
        (fun i x=>F.decode ((baseTables F H).vertex i x))
        (fun j b c=>F.decode ((baseTables F H).edge j b c))).denote x/(1 : K))⟩ :=
    Sigma.ext (Adjoin.new_boundary (template H d))
      (ScaledAdjoin.new_coordinates F (baseTables F H) (template H d) d.labels.wellFormed (1 : K))
  refine (congrArg (decodeAny F) h).trans ?_
  apply congrArg (fun f : Signature K 1=>(⟨1,f⟩ : AnySignature K))
  funext x
  change F.decode (F.decode.symm _)=_
  rw [LinearEquiv.apply_symm_apply,macro_exact,div_one]

theorem ordinary_tables : QuaternaryOrdinaryCompanion.tables F (signatures F H d)=tables F H d := by
  unfold QuaternaryOrdinaryCompanion.tables
  congr 1
  · funext i x
    exact F.decode.symm_apply_apply _

def source : LengthControlledOracleReduction
    (inputEncoding H d) F.encoding (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F (signatures F H d)).evaluate F)
    ((baseTables F H).evaluate F) := by
  rw [ordinary_tables]
  exact Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin F (baseTables F H)
    (template H d) d.labels.wellFormed (1 : K) one_ne_zero

section Original
variable {r : ℕ} {b : ℕ→ℕ}
variable (G : (i : Fin r)→Signature AlgebraicComplex (b i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (u : Output src.H)

def data : GenericOrdinarySource.Data G where
  K := src.K
  degree := src.degree
  F := src.F
  size := src.size+1
  b := arity src.H u
  H := signatures src.F src.H u
  e := old src.H src.e
  p v := old src.H (src.p v)
  he := (old_literal src.F src.H u src.e).trans src.he
  hp v := (old_literal src.F src.H u (src.p v)).trans (src.hp v)
  toOriginal := Programme.compose (source src.F src.H u) src.toOriginal

theorem family_included : GenericOrdinarySource.family G src⊆GenericOrdinarySource.family G (data G src u) := by
  rintro f ⟨i,rfl⟩
  refine ⟨old src.H i,?_⟩
  change RingHomRealization.mapAny src.K.subtype
    (⟨arity src.H u (old src.H i).val,signatures src.F src.H u (old src.H i)⟩ : AnySignature src.K)=_
  rw [old_literal]

theorem obstruction (negative : StableHigherCurrentOrdinaryTerminal.Obstruction
    (preprocess (GenericOrdinarySource.family G src))) :
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G (data G src u))) := by
  apply (GenericOrdinarySource.rejected_iff G (data G src u)).mp
  intro tract
  exact (GenericOrdinarySource.rejected_iff G src).mpr negative
    (tract.mono_family (family_included G src u))


end Original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryLiteralSource
end
