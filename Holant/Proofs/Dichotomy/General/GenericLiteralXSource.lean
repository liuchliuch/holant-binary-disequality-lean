import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4FullSource

/-! A generic actual literal-Eq4/pin/X ordinary source.  The sole computational
input is a real length-controlled ordinary-graph programme to unchanged G.
No Palette assertion, class decision, or hardness backend is a field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GenericLiteralXSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

structure Data : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K := K.algebra'; FixedField K degree
  size : ℕ
  b : ℕ→ℕ
  H : (i : Fin size)→Signature K (b i.val)
  e : Fin size
  p : Bool→Fin size
  x : Fin size
  he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩
  hp : ∀v : Bool,(⟨b (p v).val,H (p v)⟩ : AnySignature K)=⟨1,QuaternaryUnaryAccess.pin v⟩
  hx : (⟨b x.val,H x⟩ : AnySignature K)=⟨2,fun z=>Signature.disequality (z 0) (z 1)⟩
  toOriginal : letI : Algebra ℚ K := K.algebra'; LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding size 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G)

variable (src : Data G)
abbrev field := src.K
local instance : Algebra ℚ (field G src) := (field G src).algebra'
abbrev presentation := src.F
abbrev count := src.size
abbrev arity := src.b
abbrev table := src.H
abbrev eq4Label := src.e
abbrev pinLabel := src.p
abbrev xLabel := src.x
abbrev eq4_literal := src.he
abbrev pin_literal := src.hp
abbrev x_literal := src.hx
abbrev ordinarySource := src.toOriginal

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin (count G src) =>
  RingHomRealization.mapAny (field G src).subtype ⟨arity G src i.val,table G src i⟩

theorem family_eq4 : (⟨4,StableHigherCurrentAnchorCriterion.eq4⟩ : AnySignature AlgebraicComplex)∈
    family G src := by
  refine ⟨eq4Label G src,?_⟩
  dsimp only
  rw [eq4_literal]
  apply congrArg (fun f : Signature AlgebraicComplex 4 => (⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,StableHigherCurrentAnchorCriterion.eq4,
    Holant.EightVertex.ProductAnchor.equalityFour]

theorem family_pin (b : Bool) :
    (⟨1,StableHigherCurrentOrdinaryTerminal.L.pin b⟩ : AnySignature AlgebraicComplex)∈family G src := by
  refine ⟨pinLabel G src b,?_⟩
  dsimp only
  rw [pin_literal]
  apply congrArg (fun f : Signature AlgebraicComplex 1 => (⟨1,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,QuaternaryUnaryAccess.pin,
    StableHigherCurrentAnchorLocalBasis.pin]

theorem family_x : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈
    family G src := by
  refine ⟨xLabel G src,?_⟩
  dsimp only
  rw [x_literal]
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,kernelSignature,Signature.disequality]


def evenCSPSource := PhysicalProgramme.ofControlled (Programme.compose
  (StableHigherCurrentEvenCSPSource.controlled (presentation G src) (table G src)
    (eq4Label G src) (eq4_literal G src)) (ordinarySource G src))

def squareCSPSource := PhysicalProgramme.ofControlled (Programme.compose
  (StableHigherCurrentEvenCSPSource.squareGraphControlled (presentation G src) (table G src)
    (eq4Label G src) (eq4_literal G src)) (ordinarySource G src))

theorem tract_iff_test : Tract (family G src) ↔
    StableHigherCurrentOrdinaryTerminal.Test (preprocess (family G src)) := by
  rw [StableHigherCurrentOrdinaryTerminal.tract_iff_finite_test
    (family_pin G src false) (family_pin G src true) (family_eq4 G src)]
  exact and_iff_right ((Set.finite_range _).subset (fun _ h => h.1))

theorem rejected_iff : ¬Tract (family G src) ↔
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (family G src)) :=
  StableHigherCurrentOrdinaryTerminal.not_tract_iff_obstruction
    ((Set.finite_range _).subset (fun _ h => h.1))
    (family_pin G src false) (family_pin G src true) (family_eq4 G src)

/-- The established native Eq4 source is one concrete instance. -/
def ofEq4 (P : Palette G) (out : GlobalCloseCompletionEq4Graph.Output G P) : Data G where
  K := GlobalCloseCompletionEq4CSPSource.field G P out
  degree := _
  F := GlobalCloseCompletionEq4CSPSource.presentation G P out
  size := GlobalCloseCompletionEq4FullSource.count G P
  b := GlobalCloseCompletionEq4FullSource.arity G P out
  H := GlobalCloseCompletionEq4FullSource.table G P out
  e := GlobalCloseCompletionEq4FullSource.eq4Label G P
  p := GlobalCloseCompletionEq4FullSource.pinLabel G P
  x := GlobalCloseCompletionEq4FullSource.xLabel G P
  he := GlobalCloseCompletionEq4FullSource.eq4_literal G P out
  hp := GlobalCloseCompletionEq4FullSource.pin_literal G P out
  hx := GlobalCloseCompletionEq4FullSource.x_literal G P out
  toOriginal := GlobalCloseCompletionEq4FullSource.ordinarySource G P out

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GenericLiteralXSource
end
