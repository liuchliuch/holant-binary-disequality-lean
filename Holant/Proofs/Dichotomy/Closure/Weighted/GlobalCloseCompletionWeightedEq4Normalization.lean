import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorInput
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDiagonalCorrection
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationAdjoin

/-! A genuine weighted ordinary equality-four source is normalized internally.
Finite ratio uses positive physical graph powers. Infinite ratio adjoins one
literal diagonal via actual interpolation, then corrects one old graph leg.
The old coefficient field and all old labels remain exact in either branch. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionWeightedEq4Normalization
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.BinaryInterpolation
namespace Q
export GlobalCloseCompletionUnaryOrdinaryEquality
  (endpoint power powerLabels power_exact power_ordinary period_denote)
end Q
namespace C
export GlobalCloseCompletionUnaryDiagonalCorrection
  (binary binary_denote correct labels exact ordinary corrected)
end C
namespace I
export OrdinaryTargetInterpolationAdjoin (data signatures tables new_literal controlled)
end I
namespace Fm
export OrdinaryTargetInterpolationFamily (old_literal)
end Fm
namespace R
export OrdinaryTargetInterpolationRecovery (G kernels)
end R
namespace Diag
export OrdinaryTargetInterpolationDiagonal (diagonal)
end Diag
namespace Out
export GlobalCloseCompletionOrdinaryAnchorInput (Input mapped)
end Out
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

structure Input : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K := K.algebra'; FixedField K degree
  count : ℕ
  b : ℕ→ℕ
  H : (i : Fin count)→Signature K (b i.val)
  graph : Network K 4
  labels : Labelling graph.shape count 1 b
  exact : LabelledNetwork.Exact H graph labels
  ordinary : ∀e,graph.edge e=Signature.equality
  left : K
  right : K
  left_nonzero : left≠0
  right_nonzero : right≠0
  denote : graph.denote=Q.endpoint 4 left right
  toOriginal : letI : Algebra ℚ K := K.algebra'; LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G)

variable (D : Input G)
local instance : Algebra ℚ D.K := D.K.algebra'

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin D.count=>
  RingHomRealization.mapAny D.K.subtype (⟨D.b i.val,D.H i⟩ : AnySignature D.K)

structure Receipt : Type 1 where
  output : Out.Input G
  included : family G D⊆UniversalPairReduction.FiniteFamily.family (Out.mapped G output)

def finite (t : ℕ) (ht : 0<t) (period : (D.right/D.left)^t=1) : Receipt G D where
  output := {
    K := D.K
    degree := D.degree
    F := D.F
    count := D.count
    b := D.b
    H := D.H
    graph := Q.power D.graph (t-1)
    labels := Q.powerLabels D.graph D.labels (t-1)
    exact := Q.power_exact D.H D.graph D.labels D.exact (t-1)
    ordinary := Q.power_ordinary D.graph D.ordinary (t-1)
    scalar := D.left^t
    nonzero := pow_ne_zero _ D.left_nonzero
    denote := Q.period_denote D.graph D.left D.right D.left_nonzero D.denote t ht period
    toOriginal := D.toOriginal }
  included := fun _ h=>h

abbrev baseTables := QuaternaryOrdinaryCompanion.tables D.F D.H
abbrev binaryLabels := LabelledNetwork.contract D.graph D.labels 0 Signature.equality
abbrev template := (binaryLabels G D).template
abbrev valid := (binaryLabels G D).wellFormed

theorem boundary : (template G D).boundary=2 := rfl

private theorem cast_value {K : Type} {m n : ℕ} (f : Signature K m) (g : Signature K n)
    (eqn : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases eqn; rfl

private theorem diagonal_signature {K : Type} [Field K] (u v : K) :
    Q.endpoint 2 u v=Holant.Complexity.BinaryInterpolation.Chains.binarySignature (Diag.diagonal u v) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Q.endpoint,Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps.purePin,
      Holant.Complexity.BinaryInterpolation.Chains.binarySignature,Diag.diagonal,
      funext_iff,Fin.forall_fin_succ,h0,h1]

theorem ordinary_kernel : R.kernels (field:=D.F) (T:=baseTables G D) (0 : Fin 1)=Signature.equality := by
  funext x y
  exact D.F.decode.apply_symm_apply _

theorem macro_exact : (⟨(template G D).boundary,
    ((template G D).network (valid G D) (R.G (field:=D.F) (T:=baseTables G D))
      (R.kernels (field:=D.F) (T:=baseTables G D))).denote⟩ : AnySignature D.K)=
      ⟨2,Holant.Complexity.BinaryInterpolation.Chains.binarySignature (Diag.diagonal D.left D.right)⟩ := by
  apply congrArg (fun f : Signature D.K 2=>(⟨2,f⟩ : AnySignature D.K))
  have decoded : R.G (field:=D.F) (T:=baseTables G D)=D.H := by
    funext i x
    exact D.F.decode.apply_symm_apply _
  rw [decoded,Labelling.denote_template]
  have real : ((binaryLabels G D).sourceNetwork D.H (R.kernels (field:=D.F) (T:=baseTables G D))).denote=
      (C.binary D.graph).denote := by
    apply Network.denote_congr
    · intro v x
      exact cast_value _ _ (D.exact v) (D.labels.vertex_arity v) x
    · intro e x y
      have ho : (C.binary D.graph).edge e=Signature.equality :=
        Fin.cases rfl (fun e=>D.ordinary e) e
      exact (congrFun₂ (ordinary_kernel G D) x y).trans (congrFun₂ ho.symm x y)
  rw [real,C.binary_denote D.graph D.left D.right D.denote,diagonal_signature]

abbrev interpolation := I.data D.F (baseTables G D) (template G D) (valid G D) (boundary G D)
  (0 : Fin 1) D.left D.right (D.left/D.right)
abbrev arity := PhysicalQueries.A (s:=D.count) D.b (template G D)
abbrev signatures := I.signatures D.F (baseTables G D) (template G D) (valid G D) (boundary G D)
  (0 : Fin 1) D.left D.right (D.left/D.right)
abbrev tables := I.tables D.F (baseTables G D) (template G D) (valid G D) (boundary G D)
  (0 : Fin 1) D.left D.right (D.left/D.right)
def old (i : Fin D.count) : Fin (D.count+1) := Fin.castAdd 1 i
def newLabel : Fin (D.count+1) := ⟨D.count,Nat.lt_succ_self _⟩

theorem old_literal (i : Fin D.count) :
    (⟨arity G D (old G D i).val,signatures G D (old G D i)⟩ : AnySignature D.K)=⟨D.b i.val,D.H i⟩ := by
  refine (Fm.old_literal (interpolation G D) (Diag.diagonal 1 0) (Diag.diagonal 0 1) i).trans ?_
  apply congrArg (fun f : Signature D.K (D.b i.val)=>(⟨D.b i.val,f⟩ : AnySignature D.K))
  funext x
  exact D.F.decode.apply_symm_apply _

theorem new_literal : (⟨arity G D (newLabel G D).val,signatures G D (newLabel G D)⟩ : AnySignature D.K)=
    ⟨2,Q.endpoint 2 1 (D.left/D.right)⟩ := by
  exact (I.new_literal D.F (baseTables G D) (template G D) (valid G D) (boundary G D)
    (0 : Fin 1) D.left D.right (D.left/D.right)).trans
      (congrArg (fun f : Signature D.K 2=>(⟨2,f⟩ : AnySignature D.K)) (diagonal_signature _ _).symm)

def oldLabels : Labelling D.graph.shape (D.count+1) 1 (arity G D) where
  vertex v := old G D (D.labels.vertex v)
  vertex_arity v := (congrArg Sigma.fst (old_literal G D (D.labels.vertex v))).trans (D.labels.vertex_arity v)
  edge := D.labels.edge

theorem old_exact : LabelledNetwork.Exact (signatures G D) D.graph (oldLabels G D) :=
  fun v=>(old_literal G D (D.labels.vertex v)).trans (D.exact v)

def diagonalGraph : Network D.K 2 := Network.corolla (Q.endpoint 2 1 (D.left/D.right))
def diagonalLabels : Labelling (diagonalGraph G D).shape (D.count+1) 1 (arity G D) where
  vertex _ := newLabel G D
  vertex_arity _ := congrArg Sigma.fst (new_literal G D)
  edge e := Fin.elim0 e

theorem diagonal_exact : LabelledNetwork.Exact (signatures G D) (diagonalGraph G D) (diagonalLabels G D) :=
  fun _=>new_literal G D

theorem ordinary_tables : QuaternaryOrdinaryCompanion.tables D.F (signatures G D)=tables G D := rfl

variable (infinite : ∀t : ℕ,0<t→(D.right/D.left)^t≠1)

def interpolatedSource : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (D.count+1) 1 (arity G D)) D.F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables D.F (signatures G D)).evaluate D.F) (OriginalForestSource.value G) := by
  have source := I.controlled D.F (baseTables G D) (template G D) (valid G D) (boundary G D)
    (0 : Fin 1) D.left D.right (D.left/D.right) (ordinary_kernel G D) (macro_exact G D)
    D.left_nonzero D.right_nonzero infinite
  exact Programme.compose (by simpa only [ordinary_tables] using source) D.toOriginal

def nonperiodic : Receipt G D where
  output := {
    K := D.K
    degree := D.degree
    F := D.F
    count := D.count+1
    b := arity G D
    H := signatures G D
    graph := C.correct D.graph (diagonalGraph G D)
    labels := C.labels D.graph (diagonalGraph G D) (oldLabels G D) (diagonalLabels G D)
    exact := C.exact (signatures G D) D.graph (diagonalGraph G D) (oldLabels G D) (diagonalLabels G D)
      (old_exact G D) (diagonal_exact G D)
    ordinary := C.ordinary D.graph (diagonalGraph G D) D.ordinary (fun e=>Fin.elim0 e)
    scalar := D.left
    nonzero := D.left_nonzero
    denote := C.corrected D.graph (diagonalGraph G D) D.left D.right D.right_nonzero D.denote
      (Network.denote_corolla _)
    toOriginal := interpolatedSource G D infinite }
  included := by
    rintro f ⟨i,rfl⟩
    refine ⟨old G D i,?_⟩
    change RingHomRealization.mapAny D.K.subtype
      (⟨arity G D (old G D i).val,signatures G D (old G D i)⟩ : AnySignature D.K)=_
    rw [old_literal]

/-- Both alternatives are selected internally from the actual old weights. -/
def produce : Receipt G D := by
  classical
  by_cases period : ∃t : ℕ,0<t ∧ (D.right/D.left)^t=1
  · exact finite G D period.choose period.choose_spec.1 period.choose_spec.2
  · exact nonperiodic G D (fun t ht hpow=>period ⟨t,ht,hpow⟩)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionWeightedEq4Normalization
end
