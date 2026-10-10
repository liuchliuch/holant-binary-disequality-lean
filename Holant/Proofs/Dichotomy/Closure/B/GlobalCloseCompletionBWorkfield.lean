import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Pins
import Holant.Proofs.Algorithms.HolographicTransport
import Holant.Marked.Dictionary

/-! A complete whole-current B-coordinate source with exact ordinary edges.
The extra imaginary unit belongs only to the finite work field. Every old
label remains once, and scalar edge correction plus a real answer retraction
terminates at the unchanged original-G oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBWorkfield
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace GOT
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients coefficients_algebraic originalPresentation originalTables originalValue target_exact)
end GOT
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
abbrev mapped := StableHigherCurrentPurePinsCore.mapped G P
abbrev originalCoefficient := OriginalFamily.coefficient (mapped G P) KSourceTransport.nativeEdges
def values : ExactSignatureTables.CoefficientIndex P.count 1 P.arity ⊕ Unit → AlgebraicComplex
  | .inl c => originalCoefficient G P c
  | .inr _ => imaginaryUnit

theorem algebraic (i) : IsAlgebraic ℚ (values G P i) := Algebra.IsAlgebraic.isAlgebraic _
abbrev K := familyField (values G P)
local instance : Algebra ℚ (K G P) := (K G P).algebra'
abbrev field := familyPresentation (values G P) (algebraic G P)
abbrev originalTables := PresentedScaledFamily.tables (values G P) (algebraic G P) Sum.inl
abbrev originalValue := (originalTables G P).evaluate (field G P)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding P.count 1 P.arity

def imaginary : K G P := fieldCoefficient (values G P) (.inr ())
def delta : K G P := -2*imaginary G P

@[simp] theorem imaginary_value : (K G P).val (imaginary G P)=imaginaryUnit := rfl

theorem delta_nonzero : delta G P≠0 := by
  intro zero
  apply Holant.Marked.edgeB_multiplier_ne_zero
  exact congrArg (fun z : K G P => (z : AlgebraicComplex)) zero

def matrix : Kernel (K G P) := fun b c => Signature.equality b c-imaginary G P*Signature.disequality b c
def inverse : Kernel (K G P) := fun b c => (Signature.equality b c+imaginary G P*Signature.disequality b c)/2

theorem matrix_value (b c : Bool) : (K G P).val (matrix G P b c)=Holant.Marked.basisB.matrix b c := by
  cases b <;> cases c <;> rfl

theorem inverse_value (b c : Bool) : (K G P).val (inverse G P b c)=Holant.Marked.basisB.inverse b c := by
  change (K G P).val ((Signature.equality b c+imaginary G P*Signature.disequality b c)/2)=_
  cases b <;> cases c <;>
    simp [map_div₀,map_ofNat,imaginary_value,
      Holant.Marked.basisB,Holant.Marked.UBInv,Signature.equality,Signature.disequality]

theorem matrix_inverse : Kernel.mul (matrix G P) (inverse G P)=Signature.equality := by
  funext b c
  apply Subtype.val_injective
  have h := congrFun (congrFun Holant.Marked.basisB.matrix_inverse b) c
  change (K G P).val (Kernel.mul (matrix G P) (inverse G P) b c)=
    (K G P).val (Signature.equality b c)
  cases b <;> cases c <;>
    simpa [Kernel.mul_apply,map_add,map_mul,matrix_value,inverse_value,Signature.equality] using h

theorem edge_exact : Kernel.pullback Signature.disequality (matrix G P)=
    fun b c => delta G P*Signature.equality b c := by
  funext b c
  apply Subtype.val_injective
  change (K G P).val (Kernel.pullback Signature.disequality (matrix G P) b c)=
    (K G P).val (delta G P*Signature.equality b c)
  have h := congrFun (congrFun Holant.Marked.edgeB b) c
  cases b <;> cases c <;>
    simpa [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,delta,
      map_add,map_mul,map_neg,map_ofNat,matrix_value,imaginary_value,
      Signature.equality,Signature.disequality,ite_true,ite_false,reduceCtorEq,map_zero,map_one,
      Holant.Marked.sectorEdge,Holant.Marked.scale,Holant.Marked.basisB,Holant.Marked.UB] using h

theorem original_vertex (i : Fin P.count) (x : Fin (P.arity i.val) → Bool) :
    (K G P).val ((field G P).decode ((originalTables G P).vertex i x))=mapped G P i x :=
  familyCoordinates_spec (values G P) (algebraic G P) (.inl (.inl ⟨i,x⟩))

theorem original_edge (i : Fin 1) (b c : Bool) :
    (field G P).decode ((originalTables G P).edge i b c)=Signature.disequality b c := by
  apply Subtype.val_injective
  have h := familyCoordinates_spec (values G P) (algebraic G P) (.inl (.inr (i,b,c)))
  change (((field G P).decode ((originalTables G P).edge i b c) : K G P) : AlgebraicComplex)=
    Signature.disequality b c at h
  simpa only [Signature.disequality,apply_ite,IntermediateField.coe_zero,IntermediateField.coe_one] using h

abbrev transformed := HolographicTransport.tables (field G P) (originalTables G P) (matrix G P) (inverse G P)
def tables : ExactSignatureTables (Module.finrank ℚ (K G P)) P.count 1 P.arity where
  vertex := (transformed G P).vertex
  edge _ b c := (field G P).decode.symm (Signature.equality b c)
def table (i : Fin P.count) : Signature (K G P) (P.arity i.val) :=
  fun x => (field G P).decode ((tables G P).vertex i x)
abbrev value := (tables G P).evaluate (field G P)

theorem table_value (i : Fin P.count) (x : Fin (P.arity i.val) → Bool) :
    (table G P i x : AlgebraicComplex)=Holant.Marked.basisB.symm.action (mapped G P i) x := by
  change (K G P).val ((field G P).decode ((transformed G P).vertex i x))=_
  simp only [transformed,HolographicTransport.tables,LinearEquiv.apply_symm_apply,
    Signature.coordinateAction,map_sum,map_mul,map_prod,original_vertex,inverse_value]
  rfl

theorem transformed_edge (i : Fin 1) (b c : Bool) :
    (field G P).decode ((transformed G P).edge i b c)=delta G P*Signature.equality b c := by
  simp only [transformed,HolographicTransport.tables,LinearEquiv.apply_symm_apply]
  simp_rw [original_edge]
  exact congrFun (congrFun (edge_exact G P) b) c

theorem transformed_value (r : ExactSignatureTables.Input P.count 1 P.arity) :
    (transformed G P).evaluate (field G P) r=(delta G P)^r.val.edges.length*value G P r := by
  unfold value
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [Network.denote,RawClosedNetwork.realize,tables,LinearEquiv.apply_symm_apply]
  simp_rw [transformed_edge]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change (∑z,_)=(delta G P)^r.val.edges.length*∑z,_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [RawClosedNetwork.shape]
  ring

def edgeControlled : LengthControlledOracleReduction (inputEncoding G P) (field G P).encoding
    (inputEncoding G P) (field G P).encoding (value G P) ((transformed G P).evaluate (field G P)) :=
  ControlledCap.controlledContextOfEq
    (pairComputes (identityComputes (inputEncoding G P)) (Compiler.edgeCountComputes P.count 1 P.arity))
    (ScalarPower.correction (field G P) (delta G P))
    ((transformed G P).outputBound (field G P)) (value G P) (fun r => by
      change value G P r=_*(delta G P)⁻¹^r.val.edges.length
      dsimp only [id,Prod.fst,Prod.snd]
      rw [transformed_value,ScalarPower.cancel_scale_power _ _ (delta_nonzero G P)])

def originalControlled : LengthControlledOracleReduction
    (inputEncoding G P) (field G P).encoding
    (inputEncoding G P) (GOT.originalPresentation (mapped G P)).encoding
    (originalValue G P) (GOT.originalValue (mapped G P)) :=
  controlledOneQueryOfEq (identityComputes (inputEncoding G P))
    (FamilyAnswerTransport.computes (values G P) (GOT.coefficients (mapped G P))
      (algebraic G P) (GOT.coefficients_algebraic (mapped G P)))
    ((GOT.originalTables (mapped G P)).outputBound (GOT.originalPresentation (mapped G P)))
    (originalValue G P) (fun r => by
      symm
      apply FamilyAnswerTransport.recover_exact
      unfold originalValue originalTables
      rw [GOT.target_exact,PresentedScaledFamily.target_value_exact]
      rfl)

def source : LengthControlledOracleReduction
    (inputEncoding G P) (field G P).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P) (OriginalForestSource.value G) :=
  Programme.compose (edgeControlled G P)
    (Programme.compose (HolographicTransport.fromTransformed (field G P) (originalTables G P)
      (matrix G P) (inverse G P) (matrix_inverse G P))
      (Programme.compose (originalControlled G P)
        (Programme.compose (OriginalLCodec.fromCoefficient (StableHigherCurrentPurePinsCore.embedding G) P.table)
          P.toOriginal.controlled)))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBWorkfield
end
