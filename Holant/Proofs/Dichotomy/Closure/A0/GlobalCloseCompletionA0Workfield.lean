import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Pins
import Holant.Proofs.Algorithms.HolographicTransport
import Holant.Proofs.Closure.ClosureMarkedDihedralA0

/-! Whole-current Hadamard coordinates in the unchanged original coefficient
field. Every current label is retained once. The exact transformed edge is
2Z; removing its factor two is charged by the actual edge-count programme.
Neither coordinate table nor coordinate matrix is asserted to be a Palette. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Workfield
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
abbrev K := OI.K G
abbrev field := OI.presentation G
abbrev mapped := StableHigherCurrentPurePinsCore.mapped G P
abbrev matrix : Kernel (K G) := ClosureMarkedCyclic.Source.sourceMatrix
abbrev inverse : Kernel (K G) := ClosureMarkedCyclic.Source.sourceInverse
abbrev basis := ClosureMarkedDihedralA0.basis

def z : Kernel (K G) := fun b c => if b=c then (if b then -1 else 1) else 0

theorem matrix_inverse : Kernel.mul (matrix G) (inverse G)=Signature.equality := by
  funext b c
  cases b <;> cases c <;>
    norm_num [matrix,inverse,ClosureMarkedCyclic.Source.sourceMatrix,
      ClosureMarkedCyclic.Source.sourceInverse,Kernel.mul_apply,Signature.equality]

theorem edge_exact : Kernel.pullback Signature.disequality (matrix G)=
    fun b c => 2*z G b c := by
  funext b c
  cases b <;> cases c <;>
    norm_num [matrix,ClosureMarkedCyclic.Source.sourceMatrix,z,
      Kernel.pullback,Kernel.mul_apply,Kernel.transpose,Signature.disequality]

theorem inverse_value (b c : Bool) :
    StableHigherCurrentPurePinsCore.embedding G (inverse G b c)=basis.inverse b c := by
  cases b <;> cases c <;>
    simp [inverse,ClosureMarkedCyclic.Source.sourceInverse,basis,
      ClosureMarkedDihedralA0.basis,ClosureMarkedCyclic.basis,
      Holant.Marked.basisA,Holant.Marked.UAInv,map_ofNat]
  change (StableHigherCurrentPurePinsCore.embedding G) (2 : K G)=2
  exact map_ofNat _ 2

abbrev originalTables := OriginalLCodec.tables P.table
abbrev transformed := HolographicTransport.tables (field G) (originalTables G P) (matrix G) (inverse G)
def tables : ExactSignatureTables (Module.finrank ℚ (K G)) P.count 1 P.arity where
  vertex := (transformed G P).vertex
  edge _ b c := (field G).decode.symm (z G b c)
def table (i : Fin P.count) : Signature (K G) (P.arity i.val) :=
  fun x => (field G).decode ((tables G P).vertex i x)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding P.count 1 P.arity
abbrev value := (tables G P).evaluate (field G)

theorem original_vertex (i : Fin P.count) (x : Fin (P.arity i.val) → Bool) :
    (field G).decode ((originalTables G P).vertex i x)=P.table i x := by
  exact LinearEquiv.apply_symm_apply _ _

theorem original_edge (i : Fin 1) (b c : Bool) :
    (field G).decode ((originalTables G P).edge i b c)=Signature.disequality b c := by
  exact LinearEquiv.apply_symm_apply _ _

theorem table_exact (i : Fin P.count) : table G P i=
    Signature.coordinateAction (fun _ => inverse G) (P.table i) := by
  funext x
  simp only [table,tables,transformed,HolographicTransport.tables,
    LinearEquiv.apply_symm_apply,original_vertex]

theorem table_value (i : Fin P.count) (x : Fin (P.arity i.val) → Bool) :
    StableHigherCurrentPurePinsCore.embedding G (table G P i x)=
      basis.symm.action (mapped G P i) x := by
  rw [table_exact]
  simp only [Signature.coordinateAction,map_sum,map_mul,map_prod,inverse_value]
  rfl

theorem transformed_edge (i : Fin 1) (b c : Bool) :
    (field G).decode ((transformed G P).edge i b c)=2*z G b c := by
  simp only [transformed,HolographicTransport.tables,LinearEquiv.apply_symm_apply]
  simp_rw [original_edge]
  exact congrFun (congrFun (edge_exact G) b) c

theorem transformed_value (r : ExactSignatureTables.Input P.count 1 P.arity) :
    (transformed G P).evaluate (field G) r=(2 : K G)^r.val.edges.length*value G P r := by
  unfold value
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [Network.denote,RawClosedNetwork.realize,tables,LinearEquiv.apply_symm_apply]
  simp_rw [transformed_edge]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change (∑z,_)=(2 : K G)^r.val.edges.length*∑z,_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [RawClosedNetwork.shape]
  ring

def edgeControlled : LengthControlledOracleReduction (inputEncoding G P) (field G).encoding
    (inputEncoding G P) (field G).encoding (value G P) ((transformed G P).evaluate (field G)) :=
  ControlledCap.controlledContextOfEq
    (pairComputes (identityComputes (inputEncoding G P)) (Compiler.edgeCountComputes P.count 1 P.arity))
    (ScalarPower.correction (field G) 2)
    ((transformed G P).outputBound (field G)) (value G P) (fun r => by
      change value G P r=_*(2 : K G)⁻¹^r.val.edges.length
      dsimp only [id,Prod.fst,Prod.snd]
      rw [transformed_value,ScalarPower.cancel_scale_power _ _ (by norm_num : (2 : K G)≠0)])

def source : LengthControlledOracleReduction
    (inputEncoding G P) (field G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P) (OriginalForestSource.value G) :=
  Programme.compose (edgeControlled G P)
    (Programme.compose (HolographicTransport.fromTransformed (field G) (originalTables G P)
      (matrix G) (inverse G) (matrix_inverse G)) P.toOriginal.controlled)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Workfield
end
