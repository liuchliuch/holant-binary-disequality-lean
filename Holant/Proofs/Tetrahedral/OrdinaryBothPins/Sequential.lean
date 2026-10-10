import Holant.Proofs.Tetrahedral.OrdinaryBothPins.Coordinates


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution UniversalPairReduction
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.GeneralExtraction
open scoped BigOperators

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (FiniteFamily.family G))
local instance : Algebra ℚ (Single.K G A) := (Single.K G A).algebra'
local instance : CharZero (Single.K G A) := Algebra.charZero_of_charZero ℚ (Single.K G A)

abbrev internalEncoding (n : ℕ) := RawClosedNetwork.validatedEncoding ((s+3)+n) 1 (arity G A)
def nativeTables (n : ℕ) := GeneralFieldReduction.targetTables (Single.F G A) (nativeFamily G A n)
def ordinaryTables (n : ℕ) := Companion.tables (Single.F G A) (ordinaryFamily G A n)
abbrev nativeValue (n : ℕ) := (nativeTables G A n).evaluate (Single.F G A)
abbrev ordinaryValue (n : ℕ) := (ordinaryTables G A n).evaluate (Single.F G A)
def transformedTables (n : ℕ) := HolographicTransport.tables (Single.F G A) (nativeTables G A n)
  (Anchor.inverse G A) (Anchor.matrix G A)

theorem transformed_vertex (n : ℕ) (i : Fin ((s+3)+n)) (x : Fin (arity G A i.val) → Bool) :
    (Single.F G A).decode ((transformedTables G A n).vertex i x)=ordinaryFamily G A n i x := by
  simp only [transformedTables,HolographicTransport.tables,LinearEquiv.apply_symm_apply]
  change Signature.coordinateAction (fun _ => Anchor.matrix G A)
    (fun y => (Single.F G A).decode ((nativeTables G A n).vertex i y)) x=_
  simp only [nativeTables,GeneralFieldReduction.targetTables,
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables,
    LinearEquiv.apply_symm_apply,nativeFamily,FactorSaturation.PrefixMachine.family,
    ordinaryFamily]
  exact congrFun (forward G A i.val) x

theorem transformed_edge (n : ℕ) (i : Fin 1) (b c : Bool) :
    (Single.F G A).decode ((transformedTables G A n).edge i b c)=
      Anchor.kappa G A*Signature.equality b c := by
  simp only [transformedTables,HolographicTransport.tables,LinearEquiv.apply_symm_apply,
    nativeTables,GeneralFieldReduction.targetTables,
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables]
  exact congrFun (congrFun (Anchor.pulled_edge G A) b) c

/-- Every row includes the retained false pin. Every real edge, including
loops, contributes its own kappa; this is a whole-network proof. -/
theorem native_value (n : ℕ) (r : ExactSignatureTables.Input ((s+3)+n) 1 (arity G A)) :
    nativeValue G A n r=(Anchor.kappa G A)^r.val.edges.length*ordinaryValue G A n r := by
  change (nativeTables G A n).evaluate (Single.F G A) r=_
  rw [←HolographicTransport.value_eq (Single.F G A) (nativeTables G A n)
    (Anchor.inverse G A) (Anchor.matrix G A) (Anchor.inverse_matrix G A)]
  change (transformedTables G A n).evaluate (Single.F G A) r=_
  rw [ordinaryValue]
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [Network.denote,RawClosedNetwork.realize]
  simp_rw [transformed_vertex,transformed_edge]
  simp only [ordinaryTables,Companion.tables,LinearEquiv.apply_symm_apply,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change (∑z,_)=(Anchor.kappa G A)^r.val.edges.length*∑z,_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [RawClosedNetwork.shape]
  ring

/-- Arity alignment is identity on the entire raw record, not a restricted
compiler-image promise or a change of ordered ports. -/
def pairQuery := RawArityTransport.input (base_arity G A) (b:=1)
def pairQueryComputes := RawArityTransport.computes (base_arity G A) (b:=1)
theorem pair_query_raw (r : ExactSignatureTables.Input (s+3) 1 (arity G A)) :
    (pairQuery G A r).val=r.val := rfl
theorem base_ordinary_value (r : ExactSignatureTables.Input (s+3) 1 (arity G A)) :
    ordinaryValue G A 0 r=Pair.sourceValue (old G A) true (pairQuery G A r) := by
  rw [ordinaryValue,ExactSignatureTables.evaluate_eq_decoded]
  simp only [ordinaryTables,Companion.tables,LinearEquiv.apply_symm_apply]
  rw [←RawArityTransport.denote (base_arity G A) (ordinaryFamily G A 0)
    (fun _ : Fin 1 => Signature.equality) r,base_signatures]
  rfl

def pairTables := Companion.tables (Single.F G A) (pairFamily G A)
theorem pair_tables_value (r : ExactSignatureTables.Input (s+3) 1 (pairArity G A)) :
    (pairTables G A).evaluate (Single.F G A) r=Pair.sourceValue (old G A) true r := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [pairTables,Companion.tables,LinearEquiv.apply_symm_apply]
  rfl
def pairAnswerBound : PolynomialOutputBound (Pair.sourceEncoding (s+2) (oldArity G A))
    (Single.F G A).encoding (Pair.sourceValue (old G A) true) where
  bound := (pairTables G A).outputPolynomial (Single.F G A)
  length_le r := by
    have h := (pairTables G A).output_length_le (Single.F G A) r
    rw [pair_tables_value] at h
    exact h

def nativePairControlled : LengthControlledOracleReduction (internalEncoding G A 0)
    (Single.F G A).encoding (Pair.sourceEncoding (s+2) (oldArity G A)) (Single.F G A).encoding
    (nativeValue G A 0) (Pair.sourceValue (old G A) true) :=
  ControlledCap.controlledContextOfEq
    (pairComputes (pairQueryComputes G A) (Compiler.edgeCountComputes (s+3) 1 (arity G A)))
    (ScalarPower.correction (Single.F G A) (Anchor.kappa G A)⁻¹)
    (pairAnswerBound G A) (nativeValue G A 0) (fun r => by
      change nativeValue G A 0 r=Pair.sourceValue (old G A) true (pairQuery G A r)*
        ((Anchor.kappa G A)⁻¹)⁻¹^r.val.edges.length
      rw [native_value,base_ordinary_value,inv_inv]
      exact mul_comm _ _)

/-- The two finite physical callers see exactly old=Single.palette false.
Their old unary labels are passed through just like every other old label. -/
def pairPrefix := Pair.controlled (s+2) (oldArity G A) (Single.F G A)
  (old G A) (eq4Index (s:=s)) (old_eq4 G A) true
def companionPrefix := Companion.controlled (Single.F G A) (old G A)
  (eq4Index (s:=s)) (old_eq4 G A) true

/-- The actual second replication query, after the byte-identity arity
alignment. It keeps one true carrier even when its input has no pair row. -/
def replicationQuery (r : ExactSignatureTables.Input (s+3) 1 (arity G A)) :=
  Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.query
    (eq4Index (s:=s)) (congrArg Sigma.fst (old_eq4 G A)) (pairQuery G A r)
def replicationQueryComputes := (pairQueryComputes G A).andThen
  (Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.queryComputes
    (s+2) (oldArity G A) (eq4Index (s:=s)) (congrArg Sigma.fst (old_eq4 G A)))

theorem replication_scalar (r : ExactSignatureTables.Input (s+3) 1 (arity G A)) :
    QuaternaryOrdinaryCompanion.value (old G A)
      (QuaternaryOrdinaryCompanion.pair (old G A) true) (replicationQuery G A r)=
        QuaternaryOrdinaryCompanion.companion (old G A) true true*ordinaryValue G A 0 r := by
  rw [replicationQuery,
    Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.query_value
      (old G A) (eq4Index (s:=s)) (old_eq4 G A) true,
    ←base_ordinary_value]

theorem replication_one_carrier (r : ExactSignatureTables.Input (s+3) 1 (arity G A)) :
    FixedGadgetSubstitution.occurrences (s+2) (replicationQuery G A r).val=1 :=
  Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.one_carrier
    (eq4Index (s:=s)) (congrArg Sigma.fst (old_eq4 G A)) (pairQuery G A r)

/-- This is the executed row emitter. The first unary is an OLD row, so
its entire ordered endpoint list is copied verbatim, however often it occurs. -/
theorem replication_old_row (row : RawVertex) (h : row.1<s+2) (m t : ℕ) :
    Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.emitRow
      (s+2) s m t row=[row] := by
  simp only [Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.emitRow,
    if_neg (Nat.ne_of_lt h)]

theorem replication_old_edges (r : ExactSignatureTables.Input (s+3) 1 (arity G A)) :
    (replicationQuery G A r).val.edges.take r.val.edges.length=r.val.edges :=
  Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.raw_edge_prefix
    (s+2) s r.val

def pairAccess : PolyTimeOracleReduction (Pair.sourceEncoding (s+2) (oldArity G A))
    (Single.F G A).encoding (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
    (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
    (Pair.sourceValue (old G A) true) (QuaternaryAnchorAccess.GOT.originalValue G) :=
  (pairPrefix G A).compose ((companionPrefix G A).compose (Single.source G A false))

def factorQuery := GeneralFieldReduction.query (nativeFamily G A 0)
  (nativeTable G A (s+3)) (nextPower G A)
def factorQueryComputes := GeneralFieldReduction.queryComputes (nativeFamily G A 0)
  (nativeTable G A (s+3)) (nextPower G A)
def factorCorrection := GeneralFieldReduction.correctionComputes (Single.F G A)
  (nativeFamily G A 0) (nativeTable G A (s+3)) (nextPower G A)
def factorControlled : LengthControlledOracleReduction (internalEncoding G A 1) (Single.F G A).encoding
    (internalEncoding G A 0) (Single.F G A).encoding (nativeValue G A 1) (nativeValue G A 0) := by
  have R := RecursiveMachine.step (Single.F G A) (nativeTable G A (s+3)) (nextPower G A)
  rw [FactorSaturation.PrefixMachine.extension (s:=s+3) (nativeTable G A) 0] at R
  exact R

/-- The source-side return to ordinary coordinates counts its OWN edges;
the pair-side multiplication above counts the emitted factor query's edges. -/
def ordinaryControlled : LengthControlledOracleReduction (internalEncoding G A 1) (Single.F G A).encoding
    (internalEncoding G A 1) (Single.F G A).encoding (ordinaryValue G A 1) (nativeValue G A 1) :=
  ControlledCap.controlledContextOfEq
    (pairComputes (identityComputes (internalEncoding G A 1))
      (Compiler.edgeCountComputes ((s+3)+1) 1 (arity G A)))
    (ScalarPower.correction (Single.F G A) (Anchor.kappa G A))
    ((nativeTables G A 1).outputBound (Single.F G A)) (ordinaryValue G A 1)
    (fun r => by
      change ordinaryValue G A 1 r=nativeValue G A 1 r*(Anchor.kappa G A)⁻¹^r.val.edges.length
      rw [native_value,ScalarPower.cancel_scale_power _ _ (Anchor.kappa_ne G A)])

def internalAccess : PolyTimeOracleReduction (internalEncoding G A 1) (Single.F G A).encoding
    (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
    (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
    (ordinaryValue G A 1) (QuaternaryAnchorAccess.GOT.originalValue G) :=
  (ordinaryControlled G A).compose ((factorControlled G A).compose
    ((nativePairControlled G A).compose (pairAccess G A)))

theorem factor_query_length (r : ExactSignatureTables.Input ((s+3)+1) 1 (arity G A)) :
    ((internalEncoding G A 0).encode (factorQuery G A r)).length≤
      (factorQueryComputes G A).outputBound.bound.eval ((internalEncoding G A 1).encode r).length :=
  (factorQueryComputes G A).outputBound.length_le r
theorem factor_query_cost (r : ExactSignatureTables.Input ((s+3)+1) 1 (arity G A)) :
    primitiveCost (factorQueryComputes G A).machine ((factorQueryComputes G A).outputs r).steps
      (some (Turing.initList (factorQueryComputes G A).machine.computer
        ((internalEncoding G A 1).encode r)))≤
      (primitivePolynomial (factorQueryComputes G A)).eval ((internalEncoding G A 1).encode r).length :=
  computes_primitive_cost (factorQueryComputes G A) r

section OriginalL
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
variable {L : Type} [Field L] [NumberField L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (H : (i : Fin s) → Signature L (a i.val))
variable (B : QuaternaryEqualityTerminal.AnchorStep (FiniteFamily.family (OriginalLCodec.mapped φ H)))

def pairAccessOriginalL : PolyTimeOracleReduction
    (Pair.sourceEncoding (s+2) (oldArity (OriginalLCodec.mapped φ H) B))
    (Single.F (OriginalLCodec.mapped φ H) B).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (Pair.sourceValue (old (OriginalLCodec.mapped φ H) B) true) (OriginalLCodec.value H) :=
  (pairPrefix (OriginalLCodec.mapped φ H) B).compose
    ((companionPrefix (OriginalLCodec.mapped φ H) B).compose (Single.sourceOriginalL φ H B false))

def internalAccessOriginalL : PolyTimeOracleReduction
    (internalEncoding (OriginalLCodec.mapped φ H) B 1) (Single.F (OriginalLCodec.mapped φ H) B).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (ordinaryValue (OriginalLCodec.mapped φ H) B 1) (OriginalLCodec.value H) :=
  (ordinaryControlled (OriginalLCodec.mapped φ H) B).compose
    ((factorControlled (OriginalLCodec.mapped φ H) B).compose
      ((nativePairControlled (OriginalLCodec.mapped φ H) B).compose (pairAccessOriginalL φ H B)))
end OriginalL
end Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins
