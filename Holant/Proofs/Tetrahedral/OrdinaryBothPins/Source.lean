import Holant.Proofs.Tetrahedral.OrdinaryBothPins.Sequential
import Holant.Complexity.OracleBatch.QueryCount


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution UniversalPairReduction
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open scoped BigOperators

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (FiniteFamily.family G))
local instance : Algebra ℚ (Single.K G A) := (Single.K G A).algebra'
local instance : CharZero (Single.K G A) := Algebra.charZero_of_charZero ℚ (Single.K G A)

/-- All old indices and arities are literally the FIRST source's table.
The one new public slot is unary; the internal true-pair slot is skipped. -/
abbrev paletteArity := oldArity G A
def includeLabel (i : Fin (s+3)) : Fin ((s+3)+1) :=
  if hi : i.val<s+2 then ⟨i.val,by omega⟩ else ⟨i.val+1,by have := i.isLt; omega⟩
theorem include_arity (i : Fin (s+3)) :
    arity G A (includeLabel i).val=paletteArity G A i.val := by
  by_cases hi : i.val<s+2
  · simp [includeLabel,arity,pairArity,extendedArity,hi,
      show i.val<s+3 by omega,paletteArity]
  · have he : i.val=s+2 := by have := i.isLt; omega
    simp [includeLabel,arity,paletteArity,oldArity,Single.paletteArity,hi,he,
      show ¬s+2<s+1 by omega]
def palette (i : Fin (s+3)) : Signature (Single.K G A) (paletteArity G A i.val) :=
  fun x => ordinaryFamily G A 1 (includeLabel i)
    (fun k => x (Fin.cast (include_arity G A i) k))
def tables := Companion.tables (Single.F G A) (palette G A)
abbrev value := (tables G A).evaluate (Single.F G A)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+3) 1 (paletteArity G A)
abbrev Input := ExactSignatureTables.Input (s+3) 1 (paletteArity G A)

private theorem signature_cast_sigma {K : Type} {m n : ℕ} (h : m=n) (f : Signature K m) :
    (⟨n,fun x => f (fun k => x (Fin.cast h k))⟩ : AnySignature K)=⟨m,f⟩ := by
  subst n
  rfl

theorem palette_lift (i : Fin (s+3)) :
    (⟨paletteArity G A i.val,palette G A i⟩ : AnySignature (Single.K G A))=
      ⟨arity G A (includeLabel i).val,ordinaryFamily G A 1 (includeLabel i)⟩ :=
  signature_cast_sigma (include_arity G A i) (ordinaryFamily G A 1 (includeLabel i))

/-- Complete old table alignment, INCLUDING the first pin, rather than
an equality only on original RG rows or on a restricted query image. -/
theorem palette_old (i : Fin (s+2)) :
    (⟨paletteArity G A i.val,palette G A ⟨i.val,by have := i.isLt; omega⟩⟩ :
      AnySignature (Single.K G A))=⟨oldArity G A i.val,old G A i⟩ := by
  apply (palette_lift G A ⟨i.val,by have := i.isLt; omega⟩).trans
  have hi : includeLabel (⟨i.val,by have := i.isLt; omega⟩ : Fin (s+3))=
      (⟨i.val,by have := i.isLt; omega⟩ : Fin ((s+3)+1)) := by
    simp [includeLabel,i.isLt]
  rw [hi]
  exact base_old G A i

theorem palette_first_pin :
    (⟨paletteArity G A (s+1),palette G A ⟨s+1,by omega⟩⟩ :
      AnySignature (Single.K G A))=⟨1,Single.pin G A false⟩ :=
  (palette_old G A ⟨s+1,by omega⟩).trans (Single.palette_pin G A false)

theorem palette_second_pin :
    (⟨paletteArity G A (s+2),palette G A ⟨s+2,by omega⟩⟩ :
      AnySignature (Single.K G A))=⟨1,Single.pin G A true⟩ := by
  apply (palette_lift G A ⟨s+2,by omega⟩).trans
  have hi : includeLabel (⟨s+2,by omega⟩ : Fin (s+3))=
      (⟨s+3,by omega⟩ : Fin ((s+3)+1)) := by
    simp [includeLabel]
  rw [hi]
  exact ordinary_next_label G A

theorem palette_original (i : Fin (s+1)) :
    (⟨paletteArity G A i.val,palette G A ⟨i.val,by have := i.isLt; omega⟩⟩ :
      AnySignature (Single.K G A))=⟨Anchor.arity G A i.val,Companion.decoded G A i⟩ :=
  (palette_old G A ⟨i.val,by have := i.isLt; omega⟩).trans (Single.palette_old G A false i)

theorem palette_family :
    Set.range (fun i : Fin (s+3) =>
      (⟨paletteArity G A i.val,palette G A i⟩ : AnySignature (Single.K G A)))=
      Set.range (fun i : Fin (s+2) =>
        (⟨oldArity G A i.val,old G A i⟩ : AnySignature (Single.K G A))) ∪
          {⟨1,Single.pin G A true⟩} := by
  ext f
  simp only [Set.mem_union,Set.mem_range,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<s+2
    · exact Or.inl ⟨⟨i.val,hi⟩,(palette_old G A ⟨i.val,hi⟩).symm⟩
    · have he : i=⟨s+2,by omega⟩ := Fin.ext (by change i.val=s+2; have := i.isLt; omega)
      exact Or.inr (by rw [he]; exact palette_second_pin G A)
  · rintro (⟨i,rfl⟩|rfl)
    · exact ⟨⟨i.val,by have := i.isLt; omega⟩,palette_old G A i⟩
    · exact ⟨⟨s+2,by omega⟩,palette_second_pin G A⟩

theorem palette_family_exact :
    Set.range (fun i : Fin (s+3) =>
      (⟨paletteArity G A i.val,palette G A i⟩ : AnySignature (Single.K G A)))=
      (Set.range (fun i : Fin (s+1) =>
        (⟨Anchor.arity G A i.val,Companion.decoded G A i⟩ : AnySignature (Single.K G A))) ∪
          {⟨1,Single.pin G A false⟩}) ∪ {⟨1,Single.pin G A true⟩} := by
  rw [palette_family]
  rw [show Set.range (fun i : Fin (s+2) =>
      (⟨oldArity G A i.val,old G A i⟩ : AnySignature (Single.K G A)))=_ from
    Single.palette_family G A false]

/-- The original common R and its coefficient embedding, with BOTH
literal pins. This semantic embedding does not make R a physical binary. -/
theorem palette_ambient :
    Set.range (fun i : Fin (s+3) => RingHomRealization.mapAny (Single.K G A).subtype
      (⟨paletteArity G A i.val,palette G A i⟩ : AnySignature (Single.K G A)))=
      ((familyAction A.basis (FiniteFamily.family G) ∪
        {⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩}) ∪
          {⟨1,QuaternaryUnaryAccess.pin (K:=AlgebraicComplex) false⟩}) ∪
            {⟨1,QuaternaryUnaryAccess.pin (K:=AlgebraicComplex) true⟩} := by
  have hp : RingHomRealization.mapAny (Single.K G A).subtype
      (⟨1,Single.pin G A true⟩ : AnySignature (Single.K G A))=
        ⟨1,QuaternaryUnaryAccess.pin (K:=AlgebraicComplex) true⟩ := by
    change (⟨1,RingHomRealization.mapSignature (Single.K G A).subtype
      (Single.pin G A true)⟩ : AnySignature AlgebraicComplex)=_
    apply congrArg (fun f : Signature AlgebraicComplex 1 => (⟨1,f⟩ : AnySignature AlgebraicComplex))
    funext x
    simp [RingHomRealization.mapAny,RingHomRealization.mapSignature,
      Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess.pin,
      QuaternaryUnaryAccess.pin,apply_ite]
  rw [Set.range_comp',palette_family,Set.image_union,Set.image_singleton,
    ←Set.range_comp',hp]
  rw [show Set.range (fun i : Fin (s+2) => RingHomRealization.mapAny (Single.K G A).subtype
      (⟨oldArity G A i.val,old G A i⟩ : AnySignature (Single.K G A)))=_ from
    Single.palette_ambient G A false]

def query := CanonicalFamily.Relabel.input (includeLabel (s:=s)) (include_arity G A)
def queryComputes := CanonicalFamily.Relabel.computes (includeLabel (s:=s)) (include_arity G A)
theorem query_ports (r : Input G A) :
    (query G A r).val.vertices.map Prod.snd=r.val.vertices.map Prod.snd :=
  CanonicalFamily.Relabel.ordered_ports (includeLabel (s:=s)) r.val
theorem query_edges (r : Input G A) : (query G A r).val.edges=r.val.edges := rfl
theorem query_vertices (r : Input G A) :
    (query G A r).val.vertices.length=r.val.vertices.length :=
  CanonicalFamily.Relabel.vertices_length (includeLabel (s:=s)) r.val

/-- Whole partition equality for an arbitrary validated two-pin input.
The real finite relabel changes only the last pin's label, never its port. -/
theorem query_value (r : Input G A) : value G A r=ordinaryValue G A 1 (query G A r) := by
  rw [value,ordinaryValue,ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [tables,ordinaryTables,Companion.tables,LinearEquiv.apply_symm_apply]
  rw [Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.EqChoice.denote_eq_evaluate,
    Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.EqChoice.denote_eq_evaluate]
  unfold Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.EqChoice.evaluate
  apply Finset.sum_congr rfl
  intro z _
  unfold Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.EqChoice.weight
  change (r.val.vertices.map _).prod=
    ((r.val.vertices.map (CanonicalFamily.Relabel.row (includeLabel (s:=s)))).map _).prod
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro row hr
  have hi := (((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property).1 row hr).1
  have ht := (includeLabel (⟨row.1,hi⟩ : Fin (s+3))).isLt
  have hrow : CanonicalFamily.Relabel.row (includeLabel (s:=s)) row=
      ((includeLabel ⟨row.1,hi⟩).val,row.2) := by
    simp [CanonicalFamily.Relabel.row,CanonicalFamily.Relabel.label,hi]
  simp only [Function.comp_apply]
  rw [hrow]
  simp only [Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.EqChoice.rowValue,
    UniversalPairReduction.Surgery.Choice.table,dif_pos hi,dif_pos ht,palette,Fin.val_cast]

def paletteControlled : LengthControlledOracleReduction (inputEncoding G A) (Single.F G A).encoding
    (internalEncoding G A 1) (Single.F G A).encoding (value G A) (ordinaryValue G A 1) :=
  controlledOneQueryOfEq (queryComputes G A) (identityComputes (Single.F G A).encoding)
    ((ordinaryTables G A 1).outputBound (Single.F G A)) (value G A) (query_value G A)

abbrev Access := PolyTimeOracleReduction (inputEncoding G A) (Single.F G A).encoding
    (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
    (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
    (value G A) (QuaternaryAnchorAccess.GOT.originalValue G)

/-- SOLE algebraic-complex public source: one machine for arbitrary mixed
e0/e1 occurrence patterns, with the first source inside the second caller. -/
def top : Access G A := (paletteControlled G A).compose (internalAccess G A)
def outputBound : PolynomialOutputBound (inputEncoding G A) (Single.F G A).encoding (value G A) :=
  (tables G A).outputBound (Single.F G A)
theorem query_bit_bound (r : Input G A) :
    ((internalEncoding G A 1).encode (query G A r)).length≤
      (queryComputes G A).outputBound.bound.eval ((inputEncoding G A).encode r).length :=
  (queryComputes G A).outputBound.length_le r
theorem query_primitive_cost (r : Input G A) :
    primitiveCost (queryComputes G A).machine ((queryComputes G A).outputs r).steps
      (some (Turing.initList (queryComputes G A).machine.computer ((inputEncoding G A).encode r)))≤
      (primitivePolynomial (queryComputes G A)).eval ((inputEncoding G A).encode r).length :=
  computes_primitive_cost (queryComputes G A) r

private theorem query_count_le (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (n : ℕ) : UniversalPairReduction.ThreeQuery.queryCount m oracle c n≤n := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    change (match m.step oracle c with
      | none => 0
      | some d => UniversalPairReduction.ThreeQuery.queryCost m c+
          UniversalPairReduction.ThreeQuery.queryCount m oracle d n)≤n+1
    cases hs : m.step oracle c with
    | none => exact Nat.zero_le _
    | some d =>
      have hq : UniversalPairReduction.ThreeQuery.queryCost m c≤1 := by
        unfold UniversalPairReduction.ThreeQuery.queryCost
        cases c.l with
        | none => exact Nat.zero_le _
        | some l => cases hp : m.program l <;> simp [hp]
      exact (Nat.add_le_add hq (ih d)).trans (by omega)

theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
      (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
      (QuaternaryAnchorAccess.GOT.originalValue G) oracle) (r : Input G A) :
    ∃t≤(top G A).time.eval ((inputEncoding G A).encode r).length,
      (fun c => c.bind ((top G A).machine.step oracle))^[t]
        (some ((top G A).machine.init ((inputEncoding G A).encode r)))=
        some ((top G A).machine.output ((Single.F G A).encoding.encode (value G A r))) ∧
      OracleBatch.primitiveCount (top G A).machine oracle
        ((top G A).machine.init ((inputEncoding G A).encode r)) t≤
        (top G A).machine.primitiveBudget*(top G A).time.eval ((inputEncoding G A).encode r).length ∧
      UniversalPairReduction.ThreeQuery.queryCount (top G A).machine oracle
        ((top G A).machine.init ((inputEncoding G A).encode r)) t≤
        (top G A).time.eval ((inputEncoding G A).encode r).length := by
  let run := (top G A).correct oracle ho r
  refine ⟨run.steps,run.steps_le_m,run.evals_in_steps,?_,?_⟩
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans
      (Nat.mul_le_mul_left (top G A).machine.primitiveBudget run.steps_le_m)
  · exact (query_count_le _ _ _ _).trans run.steps_le_m

section OriginalL
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
variable {L : Type} [Field L] [NumberField L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (H : (i : Fin s) → Signature L (a i.val))
variable (B : QuaternaryEqualityTerminal.AnchorStep (FiniteFamily.family (OriginalLCodec.mapped φ H)))

/-- SAME original H table, raw input codec and L answer codec. No factor
of R is treated as an L-valued physical binary and no descent is assumed. -/
def topOriginalL : PolyTimeOracleReduction
    (inputEncoding (OriginalLCodec.mapped φ H) B) (Single.F (OriginalLCodec.mapped φ H) B).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (value (OriginalLCodec.mapped φ H) B) (OriginalLCodec.value H) :=
  (paletteControlled (OriginalLCodec.mapped φ H) B).compose (internalAccessOriginalL φ H B)

theorem executionOriginalL (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 a)
      (OriginalLCodec.presentation (L:=L)).encoding (OriginalLCodec.value H) oracle)
    (r : Input (OriginalLCodec.mapped φ H) B) :
    ∃t≤(topOriginalL φ H B).time.eval
        ((inputEncoding (OriginalLCodec.mapped φ H) B).encode r).length,
      (fun c => c.bind ((topOriginalL φ H B).machine.step oracle))^[t]
        (some ((topOriginalL φ H B).machine.init
          ((inputEncoding (OriginalLCodec.mapped φ H) B).encode r)))=
        some ((topOriginalL φ H B).machine.output
          ((Single.F (OriginalLCodec.mapped φ H) B).encoding.encode
            (value (OriginalLCodec.mapped φ H) B r))) ∧
      OracleBatch.primitiveCount (topOriginalL φ H B).machine oracle
        ((topOriginalL φ H B).machine.init
        ((inputEncoding (OriginalLCodec.mapped φ H) B).encode r)) t≤
        (topOriginalL φ H B).machine.primitiveBudget*(topOriginalL φ H B).time.eval
          ((inputEncoding (OriginalLCodec.mapped φ H) B).encode r).length ∧
      UniversalPairReduction.ThreeQuery.queryCount (topOriginalL φ H B).machine oracle
        ((topOriginalL φ H B).machine.init
          ((inputEncoding (OriginalLCodec.mapped φ H) B).encode r)) t≤
        (topOriginalL φ H B).time.eval ((inputEncoding (OriginalLCodec.mapped φ H) B).encode r).length := by
  let run := (topOriginalL φ H B).correct oracle ho r
  refine ⟨run.steps,run.steps_le_m,run.evals_in_steps,?_,?_⟩
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans
      (Nat.mul_le_mul_left (topOriginalL φ H B).machine.primitiveBudget run.steps_le_m)
  · exact (query_count_le _ _ _ _).trans run.steps_le_m
end OriginalL
end Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
