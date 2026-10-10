import Holant.Proofs.Tetrahedral.OrdinaryUnaryAccess.Coordinates
import Holant.Proofs.Reductions.CanonicalFamily.Semantics
import Holant.Proofs.Algorithms.RawArityTransport


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution UniversalPairReduction
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (FiniteFamily.family G))
local instance : Algebra ℚ (K G A) := (K G A).algebra'
local instance : CharZero (K G A) := Algebra.charZero_of_charZero ℚ (K G A)
variable (j : Bool)

abbrev encoding (n : ℕ) := RawClosedNetwork.validatedEncoding ((s+2)+n) 1 (arity G A)
def nativeTables (n : ℕ) := GeneralFieldReduction.targetTables (F G A) (family G A j n)
def ordinaryTables (n : ℕ) := QuaternaryOrdinaryCompanion.tables (F G A) (ordinaryFamily G A j n)
abbrev nativeValue (n : ℕ) := (nativeTables G A j n).evaluate (F G A)
abbrev ordinaryValue (n : ℕ) := (ordinaryTables G A j n).evaluate (F G A)

def transformedTables (n : ℕ) := HolographicTransport.tables (F G A) (nativeTables G A j n)
  (Anchor.inverse G A) (Anchor.matrix G A)

theorem transformed_vertex (n : ℕ) (i : Fin ((s+2)+n)) (x : Fin (arity G A i.val) → Bool) :
    (F G A).decode ((transformedTables G A j n).vertex i x)=ordinaryFamily G A j n i x := by
  simp only [transformedTables,HolographicTransport.tables,LinearEquiv.apply_symm_apply]
  change Signature.coordinateAction (fun _ => Anchor.matrix G A)
    (fun y => (F G A).decode ((nativeTables G A j n).vertex i y)) x=_
  simp only [nativeTables,GeneralFieldReduction.targetTables,FieldReduction.targetTables,
    LinearEquiv.apply_symm_apply,family,FactorSaturation.PrefixMachine.family]
  exact congrFun (forward G A j i.val) x

theorem transformed_edge (n : ℕ) (i : Fin 1) (b c : Bool) :
    (F G A).decode ((transformedTables G A j n).edge i b c)=
      Anchor.kappa G A*Signature.equality b c := by
  simp only [transformedTables,HolographicTransport.tables,LinearEquiv.apply_symm_apply,
    nativeTables,GeneralFieldReduction.targetTables,FieldReduction.targetTables]
  exact congrFun (congrFun (Anchor.pulled_edge G A) b) c

/-- Extension of the already delivered holographic transport to the SAME
pair/unary table. All individual edges, including loops, contribute κ. -/
theorem native_value (n : ℕ) (r : ExactSignatureTables.Input ((s+2)+n) 1 (arity G A)) :
    nativeValue G A j n r=(Anchor.kappa G A)^r.val.edges.length*ordinaryValue G A j n r := by
  change (nativeTables G A j n).evaluate (F G A) r=_
  rw [←HolographicTransport.value_eq (F G A) (nativeTables G A j n)
    (Anchor.inverse G A) (Anchor.matrix G A) (Anchor.inverse_matrix G A)]
  change (transformedTables G A j n).evaluate (F G A) r=_
  rw [ordinaryValue]
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [Network.denote,RawClosedNetwork.realize]
  simp_rw [transformed_vertex,transformed_edge]
  simp only [ordinaryTables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change (∑z,_)=(Anchor.kappa G A)^r.val.edges.length*∑z,_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [RawClosedNetwork.shape]
  ring

def pairQuery := RawArityTransport.input (base_arity G A) (b:=1)
def pairQueryComputes := RawArityTransport.computes (base_arity G A) (b:=1)
theorem pairQuery_raw (r : ExactSignatureTables.Input (s+2) 1 (arity G A)) :
    (pairQuery G A r).val=r.val := rfl

theorem base_signatures :
    RawArityTransport.signatures (base_arity G A) (ordinaryFamily G A j 0)=originalPair G A j := by
  funext i x
  simp [RawArityTransport.signatures,ordinaryFamily,FactorSaturation.PrefixMachine.family,
    ordinaryTable,i.isLt]

theorem base_ordinary_value (r : ExactSignatureTables.Input (s+2) 1 (arity G A)) :
    ordinaryValue G A j 0 r=Pair.anchorValue s a G A j (pairQuery G A r) := by
  rw [ordinaryValue,ExactSignatureTables.evaluate_eq_decoded]
  simp only [ordinaryTables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  rw [←RawArityTransport.denote (base_arity G A) (ordinaryFamily G A j 0)
    (fun _ : Fin 1 => Signature.equality) r,base_signatures]
  rfl

def pairTables := QuaternaryOrdinaryCompanion.tables (F G A) (originalPair G A j)
theorem pair_tables_value (r : ExactSignatureTables.Input (s+2) 1 (pairArity G A)) :
    (pairTables G A j).evaluate (F G A) r=Pair.anchorValue s a G A j r := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [pairTables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  rfl
def pairAnswerBound : PolynomialOutputBound (Pair.anchorInputEncoding s a G A) (F G A).encoding
    (Pair.anchorValue s a G A j) where
  bound := (pairTables G A j).outputPolynomial (F G A)
  length_le r := by
    have h := (pairTables G A j).output_length_le (F G A) r
    rw [pair_tables_value] at h
    exact h

/-- A native pair-base query goes to the SAME ordinary raw query. The
answer multiplies κ^E; ScalarPower.correction(κ^{-1}) executes this exactly. -/
def pairControlled : LengthControlledOracleReduction (encoding G A 0) (F G A).encoding
    (Pair.anchorInputEncoding s a G A) (F G A).encoding
    (nativeValue G A j 0) (Pair.anchorValue s a G A j) :=
  ControlledCap.controlledContextOfEq
    (pairComputes (pairQueryComputes G A) (Compiler.edgeCountComputes (s+2) 1 (arity G A)))
    (ScalarPower.correction (F G A) (Anchor.kappa G A)⁻¹)
    (pairAnswerBound G A j) (nativeValue G A j 0) (fun r => by
      change nativeValue G A j 0 r=Pair.anchorValue s a G A j (pairQuery G A r)*
        ((Anchor.kappa G A)⁻¹)⁻¹^r.val.edges.length
      rw [native_value,base_ordinary_value,inv_inv]
      exact mul_comm _ _)

def baseAccess : PolyTimeOracleReduction (encoding G A 0) (F G A).encoding
    (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
    (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
    (nativeValue G A j 0) (QuaternaryAnchorAccess.GOT.originalValue G) :=
  (pairControlled G A j).compose (Pair.access s a G A j)

/-- Actual one-step factor interpreter. Power exponent, residue anchors,
macro scale and its original-label expansion are internally produced. -/
def nativeAccess : PolyTimeOracleReduction (encoding G A 1) (F G A).encoding
    (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
    (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
    (nativeValue G A j 1) (QuaternaryAnchorAccess.GOT.originalValue G) :=
  FactorSaturation.PrefixMachine.withTerminal (nativeTable G A j) (F G A)
    (baseAccess G A j) (chain G A j)

/-- The concrete factor-side query producer; it is not an existential
gadget/source wrapper. Dead residue classes retain the old zero-answer path. -/
def factorQuery := GeneralFieldReduction.query (family G A j 0)
  (nativeTable G A j (s+2)) (nextPower G A j 0)
def factorQueryComputes := GeneralFieldReduction.queryComputes (family G A j 0)
  (nativeTable G A j (s+2)) (nextPower G A j 0)
def factorCorrection := GeneralFieldReduction.correctionComputes (F G A) (family G A j 0)
  (nativeTable G A j (s+2)) (nextPower G A j 0)

/-- The actual controlled local factor program, before its pair terminal is
installed. The stored prefix extension is a literal equality of tables. -/
def factorControlled : LengthControlledOracleReduction (encoding G A 1) (F G A).encoding
    (encoding G A 0) (F G A).encoding (nativeValue G A j 1) (nativeValue G A j 0) := by
  have R := RecursiveMachine.step (F G A) (nativeTable G A j (s+2)) (nextPower G A j 0)
  rw [FactorSaturation.PrefixMachine.extension (s:=s+2) (nativeTable G A j) 0] at R
  exact R

def factorQueryBound := GeneralFieldReduction.queryPolynomial (family G A j 0)
  (nativeTable G A j (s+2)) (nextPower G A j 0)
def factorAnswerBound := GeneralFieldReduction.answerPolynomial (F G A) (family G A j 0)
  (nativeTable G A j (s+2)) (nextPower G A j 0)

theorem factor_query_length (r : ExactSignatureTables.Input ((s+2)+1) 1 (arity G A)) :
    ((encoding G A 0).encode (factorQuery G A j r)).length≤
      (factorQueryBound G A j).eval ((encoding G A 1).encode r).length :=
  GeneralFieldReduction.query_length (family G A j 0)
    (nativeTable G A j (s+2)) (nextPower G A j 0) r

theorem factor_answer_length (r : ExactSignatureTables.Input ((s+2)+1) 1 (arity G A)) :
    ((F G A).encoding.encode (nativeValue G A j 0 (factorQuery G A j r))).length≤
      (factorAnswerBound G A j).eval ((encoding G A 1).encode r).length :=
  GeneralFieldReduction.answer_length (F G A) (family G A j 0)
    (nativeTable G A j (s+2)) (nextPower G A j 0) r

/-- Actual Boolean-stack instruction cost, independently of the emitted
query's length bound. The grouping/anchor/macro compiler is reused intact. -/
theorem factor_query_runtime (r : ExactSignatureTables.Input ((s+2)+1) 1 (arity G A)) :
    primitiveCost (factorQueryComputes G A j).machine ((factorQueryComputes G A j).outputs r).steps
      (some (Turing.initList (factorQueryComputes G A j).machine.computer
        ((encoding G A 1).encode r)))≤
      (primitivePolynomial (factorQueryComputes G A j)).eval ((encoding G A 1).encode r).length :=
  computes_primitive_cost (factorQueryComputes G A j) r

/-- Return to ordinary coordinates after the actual unary was extracted.
Here the correction is κ^{-E}, on THIS source query's edge count. -/
def ordinaryControlled : LengthControlledOracleReduction (encoding G A 1) (F G A).encoding
    (encoding G A 1) (F G A).encoding (ordinaryValue G A j 1) (nativeValue G A j 1) :=
  ControlledCap.controlledContextOfEq
    (pairComputes (identityComputes (encoding G A 1))
      (Compiler.edgeCountComputes ((s+2)+1) 1 (arity G A)))
    (ScalarPower.correction (F G A) (Anchor.kappa G A))
    ((nativeTables G A j 1).outputBound (F G A)) (ordinaryValue G A j 1)
    (fun r => by
      change ordinaryValue G A j 1 r=nativeValue G A j 1 r*(Anchor.kappa G A)⁻¹^r.val.edges.length
      rw [native_value,ScalarPower.cancel_scale_power _ _ (Anchor.kappa_ne G A)])

/-- USER source palette: the original ordinary RG+Eq4 table plus one
literal e_j. The pair slot is INTERNAL and is absent from this palette. -/
def paletteArity (i : ℕ) : ℕ := if i<s+1 then Anchor.arity G A i else 1
def includeLabel (i : Fin (s+2)) : Fin ((s+2)+1) :=
  if hi : i.val<s+1 then ⟨i.val,by omega⟩ else ⟨i.val+1,by have := i.isLt; omega⟩
theorem include_arity (i : Fin (s+2)) :
    arity G A (includeLabel i).val=paletteArity G A i.val := by
  by_cases hi : i.val<s+1
  · simp [includeLabel,arity,pairArity,extendedArity,paletteArity,hi,show i.val<s+2 by omega]
  · have he : i.val=s+1 := by have := i.isLt; omega
    simp [includeLabel,arity,paletteArity,hi,he]
def palette (i : Fin (s+2)) : Signature (K G A) (paletteArity G A i.val) :=
  fun x => ordinaryFamily G A j 1 (includeLabel i) (fun k => x (Fin.cast (include_arity G A i) k))
def paletteTables := QuaternaryOrdinaryCompanion.tables (F G A) (palette G A j)
abbrev value := (paletteTables G A j).evaluate (F G A)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+2) 1 (paletteArity G A)

private theorem signature_cast_sigma {K : Type*} {m n : ℕ} (h : m=n)
    (f : Signature K m) :
    (⟨n,fun x => f (fun k => x (Fin.cast h k))⟩ : AnySignature K)=⟨m,f⟩ := by
  subst n
  rfl

theorem palette_lift (i : Fin (s+2)) :
    (⟨paletteArity G A i.val,palette G A j i⟩ : AnySignature (K G A))=
      ⟨arity G A (includeLabel i).val,ordinaryFamily G A j 1 (includeLabel i)⟩ :=
  signature_cast_sigma (include_arity G A i) (ordinaryFamily G A j 1 (includeLabel i))

theorem ordinary_old_label (i : Fin (s+1)) :
    (⟨arity G A i.val,ordinaryTable G A j i.val⟩ : AnySignature (K G A))=
      ⟨Anchor.arity G A i.val,Companion.decoded G A i⟩ := by
  have hi : i.val<s+2 := by have := i.isLt; omega
  simp only [ordinaryTable,dif_pos hi]
  apply (signature_cast_sigma (base_arity G A ⟨i.val,hi⟩).symm
    (originalPair G A j ⟨i.val,hi⟩)).trans
  unfold originalPair BinaryFamily.signatures
  simp only [Fin.val_mk,dif_pos i.isLt]
  exact signature_cast_sigma (m:=Anchor.arity G A i.val) (n:=pairArity G A i.val)
    (by simp [pairArity,extendedArity,i.isLt]) (Companion.decoded G A i)

theorem palette_old (i : Fin (s+1)) :
    (⟨paletteArity G A i.val,palette G A j ⟨i.val,by have := i.isLt; omega⟩⟩ : AnySignature (K G A))=
      ⟨Anchor.arity G A i.val,Companion.decoded G A i⟩ := by
  apply (palette_lift G A j ⟨i.val,by have := i.isLt; omega⟩).trans
  have hi : includeLabel (⟨i.val,by have := i.isLt; omega⟩ : Fin (s+2))=
      (⟨i.val,by have := i.isLt; omega⟩ : Fin ((s+2)+1)) := by
    simp [includeLabel,i.isLt]
  rw [hi]
  exact ordinary_old_label G A j i

theorem palette_pin :
    (⟨paletteArity G A (s+1),palette G A j ⟨s+1,by omega⟩⟩ : AnySignature (K G A))=
      ⟨1,pin G A j⟩ := by
  apply (palette_lift G A j ⟨s+1,by omega⟩).trans
  have hi : includeLabel (⟨s+1,by omega⟩ : Fin (s+2))=
      (⟨s+2,by omega⟩ : Fin ((s+2)+1)) := by
    simp [includeLabel]
  rw [hi]
  exact ordinary_next_label G A j

theorem pin_nonzero : pin G A j≠0 := by
  intro h
  have hh := congrFun h (fun _ => j)
  simp [pin] at hh

/-- Exact public family: all old ordinary labels and this SINGLE literal
unary. The accessible pair remains an internal query alphabet only. -/
theorem palette_family :
    Set.range (fun i : Fin (s+2) =>
      (⟨paletteArity G A i.val,palette G A j i⟩ : AnySignature (K G A)))=
    Set.range (fun i : Fin (s+1) =>
      (⟨Anchor.arity G A i.val,Companion.decoded G A i⟩ : AnySignature (K G A))) ∪
      {⟨1,pin G A j⟩} := by
  ext f
  simp only [Set.mem_union,Set.mem_range,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<s+1
    · exact Or.inl ⟨⟨i.val,hi⟩,(palette_old G A j ⟨i.val,hi⟩).symm⟩
    · have he : i=⟨s+1,by omega⟩ := Fin.ext (by change i.val=s+1; have := i.isLt; omega)
      exact Or.inr (by rw [he]; exact palette_pin G A j)
  · rintro (⟨i,rfl⟩|rfl)
    · exact ⟨⟨i.val,by have := i.isLt; omega⟩,palette_old G A j i⟩
    · exact ⟨⟨s+1,by omega⟩,palette_pin G A j⟩

/-- The SAME actual common R is used on the whole original family. This
semantic embedding is not a new coefficient codec or a physical R gadget. -/
theorem palette_ambient :
    Set.range (fun i : Fin (s+2) => RingHomRealization.mapAny (K G A).subtype
      (⟨paletteArity G A i.val,palette G A j i⟩ : AnySignature (K G A)))=
    (familyAction A.basis (FiniteFamily.family G) ∪
      {⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩}) ∪
      {⟨1,QuaternaryUnaryAccess.pin (K:=AlgebraicComplex) j⟩} := by
  have hold : Set.range (fun i : Fin (s+1) => RingHomRealization.mapAny (K G A).subtype
      (⟨Anchor.arity G A i.val,Companion.decoded G A i⟩ : AnySignature (K G A)))=
      familyAction A.basis (FiniteFamily.family G) ∪
        {⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩} := by
    change Set.range (fun i : Fin (s+1) =>
      (⟨Anchor.arity G A i.val,fun x =>
        (((QuaternaryAnchorAccess.presentation G A).decode
          ((QuaternaryAnchorAccess.tables G A).vertex i x) : K G A) : AlgebraicComplex)⟩ :
            AnySignature AlgebraicComplex))=_
    exact QuaternaryAnchorAccess.family_exact G A
  have hp : RingHomRealization.mapAny (K G A).subtype
      (⟨1,pin G A j⟩ : AnySignature (K G A))=
      ⟨1,QuaternaryUnaryAccess.pin (K:=AlgebraicComplex) j⟩ := by
    change (⟨1,RingHomRealization.mapSignature (K G A).subtype (pin G A j)⟩ :
      AnySignature AlgebraicComplex)=_
    apply congrArg (fun f : Signature AlgebraicComplex 1 => (⟨1,f⟩ : AnySignature AlgebraicComplex))
    funext x
    simp [RingHomRealization.mapAny,RingHomRealization.mapSignature,
      pin,QuaternaryUnaryAccess.pin,apply_ite]
  rw [Set.range_comp',palette_family,Set.image_union,Set.image_singleton,
    ←Set.range_comp',hold,hp]

def paletteQuery := CanonicalFamily.Relabel.input (includeLabel (s:=s)) (include_arity G A)
def paletteQueryComputes := CanonicalFamily.Relabel.computes (includeLabel (s:=s)) (include_arity G A)
theorem palette_query_ports (r : ExactSignatureTables.Input (s+2) 1 (paletteArity G A)) :
    (paletteQuery G A r).val.vertices.map Prod.snd=r.val.vertices.map Prod.snd :=
  CanonicalFamily.Relabel.ordered_ports (includeLabel (s:=s)) r.val
theorem palette_query_edges (r : ExactSignatureTables.Input (s+2) 1 (paletteArity G A)) :
    (paletteQuery G A r).val.edges=r.val.edges := rfl
theorem palette_query_vertices (r : ExactSignatureTables.Input (s+2) 1 (paletteArity G A)) :
    (paletteQuery G A r).val.vertices.length=r.val.vertices.length :=
  CanonicalFamily.Relabel.vertices_length (includeLabel (s:=s)) r.val

theorem palette_value (r : ExactSignatureTables.Input (s+2) 1 (paletteArity G A)) :
    value G A j r=ordinaryValue G A j 1 (paletteQuery G A r) := by
  rw [value,ordinaryValue,ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [paletteTables,ordinaryTables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
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
  have ht := (includeLabel (⟨row.1,hi⟩ : Fin (s+2))).isLt
  have hrow : CanonicalFamily.Relabel.row (includeLabel (s:=s)) row=
      ((includeLabel ⟨row.1,hi⟩).val,row.2) := by
    simp [CanonicalFamily.Relabel.row,CanonicalFamily.Relabel.label,hi]
  simp only [Function.comp_apply]
  rw [hrow]
  simp only [Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.EqChoice.rowValue,
    UniversalPairReduction.Surgery.Choice.table,dif_pos hi,dif_pos ht,palette,Fin.val_cast]

def paletteControlled : LengthControlledOracleReduction (inputEncoding G A) (F G A).encoding
    (encoding G A 1) (F G A).encoding (value G A j) (ordinaryValue G A j 1) :=
  controlledOneQueryOfEq (paletteQueryComputes G A) (identityComputes (F G A).encoding)
    ((ordinaryTables G A j 1).outputBound (F G A)) (value G A j) (palette_value G A j)

abbrev Access := PolyTimeOracleReduction (inputEncoding G A) (F G A).encoding
    (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
    (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
    (value G A j) (QuaternaryAnchorAccess.GOT.originalValue G)

/-- Single public entry: internally derive the unary macro, execute its
controlled prefix, and terminate in the ACTUAL original-G pair access. -/
def source : Access G A j :=
  (paletteControlled G A j).compose ((ordinaryControlled G A j).compose (nativeAccess G A j))

def execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
      (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
      (QuaternaryAnchorAccess.GOT.originalValue G) oracle)
    (r : ExactSignatureTables.Input (s+2) 1 (paletteArity G A)) :=
  (source G A j).correct oracle ho r

/-- Source answer length is derived from its ACTUAL ordinary table. The
reduction's runtime is supplied separately by its constructed inlined machine. -/
def outputBound : PolynomialOutputBound (inputEncoding G A) (F G A).encoding (value G A j) :=
  (paletteTables G A j).outputBound (F G A)

theorem source_run_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
      (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
      (QuaternaryAnchorAccess.GOT.originalValue G) oracle)
    (r : ExactSignatureTables.Input (s+2) 1 (paletteArity G A)) :
    ∃ t≤(source G A j).time.eval ((inputEncoding G A).encode r).length,
      (fun c => c.bind ((source G A j).machine.step oracle))^[t]
        (some ((source G A j).machine.init ((inputEncoding G A).encode r)))=
        some ((source G A j).machine.output ((F G A).encoding.encode (value G A j r))) ∧
      OracleBatch.primitiveCount (source G A j).machine oracle
        ((source G A j).machine.init ((inputEncoding G A).encode r)) t≤
        (source G A j).machine.primitiveBudget*
          (source G A j).time.eval ((inputEncoding G A).encode r).length := by
  let run := (source G A j).correct oracle ho r
  refine ⟨run.steps,run.steps_le_m,run.evals_in_steps,?_⟩
  exact (OracleBatch.primitiveCount_le (source G A j).machine oracle
    ((source G A j).machine.init ((inputEncoding G A).encode r)) run.steps).trans
      (Nat.mul_le_mul_left (source G A j).machine.primitiveBudget run.steps_le_m)

section OriginalL
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
variable {L : Type} [Field L] [NumberField L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (H : (i : Fin s) → Signature L (a i.val))
variable (B : QuaternaryEqualityTerminal.AnchorStep (FiniteFamily.family (OriginalLCodec.mapped φ H)))

def nativeAccessOriginalL (b : Bool) : PolyTimeOracleReduction (encoding (OriginalLCodec.mapped φ H) B 1)
    (F (OriginalLCodec.mapped φ H) B).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (nativeValue (OriginalLCodec.mapped φ H) B b 1) (OriginalLCodec.value H) :=
  FactorSaturation.PrefixMachine.withTerminal (nativeTable (OriginalLCodec.mapped φ H) B b)
    (F (OriginalLCodec.mapped φ H) B)
    ((pairControlled (OriginalLCodec.mapped φ H) B b).compose (Pair.accessOriginalL s a φ H B b))
    (chain (OriginalLCodec.mapped φ H) B b)

def sourceOriginalL (b : Bool) : PolyTimeOracleReduction (inputEncoding (OriginalLCodec.mapped φ H) B)
    (F (OriginalLCodec.mapped φ H) B).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (value (OriginalLCodec.mapped φ H) B b) (OriginalLCodec.value H) :=
  (paletteControlled (OriginalLCodec.mapped φ H) B b).compose
    ((ordinaryControlled (OriginalLCodec.mapped φ H) B b).compose (nativeAccessOriginalL φ H B b))

def executionOriginalL (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 a)
      (OriginalLCodec.presentation (L:=L)).encoding (OriginalLCodec.value H) oracle)
    (r : ExactSignatureTables.Input (s+2) 1 (paletteArity (OriginalLCodec.mapped φ H) B)) :=
  (sourceOriginalL φ H B j).correct oracle ho r
end OriginalL
end Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess
