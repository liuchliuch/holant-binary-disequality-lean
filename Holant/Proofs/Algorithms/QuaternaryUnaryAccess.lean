import Holant.Proofs.Algorithms.QuaternaryReplicationCompiler
import Holant.Proofs.Reductions.FactorExposureNoIdentity
import Holant.Proofs.Reductions.FactorSaturation.PrefixMachine
import Holant.Proofs.Reductions.CanonicalFamily.Semantics
import Holant.Proofs.Algorithms.RawArityTransport
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Proofs.Reductions.FrozenFactorNormalization.OriginalLCodec


noncomputable section
namespace Holant.LocalDrafts.MainChain.QuaternaryUnaryAccess
open Holant Holant.Tractable Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.FinitePGL2.Stabilization
open GeneralPowerExposure
open UniversalPairReduction.Surgery
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

section Literal
variable {K : Type*} [Field K]
private theorem signature_eq {n m : ℕ} (f : Signature K n) (g : Signature K m)
    (h : n=m) (he : ∀ x, f (fun i => x (Fin.cast h i))=g x) :
    (⟨n,f⟩ : AnySignature K)=⟨m,g⟩ := by
  cases h
  exact congrArg (fun f : Signature K n => (⟨n,f⟩ : AnySignature K))
    (funext (fun x => by simpa using he x))

def pin (b : Bool) : Signature K 1 := fun x => if x 0=b then 1 else 0
def rest (b : Bool) : Signature K 3 := fun x => if x=![!b,false,true] then 1 else 0
def splitPorts (b : Bool) : (Fin 1 ⊕ Fin 3) ≃ Fin 4 :=
  finSumFinEquiv.trans (if b then Equiv.swap 0 1 else Equiv.refl _)

theorem pin_nonzero (b : Bool) : pin (K:=K) b≠0 := by
  intro h
  have he := congrFun h (fun _ => b)
  simpa [pin] using he

theorem square_nonzero : QuaternaryEqualityTerminal.square (K:=K)≠0 := by
  intro h
  have he := congrFun h ![false,true,false,true]
  simpa [QuaternaryEqualityTerminal.square,Signature.tensor_apply,
    QuaternaryEqualityTerminal.delta,UniversalPairReduction.BinaryTable.delta] using he

/-- Original square port 0 exposes pin false; original port 1 exposes pin
true. The right factors retain ports (1,2,3) and (0,2,3), respectively. -/
def squareSplit (b : Bool) : ProperSplit
    (⟨4,QuaternaryEqualityTerminal.square⟩ : AnySignature K) ⟨1,pin b⟩ ⟨3,rest b⟩ where
  left_pos := by norm_num
  right_pos := by norm_num
  ports := splitPorts b
  scale := 1
  equation := by
    funext x
    cases b <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
      cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [QuaternaryEqualityTerminal.square,Signature.tensor_apply,
        QuaternaryEqualityTerminal.delta,UniversalPairReduction.BinaryTable.delta,
        pin,rest,splitPorts,finSumFinEquiv,Equiv.swap_apply_def,
        Fin.castAdd,Fin.natAdd,funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

theorem split_nonzero (b : Bool) : pin (K:=K) b≠0 ∧ rest (K:=K) b≠0 :=
  (squareSplit b).factors_nonzero square_nonzero

theorem pin_map {L : Type*} [Field L] (φ : K →+* L) (b : Bool) (x : Fin 1 → Bool) :
    φ (pin (K:=K) b x)=pin (K:=L) b x := by
  simp only [pin]; split_ifs <;> simp

def castPower {n : ℕ} {a : ℕ → ℕ} {H : (i : Fin n) → Signature K (a i.val)}
    {u v : AnySignature K} (h : u=v) (M : PowerMacro H v.2) : PowerMacro H u.2 := by
  cases h
  exact M
end Literal

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (j : Fin s) {q : Signature AlgebraicComplex 4}
variable (hj : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=⟨4,q⟩)
variable (P : QuaternaryEqualityTerminal.PureStep q)

abbrev K := UniversalPairReduction.Source.field G
abbrev F := UniversalPairReduction.Source.presentation G (QuaternaryEqualityTerminal.algebraic G)
abbrev originalTables := UniversalPairReduction.Source.tables G (QuaternaryEqualityTerminal.algebraic G)
abbrev decoded := UniversalPairReduction.ValueJoins.signatures (F G) (originalTables G)
local instance rationalAlgebra : Algebra ℚ (K G) := (UniversalPairReduction.Source.field G).algebra'
local instance characteristicZero : CharZero (K G) := Algebra.charZero_of_charZero ℚ (K G)

/-- The same original labels, then square, then two unary slots. Only the
total arity function beyond the original range needs an identity-byte bridge. -/
def A (s : ℕ) (a : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i<s then a i else if i=s then 4 else 1

def table (i : ℕ) (x : Fin (A s a i) → Bool) : K G :=
  if hi : i<s then decoded G ⟨i,hi⟩ (fun k => x (Fin.cast (by simp [A,hi]) k))
  else if he : i=s then QuaternaryEqualityTerminal.square
    (fun k => x (Fin.cast (by simp [A,hi,he]) k))
  else pin (decide (i≠s+1)) (fun k => x (Fin.cast (by simp [A,hi,he]) k))

private theorem table_old (i : Fin s) : HEq (table G i.val) (decoded G i) := by
  have ht : table G i.val = fun x => decoded G i
      (fun k => x (Fin.cast (by simp [A,i.isLt]) k)) := by
    funext x
    unfold table
    rw [dif_pos i.isLt]
  exact (heq_of_eq ht).trans
    (EdgeSubdivision.signature_cast_heq (by simp [A,i.isLt]) (decoded G i))

abbrev family (n : ℕ) := FactorSaturation.PrefixMachine.family (s:=s+1) (table G) n
def tables (n : ℕ) := GeneralFieldReduction.targetTables (F G) (family G n)
abbrev value (n : ℕ) := (tables G n).evaluate (F G)
abbrev encoding (s : ℕ) (a : ℕ → ℕ) (n : ℕ) :=
  RawClosedNetwork.validatedEncoding ((s+1)+n) 1 (A s a)

theorem square_label :
    (⟨A s a s, family G 0 ⟨s,by omega⟩⟩ : AnySignature (K G))=
      ⟨4,QuaternaryEqualityTerminal.square⟩ := by
  apply signature_eq _ _ (by simp [A])
  intro x
  simp [family,FactorSaturation.PrefixMachine.family,table,A]

theorem square_member : (⟨4,QuaternaryEqualityTerminal.square⟩ : AnySignature (K G))∈
    Set.range (fun i => (⟨A s a i.val,family G 0 i⟩ : AnySignature (K G))) :=
  ⟨⟨s,by omega⟩,square_label G⟩

theorem original_endpoint (b : Bool) :
    (family G 0 ⟨j.val,by have := j.isLt; omega⟩ (fun _ => b) : AlgebraicComplex)=
      G j (fun _ => b) := by
  simp only [family,FactorSaturation.PrefixMachine.family,table,dif_pos j.isLt]
  exact familyCoordinates_spec (UniversalPairReduction.FiniteFamily.coefficient G)
    (UniversalPairReduction.FiniteFamily.coefficient_algebraic G
      (QuaternaryEqualityTerminal.algebraic G)) _

include j hj P in
/-- Both charge signs come from q's ACTUAL two nonzero endpoints. Square
itself has only a balanced supported word and does not supply this premise. -/
theorem mixedSupport : GeneralCarrierExistence.MixedSupport
    (Set.range (fun i => (⟨A s a i.val,family G 0 i⟩ : AnySignature (K G)))) := by
  have ha : A s a j.val=4 := by simpa [A,j.isLt] using congrArg Sigma.fst hj
  have he (b : Bool) : G j (fun _ => b)≠0 := by
    have hcast := Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (G j) q hj (congrArg Sigma.fst hj) (fun _ => b)
    rw [hcast]
    cases b
    · have hv : q (fun _ => false)=P.left := (congrFun P.original _).trans
        (Holant.EightVertex.ProductAnchor.ge4_left _ _ _)
      rw [hv]; exact (mul_ne_zero_iff.mp P.scale_ne_zero).1
    · have hv : q (fun _ => true)=P.right := (congrFun P.original _).trans
        (Holant.EightVertex.ProductAnchor.ge4_right _ _ _)
      rw [hv]; exact (mul_ne_zero_iff.mp P.scale_ne_zero).2
  intro b
  refine ⟨A s a j.val,family G 0 ⟨j.val,by have := j.isLt; omega⟩,
    ⟨⟨j.val,by have := j.isLt; omega⟩,rfl⟩,
    (fun _ => b),?_,?_⟩
  · intro h
    have hz := congrArg (fun z : K G => (z : AlgebraicComplex)) h
    rw [original_endpoint G j] at hz
    exact he b hz
  · norm_num [Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.balance,ha]

/-- No-I ordinary power exposure, applied to the SPECIFIED square split.
The resulting scalar lives in K already because the theorem runs in K. -/
def pinPower (b : Bool) : PowerMacro (family G 0) (pin (K:=K G) b) :=
  Classical.choice (FactorExposureNoIdentity.labelled (squareSplit b) (family G 0)
    (by norm_num) (mixedSupport G j hj P) square_nonzero (square_member G))

theorem new_signature (i : Fin 2) :
    (⟨A s a ((s+1)+i.val),table G ((s+1)+i.val)⟩ : AnySignature (K G))=
      ⟨1,pin (i.val==1)⟩ := by
  apply signature_eq _ _ (by simp [A,show ¬(s+1)+i.val<s by omega,
    show (s+1)+i.val≠s by omega])
  intro x
  fin_cases i <;> simp [A,table,show ¬s+1<s by omega,show ¬s+2<s by omega,
    show s+1≠s by omega,show s+2≠s by omega,Nat.add_assoc]

def power (i : Fin 2) : PowerMacro (family G 0) (table G ((s+1)+i.val)) :=
  castPower (new_signature G i) (pinPower G j hj P (i.val==1))

def chain : RecursiveMachine.Chain (family G 0) (family G 2) :=
  FactorSaturation.PrefixMachine.chain (table G) (power G j hj P) 2 le_rfl

/-- The explicit two node extension is the only new factor data. No
alternative forest or factor-saturation choice has been installed. -/
theorem final_pin (i : Fin 2) :
    (⟨A s a ((s+1)+i.val),family G 2 ⟨(s+1)+i.val,by have := i.isLt; omega⟩⟩ :
      AnySignature (K G))=⟨1,pin (i.val==1)⟩ := new_signature G i

theorem base_arity (i : Fin (s+1)) : A s a i.val=QuaternaryReplicationMachine.squareArity s a i.val := by
  by_cases hi : i.val<s
  · simp [A,QuaternaryReplicationMachine.squareArity,hi]
  · have he : i.val=s := by have := i.isLt; omega
    simp [A,QuaternaryReplicationMachine.squareArity,he]

def squareQuery := RawArityTransport.input (base_arity (s:=s) (a:=a)) (b:=1)
def squareQueryComputes := RawArityTransport.computes (base_arity (s:=s) (a:=a)) (b:=1)

theorem base_signatures : RawArityTransport.signatures (base_arity (s:=s) (a:=a)) (family G 0)=
    QuaternaryReplicationMachine.squareSignatures (decoded G) := by
  funext i x
  by_cases hi : i.val<s
  · simp [RawArityTransport.signatures,family,FactorSaturation.PrefixMachine.family,
      table,QuaternaryReplicationMachine.squareSignatures,hi]
  · have he : i.val=s := by have := i.isLt; omega
    simp [RawArityTransport.signatures,family,FactorSaturation.PrefixMachine.family,
      table,QuaternaryReplicationMachine.squareSignatures,hi,he]

theorem base_value (r : ExactSignatureTables.Input (s+1) 1 (A s a)) :
    value G 0 r=QuaternaryReplicationMachine.squareFieldValue G (squareQuery r) := by
  rw [value,tables,Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.target_evaluate]
  rw [←RawArityTransport.denote (base_arity (s:=s) (a:=a)) (family G 0)
    (fun _ : Fin 1 => Signature.disequality) r,base_signatures]
  rfl

def squareTables := GeneralFieldReduction.targetTables (F G)
  (QuaternaryReplicationMachine.squareSignatures (decoded G))
theorem square_tables_value (r : QuaternaryReplicationMachine.Input s a) :
    (squareTables G).evaluate (F G) r=QuaternaryReplicationMachine.squareFieldValue G r :=
  Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.target_evaluate _ _ _

def squareOutput : PolynomialOutputBound (QuaternaryReplicationCompiler.sourceEncoding s a)
    (F G).encoding (QuaternaryReplicationMachine.squareFieldValue G) where
  bound := (squareTables G).outputPolynomial (F G)
  length_le r := by
    have h := (squareTables G).output_length_le (F G) r
    rw [square_tables_value] at h
    exact h

/-- Identity BYTES for the graph, and the very same fixed field codec for
the answer. The explicit field is shared with replication from the start. -/
def toSquare : LengthControlledOracleReduction (encoding s a 0) (F G).encoding
    (QuaternaryReplicationCompiler.sourceEncoding s a) (F G).encoding
    (value G 0) (QuaternaryReplicationMachine.squareFieldValue G) :=
  controlledOneQueryOfEq squareQueryComputes (identityComputes (F G).encoding)
    (squareOutput G) (value G 0) (base_value G)

def terminal : PolyTimeOracleReduction (encoding s a 0) (F G).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (F G).encoding (value G 0)
    (UniversalPairReduction.Source.targetValue G (QuaternaryEqualityTerminal.algebraic G)) :=
  (toSquare G).compose (QuaternaryReplicationCompiler.reduction s a G j hj P)

/-- withTerminal expands EACH controlled factor step around the actual
square terminal. No two arbitrary Poly reductions are composed. -/
def augmentedAccess : PolyTimeOracleReduction (encoding s a 2) (F G).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (F G).encoding (value G 2)
    (UniversalPairReduction.Source.targetValue G (QuaternaryEqualityTerminal.algebraic G)) :=
  FactorSaturation.PrefixMachine.withTerminal (table G) (F G)
    (terminal G j hj P) (chain G j hj P)

/-! Remove the square slot from the USER palette. The square remains an
internal terminal resource, not an input assumption or a free source label. -/
def paletteArity (s : ℕ) (a : ℕ → ℕ) (i : ℕ) : ℕ := if i<s then a i else 1
def includeLabel (s : ℕ) (i : Fin (s+2)) : Fin ((s+1)+2) :=
  if hi : i.val<s then ⟨i.val,by omega⟩ else ⟨i.val+1,by have := i.isLt; omega⟩
private theorem includeLabel_old (i : Fin s) :
    includeLabel s ⟨i.val,by have := i.isLt; omega⟩ = Fin.castAdd 3 i := by
  unfold includeLabel
  rw [dif_pos i.isLt]
  rfl
theorem include_arity (i : Fin (s+2)) : A s a (includeLabel s i).val=paletteArity s a i.val := by
  by_cases hi : i.val<s
  · simp [includeLabel,A,paletteArity,hi]
  · simp [includeLabel,paletteArity,hi,A,show ¬i.val+1<s by omega,show i.val+1≠s by omega]

def palette (i : Fin (s+2)) : Signature (K G) (paletteArity s a i.val) :=
  fun x => family G 2 (includeLabel s i) (fun k => x (Fin.cast (include_arity i) k))
private theorem palette_heq (i : Fin (s+2)) :
    HEq (palette G i) (family G 2 (includeLabel s i)) :=
  EdgeSubdivision.signature_cast_heq (include_arity i) (family G 2 (includeLabel s i))
def paletteTables := GeneralFieldReduction.targetTables (F G) (palette G)
abbrev paletteValue := (paletteTables G).evaluate (F G)
abbrev paletteEncoding (s : ℕ) (a : ℕ → ℕ) :=
  RawClosedNetwork.validatedEncoding (s+2) 1 (paletteArity s a)

theorem palette_old (i : Fin s) :
    (⟨paletteArity s a i.val,palette G ⟨i.val,by have := i.isLt; omega⟩⟩ : AnySignature (K G))=
      ⟨a i.val,decoded G i⟩ := by
  apply Sigma.ext (by simp [paletteArity,i.isLt])
  have hp := palette_heq G ⟨i.val,by have := i.isLt; omega⟩
  rw [includeLabel_old] at hp
  exact hp.trans (table_old G i)

theorem palette_pin (b : Bool) :
    (⟨paletteArity s a (s+b.toNat),palette G ⟨s+b.toNat,by cases b <;> simp <;> omega⟩⟩ :
      AnySignature (K G))=⟨1,pin b⟩ := by
  apply signature_eq _ _ (by cases b <;> simp [paletteArity])
  intro x
  cases b <;> simp [paletteArity,palette,family,FactorSaturation.PrefixMachine.family,
    includeLabel,table,A,Nat.add_assoc,show ¬s+1<s by omega,show ¬s+2<s by omega,
    show s+1≠s by omega,show s+2≠s by omega,Fin.cast_cast]

/-- Both actual nonzero unaries, with literal orientation and unit scale,
are present in the source of access. No occurrence of square is required. -/
theorem palette_contains_pins (b : Bool) :
    (⟨1,pin b⟩ : AnySignature (K G))∈
      Set.range (fun i => (⟨paletteArity s a i.val,palette G i⟩ : AnySignature (K G))) ∧
      pin (K:=K G) b≠0 :=
  ⟨⟨⟨s+b.toNat,by cases b <;> simp <;> omega⟩,palette_pin G b⟩,pin_nonzero b⟩

theorem decoded_exact (i : Fin s) (x : Fin (a i.val) → Bool) :
    (decoded G i x : AlgebraicComplex)=G i x :=
  familyCoordinates_spec (UniversalPairReduction.FiniteFamily.coefficient G)
    (UniversalPairReduction.FiniteFamily.coefficient_algebraic G
      (QuaternaryEqualityTerminal.algebraic G)) _

/-- The whole source family, not a singleton product test: the original
coefficient table together with precisely the two literal nonzero pins. -/
theorem palette_family :
    Set.range (fun i => (⟨paletteArity s a i.val,palette G i⟩ : AnySignature (K G)))=
      Set.range (fun i : Fin s => (⟨a i.val,decoded G i⟩ : AnySignature (K G))) ∪
        {(⟨1,pin false⟩ : AnySignature (K G)),⟨1,pin true⟩} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<s
    · exact Or.inl ⟨⟨i.val,hi⟩,by simpa using (palette_old G ⟨i.val,hi⟩).symm⟩
    · have hs : i.val=s ∨ i.val=s+1 := by have := i.isLt; omega
      rcases hs with hs|hs
      · have he : i=⟨s,by omega⟩ := Fin.ext hs
        rw [he]
        exact Or.inr (by
          dsimp only
          rw [show (⟨paletteArity s a s,palette G ⟨s,by omega⟩⟩ : AnySignature (K G))=
            ⟨1,pin false⟩ by simpa using palette_pin G false]
          simp)
      · have he : i=⟨s+1,by omega⟩ := Fin.ext hs
        rw [he]
        exact Or.inr (by
          dsimp only
          rw [show (⟨paletteArity s a (s+1),palette G ⟨s+1,by omega⟩⟩ : AnySignature (K G))=
            ⟨1,pin true⟩ by simpa using palette_pin G true]
          simp)
  · rintro (⟨i,rfl⟩|h)
    · exact ⟨⟨i.val,by have := i.isLt; omega⟩,palette_old G i⟩
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
      rcases h with rfl|rfl
      · exact (palette_contains_pins G false).1
      · exact (palette_contains_pins G true).1

def paletteQuery := CanonicalFamily.Relabel.input (includeLabel s) (include_arity (s:=s) (a:=a))
def paletteQueryComputes := CanonicalFamily.Relabel.computes
  (includeLabel s) (include_arity (s:=s) (a:=a))

theorem palette_value (r : ExactSignatureTables.Input (s+2) 1 (paletteArity s a)) :
    paletteValue G r=value G 2 (paletteQuery r) := by
  rw [paletteValue,paletteTables,value,tables,
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.target_evaluate,
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.target_evaluate,
    Choice.denote_eq_evaluate,Choice.denote_eq_evaluate]
  have h := CanonicalFamily.Relabel.value_scaled (includeLabel s)
    (Choice.table (palette G)) (Choice.table (family G 2)) (fun _ => (1 : K G))
    (include_arity (s:=s) (a:=a)) r (by
      intro i bits
      unfold Choice.table
      rw [dif_pos i.isLt,dif_pos (includeLabel s i).isLt]
      simp only [one_mul,palette,Fin.val_cast])
  have ho : RootPreprocessing.OccurrenceProduct.value (fun _ : Fin (s+2) => (1 : K G)) r.val=1 := by
    unfold RootPreprocessing.OccurrenceProduct.value
    have hm : r.val.vertices.map
        (fun row => RootPreprocessing.OccurrenceProduct.total (fun _ : Fin (s+2) => (1 : K G)) row.1) =
        r.val.vertices.map (fun _ => (1 : K G)) := by
      apply List.map_congr_left
      intro row hr
      have hi := (((Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping.wellFormed_iff_members
        _ _ _ _).mp r.property).1 row hr).1
      simp only [RootPreprocessing.OccurrenceProduct.total,dif_pos hi]
    rw [hm,List.map_const',List.prod_replicate,one_pow]
  rw [ho,one_mul] at h
  exact h

/-- This prefix is controlled too, so installing the full factor interpreter
does not rely on arbitrary composition of two polynomial reductions. -/
def paletteControlled : LengthControlledOracleReduction (paletteEncoding s a) (F G).encoding
    (encoding s a 2) (F G).encoding (paletteValue G) (value G 2) :=
  controlledOneQueryOfEq paletteQueryComputes (identityComputes (F G).encoding)
    ((tables G 2).outputBound (F G)) (paletteValue G) (palette_value G)

abbrev Access := PolyTimeOracleReduction (paletteEncoding s a) (F G).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (F G).encoding (paletteValue G)
    (UniversalPairReduction.Source.targetValue G (QuaternaryEqualityTerminal.algebraic G))

/-- Arbitrarily many occurrences of BOTH pins reduce to the actual original
CURRENT G oracle. All recursive factor steps are expanded by withTerminal. -/
def access : Access G :=
  (paletteControlled G).compose (augmentedAccess G j hj P)

theorem palette_ports (r : ExactSignatureTables.Input (s+2) 1 (paletteArity s a)) :
    (paletteQuery r).val.vertices.map Prod.snd=r.val.vertices.map Prod.snd :=
  CanonicalFamily.Relabel.ordered_ports (includeLabel s) r.val
theorem palette_edges (r : ExactSignatureTables.Input (s+2) 1 (paletteArity s a)) :
    (paletteQuery r).val.edges=r.val.edges := rfl

def execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 a) (F G).encoding
      (UniversalPairReduction.Source.targetValue G (QuaternaryEqualityTerminal.algebraic G)) oracle)
    (r : ExactSignatureTables.Input (s+2) 1 (paletteArity s a)) :=
  (access G j hj P).correct oracle ho r

section OriginalL
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
variable {L : Type} [Field L] [NumberField L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (H : (i : Fin s) → Signature L (a i.val))

/-- Native X contributes only 0 and 1. Consequently the replication field
embeds in the vertex-only field handled by OriginalLCodec; bases/codecs are
still NOT identified. -/
theorem whole_le_vertex : K (OriginalLCodec.mapped φ H) ≤ OriginalLCodec.coefficientField φ H := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨idx,rfl⟩
  rcases idx with ⟨i,x⟩|⟨e,b,c⟩
  · exact coefficient_mem_familyField (GeneralOriginalTarget.coefficients (OriginalLCodec.mapped φ H)) ⟨i,x⟩
  · cases b <;> cases c <;>
      simp [UniversalPairReduction.FiniteFamily.coefficient,Signature.disequality]

def intoL : K (OriginalLCodec.mapped φ H) →ₐ[ℚ] L :=
  (OriginalLCodec.intoL φ H).comp (IntermediateField.inclusion (whole_le_vertex φ H))

private theorem composition_value (M N : IntermediateField ℚ AlgebraicComplex)
    (ψ : N →ₐ[ℚ] L) (h : M ≤ N)
    (hψ : ∀ z : N, φ (ψ z)=(z : AlgebraicComplex)) (z : M) :
    φ ((ψ.comp (IntermediateField.inclusion h)) z)=(z : AlgebraicComplex) := hψ _

theorem intoL_exact (z : K (OriginalLCodec.mapped φ H)) : φ (intoL φ H z)=(z : AlgebraicComplex) :=
  composition_value φ _ _ (OriginalLCodec.intoL φ H) (whole_le_vertex φ H)
    (OriginalLCodec.intoL_value φ H) z

def recoverL := FieldCodec.retractComputes (F (OriginalLCodec.mapped φ H)) (OriginalLCodec.presentation (L:=L)) (intoL φ H)
theorem intoL_original (i : Fin s) (x : Fin (a i.val) → Bool) : intoL φ H (decoded (OriginalLCodec.mapped φ H) i x)=H i x := by
  apply φ.injective
  change φ (intoL φ H (decoded (OriginalLCodec.mapped φ H) i x))=φ (H i x)
  rw [intoL_exact]
  exact familyCoordinates_spec (UniversalPairReduction.FiniteFamily.coefficient (OriginalLCodec.mapped φ H))
    (UniversalPairReduction.FiniteFamily.coefficient_algebraic (OriginalLCodec.mapped φ H)
      (QuaternaryEqualityTerminal.algebraic (OriginalLCodec.mapped φ H))) _

theorem delta_intoL (r : UniversalPairReduction.Input s a) :
    intoL φ H (UniversalPairReduction.Source.sourceValue (OriginalLCodec.mapped φ H) (QuaternaryEqualityTerminal.algebraic (OriginalLCodec.mapped φ H)) r)=
      UniversalPairReduction.BinaryFamily.value H UniversalPairReduction.BinaryTable.delta r := by
  unfold UniversalPairReduction.Source.sourceValue UniversalPairReduction.BinaryFamily.value
  change (intoL φ H).toRingHom _ = _
  rw [←Network.denote_map]
  congr 1
  unfold UniversalPairReduction.BinaryFamily.network Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    dsimp only
    unfold UniversalPairReduction.BinaryFamily.signatures
    split_ifs with hi
    · exact intoL_original φ H _ _
    · simp only [UniversalPairReduction.BinaryTable.delta]
      split_ifs <;> simp
  · funext e b c
    cases b <;> cases c <;> simp [Signature.disequality]

def deltaLTables := GeneralFieldReduction.targetTables (OriginalLCodec.presentation (L:=L))
  (UniversalPairReduction.BinaryFamily.signatures H UniversalPairReduction.BinaryTable.delta)
def deltaLOutput : PolynomialOutputBound (UniversalPairReduction.inputEncoding s a)
    (OriginalLCodec.presentation (L:=L)).encoding
    (UniversalPairReduction.BinaryFamily.value H UniversalPairReduction.BinaryTable.delta) where
  bound := (deltaLTables H).outputPolynomial (OriginalLCodec.presentation (L:=L))
  length_le r := by
    have h := (deltaLTables H).output_length_le (OriginalLCodec.presentation (L:=L)) ⟨r.val,r.property.1⟩
    unfold deltaLTables GeneralFieldReduction.targetTables at h
    rw [Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.target_evaluate] at h
    exact h

/-- Reuse the existing represented single-Delta compiler with the REAL
original-L tables. This is the same algorithmic theorem, not a free change
of oracle answer encoding of the previously selected coefficient program. -/
def singleDeltaL : PolyTimeOracleReduction (UniversalPairReduction.inputEncoding s a)
    (OriginalLCodec.presentation (L:=L)).encoding (RawClosedNetwork.validatedEncoding s 1 a)
    (OriginalLCodec.presentation (L:=L)).encoding
    (UniversalPairReduction.BinaryFamily.value H UniversalPairReduction.BinaryTable.delta)
    (OriginalLCodec.value H) := by
  have hn : ∀i b c,(OriginalLCodec.presentation (L:=L)).decode
      ((OriginalLCodec.tables H).edge i b c)=Signature.disequality b c := by
    intro i b c
    simp [OriginalLCodec.tables,GeneralFieldReduction.targetTables,
      Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables]
  let R := Classical.choose (UniversalPairReduction.represented_one_pair_reduction
    (OriginalLCodec.presentation (L:=L)) (OriginalLCodec.tables H) hn)
  apply UniversalPairReduction.SmoothingCompiler.sourceTransfer R
    (UniversalPairReduction.BinaryFamily.value H UniversalPairReduction.BinaryTable.delta)
  intro r
  have hv : UniversalPairReduction.ValueJoins.signatures (OriginalLCodec.presentation (L:=L))
      (OriginalLCodec.tables H)=H := by
    funext i x
    simp [UniversalPairReduction.ValueJoins.signatures,OriginalLCodec.tables,
      GeneralFieldReduction.targetTables,
      Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables]
  change _=UniversalPairReduction.BinaryFamily.value
    (UniversalPairReduction.ValueJoins.signatures _ _) _ r
  rw [hv]

variable (jl : Fin s) {ql : Signature AlgebraicComplex 4}
variable (hjl : (⟨a jl.val,(OriginalLCodec.mapped φ H) jl⟩ : AnySignature AlgebraicComplex)=⟨4,ql⟩)
variable (Pl : QuaternaryEqualityTerminal.PureStep ql)

def squareControlledL : LengthControlledOracleReduction
    (QuaternaryReplicationCompiler.sourceEncoding s a) (F (OriginalLCodec.mapped φ H)).encoding
    (UniversalPairReduction.inputEncoding s a) (OriginalLCodec.presentation (L:=L)).encoding
    (QuaternaryReplicationMachine.squareFieldValue (OriginalLCodec.mapped φ H))
    (UniversalPairReduction.BinaryFamily.value H UniversalPairReduction.BinaryTable.delta) := by
  let post := (leftMapComputes GraphPreprocessing.UnaryBinary.unaryEncoding (recoverL φ H)).andThen
    (QuaternaryReplicationMachine.correction (OriginalLCodec.mapped φ H) jl)
  apply ControlledCap.controlledContextOfEq
    (QuaternaryReplicationCompiler.prepared s a jl (congrArg Sigma.fst hjl)) post
    (deltaLOutput H) (QuaternaryReplicationMachine.squareFieldValue (OriginalLCodec.mapped φ H))
  intro r
  change QuaternaryReplicationMachine.squareFieldValue (OriginalLCodec.mapped φ H) r=
    ((intoL φ H).toLinearMap.leftInverse
      (UniversalPairReduction.BinaryFamily.value H UniversalPairReduction.BinaryTable.delta
        (QuaternaryReplicationMachine.query jl (congrArg Sigma.fst hjl) r))) *
      (QuaternaryReplicationMachine.scale (OriginalLCodec.mapped φ H) jl)⁻¹^QuaternaryReplicationMachine.count s r.val.vertices
  rw [←delta_intoL φ H,FieldCodec.retract_embedding,
    QuaternaryReplicationMachine.query_value_field (OriginalLCodec.mapped φ H) jl hjl Pl,
    ScalarPower.cancel_scale_power _ _ (QuaternaryReplicationMachine.scale_nonzero (OriginalLCodec.mapped φ H) jl hjl Pl)]

def originalLTerminal : PolyTimeOracleReduction (encoding s a 0) (F (OriginalLCodec.mapped φ H)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (value (OriginalLCodec.mapped φ H) 0) (OriginalLCodec.value H) :=
  (toSquare (OriginalLCodec.mapped φ H)).compose ((squareControlledL φ H jl hjl Pl).compose (singleDeltaL H))

/-- The original-L oracle is injected BEFORE interpreting either factor
step. In particular this is not `access.compose` with an arbitrary Poly. -/
def accessOriginalL : PolyTimeOracleReduction (paletteEncoding s a) (F (OriginalLCodec.mapped φ H)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (paletteValue (OriginalLCodec.mapped φ H)) (OriginalLCodec.value H) :=
  (paletteControlled (OriginalLCodec.mapped φ H)).compose
    (FactorSaturation.PrefixMachine.withTerminal (table (OriginalLCodec.mapped φ H)) (F (OriginalLCodec.mapped φ H))
      (originalLTerminal φ H jl hjl Pl) (chain (OriginalLCodec.mapped φ H) jl hjl Pl))

end OriginalL

end Holant.LocalDrafts.MainChain.QuaternaryUnaryAccess
