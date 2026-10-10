import Holant.Proofs.BinaryInterpolation.MachineCapstone
import Holant.Proofs.BinaryInterpolation.PostprocessCorrectness
import Holant.Complexity.BinaryInterpolation.AlgebraicSource.FiniteField


namespace Holant.LocalDrafts.BinaryInterpolation.FieldSource
open Computability Holant.Algebraic
open Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

namespace CF
export AlgebraicSource.CommonField (field presentation original representative left right beta rho node
  original_exact representative_exact left_exact right_exact beta_exact rho_exact node_exact
  targetValue sourceValue target_value_exact source_value_exact source_family_exact
  beta_nonzero rho_nonzero positive_nodes_injective right_nonzero)
end CF

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature ℂ (arity i.val))
variable (halg : ∀ i x, IsAlgebraic ℚ (G i x))
variable {B : Binary (K:=ℂ)} (M : AlgebraicSource.Macro G B)
variable (p : AlgebraicSource.Pencil M.binary)

abbrev Field := CF.field G M.binary p
abbrev fixedField := CF.presentation G halg M.binary M.binary_algebraic p
abbrev original := CF.original G M.binary p
abbrev H := CF.right G M.binary p
abbrev gamma := CF.beta G M.binary p
abbrev rho := CF.rho G M.binary p

/-- Canonical rational-coordinate tables for the literal original Γ family.
Both the target oracle and the new machine use exactly this fixed codec. -/
def targetTables : ExactSignatureTables (Module.finrank ℚ (Field G M p)) s 1 arity where
  vertex i x := (fixedField G halg M p).decode.symm (original G M p i x)
  edge _ a b := (fixedField G halg M p).decode.symm (Signature.disequality a b)

theorem target_evaluate (q : ExactSignatureTables.Input s 1 arity) :
    (targetTables G halg M p).evaluate (fixedField G halg M p) q =
      CF.targetValue G M.binary p q := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [targetTables, LinearEquiv.apply_symm_apply]
  rfl

theorem target_exact (q : ExactSignatureTables.Input s 1 arity) :
    (((targetTables G halg M p).evaluate (fixedField G halg M p) q : Field G M p) : ℂ) =
      PostprocessCorrectness.target G q := by
  rw [target_evaluate]
  exact CF.target_value_exact G M.binary p q

def data : MachineCapstone.Data (fixedField G halg M p) (targetTables G halg M p) where
  template := M.label.template
  valid := M.label.wellFormed
  binary := rfl
  edge := 0
  gamma := gamma G M p
  rho := rho G M p
  geometric := p.geometric

abbrev Input := ExactSignatureTables.Input (s+1) 1 (extendedArity s arity)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (extendedArity s arity)
abbrev outputEncoding := (fixedField G halg M p).encoding
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 arity

theorem arity_eq : PhysicalQueries.A (s:=s) arity M.label.template = extendedArity s arity := by
  funext i
  by_cases hi : i < s
  · simp [PhysicalQueries.A, Chains.Compiler.OriginalFamily.macroArity, sourceArity,
      Adjoin.templates, hi, identityTemplate, extendedArity]
  · simp [PhysicalQueries.A, Chains.Compiler.OriginalFamily.macroArity, sourceArity,
      Adjoin.templates, hi, Labelling.template, extendedArity]

def asMacroInput (r : Input (s:=s) (arity:=arity)) :
    PhysicalQueries.Source (s:=s) (b:=1) arity M.label.template :=
  ⟨r.val, by rw [arity_eq G M]; exact r.property⟩

@[simp] theorem input_bytes (r : Input (s:=s) (arity:=arity)) :
    (MachineCapstone.inputEncoding (data G halg M p)).encode (asMacroInput G M r) =
      (inputEncoding (s:=s) (arity:=arity)).encode r := rfl

/-- Mapping the actual labelled macro into ℂ recovers exactly its original
denotation; the original nonzero macro scalar is already in M.binary. -/
theorem macro_denote :
    (M.label.template.network M.label.wellFormed (original G M p)
      (fun _ : Fin 1 => Signature.disequality)).denote =
      Chains.binarySignature (CF.representative G M.binary p) := by
  let N := M.label.template.network M.label.wellFormed (original G M p)
    (fun _ : Fin 1 => Signature.disequality)
  have hn : N.map (CF.field G M.binary p).subtype =
      M.label.template.network M.label.wellFormed G
        (fun _ : Fin 1 => Signature.disequality) := by
    unfold N Network.map Template.network
    congr 1
    funext e a b
    cases a <;> cases b <;> rfl
  change (N : Network (Field G M p) 2).denote = _
  funext x
  apply Subtype.ext
  change (CF.field G M.binary p).subtype (N.denote x) = _
  rw [← Network.denote_map, hn, M.denote_exact]
  exact (CF.representative_exact G M.binary p
    (x ⟨0, by change 0 < 2; decide⟩) (x ⟨1, by change 1 < 2; decide⟩)).symm

/-- The entire spectral identity holds inside the same faithful field.
Injectivity of its actual embedding, not a new spectral assumption, proves it. -/
theorem power_identity (t : ℕ) :
    (CF.representative G M.binary p * X)^t * X =
      (gamma G M p)^t • (CF.left G M.binary p +
        CF.node G M.binary p t • H G M p) := by
  let f := (CF.field G M.binary p).subtype
  have hx : (X : Binary (K:=Field G M p)).map f = X := by
    ext a b
    cases a <;> cases b <;> rfl
  have hr : (CF.representative G M.binary p).map f = M.binary := by
    ext a b
    exact CF.representative_exact G M.binary p a b
  have hp : (((CF.representative G M.binary p * X)^t * X).map f) =
      (M.binary*X)^t*X := by rw [Matrix.map_mul (f:=f), Matrix.map_pow _ f, Matrix.map_mul (f:=f), hr, hx]
  apply Matrix.ext
  intro a b
  apply Subtype.ext
  have hs := congrFun₂ (hp.trans (p.power_identity t)) a b
  cases hg : p.geometric <;>
    simp [hg, f, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      gamma, H, AlgebraicSource.Pencil.node] at hs ⊢ <;> exact hs

/-- Congruence across validated arity transports, preserving raw incidence,
both kernel ends, and every ordered signature argument. -/
theorem raw_value_transport {K : Type} [CommSemiring K] {u e : ℕ}
    {a a' : ℕ → ℕ} (ha : a = a')
    (S : (i : Fin u) → Signature K (a i.val))
    (S' : (i : Fin u) → Signature K (a' i.val))
    (hs : ∀ i, (⟨a i.val,S i⟩ : AnySignature K) = ⟨a' i.val,S' i⟩)
    (kernels : Fin e → Bool → Bool → K) (r : RawClosedNetwork)
    (h : r.WellFormed u e a) (h' : r.WellFormed u e a') :
    (r.realize h S kernels).denote Fin.elim0 = (r.realize h' S' kernels).denote Fin.elim0 := by
  subst a'
  have he : S = S' := by
    funext i
    exact eq_of_heq (Sigma.mk.inj_iff.mp (hs i)).2
  subst S'
  rfl

private theorem signature_cast_heq {K : Type} {m n : ℕ} (hm : m=n) (f : Signature K m) :
    HEq (fun x : Fin n → Bool => f (fun i => x (Fin.cast hm i))) f := by
  subst n
  rfl

theorem slot_canonical {K : Type} [_root_.Field K]
    (G' : (i : Fin s) → Signature K (arity i.val)) (J : Binary (K:=K)) (i : Fin (s+1)) :
    (⟨PhysicalQueries.A (s:=s) arity M.label.template i.val,
      OriginalTables.binarySlot M.label.template M.label.wellFormed G'
        (fun _ : Fin 1 => Signature.disequality) rfl J i⟩ : AnySignature K) =
    ⟨extendedArity s arity i.val,BinaryFamily.signatures G' J i⟩ := by
  by_cases hi : i.val < s
  · have h := OriginalTables.binarySlot_old M.label.template M.label.wellFormed G'
      (fun _ : Fin 1 => Signature.disequality) rfl J (⟨i.val,hi⟩ : Fin s)
    have hc : (⟨extendedArity s arity i.val,BinaryFamily.signatures G' J i⟩ : AnySignature K) =
        ⟨arity i.val,G' ⟨i.val,hi⟩⟩ := by
      apply Sigma.ext (by simp [extendedArity, hi])
      unfold BinaryFamily.signatures
      simp only [dif_pos hi]
      exact signature_cast_heq _ _
    exact h.trans hc.symm
  · have hv : i.val = s := by omega
    have he : i = PhysicalQueries.newLabel := Fin.ext hv
    subst i
    have h := OriginalTables.binarySlot_new M.label.template M.label.wellFormed G'
      (fun _ : Fin 1 => Signature.disequality) rfl J
    apply h.trans
    apply Sigma.ext (by simp [extendedArity, PhysicalQueries.newLabel])
    symm
    unfold BinaryFamily.signatures
    simp only [PhysicalQueries.newLabel, Fin.val_mk, dif_neg (Nat.lt_irrefl s)]
    exact signature_cast_heq _ (Chains.binarySignature J)

theorem values_exact (r : PhysicalQueries.Source (s:=s) (b:=1) arity M.label.template)
    (i : Fin (occurrences s r.val+1)) :
    ((MachineCapstone.values (data G halg M p) r i : Field G M p) : ℂ) =
      PostprocessCorrectness.answers G M r i :=
  target_exact G halg M p _

/-- Every operation in the explicit quotient is respected by the same field
embedding, including products, zero answers, and the final reciprocal. -/
theorem interpolated_exact (r : PhysicalQueries.Source (s:=s) (b:=1) arity M.label.template) :
    ((MachineCapstone.interpolatedValue (data G halg M p) r : Field G M p) : ℂ) =
    commonNumerator (PostprocessCorrectness.denominators G M p r)
      (PostprocessCorrectness.answers G M r) /
      Holant.Complexity.BinaryInterpolation.commonDenominator (PostprocessCorrectness.denominators G M p r) := by
  let φ : Field G M p →+* ℂ := (CF.field G M.binary p).subtype
  change φ (MachineCapstone.interpolatedValue (data G halg M p) r) = _
  have hv (i : Fin (occurrences s r.val+1)) : φ (MachineCapstone.values (data G halg M p) r i) =
      PostprocessCorrectness.answers G M r i := values_exact G halg M p r i
  simp only [MachineCapstone.interpolatedValue, MachineCapstone.resultPair,
    commonNumerator, Holant.Complexity.BinaryInterpolation.commonDenominator,
    map_div₀, map_sum, map_mul, map_prod, hv]
  have hb : (CF.field G M.binary p).val (CF.beta G M.binary p) = p.beta := rfl
  have hr : (CF.field G M.binary p).val (CF.rho G M.binary p) = p.rho := rfl
  cases hg : p.geometric <;>
    simp [MachineCapstone.denominator, PostprocessCorrectness.denominators,
      queryDenominator, interpolationDenominator, WeightFormulas.nodes, WeightFormulas.scales,
      data, gamma, rho, hg, φ, hb, hr] <;> rfl

theorem recovery (r : Input (s:=s) (arity:=arity)) :
    MachineCapstone.interpolatedValue (data G halg M p) (asMacroInput G M r) =
      CF.sourceValue G M.binary p r := by
  apply Subtype.ext
  calc
    _ = commonNumerator (PostprocessCorrectness.denominators G M p (asMacroInput G M r))
        (PostprocessCorrectness.answers G M (asMacroInput G M r)) /
        Holant.Complexity.BinaryInterpolation.commonDenominator (PostprocessCorrectness.denominators G M p (asMacroInput G M r)) :=
      interpolated_exact G halg M p _
    _ = ((asMacroInput G M r).val.realize (asMacroInput G M r).property
        (OriginalTables.binarySlot M.label.template M.label.wellFormed G
          (fun _ : Fin 1 => Signature.disequality) rfl p.H)
        (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 :=
      PostprocessCorrectness.quotient_correct G M p _
    _ = (r.val.realize r.property (BinaryFamily.signatures G p.H)
        (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 :=
      raw_value_transport (arity_eq G M) _ _ (slot_canonical G M G p.H)
        (fun _ : Fin 1 => Signature.disequality) r.val (asMacroInput G M r).property r.property
    _ = (CF.sourceValue G M.binary p r : ℂ) := (CF.source_value_exact G M.binary p r).symm

theorem denominator_nonzero (r : Input (s:=s) (arity:=arity)) :
    (MachineCapstone.resultPair (data G halg M p) (asMacroInput G M r)).2 ≠ 0 := by
  apply Holant.Complexity.BinaryInterpolation.commonDenominator_ne_zero
  intro i
  apply queryDenominator_ne_zero
  · exact CF.positive_nodes_injective G M.binary p (occurrences s r.val)
  · intro j
    exact pow_ne_zero _ (CF.beta_nonzero G M.binary p)

/-- The complete source reduction uses the canonical Γ∪{H} input encoding,
the original Γ query encoding, and the same exact number-field answer encoding.
Neither the reduction nor any whole-instance correctness property is assumed. -/
def reduction : PolyTimeOracleReduction (inputEncoding (s:=s) (arity:=arity))
    (outputEncoding G halg M p) (targetEncoding (s:=s) (arity:=arity))
    (outputEncoding G halg M p) (CF.sourceValue G M.binary p) (CF.targetValue G M.binary p) where
  machine := MachineCapstone.machine (data G halg M p)
  time := MachineCapstone.timePolynomial (data G halg M p)
  correct oracle ho r := by
    have ho' : RepresentsOracle (targetEncoding (s:=s) (arity:=arity))
        (outputEncoding G halg M p)
        ((targetTables G halg M p).evaluate (fixedField G halg M p)) oracle := by
      intro q
      simpa only [target_evaluate] using ho q
    have h := (MachineCapstone.reduction (data G halg M p)).correct oracle ho' (asMacroInput G M r)
    simp only [recovery, input_bytes] at h
    exact h

/-- The capstone keeps the exact ordered transcript on the same successful
execution that returns the Γ∪{H} value, not merely a separate list-size bound. -/
theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (arity:=arity)) (outputEncoding G halg M p)
      (CF.targetValue G M.binary p) oracle) (r : Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction G halg M p).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction G halg M p).machine oracle
        ((reduction G halg M p).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction G halg M p).machine.output
          ((outputEncoding G halg M p).encode (CF.sourceValue G M.binary p r))) t
        ((MachineCapstone.queries (data G halg M p) (asMacroInput G M r)).map
          (targetEncoding (s:=s) (arity:=arity)).encode) := by
  have ho' : RepresentsOracle (targetEncoding (s:=s) (arity:=arity)) (outputEncoding G halg M p)
      ((targetTables G halg M p).evaluate (fixedField G halg M p)) oracle := by
    intro q
    simpa only [target_evaluate] using ho q
  have h := MachineCapstone.execution (data G halg M p) oracle ho' (asMacroInput G M r)
  simp only [recovery, input_bytes] at h
  exact h

theorem execution_certificate (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (arity:=arity)) (outputEncoding G halg M p)
      (CF.targetValue G M.binary p) oracle) (r : Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction G halg M p).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction G halg M p).machine oracle
        ((reduction G halg M p).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction G halg M p).machine.output
          ((outputEncoding G halg M p).encode (CF.sourceValue G M.binary p r))) t
        ((MachineCapstone.queries (data G halg M p) (asMacroInput G M r)).map
          (targetEncoding (s:=s) (arity:=arity)).encode) ∧
      UniversalPairReduction.ThreeQuery.queryCount (reduction G halg M p).machine oracle
        ((reduction G halg M p).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t =
          occurrences s r.val+1 ∧
      OracleBatch.primitiveCount (reduction G halg M p).machine oracle
        ((reduction G halg M p).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (Polynomial.C (reduction G halg M p).machine.primitiveBudget *
          (reduction G halg M p).time).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  obtain ⟨t,ht,hr⟩ := execution G halg M p oracle ho r
  refine ⟨t,ht,hr,?_,?_⟩
  · have hc := hr.count
    simp only [List.length_map, MachineCapstone.queries, EncodedBatch.query_count] at hc
    exact hc
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [Polynomial.eval_mul, Polynomial.eval_C] using
        Nat.mul_le_mul_left (reduction G halg M p).machine.primitiveBudget ht)

theorem exact_calls_and_primitive (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (arity:=arity)) (outputEncoding G halg M p)
      (CF.targetValue G M.binary p) oracle) (r : Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction G halg M p).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount (reduction G halg M p).machine oracle
        ((reduction G halg M p).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t =
          occurrences s r.val+1 ∧
      OracleBatch.primitiveCount (reduction G halg M p).machine oracle
        ((reduction G halg M p).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (Polynomial.C (reduction G halg M p).machine.primitiveBudget *
          (reduction G halg M p).time).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  have ho' : RepresentsOracle (targetEncoding (s:=s) (arity:=arity)) (outputEncoding G halg M p)
      ((targetTables G halg M p).evaluate (fixedField G halg M p)) oracle := by
    intro q
    simpa only [target_evaluate] using ho q
  exact MachineCapstone.exact_calls_and_primitive (data G halg M p) oracle ho' (asMacroInput G M r)

end
end Holant.LocalDrafts.BinaryInterpolation.FieldSource
