import Holant.Proofs.Algorithms.QuaternaryEqualityTerminal
import Holant.OpenNetworkComposition.FactorFreeNormalization.Reduction
import Holant.Proofs.Algorithms.HolographicTransport
import Holant.Proofs.Algorithms.FamilyAnswerTransport
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Reductions.FrozenFactorNormalization.OriginalLCodec
import Holant.Projective.CyclicQuaternary.Physical


noncomputable section
namespace Holant.LocalDrafts.MainChain.QuaternaryAnchorAccess
open Computability Holant.Algebraic Holant.Complexity Holant.Tractable
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.EightVertex.ProductAnchor
open Holant.LocalDrafts.Hardness
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

abbrev Anchor := QuaternaryEqualityTerminal.AnchorStep

private def actionSignature (B : InvertibleKernel)
    (f : AnySignature AlgebraicComplex) : AnySignature AlgebraicComplex :=
  ⟨f.1,B.action f.2⟩

section NoFreeWire
variable {F : SignatureFamily AlgebraicComplex} (A : Anchor F)

/-- A consequence of the two ACTUAL anchor equations, not an extra endpoint
premise. It rules out free/free native-X wires in any supplied realization. -/
theorem anchor_endpoint : A.signature (fun _ => false)≠0 := by
  let a := A.basis.inverse false false
  let b := A.basis.inverse false true
  let c := A.basis.inverse true false
  let d := A.basis.inverse true true
  have h00 : 2*a*c=A.edgeScale := by
    have h := congrFun (congrFun A.edge_exact false) false
    have he : a*c+a*c=A.edgeScale := by
      simpa [Kernel.pullback,Kernel.mul,Kernel.transpose,Signature.disequality,
        Signature.equality,Fintype.sum_bool,a,c,mul_comm] using h
    linear_combination he
  have h11 : 2*b*d=A.edgeScale := by
    have h := congrFun (congrFun A.edge_exact true) true
    have he : b*d+b*d=A.edgeScale := by
      simpa [Kernel.pullback,Kernel.mul,Kernel.transpose,Signature.disequality,
        Signature.equality,Fintype.sum_bool,b,d,mul_comm] using h
    linear_combination he
  have h01 : a*d+b*c=0 := by
    have h := congrFun (congrFun A.edge_exact false) true
    simpa [Kernel.pullback,Kernel.mul,Kernel.transpose,Signature.disequality,
      Signature.equality,Fintype.sum_bool,a,b,c,d,mul_comm,add_comm] using h
  have ha : a≠0 := by
    intro hz
    apply A.edge_ne_zero
    simpa [hz] using h00.symm
  have hs : a^2+b^2=0 := by
    have hk : A.edgeScale*(a^2+b^2)=0 := by
      calc
        A.edgeScale*(a^2+b^2)=2*a*b*(a*d+b*c) := by
          linear_combination -a^2*h11-b^2*h00
        _=0 := by rw [h01]; ring
    exact (mul_eq_zero.mp hk).resolve_left A.edge_ne_zero
  have h4 : b^4=a^4 := by
    linear_combination (b^2-a^2)*hs
  have hback : A.signature=A.basis.symm.action
      (fun x => A.vertexScale*equalityFour x) := by
    rw [←A.anchor_exact,A.basis.symm_action_action]
  have hv : A.signature (fun _ => false)=A.vertexScale*(a^4+b^4) := by
    rw [hback]
    simp [InvertibleKernel.action,InvertibleKernel.symm,Signature.coordinateAction,
      Holant.Projective.CyclicQuaternary.Physical.sum_words4,
      equalityFour,Fin.prod_univ_succ,
      Fintype.sum_bool,Fin.forall_fin_succ,a,b]
    <;> ring
  rw [hv,h4]
  exact mul_ne_zero A.vertex_ne_zero (by
    rw [←two_mul]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ ha))

theorem anchor_noXFactor :
    OpenNetworkComposition.FactorFreeNormalization.NoXFactor A.signature := by
  rintro ⟨i,j,hij,f,hf⟩
  apply anchor_endpoint A
  simpa [Signature.disequality] using hf (fun _ => false)

theorem ordinary_exists : ∃N : Network AlgebraicComplex 4,
    (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex)∈F) ∧
    (∀e,N.edge e=Signature.disequality) ∧ N.denote=A.signature :=
  OpenNetworkComposition.FactorFreeNormalization.realizes_exists_ordinary
    A.actual (anchor_noXFactor A)

/-- Chosen from the given realization's normalization proof, including all
its scalar components; no alternate saturation tree or parent is selected. -/
def ordinary := Classical.choose (ordinary_exists A)
theorem ordinary_labels : ∀v,(⟨(ordinary A).shape.arity v,(ordinary A).vertex v⟩ :
    AnySignature AlgebraicComplex)∈F := (Classical.choose_spec (ordinary_exists A)).1
theorem ordinary_edges : ∀e,(ordinary A).edge e=Signature.disequality :=
  (Classical.choose_spec (ordinary_exists A)).2.1
theorem ordinary_denote : (ordinary A).denote=A.signature :=
  (Classical.choose_spec (ordinary_exists A)).2.2
end NoFreeWire

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (A : Anchor (UniversalPairReduction.FiniteFamily.family G))

def labels := UniversalPairReduction.FiniteFamily.labelling G (ordinary A) (ordinary_labels A)
def template := (labels G A).template
theorem macro_valid : (template G A).WellFormed s 1 a := (labels G A).wellFormed
theorem macro_exact : ((template G A).network (macro_valid G A) G
    (fun _ : Fin 1 => Signature.disequality)).denote=A.signature := by
  unfold template labels
  rw [Labelling.denote_template,
    UniversalPairReduction.FiniteFamily.labelled_network G (ordinary A)
      (ordinary_labels A) (ordinary_edges A),ordinary_denote]

/-- These are coefficient indices, NEVER auxiliary vertex labels. -/
abbrev Extra := (Bool×Bool) ⊕ ((Bool×Bool) ⊕ Bool)
local instance coefficientIndexFintype :
    Fintype (ExactSignatureTables.CoefficientIndex s 1 a ⊕ Extra) := Fintype.ofFinite _
def values : ExactSignatureTables.CoefficientIndex s 1 a ⊕ Extra → AlgebraicComplex
  | .inl i => UniversalPairReduction.FiniteFamily.coefficient G i
  | .inr (.inl (b,c)) => A.basis.matrix b c
  | .inr (.inr (.inl (b,c))) => A.basis.inverse b c
  | .inr (.inr (.inr false)) => A.edgeScale
  | .inr (.inr (.inr true)) => A.vertexScale
theorem values_algebraic (i) : IsAlgebraic ℚ (values G A i) :=
  Algebra.IsAlgebraic.isAlgebraic _
abbrev K := familyField (values G A)
local instance coefficientAlgebra : Algebra ℚ (K G A) := (K G A).algebra'
local instance coefficientCharZero : CharZero (K G A) := Algebra.charZero_of_charZero ℚ (K G A)
abbrev presentation := familyPresentation (values G A) (values_algebraic G A)
local instance rationalAlgebra : Algebra ℚ (K G A) := (K G A).algebra'
def matrix : Kernel (K G A) := fun b c => fieldCoefficient (values G A) (.inr (.inl (b,c)))
def inverse : Kernel (K G A) := fun b c => fieldCoefficient (values G A) (.inr (.inr (.inl (b,c))))
def kappa : K G A := fieldCoefficient (values G A) (.inr (.inr (.inr false)))
def lambda : K G A := fieldCoefficient (values G A) (.inr (.inr (.inr true)))
theorem kappa_ne : kappa G A≠0 := fun h => A.edge_ne_zero (congrArg Subtype.val h)
theorem lambda_ne : lambda G A≠0 := fun h => A.vertex_ne_zero (congrArg Subtype.val h)

def originalTables := PresentedScaledFamily.tables (values G A) (values_algebraic G A) Sum.inl
abbrev originalValue := (originalTables G A).evaluate (presentation G A)

theorem original_vertex (i : Fin s) (x : Fin (a i.val) → Bool) :
    (((presentation G A).decode ((originalTables G A).vertex i x) : K G A) :
      AlgebraicComplex)=G i x := familyCoordinates_spec _ _ _
theorem original_edge (i : Fin 1) (b c : Bool) :
    (presentation G A).decode ((originalTables G A).edge i b c)=Signature.disequality b c := by
  apply Subtype.val_injective
  have h := familyCoordinates_spec (values G A) (values_algebraic G A) (.inl (.inr (i,b,c)))
  change (((presentation G A).decode ((originalTables G A).edge i b c) : K G A) :
    AlgebraicComplex)=Signature.disequality b c at h
  simpa only [Signature.disequality,apply_ite,IntermediateField.coe_zero,
    IntermediateField.coe_one] using h

theorem inverse_matrix : Kernel.mul (inverse G A) (matrix G A)=Signature.equality := by
  funext b c
  apply Subtype.val_injective
  have h := congrFun (congrFun A.basis.inverse_matrix b) c
  cases b <;> cases c <;>
    simpa [Kernel.mul,Fintype.sum_bool,inverse,matrix,fieldCoefficient,values,
      Signature.equality] using h

theorem pulled_edge : Kernel.pullback (Signature.disequality : Kernel (K G A))
    (inverse G A)=fun b c => kappa G A*Signature.equality b c := by
  funext b c
  apply Subtype.val_injective
  have h := congrFun (congrFun A.edge_exact b) c
  cases b <;> cases c <;>
    simpa [Kernel.pullback,Kernel.mul,Kernel.transpose,Fintype.sum_bool,inverse,kappa,
      fieldCoefficient,values,Signature.equality,Signature.disequality] using h

abbrev arity := sourceArity (Adjoin.templates s a (template G A))
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (arity G A)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
def normalizedTables := sourceTables (Adjoin.templates s a (template G A)) (originalTables G A)
  (ScaledAdjoin.coordinates (presentation G A) (originalTables G A)
    (template G A) (macro_valid G A) (lambda G A))
def transformedTables := HolographicTransport.tables (presentation G A)
  (normalizedTables G A) (inverse G A) (matrix G A)
/-- Actual ORDINARY edges. The separate controlled prefix accounts for κ^E. -/
def tables : ExactSignatureTables (Module.finrank ℚ (K G A)) (s+1) 1 (arity G A) where
  vertex := (transformedTables G A).vertex
  edge _ b c := (presentation G A).decode.symm (Signature.equality b c)
abbrev value := (tables G A).evaluate (presentation G A)

theorem table_action (i : Fin (s+1)) (x : Fin (arity G A i.val) → Bool) :
    (((presentation G A).decode ((tables G A).vertex i x) : K G A) : AlgebraicComplex)=
      A.basis.action (fun y => (((presentation G A).decode
        ((normalizedTables G A).vertex i y) : K G A) : AlgebraicComplex)) x := by
  simp [tables,transformedTables,HolographicTransport.tables,
    InvertibleKernel.action,Signature.coordinateAction,matrix,fieldCoefficient,values]

/-- Physical source identities before basis change, retaining the actual
anchor normalization λ. -/
theorem normalized_ambient : Set.range (fun i : Fin (s+1) =>
    (⟨arity G A i.val,fun x => (((presentation G A).decode
      ((normalizedTables G A).vertex i x) : K G A) : AlgebraicComplex)⟩ :
      AnySignature AlgebraicComplex)) =
    UniversalPairReduction.FiniteFamily.family G ∪
      {⟨4,fun x => A.signature x/A.vertexScale⟩} := by
  have h := PresentedScaledFamily.ambientSource_family (values G A) Sum.inl
    (template G A) (macro_valid G A) (lambda G A)
  have hm : (OriginalFamily.ambientMacro (fun i => values G A (Sum.inl i))
      (template G A) (macro_valid G A)).denote=A.signature := macro_exact G A
  simp only [hm] at h
  have hc : ∀(i : Fin (s+1)) x,
      (((presentation G A).decode ((normalizedTables G A).vertex i x) : K G A) :
        AlgebraicComplex)=PresentedScaledFamily.ambientSource (values G A) Sum.inl
          (template G A) (macro_valid G A) (lambda G A) i x := by
    intro i x
    exact PresentedScaledFamily.coordinates_value_exact (values G A) (values_algebraic G A)
      Sum.inl (template G A) (macro_valid G A) (lambda G A) i x
  simp_rw [hc]
  exact h

theorem normalized_anchor_action :
    A.basis.action (fun x => A.signature x/A.vertexScale)=equalityFour := by
  have h := coordinateAction_scale (fun _ : Fin 4 => A.basis.matrix)
    A.vertexScale⁻¹ A.signature
  change Signature.coordinateAction (fun _ => A.basis.matrix) _=equalityFour
  simp_rw [div_eq_mul_inv,mul_comm _ A.vertexScale⁻¹]
  rw [h]
  change (fun x => A.vertexScale⁻¹*A.basis.action A.signature x)=_
  rw [A.anchor_exact]
  funext x
  simp [A.vertex_ne_zero]

/-- Every member, not just the anchor, has the SAME R. Eq4 is the normalized
last physical template, and the source has literal ordinary equality edges. -/
theorem family_exact : Set.range (fun i : Fin (s+1) =>
    (⟨arity G A i.val,fun x => (((presentation G A).decode
      ((tables G A).vertex i x) : K G A) : AlgebraicComplex)⟩ :
      AnySignature AlgebraicComplex)) =
    familyAction A.basis (UniversalPairReduction.FiniteFamily.family G) ∪ {⟨4,equalityFour⟩} := by
  have hmap : ∀(i : Fin (s+1)) x,
      (((presentation G A).decode ((tables G A).vertex i x) : K G A) : AlgebraicComplex)=
      A.basis.action (fun y => (((presentation G A).decode
        ((normalizedTables G A).vertex i y) : K G A) : AlgebraicComplex)) x := by
    intro i x
    exact table_action G A i x
  simp_rw [hmap]
  have hi : Set.range (fun i : Fin (s+1) =>
      (⟨arity G A i.val,A.basis.action (fun y => (((presentation G A).decode
        ((normalizedTables G A).vertex i y) : K G A) : AlgebraicComplex))⟩ :
          AnySignature AlgebraicComplex)) =
      familyAction A.basis (Set.range (fun i : Fin (s+1) =>
        (⟨arity G A i.val,fun y => (((presentation G A).decode
          ((normalizedTables G A).vertex i y) : K G A) : AlgebraicComplex)⟩ :
            AnySignature AlgebraicComplex))) := by
    ext f
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i,rfl⟩,rfl⟩
    · rintro ⟨g,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  rw [hi]
  rw [normalized_ambient]
  simp only [familyAction,Set.image_union,Set.image_singleton,
    normalized_anchor_action]

/-- The ordered new slot, not merely an existential member of the source
family. Its four ports are exactly the original anchor's four boundary ports. -/
theorem eq4_label :
    (⟨arity G A s,fun x => (((presentation G A).decode
      ((tables G A).vertex ⟨s,Nat.lt_succ_self s⟩ x) : K G A) : AlgebraicComplex)⟩ :
        AnySignature AlgebraicComplex)=⟨4,equalityFour⟩ := by
  have hn :
      (⟨arity G A s,fun x => (((presentation G A).decode
        ((normalizedTables G A).vertex ⟨s,Nat.lt_succ_self s⟩ x) : K G A) : AlgebraicComplex)⟩ :
          AnySignature AlgebraicComplex)=⟨4,fun x => A.signature x/A.vertexScale⟩ := by
    have he := PresentedScaledFamily.ambientSource_new (values G A) Sum.inl
      (template G A) (macro_valid G A) (lambda G A)
    have hm : (OriginalFamily.ambientMacro (fun i => values G A (Sum.inl i))
        (template G A) (macro_valid G A)).denote=A.signature := macro_exact G A
    rw [hm] at he
    apply Sigma.ext (Adjoin.new_boundary (template G A))
    apply HEq.trans _ he
    apply heq_of_eq
    funext x
    exact PresentedScaledFamily.coordinates_value_exact (values G A) (values_algebraic G A)
      Sum.inl (template G A) (macro_valid G A) (lambda G A) ⟨s,Nat.lt_succ_self s⟩ x
  have ht := congrArg (actionSignature A.basis) hn
  calc
    (⟨arity G A s,fun x => (((presentation G A).decode
        ((tables G A).vertex ⟨s,Nat.lt_succ_self s⟩ x) : K G A) : AlgebraicComplex)⟩ :
        AnySignature AlgebraicComplex) =
      (⟨arity G A s,A.basis.action (fun x => (((presentation G A).decode
        ((normalizedTables G A).vertex ⟨s,Nat.lt_succ_self s⟩ x) : K G A) :
          AlgebraicComplex))⟩ : AnySignature AlgebraicComplex) := by
      exact congrArg (fun f : Signature AlgebraicComplex (arity G A s) =>
        (⟨arity G A s,f⟩ : AnySignature AlgebraicComplex))
        (funext (table_action G A ⟨s,Nat.lt_succ_self s⟩))
    _ = ⟨4,equalityFour⟩ := by
      simpa only [actionSignature,normalized_anchor_action] using ht

theorem ordinary_edge (i : Fin 1) (b c : Bool) :
    (presentation G A).decode ((tables G A).edge i b c)=Signature.equality b c :=
  LinearEquiv.apply_symm_apply _ _

theorem transformed_edge (i : Fin 1) (b c : Bool) :
    (presentation G A).decode ((transformedTables G A).edge i b c)=
      kappa G A*Signature.equality b c := by
  simp only [transformedTables,HolographicTransport.tables,LinearEquiv.apply_symm_apply]
  simp_rw [show (fun u v => (presentation G A).decode
    ((normalizedTables G A).edge i u v))=Signature.disequality from
      funext (fun u => funext (fun v => original_edge G A i u v))]
  exact congrFun (congrFun (pulled_edge G A) b) c

/-- Entire assignment sum, with edge multiplicity, loops, scalar components,
empty graphs, and nullary vertices. E counts INPUT edges before substitution. -/
theorem transformed_value (r : ExactSignatureTables.Input (s+1) 1 (arity G A)) :
    (transformedTables G A).evaluate (presentation G A) r=
      (kappa G A)^r.val.edges.length*value G A r := by
  unfold value
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [Network.denote,RawClosedNetwork.realize,tables,
    LinearEquiv.apply_symm_apply]
  simp_rw [transformed_edge]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change (∑ z, _)=(kappa G A)^r.val.edges.length*∑ z, _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [RawClosedNetwork.shape]
  ring

def edgeControlled : LengthControlledOracleReduction (inputEncoding G A) (presentation G A).encoding
    (inputEncoding G A) (presentation G A).encoding (value G A)
    ((transformedTables G A).evaluate (presentation G A)) :=
  ControlledCap.controlledContextOfEq
    (pairComputes (identityComputes (inputEncoding G A))
      (Compiler.edgeCountComputes (s+1) 1 (arity G A)))
    (ScalarPower.correction (presentation G A) (kappa G A))
    ((transformedTables G A).outputBound (presentation G A)) (value G A)
    (fun r => by
      change value G A r=_*(kappa G A)⁻¹^r.val.edges.length
      dsimp only [id,Prod.fst,Prod.snd]
      rw [transformed_value,ScalarPower.cancel_scale_power _ _ (kappa_ne G A)])

def basisControlled := HolographicTransport.fromTransformed (presentation G A)
  (normalizedTables G A) (inverse G A) (matrix G A) (inverse_matrix G A)
def macroControlled := ControlledCap.scaledAdjoin (presentation G A) (originalTables G A)
  (template G A) (macro_valid G A) (lambda G A) (lambda_ne G A)

/-- Exact underlying query of the composed access: holographic and edge
prefixes preserve the raw graph; this is the sole structural replacement. -/
def query := Compiler.value (s+1) 1 (arity G A) (Adjoin.templates s a (template G A)) s a
  (compilerHypotheses (Adjoin.templates s a (template G A)) (Adjoin.wellFormed _ (macro_valid G A)))
def queryComputes := Compiler.computes (s+1) 1 (arity G A) (Adjoin.templates s a (template G A)) s a
  (compilerHypotheses (Adjoin.templates s a (template G A)) (Adjoin.wellFormed _ (macro_valid G A)))

theorem query_value (r : ExactSignatureTables.Input (s+1) 1 (arity G A)) :
    originalValue G A (query G A r)=
      (lambda G A)^occurrences s r.val*(kappa G A)^r.val.edges.length*value G A r := by
  have hd : ∀i : Fin (s+1),
      ((Adjoin.templates s a (template G A) i.val).network
        (Adjoin.wellFormed _ (macro_valid G A) i.val i.isLt)
        (fun j x => (presentation G A).decode ((originalTables G A).vertex j x))
        (fun j b c => (presentation G A).decode ((originalTables G A).edge j b c))).denote =
      (if i.val=s then lambda G A else 1) •
        (fun x => (presentation G A).decode ((normalizedTables G A).vertex i x)) := by
    intro i
    funext x
    change _=(if i.val=s then lambda G A else 1)*
      (presentation G A).decode (ScaledAdjoin.coordinates (presentation G A)
        (originalTables G A) (template G A) (macro_valid G A) (lambda G A) i x)
    unfold ScaledAdjoin.coordinates ScaledAdjoin.rescale
    rw [LinearEquiv.apply_symm_apply]
    dsimp only [Adjoin.coordinates]
    rw [decode_templateCoordinates]
    have hn : (if i.val=s then lambda G A else 1)≠0 := by
      split_ifs <;> simp_all [lambda_ne G A]
    field_simp
  have h := replacement_scale_power (Adjoin.templates s a (template G A)) r.val r.property
    (Adjoin.wellFormed _ (macro_valid G A))
    (fun i x => (presentation G A).decode ((normalizedTables G A).vertex i x))
    (fun i x => (presentation G A).decode ((originalTables G A).vertex i x))
    (fun i b c => (presentation G A).decode ((originalTables G A).edge i b c)) s (lambda G A) hd
  change originalValue G A (query G A r)=(lambda G A)^occurrences s r.val*
    (normalizedTables G A).evaluate (presentation G A) r at h
  rw [←HolographicTransport.value_eq (presentation G A) (normalizedTables G A)
    (inverse G A) (matrix G A) (inverse_matrix G A) r] at h
  rw [show (HolographicTransport.tables (presentation G A) (normalizedTables G A)
    (inverse G A) (matrix G A)).evaluate (presentation G A) r=
      (kappa G A)^r.val.edges.length*value G A r from transformed_value G A r] at h
  exact h.trans (mul_assoc _ _ _).symm

theorem query_old_edges (r : ExactSignatureTables.Input (s+1) 1 (arity G A)) :
    (query G A r).val.edges=r.val.edges++
      (expandRows (Adjoin.templates s a (template G A)) r.val.edges.length r.val.vertices).edges := rfl

theorem query_length (r : ExactSignatureTables.Input (s+1) 1 (arity G A)) :
    ((targetEncoding (s:=s) (a:=a)).encode (query G A r)).length ≤
      (queryComputes G A).outputBound.bound.eval ((inputEncoding G A).encode r).length :=
  (queryComputes G A).outputBound.length_le r

/-- Machine-derived running time; the output-length bound alone is not used
as a running-time estimate. -/
theorem query_primitive_bound (r : ExactSignatureTables.Input (s+1) 1 (arity G A)) :
    primitiveCost (queryComputes G A).machine ((queryComputes G A).outputs r).steps
      (some (Turing.initList (queryComputes G A).machine.computer ((inputEncoding G A).encode r))) ≤
      (primitivePolynomial (queryComputes G A)).eval ((inputEncoding G A).encode r).length :=
  computes_primitive_cost (queryComputes G A) r

namespace GOT
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients coefficients_algebraic originalPresentation originalTables originalValue target_exact)
end GOT

/-- The original oracle's answer is recovered into the finite work field by
an actual rational linear machine. R need not belong to the original field. -/
def originalControlled : LengthControlledOracleReduction
    (targetEncoding (s:=s) (a:=a)) (presentation G A).encoding
    (targetEncoding (s:=s) (a:=a)) (GOT.originalPresentation G).encoding
    (originalValue G A) (GOT.originalValue G) :=
  controlledOneQueryOfEq (identityComputes (targetEncoding (s:=s) (a:=a)))
    (FamilyAnswerTransport.computes (values G A) (GOT.coefficients G)
      (values_algebraic G A) (GOT.coefficients_algebraic G))
    ((GOT.originalTables G).outputBound (GOT.originalPresentation G)) (originalValue G A)
    (fun r => by
      symm
      apply FamilyAnswerTransport.recover_exact
      unfold originalValue originalTables
      rw [GOT.target_exact,PresentedScaledFamily.target_value_exact]
      rfl)

abbrev Access := PolyTimeOracleReduction (inputEncoding G A) (presentation G A).encoding
  (targetEncoding (s:=s) (a:=a)) (GOT.originalPresentation G).encoding
  (value G A) (GOT.originalValue G)

/-- Only concrete controlled callers are composed. This substitutes the SAME
ordinary template at each anchor occurrence; no free Eq4 or free basis gadget. -/
def access : Access G A :=
  (edgeControlled G A).compose ((basisControlled G A).compose
    ((macroControlled G A).compose (originalControlled G A).reduction))

def execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (a:=a)) (GOT.originalPresentation G).encoding
      (GOT.originalValue G) oracle)
    (r : ExactSignatureTables.Input (s+1) 1 (arity G A)) :=
  (access G A).correct oracle ho r

section OriginalL
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
variable {L : Type} [Field L] [NumberField L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (H : (i : Fin s) → Signature L (a i.val))
variable (B : Anchor (UniversalPairReduction.FiniteFamily.family (OriginalLCodec.mapped φ H)))

/-- The target really is CURRENT G in its original L codec. The source
remains in the derived extension; no R-entry membership in L is asserted. -/
def accessOriginalL : PolyTimeOracleReduction
    (inputEncoding (OriginalLCodec.mapped φ H) B) (presentation (OriginalLCodec.mapped φ H) B).encoding
    (targetEncoding (s:=s) (a:=a)) (OriginalLCodec.presentation (L:=L)).encoding
    (value (OriginalLCodec.mapped φ H) B) (OriginalLCodec.value H) :=
  let G' := OriginalLCodec.mapped φ H
  (edgeControlled G' B).compose ((basisControlled G' B).compose
    ((macroControlled G' B).compose ((originalControlled G' B).compose
      (OriginalLCodec.fromCoefficient φ H).reduction)))
end OriginalL

end Holant.LocalDrafts.MainChain.QuaternaryAnchorAccess
