import Holant.Proofs.BinaryInterpolation.SingularExtraction.FieldReduction
import Holant.Algebraic.FiniteFamilyField
import Holant.NetworkAlgebra


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.CommonField
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (u v : Bool → AlgebraicComplex) (U : PowerMacro G u) (V : PowerMacro G v)

abbrev Index (s : ℕ) (arity : ℕ → ℕ) :=
  (Σ i : Fin s, (Fin (arity i.val) → Bool)) ⊕ ((Bool × Bool) ⊕ Bool)

def coefficient : Index s arity → AlgebraicComplex
  | .inl ⟨i,x⟩ => G i x
  | .inr (.inl (q,a)) => if q then v a else u a
  | .inr (.inr q) => if q then V.scale else U.scale

theorem coefficient_algebraic (i : Index s arity) :
    IsAlgebraic ℚ (coefficient G u v U V i) := Algebra.IsAlgebraic.isAlgebraic _

abbrev field := familyField (coefficient G u v U V)
abbrev presentation := familyPresentation (coefficient G u v U V) (coefficient_algebraic G u v U V)

theorem finiteDimensional : FiniteDimensional ℚ (field G u v U V) :=
  familyField_finiteDimensional (coefficient G u v U V) (coefficient_algebraic G u v U V)

abbrev original (i : Fin s) (x : Fin (arity i.val) → Bool) : field G u v U V :=
  fieldCoefficient (coefficient G u v U V) (.inl ⟨i,x⟩)

def left (a : Bool) : field G u v U V :=
  fieldCoefficient (coefficient G u v U V) (.inr (.inl (false,a)))
def right (a : Bool) : field G u v U V :=
  fieldCoefficient (coefficient G u v U V) (.inr (.inl (true,a)))
def leftScale : field G u v U V :=
  fieldCoefficient (coefficient G u v U V) (.inr (.inr false))
def rightScale : field G u v U V :=
  fieldCoefficient (coefficient G u v U V) (.inr (.inr true))

@[simp] theorem original_exact (i : Fin s) (x : Fin (arity i.val) → Bool) :
    (original G u v U V i x : AlgebraicComplex) = G i x := rfl
@[simp] theorem left_exact (a : Bool) : (left G u v U V a : AlgebraicComplex) = u a := rfl
@[simp] theorem right_exact (a : Bool) : (right G u v U V a : AlgebraicComplex) = v a := rfl
@[simp] theorem leftScale_exact : (leftScale G u v U V : AlgebraicComplex) = U.scale := rfl
@[simp] theorem rightScale_exact : (rightScale G u v U V : AlgebraicComplex) = V.scale := rfl

/-- Transport a locally proved macro through the faithful embedding. The two
entry equalities identify literal coefficients; no realization is presumed in
the smaller field. Its actual network and local value proof are built here. -/
def liftMacro (w : Bool → AlgebraicComplex) (M : PowerMacro G w)
    (w' : Bool → field G u v U V) (a : field G u v U V)
    (hw : ∀ b, (w' b : AlgebraicComplex) = w b) (ha : (a : AlgebraicComplex) = M.scale) :
    PowerMacro (original G u v U V) w' where
  exponent := M.exponent
  positive := M.positive
  scale := a
  scale_ne_zero := by
    intro h
    apply M.scale_ne_zero
    rw [← ha, h]
    rfl
  network := M.labels.sourceNetwork (original G u v U V) (fun _ => Signature.disequality)
  labels := M.labels
  value := by
    let N := M.labels.template.network M.labels.wellFormed (original G u v U V)
      (fun _ : Fin 1 => Signature.disequality)
    have hn : N.map (field G u v U V).subtype =
        M.labels.template.network M.labels.wellFormed G (fun _ => Signature.disequality) := by
      unfold N Network.map Template.network
      congr 1
      funext e b c
      cases b <;> cases c <;> rfl
    funext x
    apply Subtype.ext
    change (field G u v U V).subtype (N.denote x) = _
    rw [← Network.denote_map, hn, M.value]
    change M.scale * ∏ i, w (x i) = (field G u v U V).subtype (a * ∏ i, w' (x i))
    simp only [map_mul, map_prod]
    change M.scale * ∏ i, w (x i) = (a : AlgebraicComplex) * ∏ i, (w' (x i) : AlgebraicComplex)
    rw [ha]
    simp only [hw]

def leftMacro : PowerMacro (original G u v U V) (left G u v U V) :=
  liftMacro G u v U V u U (left G u v U V) (leftScale G u v U V)
    (left_exact G u v U V) (leftScale_exact G u v U V)

def rightMacro : PowerMacro (original G u v U V) (right G u v U V) :=
  liftMacro G u v U V v V (right G u v U V) (rightScale G u v U V)
    (right_exact G u v U V) (rightScale_exact G u v U V)

theorem familyTable_exact (i : ℕ) (bits : List Bool) :
    ((Tables.familyTable (original G u v U V) (left G u v U V) (right G u v U V) i bits : field G u v U V) :
      AlgebraicComplex) = Tables.familyTable G u v i bits := by
  change (field G u v U V).subtype _ = _
  have hl (x : Bool) : (field G u v U V).val (left G u v U V x) = u x := rfl
  have hr (x : Bool) : (field G u v U V).val (right G u v U V x) = v x := rfl
  by_cases hs : i = s <;> by_cases hc : i = s+1 <;> by_cases hi : i < s <;>
    simp [Tables.familyTable, GroupedQuery.table, RawGrouping.withPower, Choice.table,
      hs, hc, hi, hl, hr, map_list_prod, List.map_map, Function.comp_def] <;> rfl

def targetValue (q : ExactSignatureTables.Input s 1 arity) : field G u v U V :=
  (FieldReduction.targetTables (presentation G u v U V) (original G u v U V)).evaluate
    (presentation G u v U V) q

def sourceValue (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) : field G u v U V :=
  FieldReduction.sourceValue (original G u v U V) (left G u v U V) (right G u v U V) r

/-- The target oracle is exactly the literal original Γ family. -/
theorem target_exact (q : ExactSignatureTables.Input s 1 arity) :
    (targetValue G u v U V q : AlgebraicComplex) =
      (q.val.realize q.property G (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [targetValue, FieldReduction.target_evaluate]
  change (field G u v U V).subtype _ = _
  rw [← Network.denote_map]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  funext e a b
  cases a <;> cases b <;> rfl

theorem source_table_exact (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    (sourceValue G u v U V r : AlgebraicComplex) =
      ResidueAnchors.value (Tables.familyTable G u v) r := by
  change (field G u v U V).subtype _ = _
  unfold sourceValue FieldReduction.sourceValue ResidueAnchors.value Choice.evaluate Choice.weight
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_list_prod]
  congr 1
  simp only [List.map_map, Function.comp_def, Choice.rowValue]
  exact List.map_congr_left (fun row _ => familyTable_exact G u v U V row.1 _)

/-- The output is the original native-X closed Holant value with two separately
labelled unaries, including unequal multiplicities, loops and zero answers. -/
theorem source_exact (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    (sourceValue G u v U V r : AlgebraicComplex) =
      (r.val.realize r.property
        (Tables.typed (Tables.familyTable G u v) (s+2) (Tables.adjoinedArity s arity 1 1))
        (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [source_table_exact]
  exact (Tables.denote_eq_evaluate _ r.val r.property).symm

/-- This declaration fixes one rational-coordinate output codec shared by the
original-family oracle and the answer. Every machine component is constructed. -/
def reduction : PolyTimeOracleReduction
    (FieldReduction.inputEncoding (s:=s) (arity:=arity)) (presentation G u v U V).encoding
    (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (presentation G u v U V).encoding
    (sourceValue G u v U V) (targetValue G u v U V) :=
  FieldReduction.reduction (presentation G u v U V) (original G u v U V)
    (left G u v U V) (right G u v U V) (leftMacro G u v U V) (rightMacro G u v U V)

abbrev timePolynomial := FieldReduction.timePolynomial (presentation G u v U V)
  (original G u v U V) (left G u v U V) (right G u v U V)
  (leftMacro G u v U V) (rightMacro G u v U V)
abbrev primitivePolynomial := FieldReduction.primitivePolynomial (presentation G u v U V)
  (original G u v U V) (left G u v U V) (right G u v U V)
  (leftMacro G u v U V) (rightMacro G u v U V)
abbrev budget := FieldReduction.budget (presentation G u v U V)
  (original G u v U V) (left G u v U V) (right G u v U V)
  (leftMacro G u v U V) (rightMacro G u v U V)

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.CommonField
