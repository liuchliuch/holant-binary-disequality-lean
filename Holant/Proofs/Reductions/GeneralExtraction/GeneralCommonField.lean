import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalIndex
import Holant.Proofs.Reductions.GeneralExtraction.GeneralFieldReduction
import Holant.Algebraic.FiniteFamilyField
import Holant.NetworkAlgebra


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralCommonField
open Holant.Tractable
open Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralPowerExposure
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (f : Signature AlgebraicComplex (arity s)) (P : PowerMacro G f)

abbrev Index (s : ℕ) (arity : ℕ → ℕ) := OriginalIndex s arity ⊕ ((Fin (arity s) → Bool) ⊕ Unit)

def coefficient : Index s arity → AlgebraicComplex
  | .inl ⟨i,x⟩ => G i x
  | .inr (.inl x) => f x
  | .inr (.inr _) => P.scale

theorem coefficient_algebraic (i : Index s arity) :
    IsAlgebraic ℚ (coefficient G f P i) := Algebra.IsAlgebraic.isAlgebraic _

abbrev field := familyField (coefficient G f P)
abbrev presentation := familyPresentation (coefficient G f P) (coefficient_algebraic G f P)

theorem finiteDimensional : FiniteDimensional ℚ (field G f P) :=
  familyField_finiteDimensional (coefficient G f P) (coefficient_algebraic G f P)

def original (i : Fin s) (x : Fin (arity i.val) → Bool) : field G f P :=
  fieldCoefficient (coefficient G f P) (.inl ⟨i,x⟩)
def factor (x : Fin (arity s) → Bool) : field G f P :=
  fieldCoefficient (coefficient G f P) (.inr (.inl x))
def scale : field G f P := fieldCoefficient (coefficient G f P) (.inr (.inr ()))

@[simp] theorem original_exact (i : Fin s) (x : Fin (arity i.val) → Bool) :
    (original G f P i x : AlgebraicComplex) = G i x := rfl
@[simp] theorem factor_exact (x : Fin (arity s) → Bool) :
    (factor G f P x : AlgebraicComplex) = f x := rfl
@[simp] theorem scale_exact : (scale G f P : AlgebraicComplex) = P.scale := rfl

/-- The same literal labelled template in the common field, with its value
proved through the faithful embedding. The output has arity exponent*n. -/
def powerMacro : PowerMacro (original G f P) (factor G f P) where
  exponent := P.exponent
  positive := P.positive
  scale := scale G f P
  scale_ne_zero := by
    intro h
    have he := congrArg (fun x : field G f P => (x : AlgebraicComplex)) h
    exact P.scale_ne_zero he
  network := P.labels.sourceNetwork (original G f P) (fun _ => Signature.disequality)
  labels := P.labels
  value := by
    let N := P.labels.template.network P.labels.wellFormed (original G f P)
      (fun _ : Fin 1 => Signature.disequality)
    have hn : N.map (field G f P).subtype =
        P.labels.template.network P.labels.wellFormed G (fun _ => Signature.disequality) := by
      unfold N Network.map Template.network
      congr 1
      funext e a b
      cases a <;> cases b <;> rfl
    funext x
    apply Subtype.ext
    change (field G f P).subtype (N.denote x) = _
    rw [← Network.denote_map, hn, P.value]
    change P.scale * Carrier.blockPower f P.exponent x = (field G f P).subtype (scale G f P * Carrier.blockPower (factor G f P) P.exponent x)
    simp [Carrier.blockPower, map_mul, map_prod, factor_exact, scale_exact] <;> rfl

theorem factorTable_exact (i : ℕ) (bits : List Bool) :
    ((GeneralOriginalQuery.factorTable (original G f P) (factor G f P) i bits : field G f P) : AlgebraicComplex) =
      GeneralOriginalQuery.factorTable G f i bits := by
  by_cases hs : i = s <;> by_cases hi : i < s <;>
    simp [GeneralOriginalQuery.factorTable, RawFactorGrouping.sourceTable,
      GroupedWords.word, Choice.table, hs, hi]

def targetValue (q : ExactSignatureTables.Input s 1 arity) : field G f P :=
  (GeneralFieldReduction.targetTables (presentation G f P) (original G f P)).evaluate (presentation G f P) q
def sourceValue (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) : field G f P :=
  GeneralFieldReduction.sourceValue (original G f P) (factor G f P) r

theorem target_exact (q : ExactSignatureTables.Input s 1 arity) :
    (targetValue G f P q : AlgebraicComplex) =
      (q.val.realize q.property G (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [targetValue, FieldReduction.target_evaluate]
  change (field G f P).subtype _ = _
  rw [← Network.denote_map]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  funext e a b
  cases a <;> cases b <;> rfl

theorem source_table_exact (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    (sourceValue G f P r : AlgebraicComplex) =
      ResidueAnchors.value (GeneralOriginalQuery.factorTable G f) r := by
  change (field G f P).subtype _ = _
  unfold sourceValue GeneralFieldReduction.sourceValue ResidueAnchors.value Choice.evaluate Choice.weight
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_list_prod]
  congr 1
  simp only [List.map_map, Function.comp_def, Choice.rowValue]
  exact List.map_congr_left (fun row _ => factorTable_exact G f P row.1 _)

theorem source_exact (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    (sourceValue G f P r : AlgebraicComplex) =
      (r.val.realize r.property (Tables.typed (GeneralOriginalQuery.factorTable G f) (s+1) arity)
        (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [source_table_exact]
  exact (Tables.denote_eq_evaluate _ r.val r.property).symm

def reduction : PolyTimeOracleReduction
    (GeneralFieldReduction.inputEncoding (s:=s) (arity:=arity)) (presentation G f P).encoding
    (GeneralFieldReduction.queryEncoding (s:=s) (arity:=arity)) (presentation G f P).encoding
    (sourceValue G f P) (targetValue G f P) :=
  GeneralFieldReduction.reduction (presentation G f P) (original G f P) (factor G f P) (powerMacro G f P)

def controlled : LengthControlledOracleReduction
    (GeneralFieldReduction.inputEncoding (s:=s) (arity:=arity)) (presentation G f P).encoding
    (GeneralFieldReduction.queryEncoding (s:=s) (arity:=arity)) (presentation G f P).encoding
    (sourceValue G f P) (targetValue G f P) :=
  GeneralFieldReduction.controlled (presentation G f P) (original G f P) (factor G f P) (powerMacro G f P)

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralCommonField
